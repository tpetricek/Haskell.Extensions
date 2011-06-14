{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}

{-# OPTIONS_GHC -fno-warn-warnings-deprecations #-}

module CmmRewriteAssignments
  ( rewriteAssignments
  ) where

import Cmm
import CmmExpr
import OptimizationFuel
import StgCmmUtils

import Control.Monad
import UniqFM
import Unique

import Compiler.Hoopl hiding (Unique)
import Data.Maybe
import Prelude hiding (succ, zip)

----------------------------------------------------------------
--- Usage information

-- We decorate all register assignments with usage information,
-- that is, the maximum number of times the register is referenced
-- while it is live along all outgoing control paths.  There are a few
-- subtleties here:
--
--  - If a register goes dead, and then becomes live again, the usages
--    of the disjoint live range don't count towards the original range.
--
--          a = 1; // used once
--          b = a;
--          a = 2; // used once
--          c = a;
--
--  - A register may be used multiple times, but these all reside in
--    different control paths, such that any given execution only uses
--    it once. In that case, the usage count may still be 1.
--
--          a = 1; // used once
--          if (b) {
--              c = a + 3;
--          } else {
--              c = a + 1;
--          }
--
--    This policy corresponds to an inlining strategy that does not
--    duplicate computation but may increase binary size.
--
--  - If we naively implement a usage count, we have a counting to
--    infinity problem across joins.  Furthermore, knowing that
--    something is used 2 or more times in one runtime execution isn't
--    particularly useful for optimizations (inlining may be beneficial,
--    but there's no way of knowing that without register pressure
--    information.)
--
--          while (...) {
--              // first iteration, b used once
--              // second iteration, b used twice
--              // third iteration ...
--              a = b;
--          }
--          // b used zero times
--
--    There is an orthogonal question, which is that for every runtime
--    execution, the register may be used only once, but if we inline it
--    in every conditional path, the binary size might increase a lot.
--    But tracking this information would be tricky, because it violates
--    the finite lattice restriction Hoopl requires for termination;
--    we'd thus need to supply an alternate proof, which is probably
--    something we should defer until we actually have an optimization
--    that would take advantage of this.  (This might also interact
--    strangely with liveness information.)
--
--          a = ...;
--          // a is used one time, but in X different paths
--          case (b) of
--              1 -> ... a ...
--              2 -> ... a ...
--              3 -> ... a ...
--              ...
--
--  This analysis is very similar to liveness analysis; we just keep a
--  little extra info. (Maybe we should move it to CmmLive, and subsume
--  the old liveness analysis.)

data RegUsage = SingleUse | ManyUse
    deriving (Ord, Eq, Show)
-- Absence in map = ZeroUse

{-
-- minBound is bottom, maxBound is top, least-upper-bound is max
-- ToDo: Put this in Hoopl.  Note that this isn't as useful as I
-- originally hoped, because you usually want to leave out the bottom
-- element when you have things like this put in maps.  Maybe f is
-- useful on its own as a combining function.
boundedOrdLattice :: (Bounded a, Ord a) => String -> DataflowLattice a
boundedOrdLattice n = DataflowLattice n minBound f
    where f _ (OldFact x) (NewFact y)
            | x >= y    = (NoChange,   x)
            | otherwise = (SomeChange, y)
-}

-- Custom node type we'll rewrite to.  CmmAssign nodes to local
-- registers are replaced with AssignLocal nodes.
data WithRegUsage n e x where
    -- Plain will not contain CmmAssign nodes immediately after
    -- transformation, but as we rewrite assignments, we may have
    -- assignments here: these are assignments that should not be
    -- rewritten!
    Plain       :: n e x -> WithRegUsage n e x
    AssignLocal :: LocalReg -> CmmExpr -> RegUsage -> WithRegUsage n O O

instance UserOfLocalRegs (n e x) => UserOfLocalRegs (WithRegUsage n e x) where
    foldRegsUsed f z (Plain n) = foldRegsUsed f z n
    foldRegsUsed f z (AssignLocal _ e _) = foldRegsUsed f z e

instance DefinerOfLocalRegs (n e x) => DefinerOfLocalRegs (WithRegUsage n e x) where
    foldRegsDefd f z (Plain n) = foldRegsDefd f z n
    foldRegsDefd f z (AssignLocal r _ _) = foldRegsDefd f z r

instance NonLocal n => NonLocal (WithRegUsage n) where
    entryLabel (Plain n) = entryLabel n
    successors (Plain n) = successors n

liftRegUsage :: Graph n e x -> Graph (WithRegUsage n) e x
liftRegUsage = mapGraph Plain

eraseRegUsage :: Graph (WithRegUsage CmmNode) e x -> Graph CmmNode e x
eraseRegUsage = mapGraph f
    where f :: WithRegUsage CmmNode e x -> CmmNode e x
          f (AssignLocal l e _) = CmmAssign (CmmLocal l) e
          f (Plain n) = n

type UsageMap = UniqFM RegUsage

usageLattice :: DataflowLattice UsageMap
usageLattice = DataflowLattice "usage counts for registers" emptyUFM (joinUFM f)
    where f _ (OldFact x) (NewFact y)
            | x >= y    = (NoChange,   x)
            | otherwise = (SomeChange, y)

-- We reuse the names 'gen' and 'kill', although we're doing something
-- slightly different from the Dragon Book
usageTransfer :: BwdTransfer (WithRegUsage CmmNode) UsageMap
usageTransfer = mkBTransfer3 first middle last
    where first _ f = f
          middle :: WithRegUsage CmmNode O O -> UsageMap -> UsageMap
          middle n f = gen_kill n f
          last :: WithRegUsage CmmNode O C -> FactBase UsageMap -> UsageMap
          -- Checking for CmmCall/CmmForeignCall is unnecessary, because
          -- spills/reloads have already occurred by the time we do this
          -- analysis.
          -- XXX Deprecated warning is puzzling: what label are we
          -- supposed to use?
          -- ToDo: With a bit more cleverness here, we can avoid
          -- disappointment and heartbreak associated with the inability
          -- to inline into CmmCall and CmmForeignCall by
          -- over-estimating the usage to be ManyUse.
          last n f = gen_kill n (joinOutFacts usageLattice n f)
          gen_kill :: WithRegUsage CmmNode e x -> UsageMap -> UsageMap
          gen_kill a = gen a . kill a
          gen :: WithRegUsage CmmNode e x -> UsageMap -> UsageMap
          gen  a f = foldRegsUsed increaseUsage f a
          kill :: WithRegUsage CmmNode e x -> UsageMap -> UsageMap
          kill a f = foldRegsDefd delFromUFM f a
          increaseUsage f r = addToUFM_C combine f r SingleUse
            where combine _ _ = ManyUse

usageRewrite :: BwdRewrite FuelUniqSM (WithRegUsage CmmNode) UsageMap
usageRewrite = mkBRewrite3 first middle last
    where first  _ _ = return Nothing
          middle :: Monad m => WithRegUsage CmmNode O O -> UsageMap -> m (Maybe (Graph (WithRegUsage CmmNode) O O))
          middle (Plain (CmmAssign (CmmLocal l) e)) f
                     = return . Just
                     $ case lookupUFM f l of
                            Nothing    -> emptyGraph
                            Just usage -> mkMiddle (AssignLocal l e usage)
          middle _ _ = return Nothing
          last   _ _ = return Nothing

type CmmGraphWithRegUsage = GenCmmGraph (WithRegUsage CmmNode)
annotateUsage :: CmmGraph -> FuelUniqSM (CmmGraphWithRegUsage)
annotateUsage vanilla_g =
    let g = modifyGraph liftRegUsage vanilla_g
    in liftM fst $ dataflowPassBwd g [(g_entry g, fact_bot usageLattice)] $
                                   analRewBwd usageLattice usageTransfer usageRewrite

----------------------------------------------------------------
--- Assignment tracking

-- The idea is to maintain a map of local registers do expressions,
-- such that the value of that register is the same as the value of that
-- expression at any given time.  We can then do several things,
-- as described by Assignment.

-- Assignment describes the various optimizations that are valid
-- at a given point in the program.
data Assignment =
-- This assignment can always be inlined.  It is cheap or single-use.
                  AlwaysInline CmmExpr
-- This assignment should be sunk down to its first use.  (This will
-- increase code size if the register is used in multiple control flow
-- paths, but won't increase execution time, and the reduction of
-- register pressure is worth it.)
                | AlwaysSink CmmExpr
-- We cannot safely optimize occurrences of this local register. (This
-- corresponds to top in the lattice structure.)
                | NeverOptimize

-- Extract the expression that is being assigned to
xassign :: Assignment -> Maybe CmmExpr
xassign (AlwaysInline e) = Just e
xassign (AlwaysSink e)   = Just e
xassign NeverOptimize    = Nothing

-- Extracts the expression, but only if they're the same constructor
xassign2 :: (Assignment, Assignment) -> Maybe (CmmExpr, CmmExpr)
xassign2 (AlwaysInline e, AlwaysInline e') = Just (e, e')
xassign2 (AlwaysSink e, AlwaysSink e')     = Just (e, e')
xassign2 _ = Nothing

-- Note: We'd like to make decisions about "not optimizing" as soon as
-- possible, because this will make running the transfer function more
-- efficient.
type AssignmentMap = UniqFM Assignment

assignmentLattice :: DataflowLattice AssignmentMap
assignmentLattice = DataflowLattice "assignments for registers" emptyUFM (joinUFM add)
    where add _ (OldFact old) (NewFact new)
            = case (old, new) of
                (NeverOptimize, _) -> (NoChange,   NeverOptimize)
                (_, NeverOptimize) -> (SomeChange, NeverOptimize)
                (xassign2 -> Just (e, e'))
                    | e == e'   -> (NoChange, old)
                    | otherwise -> (SomeChange, NeverOptimize)
                _ -> (SomeChange, NeverOptimize)

-- Deletes sinks from assignment map, because /this/ is the place
-- where it will be sunk to.
deleteSinks :: UserOfLocalRegs n => n -> AssignmentMap -> AssignmentMap
deleteSinks n m = foldRegsUsed (adjustUFM f) m n
  where f (AlwaysSink _) = NeverOptimize
        f old = old

-- Invalidates any expressions that use a register.
invalidateUsersOf :: CmmReg -> AssignmentMap -> AssignmentMap
-- foldUFM_Directly :: (Unique -> elt -> a -> a) -> a -> UniqFM elt -> a
invalidateUsersOf reg m = foldUFM_Directly f m m -- [foldUFM performance]
    where f u (xassign -> Just e) m | reg `regUsedIn` e = addToUFM_Directly m u NeverOptimize
          f _ _ m = m
{- This requires the entire spine of the map to be continually rebuilt,
 - which causes crazy memory usage!
invalidateUsersOf reg = mapUFM (invalidateUsers' reg)
  where invalidateUsers' reg (xassign -> Just e) | reg `regUsedIn` e = NeverOptimize
        invalidateUsers' _ old = old
-}

-- Note [foldUFM performance]
-- These calls to fold UFM no longer leak memory, but they do cause
-- pretty killer amounts of allocation.  So they'll be something to
-- optimize; we need an algorithmic change to prevent us from having to
-- traverse the /entire/ map continually.

middleAssignment :: WithRegUsage CmmNode O O -> AssignmentMap -> AssignmentMap

-- Algorithm for annotated assignments:
--  1. Delete any sinking assignments that were used by this instruction
--  2. Add the assignment to our list of valid local assignments with
--     the correct optimization policy.
--  3. Look for all assignments that reference that register and
--     invalidate them.
middleAssignment n@(AssignLocal r e usage) assign
    = invalidateUsersOf (CmmLocal r) . add . deleteSinks n $ assign
      where add m = addToUFM m r
                  $ case usage of
                        SingleUse -> AlwaysInline e
                        ManyUse   -> decide e
            decide CmmLit{}       = AlwaysInline e
            decide CmmReg{}       = AlwaysInline e
            decide CmmLoad{}      = AlwaysSink e
            decide CmmStackSlot{} = AlwaysSink e
            decide CmmMachOp{}    = AlwaysSink e
            -- We'll always inline simple operations on the global
            -- registers, to reduce register pressure: Sp - 4 or Hp - 8
            -- EZY: Justify this optimization more carefully.
            decide CmmRegOff{}    = AlwaysInline e

-- Algorithm for unannotated assignments of global registers:
-- 1. Delete any sinking assignments that were used by this instruction
-- 2. Look for all assignments that reference this register and
--    invalidate them.
middleAssignment (Plain n@(CmmAssign reg@(CmmGlobal _) _)) assign
    = invalidateUsersOf reg . deleteSinks n $ assign

-- Algorithm for unannotated assignments of *local* registers: do
-- nothing (it's a reload, so no state should have changed)
middleAssignment (Plain (CmmAssign (CmmLocal _) _)) assign = assign

-- Algorithm for stores:
--  1. Delete any sinking assignments that were used by this instruction
--  2. Look for all assignments that load from memory locations that
--     were clobbered by this store and invalidate them.
middleAssignment (Plain n@(CmmStore lhs rhs)) assign
    = let m = deleteSinks n assign
      in foldUFM_Directly f m m -- [foldUFM performance]
      where f u (xassign -> Just x) m | (lhs, rhs) `clobbers` (u, x) = addToUFM_Directly m u NeverOptimize
            f _ _ m = m
{- Also leaky
    = mapUFM_Directly p . deleteSinks n $ assign
      -- ToDo: There's a missed opportunity here: even if a memory
      -- access we're attempting to sink gets clobbered at some
      -- location, it's still /better/ to sink it to right before the
      -- point where it gets clobbered.  How might we do this?
      -- Unfortunately, it's too late to change the assignment...
      where p r (xassign -> Just x) | (lhs, rhs) `clobbers` (r, x) = NeverOptimize
            p _ old = old
-}

-- Assumption: Unsafe foreign calls don't clobber memory
-- Since foreign calls clobber caller saved registers, we need
-- invalidate any assignments that reference those global registers.
-- This is kind of expensive. (One way to optimize this might be to
-- store extra information about expressions that allow this and other
-- checks to be done cheaply.)
middleAssignment (Plain n@(CmmUnsafeForeignCall{})) assign
    = deleteCallerSaves (foldRegsDefd (\m r -> addToUFM m r NeverOptimize) (deleteSinks n assign) n)
    where deleteCallerSaves m = foldUFM_Directly f m m
          f u (xassign -> Just x) m | wrapRecExpf g x False = addToUFM_Directly m u NeverOptimize
          f _ _ m = m
          g (CmmReg (CmmGlobal r)) _      | callerSaves r = True
          g (CmmRegOff (CmmGlobal r) _) _ | callerSaves r = True
          g _ b = b

middleAssignment (Plain (CmmComment {})) assign
    = assign

-- Assumptions:
--  * Writes using Hp do not overlap with any other memory locations
--    (An important invariant being relied on here is that we only ever
--    use Hp to allocate values on the heap, which appears to be the
--    case given hpReg usage, and that our heap writing code doesn't
--    do anything stupid like overlapping writes.)
--  * Stack slots do not overlap with any other memory locations
--  * Stack slots for different areas do not overlap
--  * Stack slots within the same area and different offsets may
--    overlap; we need to do a size check (see 'overlaps').
--  * Register slots only overlap with themselves.  (But this shouldn't
--    happen in practice, because we'll fail to inline a reload across
--    the next spill.)
--  * Non stack-slot stores always conflict with each other.  (This is
--    not always the case; we could probably do something special for Hp)
clobbers :: (CmmExpr, CmmExpr) -- (lhs, rhs) of clobbering CmmStore
         -> (Unique,  CmmExpr) -- (register, expression) that may be clobbered
         -> Bool
clobbers (CmmRegOff (CmmGlobal Hp) _, _) (_, _) = False
clobbers (CmmReg (CmmGlobal Hp), _) (_, _) = False
-- ToDo: Also catch MachOp case
clobbers (ss@CmmStackSlot{}, CmmReg (CmmLocal r)) (u, CmmLoad (ss'@CmmStackSlot{}) _)
    | getUnique r == u, ss == ss' = False -- No-op on the stack slot (XXX: Do we need this special case?)
clobbers (CmmStackSlot (CallArea a) o, rhs) (_, expr) = f expr
    where f (CmmLoad (CmmStackSlot (CallArea a') o') t)
            = (a, o, widthInBytes (cmmExprWidth rhs)) `overlaps` (a', o', widthInBytes (typeWidth t))
          f (CmmLoad e _)    = containsStackSlot e
          f (CmmMachOp _ es) = or (map f es)
          f _                = False
          -- Maybe there's an invariant broken if this actually ever
          -- returns True
          containsStackSlot (CmmLoad{})      = True -- load of a load, all bets off
          containsStackSlot (CmmMachOp _ es) = or (map containsStackSlot es)
          containsStackSlot (CmmStackSlot{}) = True
          containsStackSlot _ = False
clobbers (CmmStackSlot (RegSlot l) _, _) (_, expr) = f expr
    where f (CmmLoad (CmmStackSlot (RegSlot l') _) _) = l == l'
          f _ = False
clobbers _ (_, e) = f e
    where f (CmmLoad (CmmStackSlot _ _) _) = False
          f (CmmLoad{}) = True -- conservative
          f (CmmMachOp _ es) = or (map f es)
          f _ = False

-- Check for memory overlapping.
-- Diagram:
--      4      8     12
--      s -w-  o
--      [ I32  ]
--      [    F64     ]
--      s'   -w'-    o'
type CallSubArea = (AreaId, Int, Int) -- area, offset, width
overlaps :: CallSubArea -> CallSubArea -> Bool
overlaps (a, _, _) (a', _, _) | a /= a' = False
overlaps (_, o, w) (_, o', w') =
    let s  = o  - w
        s' = o' - w'
    in (s' < o) && (s < o) -- Not LTE, because [ I32  ][ I32  ] is OK

lastAssignment :: WithRegUsage CmmNode O C -> AssignmentMap -> [(Label, AssignmentMap)]
-- Variables are dead across calls, so invalidating all mappings is justified
lastAssignment (Plain (CmmCall _ (Just k) _ _ _)) assign = [(k, mapUFM (const NeverOptimize) assign)]
lastAssignment (Plain (CmmForeignCall {succ=k}))  assign = [(k, mapUFM (const NeverOptimize) assign)]
lastAssignment l assign = map (\id -> (id, deleteSinks l assign)) $ successors l

assignmentTransfer :: FwdTransfer (WithRegUsage CmmNode) AssignmentMap
assignmentTransfer = mkFTransfer3 (flip const) middleAssignment ((mkFactBase assignmentLattice .) . lastAssignment)

assignmentRewrite :: FwdRewrite FuelUniqSM (WithRegUsage CmmNode) AssignmentMap
assignmentRewrite = mkFRewrite3 first middle last
    where
        first _ _ = return Nothing
        middle :: WithRegUsage CmmNode O O -> AssignmentMap -> GenCmmReplGraph (WithRegUsage CmmNode) O O
        middle (Plain m) assign = return $ rewrite assign (precompute assign m) mkMiddle m
        middle (AssignLocal l e u) assign = return $ rewriteLocal assign (precompute assign (CmmAssign (CmmLocal l) e)) l e u
        last (Plain l) assign = return $ rewrite assign (precompute assign l) mkLast l
        -- Tuple is (inline?, reloads)
        precompute :: AssignmentMap -> CmmNode O x -> (Bool, [WithRegUsage CmmNode O O])
        precompute assign n = foldRegsUsed f (False, []) n -- duplicates are harmless
            where f (i, l) r = case lookupUFM assign r of
                                Just (AlwaysSink e)   -> (i, (Plain (CmmAssign (CmmLocal r) e)):l)
                                Just (AlwaysInline _) -> (True, l)
                                Just NeverOptimize    -> (i, l)
                                -- This case can show up when we have
                                -- limited optimization fuel.
                                Nothing -> (i, l)
        rewrite :: AssignmentMap
                -> (Bool, [WithRegUsage CmmNode O O])
                -> (WithRegUsage CmmNode O x -> Graph (WithRegUsage CmmNode) O x)
                -> CmmNode O x
                -> Maybe (Graph (WithRegUsage CmmNode) O x)
        rewrite _ (False, []) _ _ = Nothing
        -- Note [CmmCall Inline Hack]
        -- Conservative hack: don't do any inlining on what will
        -- be translated into an OldCmm CmmCalls, since the code
        -- produced here tends to be unproblematic and I need to write
        -- lint passes to ensure that we don't put anything in the
        -- arguments that could be construed as a global register by
        -- some later translation pass.  (For example, slots will turn
        -- into dereferences of Sp).  See [Register parameter passing].
        -- ToDo: Fix this up to only bug out if all inlines were for
        -- CmmExprs with global registers (we can't use the
        -- straightforward mapExpDeep call, in this case.) ToDo: We miss
        -- an opportunity here, where all possible inlinings should
        -- instead be sunk.
        rewrite _ (True, []) _ n | not (inlinable n) = Nothing -- see [CmmCall Inline Hack]
        rewrite assign (i, xs) mk n = Just $ mkMiddles xs <*> mk (Plain (inline i assign n))

        rewriteLocal :: AssignmentMap
                     -> (Bool, [WithRegUsage CmmNode O O])
                     -> LocalReg -> CmmExpr -> RegUsage
                     -> Maybe (Graph (WithRegUsage CmmNode) O O)
        rewriteLocal _ (False, []) _ _ _ = Nothing
        rewriteLocal assign (i, xs) l e u = Just $ mkMiddles xs <*> mkMiddle n'
            where n' = AssignLocal l e' u
                  e' = if i then wrapRecExp (inlineExp assign) e else e
            -- inlinable check omitted, since we can always inline into
            -- assignments.

        inline :: Bool -> AssignmentMap -> CmmNode e x -> CmmNode e x
        inline False _ n = n
        inline True  _ n | not (inlinable n) = n -- see [CmmCall Inline Hack]
        inline True assign n = mapExpDeep (inlineExp assign) n

        inlineExp assign old@(CmmReg (CmmLocal r))
          = case lookupUFM assign r of
              Just (AlwaysInline x) -> x
              _ -> old
        inlineExp assign old@(CmmRegOff (CmmLocal r) i)
          = case lookupUFM assign r of
              Just (AlwaysInline x) ->
                case x of
                    (CmmRegOff r' i') -> CmmRegOff r' (i + i')
                    _ -> CmmMachOp (MO_Add rep) [x, CmmLit (CmmInt (fromIntegral i) rep)]
                          where rep = typeWidth (localRegType r)
              _ -> old
        inlineExp _ old = old

        inlinable :: CmmNode e x -> Bool
        inlinable (CmmCall{}) = False
        inlinable (CmmForeignCall{}) = False
        inlinable (CmmUnsafeForeignCall{}) = False
        inlinable _ = True

rewriteAssignments :: CmmGraph -> FuelUniqSM CmmGraph
rewriteAssignments g = do
  g'  <- annotateUsage g
  g'' <- liftM fst $ dataflowPassFwd g' [(g_entry g, fact_bot assignmentLattice)] $
                                     analRewFwd assignmentLattice assignmentTransfer assignmentRewrite
  return (modifyGraph eraseRegUsage g'')

-- ToDo: Outputable instance for UsageMap and AssignmentMap
