{- |

This module contains an executable, type ignoring small-step semantics for
Haskell Core with lazyness.

It has a heap, a current expression and a stack, and closely follows Sestoft’s
semantics.

Naming is handled the same way as in GHC: When we enter a binder (which we do
when applying a lambda, when moving let-bound things onto the heap and in a
case expression), we freshen the names as required.

This semantics ignores types. This means that intermediate configurations will
not be well-typed.

The semantics ignores the 'IdInfo' of GHC variables. It remains to be seen if
some of the convenience functions (e.g. exprIsHNF and exprIsTrivial) use them,
and if that causes problems.

The semantics handles closed terms. There is no support for a module structure
(although that would not be hard to add).

Relatedly, primitive operations (which are manifest simply as free global
variables) are not supported. It might be possible to parametrize over their
execution.


-}
module GHC.SmallStep
    ( Conf, Heap, Stack, StackElem(..)
    , step
    )
    where

import FastString
import CoreSyn
import CoreSubst
import CoreUtils
import Id
import VarEnv
import Unique
import Outputable
import DataCon

-- | The configuration of the semantics.
--
-- Invariant:
--
--  * All free variables are bound in the heap
type Conf = (Heap, CoreExpr, Stack)

-- | The heap of a 'Conf'.
type Heap = VarEnv (Var, CoreExpr)
-- We need the Var to build an InScopeSet

-- | The stack of a 'Conf'
type Stack = [StackElem]

-- | Stack elements
data StackElem
    = ApplyTo CoreExpr        -- a pending function application
    | Alts CoreBndr [CoreAlt] -- a pending case analysis
    | Update Id               -- a pending thunk update

in_scope :: Heap -> InScopeSet
in_scope = mkInScopeSet . mapVarEnv fst

addToHeap :: Id -> CoreExpr -> Heap -> Heap
addToHeap v e heap = extendVarEnv heap v (v,e)

addManyToHeap :: [Id] -> [CoreExpr] -> Heap -> Heap
addManyToHeap vs es = foldr (.) id (zipWith addToHeap vs es)

-- | The small-step semantics
--
-- This calculates the next step of a configuration, if there is one.
--
-- If there is no step, then this may have one of three reasons:
--
--  * The configuration is fully evaluated.
--  * The configuration is stuck (which should not happen for well-typed,
--    closed terms)
--  * There is a bug in the semantics.
step :: Conf -> Maybe Conf

-- the transparent cases
step (heap, Tick _ e, s)              = step (heap, e, s)
step (heap, App e a, s) | isTypeArg a = step (heap, e, s)
step (heap, Cast e _, s)              = step (heap, e, s)

-- Variable (evaluated)
step (heap, Var v, s) | Just (_, e) <- lookupVarEnv heap v, exprIsHNF e
    = Just (heap, e, s)

-- Variable (unevaluated)
step (heap, Var v, s) | Just (_, e) <- lookupVarEnv heap v
    = Just (heap, e, Update v : s)

step (heap, e, Update v : s) | exprIsHNF e
    = Just (addToHeap v e heap, e, s)

-- Function application
step (heap, App e a, s)
    = Just (heap, e, ApplyTo a : s)

-- Because terms are not in A-Normal form, we have to ensure sharing here.l
-- So let us have two rules, one for trivial arguments and one for non-trivial ones.
step (heap, Lam v e, ApplyTo a : s) | exprIsTrivial a
    = Just (heap, substExpr empty subst e, s)
  where
    subst = extendSubst (mkEmptySubst (in_scope heap)) v a

step (heap, Lam v e, ApplyTo a : s)
    = Just (addToHeap fresh a heap, substExpr empty subst e, s)
  where
    subst = extendSubstWithVar (mkEmptySubst (in_scope heap)) v fresh

    fresh_tmpl = mkSysLocal (fsLit "arg") (mkBuiltinUnique 1) (exprType a)
    fresh = uniqAway (in_scope heap) fresh_tmpl

-- Let expression (non-recursive)
step (heap, Let (NonRec v rhs) e, s)
    = Just (addToHeap v' rhs heap, e', s)
  where
    subst0 = mkEmptySubst (in_scope heap)
    (subst1, v') = substBndr subst0 v
    e' = substExpr empty subst1 e

-- Let expression (non-recursive)
step (heap, Let (Rec pairs) e, s)
    = Just (addManyToHeap vars' rhss' heap, e', s)
  where
    subst0 = mkEmptySubst (in_scope heap)
    (vars, rhss) = unzip pairs
    (subst1, vars') = substRecBndrs subst0 vars
        -- we could use substBndrs if that is easier, as we do not care about
        -- the idInfo
    rhss' = map (substExpr empty subst1) rhss
    e' = substExpr empty subst1 e

-- Case expressions
step (heap, Case e b _ alts, s)
    = Just (heap, e, Alts b alts : s)

step (heap, val, Alts b [(DEFAULT, [], rhs)] : s) | exprIsHNF val
    = let rhs' = substExpr empty subst1 rhs
          heap' = addToHeap b val heap
      in  Just (heap', rhs', s)
  where
    subst0 = mkEmptySubst (in_scope heap)
    (subst1, b') = substBndr subst0 b

step (heap, Lit l, Alts b alts : s)
    | Just (_, [], rhs) <- findAlt (LitAlt l) alts
    = let rhs' = substExpr empty subst1 rhs
          heap' = addToHeap b (Lit l) heap
      in  Just (heap', rhs', s)
  where
    subst0 = mkEmptySubst (in_scope heap)
    (subst1, b') = substBndr subst0 b

step (heap, val, Alts b alts : s)
    | Just (dc, args) <- isDataConApp val
    , Just (_, pats, rhs) <- findAlt (DataAlt dc) alts
    = let val_pats = filter isId pats
          (subst2, pats') = substBndrs subst1 val_pats
          rhs' = substExpr empty subst2 rhs
          heap' = addManyToHeap pats' args $ addToHeap b val heap
      in  Just (heap', rhs', s)
  where
    subst0 = mkEmptySubst (in_scope heap)
    (subst1, b') = substBndr subst0 b

-- Makes sure the DataCon is fully applied, and return only the value arguments
isDataConApp :: CoreExpr -> Maybe (DataCon, [CoreArg])
isDataConApp = go []
  where go args (App e a) | isTypeArg a = go args e
        go args (App e a) = go (a:args) e
        go args (Var v) | Just dc <- isDataConWorkId_maybe v
                        , dataConRepArity dc == length args
                        = Just (dc, args)
        go _ _ = Nothing
