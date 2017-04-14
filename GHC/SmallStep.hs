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
some of the functions from the GHC API that we use look at them, and if that
causes problems.

The semantics handles closed terms. There is no support for a module structure
(although that would not be hard to add).

Relatedly, primitive operations (which are manifest simply as free global
variables) are not supported. It might be possible to parametrize over their
execution.


-}
module GHC.SmallStep
    ( -- * Trivial expressions and Values
      TrivialArg, exprIsTrivial'
    , Value(..), isValue, isValue_maybe
      -- * Configurations
    , Conf, Heap, Stack, StackElem(..)
      -- * The small-steps semantics
    , initConf
    , Step(..)
    , step
    )
    where

import FastString
import CoreSyn
import CoreSubst
import CoreUtils hiding (exprIsTrivial, exprIsHNF)
import Id
import VarEnv
import Unique
import Outputable
import DataCon
import Literal
import Coercion (Coercion)
import Data.Maybe

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

instance Outputable StackElem where
    ppr (ApplyTo e) = char '$' <+> ppr e
    ppr (Alts b alts) = text "as" <+> ppr b <+> braces (ppr alts)
    ppr (Update v) = char '#' <+> ppr v

in_scope :: Heap -> InScopeSet
in_scope = mkInScopeSet . mapVarEnv fst

addToHeap :: Id -> CoreExpr -> Heap -> Heap
addToHeap v e heap = extendVarEnv heap v (v,e)

addManyToHeap :: [Id] -> [CoreExpr] -> Heap -> Heap
addManyToHeap vs es = foldr (.) id (zipWith addToHeap vs es)

-- | Initial configuration (empty heap and stack)
initConf :: CoreExpr -> Conf
initConf e = (emptyVarEnv, e, [])


-- | A trivial argument
type TrivialArg = CoreArg

-- | A Value
data Value = DataConApp DataCon [TrivialArg]
             -- ^ Saturated data con application (trivial value arguments only)
           | LitVal Literal
             -- ^ Literal
           | LamVal Id CoreExpr
             -- ^ A value lambda
           | CoercionVal Coercion
             -- ^ Coercion token. Can be passed around, but nothing can be done to it.

valueToExpr :: Value -> CoreExpr
valueToExpr (DataConApp dc args) = mkConApp dc args
valueToExpr (LitVal l)           = Lit l
valueToExpr (LamVal v e)         = Lam v e
valueToExpr (CoercionVal co)     = Coercion co

-- | An expression is trivial if it can be passed to a function: Variables,
-- literals and coercions.
exprIsTrivial' :: CoreExpr -> Bool
exprIsTrivial' (Tick _ e)               = exprIsTrivial' e
exprIsTrivial' (App e a) | isTypeArg a  = exprIsTrivial' e
exprIsTrivial' (Lam v e) | not (isId v) = exprIsTrivial' e
exprIsTrivial' (Cast e _)               = exprIsTrivial' e

exprIsTrivial' (Var _)      = True
exprIsTrivial' (Lit _)      = True
exprIsTrivial' (Coercion _) = True
exprIsTrivial' _ = False

-- | An expression is a value if it is a data constructor fully applied to
-- trivial arguments, or a literal, or a value lambda, or a coercion.
--
-- Why only to trivial arguments? Because non-trivial arguments need to be
-- bound on the heap before they can be “stored” in the data constructor, so
-- there is work to be done. Without this provision, sharing would not work as
-- expected.
isValue :: CoreExpr -> Bool
isValue e = isJust (isValue_maybe e)

-- | See 'isValue'
isValue_maybe :: CoreExpr -> Maybe Value
isValue_maybe (Tick _ e)               = isValue_maybe e
isValue_maybe (App e a) | isTypeArg a  = isValue_maybe e
isValue_maybe (Lam v e) | not (isId v) = isValue_maybe e
isValue_maybe (Cast e _)               = isValue_maybe e

isValue_maybe (Lit l)                               = Just (LitVal l)
isValue_maybe (Coercion c)                          = Just (CoercionVal c)
isValue_maybe (Lam v e)                             = Just (LamVal v e)
isValue_maybe e | Just (dc, args) <- isDataConApp e
                , all exprIsTrivial' args = Just (DataConApp dc args)

isValue_maybe _ = Nothing

-- | A small step configuration can either be stuck (with a helpful error
-- message), done (fully evaluated, empty stack) or take a step.
data Step a = Error String | Done | Step a

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
step :: Conf -> Step Conf

-- the transparent cases
step (heap, Tick _ e, s)               = step (heap, e, s)
step (heap, App e a, s) | isTypeArg a  = step (heap, e, s)
step (heap, Lam v e, s) | not (isId v) = step (heap, e, s)
step (heap, Cast e _, s)               = step (heap, e, s)

-- The value cases
step (heap, e, s) | Just val <- isValue_maybe  e = valStep (heap, val, s)

-- The non-value cases

-- Variable (non-nullary data constructor)
step (heap, Var v, s)
    | Just dc <- isDataConWorkId_maybe v
    , dataConRepArity dc > 0
    = Step (heap, etaExpandDCWorker dc, s)

-- Variable (evaluated)
step (heap, Var v, s) | Just (_, e) <- lookupVarEnv heap v, isValue e
    = Step (heap, e, s)

-- Variable (unevaluated)
step (heap, Var v, s) | Just (_, e) <- lookupVarEnv heap v
    = Step (heap, e, Update v : s)

-- Variable (unbound)
step (heap, Var v, s) = Error "unbound variable"

-- Function application
step (heap, App e a, s)
    = Step (heap, e, ApplyTo a : s)

-- Let expression (non-recursive)
step (heap, Let (NonRec v rhs) e, s)
    = Step (addToHeap v' rhs heap, e', s)
  where
    subst0 = mkEmptySubst (in_scope heap)
    (subst1, v') = substBndr subst0 v
    e' = substExpr empty subst1 e

-- Let expression (non-recursive)
step (heap, Let (Rec pairs) e, s)
    = Step (addManyToHeap vars' rhss' heap, e', s)
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
    = Step (heap, e, Alts b alts : s)

step (heap, Type _, s) = Error "type expression in control position"
step _ = Error "Should be unreachable"

valStep :: (Heap, Value, Stack) -> Step Conf
valStep (heap, val, []) = Done

valStep (heap, val, Update v : s)
    = Step (addToHeap v (valueToExpr val) heap, valueToExpr val, s)

-- Because terms are not in A-Normal form, we have to ensure sharing here.l
-- So let us have two rules, one for trivial arguments and one for non-trivial ones.
valStep (heap, LamVal v e, ApplyTo a : s) | exprIsTrivial' a
    = Step (heap, substExpr empty subst e, s)
  where
    subst = extendSubst (mkEmptySubst (in_scope heap)) v a

valStep (heap, LamVal v e, ApplyTo a : s)
    = Step (addToHeap fresh a heap, substExpr empty subst e, s)
  where
    subst = extendSubstWithVar (mkEmptySubst (in_scope heap)) v fresh

    fresh_tmpl = mkSysLocal (fsLit "arg") (mkBuiltinUnique 1) (exprType a)
    fresh = uniqAway (in_scope heap) fresh_tmpl

valStep (heap, val, ApplyTo a : s)
    = Error "non-function applied to argument"

valStep (heap, val, Alts b [] : s)
    = Error "empty case"

valStep (heap, val, Alts b [(DEFAULT, [], rhs)] : s)
    = let rhs' = substExpr empty subst1 rhs
          heap' = addToHeap b' (valueToExpr val) heap
      in  Step (heap', rhs', s)
  where
    subst0 = mkEmptySubst (in_scope heap)
    (subst1, b') = substBndr subst0 b

valStep (heap, LitVal l, Alts b alts : s)
    | Just (_, [], rhs) <- findAlt (LitAlt l) alts
    = let rhs' = substExpr empty subst1 rhs
          heap' = addToHeap b' (Lit l) heap
      in  Step (heap', rhs', s)
  where
    subst0 = mkEmptySubst (in_scope heap)
    (subst1, b') = substBndr subst0 b

valStep (heap, LitVal l, Alts b alts : s)
    = Error "literal not found in alts"

valStep (heap, val@(DataConApp dc args), Alts b alts : s)
    | Just (_, pats, rhs) <- findAlt (DataAlt dc) alts
    = let val_pats = filter isId pats
          (subst2, pats') = substBndrs subst1 val_pats
          rhs' = substExpr empty subst2 rhs
          heap' = addManyToHeap pats' args $ addToHeap b' (valueToExpr val) heap
      in  Step (heap', rhs', s)
  where
    subst0 = mkEmptySubst (in_scope heap)
    (subst1, b') = substBndr subst0 b

valStep (heap, val@(DataConApp dc args), Alts b alts : s)
    = Error "data con not found in alts"

valStep (heap, val, Alts b alts : s)
    = Error "non-datacon scrutinized"


-- |
--
-- An unsaturated DataCon worker is actually a function, taking enough arguments,
-- and then applying them to the DataCon worker. Only then isValue will trigger on it.
--
-- So treat an non-nullary DataCon worker as if the environment had an entry
-- that does the eta-expansion.
--
-- This would not be necessary if we assumed CorePrep output in our terms.
etaExpandDCWorker :: DataCon -> CoreExpr
etaExpandDCWorker dc = mkLams params (mkConApp dc (map Var params))
  where params = zipWith (\n t -> mkSysLocalOrCoVar (fsLit "eta") (mkBuiltinUnique n) t)
                         [1..]
                         (dataConRepArgTys dc)

-- Makes sure the DataCon is fully applied, and return only the value arguments
isDataConApp :: CoreExpr -> Maybe (DataCon, [CoreArg])
isDataConApp = go []
  where go args (App e a) | isTypeArg a = go args e
        go args (App e a) = go (a:args) e
        go args (Var v) | Just dc <- isDataConWorkId_maybe v
                        , dataConRepArity dc == length args
                        = Just (dc, args)
        go _ _ = Nothing
