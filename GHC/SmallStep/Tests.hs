module GHC.SmallStep.Tests (factExpr) where

import CoreSyn hiding (mkLet)
import CoreUtils
import MkId
import BasicTypes
import Id
import Type
import TyCon
import Name
import TysWiredIn
import TysWiredIn
import FastString
import Literal
import Unique
import DataCon

-- | A core expression of type Nat that evaluates to fact n in unary presentation.
factExpr :: Int -> CoreExpr
factExpr n =
    mkRFun plus [x,y] (
        Case (Var x) b natTy [(DataAlt dcZero, [],  Var y)
                             ,(DataAlt dcSucc, [z], Var dcSuccWrk `App` (Var plus `App` Var z `App` Var y))]
    ) $
    mkRFun times [x,y] (
        Case (Var x) b natTy [(DataAlt dcZero, [],  Var dcZeroWrk)
                             ,(DataAlt dcSucc, [z], Var plus `App` Var y `App` (Var times `App` Var z `App` Var y))]
    ) $
    mkRFun fact [x] (
        Case (Var x) b natTy [(DataAlt dcZero, [],  Var dcSuccWrk `App` Var dcZeroWrk)
                             ,(DataAlt dcSucc, [z], Var times `App` Var b `App` (Var fact `App` Var z))]
    ) $
    mkRFun deepseq [x,y] (
        Case (Var x) b natTy [(DataAlt dcZero, [],  Var y)
                             ,(DataAlt dcSucc, [z], Var deepseq `App` Var z `App` Var y)]
    ) $
    mkLet x (Var fact `App` ((iterate (Var dcSuccWrk `App`) (Var dcZeroWrk)) !! n)) $
    Var deepseq `App` Var x `App` Var x


-- Build IDs. use mkTemplateLocal, more predictable than proper uniques
plus, times, deepseq, fact, x, y, z, b:: Id
[plus, times, deepseq, fact, x, y, z, b] = mkTestIds
    (words "plus times deepseq fact x y z b")
    [ mkFunTys [natTy, natTy] natTy
    , mkFunTys [natTy, natTy] natTy
    , mkFunTys [natTy, natTy] natTy
    , mkFunTys [natTy] natTy
    , natTy
    , natTy
    , natTy
    , natTy
    ]

-- Build DataCons. This is involved

dcZero :: DataCon
dcZero = mkDataCon
    dcZeroName
    False
    dcZeroName
    [] [] [] [] [] [] [] []
    natTy
    NoRRI
    natTyCon
    []
    dcZeroWrk
    NoDataConRep

dcZeroName :: Name
dcZeroName = mkSystemName (mkBuiltinUnique 100) (mkDataOcc "Zero")

dcZeroWrkName :: Name
dcZeroWrkName = mkSystemName (mkBuiltinUnique 101) (mkVarOcc "Zero")

dcZeroWrk :: Id
dcZeroWrk = mkDataConWorkId dcZeroWrkName dcZero

dcSucc :: DataCon
dcSucc = mkDataCon
    dcSuccName
    False
    dcSuccName
    [] [] [] [] [] [] [] [natTy]
    natTy
    NoRRI
    natTyCon
    []
    dcSuccWrk
    NoDataConRep

dcSuccName :: Name
dcSuccName = mkSystemName (mkBuiltinUnique 102) (mkDataOcc "Succ")

dcSuccWrkName :: Name
dcSuccWrkName = mkSystemName (mkBuiltinUnique 103) (mkVarOcc "Succ")

dcSuccWrk :: Id
dcSuccWrk = mkDataConWorkId dcSuccWrkName dcSucc

natTy :: Type
natTy = mkTyConTy natTyCon

natTcName :: Name
natTcName = mkSystemName (mkBuiltinUnique 104) (mkTcOcc "Nat")

natTyCon :: TyCon
natTyCon = mkAlgTyCon
    natTcName
    []
    liftedTypeKind
    []
    Nothing
    []
    (DataTyCon [dcZero, dcSucc] False)
    (VanillaAlgTyCon natTcName)
    False

-- Utilities
mkLApps :: Id -> [Integer] -> CoreExpr
mkLApps v = mkApps (Var v) . map mkLit

mkTestId :: Int -> String -> Type -> Id
mkTestId i s ty = mkSysLocal (mkFastString s) (mkBuiltinUnique i) ty

mkTestIds :: [String] -> [Type] -> [Id]
mkTestIds ns tys = zipWith3 mkTestId [0..] ns tys

mkLet :: Id -> CoreExpr -> CoreExpr -> CoreExpr
mkLet v rhs body = Let (NonRec v rhs) body

mkRLet :: Id -> CoreExpr -> CoreExpr -> CoreExpr
mkRLet v rhs body = Let (Rec [(v, rhs)]) body

mkFun :: Id -> [Id] -> CoreExpr -> CoreExpr -> CoreExpr
mkFun v xs rhs body = mkLet v (mkLams xs rhs) body

mkRFun :: Id -> [Id] -> CoreExpr -> CoreExpr -> CoreExpr
mkRFun v xs rhs body = mkRLet v (mkLams xs rhs) body

mkLit :: Integer -> CoreExpr
mkLit i = Lit (mkLitInteger i intTy)
