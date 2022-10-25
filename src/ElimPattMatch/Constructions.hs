{-# LANGUAGE FlexibleContexts #-}
module ElimPattMatch.Constructions where

import qualified Data.Map as Map
import Text.PrettyPrint

import Data.Maybe (fromMaybe)
import Agda.Utils.Pretty (pretty)
import Agda.Syntax.Internal
import Agda.Syntax.Position
import Agda.Syntax.Scope.Monad (resolveName')
import Agda.TypeChecking.Substitute
import qualified Agda.TypeChecking.Pretty as AP
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Level
import Agda.TypeChecking.CheckInternal
import Agda.TypeChecking.Sort
import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Primitive.Base
import Agda.Syntax.Scope.Base (allKindsOfNames, AbstractName(AbsName), anameName, ResolvedName (DefinedName, ConstructorName))
import qualified Agda.Syntax.Concrete.Name as CN
import Agda.TypeChecking.Monad.Context
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Monad.Signature
import Agda.TypeChecking.Monad.Builtin
import Agda.Syntax.Common
import Agda.Utils.Size
import qualified Agda.Syntax.Concrete.Name as CN
import Agda.Utils.Impossible

import Agda.Utils.List1 (initLast)

import Data.List.NonEmpty (fromList, toList)
import Data.List (elemIndex)
import qualified Data.Set

import Control.Monad.State
import Control.Monad.Trans.Maybe
import Control.Monad

import DkMonad

defaultConHead consName = ConHead{conName = consName,
                                  conDataRecord = IsData,
                                  conInductive = Inductive,
                                  conFields = []}

defaultConInfo = ConOCon

genList 0 = []
genList n = (n - 1) : (genList (n - 1))
genElim n = map (\x -> Apply $ defaultArg $ Var x []) $ genList n

genPattsFromInts l =
          map (\x -> defaultNamedArg $ varP DBPatVar{dbPatVarName = "x", dbPatVarIndex = x}) l

-- remove the first hidden args of the telescope.
-- when given the telescope generated from a constructor type, these are generally the parameters
removeParams EmptyTel = EmptyTel
removeParams tel@(ExtendTel x y) = if argInfoHiding (domInfo x) == Hidden
                                   then removeParams $ unAbs y
                                   else tel
                                        


-- given type D with numPars parameters
-- builds the type D p -> Set_i in the context i : Level, p : Pars
mkMotiveType :: QName -> Int -> TCM Type
-- mkMotiveType :: forall m. (MonadTCM m) => QName -> Int -> m Type
mkMotiveType dataname numPars =
  do
    let dataAppliedToPars = Def dataname $ genElim numPars
    sortDataAppliedToPars <- sortOf dataAppliedToPars
    let returnTy = Sort (Type (Max 0 [Plus 0 (Var numPars [])]))
    sortReturnTy <- sortOf returnTy
    let returnTy' = El{_getSort = sortReturnTy, unEl = returnTy}
    let ty =
          Pi (defaultDom $ El{_getSort = sortDataAppliedToPars, unEl = dataAppliedToPars})
          (NoAbs{absName = "x", unAbs = returnTy'})
    sortTy <- sortOf ty
    return El{_getSort = sortTy, unEl = ty}

-- given type D with numPars parameters
-- build the type (x : D p) -> P x in context i : Level, p : Pars, P : D p -> Set_i
mkEndType :: DkMonad m => QName -> Int -> m Type
mkEndType dataname numPars =
  do
    let dataAppliedToPars = raise 1 $ Def dataname $ genElim numPars
    sortDataAppliedToPars <- liftTCM $ sortOf dataAppliedToPars
    let dataAppliedToPars' = El{_getSort = sortDataAppliedToPars, unEl = dataAppliedToPars}

    let returnTy = Var 1 $ genElim 1
    sortReturnTy <- addContext ("x", defaultDom dataAppliedToPars') $ liftTCM $ sortOf returnTy
--    reportSDoc "toDk.elimPattMatch" 20  $ AP.prettyTCM sortReturnTy
    let returnTy' = El{_getSort= sortReturnTy, unEl= returnTy}
    let ty =
          Pi (defaultDom dataAppliedToPars')
          (Abs{absName = "x", unAbs = returnTy'})

    sortTy <- liftTCM $ sortOf ty
    return El{_getSort = sortTy, unEl = ty}

-- given type D with numPars parameters
-- builds the type (i : Level) -> (p : Pars) -> (P : D p -> Set_i) -> D p -> Set_i
mkBelowType :: DkMonad m => QName -> m Type
mkBelowType qname =
  do
    -- gets parameters telescope
    pars <- theTel <$> (telView =<< defType <$> getConstInfo qname)

    -- tel = i : Level, p : Pars
    tel <- do
      levelType <- liftTCM $ levelType
      return $ ExtendTel (defaultDom levelType) (Abs{absName = "i", unAbs = pars})

    -- tel' = i : Level, p : Pars, P : D p -> Set_i
    tel' <- do
      motiveTy <- liftTCM $ addContext tel $ mkMotiveType qname $ length pars
      return $
        tel `abstract` (ExtendTel (defaultDom motiveTy) Abs{absName =  "P", unAbs = EmptyTel})

    -- TODO : the end universe (Set i) can actually increase when using higher-order recursion
    -- whose indexing type is at universe > 0
    end <- liftTCM $ addContext tel $ raise 1 <$> mkMotiveType qname (length pars)
    let finalTy = telePi_ tel' $ end

    _ <- liftTCM $ checkType' finalTy -- checks it is well-sorted
    reportSDoc "toDk.elimPattMatch.below" 20 $ AP.prettyTCM finalTy
    return finalTy

-- generates the type
-- i -> (p : Pars) -> (P : D p -> Set_i) -> (p : (x : D) -> BelowD P x -> P x) -> (x : D) -> P x
mkPrfBelowType :: DkMonad m => QName -> m Type
mkPrfBelowType qname =
  do
    -- gets parameters telescope
    pars <- theTel <$> (telView =<< defType <$> getConstInfo qname)

    -- tel = i : Level, p : Pars
    tel <- do
      levelType <- liftTCM $ levelType
      return $ ExtendTel (defaultDom levelType) (Abs{absName = "i", unAbs = pars})

    -- tel' = i : Level, p : Pars, P : D p -> Set_i
    tel' <- do
      motiveTy <- liftTCM $ addContext tel $ mkMotiveType qname $ length pars
      return $
        tel `abstract` (ExtendTel (defaultDom motiveTy) Abs{absName =  "P", unAbs = EmptyTel})

    -- generates the singleton tel i : Level, p : Pars, P : D p -> Set_i |- x : D
    -- and the type i : Level, p : Pars, P : D p -> Set_i, x : D |- P x
    TelV{theTel = xD, theCore = pX} <-
      telView =<< (addContext tel' $ mkEndType qname (length pars))

    -- generates the type i : Level, p : Pars, P : D p -> Set_i, x : D |- BelowD P x
    belowP <- do
      reportSDoc "toDk.elimPattMatch.below" 20 $ AP.prettyTCM (tel' `abstract` xD)
      DkState{belowOfData = belowOfData} <- get
      let Just qnameOfBelow = belowOfData qname
      let te = Def qnameOfBelow $ genElim 3
      addContext (tel' `abstract` xD) $
        reportSDoc "toDk.elimPattMatch.below" 20 $ AP.prettyTCM te
      addContext (tel' `abstract` xD) $ typeOfTerm te
    reportSDoc "toDk.elimPattMatch.below" 20 $ return $ text "oi"
    -- tel' = i : Level, p : Pars, P : D p -> Set_i, p : (x : D) -> BelowD P x -> P x
    tel'' <- do
      let belowP' = ExtendTel (defaultDom belowP) Abs{absName =  "", unAbs = EmptyTel}
      let p = telePi_ xD $ telePi_ belowP' $ raise 1 $ pX
      return $ tel' `abstract` (ExtendTel (defaultDom p) Abs{absName =  "p", unAbs = EmptyTel})

    let finalTy = telePi_ (tel'' `abstract` (raise 1 xD)) (raiseFrom 1 1 pX)
    _ <- liftTCM $ checkType' finalTy -- checks it is well-sorted

    reportSDoc "toDk.elimPattMatch.below" 20 $ AP.prettyTCM finalTy
    return finalTy


-- given constructor c : {p : Pars} -> (a : Phi) -> D p,
-- builds type (a : Phi) -> P (c p a) in context i : Level, p : Pars, P : D p -> Set_i
mkCaseMethodType :: QName -> TCM Type
mkCaseMethodType conName =
  do
    consType <- defType <$> getConstInfo conName
    tel' <- theTel <$> telView consType
    -- raise it by one to make space for the P : D pars -> Set_i
    let tel = raise 1 $ removeParams tel'
    let conHead =
          ConHead{conName = conName, conDataRecord = IsData, conInductive = Inductive, conFields = []}
    let conInfo = ConOCon
    let coDom = Var (size tel) [Apply $ defaultArg $ Con conHead conInfo $
                                 map (\x -> Apply $ defaultArg $ Var x []) $ genList $ size tel]
    sort <- addContext tel $ sortOf coDom
    return $ telePi tel El {_getSort = sort, unEl = coDom}

mkCaseType :: DkMonad m => QName -> m Type
mkCaseType qname =
  do
    -- gets constructors
    Datatype{dataCons = cons} <- theDef <$> getConstInfo qname

    -- gets parameters telescope
    pars <- theTel <$> (telView =<< defType <$> getConstInfo qname)

    -- tel = i : Level, p : Pars
    tel <- do
      levelType <- liftTCM $ levelType
      return $ ExtendTel (defaultDom levelType) (Abs{absName = "i", unAbs = pars})

    -- tel' = i : Level, p : Pars, P : D p -> Set_i
    tel' <- do
      motiveTy <- liftTCM $ addContext tel $ mkMotiveType qname $ length pars
      return $
        tel `abstract` (ExtendTel (defaultDom motiveTy) Abs{absName =  "P", unAbs = EmptyTel})


    -- tel'' = i : Level, p : Pars, P : D p -> Set_i, m_j : (a : Phi_j -> P (c_j p a))
    tel'' <- do
      methods <- liftTCM $ addContext tel' $ mapM mkCaseMethodType cons

      let methodsRaised =
            reverse $ fst $
            foldl (\(l, n) x -> ((raise n x, "M_" ++ (show n)) : l, n + 1)) ([], 0) methods

      return $ foldl
        (\acc (ty, s) -> acc `abstract` (ExtendTel (defaultDom ty) Abs{absName=s, unAbs=EmptyTel}))
            tel' methodsRaised

    end <- addContext tel' $ mkEndType qname $ length pars

    let caseType = telePi_ tel'' $ raise (length cons) end   
    _ <- liftTCM $ checkType' caseType -- checks it is well-sorted

    return caseType


-- given a constructor c : ϕ -> D, we return a list containing the arguments Δ of recursive
-- positions Δ -> D in ϕ, along with the indices of such positions in ϕ
mkRecArgsTel :: DkMonad m => QName -> QName -> m [(Int, Telescope)]
mkRecArgsTel dName conName =
  do
    consTel <- theTel <$> (telView =<< defType <$> getConstInfo conName)
    let telList = flattenTel consTel -- list of all entries in consTel, weakened up to consTel

    -- we go through reversed telList and if we find a type of the form Δ -> D, we save Δ
    -- along with its index on the list
    ho_tel <- snd <$>
      foldM
      (\vrec x -> do
          let (n, l) = vrec
          TelV{theTel = tel, theCore = codom} <- telView (unDom x)
          case unEl codom of
            Def qname _ | dName == qname -> return (n + 1, (n, tel) : l)
            _ -> return (n+1,l))
      (0, [])
      (reverse telList)

    -- print to debuging
    _ <- addContext consTel $
      mapM (\x -> reportSDoc "toDk.elimPattMatch.below" 20 $ AP.prettyTCM x) ho_tel

    -- we raise it from Pars, Delta, Phi to Pars, x : P, Delta, Phi
    return $ map (\(n, x) -> (n, raiseFrom (length $ removeParams consTel) 1 x)) ho_tel

typeOfTerm :: DkMonad m => Term -> m Type
typeOfTerm t =
  do
    s <- liftTCM $ sortOf t
    return El{_getSort = s, unEl = t}


-- given types A, B, returns the type A ∧ B
mkProd :: DkMonad m => Type -> Type -> m Type
mkProd a b =
  do
    (la, t_a) <- do
      -- we need to reduce it, because sometimes the sort is not fully computed
      Type la <- reduce $ _getSort a
      return (la, unEl a)

    (lb, t_b) <- do
      Type lb <- reduce $ _getSort b
      return (lb, unEl b)

    -- gets the qname of ∧
    DefinedName _ (AbsName{anameName = prod}) _ <- liftTCM $ resolveName' allKindsOfNames Nothing $
        CN.Qual (CN.simpleName "elimPattPrelude") (CN.QName $ CN.simpleName "∧")

    t <- pure (Def prod []) <#> pure (Level la)
         <#> pure (Level lb)
         <@> pure t_a
         <@> pure t_b

    typeOfTerm t

-- returns the qname of unit
getUnitQName :: DkMonad m => m QName
getUnitQName = do
    DefinedName _ (AbsName{anameName = unit}) _ <- liftTCM $ resolveName' allKindsOfNames Nothing $
        CN.Qual (CN.simpleName "elimPattPrelude") (CN.QName $ CN.simpleName "UUnit")
    return unit

-- returns the name of constructor tt of unit
getTTQName :: DkMonad m => m QName
getTTQName = do -- todo: get rid of alias ttt
    DefinedName _ (AbsName{anameName = tt}) _ <- liftTCM $ resolveName' allKindsOfNames Nothing $
        CN.Qual (CN.simpleName "elimPattPrelude") (CN.QName $ CN.simpleName "ttt")
    return tt

-- let c : Delta -> (Phi_{n-1} -> D) .. -> (Phi_0 -> D) -> D
-- given an index ix, we return the term
-- i, pars, P, p, Delta, h_{n-1} ...  h_0  |-
--    λ (v : Phi_ix). ( prfBelow i pars P p (h_i v),  p (h_i v) (prfBelow i pars P p (h_i v)) )
mkPrfBelowLam :: DkMonad m =>
  QName -> -- qname of D
  QName -> -- qname of constructor
  Int -> -- index of the rec argument in which we are doing abstraction
  Telescope -> -- the telescope of arguments of the recursive argument (Phi_ix)
  m Term
mkPrfBelowLam dName consName ix ixArgs =
  do
    let numIxArgs = length ixArgs -- lenght of Phi_ix
    numArgs <- -- number of args the constructor takes
      length <$> removeParams <$> theTel <$> (telView =<< defType <$> getConstInfo consName)

    -- builds the term i, pars, P, p, ϕ, v : Phi_i |- prfBelow i pars P p (h_i v)
    l <- do
          DkState{prfBelowOfData = prfBelowOfData} <- get
          let Just prfBelowName = prfBelowOfData dName

          Datatype{dataPars = numPars} <- theDef <$> getConstInfo dName

          let i_ = [Apply $ defaultArg $ Var (numIxArgs + numArgs + 2 + numPars) []]
          let pars_ = raise (numIxArgs + numArgs + 2) $ genElim numPars
          let pP_ = [Apply $ defaultArg $ Var (numIxArgs + numArgs + 1) []]
          let p_ = [Apply $ defaultArg $ Var (numIxArgs + numArgs) []]
          let hi_ = [Apply $ defaultArg $ Var (numIxArgs + ix) $ genElim numIxArgs]
          return $ Def prfBelowName (i_ ++ pars_ ++ pP_ ++ p_ ++ hi_)

    -- builds the term i, pars, P, p, ϕ, v : Phi_i |- p (h_i v) (prfBelow i pars P p (h_i v))
    let r =
          let hi_ = [Apply $ defaultArg $ Var (numIxArgs + ix) $ genElim numIxArgs] in
          let l' = [Apply (defaultArg l)] in
          Var (numIxArgs + numArgs) (hi_ ++ l')

    -- builds λ v. ( prfBelow i pars P p (h_i v),  p (h_i v) (prfBelow i pars P p (h_i v)) )
    finalTerm <- do
      Just sig <- getSigmaKit
      let sig_constructor = conName $ sigmaCon $ sig
      return $ teleLam ixArgs $ Def sig_constructor [Apply (defaultArg l), Apply (defaultArg r)]

    reportSDoc "toDk.elimPattMatch.below" 20 $ AP.prettyTCM finalTerm
    return finalTerm


-- let c : Delta -> (Phi_{n-1} -> D) .. -> (Phi_0 -> D) -> D
-- given an index ix, we return the type
-- i, pars, P, Delta, h_{n-1} ...  h_0  |- v : Phi_ix -> Below i pars P (h_i v) /\ P (h_i)
mkBelowProduct :: DkMonad m =>
  QName -> -- qname of D
  QName -> -- qname of constructor
  Int -> -- index of the rec argument in which we are doing product
  Telescope -> -- the telescope of arguments of the recursive argument (Phi_ix)
  m Type
mkBelowProduct dName consName ix ixArgs =
  do
    let numIxArgs = length ixArgs -- lenght of Phi_ix
    numArgs <- -- number of args the constructor takes
      length <$> removeParams <$> theTel <$> (telView =<< defType <$> getConstInfo consName)

    -- builds the term i, pars, consArgs, v : Phi_i |- Below i pars P (h_i v)
    bellowApp <- do
          DkState{belowOfData = belowOfData} <- get
          let Just belowName = belowOfData dName

          Datatype{dataPars = numPars} <- theDef <$> getConstInfo dName

          let i_ = [Apply $ defaultArg $ Var (numIxArgs + numArgs + 1 + numPars) []]
          let pars_ = raise (numIxArgs + numArgs + 1) $ genElim numPars
          let p_ = [Apply $ defaultArg $ Var (numIxArgs + numArgs) []]
          let hi_ = [Apply $ defaultArg $ Var (numIxArgs + ix) $ genElim numIxArgs]
          return $ Def belowName (i_ ++ pars_ ++ p_ ++ hi_)

    -- builds the term i, pars, consArgs, v : Phi_i |- P (h_i v)
    let p_hi =
          let hi_ = [Apply $ defaultArg $ Var (numIxArgs + ix) $ genElim numIxArgs] in
          Var (numIxArgs + numArgs) hi_

    prod <- addContext ixArgs $ telePi ixArgs <$>
      do
        below_ap_ty <- typeOfTerm bellowApp
        p_hi_ty <- typeOfTerm p_hi
        mkProd below_ap_ty p_hi_ty

    reportSDoc "toDk.elimPattMatch.below" 20 $ AP.prettyTCM prod
    return prod

assembleClause :: QName -> Telescope -> Telescope -> Type -> Term -> Clause
assembleClause consName gamma consTel clauseTy body =
  let patts =
        (genPattsFromInts $ reverse $ map ((+) $ length consTel) [0 .. ((length gamma) - 1)])
          ++ [defaultNamedArg $ ConP (defaultConHead consName) noConPatternInfo $
              genPattsFromInts $ reverse [0 .. ((length consTel) - 1)]] in
  Clause{ clauseLHSRange = NoRange
        , clauseFullRange = NoRange
        , clauseTel = gamma `abstract` consTel
        , namedClausePats = patts
        , clauseBody = Just body
        , clauseType = Just $ defaultArg clauseTy
        , clauseCatchall = False
        , clauseExact = Nothing
        , clauseRecursive = Nothing
        , clauseUnreachable = Nothing
        , clauseEllipsis = NoEllipsis
        , clauseWhereModule = Nothing}

mkPrfBelowClause :: DkMonad m => QName -> Type -> QName -> m Clause
mkPrfBelowClause dname ty consName = do
  -- Γ, ϕ ⊢ clauseTy, where ϕ are the constructor arguments
  (gamma, consTel, clauseTy) <- mkClauseTele dname ty consName

  body <- do
    let clauseTel = gamma `abstract` consTel

    -- gets the arguments telescopes of recursive positions in the type of consName
    ho_tel <- mkRecArgsTel dname consName

    -- generates list with the λ v : Phi_i. (below ..., P (h_i v) (below ...))
    -- for each recursive argument of the constructor
    belows <- addContext clauseTel $
      mapM (\(i, tel) -> mkPrfBelowLam dname consName i tel) ho_tel

    -- gets sig constructor _,_
    Just sig <- getSigmaKit
    let sig_cons = conName $ sigmaCon $ sig

    -- builds the body by taking the product of everyone in belows
    ttt <- getTTQName
    case belows of
      [] -> do -- we build p (c args) tt
        tt <- reduce $  Def ttt $ [Apply $ defaultArg $ Var (length clauseTel - 1) []]
        let c = Def consName $ genElim $ length consTel
        return $ Var (length clauseTel - 3) $ [Apply $ defaultArg c, Apply $ defaultArg tt]

      x : l ->
        return $ foldl (\v x -> Def sig_cons [Apply $ defaultArg x, Apply $ defaultArg v]) x l

  let clause = assembleClause consName gamma consTel clauseTy body

  reportSDoc "toDk.elimPattMatch.below" 20 $ AP.prettyTCM $ clause
  return clause


mkBelowClause :: DkMonad m => QName -> Type -> QName -> m Clause
mkBelowClause dname belowTy consName =
  do
    -- Γ, ϕ ⊢ clauseTy, where ϕ are the constructor arguments
    (gamma, consTel, clauseTy) <- mkClauseTele dname belowTy consName

    body <- do
      let clauseTel = gamma `abstract` consTel

      -- gets the arguments telescopes of recursive positions in the type of consName
      ho_tel <- mkRecArgsTel dname consName

      -- generates list with the (v : Phi_i -> belowD i pars P (h_i v) /\ P (h_i v))
      -- for each recursive argument of the constructor
      belows <- addContext clauseTel $
        mapM (\(i, tel) -> mkBelowProduct dname consName i tel) ho_tel

      -- builds the body by taking the product of everyone in belows
      unit <- getUnitQName
      case belows of
        [] -> typeOfTerm $ Def unit $ [Apply $ defaultArg $ Var (length clauseTel - 1) []]
        x : l -> addContext clauseTel $ foldM (\v x -> mkProd x v) x l

    let clause = assembleClause consName gamma consTel clauseTy (unEl body)

    reportSDoc "toDk.elimPattMatch.below" 20 $ AP.prettyTCM $ clause
    return clause

mkCaseClause :: DkMonad m => QName -> Type -> QName -> m Clause
mkCaseClause dname caseTy consName =
  do
    -- Γ, ϕ ⊢ clauseTy, where ϕ are the constructor arguments
    (gamma, consTel, clauseTy) <- mkClauseTele dname caseTy consName

    body <- do
          Datatype{dataCons = cons} <- theDef <$> getConstInfo dname
          let Just consIndex = elemIndex consName cons
          -- the index of m_cons in
          -- i : Lvl, pars : Pars, P : D pars -> Set i, m_0 .. m_k-1, a : Phi
          let consMethodIndex = (length cons) + (length consTel) - consIndex - 1
          return $ Var consMethodIndex $ genElim $ length consTel

    let patts =
          (genPattsFromInts $ reverse $ map ((+) $ length consTel) [0 .. ((length gamma) - 1)])
          ++ [defaultNamedArg $ ConP (defaultConHead consName) noConPatternInfo $
               genPattsFromInts $ reverse [0 .. ((length consTel) - 1)]]

    let clause = assembleClause consName gamma consTel clauseTy body

    reportSDoc "toDk.elimPattMatch" 20 $ AP.prettyTCM $ clause
    return clause

-- given a type Γ -> x : D -> A and a constructor c of D,
-- returns (Γ, args : ϕ, A{c args / x}), where c : (args : ϕ) -> D
mkClauseTele :: DkMonad m => QName -> Type -> QName -> m (Telescope, Telescope, Type)
mkClauseTele dname ty consName =
  do
    TelV{theTel = tel, theCore = clauseTy} <- telView ty

    -- splits the telescope tel as Gamma, x : D pars
    let (gamma, ExtendTel Dom{unDom = El{unEl = Def _ pars}} Abs{unAbs = EmptyTel}) =
          splitTelescopeAt ((length tel) - 1) tel

    -- we have Gamma, a : Phi, Empty |- caseTy{c a/x}
    (_, consTel, _, clauseTy') <-
      instantiateWithConstructor gamma dname pars EmptyTel clauseTy consName
    return (gamma, consTel, clauseTy')

data Construction = TheCase | TheBelow | ThePrfBelow | TheRec

mkConstruction :: DkMonad m => Construction -> QName -> m Definition
mkConstruction construction dQName =
  do
    -- gets the type
    ty <- case construction of
      TheCase -> mkCaseType dQName
      TheBelow -> mkBelowType dQName
      ThePrfBelow -> mkPrfBelowType dQName
      _ -> __IMPOSSIBLE__

    -- creates name
    constrQName <- do
      dQNameString <- liftTCM $ map (\c -> if c == '.' then '-' else c) <$>
        render <$> AP.prettyTCM dQName
      let str = case construction of
            TheCase -> "case"
            TheBelow -> "below"
            ThePrfBelow -> "prfBelow"
            _ -> __IMPOSSIBLE__
      constructionName <- liftTCM $ freshName_ $ str ++ dQNameString
      return QName{qnameModule = qnameModule dQName, qnameName = constructionName}

    -- declares the constant
    liftTCM $ addConstant constrQName $
      defaultDefn defaultArgInfo constrQName ty WithoutK emptyFunction

    -- stores in dkstate the qname of belowD
    dkState <- get
    put $ case construction of
      TheCase ->
        dkState{caseOfData =
                (\x -> if x == dQName then Just constrQName else caseOfData dkState x)}
      TheBelow ->
        dkState{belowOfData =
                (\x -> if x == dQName then Just constrQName else belowOfData dkState x)}
      ThePrfBelow ->
        dkState{prfBelowOfData =
                (\x -> if x == dQName then Just constrQName else prfBelowOfData dkState x)}
      _ -> __IMPOSSIBLE__

    -- computes the clauses
    clauses <- do
      Datatype{dataCons = cons} <- theDef <$> getConstInfo dQName -- gets constructors
      case construction of
        TheCase -> mapM (\consname -> mkCaseClause dQName ty consname) cons
        TheBelow -> mapM (\consname -> mkBelowClause dQName ty consname) cons
        ThePrfBelow -> mapM (\consname -> mkPrfBelowClause dQName ty consname) cons
        _ -> __IMPOSSIBLE__

    -- adds the clauses
    liftTCM $ addClauses constrQName clauses

    -- gets the updated definition and returns it
    updatedDef <- getConstInfo constrQName
    return updatedDef

telNames :: Telescope -> [String]
telNames EmptyTel = []
telNames (ExtendTel _ Abs{absName = name, unAbs = nextTel}) = name : (telNames nextTel)


-- given Gamma, x : D pars, Delta |- A
-- and a constructor c : {pars : Pars} -> Phi -> D pars of D
-- returns Gamma, a : Phi, Delta{c a/x} |- A{c a/x}
instantiateWithConstructor :: DkMonad m => Telescope -> QName -> Elims -> Telescope -> Type -> QName ->
                              m (Telescope, Telescope, Telescope, Type)
instantiateWithConstructor gamma d pars delta returnTy consName =
  do
    -- Gamma |- pars : Pars
    let subst = foldl (\acc x -> x :# acc) (EmptyS __IMPOSSIBLE__) $ map (\(Apply x) -> unArg x) pars

    cons <- getConstInfo consName
    let consTy = defType cons
    TelV{theTel = consTel} <- telView $ consTy
    -- Gamma |- pars : Pars applied to p : Pars |- (removeParms consTel) : Phi
    -- gives Gamma |- consTel' : Phi{pars/p}
    -- that is, the parameters in the telescope are instanciated with pars
    let consTel' = applySubst subst (removeParams consTel)

    -- makes space for Phi
    let delta' = raiseFrom 1 (length consTel') delta
    -- maps Gamma, x : D pars |- delta' to Gamma, a : Phi |- delta'{c a/x}
    let delta'' =
          let conHead = ConHead{conName = consName,
                                conDataRecord = IsData,
                                conInductive = Inductive,
                                conFields = []} in
            let conInfo = ConOCon in
              let consApplied = Con conHead conInfo $ genElim (length consTel') in
                applySubst (consApplied :# IdS) delta'

    let returnTy' = raiseFrom (1 + (length delta)) ((length consTel') + (length delta)) returnTy
    -- maps Gamma, x : D pars, Delta' |- returnTy to Gamma, a : Phi, Delta' |- returnTy{c a/x}
    let returnTy'' =
          let conHead = ConHead{conName = consName, conDataRecord = IsData, conInductive = Inductive, conFields = []} in
            let conInfo = ConOCon in
              let consApplied = Con conHead conInfo $ genElim (length consTel') in
                applySubst (Lift (length delta) (consApplied :# IdS)) returnTy'

    return (gamma, consTel', delta'', returnTy'')

-- Given Gamma, x : D pars, Delta |- returnTy,
-- a constructor c of D, of type {p : pars} -> (a : Phi) -> D pars
-- produces a term t with Gamma |- t : (a : Phi) -> Delta{c a/x} -> returnTy{c a/x},
-- calling compiledClausesToCase recursively
buildMethod :: DkMonad m =>
               Telescope -> QName -> Elims -> Telescope -> Type -> QName -> CompiledClauses ->
               MaybeT m Term
buildMethod gamma d pars delta returnTy consName compiledC =
  do

    -- prepares the new telescope before calling compieldClausesToCase
    (_, consTel', delta', returnTy') <-
      instantiateWithConstructor gamma d pars delta returnTy consName 
    
    let newTel = gamma `abstract` (consTel' `abstract` delta')

    ---- now that we have computed newTel and returnTy'', we use
    ---- compiledClausesToCase to get a t such that newTel |- t : returnTy''
    t <- compiledClausesToCase newTel returnTy' compiledC

    let namesToBeAbstracted = telNames $ consTel' `abstract` delta'

    -- computes Gamma |- abs_t : (a : Phi) -> Delta' -> returnTy''
    let abstracted_t = foldr (\x recCall -> Lam defaultArgInfo Abs{absName = x, unAbs = recCall})
                       t namesToBeAbstracted

    -- weakens Gamma |- abs_t  to Gamma, x : D pars, Delta |- abs_t
    let raised_t = raise (1 + (length delta)) abstracted_t
    
    return raised_t

buildMethodCatchAll :: DkMonad m =>
                       Telescope -> Telescope -> QName -> Elims -> Telescope ->
                       Type -> QName -> CompiledClauses -> MaybeT m Term
buildMethodCatchAll fullTel gamma d pars delta returnTy consName compiledC =
  do
    -- gives t with Gamma, x : D p, Delta |- t : A
    t <- compiledClausesToCase fullTel returnTy compiledC

    cons <- getConstInfo consName
    let consTy = defType cons
    TelV{theTel = preConsTel} <- telView $ consTy
    let consTel = removeParams preConsTel
    let numConsArgs = length consTel

    -- appliedCons = c a
    let appliedCons =
          let conHead = ConHead{conName = consName,
                                conDataRecord = IsData,
                                conInductive = Inductive,
                                conFields = []} in
            let conInfo = ConOCon in
              Con conHead conInfo $ genElim numConsArgs

    -- Gamma, a : Phi |- subst : Gamma
    let subst = Wk numConsArgs IdS
    -- Gamma, a : Phi |- subst' : Gamma, x : D pars
    let subst' = appliedCons :# subst
    -- Gamma, a : Phi, Delta{c a/x} |- subst'' : Gamma, x : D pars, Delta
    let subst'' = Lift (length delta) subst'

    -- gives t' with Gamma, a : Phi, Delta{c a/x} |- t' : A{c a/x}
    let t' = applySubst subst'' t

    let namesToBeAbstracted = (replicate numConsArgs "x") ++ (telNames delta)

    -- computes Gamma |- abs_t : (a : Phi) -> Delta' -> A
    let abstracted_t = foldr (\x recCall -> Lam defaultArgInfo Abs{absName = x, unAbs = recCall})
                       t' namesToBeAbstracted

    -- weakens Gamma |- abs_t  to Gamma, x : D pars, Delta |- abs_t
    let raised_t = raise (1 + (length delta)) abstracted_t
    
    return raised_t
    

          
compiledClausesToCase :: DkMonad m => Telescope -> Type -> CompiledClauses -> MaybeT m Term
compiledClausesToCase tel returnTy (Done _ body) = return body -- trivial node
compiledClausesToCase tel returnTy tree@(Case n bs) =
  do
    let splitPoint = unArg n
    let (gamma, preDelta) = splitTelescopeAt splitPoint tel
    let
      ExtendTel
        splitTy@Dom{unDom = El{unEl = Def d pars}}
        Abs{absName = splitName, unAbs = delta} = preDelta

    -- this node is of the form gamma, x : D pars, delta |- returnTy, that is, matching on x : D pars

    dDef <- theDef <$> getConstInfo d
    -- gets list of constructors of D
    let constructors = dataCons dDef

    -- we only support non-indexed data
    guard $ case dDef of Datatype{} -> True; _ -> False

    guard $ (dataIxs dDef) == 0
    
    let Type returnLvl = _getSort returnTy
    -- elim = returnLvl
    let elim = [Apply Arg{argInfo = defaultArgInfo, unArg = Level returnLvl}]

    -- elim' = returnLvl pars
    let elim' = elim ++ (raise (1 + (length delta)) pars)

    -- motiveTy = \x. Delta -> returnTy
    let motiveTy =
          Apply Arg{argInfo = defaultArgInfo,
                    unArg = raise (1 + (length delta)) $ 
                     Lam defaultArgInfo Abs{absName = splitName, unAbs = unEl $ telePi delta returnTy}}
    -- elim '' = returnLvl pars (\x. Delta -> returnTy)
    let elim'' = elim' ++ [motiveTy]

    -- calculates the methods
    methods <- mapM
               (\consName ->
                  case (Map.lookup consName (conBranches bs), catchAllBranch bs) of
                    (Just compiledC, _)      -> -- constructor consName has a branch on the case tree bs
                      buildMethod gamma d pars delta returnTy consName (content compiledC)
                    (Nothing, Just catchAll) -> -- no branch, there must be a catchall clause
                      buildMethodCatchAll tel gamma d pars delta returnTy consName catchAll
                    _                        -> __IMPOSSIBLE__)
               constructors

    -- elim''' = returnLvl pars (\x. Delta -> returnTy) m1 .. mk
    let elim''' = elim'' ++ (map (\x -> Apply Arg{argInfo = defaultArgInfo, unArg = x}) methods)

    -- finalElim = returnLvl pars (\x. Delta -> returnTy) m1 .. mk x delta
    let finalElim = elim''' ++ (map (\x -> Apply $ defaultArg $ Var x []) $ genList $ 1 + (size delta))

--    reportSDoc "toDk.elimPattMatch" 20 $ AP.prettyTCM $ Def d finalElim

    caseOfData <- gets caseOfData
    let Just caseName = caseOfData d
    return $ Def caseName finalElim

{-
getRecursiveIndex :: DkMonad m => [Clause] -> MaybeT m Int
getRecursiveIndex clauses =
  do
    let lhs = map (patternToTerm . namedArg) clauses
    TODO
  -}

{-
compiledClausesToCase tel returnTy tree@(Case n bs) =
  do
--    reportSDoc "toDk.elimPattMatch" 20 $ return $ text $ show (unArg n)
--    let splitPoint = (length tel) - (unArg n)
    let splitPoint = unArg n
    let (gamma, preDelta) = splitTelescopeAt splitPoint tel
--    reportSDoc "toDk.elimPattMatch" 20 $ return $ text $ show splitPoint
--    reportSDoc "toDk.elimPattMatch" 20 $ AP.prettyTCM gamma    
--    reportSDoc "toDk.elimPattMatch" 20 $ AP.prettyTCM preDelta
    let
      ExtendTel
        splitTy@Dom{unDom = El{unEl = Def dataTypeName pars}}
        Abs{absName = splitName, unAbs = delta} = preDelta
    let Type returnLvl = _getSort returnTy

    let elim = [Apply Arg{argInfo = defaultArgInfo, unArg = Level returnLvl}]
    let elim' = elim ++ (raise (1 + (length delta)) pars)

    let motiveTy =
          Apply Arg{argInfo = defaultArgInfo,
                    unArg = raise (length delta) $ 
                     Lam defaultArgInfo Abs{absName = splitName, unAbs = unEl $ telePi delta returnTy}}
    let elim'' = elim' ++ [motiveTy]

    -- Gamma |- subst : Pars
    let subst = foldl (\acc x -> x :# acc) (EmptyS __IMPOSSIBLE__) $ map (\(Apply x) -> unArg x) pars

--    reportSDoc "toDk.elimPattMatch" 20 $ AP.prettyTCM $ subst

    Datatype {dataCons = cons} <- theDef <$> getConstInfo dataTypeName
    cons0 <- getConstInfo (head cons)
    let cons0Ty = defType cons0
    TelV{theTel = cons0Tel} <- telView $ cons0Ty
    let cons0Tel' = applySubst subst (removeParams cons0Tel)
--    reportSDoc "toDk.elimPattMatch" 20 $ AP.prettyTCM $ (removeParams cons0Tel)
--    reportSDoc "toDk.elimPattMatch" 20 $ AP.prettyTCM $ cons0Tel'

    let delta' = raiseFrom 1 (length cons0Tel') delta
    let delta'' =
          let conHead = ConHead{conName = head cons, conDataRecord = IsData, conInductive = Inductive, conFields = []} in
            let conInfo = ConOCon in
              let consApplied = Con conHead conInfo $ genElim (length cons0Tel') in
                applySubst (consApplied :# IdS) delta'

    let returnTy' = raiseFrom (1 + (length delta)) ((length cons0Tel') + (length delta)) returnTy
    let returnTy'' =
          let conHead = ConHead{conName = head cons, conDataRecord = IsData, conInductive = Inductive, conFields = []} in
            let conInfo = ConOCon in
              let consApplied = Con conHead conInfo $ genElim (length cons0Tel') in
                applySubst (Lift (length delta) (consApplied :# IdS)) returnTy'


    let finalTy = gamma `abstract` (cons0Tel' `abstract` (delta'' `abstract` returnTy''))
    reportSDoc "toDk.elimPattMatch" 20 $ AP.prettyTCM $ finalTy    
--    reportSDoc "toDk.elimPattMatch" 20 $ AP.prettyTCM $ gamma
--    reportSDoc "toDk.elimPattMatch" 20 $ AP.prettyTCM $ cons0Tel'
--    reportSDoc "toDk.elimPattMatch" 20 $ AP.prettyTCM $ delta''
--    reportSDoc "toDk.elimPattMatch" 20 $ AP.prettyTCM $ returnTy''


    
    let endElims = elim'' ++ (map (\x -> Apply $ defaultArg $ Var x []) $ genList $ 1 + (size delta))

    reportSDoc "toDk.elimPattMatch" 20 $ AP.prettyTCM $ Def dataTypeName endElims

    return ()
-}    
    
                             
               
                      






