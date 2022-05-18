{-# LANGUAGE FlexibleContexts #-}
module ElimPattMatch.Constructions where

import qualified Data.Map as Map
import Text.PrettyPrint

import Agda.Utils.Pretty (pretty)
import Agda.Syntax.Internal
import Agda.TypeChecking.Substitute
import qualified Agda.TypeChecking.Pretty as AP
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Level
import Agda.TypeChecking.CheckInternal
import Agda.TypeChecking.Sort
import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Context
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Monad.Signature
import Agda.TypeChecking.Monad.Builtin
import Agda.Syntax.Common
import Agda.Utils.Size
import qualified Agda.Syntax.Concrete.Name as CN
import Agda.Utils.Impossible
import Data.List.NonEmpty (fromList, toList)

import Control.Monad.State
import Control.Monad.Trans.Maybe
import Control.Monad

import DkMonad

genList 0 = []
genList n = (n - 1) : (genList (n - 1))
genElim n = map (\x -> Apply $ defaultArg $ Var x []) $ genList n

-- remove the first hidden args of the telescope.
-- when given the telescope generated from a constructor type, these are generally the parameters
removeParams EmptyTel = EmptyTel
removeParams tel@(ExtendTel x y) = if argInfoHiding (domInfo x) == Hidden
                                   then removeParams $ unAbs y
                                   else tel
                                        
-- given constructor c : {p : Pars} -> (a : Phi) -> D p,
-- builds type (a : Phi) -> P (c p a) in context i : Level, p : Pars, P : D p -> Set_i
mkCaseMethod :: QName -> TCM Type
mkCaseMethod conName =
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
mkEnd :: QName -> Int -> TCM Type
mkEnd dataname numPars =
  do
    let dataAppliedToPars = raise 1 $ Def dataname $ genElim numPars
    sortDataAppliedToPars <- sortOf dataAppliedToPars
    let dataAppliedToPars' = El{_getSort = sortDataAppliedToPars, unEl = dataAppliedToPars}

    let returnTy = Var 1 $ genElim 1
    sortReturnTy <- addContext ("x", defaultDom dataAppliedToPars') $ sortOf returnTy
--    reportSDoc "toDk.elimPattMatch" 20  $ AP.prettyTCM sortReturnTy
    let returnTy' = El{_getSort= sortReturnTy, unEl= returnTy}
    let ty =
          Pi (defaultDom dataAppliedToPars')
          (Abs{absName = "x", unAbs = returnTy'})

    sortTy <- sortOf ty
    return El{_getSort = sortTy, unEl = ty}

-- runState (mkCase ...) initState :: MonadTCM m => m (Type,ToDKState)

-- given dataype name D, generates the type of case_D
-- mkCase :: forall m. (MonadTCM m, MonadState ToDKState m) => QName -> m Type
mkCase :: DkMonad m => QName -> m Definition
mkCase qname =
  do
{-    st <- gets fieldName
    put st
    modify -}
    
    Datatype{dataPars = numPars, dataCons = cons} <- theDef <$> getConstInfo qname
    dType <- defType <$> getConstInfo qname
    pars' <- theTel <$> telView dType
    levelType <- levelType

    -- tel = i : Level, p : Pars
    let tel = ExtendTel (defaultDom levelType) (Abs{absName = "i", unAbs = pars'})
    motiveTy <- liftTCM $ addContext tel $ mkMotiveType qname $ length pars'

    -- tel' = i : Level, p : Pars, P : D p -> Set_i
    let tel' = tel `abstract` (ExtendTel (defaultDom motiveTy) Abs{absName =  "P", unAbs = EmptyTel})
    methods <- liftTCM $ addContext tel' $ mapM mkCaseMethod cons
    let methodsRaised =
          reverse $ fst $
          foldl (\(l, n) x -> ((raise n x, "M_" ++ (show n)) : l, n + 1)) ([], 0) methods

    -- tel'' = i : Level, p : Pars, P : D p -> Set_i, m_j : (a : Phi_j -> P (c_j p a))
    let tel'' = foldl
                (\acc (ty, s) -> acc `abstract`
                                 (ExtendTel (defaultDom ty) Abs{absName=s, unAbs=EmptyTel}))
                tel' methodsRaised
    end <- liftTCM $ addContext tel' $ mkEnd qname numPars

    let caseType = telePi_ tel'' $ raise (length cons) end   
    _ <- liftTCM $ checkType' caseType -- checks it is well-sorted
    -- we have finished building the type of case, now we add it to the signature


    let dataTypeNameString = concat $
                             map (\x -> case x of
                                          CN.Hole -> "_"
                                          CN.Id s -> s)
                             $ toList $ CN.nameNameParts $ nameConcrete $ qnameName qname
    caseName <- liftTCM $ freshName_ $ "case" ++ dataTypeNameString
    let caseQName = QName{qnameModule = qnameModule qname, qnameName = caseName}

    let theCase = defaultDefn defaultArgInfo caseQName caseType WithoutK Axiom{axiomConstTransp=False}
    
    liftTCM $ addConstant caseQName $ theCase
      

    dkState@DkState{caseOfData = caseOfData} <- get
    put $ dkState{caseOfData = (\x -> if x == qname then Just caseQName else caseOfData x)}
    return theCase
      
telNames :: Telescope -> [String]
telNames EmptyTel = []
telNames (ExtendTel _ Abs{absName = name, unAbs = nextTel}) = name : (telNames nextTel)


-- Given Gamma, x : D pars, Delta |- returnTy,
-- a constructor c of D, of type {p : pars} -> (a : Phi) -> D pars
-- produces Gamma |- (a : Phi) -> Delta{c a/x} -> returnTy{c a/x},
-- calling compiledClausesToCase recursively
buildMethod :: DkMonad m =>
               Telescope -> QName -> Elims -> Telescope -> Type -> QName -> CompiledClauses ->
               MaybeT m Term
buildMethod gamma d pars delta returnTy consName compiledC =
  do
    -- Gamma |- pars : Pars
    let subst = foldl (\acc x -> x :# acc) (EmptyS __IMPOSSIBLE__) $ map (\(Apply x) -> unArg x) pars

    -------- prepares the new telescope before calling compieldClausesToCase --------

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
    
    let newTel = gamma `abstract` (consTel' `abstract` delta'')

    ---- now that we have computed newTel and returnTy'', we use
    ---- compiledClausesToCase to get a t such that newTel |- t : returnTy''
    t <- compiledClausesToCase newTel returnTy'' compiledC

    let namesToBeAbstracted = telNames $ consTel' `abstract` delta''

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
    
                             
               
                      






