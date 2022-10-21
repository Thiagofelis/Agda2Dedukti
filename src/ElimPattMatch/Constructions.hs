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
import Agda.Syntax.Scope.Base (allKindsOfNames, AbstractName(AbsName), anameName, ResolvedName (DefinedName))
import qualified Agda.Syntax.Concrete.Name as CN
import Agda.TypeChecking.Monad.Context
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Monad.Signature
import Agda.TypeChecking.Monad.Builtin
import Agda.Syntax.Common
import Agda.Utils.Size
import qualified Agda.Syntax.Concrete.Name as CN
import Agda.Utils.Impossible

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
mkEndType :: QName -> Int -> TCM Type
mkEndType dataname numPars =
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

-- given type D with numPars parameters
-- builds the type (i : Level) -> (p : Pars) -> (P : D p -> Set_i) -> D p -> Set_i
mkBelowType :: DkMonad m => QName -> Telescope -> m Type
mkBelowType qname pars =
  do
    levelType <- liftTCM $ levelType
    -- tel = i : Level, p : Pars
    let tel = ExtendTel (defaultDom levelType) (Abs{absName = "i", unAbs = pars})

    motiveTy <- liftTCM $ addContext tel $ mkMotiveType qname $ length pars

    -- tel' = i : Level, p : Pars, P : D p -> Set_i
    let tel' = tel `abstract` (ExtendTel (defaultDom motiveTy) Abs{absName =  "P", unAbs = EmptyTel})


    -- TODO : the end universe (Set i) can actually increase when dealing with higher-order recursion
    -- whose indexing type is at universe > 0
    end <- liftTCM $ addContext tel $ raise 1 <$> mkMotiveType qname (length pars)

    let caseType = telePi_ tel' $ end
    _ <- liftTCM $ checkType' caseType -- checks it is well-sorted
    reportSDoc "toDk.elimPattMatch.below" 20 $ AP.prettyTCM caseType
    return caseType

mkCaseType :: DkMonad m => QName -> Telescope -> [QName] -> m Type
mkCaseType qname pars cons =
  do
    levelType <- liftTCM $ levelType
    -- tel = i : Level, p : Pars
    let tel = ExtendTel (defaultDom levelType) (Abs{absName = "i", unAbs = pars})

    motiveTy <- liftTCM $ addContext tel $ mkMotiveType qname $ length pars

    -- tel' = i : Level, p : Pars, P : D p -> Set_i
    let tel' = tel `abstract` (ExtendTel (defaultDom motiveTy) Abs{absName =  "P", unAbs = EmptyTel})
    methods <- liftTCM $ addContext tel' $ mapM mkCaseMethodType cons
    let methodsRaised =
          reverse $ fst $
          foldl (\(l, n) x -> ((raise n x, "M_" ++ (show n)) : l, n + 1)) ([], 0) methods

    -- tel'' = i : Level, p : Pars, P : D p -> Set_i, m_j : (a : Phi_j -> P (c_j p a))
    let tel'' = foldl
                (\acc (ty, s) -> acc `abstract`
                                 (ExtendTel (defaultDom ty) Abs{absName=s, unAbs=EmptyTel}))
                tel' methodsRaised
    end <- liftTCM $ addContext tel' $ mkEndType qname $ length pars

    let caseType = telePi_ tel'' $ raise (length cons) end   
    _ <- liftTCM $ checkType' caseType -- checks it is well-sorted

    return caseType


mkHOTel :: DkMonad m => QName -> QName -> m [(Int, Telescope)]
mkHOTel dName conName =
  do
    consType <- defType <$> getConstInfo conName
    consTel <-theTel <$> telView consType
    let telList = flattenTel consTel

    -- CONTINUER HERE
    ho_tel <- snd <$>
      foldM
      (\vrec x -> do
          let (n, l) = vrec
          TelV{theTel = tel, theCore = codom} <- telView (unDom x)

          case unEl codom of
            Def qname _ -> return (if dName == qname then (n + 1, (n, tel) : l) else (n+1, l))
            _ -> return (n+1,l))
      (0, [])
      (reverse telList)

    -- print to debug
    _ <- addContext consTel $
      mapM (\x -> reportSDoc "toDk.elimPattMatch.below" 20 $ AP.prettyTCM x)
      ho_tel

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

-- let c : Delta -> (Phi_{n-1} -> D) .. -> (Phi_0 -> D) -> D
-- given an index ix, we return the type
-- i, pars, P, Delta, h_{n-1} ...  h_0  |- v : Phi_ix -> Below i pars P (h_i v) /\ P (h_i)
mkBelowProduct :: DkMonad m =>
  QName -> -- qname of D
  QName -> -- qname of constructor
  Int -> -- number of recursive arguments of the constructor
  Int -> -- index of the rec argument in which we are doing product
  Telescope -> -- the telescope of arguments of the recursive argument
  m Type
mkBelowProduct dName consName nRecArgs ix ixArgs =
  do
    dkState@DkState{belowOfData = belowOfData} <- get
    let Just belowName = belowOfData dName


    let lengthElim = length ixArgs
    let argsElim = genElim lengthElim

    consTy <- defType <$> getConstInfo consName
    consArgs <- theTel <$> telView consTy
    let numArgs = length $ removeParams consArgs

    Datatype{dataCons = cons, dataPars = numPars} <- theDef <$> getConstInfo dName

    -- builds the term i, pars, consArgs, v : Phi_i |- Below i pars P (h_i v)

    let bellowApp =
          let i_ = [Apply $ defaultArg $ Var (lengthElim + numArgs + 1 + numPars) []] in
          let pars_ = raise (lengthElim + numArgs + 1) $ genElim numPars in
          let p_ = [Apply $ defaultArg $ Var (lengthElim + numArgs) []] in
          let hi_ = [Apply $ defaultArg $ Var (lengthElim + ix) $ argsElim] in
          Def belowName (i_ ++ pars_ ++ p_ ++ hi_)

    let p_hi =
          let hi_ = [Apply $ defaultArg $ Var (lengthElim + ix) $ argsElim] in
          Var (lengthElim + numArgs) hi_

    reportSDoc "toDk.elimPattMatch.below" 20 $ AP.prettyTCM (ixArgs `abstract` bellowApp)
    reportSDoc "toDk.elimPattMatch.below" 20 $ AP.prettyTCM (ixArgs `abstract` p_hi)

    prod <- addContext ixArgs $
      do
        below_ap_ty <- typeOfTerm bellowApp
        p_hi_ty <- typeOfTerm p_hi
        mkProd below_ap_ty p_hi_ty

    let prod' = telePi ixArgs prod
    reportSDoc "toDk.elimPattMatch.below" 20 $ AP.prettyTCM prod'
    return prod'

mkBelowClause :: DkMonad m => QName -> Type -> QName -> m Clause
mkBelowClause dname belowTy consName =
  do
    TelV{theTel = tel, theCore = belowCoDomTy} <- telView belowTy

    Datatype{dataCons = cons, dataPars = numPars} <- theDef <$> getConstInfo dname
    let Just consIndex = elemIndex consName cons

    -- splits the telescope tel as Gamma, x : D pars
    let (gamma, ExtendTel Dom{unDom = El{unEl = Def _ pars}} Abs{unAbs = EmptyTel}) =
          splitTelescopeAt ((length tel) - 1) tel

    -- we have Gamma, a : Phi, Empty |- belowCoDomTy{c a/x}
    (_, consTel, _, clauseTy') <-
      instantiateWithConstructor gamma dname pars EmptyTel belowCoDomTy consName

    let clauseTel = gamma `abstract` consTel

    -- gets the higher order args telescopes
    ho_tel <- mkHOTel dname consName

    -- generates list with the (v : Phi_i -> belowD i pars P (h_i v) /\ P (h_i v)), for each recursive argument of the constructor
    belows <- addContext clauseTel $
      mapM (\(i, tel) -> mkBelowProduct dname consName (length ho_tel) i tel) ho_tel

    unit <- getUnitQName

    -- builds the body by taking the product of everyone in belows
    body <- case belows of
      [] -> typeOfTerm $ Def unit $ [Apply $ defaultArg $ Var (length clauseTel - 1) []]
      x : l ->  addContext clauseTel $ foldM (\v x -> mkProd x v) x l

    let patts =
          (genPattsFromInts $ reverse $ map ((+) $ length consTel) [0 .. ((length gamma) - 1)])
          ++ [defaultNamedArg $ ConP (defaultConHead consName) noConPatternInfo $
               genPattsFromInts $ reverse [0 .. ((length consTel) - 1)]]

    let clause =
          Clause{ clauseLHSRange = NoRange
                , clauseFullRange = NoRange
                , clauseTel = clauseTel
                , namedClausePats = patts
                , clauseBody = Just (unEl body)
                , clauseType = Just $ defaultArg clauseTy'
                , clauseCatchall = False
                , clauseExact = Nothing
                , clauseRecursive = Nothing
                , clauseUnreachable = Nothing
                , clauseEllipsis = NoEllipsis
                , clauseWhereModule = Nothing}

    reportSDoc "toDk.elimPattMatch.below" 20 $ AP.prettyTCM $ clause
    return clause

mkCaseClause :: DkMonad m => QName -> Type -> QName -> m Clause
mkCaseClause dname caseTy consName =
  do
    TelV{theTel = tel, theCore = clauseTy} <- telView caseTy
    
    Datatype{dataCons = cons, dataPars = numPars} <- theDef <$> getConstInfo dname
    let Just consIndex = elemIndex consName cons

    -- we calculate the index od m_cons in
    -- i : Lvl, pars : Pars, P : D pars -> Set i, m_0 .. m_k-1, x : D
    let consMethodIndex = (length cons) - consIndex


    -- splits the telescope tel as Gamma, x : D pars
    let (gamma, ExtendTel Dom{unDom = El{unEl = Def _ pars}} Abs{unAbs = EmptyTel}) =
          splitTelescopeAt ((length tel) - 1) tel

    -- we have Gamma, a : Phi, Empty |- caseTy{c a/x}
    (_, consTel, _, clauseTy') <- instantiateWithConstructor gamma dname pars EmptyTel clauseTy consName
    
    let clauseTel = gamma `abstract` consTel

    let body = Var (consMethodIndex + (length consTel) - 1) $ genElim $ length consTel

    let patts =
          (genPattsFromInts $ reverse $ map ((+) $ length consTel) [0 .. ((length gamma) - 1)])
          ++ [defaultNamedArg $ ConP (defaultConHead consName) noConPatternInfo $
               genPattsFromInts $ reverse [0 .. ((length consTel) - 1)]]

    let clause =
          Clause{ clauseLHSRange = NoRange
                , clauseFullRange = NoRange
                , clauseTel = clauseTel
                , namedClausePats = patts
                , clauseBody = Just body
                , clauseType = Just $ defaultArg clauseTy'
                , clauseCatchall = False
                , clauseExact = Nothing
                , clauseRecursive = Nothing
                , clauseUnreachable = Nothing
                , clauseEllipsis = NoEllipsis
                , clauseWhereModule = Nothing}
    reportSDoc "toDk.elimPattMatch" 20 $ AP.prettyTCM $ clause
    return clause
{-
data Construction = TheCase | TheBelow | ThePrfBelow | TheRec

mkConstruction :: DkMonad m => QName -> Construction -> m Definition
mkConstruction dQName construction =
  do
    Datatype{dataCons = cons} <- theDef <$> getConstInfo dQName
    dType <- defType <$> getConstInfo dQName
    pars <- theTel <$> telView dType

    ty <- case construction of
      TheCase -> mkCaseType dQName
      TheBelow -> mkBelowType dQName
      _ -> __IMPOSSIBLE__


    dQNameString <- render <$> AP.prettyTCM dQName
    constructionName <- liftTCM $ freshName_ $ "below" ++ dQNameString
    let constrQName = QName{qnameModule = qnameModule dQName, qnameName = constructionName}

    liftTCM $ addConstant constrQName $
      defaultDefn defaultArgInfo constrQName ty WithoutK emptyFunction

    -- stores in dkstate the qname of belowD
    dkState <- get
    put $ case construction of
      TheCase ->
        dkState{caseOfData = (\x -> if x == qname then Just constrQName else dkState caseOfData x)}
      TheBelow ->
        dkState{belowOfData=(\x -> if x == qname then Just constrQName else dkState belowOfData x)}
      _ -> __IMPOSSIBLE__

    -- computes the clauses
    clauses <- case construction of
      TheCase -> mapM (\consname -> mkCaseClause dQName ty consname) cons
      TheBelow -> mapM (\consname -> mkBelowClause dQName ty consname) cons
      __IMPOSSIBLE__

    liftTCM $ addClauses belowQName clauses

    -- gets the updated definition and returns it
    updatedDef <- getConstInfo belowQName
    return updatedDef

    __TODO__

-}
-- given dataype name D, generates bellow_D
mkBelow :: DkMonad m => QName -> m Definition
mkBelow qname =
  do
    Datatype{dataCons = cons} <- theDef <$> getConstInfo qname
    dType <- defType <$> getConstInfo qname
    pars <- theTel <$> telView dType

    -- calculates the type of belowD
    belowType <- mkBelowType qname pars
    let theDef =
          Function{ funClauses = []
                  , funCompiled = Nothing
                  , funSplitTree = Nothing
                  , funTreeless = Nothing
                  , funCovering = []
                  , funInv = NotInjective
                  , funMutual = Nothing
                  , funAbstr = ConcreteDef
                  , funDelayed = NotDelayed
                  , funProjection = Nothing
                  , funFlags = Data.Set.empty
                  , funTerminates = Nothing
                  , funExtLam = Nothing
                  , funWith = Nothing }

    -- generates the name of the case
    let dataTypeNameString = concat $
                             map (\x -> case x of
                                          CN.Hole -> "_"
                                          CN.Id s -> s) $
                             toList $ CN.nameNameParts $ nameConcrete $ qnameName qname
    belowName <- liftTCM $ freshName_ $ "below" ++ dataTypeNameString
    let belowQName = QName{qnameModule = qnameModule qname, qnameName = belowName}

    -- the final definition without the clauses
    let theBelow = defaultDefn defaultArgInfo belowQName belowType WithoutK theDef

    -- adds the definition to the tcm
    liftTCM $ addConstant belowQName $ theBelow

    -- stores in dkstate the qname of belowD
    dkState@DkState{belowOfData = belowOfData} <- get
    put $ dkState{belowOfData = (\x -> if x == qname then Just belowQName else belowOfData x)}

    -- computes the clauses of belowD
    clauses <- mapM (\consname -> mkBelowClause qname belowType consname) cons

    liftTCM $ addClauses belowQName clauses

    -- gets the updated definition and returns it
    updatedDef <- getConstInfo belowQName
    return updatedDef

-- given dataype name D, generates the type of case_D
mkCase :: DkMonad m => QName -> m Definition
mkCase qname =
  do
    Datatype{dataCons = cons} <- theDef <$> getConstInfo qname
    dType <- defType <$> getConstInfo qname
    pars <- theTel <$> telView dType

    -- builds the type of the case
    caseType <- mkCaseType qname pars cons

    _ <- mkBelowType qname pars

    -- builds the clauses describing the computational behavior of the case
    clauses <- mapM (\consname -> mkCaseClause qname caseType consname) cons

    let theDef =
          Function{ funClauses = clauses
                  , funCompiled = Nothing
                  , funSplitTree = Nothing
                  , funTreeless = Nothing
                  , funCovering = clauses -- should we do this?
                  , funInv = NotInjective
                  , funMutual = Nothing
                  , funAbstr = ConcreteDef
                  , funDelayed = NotDelayed
                  , funProjection = Nothing
                  , funFlags = Data.Set.empty
                  , funTerminates = Nothing
                  , funExtLam = Nothing
                  , funWith = Nothing }

    -- generates the name of the case
    let dataTypeNameString = concat $
                             map (\x -> case x of
                                          CN.Hole -> "_"
                                          CN.Id s -> s) $
                             toList $ CN.nameNameParts $ nameConcrete $ qnameName qname
    caseName <- liftTCM $ freshName_ $ "case" ++ dataTypeNameString
    let caseQName = QName{qnameModule = qnameModule qname, qnameName = caseName}

    -- the final definition
    let theCase = defaultDefn defaultArgInfo caseQName caseType WithoutK theDef

    -- adds the definition to the tcm
    liftTCM $ addConstant caseQName $ theCase

    -- stores in dkstate that the case name of datatype qname is caseQName
    dkState@DkState{caseOfData = caseOfData, belowOfData = belowOfData} <- get
    put $ dkState{caseOfData = (\x -> if x == qname then Just caseQName else caseOfData x)}
    return theCase
      
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
    
                             
               
                      






