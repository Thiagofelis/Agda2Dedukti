{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveGeneric #-}


module Compiler where

-- hides (<>), as there was a conflit with the (<>) defined here
import Prelude hiding ((<>))

import Control.Monad.State
import Control.Exception
import Data.Maybe
import System.Directory (doesFileExist)
import Data.Int
import Data.List (sortOn, stripPrefix, intercalate, (++))
import Text.PrettyPrint
import Debug.Trace
import Data.List.NonEmpty (fromList, toList, NonEmpty( (:|) ))
import Data.Text (unpack)
import Control.DeepSeq (NFData)
import GHC.Generics (Generic)

-- needed for detecting the requires on the output
import Text.Regex.TDFA ((=~), getAllTextMatches)
import Data.List.Unique (sortUniq)

import Agda.Compiler.Backend
import Agda.Compiler.Common
import Agda.Interaction.Options
import qualified Agda.Syntax.Concrete.Name as CN
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern
import Agda.Syntax.Literal
import Agda.Syntax.Position
import Agda.TypeChecking.CheckInternal
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.EtaContract
import Agda.TypeChecking.Level
import Agda.TypeChecking.ReconstructParameters
import Agda.TypeChecking.RecordPatterns
import Agda.TypeChecking.Records
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Primitive.Base
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Substitute.Class
import Agda.TypeChecking.Telescope
import qualified Agda.TypeChecking.Pretty as AP
import Agda.Utils.Monad
import Agda.Utils.Pretty (pretty)
import Agda.Utils.Impossible

import DkSyntax
import ElimPattMatch.Constructions

------------------------------------------------------------------------------
-- Backend callbacks
------------------------------------------------------------------------------

dkBackend :: Backend
dkBackend = Backend dkBackend'

dkBackend' :: Backend' DkOptions DkOptions DkModuleEnv () DkCompiled
dkBackend' = Backend'
  { backendName           = "Dk"
  , backendVersion        = Nothing
  , options               = defaultDkOptions
  , commandLineFlags      = dkCommandLineFlags
  , isEnabled             = optDkCompile
      -- ^ Flag which enables the Dedukti Backend
  , preCompile            = \opts -> return opts
      -- ^ Called after type checking completes, but before compilation starts.  
  , postCompile           = \_ _ _ -> return ()
      -- ^ Called after module compilation has completed. The @IsMain@ argument
      --   is @NotMain@ if the @--no-main@ flag is present.  
  , preModule             = dkPreModule
      -- ^ Called before compilation of each module. Gets the path to the
      --   @.agdai@ file to allow up-to-date checking of previously written
      --   compilation results. Should return @Skip m@ if compilation is not
      --   required.  
  , postModule            = dkPostModule
      -- ^ Called after all definitions of a module have been compiled.  
  , compileDef            = dkCompileDef
      -- ^ Compile a single definition.  
  , scopeCheckingSuffices = False
      -- ^ True if the backend works if @--only-scope-checking@ is used.  
  , mayEraseType          = \_ -> return True
      -- ^ The treeless compiler may ask the Backend if elements
      --   of the given type maybe possibly erased.
      --   The answer should be 'False' if the compilation of the type
      --   is used by a third party, e.g. in a FFI binding.  
  }

------------------------------------------------------------------------------
--- Options ---
------------------------------------------------------------------------------

type DkCompiled = Maybe (Int32,DkDocs)


data DkOptions = DkOptions
  { optDkCompile :: Bool
  , optDkFlags   :: [String]
  , optDkDir     :: Maybe String
  , optDkRegen   :: Bool
  , optDkModeLp  :: Bool
  , optDkEtaMode :: Bool
  } deriving Generic

instance NFData DkOptions


defaultDkOptions :: DkOptions
defaultDkOptions = DkOptions
  { optDkCompile = False
  , optDkFlags   = []
  , optDkDir     = Nothing
  , optDkRegen   = False
  , optDkModeLp  = False
  , optDkEtaMode = False
  }


-- Each OptDescr describes an option of flag. Its constructor is Option
-- The arguments to Option are:
--    - list of short option characters
--    - list of long option strings (without "--")
--    - argument descriptor, of type Flag DkOptions (Flag x = x -> OptM x, where OptM is a monad transformation,
-- so it is basically a function to change the default options)
--    - explanation of option for user 
dkCommandLineFlags :: [OptDescr (Flag DkOptions)]
dkCommandLineFlags =
    [ Option [] ["dk"]      (NoArg compileDkFlag) "compile program using the Dk backend"
    , Option [] ["outDir"]  (OptArg outp "DIR")   "output DIR"
    , Option [] ["regen"]   (NoArg forceRegenDk)  "regenerate the Dedukti file even if it already exists"
    , Option [] ["lp"]      (NoArg setLpModeOn)   "change to lp mode"
    , Option [] ["etaMode"] (NoArg setEtaModeOn)  "enables eta expansion and annotations"    
    ]
  where
    compileDkFlag o = return $ o { optDkCompile = True}
    outp d o        = return $ o { optDkDir = d}
    forceRegenDk o  = return $ o { optDkRegen = True}
    setLpModeOn o   = return $ o { optDkModeLp = True}
    setEtaModeOn o  = return $ o { optDkEtaMode = True}
    
type EtaMode = Bool

------------------------------------------------------------------------------
--- Module compilation ---
------------------------------------------------------------------------------

-- This is the name of the module and the one of "etaExpand" function --
type DkModuleEnv = ModuleName

dkPreModule :: DkOptions -> IsMain -> ModuleName -> Maybe FilePath -> TCM (Recompile DkModuleEnv ())
dkPreModule opts _ mods _ =
  let path = filePath opts mods in
  let doNotRecompileFile = not (optDkRegen opts) in
  let sizeTypesFile = (modName2DkModIdent mods == ["Agda", "Builtin", "Size"]) in
  do
    fileAlreadyCompiled <- liftIO $ doesFileExist path
    if (fileAlreadyCompiled && doNotRecompileFile) || sizeTypesFile
    then return $ Skip ()
    else do liftIO $ putStrLn $ "Generation of " ++ path
            return $ Recompile mods

dkPostModule :: DkOptions -> DkModuleEnv -> IsMain -> ModuleName -> [DkCompiled] -> TCM ()
dkPostModule opts _ _ mods defs =
  let concMods = modName2DkModIdent mods in
-- We sort the file, to make sure that declarations and rules
-- do not refer to formerly declared symbols.    
  let output = show $ orderDeclRules (catMaybes defs) concMods in
  let outLp = addRequires opts output in
  liftIO $ writeFile (filePath opts mods) (if (optDkModeLp opts) then outLp else output)


-- this functions goes through the text that is going to be printed in the .lp file
-- and seee which modules it uses and add a require for them. using regular
-- expressions, it matches names of the form '(NAME.', ' NAME.', '↪Name' and ',Name.'
-- which are then included with a require on the begining of the file. this might
-- not be the cleanest way of adding the requires, but it seems to work well
-- at least right now
addRequires :: DkOptions -> String -> String
addRequires opts s =
  let moduleRegex = "[ (↪,][a-zA-Z0-9_']*\\." in
  let removeFirstAndLastChars s = reverse $ tail $ reverse $ tail s in
  let allmods = map removeFirstAndLastChars $
                getAllTextMatches (s =~moduleRegex) :: [String] in
  let filteredmods = filter (\s -> not $ or [s == "Agda", s == "univ"]) allmods in
  let uniquemods = sortUniq filteredmods in
  let reqBase = if optDkEtaMode opts
                then "require open AgdaTheory.eta.Base;"
                else "require open AgdaTheory.noEta.Base;" in
  let reqList = ([reqBase, "require open AgdaTheory.Levels;", ""] ++) $
                map (\s -> "require tests." ++ s ++ " as " ++ s ++ ";") uniquemods in
  let requires = intercalate "\n" reqList in
  requires ++ "\n" ++  s


filePath :: DkOptions -> ModuleName -> String
filePath opts mods =
  let concMods = modName2DkModIdent mods in
  -- If a directory is not given by the user, we just use the current one.
  let dir = case optDkDir opts of Nothing -> ""
                                  Just s  -> s  in
  let mod = dropAll (intercalate "__" concMods) in
  let extension = case optDkModeLp opts of False -> ".dk"
                                           True  -> ".lp" in
  dir ++ mod ++ extension

orderDeclRules :: [(Int32,DkDocs)] -> DkModName -> Doc
orderDeclRules l mods = orderDeclRules' 0 mods empty empty empty (sortOn fst l)

-- mut is an integer to detect if two declarations are mutual.
-- accTy contains the declaration of types (which comes before the ones of constructors).
-- accTy is the "real" accumulator, ie once a mutual block is processed, the result is stored here.
-- accOther contains constructors declarations.
-- accRules contains rules.
-- In this function, we can rely on the mutuality, because a type constructor is considered mutual with its constructors.
orderDeclRules' :: Int32 -> DkModName -> Doc -> Doc -> Doc -> [(Int32,DkDocs)] -> Doc
orderDeclRules' mut mods accTy accOther accRules []                 =
  accTy <> accOther <> accRules
orderDeclRules' mut mods accTy accOther accRules l@((m,(a,b,c)):tl)
  | m==mut =
      orderDeclRules' mut mods
            (accTy    <> a)
            (accOther <> b)
            (accRules <> c)
            tl
  | otherwise =
      orderDeclRules' m mods (accTy <> accOther <> accRules) empty empty l

------------------------------------------------------------------------------
-- The main function --
------------------------------------------------------------------------------

dkCompileDef :: DkOptions -> DkModuleEnv -> IsMain -> Definition -> TCM DkCompiled
dkCompileDef dkOpts env _ def@(Defn {defCopy=isCopy, defName=n, theDef=d, defType=t, defMutual=MutId m}) =
  if isCopy
  then do
    reportSDoc "toDk" 8 $ (\x -> text "  No compilation of"<+>x<+>text "which is a copy") <$> AP.prettyTCM n
    return Nothing
  else do
    reportSDoc "toDk" 3 $ (text "  Compiling definition of" <+>) <$> AP.prettyTCM n
    reportSDoc "toDk" 10 $ return $ text "    of type" <+> pretty t
    reportSDoc "toDk" 60 $ return $ text "    " <> pretty def

    inTopContext $ do
      reportSDoc "toDk" 15 $ return $ text "Getting type"
      t' <- reconstructParametersInType' defaultAction t -- t with parameters reconstructed
      typ        <- translateType env t'
      reportSDoc "toDk" 15 $ return $ text "Getting name"      
      Right name <- qName2DkName env n -- n is not a copy
      reportSDoc "toDk" 15 $ return $ text "Getting kind"
      kind       <- getKind env t
      reportSDoc "toDk" 15 $ return $ text "Getting staticity"
      stat       <- extractStaticity n d
      reportSDoc "toDk" 15 $ return $ text "Getting rules of " <+> pretty d
      rules      <- extractRules env n d t

      let dkDef = DkDefinition
            { name      = name
            , staticity = stat
            , typ       = typ
            , kind      = kind
            , rules     = rules}

      let dkMode = case (optDkModeLp dkOpts) of False -> DkMode
                                                True  -> LpMode
      let printedDef = toDkDocs (modName2DkModIdent env) dkMode dkDef
      return $ Just (m, printedDef)

translateType :: DkModuleEnv -> Type -> TCM DkTerm
-- a type is a term with a sort annotation (as in nat : Set0)
-- to translate it, we extract the term and ignore the sort
translateType env (El {unEl=ty}) = translateTerm env ty

extractStaticity :: QName -> Defn -> TCM IsStatic
extractStaticity _ (Axiom _)         = return Static
extractStaticity _ (DataOrRecSig {}) = return Static
extractStaticity _ GeneralizableVar  = return Static
extractStaticity n (Function {})     = do
  test <- isRecordConstructor n
  return $ case test of
    Nothing -> Defin
    Just {} -> Static
extractStaticity _ (Datatype {})     = return TypeConstr
extractStaticity _ (Record {})       = return TypeConstr
extractStaticity _ (Constructor {})  = return Static
extractStaticity _ (Primitive {})    = return Defin
-- trying to guess the following ones, not sure
extractStaticity _ (PrimitiveSort {})    = return Defin
extractStaticity _ (AbstractDefn {})    = return Static


  
extractRules :: DkModuleEnv -> QName -> Defn -> Type -> TCM [DkRule]
extractRules env n (funDef@Function {}) ty =
  do

{-    
    
    -- TO TEST ELIM PATT MATCH --
    let Just compiledClauses = funCompiled funDef
    reportSDoc "toDk.elimPattMatch" 20 $ return $ pretty compiledClauses    
    TelV{ theTel = tel, theCore = returnTy} <- telView ty
    t <- compiledClausesToCase tel returnTy compiledClauses
    let t' = teleLam tel t
    reportSDoc "toDk.elimPattMatch" 20 $ AP.prettyTCM t'
    reportSDoc "toDk.elimPattMatch" 20 $ AP.prettyTCM ty
--    checkInternal t' CmpLeq ty
    -- END --

    rhsDk <- translateTerm env etaMode t'
    Right dkName <- qName2DkName env etaMode n

    return $ [DkRule
      { decoding  = False
      , context   = []
      , headsymb  = dkName
      , patts     = []
      , rhs       = rhsDk
      }]
-}

    -- if this is an alias function, it does not go through the covering checker,
    -- the only way to know if this is the case is to check if funCovering is empty
    -- and funClauses is not
    let getFunCovering = 
          if (length (funCovering funDef) == 0 && length (funClauses funDef) /= 0)
          then funClauses funDef 
          else funCovering funDef
                           
    
    -- gets the clauses to be translated
    clauses <- case funProjection funDef of
        Nothing -> do
        -- not a projection, we get the clauses after the covering checker          
          reportSDoc "toDk.clause" 20 $
            (text " taking clauses from funCovering : " <+>) <$>
            (return $ pretty $ getFunCovering )            
          return $ getFunCovering  
        Just proj  -> case projProper proj of
        -- this function is projection-like, but is it a real projection
        -- from a record?
          Nothing -> do
        -- not a record projection, we get clauses from funCovering
            reportSDoc "toDk.clause" 20 $
              (text " taking clauses from funCovering : " <+>) <$>
              (return $ pretty $ getFunCovering )            
            return $ getFunCovering
          Just _ -> do
        -- record projection, we take funClauses because projections don't go
        -- throught the covering checker          
            reportSDoc "toDk.clause" 20 $
              (text " taking clauses from funClauses : " <+>) <$>
              (return $ pretty $ funClauses funDef )
            return $ funClauses funDef

    l  <- mapM (clause2rule env n) clauses
    return $ catMaybes l


extractRules env n (Datatype {dataCons=cons, dataClause=dataClauses, dataPars=i, dataIxs=j}) ty=
  do
    {-
    -- TEST mkCaseMethod
    caseType <- mkCase n
    sort <- checkType' caseType
    reportSDoc "toDk.elimPattMatch" 20 $ AP.prettyTCM sort
    caseName <- freshName_ $ "case-D"
    modName <- freshName_ $ "testmod"         
    let caseQname = QName{qnameModule = MName{mnameToList = [modName]}, qnameName = caseName}
    addConstant caseQname $
      defaultDefn defaultArgInfo caseQname caseType WithoutK Axiom{axiomConstTransp=False}
    reportSDoc "toDk.elimPattMatch" 20 $ AP.prettyTCM caseType
    -- END OF TEST
-}

    l <- case dataClauses of
           Just c  -> sequence [clause2rule env n c, Just <$> decodedVersion env n (i+j)]
           Nothing -> sequence [Just <$> decodedVersion env n (i+j)]
    return $ catMaybes l
extractRules env n (t@Record {recClause=clauses, recPars=i, recConHead=hd, recFields=f}) ty =
  do
    translatedClauses <- maybe (return []) (\c -> sequence [clause2rule env n c]) clauses
    decodedVers <- sequence [Just <$> decodedVersion env n i]
    return $ catMaybes $ translatedClauses ++ decodedVers
    
extractRules env n (Primitive {primClauses=p}) ty =
  do
    recordCleaned <- mapM translateRecordPatterns p
    l <- mapM (clause2rule env n) recordCleaned
    return $ catMaybes l
extractRules _ _ _ _                            = sequence []

decodedVersion :: DkModuleEnv -> QName -> Int -> TCM DkRule
decodedVersion env nam i = do
  reportSDoc "toDk" 5 $ return $ text "  Decoding" <+> pretty nam
  Right nn@(DkQualified mods pseudo n) <- qName2DkName env nam -- nam is not a copy
  let decodedName = DkQualified mods ("TYPE":pseudo) n
  let hd = DkSpecial TermSymb
  ty <- defType <$> getConstInfo nam
  tele <- theTel <$> (telView ty)
  reportSDoc "toDk" 15 $ ((text "    In the context:") <+> ) <$> (AP.prettyTCM tele)
  addContext tele $
    unsafeModifyContext separateVars $ do
    tel <- getContext
    ctx <- extractContextNames tel
    patVars <- sequence (genVars ctx)
    rhs <- constructRhs tel 0 return (DkConst decodedName)
    return $ DkRule
      { decoding  = True
      , context   = ctx
      , headsymb  = hd
      , patts     = [DkJoker,DkFun nn patVars]
      , rhs       = rhs
      }
  where
    genVars = genVarsAux [] 0
    genVarsAux acc i []     = acc
    genVarsAux acc i (a:tl) =
      genVarsAux (((\x -> DkVar x i []) <$> (name2DkIdent <$> (nameOfBV i))):acc) (i+1) tl
    constructRhs :: [Dom(Name,Type)] -> Nat -> (DkTerm -> TCM DkTerm) -> DkTerm -> TCM DkTerm
    constructRhs []                     _ clo t = clo t
    constructRhs (Dom{unDom=(a,ty)}:tl) i clo t = do
      va <-  return $ var i
      vaPar <- reconstructParameters (raise (i+1) ty) va
      constructRhs tl (i+1) (\x -> clo =<< (DkApp x <$> translateTerm env vaPar)) t

clause2rule :: DkModuleEnv -> QName -> Clause -> TCM (Maybe DkRule)
clause2rule env nam c = do
  reportSDoc "toDk.clause" 5  $ ((text "  We are treating:") <+>) <$> (AP.prettyTCM nam)
  reportSDoc "toDk.clause" 10 $ return $ (text "  The clause is") <+> (pretty c)
  reportSDoc "toDk.clause" 20 $ ((text "  In the context:") <+> ) <$> (AP.prettyTCM (clauseTel c))
  reportSDoc "toDk.clause" 20 $ return $ (text "  The type is:") <+> (pretty (clauseType c))
  reportSDoc "toDk.clause" 20 $ return $ (text "  The body is:") <+> (pretty (clauseBody c))
  reportSDoc "toDk.clause" 50 $ return $ text $ "    More precisely:" ++ show (clauseBody c)
  case (clauseBody c) of
    -- Nothing means this is an absurd clause, with () at the end, so it has no body
    Nothing  -> return Nothing
    Just r   ->
      -- adds to the context the bound variables of the clause
      addContext (clauseTel c) $
      unsafeModifyContext separateVars $
      do
        reportSDoc "toDk2" 3 $ return $ text "On a changé le contexte"
        tele <- getContext
        ctx <- extractContextNames tele

        -- record projections clauses don't go throught the covering checker, so in
        -- particular the clauses do not contain the implicit arguments (which in
        -- this case are simply the record parameters), which are inserted by the
        -- covering checker. therefore, we get the number of implicit arguments, so we
        -- generate joker in order to fill the implicit arguments.
        -- for the othe functions, they already have the implicit arguments, as they
        -- have already went trough the covering checker
        imp <- isProjection nam        
        implicits <-
          case imp of
            Nothing                             -> return 0
            Just Projection{projProper=Nothing} -> return 0
            Just Projection{projProper=Just n}  ->
              (fromMaybe __IMPOSSIBLE__) <$> getNumberOfParameters n
        let impArgs = implicitArgs implicits (reverse ctx)
        
        reportSDoc "toDk2" 3 $ return $ text "On a les implicites"

        -- reconstructs the parameters of the rhs
        rhsExpanded <-
          case clauseType c of
            Nothing -> do
              -- No type stored in this clause (why?), so we can't do anything...
              reportSDoc "toDk.clause" 25 $ return $ text "    Clause without type !"
              return r
            Just t  -> do
              reportSDoc "toDk2" 3 $ return $ text "On a bien un type"
              r1 <- checkInternal' defaultAction r CmpLeq (unArg t)
              reportSDoc "toDk2" 3 $ return $ text "On a fait le premier chkIn"
              reconstructParameters' defaultAction (unArg t) r1
              
        reportSDoc "toDk.clause" 30 $ return $ text "    Parameters reconstructed"
        reportSDoc "toDk.clause" 40 $ return $ text "    The final body is" <+> pretty rhsExpanded
        reportSDoc "toDk2" 3 $ return $ text "On a reconstruit les paramètres"

        -- translates rhs
        rhsDk <- translateTerm env rhsExpanded

        -- gets the type of the name nam
        tyHd <- defType <$> getConstInfo nam

        
        reportSDoc "toDk2" 3 $ return $ text "On a traduit à droite"
        let tyInst = piApply tyHd (map (defaultArg . patternToTerm . snd) impArgs)
        reportSDoc "toDk2" 3 $ return $ text "On extrait les patterns"


        Right headSymb <- qName2DkName env nam -- nam is not a copy


        patterns <- extractPatterns env (namedClausePats c) tyInst (map fst impArgs) headSymb
        case patterns of
          Nothing -> return Nothing
          Just (headSymb, patts) -> do

            reportSDoc "toDk2" 3 $ return $ text "On a extrait les patterns"
            reportSDoc "toDk2" 3 $ return $ text "On a extrait les p " <+> pretty (namedClausePats c)
            reportSDoc "toDk2" 3 $ return $ text "On a extrait les p " <+> pretty nam

            return $ Just DkRule
              { decoding  = False
              , context   = ctx
              , headsymb  = headSymb
              , patts     = patts
              , rhs       = rhsDk
              }

    where
      implicitArgs 0 locCtx = []
      implicitArgs n (h:tl) =
        (DkVar h (length tl) [], varP (DBPatVar h (length tl))):(implicitArgs (n-1) tl)

-- gets the names of the types in the context
extractContextNames :: Context -> TCM DkCtx
extractContextNames = extractContextAux []

extractContextAux :: DkCtx -> Context -> TCM DkCtx
extractContextAux acc [] = return $ reverse acc
extractContextAux acc (Dom {unDom=(n,t)}:r) = extractContextAux (name2DkIdent n:acc) r


extractPatterns ::  DkModuleEnv ->
                    [NamedArg DeBruijnPattern] -> --patterns p1 .. pk to be translated
                    Type -> -- type of already translated part
                    [DkPattern] -> -- already translated part
                    DkName -> -- head of the already translated part
                    TCM (Maybe (DkName, [DkPattern]))
extractPatterns env [] typ dkPatts dkHead = do
  reportSDoc "toDk.pattern" 15 $ return $ text $ "    Finished extraction, the result is " ++ show (dkHead, dkPatts)
  return $ Just (dkHead, dkPatts)

extractPatterns env (p:patts) typ dkPatts dkHead = do
  reportSDoc "toDk.pattern" 15 $ return $ text $ "    The current state is  " ++ show (dkHead, dkPatts)
  reportSDoc "toDk.pattern" 15 $ return $ text "    Now we begin translating  " <+> pretty p
  
  typ <- normalise typ
  result <- extractPattern env p typ
  case result of
    Nothing ->
      -- we get nothing when we find a hott clause
      return Nothing 
    Just (translatedPattern, newType) -> do
      case namedArg p of
        ProjP _ _ -> do
          -- the application of f e1 ... en to the projection p should be translated as
          -- p a1 .. ak (f e1 .. en), where the a1 .. ak are the parameters of the record

          -- gets the head symbol and the arguments
          DkFun head args <- return translatedPattern

          extractPatterns env patts newType (args ++ [DkFun dkHead dkPatts]) head

        _ -> do
          extractPatterns env patts newType (dkPatts ++ [translatedPattern]) dkHead


-- if we are translating a pattern p which is applied to f e1 .. ek, then we need
-- the type of f e1 .. ek. we return the translation of p and the type
-- of f e1 .. ek p
extractPattern :: DkModuleEnv -> NamedArg DeBruijnPattern -> Type ->
                  TCM (Maybe (DkPattern, Type))
extractPattern env p applyingType = do
  reportSDoc "toDk.pattern" 15 $ return $ text "    Extraction of the pattern" <+> pretty p

  let patt = namedThing (unArg p)
  case patt of
    VarP _ (DBPatVar {dbPatVarIndex=i})  -> do
      reportSDoc "toDk2" 3 $ return $ text "VarP"
      nam <- nameOfBV i

      -- gets type of f e1 ... ek p
      let finalTy = piApply applyingType [defaultArg (patternToTerm (namedArg p))]

      return $ Just (DkVar (name2DkIdent nam) i [], finalTy)

    DotP _ t                             -> do
      reportSDoc "toDk2" 3 $ return $ text "DotP"
      
      let patternType = case applyingType of
                          El _ (Pi (Dom{unDom=domainType}) _) -> domainType
                          _ -> __DUMMY_TYPE__
 
      tChk <- checkInternal' defaultAction t CmpLeq patternType
      tRecons <- reconstructParameters' defaultAction patternType tChk
      term <- translateTerm env tRecons

      -- gets type of f e1 ... ek p
      let finalTy = piApply applyingType [defaultArg (patternToTerm (namedArg p))]
      
      return $ Just (DkGuarded term, finalTy)
--      return $ (DkJoker, finalTy)

    ConP (ConHead {conName=h}) ci tl     -> do
      reportSDoc "toDk2" 3 $ return $ text "ConP" <+> pretty h

      -- let f e1 ... ek the part of the patterns already translated and applyingType
      -- its type. the pattern p we are translating applies to the right of it
      -- so applyingType must be a product (x:domainType) -> coDomainType.
      -- therefore, domainType gives the type of the pattern p we are translating.

      let patternType = case applyingType of
                          El _ (Pi (Dom{unDom=domainType}) _) -> domainType
                          _ -> __DUMMY_TYPE__

      -- let p = g a1 ... ak be the pattern we are translating. As g is a
      -- constructor of an inductive type, its type is of the form
      -- g : {x1 : X1} -> ... -> {xl : Xl} ->
      --     (a1 : A1) -> ... -> (ak : Ak) -> T x1 ... xl i1 ... ij
      -- where the x are the params and i the indices of the inductive type. The
      -- parameters are implicit in agda, and thus we need to recover them to
      -- translate p correctly. To do this, we look at the domainType, which will be
      -- T x1 ... xl i1 ... ij and we extract the parameters

      -- gets head symbol type
      headType <- normalise =<< defType <$> getConstInfo h

      -- gets num of params of head symbol
      numParams <- fromMaybe (error "Why no Parameters?") <$> getNumberOfParameters h

      reportSDoc "toDk.clause" 30 $ return
        $ text "    The type of this applied constructor is" <+> pretty patternType
      reportSDoc "toDk.clause" 50 $ return
        $ text "    Type of the constructor is" <+>  pretty headType
      reportSDoc "toDk.clause" 30 $ return
        $ text "    We investigate for" <+>int numParams<+>text "params"


      -- gets the parameters
      (tyArgs, params) <-
        case patternType of
          El _ (Def _ l) -> do
            reportSDoc "toDk.clause" 30 $ return
              $ text "    Found parameters"
            caseParamFun headType (take numParams l)
          otherwise      ->  do
            reportSDoc "toDk.clause" 30 $ return
              $ text "    Parameters not found, the type is not a Def _ l"
            return $ (__DUMMY_TYPE__, replicate numParams DkJoker)

      -- now we have the parameters which are applied to the head symbol g. it's left
      -- to translate the a1 ... ak which are applied to them

      -- translates head symbol
      Right head <- qName2DkName env h

      -- translates the arguments
      args <- extractPatterns env tl tyArgs params head
      -- remember that it might me empty because we found a hott pattern in the process
      case args of
        Nothing -> return Nothing
        Just (head, args) -> do
          let translatedPatt = DkFun head args

          -- gets type of f e1 ... ek p
          let finalTy = piApply applyingType [defaultArg (patternToTerm (namedArg p))]
     
          return $ Just (translatedPatt, finalTy)

    LitP _ l                            -> do
      reportSDoc "toDk2" 3 $ return $ text "LitP"
      -- gets type of f e1 ... ek p
      let finalTy = piApply applyingType [defaultArg (patternToTerm (namedArg p))]
      return $ Just (DkPattBuiltin (translateLiteral l), finalTy)
    ProjP _ nam                         -> do
      reportSDoc "toDk2" 3 $ return $ text "ProjP"

      -- we are translating a projection p which is applied to the term f e1 .. ek of
      -- type applyingType. the term f e1 ... ek must be of a record type, so we
      -- should translate this application as p (f e1 .. ek). however, we also need
      -- to translate the parameters of the record, as the type of p is actually
      -- p : {x1 : X1} -> ... -> {xn : Xn} -> Rec x1 .. xn. so the translation
      -- should be p x1 .. xn (f e1 .. ek).
      -- we therefore extract the parameters x1 .. xn from the type of (f e1 .. ek)
      
      -- gets projection def
      imp <- isProjection nam

      -- gets head symbol type
      headType <- normalise =<< defType <$> getConstInfo nam

      -- gets number of parameters
      numParams <-
        case imp of
          Just Projection{projProper = Just _, projFromType = Arg _ nn}  -> do
                maybeNumParams <- getNumberOfParameters nn
                case maybeNumParams of Just n -> return n
                                       _      -> error "Why no params?"
          _ -> error "What is this projection?"
      
      -- gets the parameters
      (tyArgs, params) <-
        case applyingType of
          El _ (Def _ l) -> do
            reportSDoc "toDk.clause" 30 $ return
              $ text "    Found parameters"
            caseParamFun headType (take numParams l)
          otherwise      ->  do
            reportSDoc "toDk.clause" 30 $ return
              $ text "    Parameters not found, the type is not a Def _ l"
            return $ (__DUMMY_TYPE__, replicate numParams DkJoker)
      
      Right dkNam <- qName2DkName env nam

      -- gets type of p x1 .. xn (f e1 .. ek)
      -- HYPOTHESIS: If proj : {x1:X1} -> .. -> {xn:Xn} -> (rec:Rec x1 .. xn) -> field
      -- is a projection, then field does not depend on rec

      finalTy <- case tyArgs of
                   (El _ (Pi _ u)) -> return $ unAbs u
                   _ -> do
                     reportSDoc "toDk.clause" 30 $ return
                       $ text "    Not an elim, continuing with a dummy "
                       <+> pretty tyArgs
                     return __DUMMY_TYPE__
                                
      return $ Just (DkFun dkNam params, finalTy)

    otherwise                           -> do
      reportSDoc "toDk.clause" 30 $ return $ text $ "Unexpected pattern of HoTT: " ++ show patt
      return Nothing
  where

    caseParamFun :: Type -> Elims -> TCM (Type,[DkPattern])
    caseParamFun tyCons els = do
      reportSDoc "toDk2" 3 $ return $ text "ELIMS ARE ..."
      caseParamFun' tyCons els []

    caseParamFun' tyCons [] acc = do
      return (tyCons, reverse acc)
    caseParamFun' tyCons@(El _ (Pi (Dom {unDom=tyArg}) _)) ((Apply (Arg _ t)):tl) acc = do
      reportSDoc "toDk2" 3 $ return $ text "We start caseParamFun' with ..."
      reportSDoc "toDk2" 3 $ return $ text "The type is ..."
      ctxHere <- getContext
      reportSDoc "toDk2" 3 $ return $ text "The context is ..."
      tEta <- checkInternal' defaultAction t CmpLeq tyArg
      reportSDoc "toDk2" 3 $ return $ text "Eta-expansion done"
      tPar <- reconstructParameters' defaultAction tyArg tEta
      reportSDoc "toDk2" 3 $ return $ text "params reconstructed"
      tDk <- translateTerm env tPar
      reportSDoc "toDk2" 3 $ return $ text "term translated"
      caseParamFun' (piApply tyCons [defaultArg t]) tl (DkGuarded tDk:acc)

substi :: [DkPattern] -> DkTerm -> DkTerm
substi l (DkSort s)               =
  DkSort (substiSort l s)
substi l (DkProd s1 s2 x a b)     =
  DkProd (substiSort l s1) (substiSort l s2) x (substi l a) (substi l b)
substi l (DkProjProd s1 s2 x a b) =
  DkProjProd (substiSort l s1) (substiSort l s2) x (substi l a) (substi l b)
substi l (DkQuantifLevel s x a)   =
  DkQuantifLevel (substiSort l s) x (substi l a)
substi _ t@(DkConst _)            = t
substi l (DkApp t u)              =
  DkApp (substi l t) (substi l u)
substi l (DkLam x _ t)            =
  DkLam x Nothing (substi l t)
substi l (DkDB _ i)               =
  termOfPattern (l !! i)
substi l (DkLevel lv)             =
  DkLevel (substiLvl l lv)

substiLvl l (LvlMax n preLvls) = LvlMax n $ map (substiPreLvl l) preLvls

substiPreLvl l (LvlPlus i t) = LvlPlus i (substi l t)

substiSort l (DkSet lv)    = DkSet (substiLvl l lv)
substiSort l (DkProp lv)   = DkProp (substiLvl l lv)
substiSort _ DkSetOmega    = DkSetOmega
substiSort l (DkUniv s)    = DkUniv (substiSort l s)
substiSort l (DkPi s1 s2)  = DkPi (substiSort l s1) (substiSort l s2)
substiSort _ DkDefaultSort = DkDefaultSort

translateElim :: DkModuleEnv -> DkTerm -> Elims -> TCM DkTerm
-- empty elimination, return the applying term
translateElim env t []                  = return t
-- we have t applied to el = (e tl). the translation is given by translating
-- e, applying it to t and the callind translateElim env (t e) tl
translateElim env t (el@(Apply e):tl)      = do
  arg <- translateTerm env (unArg e)
  translateElim env (DkApp t arg) tl
-- elimination have gone through unspining, so we cannot have proj eliminations
translateElim env t (el@(Proj _ qn):tl)    = do
  reportSDoc "toDk" 2 $ ((text "    Pb with:" <+> printTerm Top [] DkMode [] t <+>)<$> AP.prettyTCM el)
  error "Unspining not performed!"
translateElim env t ((IApply _ _ _):tl) = error "Unexpected IApply"

translateTerm :: DkModuleEnv -> Term -> TCM DkTerm
-- Var is a variable possibly applied to a sequence of eliminations (x es)
translateTerm env (Var i elims) = do
  -- gets name of bound variable
  nam <- nameOfBV i
  -- the result is the name of the variable applied to the translation
  -- of the elimination
  translateElim env (DkDB (name2DkIdent nam) i) elims

translateTerm env (Lam _ ab) = do
  ctx <- getContext
  -- n will be name of the abstracting variable
  let n = freshStr ctx (absName ab)
  -- (adds the name n to the context permanently or just does an action
  -- with n in the context?)
  addContext n $
    do
      -- translates the term inside the abstraction, on this new context
      body <- translateTerm env (unAbs ab)
      -- gets name of debrunji index 0 (why isn't this always n?)
      nam <- nameOfBV 0
      return $ DkLam (name2DkIdent nam) Nothing body

-- builtin things, like strings, integers, etc
translateTerm env (Lit l) =
  return $ translateLiteral l

-- a function symbol n applied to a list of eliminations
translateTerm env (Def n elims) = do
  -- translate the function symbol
  nn <- qName2DkName env n
  case nn of
    -- if we get a constant name, we return it applied to the translation of the elim
    Right nam -> translateElim env (DkConst nam) elims
    -- if we get a term (why?) we translate it applied to the elim
    Left tt -> translateTerm env (tt `applyE` elims)

translateTerm env (Con hh@(ConHead {conName=h}) i elims) = do
  nn <- qName2DkName env h
  case nn of
    Right nam -> translateElim env (DkConst nam) elims
    Left tt -> translateTerm env (tt `applyE` elims)

translateTerm env (Pi d@(Dom {unDom=a}) bb) = do
  ctx <- getContext
  -- nn is the name of the abstracting variable (Pi nn : a. bb)
  let nn = freshStr ctx (absName bb)
  -- translates the domain type
  dom <- translateType env a
  -- gets kind s_a of the domain type
  ka <- getKind env a
  case bb of
    -- this is a real dependent product, we need to add nn : d to the context
    -- before calculating the domain type
    Abs n b ->
      addContext (nn,d) $ do
        -- translates codomain type
        body <- translateType env b
        -- gets codomain sort
        kb <- getKind env b
        -- gets name of type parameter (is it different from nn?)
        nam <- nameOfBV 0
        -- analyse the codomain type
        case a of
          -- is it a constant type?
          El {unEl=Def h []} -> do
            hd <- qName2DkName env h
            -- is it Level?
            if hd == Right (DkQualified ["Agda","Primitive"] [] "Level")
              -- yes! this is a a level quantification
            then return $ DkQuantifLevel kb (name2DkIdent nam) body
              -- no! this is a normal product
            else return $ DkProd ka kb (name2DkIdent nam) dom body
          -- also a normal product
          otherwise ->
            return $ DkProd ka kb (name2DkIdent nam) dom body
    -- not a real dependent product, just a regular function arrow a -> bb
    NoAbs n b -> do
      -- translate the codomain type
      body <- translateType env b
      -- gets codomain sort
      kb <- getKind env b
      -- gets name of type parameter (is it different from nn?)
      nam <- addContext (nn,d) $ nameOfBV 0
      return $ DkProd ka kb (name2DkIdent nam) dom body

translateTerm env (Sort s) = do
  ss <- extractSort env s
  return $ DkSort ss
  
translateTerm env (Level lev) = do
  lv <- lvlFromLevel env lev
  return $ DkLevel lv
  
translateTerm env (MetaV {}) = error "Not implemented yet : MetaV"
translateTerm env (DontCare t) = translateTerm env t
translateTerm env (Dummy _ _) = error "Not implemented yet : Dummy"

extractSort :: DkModuleEnv -> Sort -> TCM DkSort
extractSort env (Type i)                  =
  DkSet <$> lvlFromLevel env i
extractSort env (Prop i)                  =
  DkProp <$> lvlFromLevel env i
-- for the time beeing we translate all the SetOmegai to the same sort
-- this clearly makes the theory inconsistent, but it should work for now
extractSort env (Inf _ _)                 =
  return DkSetOmega
extractSort env SizeUniv                  =
  return $ DkSizeUniv

-- not sure about the following change

extractSort env (PiSort _ s t) = do
  dom <- extractSort env s
  codom <- extractSort env (unAbs t)
  return $ DkPi dom codom

--extractSort env (PiSort (Dom{unDom=s}) t) = do
--  dom <- extractSort env (_getSort s)
--  codom <- extractSort env (unAbs t)
--  return $ DkPi dom codom
extractSort env (UnivSort s)              =
  DkUniv <$> extractSort env s
extractSort _ _                           =
  return DkDefaultSort

lvlOf :: DkModuleEnv -> Sort -> TCM Lvl
lvlOf env (Type i) = lvlFromLevel env i
lvlOf env (Prop i) = lvlFromLevel env i

getKind :: DkModuleEnv -> Type -> TCM DkSort
getKind env (El {_getSort=s}) = extractSort env s

-- the two functions were modified to account for the new representation of
-- levels in agda
lvlFromLevel :: DkModuleEnv -> Level -> TCM Lvl
lvlFromLevel env (Max i l) =
  do
    preLvls <- mapM (preLvlFromPlusLevel env) l
    return $ LvlMax (fromInteger i) preLvls

preLvlFromPlusLevel :: DkModuleEnv -> PlusLevel -> TCM PreLvl
preLvlFromPlusLevel env (Plus i t) = LvlPlus (fromInteger i) <$> translateTerm env t

translateLiteral :: Literal -> DkTerm
translateLiteral (LitNat    i)   = DkBuiltin (DkNat (fromInteger i))
translateLiteral (LitWord64 _)   = error "Unexpected literal Word64"
translateLiteral (LitFloat  _)   = error "Unexpected literal Float"
translateLiteral (LitString s)   = DkBuiltin (DkString (unpack s))
translateLiteral (LitChar   c)   = DkBuiltin (DkChar c)
translateLiteral (LitQName  _)   = error "Unexpected literal QName"
translateLiteral (LitMeta   _ _) = error "Unexpected literal Meta"

addEl :: Term -> Elim -> Term
addEl (Var i elims) e = Var i (elims++[e])
addEl (Def n elims) e = Def n (elims++[e])
addEl (Con h i elims) e = Con h i (elims++[e])
addEl _ _ = error "Those terms do not expect elimination"


--------------------------------------------------------------------------------
-- Translation of Name and QName function
--------------------------------------------------------------------------------

qName2DkName :: DkModuleEnv -> QName -> TCM (Either Term DkName)
qName2DkName env qn@QName{qnameModule=mods, qnameName=nam} =
  do
    topMod <- topLevelModuleName mods
    def <- getConstInfo qn
    if defCopy def
    then do
      let ty = defType def
      -- why do we need to do etaExpansion here? why do we need to do this
      -- only to get the name?
      reportSDoc "toDk2" 3 $ return $ text "ty Here" <+> pretty ty
      -- this first step is just to eta-expand, in order to trigger reduction
      tChk <- checkInternal' defaultAction (Def qn []) CmpLeq ty
      reportSDoc "toDk2" 3 $ return $ text "tChk OK"
      tRed <- normalise tChk
      reportSDoc "toDk2" 3 $ return $ text "tRed OK"
      -- We have to do it again since normalise eliminated it
      tChk2 <- checkInternal' defaultAction tRed CmpLeq ty
      reportSDoc "toDk2" 3 $ return $ text "tChk2 OK"
      tRecons <- reconstructParameters' defaultAction ty tChk2
      reportSDoc "toDk2" 3 $ return $ text "tRecons OK"
      return $ Left tRecons
    else
      let otherMods = stripPrefix (mnameToList topMod) (mnameToList mods) in
      return $ Right $
        DkQualified (modName2DkModIdent topMod) (maybe [] (map name2DkIdent) otherMods) (name2DkIdent nam)

name2DkIdent :: Name -> DkIdent
name2DkIdent (Name {nameId=NameId id _, nameConcrete=CN.Name {CN.nameNameParts=n}}) =
  let list = toList n in
  let s = concat (map namePart2String list) in
  if s == ".absurdlambda"
  then s ++ ('-' : show id) -- .absurdlambda is not a user written name, it happens to be not unique in some files.
  else s
name2DkIdent (Name {nameConcrete=CN.NoName {}}) =
  "DEFAULT"

namePart2String :: CN.NamePart -> String
namePart2String CN.Hole  = "_"
namePart2String (CN.Id s) = s

modName2DkModIdent :: ModuleName -> DkModName
modName2DkModIdent (MName {mnameToList=l}) = map name2DkIdent l

separateVars :: Context -> Context
separateVars = separateAux ["_"]

separateAux used [] = []
--separateAux used ((d@Dom{unDom=(n@Name{nameConcrete=cn@CN.Name{CN.nameNameParts=l}},ty)}):tl) =
separateAux used ((d@Dom{unDom=(n@Name{nameConcrete=cn},ty)}):tl) =
  let s= name2DkIdent n in
  let ss = computeUnused used (-1) s in
  let ns = (CN.Id ss) :| [] in
  d {unDom=(n {nameConcrete= cn {CN.nameNameParts=ns}},ty)}:(separateAux (ss:used) tl)

-- gets the list of names used in the context
usedVars :: Context -> [String]
usedVars = map (name2DkIdent . fst . unDom)

-- used by freshStr
computeUnused used i s =
  let ss = if i==(-1) then s else s++(show i) in
  if elem ss used
  then computeUnused used (i+1) s
  else ss

-- freshStr ctx name returns either name or nameX for some integer X,
-- such that the returned string is not used in the context
freshStr ctx = computeUnused ("_":(usedVars ctx)) (-1)
