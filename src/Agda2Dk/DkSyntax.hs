module Agda2Dk.DkSyntax where

import Data.Word
import Data.List (sort)
import Data.List.Extra (nubOrd)
-- This next line needs the package Unique, install it from Cabal
import Data.List.Unique (sortUniq)
import Data.Int
import Data.Char


-- hides (<>), as there was a conflit with the (<>) defined here
import Prelude hiding ((<>))

import Text.PrettyPrint

import Agda.Syntax.Internal
import qualified Agda.Syntax.Concrete.Name as CN
import Agda.Utils.Impossible

type DkModName = [String]

type DkIdent = String

class PrettyDk a where
  prettyDk :: DkModName -> a -> Doc

data DkDefinition =
   DkDefinition
    { name      :: DkName
    , staticity :: IsStatic
    , typ       :: DkTerm
    , kind      :: DkSort
    , rules     :: [DkRule]
    }


etaExpandSymb :: DkName
etaExpandSymb = DkQualified ["Agda"] [] "etaExpand"

printDecl :: DkModName -> DkDefinition -> Doc
printDecl mods (DkDefinition {name=n, staticity=b, typ=t, kind=k}) =
  let special =
        case n of
          DkQualified ["Agda", "Primitive"] [] "Level" ->
            text "rule Agda.Term _ Level ↪ univ.Lvl;\n"
          DkQualified ["Agda", "Primitive"] [] "lzero" ->
            text "rule lzero ↪ univ.zero;\n"
          DkQualified ["Agda", "Primitive"] [] "lsuc"  ->
            text "rule lsuc ↪ univ.s;\n"
          DkQualified ["Agda", "Primitive"] [] "_⊔_"   ->
            text "rule {|_⊔_|} ↪ univ.max;\n"
          otherwise                                    -> empty
  in
  let kw =
        case b of
          Defin      -> text ""
          TypeConstr -> printDecodedDecl mods n t
          Static     -> text ""
  in
  let typDecl = printSort Nested mods k <+> printTerm Nested mods t in
    kw <> text "symbol" <+> prettyDk mods n <+> text ": Agda.Term" <+> typDecl <> text ";\n" <> special

printDecodedDecl :: DkModName -> DkName -> DkTerm -> Doc
printDecodedDecl mods (DkQualified _ pseudo id) t =
  let ident = "TYPE__" ++ (concat (map (++ "__") pseudo)) ++ id in
  text "symbol" <+> printIdent ident <+> char ':' <+> decodedType mods t <> text ";\n"

decodedType :: DkModName -> DkTerm -> Doc
decodedType mods (DkSort _)              = text "TYPE"
decodedType mods (DkProd s1 _ id t u)    =
  let domDecl = printSort Nested mods s1 <+> printTerm Nested mods t in
  text "Π" <+> parens (printIdent id <+> text ": Agda.Term" <+> domDecl) <+> text "," <+> decodedType mods u
decodedType mods (DkQuantifLevel _ id t) =
  text "Π" <+> parens (printIdent id <+> text ": univ.Lvl") <+> text "," <+> decodedType mods t

printRules :: DkModName -> DkDefinition -> (DkRule -> Bool) -> [Doc]
printRules mods (DkDefinition {rules=l}) f = map (prettyDk mods) (filter f l)

type Lvl = [PreLvl]

printLvl :: DkModName -> Lvl -> Doc
printLvl mods l =
  printPreLvlList mods [] l

printPreLvlList :: DkModName -> [DkIdent] -> Lvl -> Doc
printPreLvlList mods ruleVars []     = text "univ.zero"
printPreLvlList mods ruleVars (a:[]) = prettyDk_preLvl mods ruleVars a
printPreLvlList mods ruleVars (a:tl) =
  parens $ text "univ.max" <+> prettyDk_preLvl mods ruleVars a <+> printPreLvlList mods ruleVars tl

data PreLvl =
    LvlInt Int
  | LvlPlus Int DkTerm

prettyDk_preLvl :: DkModName -> [DkIdent] -> PreLvl -> Doc
prettyDk_preLvl mods ruleVars (LvlInt i)    =
  unary i
prettyDk_preLvl mods ruleVars (LvlPlus i t) =
  applyN i (parens . (text "univ.s" <+>)) (printTerm' Nested mods ruleVars t)
  where applyN i f x = iterate f x !! i


-- TODO adapt All prettyDk to deal with rule binders $
--instance PrettyDk PreLvl where
-- prettyDk mods (LvlInt i)    =
--   unary i
-- prettyDk mods (LvlPlus i t) =
--   applyN i (parens . (text "univ.s" <+>)) (printTerm Nested mods t <> text "-oi")
--  where applyN i f x = iterate f x !! i

unary :: Int -> Doc
unary x
  | x==0 = text "univ.zero"
  | x>0  = parens $ (text "univ.s")<+> (unary (x-1))

data DkSort =
    DkSet Lvl
  | DkProp Lvl
  | DkSetOmega
  | DkUniv DkSort
  | DkPi DkSort DkSort
  | DkDefaultSort

printSort :: Position -> DkModName -> DkSort -> Doc
printSort pos mods (DkSet i)     =
  paren pos $ text "Agda.set"  <+> printLvl mods i
printSort pos mods (DkProp i)    =
  paren pos $ text "Agda.prop" <+> printLvl mods i
printSort pos _    DkSetOmega    =
  text "Agda.sortOmega"
printSort pos mods (DkUniv s)    =
  paren pos $ text "Agda.axiom" <+> printSort pos mods s
printSort pos mods (DkPi s t)    =
  paren pos $
    text "Agda.rule" <+> printSort pos mods s <+> printSort pos mods t
printSort pos _    DkDefaultSort =
  text "DEFAULT_SORT"

data DkRule =
   DkRule
    { decoding :: Bool
    , context  :: DkCtx
    , headsymb :: DkName
    , patts    :: [DkPattern]
    , rhs      :: DkTerm
    }

instance PrettyDk DkRule where
  prettyDk mods (DkRule {context=c, headsymb=hd, patts=patts, rhs=rhs}) =
    -- gets the indices of the free variables of the rule
    let freeVarList = concat (map usedIndex patts) in
    -- converts the indices of the vars to names
    let freeVarNames = getVarNames freeVarList c in
    -- prints the lhs
    let lhs = prettyDk mods hd <+> hsep (map (printPattern' Nested mods freeVarNames) patts) in
    -- prints the rhs
    let rhs' = printTerm' Top mods freeVarNames rhs in
    text "rule" <+> lhs <+> text "↪" <+> rhs' <> text ";\n"      


-- returns the indices of variables appearing free in a pattern
usedIndex :: DkPattern -> [Int]
usedIndex (DkVar _ i l)  = i:(concat (map usedIndex l))
usedIndex (DkFun f l)  = concat (map usedIndex l)
usedIndex (DkLambda _ p) = map (\n -> n-1) (usedIndex p)
usedIndex _              = []

data DkTerm =
    DkSort DkSort
  | DkProd DkSort DkSort DkIdent DkTerm DkTerm
  | DkProjProd DkSort DkSort DkIdent DkTerm DkTerm
  | DkQuantifLevel DkSort DkIdent DkTerm
  | DkConst DkName
  | DkApp DkTerm DkTerm
  | DkLam DkIdent (Maybe (DkTerm,DkSort)) DkTerm
  | DkDB DkIdent Int
  | DkLevel Lvl
  | DkBuiltin DkBuiltin

printTerm :: Position -> DkModName -> DkTerm -> Doc
printTerm pos mods t = printTerm' pos mods [] t

-- this version takes as ruleVars a list of the names of variables which should be
-- printed with a '$' before it
printTerm' :: Position -> DkModName -> [DkIdent] -> DkTerm -> Doc
printTerm' pos mods ruleVars (DkSort s)               =
  paren pos $
    text "Agda.code" <+> printSort Nested mods s
printTerm' pos mods ruleVars (DkProd s1 s2 n t u)     =
  let sorts = printSort Nested mods s1 <+> printSort Nested mods s2 in
  let domain =  printTerm' Nested mods ruleVars t in
  let codomain = parens (text "λ" <+> printIdent n <+> text "," <+> printTerm' Top mods ruleVars u) in
  paren pos $
    text "Agda.prod" <+> sorts <+> domain <+> codomain
printTerm' pos mods ruleVars (DkProjProd s1 s2 n t u)     =
  let sorts = printSort Nested mods s1 <+> printSort Nested mods s2 in
  let domain =  printTerm' Nested mods ruleVars t in
  let codomain = parens (text "λ" <+> printIdent n <+> text "," <+> printTerm' Top mods ruleVars u) in
  paren pos $
    text "Agda.proj_prod" <+> sorts <+> domain <+> codomain
printTerm' pos mods ruleVars (DkQuantifLevel s n u)   =
  let sorts = parens (text "λ" <+> printIdent n <+> text "," <+> printSort Top mods s) in
  let codomain = parens (text "λ" <+> printIdent n <+> text "," <+> printTerm' Top mods ruleVars u) in
  paren pos $
    text "Agda.qLevel" <+> sorts <+> codomain
printTerm' pos mods ruleVars (DkConst f)             =
  prettyDk mods f
printTerm' pos mods ruleVars (DkApp t u)              =
  case t of
    DkApp (DkApp (DkConst n) s) ty | n == etaExpandSymb ->
      case u of
        DkApp (DkApp (DkApp (DkConst n2) s2) ty2) v | n2 == etaExpandSymb ->
          printTerm' pos mods ruleVars $ DkApp (DkApp (DkApp (DkConst n) s) ty) v
        otherwise -> defaultCase
    otherwise -> defaultCase
  where
    -- Beta-redices can be created by the expansion of copies.
    defaultCase =
      let tPos =
            case t of
              DkLam _ _ _-> Nested
              otherwise -> Top
      in
      paren pos $
        printTerm' tPos mods ruleVars t <+> printTerm' Nested mods ruleVars u
printTerm' pos mods ruleVars (DkLam n Nothing t)      =
  paren pos $
    text "λ" <+> printIdent n <+> text "," <+> printTerm' Top mods ruleVars t
printTerm' pos mods ruleVars (DkLam n (Just (a,s)) t) =
  let typCode = printTerm' Nested mods ruleVars a in
  let annot = text "Agda.Term" <+> printSort Nested mods s <+> typCode in
  paren pos $
    text "λ" <+> printIdent n <+> char ':' <+> annot <+> text "," <+> printTerm' Top mods ruleVars t -- NOT SURE HERE
printTerm' pos mods ruleVars (DkDB n _)               =
  printIdent' ruleVars n
printTerm' pos mods ruleVars (DkLevel l)              =
  printPreLvlList mods ruleVars l
printTerm' pos mods ruleVars (DkBuiltin b)            =
  printBuiltin pos mods b

data DkBuiltin =
    DkNat    Int
  | DkChar   Char
  | DkString String

printBuiltin :: Position -> DkModName ->  DkBuiltin -> Doc
printBuiltin pos mods (DkNat i) =
  printTerm pos mods (fromBuiltinNat i)
printBuiltin pos mods (DkChar c) =
  printTerm pos mods (fromBuiltinChar c)
printBuiltin pos mods (DkString s) =
  printTerm pos mods (fromBuiltinString s)

fromBuiltinNat :: Int -> DkTerm
fromBuiltinNat i =
  let zero = DkConst $ DkQualified ["Agda", "Builtin", "Nat"] ["Nat"] "zero" in
  let suc = DkConst $ DkQualified ["Agda", "Builtin", "Nat"] ["Nat"] "suc" in
  iterate (\x -> DkApp suc x) zero !! i

fromBuiltinChar :: Char -> DkTerm
fromBuiltinChar c =
  let converter = DkConst $ DkQualified ["Agda", "Builtin", "Char"] [] "primNatToChar" in
  DkApp converter (fromBuiltinNat (fromEnum c))

fromBuiltinString :: String -> DkTerm
fromBuiltinString s =
  let converter = DkConst $ DkQualified ["Agda", "Builtin", "String"] [] "primStringFromList" in
  DkApp converter (fromBuiltinListOfChar s)

fromBuiltinListOfChar []     =
  let nil = DkConst $ DkQualified ["Agda", "Builtin", "List"] ["List"] "[]" in
  let lvl0 = DkConst $ DkQualified ["univ"] [] "zero" in
  let char_type = DkConst $ DkQualified ["Agda", "Builtin", "Char"] [] "Char" in
  DkApp (DkApp nil lvl0) char_type
fromBuiltinListOfChar (c:tl) =
  let cons = DkConst $ DkQualified ["Agda", "Builtin", "List"] ["List"] "_∷_" in
  let lvl0 = DkConst $ DkQualified ["univ"] [] "zero" in
  let char_type = DkConst $ DkQualified ["Agda", "Builtin", "Char"] [] "Char" in
  DkApp (DkApp (DkApp (DkApp cons lvl0) char_type) (fromBuiltinChar c)) (fromBuiltinListOfChar tl)

paren :: Position -> Doc -> Doc
paren pos =
  case pos of
    Top    -> id
    Nested -> parens

data DkPattern =
    DkVar DkIdent Int [DkPattern]
  | DkFun DkName [DkPattern]
  | DkLambda DkIdent DkPattern
  | DkPattBuiltin DkTerm
  | DkGuarded DkTerm
  | DkJoker

printPattern ::   Position -> DkModName -> DkPattern -> Doc
printPattern pos mods patt = printPattern' pos mods [] patt

-- this version takes as ruleVars a list of the names of variables which should be
-- printed with a '$' before it
printPattern' ::   Position -> DkModName -> [DkIdent] -> DkPattern -> Doc
printPattern' pos mods ruleVars (DkVar n _ [])  =
  printIdent' ruleVars n
printPattern' pos mods ruleVars (DkVar n _ l)  =
  paren pos $
    printIdent' ruleVars n <+> hsep (map (printPattern' Nested mods ruleVars) l)
printPattern' pos mods ruleVars (DkFun n [])    =
  prettyDk mods n
printPattern' pos mods ruleVars (DkFun n l)    =
  paren pos $
    prettyDk mods n <+> hsep (map (printPattern' Nested mods ruleVars) l)
printPattern' pos mods ruleVars (DkLambda n t) =
  paren pos $
    text "λ" <+> printIdent n <+> text ", " <+> printPattern' Top mods ruleVars t
printPattern' pos mods ruleVars (DkPattBuiltin t) =
  printTerm pos mods t
-- We do not guard variables, since non-linear rules are more efficient.
printPattern' pos mods ruleVars (DkGuarded (DkDB n _)) =
  printIdent n
printPattern' pos mods ruleVars (DkGuarded t) =
  braces (printTerm Top mods t)
printPattern' pos mods ruleVars DkJoker =
  char '_'

type DkCtx = [DkIdent]

-- takes indices of variables and returns their names under the given context
getVarNames :: [Int] -> DkCtx -> [DkIdent]
getVarNames used l =
  extractIndex 0 (sortUniq used) l
  where
    extractIndex _ []     _        = []
    extractIndex a (b:tl) (x:vars)
      | a==b      = x:(extractIndex (a+1) tl vars)
      | otherwise = extractIndex (a+1) (b:tl) vars

-- prints the [x, y, z] before the rules
printContext :: [Int] -> DkCtx -> Doc
printContext used l =
  let ll = extractIndex 0 (sortUniq used) l in
  brackets (hsep (punctuate (char ',') (map printIdent (reverse ll))))
  where
    extractIndex _ []     _        = []
    extractIndex a (b:tl) (x:vars)
      | a==b      = x:(extractIndex (a+1) tl vars)
      | otherwise = extractIndex (a+1) (b:tl) vars

data DkName =
    DkLocal DkIdent
  | DkQualified DkModName DkModName DkIdent
  deriving (Eq, Show)

instance PrettyDk DkName where
  prettyDk mods (DkLocal n)            = (printIdent n) -- not here...
  prettyDk mods (DkQualified qualif pseudo n) =
    let modName =
          if mods == qualif
          then empty
          else hcat (punctuate (text "__") (map (text . dropAll) qualif)) <> char '.'
    in
    let symName = printIdent $ (concat (map (++ "__") pseudo)) ++ n in
    modName <> symName

printIdent :: DkIdent -> Doc
printIdent n = printIdent' [] n

-- this version takes as l a list of vars which are printed
-- with a '$' before it
printIdent' :: [DkIdent] -> DkIdent -> Doc
--                lambdapi doesnt like points in bound variable names
printIdent' l n = let n' = map (\c -> if c == '.' then '\'' else c) n in
                    if elem n l
                    then text $ "$" ++ (encapsulate n')
                    else text $ (encapsulate n')



data IsStatic = Static | Defin | TypeConstr

--keywords = ["Type", "def", "thm", "injective", "defac", "defacu"]
keywords = ["TYPE", "def", "thm", "injective", "defac", "defacu", "symbol", "const"]

encapsulate :: String -> String
encapsulate l =
  if all (`elem` ['a'..'z']++['A'..'Z']++['0'..'9']++['_']) l && not (elem l keywords)
  then l
  else "{|"++l++"|}"

dropAll :: String -> String
dropAll []    = []
dropAll (h:t) =
  if elem h (['a'..'z']++['A'..'Z']++['0'..'9']++['_'])
  then h:(dropAll t)
  else dropAll t

data Position = Nested | Top

termOfPattern :: DkPattern -> DkTerm
termOfPattern (DkVar x i l)  = multiApp (DkDB x i) (map termOfPattern l)
termOfPattern (DkFun f l)    = multiApp (DkConst f) (map termOfPattern l)
termOfPattern (DkLambda x p) = DkLam x Nothing (termOfPattern p)
termOfPattern (DkPattBuiltin t)  = t
termOfPattern (DkGuarded t)  = t

multiApp :: DkTerm -> [DkTerm] -> DkTerm
multiApp t []     = t
multiApp t (x:tl) = multiApp (DkApp t x) tl

type DkDocs = (Doc, Doc, Doc)

toDkDocs ::  DkModName -> DkDefinition -> DkDocs
toDkDocs mods d =
  case staticity d of
    TypeConstr ->
      ( (printDecl mods d)<>hcat (printRules mods d decoding)
      , empty
      , hcat $ printRules mods d (not . decoding))
    _ ->
      ( empty
      , printDecl mods d
      , hcat $ printRules mods d (\x -> True))



