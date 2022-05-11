import Agda.Syntax.Internal
import Agda.Typechecking.Substitute
import Agda.Typechecking.Telescope

unTelView :: Telescope -> Type -> TCM Type
unTelView EmptyTel t = return t
unTelView (ExtendTel x y) t =
  do
    s <- unTelView (unAbs y) t
    let newt = Pi x (Abs{absName = absName y, unAbs = unEl s})
    return $ El {_getSort = __DUMMY_SORT__, unEl = newt}

  
mkCaseMethod :: QName -> TCM Term
mkCaseMethod conName =
  do
    consType <- defType <$> getConstInfo consqname
    tel <- theTel <$> telView consType
    let conHead =
          ConHead{conName = conName, conDataRecord = IsData, conInductive = Induction, conFields = []}
    let conInfo = ConOCon
    let coDom = Var (size tel) [Apply $ defaultArg $ Con conHead conInfo $
                                 map (\x -> Apply $ defaultArg $ Var x []) $ genList $ size tel]
    unTelView tel coDom
    where
      genList 0 = []
      genList n = n :: (genList (n - 1))
      
      


                    
    

{-
mkCase :: QName -> TCM (Maybe Term)
mkCase qname =
  do
    def <- getConstInfo qname
    let def = theDef def
    case def of
      Datatype{} -> do
        let numpars = dataPats def
        let cons = dataCons def

      _ -> return Nothing
    
    
  -}                
  
  
