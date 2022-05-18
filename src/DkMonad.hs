{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
module DkMonad where

import Agda.Syntax.Common
import Control.Monad.State
import Agda.Compiler.Common
import Agda.Syntax.Abstract.Name
import Agda.TypeChecking.Monad
import Agda.TypeChecking.CheckInternal

data DkState = DkState
  {
    caseOfData :: QName -> Maybe QName
  }
             
type DkM a = StateT DkState TCM a


type DkMonad m =
  ( -- do not add MonadCheckInternal m
    MonadFail m
  , MonadAddContext m
  , HasConstInfo m
  , HasBuiltins m
  , MonadReduce m
  , MonadDebug m
  , MonadTCM m
  , MonadState DkState m
  )
  
