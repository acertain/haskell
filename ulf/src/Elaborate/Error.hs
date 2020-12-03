{-# Language BlockArguments #-}
{-# Language ImportQualifiedPost #-}
{-# Language ExistentialQuantification #-}
{-# Language LambdaCase #-}
{-# Language DeriveAnyClass #-}

-- |
-- Copyright :  (c) Edward Kmett and András Kovács 2020
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable

module Elaborate.Error where

import Common.Icit
import Common.Names
import Control.Monad.Catch
import Elaborate.Term
import Elaborate.Value
import Text.Megaparsec (SourcePos, sourcePosPretty)
import Control.Exception (throw, throwIO)
import Control.Monad.IO.Class (MonadIO(liftIO))
import Text.Printf (printf)

data SpineError
  = SpineNonVar
  | SpineProjection
  | NonLinearSpine Lvl
  deriving (Show, Exception)

data StrengtheningError
  = ScopeError Lvl
  | OccursCheck
  deriving (Show, Exception)

data UnifyError
  = UnifyError [Name] TM TM 
  | SpineError [Name] TM TM SpineError
  | StrengtheningError [Name] TM TM StrengtheningError
  deriving Exception

quantityError :: ElabError
quantityError = QuantityError

instance Show UnifyError where
  show _ = "UnifyError..."

data ElabError
  = IcitMismatch Icit Icit
  | ExpectedFunction TM
  | NameNotInScope Name
  | UnifyErrorWhile TM TM UnifyError
  | QuantityError
  deriving (Exception)

instance Show ElabError where
  show _ = "ElabError..."

data Err = Err [Name] ElabError (Maybe SourcePos)
  deriving (Show)

instance Exception Err where
  displayException (Err ns1 e1 p) = maybe id (\p' -> (sourcePosPretty p' ++) . (": "++)) p $ case e1 of
    NameNotInScope x -> "Name not in scope: " ++ show x
    ExpectedFunction ty -> "Expected a function type, instead inferred:\n\n  " ++ showTm ns1 ty
    IcitMismatch i i' -> printf "Function icitness mismatch: expected %s, got %s." (show i) (show i')
    QuantityError -> "Quantity mismatch"
    UnifyErrorWhile lhs1 rhs1 e2 ->
      let err1 = case e2 of
            UnifyError ns lhs rhs -> printf
              ("Cannot unify\n\n" ++
               "  %s\n\n" ++
               "with\n\n" ++
               "  %s\n\n")
              (showTm ns lhs) (showTm ns rhs)
            StrengtheningError ns lhs rhs e -> case e of
              ScopeError x -> printf (
                "Variable %s is out of scope in equation\n\n" ++
                "  %s =? %s\n\n")
                (lvlName ns x) (showTm ns lhs) (showTm ns rhs)
              OccursCheck -> printf (
                "Meta occurs cyclically in its solution candidate in equation:\n\n" ++
                "  %s =? %s\n\n")
                (showTm ns lhs) (showTm ns rhs)
            SpineError ns lhs rhs e -> case e of
              SpineNonVar -> printf (
                "Non-bound-variable value in meta spine in equation:\n\n" ++
                "  %s =? %s\n\n")
                (showTm ns lhs) (showTm ns rhs)
              SpineProjection ->
                "Projection in meta spine\n\n"
              NonLinearSpine x -> printf
                ("Nonlinear variable %s in meta spine in equation\n\n" ++
                 "  %s =? %s\n\n")
                (lvlName ns x)
                (showTm ns lhs) (showTm ns rhs)
      in err1 ++ printf
           ("while trying to unify\n\n" ++
           "  %s\n\n" ++
           "with\n\n" ++
           "  %s") (showTm ns1 lhs1) (showTm ns1 rhs1)
           where lvlName _ _ = ""

-- instance Show Err where
--   show _ = "Err..."

{- 
  showsPrec d (Err ns ee p) = showParen (d > 10) $
    showString "Err " . showsPrec 11 ns . showChar ' ' 
                      . showsPrec 11 ee . showChar ' '
                      . showsPrec 11 p
-}

addSourcePos :: SourcePos -> IO a -> IO a
addSourcePos p act = act `catch` \case
  Err ns e Nothing -> liftIO $ throwIO $ Err ns e (Just p)
  e -> liftIO $ throwIO e

reportM :: [Name] -> ElabError -> IO a
reportM ns e = throwM $ Err ns e Nothing

report :: [Name] -> ElabError -> a
report ns e = throw $ Err ns e Nothing
