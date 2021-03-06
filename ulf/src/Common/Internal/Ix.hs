{-# Language RoleAnnotations #-}
{-# Language DerivingStrategies #-}
{-# Language GeneralizedNewtypeDeriving #-}
{-# Language StandaloneKindSignatures #-}
{-# Language DataKinds #-}

module Common.Internal.Ix 
  ( Ix
  , Lvl(..)
  , topLvl
  , lvlIx
  , ixLvl
  ) where

import Common.Internal.Nat
import Data.Coerce
import Data.Kind (Type)
import GHC.TypeNats

type Ix = Fin

type Lvl :: Nat -> Type
type role Lvl nominal
newtype Lvl i = UnsafeLvl Int 
  deriving newtype (Show,ToInt)

topLvl :: N i -> Lvl (S n)
topLvl = coerce

lvlIx :: N i -> Lvl i -> Ix i
lvlIx n l = UnsafeFin (int n - int l - 1)

ixLvl :: N i -> Ix i -> Lvl i
ixLvl n i = UnsafeLvl (int n - int i - 1)

