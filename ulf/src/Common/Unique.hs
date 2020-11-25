{-# LANGUAGE DeriveDataTypeable #-}
{-# Language MagicHash #-}
{-# Language UnboxedTuples #-}
{-# Language BlockArguments #-}

-- |
-- Copyright :  (c) Edward Kmett 2018-2020
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable

module Common.Unique 
  ( Unique
  , newUnique
  ) where

import Control.Monad.Primitive
import Data.Hashable
import GHC.Prim
import GHC.Types
import Data.Data
import Data.Primitive

data Unique = Unique {-# unpack #-} !Int {-# unpack #-} !(MutableByteArray RealWorld)
  deriving (Data)

instance Eq Unique where
  Unique _ p == Unique _ q = p == q

instance Hashable Unique where
  hash (Unique i _) = i
  hashWithSalt d (Unique i _) = hashWithSalt d i

instance Show Unique where
  show (Unique i _) = "Unique " ++ show i ++ " _"

newUnique :: IO Unique
newUnique = primitive \s -> case newByteArray# 0# s of
  (# s', ba #) -> (# s', Unique (I# (addr2Int# (unsafeCoerce# ba))) (MutableByteArray ba) #)
{-# inline newUnique #-}
