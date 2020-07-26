{-# language GADTs #-}
{-# language ExistentialQuantification #-}
{-# language ViewPatterns #-}
{-# language PatternSynonyms #-}
{-# language LambdaCase #-}
{-# language FlexibleContexts #-}

-- |
-- Copyright :  (c) Edward Kmett 2018-2020
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable

module Aligned.Freer
  ( Free(F)
  , FreeView(..)
  , view, unview
  , pattern V
  , free
  , (^>>=)
  ) where

import Aligned.Base
import Control.Applicative
import Control.Arrow (Kleisli(..))
import Control.Monad (ap, liftM)
import Control.Category
import Data.Functor 
import Prelude hiding ((.),id)

data Free f a where
  F :: FreeView f x -> Rev Cat (Kleisli (Free f)) x b -> Free f b

data FreeView f a
  = Pure a
  | forall x. Free (f x) (x -> Free f a)

instance Functor (FreeView f) where
  fmap f (Pure a) = Pure (f a)
  fmap f (Free fx k) = Free fx (fmap f . k)

instance Foldable f => Foldable (FreeView f) where
  foldMap f (Pure a) = f a
  foldMap f (Free fx k) = foldMap (foldMap f . k) fx

instance Traversable f => Traversable (FreeView f) where
  traverse f (Pure a) = Pure <$> f a
  traverse f (Free fx k)
    = traverse (traverse f . k) fx <&> \fx' -> Free fx' id

view :: Free f a -> FreeView f a
view (F h t) = case h of
  pa@(Pure a) -> case unsnoc t of
    Empty     -> pa
    tc :&: hc -> view $ runKleisli hc a ^>>= tc
  Free fx k -> Free fx ((^>>= t) . k)

unview :: FreeView f a -> Free f a
unview x = F x id

pattern V :: Functor f => FreeView f a -> Free f a
pattern V a <- (view -> a) where
  V b = unview b

free :: f (Free f a) -> Free f a
free fx = F (Free fx id) id

(^>>=) :: Free f x -> Rev Cat (Kleisli (Free f)) x b -> Free f b
F h t ^>>= r = F h (r . t)

instance Functor (Free f) where
  fmap = liftM

instance Foldable f => Foldable (Free f) where
  foldMap f = foldMap f . view

instance Traversable f => Traversable (Free f) where
  traverse f = fmap unview . traverse f . view

instance Applicative (Free f) where
  pure x = F (Pure x) id
  (<*>) = ap

instance Monad (Free f) where
  F m r >>= f = F m (cons (Kleisli f) r)
