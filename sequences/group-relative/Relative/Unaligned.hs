{-# language DeriveTraversable #-}
{-# language TypeFamilies #-}
{-# language PatternSynonyms #-}
{-# language ViewPatterns #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language RoleAnnotations #-}

module Relative.Unaligned
  ( View(..) -- re-export
  , Rev(..) -- re-export
  , Cons(..)
  , Uncons(..)
  , Snoc(..)
  , Unsnoc(..)
  , Nil(..)
  , Singleton(..)
  , List(..)
  , Q(..)
  , Cat(..)
  , pattern Nil
  , pattern Cons
  , pattern Snoc
  , fromListL
  , fromListQ
  , foldMapQ
  , foldMapCat
  ) where

import Delta
import Data.Default
import Data.Function (on)
import Data.Group
import GHC.Exts as Exts
import Relative
import Unaligned.Internal (View(..), Rev(..))
import Text.Read

--------------------------------------------------------------------------------
-- * Interface
--------------------------------------------------------------------------------

-- TODO: use Control.Lens.Cons?
class Cons t where
  cons :: Relative a => a -> t a -> t a

class Nil t where
  nil :: Relative a => t a

class Uncons t where
  uncons :: Relative a => t a -> View a (t a)

class Unsnoc t where
  unsnoc :: Relative a => t a -> View (t a) a

class Snoc t where
  snoc :: Relative a => t a -> a -> t a

class Singleton t where
  singleton :: Relative a => a -> t a

pattern Nil :: (Nil t, Uncons t, Relative a) => t a
pattern Nil <- (uncons -> Empty) where
  Nil = nil

pattern Cons :: (Cons t, Uncons t, Relative a) => a -> t a -> t a
pattern Cons a as <- (uncons -> a :&: as) where
  Cons a as = cons a as

pattern Snoc :: (Snoc t, Unsnoc t, Relative a) => t a -> a -> t a
pattern Snoc as a <- (unsnoc -> as :&: a) where
  Snoc as a = snoc as a

--------------------------------------------------------------------------------
-- Reversing containers
--------------------------------------------------------------------------------

instance Nil t => Nil (Rev t) where
  nil = Rev nil

instance Cons t => Snoc (Rev t) where
  snoc (Rev t) f = Rev (cons f t)

instance Uncons t => Unsnoc (Rev t) where
  unsnoc (Rev t) = case uncons t of
    l :&: r -> Rev r :&: l
    Empty -> Empty

instance Unsnoc t => Uncons (Rev t) where
  uncons (Rev t) = case unsnoc t of
    l :&: r -> r :&: Rev l
    Empty -> Empty

instance Snoc t => Cons (Rev t) where
  cons a (Rev b) = Rev (snoc b a)

instance Singleton t => Singleton (Rev t) where
  singleton = Rev . singleton

--------------------------------------------------------------------------------
-- * Lists
--------------------------------------------------------------------------------

data List a = List {-# UNPACK #-} !Delta [a]

instance Nil List where
  nil = List mempty []

instance Cons List where
  cons a (List d as) = List d (rel (invert d) a:as)

instance Uncons List where
  uncons (List d as) = case as of
    [] -> Empty
    l:r -> rel d l :&: List d r

instance Singleton List where
  singleton a = List mempty [a]

instance (Show a, Relative a) => Show (List a) where
  showsPrec d = showsPrec d . Exts.toList

instance Read a => Read (List a) where
  readPrec = List mempty <$> readListPrec

instance (Eq a, Relative a) => Eq (List a) where
  (==) = (==) `on` Exts.toList

instance (Ord a, Relative a) => Ord (List a) where
  compare = compare `on` Exts.toList

instance Relative (List a) where
  rel d (List d' as) = List (d <> d') as

instance Relative a => IsList (List a) where
  type Item (List a) = a
  fromList = List mempty
  fromListN _ = List mempty
  toList = foldMapL pure

fromListL :: [a] -> List a
fromListL = List mempty
{-# inline fromListL #-}

foldMapL :: (Relative a, Monoid m) => (a -> m) -> List a -> m
foldMapL f (List d as) = foldMap (f . rel d) as
{-# inline foldMapL #-}

--------------------------------------------------------------------------------
-- * Queues
--------------------------------------------------------------------------------

data Q a = Q {-# unpack #-} !Delta [a] (Rev [] a) [a]

type role Q nominal

instance Relative (Q a) where
--  rel (Delta One 0) xs = xs
  rel d (Q d' as bs cs) = Q (d <> d') as bs cs

{-# complete Nil, Cons :: Q #-}

instance Default (Q a) where
  def = Q mempty [] (Rev []) []

instance (Show a, Relative a) => Show (Q a) where
  showsPrec d = showsPrec d . Exts.toList

instance Read a => Read (Q a) where
  readPrec = fromListQ <$> readListPrec

instance (Eq a, Relative a) => Eq (Q a) where
  (==) = (==) `on` Exts.toList

instance (Ord a, Relative a) => Ord (Q a) where
  compare = compare `on` Exts.toList

instance Relative a => IsList (Q a) where
  type Item (Q a) = a
  fromList = foldr cons nil
  fromListN _ = foldr cons nil
  toList = foldMapQ pure

fromListQ :: [a] -> Q a
fromListQ xs = Q mempty xs (Rev []) xs
{-# inline fromListQ #-}

foldMapQ :: (Relative a, Monoid m) => (a -> m) -> Q a -> m
foldMapQ f (Q d as bs _) = foldMap (f . rel d) as <> foldMap (f . rel d) bs

instance Nil Q where
  nil = Q mempty [] (Rev []) []

instance Cons Q where
  cons a (Q d f r s) = let a' = rel (invert d) a in Q d (a':f) r (a':s)

instance Uncons Q where
  uncons (Q _ [] (Rev []) _) = Empty
  uncons (Q d (x:f) r s) = rel d x :&: exec d f r s
  uncons _ = error "Q.uncons: invariants violated"

instance Singleton Q where
  singleton a = Q mempty [a] (Rev []) []

instance Snoc Q where
  snoc (Q d f (Rev r) s) a = exec d f (Rev (rel (invert d) a : r)) s

exec :: Delta -> [a] -> Rev [] a -> [a] -> Q a
exec d xs ys (_:t) = Q d xs ys t
exec d xs ys []    = Q d xs' (Rev []) xs' where xs' = rotate xs ys []

rotate :: [a] -> Rev [] a -> [a] -> [a]
rotate [] (Rev [y]) a = y:a
rotate (x:xs) (Rev (y:ys)) a = x:rotate xs (Rev ys) (y:a)
rotate _ _ _ = error "Q.rotate: invariant broken"

--------------------------------------------------------------------------------
-- * Catenable lists
--------------------------------------------------------------------------------

data Cat a = E | C a !(Q (Cat a))
{-# complete Nil, C #-}
{-# complete E, Cons #-}
{-# complete Nil, Cons :: Cat #-}

type role Cat nominal

instance Relative a => Relative (Cat a) where
  rel _ E = E
  -- rel (Delta One 0) as = as
  rel d (C a as) = C (rel d a) (rel d as)

instance Relative a => RelativeSemigroup (Cat a)
instance Relative a => RelativeMonoid (Cat a)

instance (Show a, Relative a) => Show (Cat a) where
  showsPrec d = showsPrec d . Exts.toList

instance (Read a, Relative a) => Read (Cat a) where
  readPrec = Exts.fromList <$> readListPrec

instance (Eq a, Relative a) => Eq (Cat a) where
  (==) = (==) `on` Exts.toList

instance (Ord a, Relative a) => Ord (Cat a) where
  compare = compare `on` Exts.toList

foldMapCat :: (Relative a, Monoid m) => (a -> m) -> Cat a -> m
foldMapCat _ E = mempty
foldMapCat f (C a as) = f a <> foldMapQ (foldMapCat f) as

instance Default (Cat a) where
  def = E

instance Relative a => Semigroup (Cat a) where
  E <> xs = xs
  xs <> E = xs
  C x xs <> ys = link x xs ys

instance Relative a => Monoid (Cat a) where
  mempty = E

instance Relative a => IsList (Cat a) where
  type Item (Cat a) = a
  fromList = foldr cons nil
  fromListN _ = foldr cons nil
  toList = foldMapCat pure

link :: Relative a => a -> Q (Cat a) -> Cat a -> Cat a
link x xs ys = C x (snoc xs ys)

-- O(1+e) where e is the number of empty catenable lists in the Q
linkAll :: Relative a => Q (Cat a) -> Cat a
linkAll q = case uncons q of
  c@(C a t) :&: q' -> case uncons q' of
    Empty -> c
    _ -> link a t (linkAll q')
  E :&: q' -> linkAll q' -- recursive case in case of empty queues, unused
  Empty -> E

instance Nil Cat where
  nil = E

instance Uncons Cat where
  uncons E = Empty
  uncons (C a q) = a :&: linkAll q

instance Cons Cat where
  cons a E  = C a nil
  cons a ys = link a nil ys

instance Singleton Cat where
  singleton a = C a nil
  {-# inline singleton #-}

instance Snoc Cat where
  snoc xs a = xs <> singleton a
