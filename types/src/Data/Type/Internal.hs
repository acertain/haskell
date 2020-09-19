{-# language CPP #-}
{-# language RankNTypes #-}
{-# language PolyKinds #-}
{-# language DataKinds #-}
{-# language PatternSynonyms #-}
{-# language DerivingStrategies #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language ViewPatterns #-}
{-# language RoleAnnotations #-}
{-# language StandaloneKindSignatures #-}
{-# language ConstraintKinds #-}
{-# language QuantifiedConstraints #-}
{-# language LambdaCase #-}
{-# language EmptyCase #-}
{-# language NPlusKPatterns #-}
{-# language TypeFamilies #-}
{-# language UndecidableInstances #-}
{-# language TypeOperators #-}
{-# language GADTs #-}
{-# language FlexibleInstances #-}
{-# language FlexibleContexts #-}
{-# language TypeApplications #-}
{-# language AllowAmbiguousTypes #-}
{-# language ScopedTypeVariables #-}
{-# language TemplateHaskell #-}
{-# language MagicHash #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- this makes the core well typed, but gets in the way of using ghci
-- that said, -fobject-code usually fixes that
--
-- #define USE_MAGICDICT 

module Data.Type.Internal where

import Control.Exception
import Data.Function
import Data.Kind
import Data.Proxy
import Data.Some
import Data.Type.Equality
import Data.Void
import GHC.Exts
import GHC.Types
import GHC.TypeNats as TN
import GHC.TypeLits as TL
import Numeric.Natural
import Text.Read hiding (Symbol)
import Type.Reflection
import Unsafe.Coerce

type Z :: Nat
type Z = 0

-- | successor of a natural number
type S :: Nat -> Nat
type S n = 1+n

--------------------------------------------------------------------------------
-- * Singletons
--------------------------------------------------------------------------------

type Sing :: forall k. k -> Type
newtype Sing (a :: k) = UnsafeSing { fromSing :: k }

instance (Typeable k, Show k) => Show (Sing (a :: k)) where
  showsPrec d (Sing k) = showParen (d > 10) $
    showString "Sing @" . showsPrec 11 (typeRep @k) . showChar ' ' . showsPrec 11 k

pattern Sing :: k -> Sing (a :: k)
pattern Sing x <- (UnsafeSing x)

{-# complete Sing #-}

instance Eq (Sing a) where
  _ == _ = True

instance Ord (Sing a) where
  compare _ _ = EQ

-- structural equality -- x = y => f x = f y 
-- class (Deciding SEq a, Eq a) => SEq a
class Eq a => SEq a
instance SEq Int
instance SEq Char
instance SEq Void
instance SEq ()
instance (SEq a, SEq b) => SEq (a, b)
instance (SEq a, SEq b) => SEq (Either a b)
instance SEq a => SEq [a]
instance SEq a => SEq (Maybe a)

-- assumes equality is structural.
instance SEq k => TestEquality (Sing :: k -> Type) where
  testEquality i j
    | fromSing i == fromSing j = Just (unsafeCoerce Refl)
    | otherwise = Nothing

type SingI :: forall k. k -> Constraint
class SingI (a :: k) where
  sing :: Sing a

type Reifies k (a::k) = SingI a

type Wrap :: forall k. k -> Type -> Type
#ifdef USE_MAGICDICT
data Wrap s r = Wrap (SingI s => Proxy# s -> r)
ify# :: (SingI a => Proxy# a -> r) -> Sing a -> Proxy# a -> r
ify# f x y = magicDict (Wrap f) x y
#else
newtype Wrap s r = Wrap (SingI s => Proxy# s -> r)
ify# :: (SingI a => Proxy# a -> r) -> Sing a -> Proxy# a -> r
ify# f x y = unsafeCoerce (Wrap f) x y
{-# inline ify# #-}
#endif

ify :: Sing a -> (SingI a => r) -> r
ify s r = ify# (\_ -> r) s proxy#

reify :: k -> (forall (a::k). SingI a => Proxy# a -> r) -> r
reify k f = ify# f (UnsafeSing k) proxy#

-- ambiguous types
reflect :: forall k a. Reifies k a => k
reflect = fromSing (sing @k @a)

--------------------------------------------------------------------------------
-- * Lowering Types
--------------------------------------------------------------------------------

type Type' = Some (TypeRep :: Type -> Type)

toType :: Type' -> Type
toType = unsafeCoerce 

fromType :: Type -> Type'
fromType = unsafeCoerce

instance Show Type where
  showsPrec d (Type t) = showsPrec d t

pattern Type :: TypeRep (a :: Type) -> Type
pattern Type t <- (fromType -> Some t) where
  Type t = toType (Some t)

instance Typeable a => SingI (a :: Type) where
  sing = UnsafeSing $ Type $ typeRep @a

type SType' :: Type -> Type
data SType' a where
  SType' :: TypeRep a -> SType' (a :: Type)

upSType :: Sing a -> SType' a
upSType (Sing (Type t)) = unsafeCoerce (SType' t)

pattern SType :: TypeRep a -> Sing (a :: Type)
pattern SType t <- (upSType -> SType' t) where
  SType t = UnsafeSing $ Type t

--------------------------------------------------------------------------------
-- * Lowering Nats
--
-- (let's make up a value rep for Nat til we get Nat=Natural in base)
--------------------------------------------------------------------------------

instance KnownNat a => SingI a where
  sing = UnsafeSing $ Nat $ TN.natVal (Proxy @a)

instance Show Nat where
  showsPrec d = showsPrec d . fromNat

instance Eq Nat where
  (==) = (==) `on` fromNat

instance SEq Nat

instance Ord Nat where
  compare = compare `on` fromNat

instance Read Nat where
  readPrec = Nat <$> readPrec

toNat :: Natural -> Nat
toNat = unsafeCoerce

fromNat :: Nat -> Natural
fromNat = unsafeCoerce

liftN2 :: (Natural -> Natural -> Natural) -> Nat -> Nat -> Nat
liftN2 f x y = Nat $ f (fromNat x) (fromNat y)

liftN :: (Natural -> Natural) -> Nat -> Nat
liftN f = Nat . f . fromNat

instance Num Nat where
  (+) = liftN2 (+)
  (-) = liftN2 (-)
  (*) = liftN2 (*)
  abs = liftN abs
  signum = liftN signum
  negate = liftN negate
  fromInteger = Nat . fromInteger

instance Enum Nat where
  succ = liftN succ
  pred = liftN pred
  toEnum = Nat . toEnum
  fromEnum = fromEnum . fromNat
  enumFrom = fmap Nat . enumFrom . fromNat
  enumFromTo (Nat n) (Nat m) = Nat <$> enumFromTo n m
  enumFromThen (Nat n) (Nat m) = Nat <$> enumFromThen n m
  enumFromThenTo (Nat n) (Nat m) (Nat o) = Nat <$> enumFromThenTo n m o

instance Real Nat where
  toRational = toRational . fromNat

instance Integral Nat where
  quot = liftN2 quot
  rem = liftN2 rem
  div = liftN2 rem
  mod = liftN2 rem
  quotRem (Nat n) (Nat m) = case quotRem n m of
    (q,r) -> (Nat q, Nat r)
  divMod (Nat n) (Nat m) = case divMod n m of
    (q,r) -> (Nat q, Nat r)
  toInteger = toInteger . fromNat

pattern Nat :: Natural -> Nat
pattern Nat n <- (fromNat -> n) where
  Nat n = toNat n

{-# complete Nat #-}

pattern Z :: Nat
pattern Z = Nat 0

safePred :: Natural -> Maybe Natural
safePred 0 = Nothing
safePred n = Just (n-1)

pattern S :: Nat -> Nat
pattern S n <- (safePred . fromNat -> Just (Nat -> n)) where
  S n = Nat (fromNat n + 1)

{-# complete Z, S #-}

type SNat' :: Nat -> Type
data SNat' n where
  SZ' :: SNat' Z
  SS' :: Sing i -> SNat' (S i)

upSNat :: Sing n -> SNat' n
upSNat (UnsafeSing 0) = unsafeCoerce SZ'
upSNat (UnsafeSing n) = unsafeCoerce $ SS' (UnsafeSing (n-1))

-- |
-- This apparently trips a GHC bug, so you may have to use 
-- -Wno-overlapping-patterns. Note the loss of type inference
-- from the "inaccessible" branch and the fact that it immediately
-- then gets executed
--
-- @
-- ghci> case SS SZ of { SS SZ -> print "hi" } :: IO ()
-- <interactive>:77:17: warning: [-Woverlapping-patterns]
--    Pattern match has inaccessible right hand side
--    In a case alternative: SS SZ -> ...
-- "hi"
-- @
pattern SZ :: () => (n ~ Z) => Sing n
pattern SZ <- (upSNat -> SZ') where
  SZ = UnsafeSing 0

pattern SS :: () => (m ~ S n) => Sing n -> Sing m
pattern SS n <- (upSNat -> SS' n) where
  SS n = UnsafeSing $ succ $ fromSing n

{-# complete SS, SZ #-}

--------------------------------------------------------------------------------
-- * Lifting Ints
--------------------------------------------------------------------------------

data family FromNat :: Nat -> k

type MkInt :: Nat -> Int
type MkInt = FromNat

instance KnownNat n => SingI (MkInt n) where
  sing = SMkInt $ UnsafeSing $ fromIntegral $ TL.natVal $ Proxy @n

type SInt' :: Int -> Type
data SInt' n where
  SIntZ' :: SInt' (MkInt Z)
  SIntS' :: Sing (MkInt i) -> SInt' (MkInt (S i))

upSInt :: Sing n -> SInt' n
upSInt (UnsafeSing 0) = unsafeCoerce SIntZ'
upSInt (UnsafeSing n) = unsafeCoerce $ SIntS' (UnsafeSing (n-1))

pattern SIntZ :: () => (n ~ MkInt Z) => Sing n
pattern SIntZ <- (upSInt -> SIntZ') where
  SIntZ = UnsafeSing 0

pattern SIntS :: () => (i ~ MkInt i', j ~ MkInt (S i')) => Sing i -> Sing j
pattern SIntS n <- (upSInt -> SIntS' n) where
  SIntS n = UnsafeSing $ succ $ fromSing n

{-# complete SIntS, SIntZ #-}

pattern SMkInt :: Sing n -> Sing (MkInt n)
pattern SMkInt n <- Sing (UnsafeSing . fromIntegral -> n) where
  SMkInt n = if fromSing n > fromIntegral (maxBound @Word) 
             then throw Overflow
             else UnsafeSing $ fromIntegral (fromSing n)

{-# complete SMkInt #-}

--------------------------------------------------------------------------------
-- * Lifting Char
--------------------------------------------------------------------------------

data family FromSymbol :: Symbol -> k

type MkChar :: Symbol -> Char
type MkChar = FromSymbol

instance KnownSymbol s => SingI (MkChar s) where
  sing = case symbolVal $ Proxy @s of
    [c] -> UnsafeSing c
    _ -> error "SChar.sing: bad argument"

--------------------------------------------------------------------------------
-- * Lowering Symbol
--------------------------------------------------------------------------------

toSymbol :: String -> Symbol
toSymbol = unsafeCoerce

fromSymbol :: Symbol -> String
fromSymbol = unsafeCoerce

pattern Symbol :: String -> Symbol
pattern Symbol s <- (fromSymbol -> s) where
  Symbol s = toSymbol s

{-# complete Symbol #-}

instance Eq Symbol where
  (==) = (==) `on` fromSymbol

instance Ord Symbol where
  compare = compare `on` fromSymbol

instance Show Symbol where
  showsPrec d = showsPrec d . fromSymbol

instance Read Symbol where
  readPrec = Symbol <$> readPrec

instance IsList Symbol where
  type Item Symbol = Char
  fromList = Symbol . fromList
  fromListN n xs = Symbol (fromListN n xs)
  toList = toList . fromSymbol

instance IsString Symbol where
  fromString = toSymbol

instance KnownSymbol s => SingI s where
  sing = UnsafeSing $ Symbol $ symbolVal $ Proxy @s

--------------------------------------------------------------------------------
-- * Lifting Lists
--------------------------------------------------------------------------------

type SList' :: forall a. [a] -> Type
type role SList' nominal
data SList' a where
  SNil' :: SList' '[]
  SCons' :: Sing a -> Sing as -> SList' (a ': as)

upSList :: Sing a -> SList' a
upSList (Sing [])     = unsafeCoerce SNil'
upSList (Sing (a:as)) = unsafeCoerce $ SCons' (UnsafeSing a) (UnsafeSing as)

pattern SNil :: () => (xs ~ '[]) => Sing xs
pattern SNil <- (upSList -> SNil') where
  SNil = UnsafeSing []

pattern SCons :: () => (aas ~ (a ': as)) => Sing a -> Sing as -> Sing aas
pattern SCons a as <- (upSList -> SCons' a as) where
  SCons (Sing a) (Sing as) = UnsafeSing (a:as)

instance SingI '[] where
  sing = UnsafeSing []

instance (SingI a, SingI as) => SingI (a ': as) where
  sing = UnsafeSing (reflect @_ @a : reflect @_ @as)

-- {-# complete SNil, SCons #-}

--------------------------------------------------------------------------------
-- * Lifting Maybe
--------------------------------------------------------------------------------

type SMaybe' :: forall a. Maybe a -> Type
type role SMaybe' nominal
data SMaybe' a where
  SNothing' :: SMaybe' 'Nothing
  SJust'    :: Sing a -> SMaybe' ('Just a)

upSMaybe :: Sing a -> SMaybe' a
upSMaybe (Sing Nothing)  = unsafeCoerce SNothing'
upSMaybe (Sing (Just a)) = unsafeCoerce $ SJust' (UnsafeSing a)

pattern SNothing :: () => (m ~ 'Nothing) => Sing m
pattern SNothing <- (upSMaybe -> SNothing') where
  SNothing = UnsafeSing Nothing

pattern SJust :: () => (ma ~ 'Just a) => Sing a -> Sing ma
pattern SJust a <- (upSMaybe -> SJust' a) where
  SJust (Sing a) = UnsafeSing (Just a)

{-# complete SNothing, SJust #-}

--------------------------------------------------------------------------------
-- * Lifting Products
--------------------------------------------------------------------------------

type SPair' :: forall a b. (a,b) -> Type
type role SPair' nominal
data SPair' t where
  SPair' :: Sing a -> Sing b -> SPair' '(a, b)

upSPair :: Sing a -> SPair' a
upSPair (Sing (a,b)) = unsafeCoerce $ SPair' (UnsafeSing a) (UnsafeSing b)

instance (SingI a, SingI b) => SingI '(a, b) where
  sing = UnsafeSing (reflect @_ @a,reflect @_ @b)

pattern SPair :: Sing a -> Sing b -> Sing '(a, b)
pattern SPair a b <- Sing (UnsafeSing -> a, UnsafeSing -> b) where
  SPair a b = UnsafeSing (fromSing a, fromSing b)

{-# complete SPair #-}

--------------------------------------------------------------------------------
-- * Lifting Booleans
--------------------------------------------------------------------------------

instance SingI 'True where sing = STrue
instance SingI 'False where sing = SFalse

type SBool' :: Bool -> Type
type role SBool' nominal
data SBool' b where
  STrue'  :: SBool' 'True
  SFalse' :: SBool' 'False

upSBool :: Sing a -> SBool' a 
upSBool (Sing True) = unsafeCoerce STrue'
upSBool (Sing False) = unsafeCoerce SFalse'

pattern STrue :: () => (b ~ 'True) => Sing b
pattern STrue <- (upSBool -> STrue') where
  STrue = UnsafeSing True

pattern SFalse :: () => (b ~ 'False) => Sing b
pattern SFalse <- (upSBool -> SFalse') where
  SFalse = UnsafeSing False

{-# complete STrue, SFalse #-}

--------------------------------------------------------------------------------
-- * Lifting Ordering
--------------------------------------------------------------------------------

instance SingI 'LT where sing = SLT
instance SingI 'EQ where sing = SEQ
instance SingI 'GT where sing = SGT

type SOrdering' :: Ordering -> Type
type role SOrdering' nominal
data SOrdering' t where
  SLT' :: SOrdering' 'LT
  SEQ' :: SOrdering' 'EQ
  SGT' :: SOrdering' 'GT

upSOrdering :: Sing a -> SOrdering' a 
upSOrdering (Sing LT) = unsafeCoerce SLT'
upSOrdering (Sing EQ) = unsafeCoerce SEQ'
upSOrdering (Sing GT) = unsafeCoerce SGT'

pattern SLT :: () => (b ~ 'LT) => Sing b
pattern SLT <- (upSOrdering -> SLT') where
  SLT = UnsafeSing LT

pattern SEQ :: () => (b ~ 'EQ) => Sing b
pattern SEQ <- (upSOrdering -> SEQ') where
  SEQ = UnsafeSing EQ

pattern SGT :: () => (b ~ 'GT) => Sing b
pattern SGT <- (upSOrdering -> SGT') where
  SGT = UnsafeSing GT

{-# complete SLT, SEQ, SGT #-}

--------------------------------------------------------------------------------
-- * Lifting Either
--------------------------------------------------------------------------------

{-
type SEither' :: forall a b. Either a b -> Type
type role SEither' nominal
data SEither' t where
  SLeft'  :: Sing a -> SEither' ('Left a)
  SRight' :: Sing b -> SEither' ('Right b)

upSEither :: Sing a -> SEither' a
upSEither (Sing (Left a))  = unsafeCoerce (SLeft' (UnsafeSing a))
upSEither (Sing (Right b)) = unsafeCoerce (SRight' (UnsafeSing b))

instance SingI a => SingI ('Left a) where sing = SLeft sing
instance SingI b => SingI ('Right b) where sing = SRight sing

pattern SLeft :: () => (ma ~ 'Left a) => Sing a -> Sing ma
pattern SLeft a <- (upSEither -> SLeft' a) where
  SLeft (Sing a) = UnsafeSing (Left a)

pattern SRight :: () => (ma ~ 'Right a) => Sing a -> Sing ma
pattern SRight a <- (upSEither -> SRight' a) where
  SRight (Sing a) = UnsafeSing (Right a)

{-# complete SLeft, SRight #-}
-}