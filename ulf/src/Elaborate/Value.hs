{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# Language CPP #-}
{-# Language PatternSynonyms #-}
{-# Language MonoLocalBinds #-}
{-# Language TemplateHaskell #-}
{-# Language ImplicitParams #-}

-- |
-- Copyright :  (c) Edward Kmett 2020, András Kovács 2020
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable

module Elaborate.Value where

import Common.Icit
import Common.Names
import Common.Unique
import Control.Lens hiding (Context)
import Data.Hashable
import Data.HashSet
import Data.IORef
import GHC.Exception
import GHC.Stack.Types
import Control.Monad.State
import Data.SBV.Trans.Control (Query, getValue, queryState, QueryT)
import Data.SBV.Trans ((.||), MonadSymbolic(..), (.&&), sNot, sBool, constrain, sFalse, sTrue, SBool)

panic :: HasCallStack => a
panic = throw (errorCallWithCallStackException "impossible" ?callStack)

data Meta = MetaRef {-# unpack #-} !Unique {-# unpack #-} !(IORef MetaEntry)

instance Eq Meta where
  MetaRef _ m == MetaRef _ n = m == n

instance Hashable Meta where
  hash (MetaRef h _) = hash h
  hashWithSalt d (MetaRef h _) = hashWithSalt d h

instance Show Meta where
  show (MetaRef u _) = "_"

newMeta :: MetaEntry -> IO Meta
newMeta m = MetaRef <$> newUnique <*> newIORef m
{-# inline newMeta #-}

writeMeta :: Meta -> MetaEntry -> IO ()
writeMeta (MetaRef _ r) s = writeIORef r s
{-# inline writeMeta #-}

readMeta :: Meta -> IO MetaEntry
readMeta (MetaRef _ r) = readIORef r
{-# inline readMeta #-}

modifyMeta :: Meta -> (MetaEntry -> MetaEntry) -> IO ()
modifyMeta (MetaRef _ r) f = modifyIORef' r f
{-# inline modifyMeta #-}

type Metas = HashSet Meta
type Blocking = Metas
type BlockedBy = Metas

data MetaEntry
  = Unsolved !Metas VTy
  | Solved !Val
#ifdef FCIF
  | Constancy !Context !VTy !VTy !BlockedBy
  | Dropped
#endif

data SlotType = Def | Bound
  deriving (Eq,Ord,Show,Read,Bounded,Enum)

data Vals
  = VNil
  | VSkip !Vals
  | VDef !Vals Val

data Types
  = TyNil
  | TySnoc !Types !SlotType VTy

data Context
  = Context
   { _vals :: Vals
   , _types :: Types
   , _names :: [Name]
   , _nameOrigin :: [NameOrigin]
   , _len :: Int
   }

emptyCtx :: Context
emptyCtx = Context VNil TyNil [] [] 0

data Q = E | L | A | R | U_ | S deriving (Show)

data Qty = Qty SBool SBool SBool

type Qtys = [Qty]

newtype M a = M (StateT Qtys Query a)
  deriving (Functor, Applicative, Monad, MonadIO)

knownQty :: Q -> Qty
knownQty = \case
  E -> Qty z o z
  L -> Qty o o o
  A -> Qty z z o
  U_ -> Qty z z z
  S -> Qty o z z
  R -> Qty o o z
  where 
    o = sTrue
    z = sFalse

qtyVar :: M Qty
qtyVar = M $ do
  x <- sBool "x"
  y <- sBool "y"
  z <- sBool "z"
  lift $ do
    constrain $ sNot (z .&& y .&& sNot x)
    constrain $ sNot (z .&& sNot y .&& x)
  pure (Qty x y z)

qtyVal :: Qty -> M Q
qtyVal (Qty x y z) = M $ ((,,) <$> getValue x <*> getValue y <*> getValue z) <&> \case
  (False, True, False)  -> E
  (True, True, True)    -> L
  (False, False, True)  -> A
  (False, False, False) -> U_
  (True, False, False)  -> S
  (True, True, False)   -> R
  _                     -> panic

mulQty :: Qty -> Qty -> Qty
mulQty (Qty a b c) (Qty x y z) = Qty (x .&& a) ((y .|| b) .&& (y .|| sNot a) .&& (b .|| sNot x)) (z .&& c)

addQty :: Qty -> Qty -> Qty
addQty (Qty a b c) (Qty x y z) = Qty (x .|| a) (y .&& b) ((z .&& sNot c .&& sNot a) .|| (c .&& sNot z .&& sNot x))


data NameOrigin = NOSource | NOInserted
  deriving (Eq,Ord,Show,Read,Bounded,Enum)

type Lvl = Int

data Head
  = HVar {-# unpack #-} !Lvl
  | HMeta {-# unpack #-} !Meta
  deriving Eq

data Spine
  = SNil
  | SApp !Icit !Spine Val
#ifdef FCIF
  | SAppTel Val !Spine Val
  | SCar !Spine
  | SCdr !Spine
#endif

type VTy = Val

data Val
  = VNe !Head !Spine
  | VPi !Name !Icit VTy EVTy
  | VLam !Name !Icit VTy EVal
  | VU
#ifdef FCIF
  | VTel
  | VRec Val
  | VTNil
  | VTCons !Name Val EVal
  | VTnil
  | VTcons Val Val
  | VPiTel !Name Val EVal
  | VLamTel !Name Val EVal
#endif

type EVal = Val -> IO Val
type EVTy = VTy -> IO VTy

pattern VVar :: Lvl -> Val
pattern VVar x = VNe (HVar x) SNil

pattern VMeta :: Meta -> Val
pattern VMeta m = VNe (HMeta m) SNil

makeLenses ''Context


