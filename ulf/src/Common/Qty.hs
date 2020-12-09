{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# Language ImplicitParams #-}

module Common.Qty (
  GivenSolver, runSolver,

  Q(..), Qty, knownQty, zeroQty, oneQty, mulQty, addQty,

  qtyVar, qtyVal, qtyEq, qtyLe, qtysLe,

  Qtys(..), mulQtys, wknQtys, headQtys, tailQtys, qtysEq, zeroQtys, wknQtysN, headQtysS,

  SQtys, newSQtys, headSQtys, tailSQtys, sQtysEq, mulSQtys, sQtysEqNil
) where

import Solver.Sat.CaDiCaL
import Data.Data
import Control.Lens
import Data.IORef
import Data.Foldable (traverse_)
import qualified Data.HashMap.Strict as HM
import System.Mem.StableName
import GHC.Types (Any)
import Unsafe.Coerce
import Data.Hashable
import GHC.Generics
import GHC.Stack
import Control.Applicative
import {-# SOURCE #-} Elaborate.Error

type GivenSolver = (GivenSAT, ?cachedStableMap :: IORef (HM.HashMap (StableName ()) Any))

runSolver :: (GivenSolver => IO a) -> IO a
runSolver x = withSolverOpts [("lucky",0),("profile",3),("inprocessing",0),("decompose",0),("elim",0)] $ do
  r <- newIORef mempty
  let ?cachedStableMap = r
  x

data Q = E | L | A | R | U | S deriving (Show, Data, Eq)

data Qty = Qty !Bit !Bit !Bit
  deriving (Data, Show, Eq, Hashable, Generic)

data Qtys = SnocQty !Qtys !Qty
          -- used for fcif telescopes/record types
          | SnocSQtys !Qtys !SQtys
          -- snoc zero or a vector of zeros
          -- invariant: n > 0
          | WknQtysN {-# UNPACK #-} !Int !Qtys
          | EmptyQtys
  deriving (Show, Data)

type QtysV = IORef QtysVEntry

data QtysVEntry =
    SolvedQV !QtysVVal
  | UnsolvedQV ![QtysVVal -> IO ()]

data QtysVVal = ConsQV !Qty !SQtys | NilQV

type SQtys = Cached QtysV

newSQtys :: IO SQtys
newSQtys = Constant <$> newIORef (UnsolvedQV [])

data Cached a = Cached (GivenSolver => IO a) | Constant a
  deriving (Typeable)

instance Show (Cached a) where show _ = "<cached>"

instance Typeable a => Data (Cached a)

runCached :: GivenSolver => Cached a -> IO a
runCached (Constant x) = pure x
runCached (Cached x) = do
  sn <- makeStableName' x
  m <- readIORef ?cachedStableMap
  case HM.lookup sn m of
    Just r -> pure $ unsafeCoerce r
    Nothing -> do
      r <- x
      modifyIORef' ?cachedStableMap (HM.insert sn (unsafeCoerce r :: Any))
      pure r
  where
    makeStableName' :: a -> IO (StableName ())
    makeStableName' x = unsafeCoerce <$> (makeStableName $! x)

groundQtysV :: GivenSolver => QtysV -> QtysVVal -> IO ()
groundQtysV r s = readIORef r >>= \case
  SolvedQV _ -> pure ()
  UnsolvedQV _ -> writeQtysV r =<< (case s of
    NilQV -> pure NilQV
    ConsQV _ _ -> ConsQV <$> qtyVar <*> newSQtys)

onQtysV :: QtysV -> (QtysVVal -> IO ()) -> IO ()
onQtysV r c = readIORef r >>= \case
  SolvedQV q -> c q
  UnsolvedQV l -> writeIORef r $ UnsolvedQV (c:l)

writeQtysV :: GivenSolver => QtysV -> QtysVVal -> IO ()
writeQtysV r x = readIORef r >>= \case
  SolvedQV y -> case (x,y) of
    (NilQV, NilQV) -> pure ()
    (ConsQV q qs, ConsQV r rs) -> qtyEq q r >> sQtysEq qs rs
    (_, _) -> error "writeQtysV: mismatched QtysVVal shapes"
  UnsolvedQV cbs -> writeIORef r (SolvedQV x) >> traverse_ ($ x) cbs


addSQtys :: SQtys -> SQtys -> SQtys
addSQtys a b = Cached $ do
  x <- runCached a
  y <- runCached b

  r <- newIORef $ UnsolvedQV []
  onQtysV x $ \xv -> onQtysV y $ \yv -> writeQtysV r undefined -- (xv <> yv)

  onQtysV x (groundQtysV y)
  onQtysV y (groundQtysV x)
  onQtysV r (groundQtysV x)

  pure r


mulSQtys :: Qty -> SQtys -> SQtys
mulSQtys m x = Cached $ do
  a <- runCached x
  readIORef a >>= \case
    -- TODO: avoid making a var when already solved
    _ -> do
      r <- newIORef $ UnsolvedQV []

      onQtysV r (groundQtysV a)
      onQtysV a \case
        NilQV -> writeQtysV r NilQV
        ConsQV q qs -> writeQtysV r (ConsQV (mulQty m q) (mulSQtys m qs))
      
      pure r

sQtysEqNil :: GivenSolver => SQtys -> IO ()
sQtysEqNil x = do
  a <- runCached x
  writeQtysV a NilQV

instance Semigroup Qtys where
  SnocQty as a <> SnocQty bs b = SnocQty (as <> bs) (addQty a b)
  SnocSQtys as a <> SnocSQtys bs b = SnocSQtys (as <> bs) (addSQtys a b)
  WknQtysN n as <> SnocSQtys bs b = SnocSQtys (wknQtysN (n-1) as <> bs) b
  WknQtysN n as <> SnocQty bs b = SnocQty (wknQtysN (n-1) as <> bs) b
  SnocSQtys bs b <> WknQtysN n as = SnocSQtys (wknQtysN (n-1) as <> bs) b
  SnocQty bs b <> WknQtysN n as = SnocQty (wknQtysN (n-1) as <> bs) b
  WknQtysN n as <> WknQtysN m bs = wknQtysN o (wknQtysN (n-o) as <> wknQtysN (m-o) bs)
    where o = min n m
  EmptyQtys <> EmptyQtys = EmptyQtys
  x <> y = error $ "(<>): mismatched qtys shape: " ++ show x ++ " <> " ++ show y

zeroQtys :: Int -> Qtys
zeroQtys n = wknQtysN n EmptyQtys

knownQty :: Q -> Qty
knownQty = \case
  E -> Qty z o z
  L -> Qty o o o
  A -> Qty z z o
  U -> Qty z z z
  S -> Qty o z z
  R -> Qty o o z
  where 
    o = trueb
    z = falseb

zeroQty :: Qty
zeroQty = knownQty E

oneQty :: Qty
oneQty = knownQty L

qtyVar :: GivenSolver => IO Qty
qtyVar = do
  x <- exists
  y <- exists
  z <- exists
  assert $ notb (z .&& y .&& notb x)
  assert $ notb (z .&& notb y .&& x)
  pure (Qty x y z)

qtyVal :: GivenSolver => Qty -> IO (Maybe Q)
qtyVal (Qty x y z) = (liftA3 (,,) <$> evalBit x <*> evalBit y <*> evalBit z) <&> fmap \case
  (False, True, False)  -> E
  (True, True, True)    -> L
  (False, False, True)  -> A
  (False, False, False) -> U
  (True, False, False)  -> S
  (True, True, False)   -> R
  _                     -> error "impossible"

mulQty :: Qty -> Qty -> Qty
mulQty (Qty a b c) (Qty x y z) = Qty (x .&& a) ((y .|| b) .&& (y .|| notb a) .&& (b .|| notb x)) (z .&& c)

addQty :: Qty -> Qty -> Qty
addQty (Qty a b c) (Qty x y z) = Qty (x .|| a) (y .&& b) ((z .&& notb c .&& notb a) .|| (c .&& notb z .&& notb x))

mulQtys :: Qty -> Qtys -> Qtys
mulQtys q = go where
  go EmptyQtys = EmptyQtys
  go (SnocQty as a) = SnocQty (go as) (mulQty q a)
  go (SnocSQtys as a) = SnocSQtys (go as) (mulSQtys q a)
  go (WknQtysN n qs) = wknQtysN n $ go qs

-- splitQty :: GivenSolver => Qty -> IO (Qty,Qty)
-- splitQty q = do
--   x <- qtyVar
--   y <- qtyVar
--   qtyEq (addQty x y) q
--   pure (x,y)

-- splitQtys :: GivenSolver => Qtys -> IO (Qtys,Qtys)
-- splitQtys = \case
--   SnocQty qs q -> do
--     x <- qtyVar
--     y <- qtyVar
--     qtyEq (addQty x y) q
--     (w,v) <- splitQtys qs
--     pure (SnocQty w x, SnocQty v y)
--   SnocSQtys qs q -> do

qtyEq :: (GivenSolver, HasCallStack) => Qty -> Qty -> IO ()
qtyEq (Qty a b c) (Qty x y z) = do
  let e = (a .== x) .&& (b .== y) .&& (c .== z)
  assert e
  solve >>= \case
    Just True -> pure ()
    Just False -> reportM [] quantityError
    Nothing -> error "solver error"
  -- solveWith [e] >>= \case
  --   Just True -> do
  --     assert e
  --     Just True <- solve
  --     pure ()
  --   Just False -> do
  --     putStrLn "qtyEq: failed equation, weakening"
  --     pure ()
  --   Nothing -> error "solver error"


-- a <= b = b can be weakened into a
-- / if i have b i can use it as an a
qtyLe :: (GivenSolver, HasCallStack) => Qty -> Qty -> IO ()
-- or disable weakening here
-- qtyLe = qtyEq
qtyLe (Qty x y z) (Qty a b c) = do
  assert e
  solve >>= \case
    Just True -> pure ()
    Just False -> reportM [] quantityError
    Nothing -> error "solver error"  
  where e =     (x .|| notb a)
            .&& (y .|| z .|| notb c)
            .&& (y .|| z .|| notb b)
            .&& (x .|| y .|| notb b)
            .&& (notb x .|| notb y .|| z .|| notb c)
            .&& (notb x .|| a .|| notb b .|| c)



qtysEq :: GivenSolver => Qtys -> Qtys -> IO ()
qtysEq EmptyQtys EmptyQtys = pure ()
qtysEq (SnocQty as a) (SnocQty bs b) = qtyEq a b >> qtysEq as bs
qtysEq (SnocSQtys as a) (SnocSQtys bs b) = sQtysEq a b >> qtysEq as bs
qtysEq (WknQtysN n x) (WknQtysN m y) = qtysEq (wknQtysN (n-o) x) (wknQtysN (m-o) y)
  where o = min n m
qtysEq (SnocQty qs q) (WknQtysN n qs') = qtyEq q zeroQty >> qtysEq qs (wknQtysN (n-1) qs')
qtysEq (SnocSQtys qs q) (WknQtysN n qs') = sQtysEqZero q >> qtysEq qs (wknQtysN (n-1) qs')
qtysEq x y = error $ "qtysEq: mismatched shape: " ++ show x ++ " == " ++ show y

qtysLe :: GivenSolver => Qtys -> Qtys -> IO ()
qtysLe EmptyQtys EmptyQtys = pure ()
qtysLe (SnocQty as a) (SnocQty bs b) = qtyLe a b >> qtysLe as bs
qtysLe (SnocSQtys as a) (SnocSQtys bs b) = sQtysLe a b >> qtysLe as bs
qtysLe (WknQtysN n x) (WknQtysN m y) = qtysLe (wknQtysN (n-o) x) (wknQtysN (m-o) y)
  where o = min n m
qtysLe (SnocQty qs q) (WknQtysN n qs') = qtyLe q zeroQty >> qtysLe qs (wknQtysN (n-1) qs')
qtysLe (WknQtysN n qs') (SnocQty qs q) = qtyLe zeroQty q >> qtysLe (wknQtysN (n-1) qs') qs
qtysLe (WknQtysN n qs') (SnocSQtys qs q) = sQtysZeroLe q >> qtysLe (wknQtysN (n-1) qs') qs
qtysLe x y = error $ "qtysLe: mismatched shape: " ++ show x ++ " == " ++ show y

sQtysMapConstrain ::  GivenSolver => (Qty -> IO ()) -> SQtys -> IO ()
sQtysMapConstrain f x = do
  r <- runCached x
  onQtysV r \case
    NilQV -> pure ()
    ConsQV q qs -> f q >> sQtysMapConstrain f qs

sQtysZeroLe :: GivenSolver => SQtys -> IO ()
sQtysZeroLe = sQtysMapConstrain (\q -> qtyLe zeroQty q)

sQtysEqZero :: GivenSolver => SQtys -> IO ()
sQtysEqZero = sQtysMapConstrain (qtyEq zeroQty)

sQtysEq :: GivenSolver => SQtys -> SQtys -> IO ()
sQtysEq x y = do
  a <- runCached x
  b <- runCached y

  onQtysV b (writeQtysV a)
  onQtysV a (writeQtysV b)

sQtysLe :: GivenSolver => SQtys -> SQtys -> IO ()
sQtysLe x y = do
  a <- runCached x
  b <- runCached y

  onQtysV a (groundQtysV b)
  onQtysV b (groundQtysV a)

  onQtysV a \av -> onQtysV b \bv -> case (av,bv) of
    (ConsQV q qs, ConsQV q' qs') -> qtyLe q q' >> sQtysLe qs qs'
    (NilQV, NilQV) -> pure ()

-- Qtys (n + 1) -> Qtys n
tailQtys :: Qtys -> Qtys
tailQtys (SnocQty qs _) = qs
tailQtys (SnocSQtys qs _) = qs
tailQtys (WknQtysN n qs) = wknQtysN (n-1) qs

headQtys :: Qtys -> Qty
headQtys (SnocQty _ q) = q
headQtys (WknQtysN n qs) = zeroQty
headQtys SnocSQtys{} = error "headQtys: bad shape"


headQtysS :: Qtys -> SQtys
headQtysS (SnocSQtys _ q) = q
headQtysS (WknQtysN n qs) = zeroSQtys
headQtysS SnocSQtys{} = error "headQtys: bad shape"

zeroSQtys :: SQtys
zeroSQtys = Cached $ do
  r <- newIORef $ UnsolvedQV []

  onQtysV r \case
    NilQV -> pure ()
    ConsQV q qs -> qtyEq q zeroQty >> sQtysEqZero qs

  pure r



-- Qtys n -> Qtys (n + 1)
wknQtys :: Qtys -> Qtys
wknQtys = wknQtysN 1

wknQtysN :: Int -> Qtys -> Qtys
wknQtysN 0 x = x
wknQtysN n (WknQtysN m x) = WknQtysN (n+m) x
wknQtysN n x = WknQtysN n x

tailSQtys :: SQtys -> SQtys
tailSQtys qv = Cached $ do
  r <- runCached qv
  readIORef r >>= \case
    SolvedQV (ConsQV _ qs) -> runCached qs
    SolvedQV NilQV -> error "tailSQtys: bad shape"
    UnsolvedQV _ -> do
      hd <- qtyVar
      tl <- newSQtys
      writeQtysV r (ConsQV hd tl)
      runCached tl

-- TODO: evaluation uses this, so consider using Cached for Qty to make this pure
headSQtys :: GivenSolver => SQtys -> IO Qty
headSQtys qv = do
  r <- runCached qv
  readIORef r >>= \case
    SolvedQV (ConsQV q _) -> pure q
    SolvedQV NilQV -> error "headSQtys: bad shape"
    UnsolvedQV _ -> do
      hd <- qtyVar
      tl <- newSQtys
      writeQtysV r (ConsQV hd tl)
      pure hd
