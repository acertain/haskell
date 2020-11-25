{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# Language ImplicitParams #-}

module Common.Qty where

import qualified Data.SBV.Internals as SBV
import Data.SBV
import Data.Data
import Control.Monad.Reader
import Data.SBV.Control
import Control.Lens
import Data.IORef
type GivenSolver = (?solver :: SBV.State)

runSolver :: (GivenSolver => IO a) -> IO a
runSolver x = runSMTWith (z3 { verbose = True }) $ query $ do
  s <- queryState
  let ?solver = s
  liftIO x

liftSBV :: GivenSolver => SBV.QueryT m a -> m a
liftSBV (SBV.QueryT q) = runReaderT q ?solver

data Q = E | L | A | R | U_ | S deriving (Show)

data Qty = Qty SBool SBool SBool

instance Data Qty where
  -- FIXME: sbv doesn't have Data instances
  gunfold _ z _ = z zeroQty
  toConstr x = mkConstr (dataTypeOf x) "Qty" [] Prefix
  dataTypeOf x = mkDataType "Elaborate.Value.Qty" [toConstr x]

-- zero-extended, snoc list
newtype Qtys = Qtys { unQtys :: [Qty] }

instance Semigroup Qtys where
  Qtys a <> Qtys b = Qtys (go a b) where
    go (x:xs) (y:ys) = addQty x y:go xs ys
    go x [] = x
    go [] x = x

instance Monoid Qtys where
  mempty = Qtys []


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

zeroQty :: Qty
zeroQty = knownQty E

oneQty :: Qty
oneQty = knownQty L

qtyVar :: GivenSolver => IO Qty
qtyVar = liftSBV $ do
  x <- freshVar "x"
  y <- freshVar "y"
  z <- freshVar "z"
  constrain $ sNot (z .&& y .&& sNot x)
  constrain $ sNot (z .&& sNot y .&& x)
  pure (Qty x y z)

qtyVal :: GivenSolver => Qty -> IO Q
qtyVal (Qty x y z) = liftSBV $ ((,,) <$> getValue x <*> getValue y <*> getValue z) <&> \case
  (False, True, False)  -> E
  (True, True, True)    -> L
  (False, False, True)  -> A
  (False, False, False) -> U_
  (True, False, False)  -> S
  (True, True, False)   -> R
  _                     -> error "impossible"

mulQty :: Qty -> Qty -> Qty
mulQty (Qty a b c) (Qty x y z) = Qty (x .&& a) ((y .|| b) .&& (y .|| sNot a) .&& (b .|| sNot x)) (z .&& c)

addQty :: Qty -> Qty -> Qty
addQty (Qty a b c) (Qty x y z) = Qty (x .|| a) (y .&& b) ((z .&& sNot c .&& sNot a) .|| (c .&& sNot z .&& sNot x))

mulQtys :: Qty -> Qtys -> Qtys
mulQtys q (Qtys x) = Qtys (go x) where
  go (y:ys) = mulQty q y:go ys
  go [] = []

splitQty :: GivenSolver => Qty -> IO (Qty,Qty)
splitQty q = do
  x <- qtyVar
  y <- qtyVar
  qtyEq (addQty x y) q
  pure (x,y)

splitQtys :: GivenSolver => Qtys -> IO (Qtys,Qtys)
splitQtys (Qtys qs) = over both Qtys . unzip <$> traverse splitQty qs

qtyEq :: GivenSolver => Qty -> Qty -> IO ()
qtyEq (Qty a b c) (Qty x y z) = liftSBV $ do
  constrain $ a .== x
  constrain $ b .== y
  constrain $ c .== z
  ensureSat

-- Qtys (n + 1) -> Qtys n
tailQtys :: Qtys -> Qtys
tailQtys (Qtys (_:xs)) = Qtys xs
tailQtys (Qtys []) = Qtys []

headQtys :: Qtys -> Qty
headQtys (Qtys (x:_)) = x
headQtys (Qtys []) = zeroQty

-- Qtys n -> Qtys (n + 1)
wknQtys :: Qtys -> Qtys
wknQtys (Qtys xs) = Qtys (zeroQty:xs)

consQtys :: Qty -> Qtys -> Qtys
consQtys x (Qtys xs) = Qtys (x:xs)
