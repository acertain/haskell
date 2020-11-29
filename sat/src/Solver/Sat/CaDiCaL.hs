{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ConstraintKinds #-}
{-# language ImplicitParams #-}
{-# language PatternSynonyms #-}

module Solver.Sat.CaDiCaL (
  Bit(..), Literal, (.&&), (.||), (.==), notb, trueb, falseb, exists,
  GivenSAT, withSolver, assert, evalBit, fixedBit, solveWith, solve
) where

import Foreign
import Foreign.C
import Data.IORef
import System.Mem.StableName
import qualified Data.HashMap.Strict as M

import Data.Functor
import Data.Foldable
import Data.Data
import Data.Hashable
import GHC.Generics

newtype Literal = Literal { literalId :: CInt }
  deriving (Data, Typeable, Show, Eq, Ord, Generic)
  deriving Hashable via Int32

deriving instance Data CInt

literalFalse :: Literal
literalFalse = Literal (-1)
literalTrue :: Literal
literalTrue = Literal 1
negateLiteral :: Literal -> Literal
negateLiteral (Literal x) = Literal (-x)

data Bit = And ![Bit] | Not !Bit | Var !Literal
  deriving (Data, Typeable, Show, Eq, Ord, Generic, Hashable)

(.&&) :: Bit -> Bit -> Bit
And as .&& And bs = And (as ++ bs)
And as .&& b = And (b:as)
a .&& And bs = And (a:bs)
a .&& b = And [a,b]

(.||) :: Bit -> Bit -> Bit
x .|| y = notb (notb x .&& notb y)

(.==) :: Bit -> Bit -> Bit
x .== y = (x .&& y) .|| (notb x .&& notb y)

notb :: Bit -> Bit
notb (Not b) = b
notb (Var l) = Var (negateLiteral l)
notb x = Not x

trueb :: Bit
trueb = Var literalTrue

falseb :: Bit
falseb = Var literalTrue


data Clause = Clause [Literal]
data Formula = Formula [Clause]

data CCadicalState

data State = State {
  cCadical :: Ptr CCadicalState,
  nextVar :: {-# UNPACK #-} !(IORef CInt),
  stableMap :: {-# UNPACK #-} !(IORef (M.HashMap (StableName Bit) Literal))
}

type GivenSAT = (?satState :: State)

-- check if the literal is known to be fixed at root decision level, replace it with its value if so
literalFixed :: GivenSAT => Literal -> IO Literal
literalFixed l = ccadical_fixed (cCadical ?satState) (literalId l) <&> \case
  1 -> Literal 1
  -1 -> Literal $ -1
  0 -> l
  _ -> error "invalid return value from ccadical_fixed"

literalExists :: GivenSAT => IO Literal
literalExists = atomicModifyIORef' (nextVar ?satState) (\i -> (i+1,Literal i))

exists :: GivenSAT => IO Bit
exists = Var <$> literalExists

withSolver :: (GivenSAT => IO a) -> IO a
withSolver x = do
  cCadical <- ccadical_init
  nextVar <- newIORef 2
  stableMap <- newIORef mempty
  let ?satState = State {..}
  assert $ Var $ Literal 1
  r <- x
  ccadical_release cCadical
  pure r

assertFormula :: GivenSAT => Formula -> IO ()
assertFormula (Formula x) = for_ x assertClause

assertClause :: GivenSAT => Clause -> IO ()
assertClause (Clause cl) = do
  let s = cCadical ?satState
  for_ cl \l -> ccadical_add s $ literalId l
  ccadical_add s 0

assert :: GivenSAT => Bit -> IO ()
assert (And bs) = for_ bs assert
assert b = do
  l <- runBit b
  assertClause $ Clause [l]

-- | Convert a 'Bit' to a 'Literal'.
runBit :: GivenSAT => Bit -> IO Literal
runBit (Not c) = negateLiteral `fmap` runBit c
runBit (Var l) = return l
runBit b = do
  sn <- makeStableName $! b
  m <- readIORef (stableMap ?satState)
  case M.lookup sn m of
    Just v -> pure v
    Nothing -> case b of
      And bs -> traverse runBit (toList bs) >>= simplifyAnd >>= \case
        [] -> pure literalTrue
        [l] -> pure l
        l -> generateLiteral sn $ \out -> assertFormula $ formulaAnd out l
      Not _ -> error "Unreachable"
      Var _ -> error "Unreachable"
  where
  simplifyAnd :: [Literal] -> IO [Literal]
  simplifyAnd (l:ls) = literalFixed l >>= \case
    Literal 1 -> simplifyAnd ls
    Literal (-1) -> pure [literalFalse]
    _ -> (l:) <$> simplifyAnd ls
  simplifyAnd [] = pure []

  generateLiteral :: StableName Bit -> (Literal -> IO ()) -> IO Literal
  generateLiteral sn f = do
    x <- literalExists
    modifyIORef' (stableMap ?satState) (M.insert sn x)
    f x
    pure x

  formulaAnd :: Literal -> [Literal] -> Formula
  formulaAnd out inpLs = Formula $
    Clause (out : map negateLiteral inpLs) : map (\inp -> Clause [negateLiteral out, inp]) inpLs

lookupBit :: GivenSAT => Bit -> IO (Maybe Literal)
lookupBit b = do
  sn <- makeStableName $! b
  m <- readIORef (stableMap ?satState)
  pure $ M.lookup sn m

evalBit :: GivenSAT => Bit -> IO Bool
evalBit b = lookupBit b >>= \case
  Just l -> e l
  Nothing -> case b of
    Var l -> e l
    And xs -> and <$> traverse evalBit xs
    Not x -> not <$> evalBit x
  where e l = maybe (error "runBit: unknown variable (call solve first!)") id <$> evalLiteral l

fixedBit :: GivenSAT => Bit -> IO (Maybe Bool)
fixedBit b = lookupBit b >>= \case
  Just l -> e l
  Nothing -> case b of
    Var l -> e l
    And xs -> fmap and . sequence <$> traverse fixedBit xs
    Not x -> fmap not <$> fixedBit x
  where
    e l = do
      r <- literalFixed l
      case r of
        Literal 1 -> pure $ Just True
        Literal (-1) -> pure $ Just False
        _ -> pure Nothing

evalLiteral :: GivenSAT => Literal -> IO (Maybe Bool)
evalLiteral (Literal l) = do
  r <- ccadical_val (cCadical ?satState) l
  pure $! if | r == -1 -> Nothing
             | r > 0 -> Just True
             | r < 0 -> Just False
             | r == 0 -> Nothing

-- | solve with assumptions
solveWith :: GivenSAT => [Bit] -> IO (Maybe Bool)
solveWith ls = do
  let s = cCadical ?satState
  ls' <- traverse runBit ls
  for_ ls' \(Literal l) -> ccadical_assume s l
  ccadical_solve s >>= \case
    0 -> pure Nothing
    10 -> pure $ Just True
    20 -> pure $ Just False
    _ -> error "invalid return value from ccadical_solve"

solve :: GivenSAT => IO (Maybe Bool)
solve = solveWith []

foreign import ccall "ccadical_init" ccadical_init :: IO (Ptr CCadicalState)
foreign import ccall "ccadical_release" ccadical_release :: Ptr CCadicalState -> IO ()

foreign import ccall "ccadical_add" ccadical_add :: Ptr CCadicalState -> CInt -> IO ()
foreign import ccall "ccadical_assume" ccadical_assume :: Ptr CCadicalState -> CInt -> IO ()

foreign import ccall "ccadical_solve" ccadical_solve :: Ptr CCadicalState -> IO CInt
foreign import ccall "ccadical_val" ccadical_val :: Ptr CCadicalState -> CInt -> IO CInt

foreign import ccall "ccadical_fixed" ccadical_fixed :: Ptr CCadicalState -> CInt -> IO CInt
