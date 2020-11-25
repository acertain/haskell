{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# Language CPP #-}
{-# Language DeriveTraversable #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ImplicitParams #-}


-- import Types

-- |
-- Copyright :  (c) Edward Kmett 2020, András Kovács 2020
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable

module Elaborate.Term (Tm(..), TM, Ty, Ix, TY, showTm) where

import Common.Icit
import Common.Names
import Common.Qty
import Elaborate.Value
import Prelude hiding (pi)
import qualified Data.Text.Short as Short
import Data.HashMap.Lazy (HashMap)
import Control.Lens
import qualified Data.HashMap.Lazy as HM
import Control.Monad.State (evalState, state,State)
import Data.Data.Lens (template)
import Numeric.Lens
import Data.Data

type Ty = Tm
type Ix = Int

data Tm a
  = Var !Ix                            -- ^ x
  | Let !Name !(Ty a) !(Tm a) !(Tm a)  -- ^ let x : A = t in u
  | Pi !Name !Icit !Qty !(Ty a) !(Ty a)     -- ^ (x : A) → B)  or  {x : A} → B
  | Lam !Name !Icit !(Ty a) !(Tm a)    -- ^ λ(x : A).t  or  λ{x : A}.t
  | App !Icit (Tm a) !(Tm a)           -- ^ t u  or  t {u}
#ifdef FCIF
  | Tel                                -- ^ Tel
  | TNil                               -- ^ ε
  | TCons !Name !Qty !(Ty a) !(Ty a)        -- ^ (x : A) ▷ B
  | Rec !(Tm a)                        -- ^ Rec A
  | Tnil                               -- ^ []
  | Tcons !(Tm a) !(Tm a)              -- ^ t :: u
  | Car !(Tm a)                        -- ^ π₁ t
  | Cdr !(Tm a)                        -- ^ π₂ t
  | PiTel !Name !Qty !(Ty a) !(Ty a)        -- ^ {x : A⃗} → B
  | AppTel !(Ty a) !(Tm a) !(Tm a)     -- ^ t {u : A⃗}
  | LamTel !Name !(Ty a) !(Tm a)       -- ^ λ{x : A⃗}.t
#endif
  | U                                  -- ^ U
  | Meta a                             -- ^ α
  | Skip !(Tm a)                       -- ^ explicit weakening for closing types
  deriving (Functor,Foldable,Traversable,Data)

type TM = Tm Meta
type TY = Ty Meta

-- | Wrap in parens if expression precedence is lower than
--   enclosing expression precedence.
par :: Int -> Int -> ShowS -> ShowS
par p p' = showParen (p < p')

-- Precedences
atomp :: Int
atomp = 3  -- identifiers, U, ε, Tel
appp :: Int
appp  = 2  -- application (functions, π₁, π₂, Rec): assocs to left
recp :: Int
recp  = 1  -- _∷_ : assocs to right
tmp :: Int
tmp   = 0  -- lam, let, Pi, PiTel, _▷_ : assocs to right

fresh :: [Name] -> Name -> Name
fresh _ x = x
-- fresh _ "_" = "_"
-- fresh ns n | elem n ns = fresh ns (n++"'")
--            | otherwise = n

icit :: Icit -> a -> a -> a
icit Implicit i _ = i
icit Explicit _ e = e

bracket :: ShowS -> ShowS
bracket s = ('{':).s.('}':)

-- | Prints a spine, also returns whether the spine is meta-headed.
spine :: (?naming :: HashMap Name String) => [Name] -> Tm Name -> (ShowS, Bool)
spine ns (App i (spine ns -> (tp, metasp)) u) =
  (tp . (' ':) . icit i (bracket (tm tmp ns u)) (tm atomp ns u), metasp)
spine ns (AppTel a (spine ns -> (tp, metasp)) u) =
  (tp . (' ':) . bracket (tm tmp ns u . (" : "++) . tm tmp ns a), metasp)
spine ns (Meta m) =
  (tm atomp ns (Meta m), True)
spine ns t =
  (tm atomp ns t, False)

lamBind :: (?naming :: HashMap Name String) => Name -> Icit -> ShowS
lamBind x i = icit i bracket id ((if null (name x "") then ("_"++) else name x))

lamTelBind :: (?naming :: HashMap Name String) => [Name] -> Name -> Tm Name -> ShowS
lamTelBind ns x a = bracket (name x.(" : "++).tm tmp ns a)

lams :: (?naming :: HashMap Name String) => [Name] -> Tm Name -> ShowS
lams ns (Lam (fresh ns -> x) i a t) =
  (' ':) . lamBind x i . lams (x:ns) t
lams ns (LamTel (fresh ns -> x) a t) =
  (' ':) . lamTelBind ns x a . lams (x:ns) t
lams ns t =
  (". "++) . tm tmp ns t

piBind :: (?naming :: HashMap Name String) => [Name] -> Name -> Icit -> Tm Name -> ShowS
piBind ns x i a =
  icit i bracket (showParen True) (name x . (" : "++) . tm tmp ns a)

pi :: (?naming :: HashMap Name String) => [Name] -> Tm Name -> ShowS
pi ns (Pi (fresh ns -> x) i _ a b)  | x /= "_" =
  piBind ns x i a . pi (x:ns) b
pi ns (PiTel (fresh ns -> x) _ a b) | x /= "_" =
  piBind ns x Implicit a . pi (x:ns) b
pi ns t = (" → "++) . tm tmp ns t

name :: (?naming :: HashMap Name String) => Name -> ShowS
name x = ((?naming ^?! ix x)++)

tm :: (?naming :: HashMap Name String) => Int -> [Name] -> Tm Name -> ShowS
tm p ns = \case
  Var x -> case ns ^? ix x of
    Just n -> name n
    Nothing -> (show x++)
  Meta m -> name m
  Let (fresh ns -> x) a t u ->
    par tmp p $
      ("let "++).name x.(" : "++). tm tmp ns a . ("\n    = "++)
      . tm tmp ns t . ("\nin\n"++) . tm tmp (x:ns) u
  t@App{} ->
    par appp p $ fst $ spine ns t
  t@AppTel{} ->
    par appp p $ fst $ spine ns t
  Lam x i a t ->
    par tmp p $ ("λ "++) . lamBind x i . lams (x:ns) t

  -- Pi "_" Expl a b ->
  --   par tmp p $ tm recp ns a . (" → "++) . tm tmp ("_":ns) b
  Pi (fresh ns -> x) i _ a b ->
    par tmp p $ piBind ns x i a . pi (x:ns) b

  U      -> ("U"++)
  Tel    -> ("Tel"++)
  TNil -> ("ε"++)

  -- TCons "_" a as ->
  --   par tmp p $ tm recp ns a . (" ▷ "++). tm tmp ns as
  TCons (fresh ns -> x) _ a as ->
    par tmp p $
      showParen True (name x . (" : "++) . tm tmp ns a)
      . (" ▷ "++). tm tmp (x:ns) as

  Tnil    -> ("[]"++)
  Rec a     -> par appp p $ ("Rec "++) . tm atomp ns a
  Tcons t u -> par recp p (tm appp ns t . (" ∷ "++). tm recp ns u)
  Car t   -> par appp p (("π₁ "++). tm atomp ns t)
  Cdr t   -> par appp p (("π₂ "++). tm atomp ns t)

  -- PiTel "_" a b ->
  --   par tmp p $ tm recp ns a . (" → "++) . tm tmp ("_":ns) b
  PiTel (fresh ns -> x) _ a b ->
    par tmp p $ piBind ns x Implicit a . pi (x:ns) b
  LamTel (fresh ns -> x) a t ->
    par tmp p $ ("λ"++) . lamTelBind ns x a . lams (x:ns) t

  Skip t -> tm p ("_":ns) t


nameMetas :: [Name] -> Tm Meta -> (Tm Name, HashMap Name String)
nameMetas ctx t = 
  -- TODO: is traverse redundant w/ template?
    (,()) <$> (toListOf (template :: Traversal' (Tm Name) Name) x <> toListOf traverse x <> ctx)
  & HM.fromList
  & itraverse (\i _ -> nm i)
  & flip evalState metaNames
  & (x,)
  where
  x = fmap metaName t

  nm :: Name -> State [String] String
  nm (SourceName tx _) = pure $ Short.toString tx
  nm (MetaName _ _) = state \case
        (n:ns) -> (n, ns)
        [] -> error "out of names"

  names' :: [String]
  names' = map pure az
      ++ [ i : review (base 36) j | j <- [1 :: Int ..], i <- az ] where
    az = ['a'..'z']

  metaNames :: [String]
  metaNames = map ('?':) names'

showTm :: [Name] -> TM -> String
showTm ns t = let (t',n) = nameMetas ns t in
              let ?naming = n in tm tmp ns t' []





-- -- -- deriving instance Show TM
-- -- -- instance Show TM where show = showTopTM
