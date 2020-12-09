{-# Language CPP #-}
{-# Language ImportQualifiedPost #-}
{-# Language LambdaCase #-}
{-# Language ViewPatterns #-}
{-# Language ScopedTypeVariables #-}

-- |
-- Copyright :  (c) Edward Kmett 2020, András Kovács 2020
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable

module Elaborate.Check where

import Common.Icit
import Common.Names
import Common.Qty
import Control.Monad (unless)
import Control.Lens hiding (Context)
import Elaborate.Error
import Elaborate.Evaluation
import Elaborate.Term
import Elaborate.Value
import Elaborate.Unification
import Source.Term qualified as Raw
import System.IO.Unsafe (unsafeInterleaveIO)
import Solver.Sat.CaDiCaL (simplifyBit)
import Data.Data.Lens

-- | Define a new variable.
define :: Name -> VTy -> Val -> Context -> Context
define x a t (Context vs tys ns no d) =
  Context (VDef vs t) (TySnoc tys Def a) (x:ns) (NOSource:no) (d + 1)

-- | Insert fresh implicit applications.
insert' :: GivenSolver => Context -> IO (Qtys, TM, VTy) -> IO (Qtys, TM, VTy)
insert' cxt act = do
  (qs1, t0, va0) <- act
  let go qs t va = force va >>= \case
        VPi _ Implicit q a b -> do
          (qs',m) <- freshMeta cxt a
          mv' <- b =<< eval (cxt^.vals) m
          go (qs <> mulQtys q qs') (App Implicit t m) mv'
        va' -> pure (qs, t, va')
  go qs1 t0 va0

-- | Insert fresh implicit applications to a term which is not
--   an implicit lambda (i.e. neutral).
insert :: GivenSolver => Context -> IO (Qtys, TM, VTy) -> IO (Qtys, TM, VTy)
insert cxt act = act >>= \case
  (qs, t@(Lam _ Implicit _ _ _), va) -> pure (qs, t, va)
  (qs, t                       , va) -> insert' cxt (pure (qs, t, va))


expectFn :: GivenSolver => Context -> Raw.Term -> Icit -> IO (Qtys, TM, Qty, VTy, EVTy)
expectFn cxt tm i = do
  (qs1, t, va) <- case i of
    -- fcif uses insert' here for agda parity
    -- > For example (λ{A} x. id {A} x) U is elaborated to (λ{A} x. id {A} x) {U} U
    -- but insert would be fine too imo
    Explicit -> insert' cxt $ infer cxt tm
    _        -> infer cxt tm
  force va >>= \case
    VPi _ i' q a b -> do
      unless (i == i') $ report (cxt^.names) $ IcitMismatch i i'
      pure (qs1, t, q, a, b)
    va'@(VNe (HMeta _) _) -> do
      (m',_,a0) <- freshMeta' cxt VU
      a <- eval (cxt^.vals) a0
      let x = metaName m'
      (_,c) <- freshMeta (bind x NOInserted a cxt) VU
      let b x' = eval (VDef (cxt^.vals) x') c
      -- TODO: subusage here?
      q <- qtyVar
      unifyWhile cxt va' (VPi x i q a b)
      pure (qs1, t, q, a, b)
    _ -> do
      r <- unsafeInterleaveIO (uneval (cxt^.len) va)
      report (cxt^.names) $ ExpectedFunction r


infer :: GivenSolver => Context -> Raw.Term -> IO (Qtys, TM, VTy)
infer cxt = \case
  Raw.Loc p t -> addSourcePos p (infer cxt t)

  Raw.U_ -> pure (zeroQtys (cxt ^. len), U_, VU)

  Raw.Var x -> do
    let go :: [Name] -> [NameOrigin] -> Types -> Int -> IO (Qtys, TM, VTy)
        go (y:_) (NOSource:_) (TySnoc _ _ a) i | SourceName x 0 == y = pure (wknQtysN i $ SnocQty (zeroQtys ((cxt ^. len) - i - 1)) oneQty,Var i,a)
        go (_:xs) (_:os) (TySnoc as _ _) i = go xs os as (i + 1)
        go [] [] TyNil _ = report (cxt^.names) $ NameNotInScope (SourceName x 0)
        go _ _ _ _ = panic
    go (cxt^.names) (cxt^.nameOrigin) (cxt^.types) 0

  Raw.Pi qt x i a b -> do
    (q1,a') <- check cxt a VU
    va <- eval (cxt^.vals) a'
    (q2,b') <- check (bind (sourceName x) NOSource va cxt) b VU
    q <- maybe qtyVar (pure . knownQty) qt
    pure (q1 <> tailQtys q2, Pi (sourceName x) i q a' b', VU)

  Raw.App i t0 u -> do
    (qs1, t, q, a, b) <- expectFn cxt t0 i
    (qs2, u') <- check cxt u a
    ty <- eval (cxt^.vals) u' >>= b
    pure (qs1 <> mulQtys q qs2, App i t u', ty)

  Raw.Lam (sourceName -> x) ann i t -> do
    (_, a) <- case ann of
      Just ann' -> check cxt ann' VU
      Nothing   -> freshMeta cxt VU
    va <- eval (cxt^.vals) a
    let cxt' = bind x NOSource va cxt
    (qs, t', liftVal cxt -> b) <- insert cxt' $ infer cxt' t
    q <- qtyVar
    qtyLe (headQtys qs) q    
    pure (tailQtys qs, Lam x i q a t', VPi x i q va b)

  Raw.Hole -> do
    (_,a) <- freshMeta cxt VU
    ~va <- eval (cxt^.vals) a
    (qs,t) <- freshMeta cxt va
    pure (qs, t, va)

  Raw.Let (sourceName -> x) a0 t0 u -> do
    (_,a) <- check cxt a0 VU
    va <- eval (cxt^.vals) a
    (q1,t) <- check cxt t0 va
    vt <- eval (cxt^.vals) t
    (q2, u', b) <- infer (define x va vt cxt) u
    pure (tailQtys q2 <> mulQtys (headQtys q2) q1, Let x a t u', b)

check :: GivenSolver => Context -> Raw.Term -> VTy -> IO (Qtys, TM)
check cxt topT ~topA0 = force topA0 >>= \ ftopA -> case (topT, ftopA) of
  (Raw.Loc p t, a) -> addSourcePos p (check cxt t a)

  (Raw.Lam (sourceName -> x) ann0 i t0, VPi _ i' q a b) | i == i' -> do
    ann' <- case ann0 of
      Just ann1 -> do
        (_, ann) <- check cxt ann1 VU
        ann' <- unsafeInterleaveIO $ eval (cxt^.vals) ann
        unifyWhile cxt ann' a
        pure ann
      Nothing -> uneval (cxt^.len) a
    (qs, t) <- do
      ty <- b (VVar (cxt^.len))
      check (bind x NOSource a cxt) t0 ty
    qtyLe (headQtys qs) q
    pure (tailQtys qs, Lam x i q ann' t)

  (t0, VPi x Implicit q a b) -> do
    ty <- b (VVar (cxt^.len))
    (qs,t) <- check (bind x NOInserted a cxt) t0 ty
    qtyLe (headQtys qs) q
    a' <- uneval (cxt^.len) a
    pure (tailQtys qs, Lam x Implicit q a' t)

#ifdef FCIF
  -- inserting a new curried function lambda
  (t0, VNe (HMeta _) _) -> do
    -- x <- ("Γ"++) . show <$> readMeta nextMId
    (m,_,d) <- freshMeta' cxt VTel
    let x = metaName m
    vdom <- unsafeInterleaveIO $ eval (cxt^.vals) d
    let cxt' = bind x NOInserted (VRec vdom) cxt
    (q2, t, liftVal cxt -> a) <- insert cxt' $ infer cxt' t0
    newConstancy cxt vdom a
    -- TODO: subusage `headQtysS q2`?
    unifyWhile cxt topA0 (VPiTel x (headQtysS q2) vdom a)
    pure (tailQtys q2, LamTel x (headQtysS q2) d t)
#endif

  -- (Raw.Let (sourceName -> x) a0 t0 u0, topA) -> do
  --   a <- check cxt a0 VU
  --   va <- unsafeInterleaveIO (eval (cxt^.vals) a)
  --   t <- check cxt t0 va
  --   vt <- unsafeInterleaveIO (eval (cxt^.vals) t)
  --   u <- check (define x va vt cxt) u0 topA
  --   pure $ Let x a t u

  (Raw.Hole, topA) -> freshMeta cxt topA

  (t0, topA) -> do
    (qs, t, va) <- insert cxt $ infer cxt t0
    unifyWhile cxt va topA
    pure (qs, t)

