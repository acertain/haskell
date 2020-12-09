{-# Language CPP #-}
{-# Language LambdaCase #-}
{-# Language BlockArguments #-}
{-# Language ScopedTypeVariables #-}
{-# Language BangPatterns #-}

-- |
-- Copyright :  (c) Edward Kmett 2020, András Kovács 2020
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable

-- QLF.Elaborate.Evaluation

module Elaborate.Evaluation where

import Common.Icit
import Common.Qty
#ifdef FCIF
import Common.Names
#endif
import Data.Functor ((<&>))
import Elaborate.Term
import Elaborate.Value
import GHC.IO.Unsafe

valsLen :: Vals -> Int
valsLen = go 0 where
  go !acc VNil        = acc
  go acc (VDef vs _) = go (acc + 1) vs
  go acc (VSkip vs)  = go (acc + 1) vs

-- eval

evalVar :: Ix -> Vals -> Val
evalVar 0 (VDef _ v) = v
evalVar 0 (VSkip vs) = VVar (valsLen vs)
evalVar x (VDef vs _) = evalVar (x - 1) vs
evalVar x (VSkip vs) = evalVar (x - 1) vs
evalVar _ _ = panic

evalMeta :: Meta -> IO Val
evalMeta m = readMeta m <&> \case
  Unsolved{} -> VMeta m
  Solved v -> v
#ifdef FCIF
  _ -> panic
#endif


#ifdef FCIF
evalCar :: GivenSolver => Val -> IO Val
evalCar (VTcons t _) = pure t
evalCar (VNe h sp) = pure $ VNe h (SCar sp)
evalCar (VLamTel x q a t) = evalLamTel pure x q a t >>= evalCar
evalCar _ = panic

evalCdr :: GivenSolver => Val -> IO Val
evalCdr (VTcons _ u) = pure u
evalCdr (VNe h sp) = pure $ VNe h (SCdr sp)
evalCdr (VLamTel x q a t) = evalLamTel pure x q a t >>= evalCdr
evalCdr _ = panic

evalPiTel :: GivenSolver => EVal -> Name -> SQtys -> VTy -> EVal -> IO Val
evalPiTel k x q a0 b = force a0 >>= \case
  VTNil -> b VTnil >>= k
  VTCons _ a as -> do
    hq <- headSQtys q
    let (x',x'') = splitName x
    pure $ VPi x' Implicit hq a \ ~x1 -> do
      ~x1v <- as x1
      evalPiTel pure x'' (tailSQtys q) x1v \ ~x2 -> b (VTcons x1 x2)
  a -> pure $ VPiTel x q a b

evalLamTel :: GivenSolver => EVal -> Name -> SQtys -> VTy -> EVal -> IO Val
evalLamTel k x q a0 t = force a0 >>= \case
  VTNil -> t VTnil >>= k
  VTCons _ a as -> do
    hq <- headSQtys q
    let (x',x'') = splitName x
    pure $ VLam x' Implicit hq a \ ~x1 -> do
      ~x1v <- as x1
      evalLamTel pure x'' (tailSQtys q) x1v \ ~x2 -> t (VTcons x1 x2)
  a -> pure $ VLamTel x q a t

evalAppTel :: GivenSolver => VTy -> Val -> Val -> IO Val
evalAppTel a0 t u = force a0 >>= \case
  VTNil -> pure t
  VTCons _ _ as -> do
    u1 <- evalCar u
    u1v <- as u1
    u2 <- evalCdr u
    t' <- evalApp Implicit t u1
    evalAppTel u1v t' u2
  a -> case t of
    VNe h sp -> pure $ VNe h (SAppTel a sp u)
    VLamTel _ _ _ t' -> t' u
    _ -> panic
#endif

evalApp :: GivenSolver => Icit -> Val -> Val -> IO Val
evalApp _ (VLam _ _ _ _ t)  u = t u
evalApp i (VNe h sp)        u = pure $ VNe h (SApp i sp u)
#ifdef FCIF
evalApp i (VLamTel x q a t) u = do
  y <- evalLamTel pure x q a t
  evalApp i y u
#endif
evalApp _                _ _ = panic

evalAppSp :: GivenSolver => Val -> Spine -> IO Val
evalAppSp h = go where
  go SNil             = pure h
  go (SApp i sp u)    = do sp' <- go sp; evalApp i sp' u
#ifdef FCIF
  go (SAppTel a sp u) = do sp' <- go sp; evalAppTel a sp' u
  go (SCar sp)      = go sp >>= evalCar
  go (SCdr sp)      = go sp >>= evalCdr
#endif

force :: GivenSolver => Val -> IO Val
force = \case
  v0@(VNe (HMeta m) sp) -> readMeta m >>= \case
    Unsolved{} -> pure v0
    Solved v   -> evalAppSp v sp >>= force
#ifdef FCIF
    _ -> panic
  VPiTel x q a b -> evalPiTel force x q a b
  VLamTel x q a t -> evalLamTel force x q a t
#endif
  v -> pure v

forceSp :: GivenSolver => Spine -> IO Spine
forceSp sp =
  -- This is a cheeky hack, the point is that (VVar (-1)) blocks computation, and
  -- we get back the new spine.  We use (-1) in order to make the hack clear in
  -- potential debugging situations.
  evalAppSp (VVar (-1)) sp >>= \case
    VNe _ sp' -> pure sp'
    _ -> panic

eval :: GivenSolver => Vals -> TM -> IO Val
eval vs = go where
  go = \case
    Var x        -> pure $ evalVar x vs
    Let _ _ t u  -> go t >>= goBind u
    U_           -> pure VU
    Meta m       -> evalMeta m
    Pi x i q a b   -> unsafeInterleaveIO (go a) <&> \a' -> VPi x i q a' (goBind b)
    Lam x i q a t  -> unsafeInterleaveIO (go a) <&> \a' -> VLam x i q a' (goBind t)
    App i t u    -> do
      t' <- unsafeInterleaveIO (go t)
      u' <- unsafeInterleaveIO (go u)
      evalApp i t' u'
#ifdef FCIF
    Tel          -> pure VTel
    TNil         -> pure VTNil
    TCons x a b  -> unsafeInterleaveIO (go a) <&> \a' -> VTCons x a' (goBind b)
    Rec a        -> VRec <$> go a
    Tnil         -> pure VTnil
    Tcons t u    -> VTcons <$> unsafeInterleaveIO (go t) <*> unsafeInterleaveIO (go u)
    Car t        -> go t >>= evalCar
    Cdr t        -> go t >>= evalCdr
    PiTel x q a b  -> do
      a' <- unsafeInterleaveIO (go a)
      evalPiTel pure x q a' (goBind b)
    AppTel a t u -> do
      a' <- unsafeInterleaveIO (go a)
      t' <- unsafeInterleaveIO (go t)
      u' <- unsafeInterleaveIO (go u)
      evalAppTel a' t' u'
    LamTel x q a t -> do
      a' <- unsafeInterleaveIO (go a)
      evalLamTel pure x q a' (goBind t)
#endif
    Skip t -> eval (VSkip vs) t

  goBind t x = eval (VDef vs x) t

uneval :: GivenSolver => Lvl -> Val -> IO TM
uneval d = go where
  go v = force v >>= \case
    VNe h sp0 ->
      let goSp SNil = case h of
            HMeta m -> pure $ Meta m
            HVar x  -> pure $ Var (d - x - 1)
          goSp (SApp i sp u) = App i <$> goSp sp <*> go u
#ifdef FCIF
          goSp (SAppTel a sp u) = AppTel <$> go a <*> goSp sp <*> go u
          goSp (SCar sp) = Car <$> goSp sp
          goSp (SCdr sp) = Cdr <$> goSp sp
#endif
      in forceSp sp0 >>= goSp

    VLam x i q a t  -> Lam x i q <$> go a <*> goBind t
    VPi x i q a b   -> Pi x i q <$> go a <*> goBind b
    VU            -> pure U_
#ifdef FCIF
    VTel          -> pure Tel
    VRec a        -> Rec <$> go a
    VTNil         -> pure TNil
    VTCons x a as -> TCons x <$> go a <*> goBind as
    VTnil         -> pure Tnil
    VTcons t u    -> Tcons <$> go t <*> go u
    VPiTel x q a b  -> PiTel x q <$> go a <*> goBind b
    VLamTel x q a t -> LamTel x q <$> go a <*> goBind t
#endif

  goBind t = t (VVar d) >>= uneval (d + 1)

uneval' :: GivenSolver => Lvl -> Val -> IO TM
uneval' d = go where
  go = \case
    VNe h sp0 ->
      let goSp SNil = case h of
            HMeta m -> pure $ Meta m
            HVar x  -> pure $ Var (d - x - 1)
          goSp (SApp i sp u) = App i <$> goSp sp <*> go u
#ifdef FCIF
          goSp (SAppTel a sp u) = AppTel <$> go a <*> goSp sp <*> go u
          goSp (SCar sp) = Car <$> goSp sp
          goSp (SCdr sp) = Cdr <$> goSp sp
#endif
      in goSp sp0

    VLam x i q a t  -> Lam x i q <$> go a <*> goBind t
    VPi x i q a b   -> Pi x i q <$> go a <*> goBind b
    VU            -> pure U_
#ifdef FCIF
    VTel          -> pure Tel
    VRec a        -> Rec <$> go a
    VTNil         -> pure TNil
    VTCons x a as -> TCons x <$> go a <*> goBind as
    VTnil         -> pure Tnil
    VTcons t u    -> Tcons <$> go t <*> go u
    VPiTel x q a b  -> PiTel x q <$> go a <*> goBind b
    VLamTel x q a t -> LamTel x q <$> go a <*> goBind t
#endif

  goBind t = t (VVar d) >>= uneval (d + 1)


nf :: GivenSolver => Vals -> TM -> IO TM
nf vs t = do
  v <- eval vs t
  uneval 0 v
{-# inline nf #-}
