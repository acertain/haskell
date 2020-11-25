{-# Language CPP #-}
{-# Language ScopedTypeVariables #-}
{-# Language LambdaCase #-}

module Elaborate.Zonk where

import Data.Functor ((<&>))
import Elaborate.Evaluation
import Elaborate.Term
import Elaborate.Value

-- | Unfold all metas and evaluate meta-headed spines, but don't evaluate
--   anything else.
zonk :: Vals -> TM -> IO TM
zonk vs t0 = go t0 where

  goSp :: TM -> IO (Either Val TM)
  goSp = \case
    Meta m -> readMeta m <&> \case
      Solved v -> Left v
      _        -> Right (Meta m)
    App ni t1 u -> goSp t1 >>= \case
      Left t  -> Left <$> do
        u' <- eval vs u
        evalApp ni t u'
      Right t -> go u <&> \u' -> Right $ App ni t u'
#ifdef FCIF
    AppTel a t1 u -> goSp t1 >>= \case
      Left t  -> do
        a' <- eval vs a
        u' <- eval vs u
        Left <$> evalAppTel a' t u'
      Right t -> do
        a' <- go a 
        u' <- go u
        pure $ Right $ AppTel a' t u'
#endif
    t -> Right <$> zonk vs t

  goBind = zonk (VSkip vs)

  go = \case
    Var x        -> pure $ Var x
    Meta m       -> readMeta m >>= \case
      Solved v   -> uneval (valsLen vs) v
      Unsolved{} -> pure $ Meta m
#ifdef FCIF
      _          -> panic
#endif
    U            -> pure U
    Pi x i q a b   -> Pi x i q <$> go a <*> goBind b
    App ni t1 u   -> goSp t1 >>= \case
      Left t  -> do
        u' <- eval vs u
        t' <- evalApp ni t u'
        uneval (valsLen vs) t'
      Right t -> App ni t <$> go u
    Lam x i a t  -> Lam x i <$> go a <*> goBind t
    Let x a t u  -> Let x <$> go a <*> go t <*> goBind u
    Skip t       -> Skip <$> goBind t
#ifdef FCIF
    Tel          -> pure Tel
    TNil         -> pure TNil
    TCons x q t u  -> TCons x q <$> go t <*> goBind u
    Rec a        -> Rec <$> go a
    Tnil         -> pure Tnil
    Tcons t u    -> Tcons <$> go t <*> go u
    Car t        -> Car <$> go t
    Cdr t        -> Cdr <$> go t
    PiTel x q a b  -> PiTel x q <$> go a <*> goBind b
    AppTel a t1 u -> goSp t1 >>= \case
      Left t  -> do
        a' <- eval vs a
        u' <- eval vs u
        t' <- evalAppTel a' t u'
        uneval (valsLen vs) t'
      Right t -> do
        a' <- go a
        u' <- go u
        pure $ AppTel a' t u'
    LamTel x a b -> LamTel x <$> go a <*> goBind b
#endif
