{-# Language CPP #-}
{-# Language LambdaCase #-}
{-# Language BlockArguments #-}
{-# Language ImportQualifiedPost #-}
{-# Language ViewPatterns #-}
{-# Language TemplateHaskell #-}
{-# Language BangPatterns #-}
{-# Language DeriveAnyClass #-}
{-# Language DerivingVia #-}
{-# Language GADTs #-}
{-# Language ScopedTypeVariables #-}
{-# Language TypeApplications #-}
{-# Language TupleSections #-}

-- |
-- Copyright :  (c) Edward Kmett and András Kovács 2020
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable

module Elaborate.Unification where

import Common.Icit
import Common.Names
import Common.Qty
import Control.Lens hiding (Context)
import Data.Foldable (forM_)
#ifdef FCIF
import Data.HashSet qualified as HS
#endif
import Data.HashMap.Strict qualified as HM
import Data.Maybe (isJust)
import Elaborate.Error
import Elaborate.Evaluation
import Elaborate.Term
import Elaborate.Value
#ifdef FCIF
import Elaborate.Occurrence
#endif
import System.IO.Unsafe (unsafeInterleaveIO)
import Control.Exception (catch, throwIO, try)

lvlName :: Int -> [Name] -> Lvl -> Name
lvlName ln ns x = ns !! (ln - x - 1)

type Renaming = HM.HashMap Lvl Lvl

-- | Add a bound variable.
bind :: Name -> NameOrigin -> VTy -> Context -> Context
bind x o a (Context vs tys ns no d) = Context (VSkip vs) (TySnoc tys Bound a) (x:ns) (o:no) (d + 1)

bindSrc :: Name -> VTy -> Context -> Context
bindSrc x = bind x NOSource

-- | Lift ("skolemize") a value in an extended context to a function in a
--   non-extended context.
liftVal :: Context -> Val -> EVal
liftVal cxt t = \ ~x -> do
  tm <- uneval (cxt^.len+1) t
  eval (VDef (cxt^.vals) x) tm

-- | Explicit strengthening. We use this for pruning and checking meta solution
--   candidates.
data Str = Str {
  _dom :: {-# UNPACK #-} !Lvl, -- ^ size of renaming domain
  _cod :: {-# UNPACK #-} !Lvl, -- ^ size of renaming codomain
  _ren :: !Renaming,           -- ^ partial renaming
  _occ :: Maybe Meta           -- ^ meta for occurs checking
  }

makeLenses ''Str

-- | Strengthens a value, returns a unevaled normal result. This performs scope
--   checking, meta occurs checking and (recursive) pruning at the same time.
--   May throw `StrengtheningError`.
strengthen :: Str -> Val -> IO TM
strengthen str0 = go where

  -- we only prune all-variable spines with illegal var occurrences,
  -- we don't prune illegal cyclic meta occurrences.
  prune :: Meta -> Spine -> IO ()
  prune m sp0 = do

    let prune' :: [Bool] -> Spine -> IO (Maybe [Bool])
        prune' acc SNil                    = pure (Just acc)
        prune' acc (SApp _ sp (VVar x))    = prune' (isJust (HM.lookup x (str0^.ren)) : acc) sp
#ifdef FCIF
        prune' acc (SAppTel _ sp (VVar x)) = prune' (isJust (HM.lookup x (str0^.ren)) : acc) sp
#endif
        prune' _   _                       = pure Nothing

    prune' [] sp0 >>= \case
      Nothing -> pure ()  -- spine is not a var substitution
      Just pruning 
        | and pruning -> pure ()  -- no pruneable vars
        | otherwise -> do

        metaTy <- readMeta m >>= \case
          Unsolved _ a -> pure a
          _ -> panic

        -- note: this can cause recursive pruning of metas in types
        prunedTy <- do
          let go' :: [Bool] -> Str -> VTy -> IO TY

              go' [] str z = strengthen str z

              go' (True:pr) str z = force z >>= \case
                VPi x i q a b -> do
                  r <- unsafeInterleaveIO $ b $ VVar (str^.cod)
                  Pi x i q <$> strengthen str a <*> go' pr (liftStr str) r
#ifdef FCIF
                VPiTel x q a b ->do
                  r <- unsafeInterleaveIO $ b $ VVar (str^.cod)
                  PiTel x q <$> strengthen str a <*> go' pr (liftStr str) r
#endif
                _ -> panic

              go' (False:pr) str z = force z >>= \case
                VPi _ _ _ _ b -> do
                  r <- unsafeInterleaveIO $ b $ VVar (str^.cod)
                  go' pr (skipStr str) r
#ifdef FCIF
                VPiTel _ _ _ b -> do
                  r <- unsafeInterleaveIO $ b $ VVar (str^.cod)
                  go' pr (skipStr str) r
#endif
                _ -> panic

          go' pruning (Str 0 0 mempty Nothing) metaTy

        pty <- eval VNil prunedTy
        -- TODO: do we need to do anything more for qtys here?
        m' <- newMeta $ Unsolved mempty pty

        let argNum = length pruning
            body = go' pruning metaTy (Meta m') 0 where
              go' [] _ acc _ = pure acc
              go' (True:pr) z acc d = do
                force z >>= \case 
                  VPi _ i _ _ b -> do
                    a' <- unsafeInterleaveIO $ b (VVar d)
                    go' pr a' (App i acc (Var (argNum - d - 1))) (d + 1)
#ifdef FCIF
                  VPiTel _ _ a b -> do
                    a' <- unsafeInterleaveIO $ b (VVar d)
                    u <- unsafeInterleaveIO $ uneval argNum a
                    go' pr a' (AppTel u acc (Var (argNum - d - 1))) (d + 1)
#endif
                  _ -> panic 
              go' (False:pr) z acc d = do
                force z >>= \case
                  VPi _ _ _ _ b -> do
                    a' <- unsafeInterleaveIO $ b (VVar d)
                    go' pr a' acc (d + 1)
#ifdef FCIF
                  VPiTel _ _ _ b -> do
                    a' <- unsafeInterleaveIO $ b (VVar d)
                    go' pr a' acc (d + 1)
#endif
                  _ -> panic

        b <- body
        rhs <- do
          rhs <- closingTm metaTy argNum [] b
          eval VNil rhs 
        writeMeta m $ Solved rhs

  go :: Val -> IO TM
  go t = force t >>= \case
    VNe (HVar x) sp  -> case HM.lookup x (str0^.ren) of
                          Nothing -> throwIO $ ScopeError x
                          Just x' -> do
                            y <- unsafeInterleaveIO (forceSp sp)
                            goSp (Var (str0^.dom - x' - 1)) y
    VNe (HMeta m0) sp -> if Just m0 == str0^.occ then
                          throwIO OccursCheck
                        else do
                          prune m0 sp
                          force (VNe (HMeta m0) sp) >>= \case
                            VNe (HMeta m') sp' -> goSp (Meta m') sp'
                            _ -> panic

    VPi x i q a b     -> Pi x i q <$> go a <*> goBind b
    VLam x i a t'    -> Lam x i <$> go a <*> goBind t'
    VU               -> pure U
#ifdef FCIF
    VTel             -> pure Tel
    VRec a           -> Rec <$> go a
    VTNil            -> pure TNil
    VTCons x q a b   -> TCons x q <$> go a <*> goBind b
    VTnil            -> pure Tnil
    VTcons t' u      -> Tcons <$> go t' <*> go u
    VPiTel x q a b   -> PiTel x q <$> go a <*> goBind b
    VLamTel x a t'   -> LamTel x <$> go a <*> goBind t'
#endif

  goBind :: EVal -> IO TM
  goBind t = t (VVar (str0^.cod)) >>= strengthen (liftStr str0) 

  goSp h = \case
    SNil           -> pure h
    SApp i sp u    -> App i <$> goSp h sp <*> go u
#ifdef FCIF
    SAppTel a sp u -> AppTel <$> go a <*> goSp h sp <*> go u
    SCar sp      -> Car <$> goSp h sp
    SCdr sp      -> Cdr <$> goSp h sp
#endif

-- | Lift a `Str` over a bound variable.
liftStr :: Str -> Str
liftStr (Str c d r o) = Str (c + 1) (d + 1) (HM.insert d c r) o

-- | Skip a bound variable.
skipStr :: Str -> Str
skipStr (Str c d r o) = Str c (d + 1) r o

closingTy :: GivenSolver => Context -> TY -> IO (TY, Qtys)
closingTy cxt = go (cxt^.types) (cxt^.names) (cxt^.len) where
  go TyNil [] _ b = pure (b, mempty)
  go (TySnoc tys Def _) (_:ns) d b = over _2 wknQtys <$> go tys ns (d-1) (Skip b)
#ifdef FCIF
  go (TySnoc tys Bound (VRec a)) (x:ns) d b = do
    a' <- uneval (d-1) a
    q <- qtyVar
    over _2 (consQtys q) <$> go tys ns (d-1) (PiTel x q a' b)
#endif
  go (TySnoc tys Bound a) (x:ns) d b = do
    a' <- uneval (d-1) a
    q <- qtyVar
    over _2 (consQtys q) <$> go tys ns (d-1) (Pi x Explicit q a' b)
  go _ _ _ _ = panic

-- | Close a term by wrapping it in `Int` number of lambdas, while taking the domain
--   types from the `VTy`, and the binder names from a list. If we run out of provided
--   binder names, we pick the names from the Pi domains.
closingTm :: VTy -> Int -> [Name] -> TM -> IO TM
closingTm = go 0 mempty where
  getName []     x = x
  getName (x:_)  _ = x

  go !_ !qs !_ 0 !_ rhs = do
    pure rhs
  go d qs ty l xs rhs = force ty >>= \case
    VPi (getName xs -> x) i q a b  -> do
      a' <- b (VVar d) 
      bd <- uneval d a 
      Lam x i bd <$> go (d + 1) (consQtys q qs) a' (l-1) (drop 1 xs) rhs
#ifdef FCIF
    VPiTel (getName xs -> x) q a b -> do
      a' <- b (VVar d)
      bd <- uneval d a
      LamTel x bd <$> go (d + 1) (consQtys q qs) a' (l-1) (drop 1 xs) rhs
#endif
    _ -> panic

#ifdef FCIF
newConstancy :: GivenSolver => Context -> VTy -> EVal -> IO ()
newConstancy cxt d c = do
  v <- c (VVar (cxt^.len))
  m <- newMeta $ Constancy cxt d v mempty
  tryConstancy m
#endif

tryConstancy :: GivenSolver => Meta -> IO ()
#ifdef FCIF
tryConstancy constM = readMeta constM >>= \case
  Constancy cxt d c blockers -> do
    forM_ blockers \m ->
      modifyMeta m \case
        Unsolved ms a -> Unsolved (HS.delete constM ms) a
        Solved t -> Solved t
        _ -> panic
    let dropConstancy = writeMeta constM Dropped
        n = cxt^.len
    occurs (n+1) n c >>= \case
      None    -> unify cxt d VTNil >> dropConstancy
      Rigid   -> dropConstancy
      Flex ms -> do
        forM_ ms \m ->
          modifyMeta m $ \case
            Unsolved ms' a -> Unsolved (HS.insert constM ms') a
            _ -> panic
        writeMeta constM $ Constancy cxt d c ms
  _ -> panic
#else
tryConstancy = panic
#endif

data SP = SP Spine {-# UNPACK #-} !Lvl

freshMeta' :: GivenSolver => Context -> VTy -> IO (Meta, Qtys, TM)
freshMeta' cxt v = do
  a <- uneval (cxt^.len) v
  (metaTy,qtys) <- closingTy cxt a
  t <- eval VNil metaTy
  m <- newMeta $ Unsolved mempty t
  let vars :: Types -> SP
      vars TyNil                                      = SP SNil 0
      vars (TySnoc (vars -> SP sp d) Def _)           = SP sp (d + 1)
#ifdef FCIF
      vars (TySnoc (vars -> SP sp d) Bound (VRec a')) = SP (SAppTel a' sp (VVar d)) (d + 1)
#endif
      vars (TySnoc (vars -> SP sp d) Bound _)         = SP (SApp Explicit sp (VVar d)) (d + 1)
  case vars (cxt^.types) of
    SP sp _ -> (m,qtys,) <$> uneval (cxt^.len) (VNe (HMeta m) sp)

freshMeta :: GivenSolver => Context -> VTy -> IO (Qtys, TM)
freshMeta cxt v = (\(_,b,c) -> (b,c)) <$> freshMeta' cxt v

-- | Wrap the inner `UnifyError` arising from unification in an `UnifyErrorWhile`.
--   This decorates an error with one additional piece of context.
unifyWhile :: GivenSolver => Context -> Val -> Val -> IO ()
unifyWhile cxt l r = unify cxt l r `catch` \e -> do
  l' <- unsafeInterleaveIO (uneval (cxt^.len) l)
  r' <- unsafeInterleaveIO (uneval (cxt^.len) l)
  reportM (cxt^.names) $ UnifyErrorWhile l' r' e

checkSp :: Spine -> IO (Renaming, Lvl, [Lvl])
checkSp s0 = do
  s1 <- forceSp s0
  go s1 <&> over _3 reverse 
 where
  go :: Spine -> IO (Renaming, Lvl, [Lvl])
  go = \case
    SNil        -> pure (mempty, 0, [])
    SApp _ sp u -> do
      (!r, !d, !xs) <- go sp
      force u >>= \case
        VVar x | HM.member x r -> throwIO $ NonLinearSpine x
               | otherwise -> pure (HM.insert x d r, d + 1, x:xs)
        _      -> throwIO SpineNonVar
#ifdef FCIF
    SAppTel _ sp u -> do
      (!r, !d, !xs) <- go sp
      force u >>= \case
        VVar x | HM.member x r -> throwIO $ NonLinearSpine x
               | otherwise     -> pure (HM.insert x d r, d + 1, x:xs)
        _    -> throwIO SpineNonVar
    SCar _ -> throwIO SpineProjection
    SCdr _ -> throwIO SpineProjection
#endif

-- | May throw `UnifyError`.
solveMeta :: GivenSolver => Context -> Meta -> Spine -> Val -> IO ()
solveMeta cxt m sp rhs = do

  -- these normal forms are only used in error reporting
  let topLhs = unsafeInterleaveIO $ uneval (cxt^.len) (VNe (HMeta m) sp)
      topRhs = unsafeInterleaveIO $ uneval (cxt^.len) rhs

  -- check spine
  (r, spLen, spVars) <- checkSp sp
    `catch` \e -> do
      tlhs <- topLhs 
      trhs <- topRhs
      throwIO $ SpineError (cxt^.names) tlhs trhs e

  --  strengthen right hand side
  srhs <- strengthen (Str spLen (cxt^.len) r (Just m)) rhs
    `catch` \e -> do
      tlhs <- topLhs 
      trhs <- topRhs
      throwIO $ StrengtheningError (cxt^.names) tlhs trhs e

  (blocked, metaTy) <- readMeta m >>= \case
    Unsolved blocked a -> pure (blocked, a)
    _ -> panic

  let spVarNames = map (lvlName (cxt^.len) (cxt^.names)) spVars
  closedRhs <- closingTm metaTy spLen spVarNames srhs
  erhs <- eval VNil closedRhs
  writeMeta m $ Solved erhs
  forM_ blocked tryConstancy

-- | May throw `UnifyError`.
unify :: GivenSolver => Context -> Val -> Val -> IO ()
unify cxt l r = go l r where

  unifyError :: IO ()
  unifyError = do
    l' <- unsafeInterleaveIO $ uneval (cxt^.len) l
    r' <- unsafeInterleaveIO $ uneval (cxt^.len) r
    throwIO $ UnifyError (cxt^.names) l' r'

  -- if both sides are meta-headed, we simply try to check both spines
  flexFlex m sp m' sp' = try @SpineError (checkSp sp) >>= \case
    Left{}  -> solveMeta cxt m' sp' (VNe (HMeta m) sp)
    Right{} -> solveMeta cxt m sp (VNe (HMeta m') sp')

#ifdef FCIF
  implArity :: Context -> EVal -> IO Int
  implArity cxt' b = b (VVar (cxt'^.len)) >>= go' 0 (cxt'^.len + 1) where
    go' :: Int -> Int -> Val -> IO Int
    go' !acc ln a = force a >>= \case
      VPi _ Implicit _ _ b' -> b' (VVar ln) >>= go' (acc + 1) (ln + 1)
      _ -> pure acc
#endif

  go :: Val -> Val -> IO ()
  go t0 t0' = ((,) <$> force t0 <*> force t0') >>= \case
    (VLam x _ a t, VLam _ _ _ t')            -> goBind x a t t'
    (VLam x i a t, t')                       -> goBind x a t \ v -> evalApp i t' v
    (t, VLam x' i' a' t')                    -> goBind x' a' (\ v -> evalApp i' t v) t'
    (VPi x i q a b, VPi _ i' q' a' b') | i == i' -> qtyEq q q' >> go a a' >> goBind x a b b'
    (VU, VU)                                 -> pure ()
#ifdef FCIF
    (VTel, VTel)                             -> pure ()
    (VRec a, VRec a')                        -> go a a'
    (VTNil, VTNil)                           -> pure ()
    (VTCons x q a b, VTCons _ q' a' b')      -> qtyEq q q' >> go a a' >> goBind x a b b'
    (VTnil, VTnil)                           -> pure ()
    (VTcons t u, VTcons t' u')               -> go t t' >> go u u'
    (VPiTel x q a b, VPiTel _ q' a' b')      -> qtyEq q q' >> go a a' >> goBind x (VRec a) b b'
    -- TODO: invalid?
    (VLamTel x a t, VLamTel _  _ t')         -> goBind x (VRec a) t t'
    (VLamTel x a t, t')                      -> goBind x (VRec a) t (evalAppTel a t')
    (t, VLamTel x' a' t')                    -> goBind x' (VRec a') (evalAppTel a' t) t'
#endif
    (VNe h sp, VNe h' sp') | h == h'         -> do
      fsp <- forceSp sp 
      fsp' <- forceSp sp'
      goSp fsp fsp'
    (VNe (HMeta m) sp, VNe (HMeta m') sp')   -> flexFlex m sp m' sp'
    (VNe (HMeta m) sp, t')                   -> solveMeta cxt m sp t'
    (t, VNe (HMeta m') sp')                  -> solveMeta cxt m' sp' t
#ifdef FCIF
    (VPiTel x q a b, t@(VPi x' Implicit q' a' b')) -> do
      ia <- implArity cxt b
      ib <- implArity cxt b'
      if ia <= ib then do
        let cxt' = bindSrc x' a' cxt
        vm <- do
          (_,m) <- freshMeta cxt' VTel
          eval (cxt'^.vals) m
        go a $ VTCons x' (mulQty q q') a' $ liftVal cxt vm
        let b2 ~x1 ~x2 = b (VTcons x1 x2)
        newConstancy cxt' vm $ b2 $ VVar (cxt^.len)
        goBind x' a' 
          (\ ~x1 -> unsafeInterleaveIO (liftVal cxt vm x1) <&> \t' -> VPiTel x q t' (b2 x1)) b'
      else do
        go a VTNil
        r' <- b VTnil
        go r' t
    (t@(VPi x' Implicit q' a' b'), VPiTel x q a b) -> do
      ia <- implArity cxt b
      ib <- implArity cxt b'
      if ia <= ib then do
        let cxt' = bindSrc x' a' cxt
        vm <- do
          (_,m) <- freshMeta cxt' VTel
          eval (cxt'^.vals) m
        go a $ VTCons x' (mulQty q q') a' $ liftVal cxt vm
        let b2 ~x1 ~x2 = b (VTcons x1 x2)
        newConstancy cxt' vm $ b2 $ VVar (cxt^.len)
        goBind x' a' b' \ ~x1 -> unsafeInterleaveIO (liftVal cxt vm x1) <&> \t' -> VPiTel x q t' (b2 x1)
      else do
        go a VTNil
        r' <- b VTnil
        go t r'
    -- TODO: set q = zero?
    (VPiTel _ q a b, t) -> do
      go a VTNil
      r' <- b VTnil
      go r' t
    (t, VPiTel _ q a b) -> do
      go a VTNil
      r' <- b VTnil
      go t r'
#endif
    _ -> unifyError

  goBind x a t t' = do
    let v = VVar (cxt^.len)
    u <- unsafeInterleaveIO $ t v
    u' <- unsafeInterleaveIO $ t' v
    unify (bindSrc x a cxt) u u'

  goSp sp0 sp0' = case (sp0, sp0') of
    (SNil, SNil) -> pure ()
    (SApp i sp u, SApp i' sp' u') | i == i' -> goSp sp sp' >> go u u'
#ifdef FCIF
    (SAppTel _ sp u, SAppTel _ sp' u')      -> goSp sp sp' >> go u u'
#endif
    _ -> panic


-- needs to work on values since it nees to infer the lhs of applications
-- 
-- m = demand/multiplier
-- possible optimization: checkQtys (use in solveMeta, instead of inferQtys & constrain le)
-- takes avail qtys, splits qtys into needed for value & left over (returned)
-- tl needs to match ctx len in Val (for HVar)
inferQtys :: Types -> Int -> Qty -> Val -> IO Qtys
inferQtys tys !tl m = \case
  VNe h spi -> snd <$> go spi where
    go :: Spine -> IO (VTy, Qtys)
    go SNil = case h of
      HMeta mv -> do
        Unsolved _ ty <- readMeta mv
        pure (ty, mempty)
      HVar v -> pure $ f tys (tl - v - 1) where
        f :: Types -> Int -> (VTy, Qtys)
        f (TySnoc _ _ t) 0 = (t, Qtys [m])
        f (TySnoc ts _ _) !i = let (x,y) = f ts (i-1) in (x,wknQtys y)
        f _ _ = panic
    go (SApp _ sp x) = go sp >>= \case
      (VPi _ _ q _ b, qs) -> do
        y <- b x
        z <- inferQtys tys tl (mulQty q m) x
        pure (y, z <> qs)
      _ -> panic
    go (SAppTel _ sp x) = go sp >>= \case
      (VPiTel _ q _ b, qs) -> do
        y <- b x
        z <- inferQtys tys tl (mulQty q m) x
        pure (y, z <> qs)
      _ -> panic
    go (SCar sp) = go sp >>= \case
      (VTCons _ q a _, qs) -> do
        undefined
      _ -> panic
    go (SCdr s) = panic
  VPi _ _ _ x y -> do
    y' <- y (VVar tl)
    (<>) <$> inferQtys tys tl m x <*> (tailQtys <$> inferQtys (TySnoc tys Bound x) (tl+1) m y')
  VLam _ _ x y -> do
    y' <- y (VVar tl)
    tailQtys <$> inferQtys (TySnoc tys Bound x) (tl+1) m y'
  VU -> pure mempty
  VTel -> pure mempty
  VRec v -> _
  VTNil -> pure mempty
  VTCons _ q x y -> _
  VTnil -> pure mempty
  VTcons x y -> _
  VPiTel _ q x b -> _
  VLamTel _ x b -> _



