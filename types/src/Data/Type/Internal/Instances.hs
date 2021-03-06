{-# language PatternSynonyms #-}
{-# language ExplicitNamespaces #-}
{-# language TemplateHaskell #-}
{-# language StandaloneKindSignatures #-}
{-# language TypeOperators #-}
{-# language FlexibleInstances #-}
{-# language DataKinds #-}
{-# language PolyKinds #-}
{-# language RoleAnnotations #-}
{-# language ViewPatterns #-}
{-# language UndecidableInstances #-}
{-# language GADTs #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_HADDOCK not-home #-}

-- |
-- Copyright :  (c) Edward Kmett 2020
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable

module Data.Type.Internal.Instances where

import Control.Applicative
import Data.Functor.Identity
import Data.Functor.Compose
import Data.List.NonEmpty
import Data.Proxy
import Data.Type.Internal.TH
import Data.Type.Equality

makeSing ''Either
makeSing ''Maybe
makeSing ''Bool
makeSing ''Ordering
makeSing ''Const
makeSing ''Compose
makeSing ''Identity
makeSing ''Proxy
makeSing ''[]
makeSing ''NonEmpty
makeSing ''()
makeSing ''(,)
makeSing ''(,,)
makeSing ''(,,,)
makeSing ''(,,,,)
makeSing ''(,,,,,)
makeSing ''(,,,,,,)
makeSing ''(,,,,,,,)
makeSing ''(,,,,,,,,)
makeSing ''(:~:)
makeSing ''(:~~:)
