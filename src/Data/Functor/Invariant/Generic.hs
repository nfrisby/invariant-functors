{-# LANGUAGE CPP #-}
#if __GLASGOW_HASKELL__ >= 702
{-# LANGUAGE FlexibleContexts #-}
#endif

{-|
Module:      Data.Functor.Invariant.Generic
Copyright:   (C) 2012-2015 Nicolas Frisby, (C) 2015 Ryan Scott
License:     BSD-style (see the file LICENSE)
Maintainer:  Ryan Scott
Portability: Portable

Exports 'genericInvmap' on GHC 7.2 or later.

-}
module Data.Functor.Invariant.Generic (
#if __GLASGOW_HASKELL__ < 702
    ) where
#else
      -- ** @GHC.Generics@
      -- $ghcgenerics
      genericInvmap
    ) where

import Data.Functor.Invariant
import GHC.Generics

{- $ghcgenerics
With GHC 7.2 or later, 'Invariant' instances can be defined easily using GHC
generics like so:

@
&#123;-&#35; LANGUAGE DeriveGeneric, FlexibleContexts &#35;-&#125;

import Data.Functor.Invariant
import GHC.Generics

data T f a = T (f a) deriving Generic1

instance Invariant f => 'Invariant' (T f) where
  invmap = genericInvmap
@

Be aware that generic 'Invariant' instances cannot be derived for data types
that have function arguments in which the last type parameter appears in a
position other than the result type (e.g., @data Fun a = Fun (a -> a)@). For
these, you can derive them using the "Data.Functor.Invariant.TH" module.
-}

-- | A generic implementation of 'invmap'.
genericInvmap :: (Generic1 f, Invariant (Rep1 f)) => (a -> b) -> (b -> a) -> f a -> f b
genericInvmap f g = to1 . invmap f g . from1
#endif
