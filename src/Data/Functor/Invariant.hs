{-|
Module:      Data.Functor.Invariant
Copyright:   (C) 2012-2015 Nicolas Frisby, (C) 2015 Ryan Scott
License:     BSD-style (see the file LICENSE)
Maintainer:  Ryan Scott
Portability: Portable

Haskell98 invariant functors (also known as exponential functors).

For more information, see Edward Kmett's article \"Rotten Bananas\":

<http://comonad.com/reader/2008/rotten-bananas/>
-}
module Data.Functor.Invariant
  ( -- * @Invariant@
    Invariant(..)
  , invmapFunctor
  , WrappedFunctor(..)
  , invmapContravariant
  , WrappedContravariant(..)
    -- * @Invariant2@
  , Invariant2(..)
  , invmap2Bifunctor
  , WrappedBifunctor(..)
  , invmap2Profunctor
  , WrappedProfunctor(..)
  ) where

import Text.ParserCombinators.ReadP (ReadP)
import Text.ParserCombinators.ReadPrec (ReadPrec)

import qualified Control.Category as Cat
import Control.Arrow
import Control.Applicative as App
import Control.Monad (MonadPlus(..))
import Control.Monad.ST (ST)

import Data.Bifunctor hiding (first)
import Data.Bifunctor.Biff
import Data.Bifunctor.Clown
import Data.Bifunctor.Flip
import Data.Bifunctor.Join
import Data.Bifunctor.Joker
import Data.Bifunctor.Product
import Data.Bifunctor.Tannen
import Data.Bifunctor.Wrapped

import Data.Functor.Contravariant
import Data.Functor.Contravariant.Compose
import Data.Functor.Contravariant.Divisible

import Data.Monoid (Dual(Dual), Endo(Endo))

import Data.Profunctor as Pro
import Data.Profunctor.Cayley
import Data.Profunctor.Closed
import Data.Profunctor.Codensity
import Data.Profunctor.Composition
import Data.Profunctor.Ran
import Data.Profunctor.Tambara

-------------------------------------------------------------------------------
-- The Invariant class
-------------------------------------------------------------------------------

-- | Any @* -> *@ type parametric in the argument permits an instance of
-- @Invariant@.
--
-- Instances should satisfy the following laws:
--
-- > invmap id id = id
-- > invmap f2 f2' . invmap f1 f1' = invmap (f2 . f1) (f1' . f2')
class Invariant f where
  invmap :: (a -> b) -> (b -> a) -> f a -> f b

-- | Every 'Functor' is also an 'Invariant' functor.
invmapFunctor :: Functor f => (a -> b) -> (b -> a) -> f a -> f b
invmapFunctor = flip $ const fmap

-- | Every 'Contravariant' functor is also an 'Invariant' functor.
invmapContravariant :: Contravariant f => (a -> b) -> (b -> a) -> f a -> f b
invmapContravariant = const contramap

-------------------------------------------------------------------------------
-- Invariant instances
-------------------------------------------------------------------------------

instance Invariant Maybe where invmap = invmapFunctor
instance Invariant [] where invmap = invmapFunctor
instance Invariant IO where invmap = invmapFunctor
instance Invariant (ST s) where invmap = invmapFunctor
instance Invariant ReadP where invmap = invmapFunctor
instance Invariant ReadPrec where invmap = invmapFunctor
instance Invariant ((->) a) where invmap = invmapFunctor
instance Invariant (Either a) where invmap = invmapFunctor
instance Invariant ((,) a) where invmap = invmapFunctor
instance Invariant ((,,) a b) where invmap f _ ~(a, b, x) = (a, b, f x)
instance Invariant ((,,,) a b c) where
  invmap f _ ~(a, b, c, x) = (a, b, c, f x)
instance Invariant ((,,,,) a b c d) where
  invmap f _ ~(a, b, c, d, x) = (a, b, c, d, f x)

-- | @Control.Applicative@
instance Invariant (Const a) where invmap = invmapFunctor
-- | @Control.Applicative@
instance Invariant ZipList where invmap = invmapFunctor
-- | @Control.Applicative@
instance Monad m => Invariant (WrappedMonad m) where invmap = invmapFunctor
-- | @Control.Applicative@
instance Arrow arr => Invariant (App.WrappedArrow arr a) where
  invmap f _ (App.WrapArrow x) = App.WrapArrow $ ((arr f) Cat.. x)

-- | @Data.Monoid@
instance Invariant Dual where invmap f _ (Dual x) = Dual (f x)
-- | @Data.Monoid@
instance Invariant Endo where
  invmap f g (Endo x) = Endo (f . x . g)

-- | from the @bifunctors@ package
instance (Invariant2 p, Invariant g) => Invariant (Biff p f g a) where
  invmap f g = Biff . invmap2 id id (invmap f g) (invmap g f) . runBiff
-- | from the @bifunctors@ package
instance Invariant (Clown f a) where
  invmap = invmapFunctor
-- | from the @bifunctors@ package
instance Invariant2 p => Invariant (Flip p a) where
  invmap = invmap2 id id
-- | from the @bifunctors@ package
instance Invariant2 p => Invariant (Join p) where
  invmap f g = Join . invmap2 f g f g . runJoin
-- | from the @bifunctors@ package
instance Invariant g => Invariant (Joker g a) where
  invmap = invmap2 id id
-- | from the @bifunctors@ package
instance (Invariant f, Invariant2 p) => Invariant (Tannen f p a) where
  invmap = invmap2 id id
-- | from the @bifunctors@ package
instance Bifunctor p => Invariant (WrappedBifunctor p a) where
  invmap = invmap2 id id

-- | from the @contravariant@ package
instance Invariant Predicate where invmap = invmapContravariant
-- | from the @contravariant@ package
instance Invariant Comparison where invmap = invmapContravariant
-- | from the @contravariant@ package
instance Invariant Equivalence where invmap = invmapContravariant
-- | from the @contravariant@ package
instance Invariant (Op a) where invmap = invmapContravariant
-- | from the @contravariant@ package
instance (Invariant f, Invariant g) => Invariant (Compose f g) where
  invmap f g (Compose x) = Compose $ invmap (invmap f g) (invmap g f) x
-- | from the @contravariant@ package
instance (Invariant f, Invariant g) => Invariant (ComposeCF f g) where
  invmap f g (ComposeCF x) = ComposeCF $ invmap (invmap f g) (invmap g f) x
-- | from the @contravariant@ package
instance (Invariant f, Invariant g) => Invariant (ComposeFC f g) where
  invmap f g (ComposeFC x) = ComposeFC $ invmap (invmap f g) (invmap g f) x

-- | from the @profunctors@ package
instance Invariant f => Invariant (Star f a) where
  invmap = invmap2 id id
-- | from the @profunctors@ package
instance Invariant (Costar f a) where
  invmap = invmapFunctor
-- | from the @profunctors@ package
instance Arrow arr => Invariant (Pro.WrappedArrow arr a) where
  invmap f _ (Pro.WrapArrow x) = Pro.WrapArrow $ ((arr f) Cat.. x)
-- | from the @profunctors@ package
instance Invariant (Forget r a) where
  invmap = invmapFunctor
-- | from the @profunctors@ package
instance Invariant2 p => Invariant (Closure p a) where
  invmap = invmap2 id id
-- | from the @profunctors@ package
instance Invariant2 p => Invariant (Codensity p a) where
  invmap = invmap2 id id
-- | from the @profunctors@ package
instance Invariant2 p => Invariant (Procompose p q a) where
  invmap k k' (Procompose f g) = Procompose (invmap2 id id k k' f) g
-- | from the @profunctors@ package
instance Invariant2 p => Invariant (Rift p q a) where
  invmap bd db (Rift f) = Rift (f . invmap2 db bd id id)
-- | from the @profunctors@ package
instance Invariant2 q => Invariant (Ran p q a) where
  invmap bd db (Ran f) = Ran (invmap2 id id bd db . f)
-- | from the @profunctors@ package
instance Invariant2 p => Invariant (Tambara p a) where
  invmap = invmap2 id id
-- | from the @profunctors@ package
instance Invariant2 p => Invariant (Cotambara p a) where
  invmap = invmap2 id id

-------------------------------------------------------------------------------
-- WrappedFunctor
-------------------------------------------------------------------------------

-- | Wrap a 'Functor' to be used as a member of 'Invariant'.
newtype WrappedFunctor f a = WrapFunctor { unwrapFunctor :: f a }
  deriving (Eq, Ord, Read, Show)

instance Functor f => Invariant (WrappedFunctor f) where
  invmap f g = WrapFunctor . invmapFunctor f g . unwrapFunctor

instance Functor f => Functor (WrappedFunctor f) where
  fmap f = WrapFunctor . fmap f . unwrapFunctor

instance Applicative f => Applicative (WrappedFunctor f) where
  pure = WrapFunctor . pure
  WrapFunctor f <*> WrapFunctor x = WrapFunctor $ f <*> x

instance Alternative f => Alternative (WrappedFunctor f) where
  empty = WrapFunctor empty
  WrapFunctor x <|> WrapFunctor y = WrapFunctor $ x <|> y

instance Monad m => Monad (WrappedFunctor m) where
  return = WrapFunctor . return
  WrapFunctor x >>= f = WrapFunctor $ x >>= unwrapFunctor . f

instance MonadPlus m => MonadPlus (WrappedFunctor m) where
  mzero = WrapFunctor mzero
  WrapFunctor x `mplus` WrapFunctor y = WrapFunctor $ x `mplus` y

-------------------------------------------------------------------------------
-- WrappedContravariant
-------------------------------------------------------------------------------

-- | Wrap a 'Contravariant' functor to be used as a member of 'Invariant'.
newtype WrappedContravariant f a = WrapContravariant { unwrapContravariant :: f a }
  deriving (Eq, Ord, Read, Show)

instance Contravariant f => Invariant (WrappedContravariant f) where
  invmap f g = WrapContravariant . invmapContravariant f g . unwrapContravariant

instance Contravariant f => Contravariant (WrappedContravariant f) where
  contramap f = WrapContravariant . contramap f . unwrapContravariant

instance Divisible f => Divisible (WrappedContravariant f) where
  divide f (WrapContravariant l) (WrapContravariant r) = WrapContravariant $ divide f l r
  conquer = WrapContravariant conquer

instance Decidable f => Decidable (WrappedContravariant f) where
  lose = WrapContravariant . lose
  choose f (WrapContravariant l) (WrapContravariant r) = WrapContravariant $ choose f l r

-------------------------------------------------------------------------------
-- The Invariant2 class
-------------------------------------------------------------------------------

-- | Any @* -> * -> *@ type parametric in both arguments permits an instance of
-- @Invariant2@.
--
-- Instances should satisfy the following laws:
--
-- > invmap2 id id id id = id
-- > invmap2 f2 f2' g2 g2' . invmap2 f1 f1' g1 g1' =
-- >   invmap2 (f2 . f1) (f1' . f2') (g2 . g1) (g1' . g2')
class Invariant2 f where
  invmap2 :: (a -> c) -> (c -> a) -> (b -> d) -> (d -> b) -> f a b -> f c d

-- | Every 'Bifunctor' is also an 'Invariant2' functor.
invmap2Bifunctor :: Bifunctor f
                 => (a -> c) -> (c -> a)
                 -> (b -> d) -> (d -> b)
                 -> f a b    -> f c d
invmap2Bifunctor f _ g _ = bimap f g

-- | Every 'Profunctor' is also an 'Invariant2' functor.
invmap2Profunctor :: Profunctor f
                  => (a -> c) -> (c -> a)
                  -> (b -> d) -> (d -> b)
                  -> f a b    -> f c d
invmap2Profunctor _ f' g _ = dimap f' g

-------------------------------------------------------------------------------
-- Invariant2 instances
-------------------------------------------------------------------------------

instance Invariant2 (->) where invmap2 = invmap2Profunctor
instance Invariant2 Either where invmap2 = invmap2Bifunctor
instance Invariant2 (,) where invmap2 f _ g _ ~(x, y) = (f x, g y)
instance Invariant2 ((,,) a) where invmap2 f _ g _ ~(a, x, y) = (a, f x, g y)
instance Invariant2 ((,,,) a b) where
  invmap2 f _ g _ ~(a, b, x, y) = (a, b, f x, g y)
instance Invariant2 ((,,,,) a b c) where
  invmap2 f _ g _ ~(a, b, c, x, y) = (a, b, c, f x, g y)

-- | @Control.Applicative@
instance Invariant2 Const where invmap2 = invmap2Bifunctor
-- | @Control.Applicative@
instance Arrow arr => Invariant2 (App.WrappedArrow arr) where
  invmap2 _ f' g _ (App.WrapArrow x) = App.WrapArrow $ arr g Cat.. x Cat.. arr f'

-- | from the @bifunctors@ package
instance (Invariant2 p, Invariant f, Invariant g) => Invariant2 (Biff p f g) where
  invmap2 f f' g g' = Biff . invmap2 (invmap f f') (invmap f' f) (invmap g g') (invmap g' g) . runBiff
-- | from the @bifunctors@ package
instance Invariant f => Invariant2 (Clown f) where
  invmap2 f f' _ _ = Clown . invmap f f' . runClown
-- | from the @bifunctors@ package
instance Invariant2 p => Invariant2 (Flip p) where
  invmap2 f f' g g' = Flip . invmap2 g g' f f' . runFlip
-- | from the @bifunctors@ package
instance Invariant g => Invariant2 (Joker g) where
  invmap2 _ _ g g' = Joker . invmap g g' . runJoker
-- | from the @bifunctors@ package
instance (Invariant2 f, Invariant2 g) => Invariant2 (Product f g) where
  invmap2 f f' g g' (Pair x y) = Pair (invmap2 f f' g g' x) (invmap2 f f' g g' y)
-- | from the @bifunctors@ package
instance (Invariant f, Invariant2 p) => Invariant2 (Tannen f p) where
  invmap2 f f' g g' = Tannen . invmap (invmap2 f f' g g') (invmap2 f' f g' g) . runTannen
-- | from the @bifunctors@ package
instance Bifunctor p => Invariant2 (WrappedBifunctor p) where
  invmap2 f f' g g' = WrapBifunctor . invmap2Bifunctor f f' g g' . unwrapBifunctor

-- | from the @contravariant@ package
instance Invariant2 Op where
  invmap2 f f' g g' (Op x) = Op $ invmap2 g g' f f' x

-- | from the @profunctors@ package
instance Invariant f => Invariant2 (Star f) where
  invmap2 _ ba cd dc (Star afc) = Star $ invmap cd dc . afc . ba
-- | from the @profunctors@ package
instance Invariant f => Invariant2 (Costar f) where
  invmap2 ab ba cd _ (Costar fbc) = Costar $ cd . fbc . invmap ba ab
-- | from the @profunctors@ package
instance Arrow arr => Invariant2 (Pro.WrappedArrow arr) where
  invmap2 _ f' g _ (Pro.WrapArrow x) = Pro.WrapArrow $ arr g Cat.. x Cat.. arr f'
-- | from the @profunctors@ package
instance Invariant2 (Forget r) where
  invmap2 = invmap2Profunctor
-- | from the @profunctors@ package
instance (Invariant f, Invariant2 p) => Invariant2 (Cayley f p) where
  invmap2 f f' g g' = Cayley . invmap (invmap2 f f' g g') (invmap2 f' f g' g) . runCayley
-- | from the @profunctors@ package
instance Invariant2 p => Invariant2 (Closure p) where
  invmap2 f f' g g' (Closure p) = Closure $ invmap2 (f .) (f' .) (g .) (g' .) p
-- | from the @profunctors@ package
instance Invariant2 (Environment p) where
  invmap2 _ f' g _ (Environment l m r) = Environment (g . l) m (r . f')
-- | from the @profunctors@ package
instance Invariant2 p => Invariant2 (Codensity p) where
  invmap2 ac ca bd db (Codensity f) = Codensity (invmap2 id id bd db . f . invmap2 id id ca ac)
-- | from the @profunctors@ package
instance (Invariant2 p, Invariant2 q) => Invariant2 (Procompose p q) where
  invmap2 l l' r r' (Procompose f g) = Procompose (invmap2 id id r r' f) (invmap2 l l' id id g)
-- | from the @profunctors@ package
instance (Invariant2 p, Invariant2 q) => Invariant2 (Rift p q) where
  invmap2 ac ca bd db (Rift f) = Rift (invmap2 ac ca id id . f . invmap2 db bd id id)
-- | from the @profunctors@ package
instance (Invariant2 p, Invariant2 q) => Invariant2 (Ran p q) where
  invmap2 ac ca bd db (Ran f) = Ran (invmap2 id id bd db . f . invmap2 id id ca ac)
-- | from the @profunctors@ package
instance Invariant2 p => Invariant2 (Tambara p) where
  invmap2 f f' g g' (Tambara p) = Tambara $ invmap2 (first f) (first f') (first g) (first g') p
-- | from the @profunctors@ package
instance Invariant2 (Pastro p) where
  invmap2 _ f' g _ (Pastro l m r) = Pastro (g . l) m (r . f')
-- | from the @profunctors@ package
instance Invariant2 p => Invariant2 (Cotambara p) where
  invmap2 f f' g g' (Cotambara p) = Cotambara $ invmap2 (left f) (left f') (left g) (left g') p
-- | from the @profunctors@ package
instance Invariant2 (Copastro p) where
  invmap2 _ f' g _ (Copastro l m r) = Copastro (g . l) m (r . f')

-------------------------------------------------------------------------------
-- WrappedProfunctor
-------------------------------------------------------------------------------

-- | Wrap a 'Profunctor' to be used as a member of 'Invariant2'.
newtype WrappedProfunctor p a b = WrapProfunctor { unwrapProfunctor :: p a b }
  deriving (Eq, Ord, Read, Show)

instance Profunctor p => Invariant2 (WrappedProfunctor p) where
  invmap2 f f' g g' = WrapProfunctor . invmap2Profunctor f f' g g' . unwrapProfunctor

instance Profunctor p => Invariant (WrappedProfunctor p a) where
  invmap = invmap2 id id

instance Profunctor p => Profunctor (WrappedProfunctor p) where
  dimap f g = WrapProfunctor . dimap f g . unwrapProfunctor

instance Strong p => Strong (WrappedProfunctor p) where
  first'  = WrapProfunctor . first'  . unwrapProfunctor
  second' = WrapProfunctor . second' . unwrapProfunctor

instance Choice p => Choice (WrappedProfunctor p) where
  left'  = WrapProfunctor . left'  . unwrapProfunctor
  right' = WrapProfunctor . right' . unwrapProfunctor

instance Costrong p => Costrong (WrappedProfunctor p) where
  unfirst  = WrapProfunctor . unfirst  . unwrapProfunctor
  unsecond = WrapProfunctor . unsecond . unwrapProfunctor

instance Cochoice p => Cochoice (WrappedProfunctor p) where
  unleft  = WrapProfunctor . unleft  . unwrapProfunctor
  unright = WrapProfunctor . unright . unwrapProfunctor

instance Closed p => Closed (WrappedProfunctor p) where
  closed = WrapProfunctor . closed . unwrapProfunctor
