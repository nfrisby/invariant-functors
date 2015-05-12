module Data.Functor.Invariant (Invariant(..), Invariant2(..)) where

import Text.ParserCombinators.ReadP (ReadP)
import Text.ParserCombinators.ReadPrec (ReadPrec)

import qualified Control.Category as Cat
import Control.Arrow (Arrow(..))
import Control.Applicative (Const(Const), ZipList)
import Control.Applicative (WrappedMonad, WrappedArrow(WrapArrow))

import Control.Monad.ST (ST)

import Data.Functor.Contravariant
import Data.Functor.Contravariant.Compose
import Data.Monoid (Endo(Endo))




-- | Any @*->*@ type parametric in the argument permits an instance of
-- @Invariant@.
--
-- Instances should satisfy the following laws:
--
-- > invmap id id = id
-- > invmap f2 f2' . invmap f1 f1' = invmap (f2 . f1) (f1' . f2')
class Invariant f where
  invmap :: (a -> b) -> (b -> a) -> f a -> f b





-- | Any @*->*->*@ type parametric in both arguments permits an instance of
-- @Invariant2@.
--
-- Instances should satisfy the following laws:
--
-- > invmap2 id id id id = id
-- > invmap2 f2 f2' g2 g2' . invmap2 f1 f1' g1 g1' =
-- >   invmap2 (f2 . f1) (f1' . f2') (g2 . g1) (g1' . g2')
class Invariant2 f where
  invmap2 :: (a -> c) -> (c -> a) -> (b -> d) -> (d -> b) -> f a b -> f c d





instance Invariant Maybe where invmap = flip $ const fmap
instance Invariant [] where invmap = flip $ const fmap
instance Invariant IO where invmap = flip $ const fmap
instance Invariant (ST s) where invmap = flip $ const fmap
instance Invariant ReadP where invmap = flip $ const fmap
instance Invariant ReadPrec where invmap = flip $ const fmap
instance Invariant ((->) a) where invmap = flip $ const fmap
instance Invariant (Either a) where invmap = flip $ const fmap
instance Invariant ((,) a) where invmap = flip $ const fmap
instance Invariant ((,,) a b) where invmap f _ ~(a, b, x) = (a, b, f x)
instance Invariant ((,,,) a b c) where
  invmap f _ ~(a, b, c, x) = (a, b, c, f x)
instance Invariant ((,,,,) a b c d) where
  invmap f _ ~(a, b, c, d, x) = (a, b, c, d, f x)

instance Invariant2 (->) where invmap2 _ f' g _ = (g .) . (. f')
instance Invariant2 Either where
  invmap2 f _ _ _ (Left  x) = Left  $ f x
  invmap2 _ _ g _ (Right y) = Right $ g y
instance Invariant2 (,) where invmap2 f _ g _ ~(x, y) = (f x, g y)
instance Invariant2 ((,,) a) where invmap2 f _ g _ ~(a, x, y) = (a, f x, g y)
instance Invariant2 ((,,,) a b) where
  invmap2 f _ g _ ~(a, b, x, y) = (a, b, f x, g y)
instance Invariant2 ((,,,,) a b c) where
  invmap2 f _ g _ ~(a, b, c, x, y) = (a, b, c, f x, g y)





-- | @Control.Applicative@
instance Invariant (Const a) where invmap _ _ (Const x) = Const x
-- | @Control.Applicative@
instance Invariant ZipList where invmap = flip $ const fmap
-- | @Control.Applicative@
instance Monad m => Invariant (WrappedMonad m) where invmap = flip $ const fmap
-- | @Control.Applicative@
instance Arrow arr => Invariant (WrappedArrow arr a) where
  invmap f _ (WrapArrow x) = WrapArrow $ ((arr f) Cat.. x)
-- | @Control.Applicative@
instance Invariant2 Const where invmap2 f _ _ _ (Const x) = Const (f x)
-- | @Control.Applicative@
instance Arrow arr => Invariant2 (WrappedArrow arr) where
  invmap2 _ f' g _ (WrapArrow x) = WrapArrow $ arr g Cat.. x Cat.. arr f'

-- | @Data.Monoid@
instance Invariant Endo where
  invmap f g (Endo x) = Endo (f . x . g)


-- | from the @contravariant@ package
instance Invariant Predicate where invmap = const contramap
-- | from the @contravariant@ package
instance Invariant Comparison where invmap = const contramap
-- | from the @contravariant@ package
instance Invariant Equivalence where invmap = const contramap
-- | from the @contravariant@ package
instance Invariant (Op a) where invmap = const contramap
-- | from the @contravariant@ package
instance Invariant2 Op where
  invmap2 f f' g g' (Op x) = Op $ invmap2 g g' f f' x





-- | from the @contravariant@ package
instance (Invariant f, Invariant g) => Invariant (Compose f g) where
  invmap f g (Compose x) = Compose $ invmap (invmap f g) (invmap g f) x
-- | from the @contravariant@ package
instance (Invariant f, Invariant g) => Invariant (ComposeCF f g) where
  invmap f g (ComposeCF x) = ComposeCF $ invmap (invmap f g) (invmap g f) x
-- | from the @contravariant@ package
instance (Invariant f, Invariant g) => Invariant (ComposeFC f g) where
  invmap f g (ComposeFC x) = ComposeFC $ invmap (invmap f g) (invmap g f) x
