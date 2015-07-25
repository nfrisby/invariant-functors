{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -fno-warn-deprecations #-}

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

-- base
import qualified Control.Category as Cat
import           Control.Arrow
import           Control.Applicative as App
import           Control.Exception (Handler(..))
import           Control.Monad (MonadPlus(..))
import qualified Control.Monad.ST as Strict (ST)
import qualified Control.Monad.ST.Lazy as Lazy (ST)
import           Data.Functor.Identity (Identity)
import           Data.Ix (Ix)
import qualified Data.Monoid as Monoid (First(..), Last(..))
#if MIN_VERSION_base(4,8,0)
import           Data.Monoid (Alt(..))
#endif
import           Data.Monoid (Dual(..), Endo(..))
import           Data.Proxy (Proxy(..))
import           System.Console.GetOpt as GetOpt
import           Text.ParserCombinators.ReadP (ReadP)
import           Text.ParserCombinators.ReadPrec (ReadPrec)

-- array
import           Data.Array (Array)

-- bifunctors
import           Data.Bifunctor hiding (first)
import           Data.Bifunctor.Biff
import           Data.Bifunctor.Clown
import           Data.Bifunctor.Flip
import           Data.Bifunctor.Join
import           Data.Bifunctor.Joker
import qualified Data.Bifunctor.Product as Bifunctors
import           Data.Bifunctor.Tannen
import           Data.Bifunctor.Wrapped

-- containers
import           Data.IntMap (IntMap)
import           Data.Map (Map)
import           Data.Sequence (Seq, ViewL, ViewR)
import           Data.Tree (Tree)

-- contravariant
import           Data.Functor.Contravariant
import           Data.Functor.Contravariant.Compose as Contravariant
import           Data.Functor.Contravariant.Divisible

-- profunctors
import           Data.Profunctor as Pro
import           Data.Profunctor.Cayley
import           Data.Profunctor.Closed
import           Data.Profunctor.Codensity
import           Data.Profunctor.Composition
import           Data.Profunctor.Ran
import           Data.Profunctor.Tambara

-- semigroups
import           Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Semigroup as Semigroup (First(..), Last(..), Option(..))
import           Data.Semigroup (Min(..), Max(..), Arg(..))

-- stm
import           Control.Concurrent.STM (STM)

-- tagged
import           Data.Tagged (Tagged(..))

-- transformers
import           Control.Applicative.Backwards (Backwards(..))
import           Control.Applicative.Lift (Lift(..))
import           Control.Monad.Trans.Cont (ContT)
import           Control.Monad.Trans.Error (ErrorT(..))
import           Control.Monad.Trans.Except (ExceptT(..), runExceptT)
import           Control.Monad.Trans.Identity (IdentityT, mapIdentityT)
import           Control.Monad.Trans.List (ListT, mapListT)
import           Control.Monad.Trans.Maybe (MaybeT, mapMaybeT)
import qualified Control.Monad.Trans.RWS.Lazy as Lazy (RWST(..))
import qualified Control.Monad.Trans.RWS.Strict as Strict (RWST(..))
import           Control.Monad.Trans.Reader (ReaderT, mapReaderT)
import qualified Control.Monad.Trans.State.Lazy as Lazy (StateT(..))
import qualified Control.Monad.Trans.State.Strict as Strict (StateT(..))
import qualified Control.Monad.Trans.Writer.Lazy as Lazy (WriterT, mapWriterT)
import qualified Control.Monad.Trans.Writer.Strict as Strict (WriterT, mapWriterT)
import qualified Data.Functor.Compose as Transformers (Compose(..))
import           Data.Functor.Constant (Constant(..))
import           Data.Functor.Product as Transformers (Product(..))
import           Data.Functor.Reverse (Reverse(..))
import           Data.Functor.Sum as Transformers (Sum(..))

-- unordered-containers
import           Data.HashMap.Lazy (HashMap)

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
instance Invariant (Strict.ST s) where invmap = invmapFunctor
instance Invariant (Lazy.ST s) where invmap = invmapFunctor
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

-- | @Control.Arrow@
instance
#if MIN_VERSION_base(4,4,0)
  Arrow a
#else
  ArrowApply a
#endif
  => Invariant (ArrowMonad a) where
  invmap f _ (ArrowMonad m) = ArrowMonad $ m >>> arr f

-- | @Control.Exception@
instance Invariant Handler where
  invmap f _ (Handler h) = Handler (fmap f . h)

-- | @Data.Functor.Identity@
instance Invariant Identity where
  invmap = invmapFunctor

-- | @Data.Monoid@
instance Invariant Dual where invmap f _ (Dual x) = Dual (f x)
-- | @Data.Monoid@
instance Invariant Endo where
  invmap f g (Endo x) = Endo (f . x . g)
-- | @Data.Monoid@
instance Invariant Monoid.First where
  invmap f g (Monoid.First x) = Monoid.First (invmap f g x)
-- | @Data.Monoid@
instance Invariant Monoid.Last where
  invmap f g (Monoid.Last x) = Monoid.Last (invmap f g x)
#if MIN_VERSION_base(4,8,0)
instance Invariant f => Invariant (Alt f) where
  invmap f g (Alt x) = Alt (invmap f g x)
#endif

-- | @Data.Proxy@
instance Invariant Proxy where
  invmap = invmapFunctor

-- | @System.Console.GetOpt@
instance Invariant ArgDescr where
  invmap f _ (NoArg a)    = NoArg (f a)
  invmap f _ (ReqArg g s) = ReqArg (f . g) s
  invmap f _ (OptArg g s) = OptArg (f . g) s
-- | @System.Console.GetOpt@
instance Invariant ArgOrder where
  invmap _ _ RequireOrder      = RequireOrder
  invmap _ _ Permute           = Permute
  invmap f _ (ReturnInOrder g) = ReturnInOrder (f . g)
-- | @System.Console.GetOpt@
instance Invariant OptDescr where
  invmap f g (GetOpt.Option a b argDescr c) = GetOpt.Option a b (invmap f g argDescr) c

-- | from the @array@ package
instance
#if __GLASGOW_HASKELL__ < 711
  Ix i
#endif
  => Invariant (Array i) where
  invmap = invmapFunctor

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

-- | from the @containers@ package
instance Invariant IntMap where
  invmap = invmapFunctor
-- | from the @containers@ package
instance Invariant (Map k) where
  invmap = invmapFunctor
-- | from the @containers@ package
instance Invariant Seq where
  invmap = invmapFunctor
-- | from the @containers@ package
instance Invariant ViewL where
  invmap = invmapFunctor
-- | from the @containers@ package
instance Invariant ViewR where
  invmap = invmapFunctor
-- | from the @containers@ package
instance Invariant Tree where
  invmap = invmapFunctor

-- | from the @contravariant@ package
instance Invariant Predicate where invmap = invmapContravariant
-- | from the @contravariant@ package
instance Invariant Comparison where invmap = invmapContravariant
-- | from the @contravariant@ package
instance Invariant Equivalence where invmap = invmapContravariant
-- | from the @contravariant@ package
instance Invariant (Op a) where invmap = invmapContravariant
-- | from the @contravariant@ package
instance (Invariant f, Invariant g) => Invariant (Contravariant.Compose f g) where
  invmap f g (Contravariant.Compose x) =
    Contravariant.Compose $ invmap (invmap f g) (invmap g f) x
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

-- | from the @semigroups@ package
instance Invariant NonEmpty where
  invmap = invmapFunctor
-- | from the @semigroups@ package
instance Invariant Min where
  invmap = invmapFunctor
-- | from the @semigroups@ package
instance Invariant Max where
  invmap = invmapFunctor
-- | from the @semigroups@ package
instance Invariant Semigroup.First where
  invmap = invmapFunctor
-- | from the @semigroups@ package
instance Invariant Semigroup.Last where
  invmap = invmapFunctor
-- | from the @semigroups@ package
instance Invariant Semigroup.Option where
  invmap = invmapFunctor
-- | from the @semigroups@ package
instance Invariant (Arg a) where
  invmap = invmapFunctor

-- | from the @stm@ package
instance Invariant STM where
  invmap = invmapFunctor

-- | from the @tagged@ package
instance Invariant (Tagged s) where
  invmap = invmapFunctor

-- | from the @transformers@ package
instance Invariant f => Invariant (Backwards f) where
  invmap f g (Backwards a) = Backwards (invmap f g a)
-- | from the @transformers@ package
instance Invariant f => Invariant (Lift f) where
  invmap f _ (Pure x)  = Pure (f x)
  invmap f g (Other y) = Other (invmap f g y)
-- | from the @transformers@ package
instance Invariant (ContT r m) where
  invmap = invmapFunctor
-- -- | from the @transformers@ package
instance Invariant m => Invariant (ErrorT e m) where
  invmap f g = ErrorT . invmap (invmap f g) (invmap g f) . runErrorT
-- | from the @transformers@ package
instance Invariant m => Invariant (ExceptT e m) where
  invmap f g = ExceptT . invmap (invmap f g) (invmap g f) . runExceptT
-- | from the @transformers@ package
instance Invariant m => Invariant (IdentityT m) where
  invmap f g = mapIdentityT (invmap f g)
-- | from the @transformers@ package
instance Invariant m => Invariant (ListT m) where
  invmap f g = mapListT $ invmap (invmap f g) (invmap g f)
-- | from the @transformers@ package
instance Invariant m => Invariant (MaybeT m) where
  invmap f g = mapMaybeT $ invmap (invmap f g) (invmap g f)
-- | from the @transformers@ package
instance Invariant m => Invariant (Lazy.RWST r w s m) where
  invmap f g m = Lazy.RWST $ \r s ->
    invmap (mapFstTriple f) (mapFstTriple g) $ Lazy.runRWST m r s
      where mapFstTriple h ~(a, s, w) = (h a, s, w)
-- | from the @transformers@ package
instance Invariant m => Invariant (Strict.RWST r w s m) where
  invmap f g m = Strict.RWST $ \r s ->
    invmap (mapFstTriple f) (mapFstTriple g) $ Strict.runRWST m r s
      where mapFstTriple h (a, s, w) = (h a, s, w)
-- | from the @transformers@ package
instance Invariant m => Invariant (ReaderT r m) where
  invmap f g = mapReaderT (invmap f g)
-- | from the @transformers@ package
instance Invariant m => Invariant (Lazy.StateT s m) where
  invmap f g m = Lazy.StateT $ \s ->
    invmap (mapFstPair f) (mapFstPair g) $ Lazy.runStateT m s
      where mapFstPair h ~(a, s) = (h a, s)
-- | from the @transformers@ package
instance Invariant m => Invariant (Strict.StateT s m) where
  invmap f g m = Strict.StateT $ \s ->
    invmap (mapFstPair f) (mapFstPair g) $ Strict.runStateT m s
      where mapFstPair h (a, s) = (h a, s)
-- | from the @transformers@ package
instance Invariant m => Invariant (Lazy.WriterT w m) where
  invmap f g = Lazy.mapWriterT $ invmap (mapFstPair f) (mapFstPair g)
    where mapFstPair h ~(a, w) = (h a, w)
-- | from the @transformers@ package
instance Invariant m => Invariant (Strict.WriterT w m) where
  invmap f g = Strict.mapWriterT $ invmap (mapFstPair f) (mapFstPair g)
    where mapFstPair h (a, w) = (h a, w)
-- | from the @transformers@ package
instance (Invariant f, Invariant g) => Invariant (Transformers.Compose f g) where
  invmap f g (Transformers.Compose x) =
    Transformers.Compose (invmap (invmap f g) (invmap g f) x)
-- | from the @transformers@ package
instance Invariant (Constant a) where
  invmap = invmapFunctor
-- | from the @transformers@ package
instance (Invariant f, Invariant g) => Invariant (Transformers.Product f g) where
  invmap f g (Transformers.Pair x y) = Transformers.Pair (invmap f g x) (invmap f g y)
-- | from the @transformers@ package
instance Invariant f => Invariant (Reverse f) where
  invmap f g (Reverse a) = Reverse (invmap f g a)
-- | from the @transformers@ package
instance (Invariant f, Invariant g) => Invariant (Transformers.Sum f g) where
  invmap f g (InL x) = InL (invmap f g x)
  invmap f g (InR y) = InR (invmap f g y)

-- | from the @unordered-containers@ package
instance Invariant (HashMap k) where
  invmap = invmapFunctor

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
  divide f (WrapContravariant l) (WrapContravariant r) =
    WrapContravariant $ divide f l r
  conquer = WrapContravariant conquer

instance Decidable f => Decidable (WrappedContravariant f) where
  lose = WrapContravariant . lose
  choose f (WrapContravariant l) (WrapContravariant r) =
    WrapContravariant $ choose f l r

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
  invmap2 f f' g g' =
    Biff . invmap2 (invmap f f') (invmap f' f) (invmap g g') (invmap g' g) . runBiff
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
instance (Invariant2 f, Invariant2 g) => Invariant2 (Bifunctors.Product f g) where
  invmap2 f f' g g' (Bifunctors.Pair x y) =
    Bifunctors.Pair (invmap2 f f' g g' x) (invmap2 f f' g g' y)
-- | from the @bifunctors@ package
instance (Invariant f, Invariant2 p) => Invariant2 (Tannen f p) where
  invmap2 f f' g g' =
    Tannen . invmap (invmap2 f f' g g') (invmap2 f' f g' g) . runTannen
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
  invmap2 f f' g g' =
    Cayley . invmap (invmap2 f f' g g') (invmap2 f' f g' g) . runCayley
-- | from the @profunctors@ package
instance Invariant2 p => Invariant2 (Closure p) where
  invmap2 f f' g g' (Closure p) = Closure $ invmap2 (f .) (f' .) (g .) (g' .) p
-- | from the @profunctors@ package
instance Invariant2 (Environment p) where
  invmap2 _ f' g _ (Environment l m r) = Environment (g . l) m (r . f')
-- | from the @profunctors@ package
instance Invariant2 p => Invariant2 (Codensity p) where
  invmap2 ac ca bd db (Codensity f) =
    Codensity (invmap2 id id bd db . f . invmap2 id id ca ac)
-- | from the @profunctors@ package
instance (Invariant2 p, Invariant2 q) => Invariant2 (Procompose p q) where
  invmap2 l l' r r' (Procompose f g) =
    Procompose (invmap2 id id r r' f) (invmap2 l l' id id g)
-- | from the @profunctors@ package
instance (Invariant2 p, Invariant2 q) => Invariant2 (Rift p q) where
  invmap2 ac ca bd db (Rift f) = Rift (invmap2 ac ca id id . f . invmap2 db bd id id)
-- | from the @profunctors@ package
instance (Invariant2 p, Invariant2 q) => Invariant2 (Ran p q) where
  invmap2 ac ca bd db (Ran f) = Ran (invmap2 id id bd db . f . invmap2 id id ca ac)
-- | from the @profunctors@ package
instance Invariant2 p => Invariant2 (Tambara p) where
  invmap2 f f' g g' (Tambara p) =
    Tambara $ invmap2 (first f) (first f') (first g) (first g') p
-- | from the @profunctors@ package
instance Invariant2 (Pastro p) where
  invmap2 _ f' g _ (Pastro l m r) = Pastro (g . l) m (r . f')
-- | from the @profunctors@ package
instance Invariant2 p => Invariant2 (Cotambara p) where
  invmap2 f f' g g' (Cotambara p) =
    Cotambara $ invmap2 (left f) (left f') (left g) (left g') p
-- | from the @profunctors@ package
instance Invariant2 (Copastro p) where
  invmap2 _ f' g _ (Copastro l m r) = Copastro (g . l) m (r . f')

-- | from the @semigroups@ package
instance Invariant2 Arg where
  invmap2 = invmap2Bifunctor

-- | from the @tagged@ package
instance Invariant2 Tagged where
  invmap2 = invmap2Bifunctor

-- | from the @transformers@ package
instance Invariant2 Constant where
  invmap2 f _ _ _ (Constant x) = Constant (f x)

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
