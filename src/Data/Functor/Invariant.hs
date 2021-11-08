{-# LANGUAGE CPP #-}

#if !(MIN_VERSION_base(4,16,0)) || !(MIN_VERSION_transformers(0,6,0))
{-# OPTIONS_GHC -fno-warn-deprecations #-}
#endif

#define GHC_GENERICS_OK __GLASGOW_HASKELL__ >= 702

#if GHC_GENERICS_OK
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
#endif

#if __GLASGOW_HASKELL__ >= 706
{-# LANGUAGE PolyKinds #-}
#endif

{-|
Module:      Data.Functor.Invariant
Copyright:   (C) 2012-2017 Nicolas Frisby, (C) 2015-2017 Ryan Scott
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
#if GHC_GENERICS_OK
    -- ** @GHC.Generics@
    -- $ghcgenerics
  , genericInvmap
#endif
  , WrappedFunctor(..)
  , invmapContravariant
  , WrappedContravariant(..)
  , InvariantProfunctor(..)
  , InvariantArrow(..)
    -- * @Invariant2@
  , Invariant2(..)
  , invmap2Bifunctor
  , WrappedBifunctor(..)
  , invmap2Profunctor
  , WrappedProfunctor(..)
  ) where

-- base
import           Control.Applicative as App
import qualified Control.Arrow as Arr
import           Control.Arrow hiding (first, second)
import qualified Control.Category as Cat
import           Control.Exception (Handler(..))
import           Control.Monad (MonadPlus(..), liftM)
import qualified Control.Monad.ST as Strict (ST)
import qualified Control.Monad.ST.Lazy as Lazy (ST)
#if MIN_VERSION_base(4,4,0)
import           Data.Complex (Complex(..))
#endif
import qualified Data.Foldable as F (Foldable(..))
import qualified Data.Functor.Compose as Functor (Compose(..))
import           Data.Functor.Identity (Identity)
import           Data.Functor.Product as Functor (Product(..))
import           Data.Functor.Sum as Functor (Sum(..))
#if __GLASGOW_HASKELL__ < 711
import           Data.Ix (Ix)
#endif
import           Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Monoid as Monoid (First(..), Last(..), Product(..), Sum(..))
#if MIN_VERSION_base(4,8,0)
import           Data.Monoid (Alt(..))
#endif
import           Data.Monoid (Dual(..), Endo(..))
import           Data.Proxy (Proxy(..))
import qualified Data.Semigroup as Semigroup (First(..), Last(..))
#if !(MIN_VERSION_base(4,16,0))
import qualified Data.Semigroup as Semigroup (Option(..))
#endif
import           Data.Semigroup (Min(..), Max(..), Arg(..))
import qualified Data.Traversable as T (Traversable(..))
#if GHC_GENERICS_OK
import           GHC.Generics
#endif
import           System.Console.GetOpt as GetOpt
import           Text.ParserCombinators.ReadP (ReadP)
import           Text.ParserCombinators.ReadPrec (ReadPrec)

-- array
import           Data.Array (Array)

-- bifunctors
import           Data.Bifunctor
import           Data.Bifunctor.Biff
import           Data.Bifunctor.Clown
import           Data.Bifunctor.Fix
import           Data.Bifunctor.Flip
import           Data.Bifunctor.Join
import           Data.Bifunctor.Joker
import qualified Data.Bifunctor.Product as Bifunctor
import qualified Data.Bifunctor.Sum as Bifunctor
import           Data.Bifunctor.Tannen
import           Data.Bifunctor.Wrapped

-- comonad
import           Control.Comonad (Comonad(..), Cokleisli(..), liftW)

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
import           Data.Profunctor.Choice
import           Data.Profunctor.Closed
import           Data.Profunctor.Composition
import           Data.Profunctor.Mapping
import           Data.Profunctor.Monad
import           Data.Profunctor.Rep
import           Data.Profunctor.Ran
import           Data.Profunctor.Strong
import           Data.Profunctor.Traversing
import           Data.Profunctor.Unsafe
import           Data.Profunctor.Yoneda

-- StateVar
import           Data.StateVar (StateVar(..), SettableStateVar(..))

-- stm
import           Control.Concurrent.STM (STM)

-- tagged
import           Data.Tagged (Tagged(..))

-- transformers
import           Control.Applicative.Backwards (Backwards(..))
import           Control.Applicative.Lift (Lift(..))
import           Control.Monad.Trans.Cont (ContT)
import           Control.Monad.Trans.Except (ExceptT(..), runExceptT)
import           Control.Monad.Trans.Identity (IdentityT, mapIdentityT)
import           Control.Monad.Trans.Maybe (MaybeT, mapMaybeT)
import qualified Control.Monad.Trans.RWS.Lazy as Lazy (RWST(..))
import qualified Control.Monad.Trans.RWS.Strict as Strict (RWST(..))
import           Control.Monad.Trans.Reader (ReaderT, mapReaderT)
import qualified Control.Monad.Trans.State.Lazy as Lazy (StateT(..))
import qualified Control.Monad.Trans.State.Strict as Strict (StateT(..))
import qualified Control.Monad.Trans.Writer.Lazy as Lazy (WriterT, mapWriterT)
import qualified Control.Monad.Trans.Writer.Strict as Strict (WriterT, mapWriterT)
#if !(MIN_VERSION_transformers(0,6,0))
import           Control.Monad.Trans.Error (ErrorT(..))
import           Control.Monad.Trans.List (ListT, mapListT)
#endif
import           Data.Functor.Constant (Constant(..))
import           Data.Functor.Reverse (Reverse(..))

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
#if GHC_GENERICS_OK
  default invmap :: (Generic1 f, Invariant (Rep1 f)) => (a -> b) -> (b -> a) -> f a -> f b
  invmap = genericInvmap
#endif

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

-- | from "Control.Applicative"
instance Invariant (Const a) where invmap = invmapFunctor
-- | from "Control.Applicative"
instance Invariant ZipList where invmap = invmapFunctor
-- | from "Control.Applicative"
instance Monad m => Invariant (WrappedMonad m) where invmap = invmapFunctor
-- | from "Control.Applicative"
instance Arrow arr => Invariant (App.WrappedArrow arr a) where
  invmap f _ (App.WrapArrow x) = App.WrapArrow $ ((arr f) Cat.. x)

-- | from "Control.Arrow"
instance
#if MIN_VERSION_base(4,4,0)
  Arrow a
#else
  ArrowApply a
#endif
  => Invariant (ArrowMonad a) where
  invmap f _ (ArrowMonad m) = ArrowMonad (m >>> arr f)
-- | from "Control.Arrow"
instance Monad m => Invariant (Kleisli m a) where
  invmap = invmap2 id id

-- | from "Control.Exception"
instance Invariant Handler where
  invmap f _ (Handler h) = Handler (fmap f . h)

#if MIN_VERSION_base(4,4,0)
-- | from "Data.Complex"
instance Invariant Complex where
  invmap f _ (r :+ i) = f r :+ f i
#endif

-- | from "Data.Functor.Compose"
instance (Invariant f, Invariant g) => Invariant (Functor.Compose f g) where
  invmap f g (Functor.Compose x) =
    Functor.Compose (invmap (invmap f g) (invmap g f) x)

-- | from "Data.Functor.Identity"
instance Invariant Identity where
  invmap = invmapFunctor

-- | from "Data.Functor.Product"
instance (Invariant f, Invariant g) => Invariant (Functor.Product f g) where
  invmap f g (Functor.Pair x y) = Functor.Pair (invmap f g x) (invmap f g y)

-- | from "Data.Functor.Sum"
instance (Invariant f, Invariant g) => Invariant (Functor.Sum f g) where
  invmap f g (InL x) = InL (invmap f g x)
  invmap f g (InR y) = InR (invmap f g y)

-- | from "Data.List.NonEmpty"
instance Invariant NonEmpty where
  invmap = invmapFunctor

-- | from "Data.Monoid"
instance Invariant Dual where
  invmap f _ (Dual x) = Dual (f x)
-- | from "Data.Monoid"
instance Invariant Endo where
  invmap f g (Endo x) = Endo (f . x . g)
-- | from "Data.Monoid"
instance Invariant Monoid.First where
  invmap f g (Monoid.First x) = Monoid.First (invmap f g x)
-- | from "Data.Monoid"
instance Invariant Monoid.Last where
  invmap f g (Monoid.Last x) = Monoid.Last (invmap f g x)
-- | from "Data.Monoid"
instance Invariant Monoid.Product where
  invmap f _ (Monoid.Product x) = Monoid.Product (f x)
-- | from "Data.Monoid"
instance Invariant Monoid.Sum where
  invmap f _ (Monoid.Sum x) = Monoid.Sum (f x)
#if MIN_VERSION_base(4,8,0)
-- | from "Data.Monoid"
instance Invariant f => Invariant (Alt f) where
  invmap f g (Alt x) = Alt (invmap f g x)
#endif

-- | from "Data.Proxy"
instance Invariant Proxy where
  invmap = invmapFunctor

-- | from "Data.Semigroup"
instance Invariant Min where
  invmap = invmapFunctor
-- | from "Data.Semigroup"
instance Invariant Max where
  invmap = invmapFunctor
-- | from "Data.Semigroup"
instance Invariant Semigroup.First where
  invmap = invmapFunctor
-- | from "Data.Semigroup"
instance Invariant Semigroup.Last where
  invmap = invmapFunctor
-- | from "Data.Semigroup"
instance Invariant (Arg a) where
  invmap = invmapFunctor
#if !(MIN_VERSION_base(4,16,0))
-- | from "Data.Semigroup"
instance Invariant Semigroup.Option where
  invmap = invmapFunctor
#endif

-- | from "System.Console.GetOpt"
instance Invariant ArgDescr where
  invmap f _ (NoArg a)    = NoArg (f a)
  invmap f _ (ReqArg g s) = ReqArg (f . g) s
  invmap f _ (OptArg g s) = OptArg (f . g) s
-- | from "System.Console.GetOpt"
instance Invariant ArgOrder where
  invmap _ _ RequireOrder      = RequireOrder
  invmap _ _ Permute           = Permute
  invmap f _ (ReturnInOrder g) = ReturnInOrder (f . g)
-- | from "System.Console.GetOpt"
instance Invariant OptDescr where
  invmap f g (GetOpt.Option a b argDescr c) = GetOpt.Option a b (invmap f g argDescr) c

-- | from the @array@ package
instance
#if __GLASGOW_HASKELL__ < 711
  Ix i =>
#endif
    Invariant (Array i) where
  invmap = invmapFunctor

-- | from the @bifunctors@ package
instance (Invariant2 p, Invariant g) => Invariant (Biff p f g a) where
  invmap f g = Biff . invmap2 id id (invmap f g) (invmap g f) . runBiff
-- | from the @bifunctors@ package
instance Invariant (Clown f a) where
  invmap = invmapFunctor
-- | from the @bifunctors@ package
instance Invariant2 p => Invariant (Fix p) where
  invmap f g = In . invmap2 (invmap f g) (invmap g f) f g . out
-- | from the @bifunctors@ package
instance Invariant2 p => Invariant (Flip p a) where
  invmap = invmap2 id id
-- | from the @bifunctors@ package
instance Invariant2 p => Invariant (Join p) where
  invmap f g = Join . invmap2 f g f g . runJoin
-- | from the @bifunctors@ package
instance Invariant g => Invariant (Joker g a) where
  invmap f g = Joker . invmap f g . runJoker
-- | from the @bifunctors@ package
instance (Invariant f, Invariant2 p) => Invariant (Tannen f p a) where
  invmap = invmap2 id id
-- | from the @bifunctors@ package
instance Bifunctor p => Invariant (WrappedBifunctor p a) where
  invmap = invmap2 id id

-- | from the @comonad@ package
instance Invariant (Cokleisli w a) where
  invmap = invmapFunctor

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
instance Invariant2 p => Invariant (Coprep p) where
  invmap f g (Coprep h) = Coprep (h . invmap2 g f id id)
-- | from the @profunctors@ package
instance Invariant2 p => Invariant (Prep p) where
  invmap f g (Prep x p) = Prep x (invmap2 id id f g p)
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
instance Invariant (Cotambara p a) where
  invmap = invmapFunctor
-- | from the @profunctors@ package
instance Invariant (CotambaraSum p a) where
  invmap = invmapFunctor
-- | from the @profunctors@ package
instance Invariant2 p => Invariant (TambaraSum p a) where
  invmap = invmap2 id id
-- | from the @profunctors@ package
instance Invariant (Yoneda p a) where
  invmap = invmapFunctor

-- | from the @StateVar@ package
instance Invariant StateVar where
  invmap f g (StateVar ga sa) = StateVar (fmap f ga) (lmap g sa)
-- | from the @StateVar@ package
instance Invariant SettableStateVar where
  invmap = invmapContravariant

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
-- | from the @transformers@ package
instance Invariant m => Invariant (ExceptT e m) where
  invmap f g = ExceptT . invmap (invmap f g) (invmap g f) . runExceptT
-- | from the @transformers@ package
instance Invariant m => Invariant (IdentityT m) where
  invmap f g = mapIdentityT (invmap f g)
-- | from the @transformers@ package
instance Invariant m => Invariant (MaybeT m) where
  invmap f g = mapMaybeT $ invmap (invmap f g) (invmap g f)
-- | from the @transformers@ package
instance Invariant m => Invariant (Lazy.RWST r w s m) where
  invmap f g m = Lazy.RWST $ \r s ->
    invmap (mapFstTriple f) (mapFstTriple g) $ Lazy.runRWST m r s
      where mapFstTriple :: (a -> b) -> (a, c, d) -> (b, c, d)
            mapFstTriple h ~(a, s, w) = (h a, s, w)
-- | from the @transformers@ package
instance Invariant m => Invariant (Strict.RWST r w s m) where
  invmap f g m = Strict.RWST $ \r s ->
    invmap (mapFstTriple f) (mapFstTriple g) $ Strict.runRWST m r s
      where mapFstTriple :: (a -> b) -> (a, c, d) -> (b, c, d)
            mapFstTriple h (a, s, w) = (h a, s, w)
-- | from the @transformers@ package
instance Invariant m => Invariant (ReaderT r m) where
  invmap f g = mapReaderT (invmap f g)
-- | from the @transformers@ package
instance Invariant m => Invariant (Lazy.StateT s m) where
  invmap f g m = Lazy.StateT $ \s ->
    invmap (mapFstPair f) (mapFstPair g) $ Lazy.runStateT m s
      where mapFstPair :: (a -> b) -> (a, c) -> (b, c)
            mapFstPair h ~(a, s) = (h a, s)
-- | from the @transformers@ package
instance Invariant m => Invariant (Strict.StateT s m) where
  invmap f g m = Strict.StateT $ \s ->
    invmap (mapFstPair f) (mapFstPair g) $ Strict.runStateT m s
      where mapFstPair :: (a -> b) -> (a, c) -> (b, c)
            mapFstPair h (a, s) = (h a, s)
-- | from the @transformers@ package
instance Invariant m => Invariant (Lazy.WriterT w m) where
  invmap f g = Lazy.mapWriterT $ invmap (mapFstPair f) (mapFstPair g)
    where mapFstPair :: (a -> b) -> (a, c) -> (b, c)
          mapFstPair h ~(a, w) = (h a, w)
-- | from the @transformers@ package
instance Invariant m => Invariant (Strict.WriterT w m) where
  invmap f g = Strict.mapWriterT $ invmap (mapFstPair f) (mapFstPair g)
    where mapFstPair :: (a -> b) -> (a, c) -> (b, c)
          mapFstPair h (a, w) = (h a, w)
-- | from the @transformers@ package
instance Invariant (Constant a) where
  invmap = invmapFunctor
-- | from the @transformers@ package
instance Invariant f => Invariant (Reverse f) where
  invmap f g (Reverse a) = Reverse (invmap f g a)
#if !(MIN_VERSION_transformers(0,6,0))
-- | from the @transformers@ package
instance Invariant m => Invariant (ErrorT e m) where
  invmap f g = ErrorT . invmap (invmap f g) (invmap g f) . runErrorT
-- | from the @transformers@ package
instance Invariant m => Invariant (ListT m) where
  invmap f g = mapListT $ invmap (invmap f g) (invmap g f)
#endif

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
  invmap = invmapFunctor

instance Functor f => Functor (WrappedFunctor f) where
  fmap f = WrapFunctor . fmap f . unwrapFunctor
  x <$ WrapFunctor f = WrapFunctor (x <$ f)

instance Applicative f => Applicative (WrappedFunctor f) where
  pure = WrapFunctor . pure
  WrapFunctor f <*> WrapFunctor x = WrapFunctor (f <*> x)
  WrapFunctor a *>  WrapFunctor b = WrapFunctor (a *>  b)
  WrapFunctor a <*  WrapFunctor b = WrapFunctor (a <*  b)

instance Alternative f => Alternative (WrappedFunctor f) where
  empty = WrapFunctor empty
  WrapFunctor x <|> WrapFunctor y = WrapFunctor (x <|> y)
  some = WrapFunctor . some . unwrapFunctor
  many = WrapFunctor . many . unwrapFunctor

instance Monad m => Monad (WrappedFunctor m) where
  WrapFunctor x >>= f = WrapFunctor (x >>= unwrapFunctor . f)
#if !(MIN_VERSION_base(4,11,0))
  return = WrapFunctor . return
  WrapFunctor a >> WrapFunctor b = WrapFunctor (a >> b)
#endif

instance MonadPlus m => MonadPlus (WrappedFunctor m) where
  mzero = WrapFunctor mzero
  WrapFunctor x `mplus` WrapFunctor y = WrapFunctor (x `mplus` y)

instance F.Foldable f => F.Foldable (WrappedFunctor f) where
  fold       = F.fold       . unwrapFunctor
  foldMap f  = F.foldMap f  . unwrapFunctor
  foldr f z  = F.foldr f z  . unwrapFunctor
  foldl f q  = F.foldl f q  . unwrapFunctor
  foldr1 f   = F.foldr1 f   . unwrapFunctor
  foldl1 f   = F.foldl1 f   . unwrapFunctor
#if MIN_VERSION_base(4,6,0)
  foldr' f z = F.foldr' f z . unwrapFunctor
  foldl' f q = F.foldl' f q . unwrapFunctor
#endif
#if MIN_VERSION_base(4,8,0)
  toList     = F.toList     . unwrapFunctor
  null       = F.null       . unwrapFunctor
  length     = F.length     . unwrapFunctor
  elem x     = F.elem x     . unwrapFunctor
  maximum    = F.maximum    . unwrapFunctor
  minimum    = F.minimum    . unwrapFunctor
  sum        = F.sum        . unwrapFunctor
  product    = F.product    . unwrapFunctor
#endif
#if MIN_VERSION_base(4,13,0)
  foldMap' f = F.foldMap' f . unwrapFunctor
#endif

instance T.Traversable f => T.Traversable (WrappedFunctor f) where
  traverse f = fmap  WrapFunctor . T.traverse f . unwrapFunctor
  sequenceA  = fmap  WrapFunctor . T.sequenceA  . unwrapFunctor
  mapM f     = liftM WrapFunctor . T.mapM f     . unwrapFunctor
  sequence   = liftM WrapFunctor . T.sequence   . unwrapFunctor

-------------------------------------------------------------------------------
-- WrappedContravariant
-------------------------------------------------------------------------------

-- | Wrap a 'Contravariant' functor to be used as a member of 'Invariant'.
newtype WrappedContravariant f a = WrapContravariant { unwrapContravariant :: f a }
  deriving (Eq, Ord, Read, Show)

instance Contravariant f => Invariant (WrappedContravariant f) where
  invmap = invmapContravariant

instance Contravariant f => Contravariant (WrappedContravariant f) where
  contramap f = WrapContravariant . contramap f . unwrapContravariant
  x >$ WrapContravariant f = WrapContravariant (x >$ f)

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

-- | from "Control.Applicative"
instance Invariant2 Const where invmap2 = invmap2Bifunctor
-- | from "Control.Applicative"
instance Arrow arr => Invariant2 (App.WrappedArrow arr) where
  invmap2 _ f' g _ (App.WrapArrow x) = App.WrapArrow $ arr g Cat.. x Cat.. arr f'

-- | from "Control.Arrow"
instance Monad m => Invariant2 (Kleisli m) where
  invmap2 _ f' g _ (Kleisli m) = Kleisli $ liftM g . m . f'

-- | from "Data.Semigroup"
instance Invariant2 Arg where
  invmap2 = invmap2Bifunctor

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
instance (Invariant2 f, Invariant2 g) => Invariant2 (Bifunctor.Product f g) where
  invmap2 f f' g g' (Bifunctor.Pair x y) =
    Bifunctor.Pair (invmap2 f f' g g' x) (invmap2 f f' g g' y)
-- | from the @bifunctors@ package
instance (Invariant2 p, Invariant2 q) => Invariant2 (Bifunctor.Sum p q) where
  invmap2 f f' g g' (Bifunctor.L2 l) = Bifunctor.L2 (invmap2 f f' g g' l)
  invmap2 f f' g g' (Bifunctor.R2 r) = Bifunctor.R2 (invmap2 f f' g g' r)
-- | from the @bifunctors@ package
instance (Invariant f, Invariant2 p) => Invariant2 (Tannen f p) where
  invmap2 f f' g g' =
    Tannen . invmap (invmap2 f f' g g') (invmap2 f' f g' g) . runTannen
-- | from the @bifunctors@ package
instance Bifunctor p => Invariant2 (WrappedBifunctor p) where
  invmap2 = invmap2Bifunctor

-- | from the @comonad@ package
instance Comonad w => Invariant2 (Cokleisli w) where
   invmap2 _ f' g _ (Cokleisli w) = Cokleisli $ g . w . liftW f'

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
  invmap2 = invmap2Profunctor
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
instance Invariant2 (PastroSum p) where
  invmap2 = invmap2Profunctor
-- | from the @profunctors@ package
instance Invariant2 p => Invariant2 (CofreeMapping p) where
  invmap2 f f' g g' (CofreeMapping p) =
    CofreeMapping (invmap2 (fmap f) (fmap f') (fmap g) (fmap g') p)
-- | from the @profunctors@ package
instance Invariant2 (FreeMapping p) where
  invmap2 = invmap2Profunctor
-- | from the @profunctors@ package
instance Invariant2 p => Invariant2 (CofreeTraversing p) where
  invmap2 f f' g g' (CofreeTraversing p) =
    CofreeTraversing (invmap2 (fmap f) (fmap f') (fmap g) (fmap g') p)
-- | from the @profunctors@ package
instance Invariant2 (FreeTraversing p) where
  invmap2 = invmap2Profunctor
-- | from the @profunctors@ package
instance Invariant2 (Pastro p) where
  invmap2 = invmap2Profunctor
-- | from the @profunctors@ package
instance Invariant2 (Cotambara p) where
  invmap2 = invmap2Profunctor
-- | from the @profunctors@ package
instance Invariant2 (CopastroSum p) where
  invmap2 = invmap2Profunctor
-- | from the @profunctors@ package
instance Invariant2 (CotambaraSum p) where
  invmap2 = invmap2Profunctor
-- | from the @profunctors@ package
instance Invariant2 p => Invariant2 (TambaraSum p) where
  invmap2 f f' g g' (TambaraSum p) =
    TambaraSum (invmap2 (first f) (first f') (first g) (first g') p)
-- | from the @profunctors@ package
instance Invariant2 (Yoneda p) where
  invmap2 = invmap2Profunctor

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
  invmap2 = invmap2Profunctor

instance Profunctor p => Invariant (WrappedProfunctor p a) where
  invmap = invmap2 id id

instance Profunctor p => Profunctor (WrappedProfunctor p) where
  dimap f g = WrapProfunctor . dimap f g . unwrapProfunctor
  lmap f    = WrapProfunctor . lmap f    . unwrapProfunctor
  rmap g    = WrapProfunctor . rmap g    . unwrapProfunctor
  WrapProfunctor x .# f = WrapProfunctor (x .# f)
  g #. WrapProfunctor x = WrapProfunctor (g #. x)

instance Cat.Category p => Cat.Category (WrappedProfunctor p) where
  id = WrapProfunctor Cat.id
  WrapProfunctor p1 . WrapProfunctor p2 = WrapProfunctor (p1 Cat.. p2)

instance Arrow p => Arrow (WrappedProfunctor p) where
  arr    = WrapProfunctor . arr
  first  = WrapProfunctor . Arr.first  . unwrapProfunctor
  second = WrapProfunctor . Arr.second . unwrapProfunctor
  WrapProfunctor p1 *** WrapProfunctor p2 = WrapProfunctor (p1 *** p2)
  WrapProfunctor p1 &&& WrapProfunctor p2 = WrapProfunctor (p1 &&& p2)

instance ArrowZero p => ArrowZero (WrappedProfunctor p) where
  zeroArrow = WrapProfunctor zeroArrow

instance ArrowPlus p => ArrowPlus (WrappedProfunctor p) where
  WrapProfunctor p1 <+> WrapProfunctor p2 = WrapProfunctor (p1 <+> p2)

instance ArrowChoice p => ArrowChoice (WrappedProfunctor p) where
  left  = WrapProfunctor . left  . unwrapProfunctor
  right = WrapProfunctor . right . unwrapProfunctor
  WrapProfunctor p1 +++ WrapProfunctor p2 = WrapProfunctor (p1 +++ p2)
  WrapProfunctor p1 ||| WrapProfunctor p2 = WrapProfunctor (p1 ||| p2)

instance ArrowLoop p => ArrowLoop (WrappedProfunctor p) where
  loop = WrapProfunctor . loop . unwrapProfunctor

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

instance Traversing p => Traversing (WrappedProfunctor p) where
  traverse' = WrapProfunctor . traverse' . unwrapProfunctor
  wander f  = WrapProfunctor . wander f  . unwrapProfunctor

instance Mapping p => Mapping (WrappedProfunctor p) where
  map' = WrapProfunctor . map' . unwrapProfunctor

instance ProfunctorFunctor WrappedProfunctor where
  promap f = WrapProfunctor . f . unwrapProfunctor

instance ProfunctorMonad WrappedProfunctor where
  proreturn = WrapProfunctor
  projoin   = unwrapProfunctor

instance ProfunctorComonad WrappedProfunctor where
  proextract   = unwrapProfunctor
  produplicate = WrapProfunctor

#if GHC_GENERICS_OK
-------------------------------------------------------------------------------
-- GHC Generics
-------------------------------------------------------------------------------

-- | from "GHC.Generics"
instance Invariant V1 where
  -- NSF 25 July 2015: I'd prefer an -XEmptyCase, but Haskell98.
  invmap _ _ x = x `seq` error "Invariant V1"
-- | from "GHC.Generics"
instance Invariant U1 where invmap _ _ _ = U1
-- | from "GHC.Generics"
instance (Invariant l, Invariant r) => Invariant ((:+:) l r) where
  invmap f g (L1 l) = L1 $ invmap f g l
  invmap f g (R1 r) = R1 $ invmap f g r
-- | from "GHC.Generics"
instance (Invariant l, Invariant r) => Invariant ((:*:) l r) where
  invmap f g ~(l :*: r) = invmap f g l :*: invmap f g r
-- | from "GHC.Generics"
instance Invariant (K1 i c) where invmap _ _ (K1 c) = K1 c
-- | from "GHC.Generics"
instance Invariant2 (K1 i) where invmap2 f _ _ _ (K1 c) = K1 $ f c
-- | from "GHC.Generics"
instance Invariant f => Invariant (M1 i t f) where invmap f g (M1 fp) = M1 $ invmap f g fp
-- | from "GHC.Generics"
instance Invariant Par1 where invmap f _ (Par1 c) = Par1 $ f c
-- | from "GHC.Generics"
instance Invariant f => Invariant (Rec1 f) where invmap f g (Rec1 fp) = Rec1 $ invmap f g fp
-- | from "GHC.Generics"
instance (Invariant f, Invariant g) => Invariant ((:.:) f g) where
  invmap f g (Comp1 fgp) = Comp1 $ invmap (invmap f g) (invmap g f) fgp

# if __GLASGOW_HASKELL__ >= 800
-- | from "GHC.Generics"
instance Invariant UAddr where
  invmap _ _ (UAddr a) = UAddr a

-- | from "GHC.Generics"
instance Invariant UChar where
  invmap _ _ (UChar c) = UChar c

-- | from "GHC.Generics"
instance Invariant UDouble where
  invmap _ _ (UDouble d) = UDouble d

-- | from "GHC.Generics"
instance Invariant UFloat where
  invmap _ _ (UFloat f) = UFloat f

-- | from "GHC.Generics"
instance Invariant UInt where
  invmap _ _ (UInt i) = UInt i

-- | from "GHC.Generics"
instance Invariant UWord where
  invmap _ _ (UWord w) = UWord w
# endif

{- $ghcgenerics
With GHC 7.2 or later, 'Invariant' instances can be defined easily using GHC
generics like so:

@
&#123;-&#35; LANGUAGE DeriveGeneric, FlexibleContexts &#35;-&#125;

import Data.Functor.Invariant
import GHC.Generics

data T f a = T (f a) deriving Generic1

instance Invariant f => 'Invariant' (T f)
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

-------------------------------------------------------------------------------
-- Wrappers
-------------------------------------------------------------------------------

newtype InvariantProfunctor p a = InvariantProfunctor (p a a)

instance Profunctor p => Invariant (InvariantProfunctor p) where
  invmap fn1 fn2 (InvariantProfunctor f) = InvariantProfunctor (dimap fn2 fn1 f)

newtype InvariantArrow c a = InvariantArrow (c a a)

instance Arrow c => Invariant (InvariantArrow c) where
  invmap fn1 fn2 (InvariantArrow arrow) = InvariantArrow (arr fn1 Cat.. arrow Cat.. arr fn2)
