{-# LANGUAGE CPP #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
#if __GLASGOW_HASKELL__ >= 708
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE RoleAnnotations #-}
#endif

{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}
#if __GLASGOW_HASKELL__ >= 800
{-# OPTIONS_GHC -fno-warn-unused-foralls #-}
#endif
module THSpec (main, spec) where

import Data.Functor.Invariant
import Data.Functor.Invariant.TH

import Test.Hspec
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck (Arbitrary)

-------------------------------------------------------------------------------

-- Adapted from the test cases from
-- https://ghc.haskell.org/trac/ghc/attachment/ticket/2953/deriving-functor-tests.patch

-- Plain data types

data Strange a b c
    = T1 a b c
    | T2 [a] [b] [c]         -- lists
    | T3 [[a]] [[b]] [[c]]   -- nested lists
    | T4 (c,(b,b),(c,c))     -- tuples
    | T5 ([c],Strange a b c) -- tycons
    | T6 (b -> c)            -- function types
    | T7 (b -> (c,a))        -- functions and tuples
    | T8 ((c -> b) -> a)     -- continuation

data NotPrimitivelyRecursive a b
    = S1 (NotPrimitivelyRecursive (a,a) (b, a))
    | S2 a
    | S3 b

newtype Compose f g a b = Compose (f (g a b))
  deriving (Arbitrary, Eq, Show)

data ComplexConstraint f a b = ComplexConstraint (f Int Int (f Bool Bool a,a,b))

data Universal a
    = Universal  (forall b. (b,[a]))
    | Universal2 (forall f. Invariant f => (f a))
    | Universal3 (forall a. a -> Int) -- reuse a
    | NotReallyUniversal (forall b. a)

data Existential b
    = forall a. ExistentialList [a]
    | forall f. Invariant f => ExistentialFunctor (f b)
    | forall b. SneakyUseSameName (b -> Bool)

type IntFun a b = b -> a
data IntFunD a b = IntFunD (IntFun a b)

data Empty1 a b
data Empty2 a b
#if __GLASGOW_HASKELL__ >= 708
type role Empty2 nominal nominal
#endif

data TyCon18 a b c = TyCon18 c (TyCon18 a a c)

data TyCon19 a b
    = TyCon19a (forall c. c -> (forall d. a -> d) -> a)
    | TyCon19b (Int -> forall c. c -> b)

type family F :: * -> * -> *
type instance F = Either

data TyCon20 a b = TyCon20 (F a b)

-- Data families

data family   StrangeFam a b c
data instance StrangeFam a b c
    = T1Fam a b c
    | T2Fam [a] [b] [c]         -- lists
    | T3Fam [[a]] [[b]] [[c]]   -- nested lists
    | T4Fam (c,(b,b),(c,c))     -- tuples
    | T5Fam ([c],Strange a b c) -- tycons
    | T6Fam (b -> c)            -- function types
    | T7Fam (b -> (c,a))        -- functions and tuples
    | T8Fam ((c -> b) -> a)     -- continuation

data family   NotPrimitivelyRecursiveFam a b
data instance NotPrimitivelyRecursiveFam a b
    = S1Fam (NotPrimitivelyRecursive (a,a) (b, a))
    | S2Fam a
    | S3Fam b

data family      ComposeFam (f :: * -> *) (g :: * -> * -> *) a b
newtype instance ComposeFam f g a b = ComposeFam (f (g a b))
  deriving (Arbitrary, Eq, Show)

data family   ComplexConstraintFam (f :: * -> * -> * -> *) a b
data instance ComplexConstraintFam f a b =
    ComplexConstraintFam (f Int Int (f Bool Bool a,a,b))

data family   UniversalFam a
data instance UniversalFam a
    = UniversalFam  (forall b. (b,[a]))
    | Universal2Fam (forall f. Invariant f => (f a))
    | Universal3Fam (forall a. a -> Int) -- reuse a
    | NotReallyUniversalFam (forall b. a)

data family   ExistentialFam b
data instance ExistentialFam b
    = forall a. ExistentialListFam [a]
    | forall f. Invariant f => ExistentialFunctorFam (f b)
    | forall b. SneakyUseSameNameFam (b -> Bool)

data family   IntFunDFam a b
data instance IntFunDFam a b = IntFunDFam (IntFun a b)

data family   TyFamily18 x y z
data instance TyFamily18 a b c = TyFamily18 c (TyFamily18 a a c)

data family   TyFamily19 x y
data instance TyFamily19 a b
    = TyFamily19a (forall c. c -> (forall d. a -> d) -> a)
    | TyFamily19b (Int -> forall c. c -> b)

data family   TyFamily20 x y
data instance TyFamily20 a b = TyFamily20 (F a b)

-------------------------------------------------------------------------------

-- Plain data types

$(deriveInvariant  ''Strange)
$(deriveInvariant2 ''Strange)

$(deriveInvariant  ''NotPrimitivelyRecursive)
$(deriveInvariant2 ''NotPrimitivelyRecursive)

instance (Invariant f, Invariant (g a)) =>
  Invariant (Compose f g a) where
    invmap = $(makeInvmap ''Compose)
$(deriveInvariant2 ''Compose)

instance Invariant (f Int Int) =>
  Invariant (ComplexConstraint f a) where
    invmap = $(makeInvmap ''ComplexConstraint)
instance (Invariant2 (f Bool), Invariant2 (f Int)) =>
  Invariant2 (ComplexConstraint f) where
    invmap2 = $(makeInvmap2 ''ComplexConstraint)

$(deriveInvariant ''Universal)

$(deriveInvariant ''Existential)

$(deriveInvariant  ''IntFunD)
$(deriveInvariant2 ''IntFunD)

$(deriveInvariant  ''Empty1)
$(deriveInvariant2 ''Empty1)

-- Use EmptyCase here
$(deriveInvariantOptions  defaultOptions{emptyCaseBehavior = True} ''Empty2)
$(deriveInvariant2Options defaultOptions{emptyCaseBehavior = True} ''Empty2)

$(deriveInvariant  ''TyCon18)
$(deriveInvariant2 ''TyCon18)

$(deriveInvariant  ''TyCon19)
$(deriveInvariant2 ''TyCon19)

$(deriveInvariant  ''TyCon20)
$(deriveInvariant2 ''TyCon20)

#if MIN_VERSION_template_haskell(2,7,0)
-- Data Families

$(deriveInvariant  'T1Fam)
$(deriveInvariant2 'T2Fam)

$(deriveInvariant  'S1Fam)
$(deriveInvariant2 'S2Fam)

instance (Invariant f, Invariant (g a)) =>
  Invariant (ComposeFam f g a) where
    invmap = $(makeInvmap 'ComposeFam)
$(deriveInvariant2 'ComposeFam)

instance Invariant (f Int Int) =>
  Invariant (ComplexConstraintFam f a) where
    invmap = $(makeInvmap 'ComplexConstraintFam)
instance (Invariant2 (f Bool), Invariant2 (f Int)) =>
  Invariant2 (ComplexConstraintFam f) where
    invmap2 = $(makeInvmap2 'ComplexConstraintFam)

$(deriveInvariant  'UniversalFam)

$(deriveInvariant  'ExistentialListFam)

$(deriveInvariant  'IntFunDFam)
$(deriveInvariant2 'IntFunDFam)

$(deriveInvariant  'TyFamily18)
$(deriveInvariant2 'TyFamily18)

$(deriveInvariant  'TyFamily19a)
$(deriveInvariant2 'TyFamily19a)

$(deriveInvariant  'TyFamily20)
$(deriveInvariant2 'TyFamily20)
#endif

-------------------------------------------------------------------------------

-- | Verifies that @invmap id id = id@ (the other 'invmap' law follows
-- as a free theorem:
-- https://www.fpcomplete.com/user/edwardk/snippets/fmap).
prop_invmapLaws :: (Eq (f a), Show (f a), Invariant f) => f a -> Expectation
prop_invmapLaws x = invmap id id x `shouldBe` x

-- | Verifies that @invmap2 id id id id = id@.
prop_invmap2Laws :: (Eq (f a b), Show (f a b), Invariant2 f) => f a b -> Expectation
prop_invmap2Laws x = invmap2 id id id id x `shouldBe` x

-------------------------------------------------------------------------------

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
    describe "Compose    Maybe Either Int Int" $ do
        prop "satisfies the invmap laws"  (prop_invmapLaws  :: Compose    Maybe Either Int Int -> Expectation)
        prop "satisfies the invmap2 laws" (prop_invmap2Laws :: Compose    Maybe Either Int Int -> Expectation)
#if MIN_VERSION_template_haskell(2,7,0)
    describe "ComposeFam Maybe Either Int Int" $ do
        prop "satisfies the invmap laws"  (prop_invmapLaws  :: ComposeFam Maybe Either Int Int -> Expectation)
        prop "satisfies the invmap2 laws" (prop_invmap2Laws :: ComposeFam Maybe Either Int Int -> Expectation)
#endif
