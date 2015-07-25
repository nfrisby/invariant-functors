{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}
module THSpec (main, spec) where

import Data.Functor.Invariant
import Data.Functor.Invariant.TH

import Test.Hspec
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck (Arbitrary)

-------------------------------------------------------------------------------

-- Adapted from the test cases from
-- https://ghc.haskell.org/trac/ghc/attachment/ticket/2953/deriving-functor-tests.patch

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

data ComplexConstraint f a b = ComplexContraint (f Int Int (f Bool Bool a,a,b))

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

-------------------------------------------------------------------------------

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

-------------------------------------------------------------------------------

-- | Verifies that @invmap id id = id@ (the other 'invmap' law follows
-- as a free theorem:
-- https://www.fpcomplete.com/user/edwardk/snippets/fmap).
prop_invmapLaws :: (Eq (f a), Invariant f) => f a -> Bool
prop_invmapLaws x = invmap id id x == x

-- | Verifies that @invmap2 id id id id = id@.
prop_invmap2Laws :: (Eq (f a b), Invariant2 f) => f a b -> Bool
prop_invmap2Laws x = invmap2 id id id id x == x

-------------------------------------------------------------------------------

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
    describe "Compose Maybe Either Int Int" $ do
        prop "satisfies the invmap laws"  (prop_invmapLaws  :: Compose Maybe Either Int Int -> Bool)
        prop "satisfies the invmap2 laws" (prop_invmap2Laws :: Compose Maybe Either Int Int -> Bool)
