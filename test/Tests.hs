module Tests where

import Data.Functor.Invariant
import Distribution.TestSuite.QuickCheck
import Test.QuickCheck
import Test.QuickCheck.Function

data Proxy a = Proxy

-----

-- These test could probably be simplified by appealing to parametricity.
tests :: IO [Test]
tests = return
  [ testProperty "composition1" $ prop  (Proxy :: Proxy Integer) (Proxy :: Proxy Bool) (Proxy :: Proxy [Bool])
  , testProperty "composition2" $ prop2 (Proxy :: Proxy Integer) (Proxy :: Proxy Bool) (Proxy :: Proxy Integer) (Proxy :: Proxy Bool) (Proxy :: Proxy (Bool,Bool))
  ]

-----

prop ::
     ( Eq (f c), Invariant f
     , Show a, Show b, Show c
     , Show (f a), Show (f c)
     )
  => proxy b -> proxy c -> proxy (f a)
  -> Fun b c -> Fun c b
  -> Fun a b -> Fun b a
  -> f a
  -> Property
prop
  _ _ _
  (Fun _ f) (Fun _ f')
  (Fun _ g) (Fun _ g')
  x =
      (invmap f f' . invmap g g') x
  === invmap (f . g) (g' . f') x

prop2 ::
     ( Eq (f c1 c2), Invariant2 f
     , Show a1, Show b1, Show c1
     , Show a2, Show b2, Show c2
     , Show (f a1 a2), Show (f c1 c2)
     )
  => proxy b1 -> proxy c1 -> proxy b2 -> proxy c2 -> proxy (f a1 a2)
  -> Fun b1 c1 -> Fun c1 b1 -> Fun b2 c2 -> Fun c2 b2
  -> Fun a1 b1 -> Fun b1 a1 -> Fun a2 b2 -> Fun b2 a2
  -> f a1 a2
  -> Property
prop2
  _ _ _ _ _
  (Fun _ f1) (Fun _ f1') (Fun _ f2) (Fun _ f2')
  (Fun _ g1) (Fun _ g1') (Fun _ g2) (Fun _ g2')
  x =
      (invmap2 f1 f1' f2 f2' . invmap2 g1 g1' g2 g2') x
  === invmap2 (f1 . g1) (g1' . f1') (f2 . g2) (g2' . f2') x
