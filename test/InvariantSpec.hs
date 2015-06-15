module InvariantSpec (main, spec) where

import Data.Functor.Invariant
import Test.Hspec
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck
import Test.QuickCheck.Function

main :: IO ()
main = hspec spec

data Proxy a = Proxy

-----

-- These test could probably be simplified by appealing to parametricity.
spec :: Spec
spec = do
  describe "Invariant"  . prop "satisfies the composition law" $
    composition1 (Proxy :: Proxy Integer)
                 (Proxy :: Proxy Bool)
                 (Proxy :: Proxy [Bool])
  describe "Invariant2" . prop "satisfies the composition law" $
    composition2 (Proxy :: Proxy Integer)
                 (Proxy :: Proxy Bool)
                 (Proxy :: Proxy Integer)
                 (Proxy :: Proxy Bool)
                 (Proxy :: Proxy (Bool,Bool))

-----

composition1
  :: (Eq (f c), Show (f c), Invariant f)
  => proxy b -> proxy c -> proxy (f a)
  -> Fun b c -> Fun c b
  -> Fun a b -> Fun b a
  -> f a
  -> Property
composition1
  _ _ _
  (Fun _ f) (Fun _ f')
  (Fun _ g) (Fun _ g')
  x =
      (invmap f f' . invmap g g') x
  === invmap (f . g) (g' . f') x

composition2
  :: (Eq (f c1 c2), Show (f c1 c2), Invariant2 f)
  => proxy b1 -> proxy c1 -> proxy b2 -> proxy c2 -> proxy (f a1 a2)
  -> Fun b1 c1 -> Fun c1 b1 -> Fun b2 c2 -> Fun c2 b2
  -> Fun a1 b1 -> Fun b1 a1 -> Fun a2 b2 -> Fun b2 a2
  -> f a1 a2
  -> Property
composition2
  _ _ _ _ _
  (Fun _ f1) (Fun _ f1') (Fun _ f2) (Fun _ f2')
  (Fun _ g1) (Fun _ g1') (Fun _ g2) (Fun _ g2')
  x =
      (invmap2 f1 f1' f2 f2' . invmap2 g1 g1' g2 g2') x
  === invmap2 (f1 . g1) (g1' . f1') (f2 . g2) (g2' . f2') x
