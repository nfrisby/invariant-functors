module Test where

import Test.QuickCheck
import Test.QuickCheck.Function

import Data.Functor.Invariant



-- These test could probably be simplified by appealing to parametricity.



test = do
  quickCheck $ prop  (0 :: Integer) 'c' . (`asTypeOf` [True])
  quickCheck $ prop2 (0 :: Integer) 'c' (0 :: Integer) 'c' . (`asTypeOf` (True, True))

  

prop :: (Eq (f c), Invariant f) =>
     b -> c -> f a -> Fun b c -> Fun c b -> Fun a b -> Fun b a -> Bool
prop b c x (Fun _ f) (Fun _ f') (Fun _ g) (Fun _ g') =
  (invmap f f' . invmap g g') x ==
     invmap ((`asTypeOf` c) . f . (`asTypeOf` b) . g) (g' . f') x

prop2 :: (Eq (f c1 c2), Invariant2 f) =>
     b1 -> c1 -> b2 -> c2 -> f a1 a2 ->
     Fun b1 c1 -> Fun c1 b1 -> Fun b2 c2 -> Fun c2 b2 ->
     Fun a1 b1 -> Fun b1 a1 -> Fun a2 b2 -> Fun b2 a2 ->
     Bool
prop2 b1 c1 b2 c2 x
        (Fun _ f1) (Fun _ f1') (Fun _ f2) (Fun _ f2')
        (Fun _ g1) (Fun _ g1') (Fun _ g2) (Fun _ g2') =
  (invmap2 f1 f1' f2 f2' . invmap2 g1 g1' g2 g2') x ==
     invmap2 ((`asTypeOf` c1) . f1 . (`asTypeOf` b1) . g1) (g1' . f1')
             ((`asTypeOf` c2) . f2 . (`asTypeOf` b2) . g2) (g2' . f2') x
