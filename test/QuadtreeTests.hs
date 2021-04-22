{-# LANGUAGE TemplateHaskell #-}

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}

module Main where

import Data.QuadTree

import Test.QuickCheck.Arbitrary (Arbitrary, arbitrary)
import Test.QuickCheck.Modifiers (Positive(..), NonNegative(..))
import Test.QuickCheck.Gen (Gen, choose, oneof, suchThat,
                            listOf, infiniteListOf)
import Test.QuickCheck.Property (Property, (==>))
import Test.QuickCheck.All (quickCheckAll, forAllProperties)

import Text.Show.Functions ()
import System.Exit (exitSuccess, exitFailure)

import Control.Monad (replicateM)
import Data.Functor ((<$>))
import Data.Foldable (find)
import Test.QuickCheck.Test
import Numeric.Natural (Natural)
import GHC.Natural (naturalFromInteger)

{- Structure

The QuadTree type has two structural invariants/constraints:

   1. The internal raw tree must not be deeper than its
   declared depth.

   2. No branch node can have four leaves that are identical.
   These need to be fused into a single leaf node by the algorithms.

We will acknowledge and manage these invariants by constructing
two separate Arbitrary generators for QuadTrees:

  1. The first generator will construct QuadTrees strictly using the
  exposed API (makeTree and setLocation). We'll use this to test if
  the invariant is consistently maintained across the subset of QuadTrees
  that the user can construct.

  2. The second generator will generate QuadTrees ex nihilo that obey
  the invariants. We'll use this for our primary testing purposes, since
  it can theoretically generate valid non-user-constructable trees and
  because it can generate large complex trees far far more efficiently.

-}

---- The API-constructable QuadTree generator

newtype APITree a = Constructed (QuadTree a)

instance Show a => Show (APITree a) where
  show (Constructed qt) = show qt

instance (Eq a, Arbitrary a) => Arbitrary (APITree a) where
  arbitrary = do
    Positive len <- arbitrary
    Positive wid <- arbitrary
    baseValue    <- arbitrary
    let baseTree = makeTree (len, wid) baseValue

    indices <- listOf $ generateIndexOf baseTree
    values  <- infiniteListOf arbitrary
    let setList = zip indices values

    return . Constructed $ foldr (uncurry setLocation) baseTree setList

-- Generates a random valid location index for a quadtree
generateIndexOf :: QuadTree a -> Gen (Natural, Natural)
generateIndexOf (Wrapper _ l w _) = do
  x <- choose (0, toInteger l - 1)
  y <- choose (0, toInteger w - 1)
  return (naturalFromInteger x, naturalFromInteger y)


---- Ex-nihilo QuadTree generator

newtype GenTree a = Generated (QuadTree a)

instance Show a => Show (GenTree a) where
  show (Generated qt) = show qt

smallestDepth :: (Natural, Natural) -> Natural
smallestDepth (x,y) = depth
  where (depth, _)         = smallestPower
        Just smallestPower = find bigEnough powersZip
        bigEnough (_, e)   = e >= max x y
        powersZip          = zip [0..] $ iterate (* 2) 1

instance (Eq a, Arbitrary a) => Arbitrary (GenTree a) where
  arbitrary = do
    Positive len <- arbitrary
    Positive wid <- arbitrary
    let depth = smallestDepth (len, wid)
    tree <- generateQuadrant depth

    return . Generated $ Wrapper tree len wid depth

generateQuadrant :: (Eq a, Arbitrary a) => Natural -> Gen (Quadrant a)
generateQuadrant 0 = generateLeaf
generateQuadrant n = oneof [generateLeaf, generateNode (n - 1)]

generateLeaf :: Arbitrary a => Gen (Quadrant a)
generateLeaf = Leaf <$> arbitrary

generateNode :: (Eq a, Arbitrary a) => Natural -> Gen (Quadrant a)
generateNode n = do
  xs <- replicateM 4 (generateQuadrant n) `suchThat` (not . equalLeaves)
  let [a,b,c,d] = xs
  return (Node a b c d)
    where equalLeaves :: Eq a => [Quadrant a] -> Bool
          equalLeaves [Leaf a, Leaf b, Leaf c, Leaf d] = a == b && b == c && c == d
          equalLeaves _                                = False


-- Ex-nihilo Quadrant generator

instance (Eq a, Arbitrary a) => Arbitrary (Quadrant a) where
  arbitrary = do
    NonNegative depth <- arbitrary
    generateQuadrant depth

---- General index generator

-- Ideally, we'd be able to generate random dimensionally valid lenses as
-- part of the arguments to property functions that take quadtrees.
-- But we'd need dependent types for that, so we're just going to generate
-- independent random lenses and only test the ones that would work with
-- the tree.

newtype Index = MkIndex (Natural, Natural)

instance Arbitrary Natural where
  arbitrary = do
    NonNegative x <- arbitrary
    return $ naturalFromInteger x

instance Arbitrary Index where
  arbitrary = do
    NonNegative x <- arbitrary
    NonNegative y <- arbitrary
    return $ MkIndex (x,y)

instance Show Index where
  show (MkIndex index) = show index

outOfBounds :: (Natural, Natural) -> QuadTree a -> Bool
outOfBounds (x,y) (Wrapper _ l w _) = x < 0 || y < 0
                         || x >= l
                         || y >= w

validIndexOf :: (Natural, Natural) -> QuadTree a -> Bool
validIndexOf l x = not $ outOfBounds l x

---- Test things

prop_getcreate :: Index -> Bool -> Index -> Property
prop_getcreate (MkIndex size) v (MkIndex loc) =
  fst loc < fst size && snd loc < snd size ==>
    getLocation loc (makeTree size v) == v

prop_getset :: GenTree Bool -> Bool -> Index -> Property
prop_getset (Generated qt) v (MkIndex loc) =
  loc `validIndexOf` qt  ==>
    getLocation loc (setLocation loc v qt) == v

prop_getset_other :: GenTree Bool -> Bool -> Index -> Index -> Property
prop_getset_other (Generated qt) v (MkIndex loc) (MkIndex otherloc) =
  loc `validIndexOf` qt && otherloc `validIndexOf` qt && loc /= otherloc ==>
    getLocation otherloc (setLocation loc v qt) == getLocation otherloc qt

prop_getmap :: GenTree Bool -> Index -> Property
prop_getmap (Generated qt) (MkIndex loc) =
  loc `validIndexOf` qt  ==>
    getLocation loc (mapLocation loc not qt) /= getLocation loc qt

prop_getmap_other :: GenTree Bool -> Index -> Index -> Property
prop_getmap_other (Generated qt) (MkIndex loc) (MkIndex otherloc) =
  loc `validIndexOf` qt && otherloc `validIndexOf` qt && loc /= otherloc ==>
    getLocation otherloc (mapLocation loc not qt) == getLocation otherloc qt

prop_iscompressed_make :: GenTree Bool -> Bool
prop_iscompressed_make (Generated qt) = isCompressed qt

prop_iscompressed_set :: GenTree Bool -> Bool -> Index -> Property
prop_iscompressed_set (Generated qt) v (MkIndex loc) =
  loc `validIndexOf` qt  ==>
    isCompressed (setLocation loc v qt)

prop_iscompressed_map :: GenTree Bool -> Index -> Property
prop_iscompressed_map (Generated qt) (MkIndex loc) =
  loc `validIndexOf` qt  ==>
    isCompressed (mapLocation loc not qt)

isCompressed :: Eq a => QuadTree a -> Bool
isCompressed (Wrapper qd _ _ _) = isCompressedSub qd where
  isCompressedSub :: Eq a => Quadrant a -> Bool
  isCompressedSub (Node (Leaf a) (Leaf b) (Leaf c) (Leaf d)) = not (a == b && b == c && c == d)
  isCompressedSub (Node a b c d) = isCompressedSub a && isCompressedSub b && isCompressedSub c && isCompressedSub d
  isCompressedSub (Leaf _) = True

---- Collate and run tests:

return [] -- Template Haskell splice. See QuickCheck hackage docs.

args :: Args
args = stdArgs
  {
    maxSize = 1000,
    maxSuccess = 1000,
    maxDiscardRatio = 100 -- Raise discard ratio a bit
  }

runTests :: IO Bool
runTests = $(forAllProperties) (quickCheckWithResult args)

main :: IO ()
main = do
  allClear <- runTests
  if allClear
    then exitSuccess
    else exitFailure
