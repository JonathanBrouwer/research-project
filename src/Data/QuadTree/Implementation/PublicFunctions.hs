{-# LANGUAGE Safe #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Rank2Types #-}

module Data.QuadTree.Implementation.PublicFunctions where




import Data.Nat
import Data.Lens.Lens
import Data.Logic

import Data.QuadTree.Implementation.Definition
import Data.QuadTree.Implementation.ValidTypes
import Data.QuadTree.Implementation.QuadrantLenses
import Data.QuadTree.Implementation.DataLenses
import Data.QuadTree.Implementation.SafeFunctions

makeTree :: Eq t => (Nat, Nat) -> t -> QuadTree t
makeTree size v = qtFromSafe $ makeTreeSafe size v

getLocation :: Eq t => (Nat, Nat) -> QuadTree t -> t
getLocation loc qt
  = getLocationSafe loc (maxDepth qt) (qtToSafe qt)

setLocation :: Eq t => (Nat, Nat) -> t -> QuadTree t -> QuadTree t
setLocation loc v qt
  = qtFromSafe $ setLocationSafe loc (maxDepth qt) v (qtToSafe qt)

mapLocation ::
              Eq t => (Nat, Nat) -> (t -> t) -> QuadTree t -> QuadTree t
mapLocation loc f qt
  = qtFromSafe $ mapLocationSafe loc (maxDepth qt) f (qtToSafe qt)

