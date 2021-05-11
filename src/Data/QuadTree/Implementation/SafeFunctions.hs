{-# LANGUAGE Safe #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Rank2Types #-}

module Data.QuadTree.Implementation.SafeFunctions where




import Data.Nat
import Data.Lens.Lens
import Data.Logic

import Data.QuadTree.Implementation.Definition
import Data.QuadTree.Implementation.ValidTypes
import Data.QuadTree.Implementation.QuadrantLenses
import Data.QuadTree.Implementation.DataLenses

makeTreeSafe :: Eq t => (Nat, Nat) -> t -> VQuadTree t
makeTreeSafe (w, h) v = CVQuadTree (Wrapper (w, h) (Leaf v))

getLocationSafe :: Eq t => (Nat, Nat) -> Nat -> VQuadTree t -> t
getLocationSafe index dep vqt = view (atLocation index dep) vqt

setLocationSafe ::
                  Eq t => (Nat, Nat) -> Nat -> t -> VQuadTree t -> VQuadTree t
setLocationSafe index dep v vqt = set (atLocation index dep) v vqt

mapLocationSafe ::
                  Eq t => (Nat, Nat) -> Nat -> (t -> t) -> VQuadTree t -> VQuadTree t
mapLocationSafe index dep f vqt = over (atLocation index dep) f vqt

