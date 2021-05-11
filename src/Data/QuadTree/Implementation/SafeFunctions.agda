module Data.QuadTree.Implementation.SafeFunctions where

open import Haskell.Prelude renaming (zero to Z; suc to S)
open import Data.Lens.Lens
open import Data.Logic
open import Data.QuadTree.Implementation.PropDepthRelation
open import Data.QuadTree.Implementation.Definition
open import Data.QuadTree.Implementation.ValidTypes
open import Data.QuadTree.Implementation.QuadrantLenses
open import Data.QuadTree.Implementation.DataLenses

{-# FOREIGN AGDA2HS
{-# LANGUAGE Safe #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Rank2Types #-}
import Data.Nat
import Data.Lens.Lens
import Data.Logic

import Data.QuadTree.Implementation.Definition
import Data.QuadTree.Implementation.ValidTypes
import Data.QuadTree.Implementation.QuadrantLenses
import Data.QuadTree.Implementation.DataLenses
#-}

---- Safe functions

makeTreeSafe : {t : Set} {{eqT : Eq t}} -> (size : Nat × Nat) -> (v : t) -> VQuadTree t {maxDepth $ Wrapper size (Leaf v)}
makeTreeSafe (w , h) v = CVQuadTree (Wrapper (w , h) (Leaf v)) {andCombine (zeroLteAny (log2up $ max w h)) IsTrue.itsTrue} {eqReflexivity (maxDepth $ Wrapper (w , h) (Leaf v))}
{-# COMPILE AGDA2HS makeTreeSafe #-}

getLocationSafe : {t : Set} {{eqT : Eq t}}
  -> (loc : Nat × Nat) -> (dep : Nat)
  -> (qt : VQuadTree t {dep})
  -> {.(IsTrue (isInsideQuadTree loc (qtFromSafe qt)))} 
  -> t
getLocationSafe index dep vqt {inside} = view (atLocation index dep {insideQTtoInsidePow index vqt inside}) vqt
{-# COMPILE AGDA2HS getLocationSafe #-}

setLocationSafe : {t : Set} {{eqT : Eq t}}
  -> (loc : Nat × Nat) -> (dep : Nat) 
  -> t -> (qt : VQuadTree t {dep}) 
  -> {.(IsTrue (isInsideQuadTree loc (qtFromSafe qt)))} 
  -> VQuadTree t {dep}
setLocationSafe index dep v vqt {inside} = set (atLocation index dep {insideQTtoInsidePow index vqt inside}) v vqt
{-# COMPILE AGDA2HS setLocationSafe #-}

mapLocationSafe : {t : Set} {{eqT : Eq t}}
  -> (loc : Nat × Nat) -> (dep : Nat)
  -> (t -> t) -> (qt : VQuadTree t {dep}) 
  -> {.(IsTrue (isInsideQuadTree loc (qtFromSafe qt)))} 
  -> VQuadTree t {dep}
mapLocationSafe index dep f vqt {inside} = over (atLocation index dep {insideQTtoInsidePow index vqt inside}) f vqt
{-# COMPILE AGDA2HS mapLocationSafe #-}