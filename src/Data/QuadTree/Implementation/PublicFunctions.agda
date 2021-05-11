module Data.QuadTree.Implementation.PublicFunctions where

open import Haskell.Prelude renaming (zero to Z; suc to S)
open import Data.Lens.Lens
open import Data.Logic
open import Data.QuadTree.Implementation.PropDepthRelation
open import Data.QuadTree.Implementation.Definition
open import Data.QuadTree.Implementation.ValidTypes
open import Data.QuadTree.Implementation.QuadrantLenses
open import Data.QuadTree.Implementation.DataLenses
open import Data.QuadTree.Implementation.SafeFunctions

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
import Data.QuadTree.Implementation.SafeFunctions
#-}

---- Unsafe functions (Original)

makeTree : {t : Set} {{eqT : Eq t}} -> (size : Nat × Nat) -> t -> QuadTree t
makeTree size v = qtFromSafe $ makeTreeSafe size v
{-# COMPILE AGDA2HS makeTree #-}

getLocation : {t : Set} {{eqT : Eq t}} 
  -> (loc : Nat × Nat) -> {dep : Nat}
  -> (qt : QuadTree t) 
  -> {.(IsTrue (isInsideQuadTree loc qt))}
  -> {.(IsTrue (isValid dep (treeToQuadrant qt)))} -> {.(IsTrue (dep == maxDepth qt))} 
  -> t
getLocation loc qt {inside} {p} {q} = getLocationSafe loc (maxDepth qt) (qtToSafe qt {p} {q}) {inside}
{-# COMPILE AGDA2HS getLocation #-}

setLocation : {t : Set} {{eqT : Eq t}} 
  -> (loc : Nat × Nat) -> t
  -> {dep : Nat} -> (qt : QuadTree t) 
  -> {.(IsTrue (isInsideQuadTree loc qt))}
  -> {.(IsTrue (isValid dep (treeToQuadrant qt)))} -> {.(IsTrue (dep == maxDepth qt))} 
  -> QuadTree t
setLocation loc v qt {inside} {p} {q} = qtFromSafe $ setLocationSafe loc (maxDepth qt) v (qtToSafe qt {p} {q}) {inside}
{-# COMPILE AGDA2HS setLocation #-}

mapLocation : {t : Set} {{eqT : Eq t}} 
  -> (loc : Nat × Nat) -> (t -> t) 
  -> {dep : Nat} -> (qt : QuadTree t) 
  -> {.(IsTrue (isInsideQuadTree loc qt))}
  -> {.(IsTrue (isValid dep (treeToQuadrant qt)))} -> {.(IsTrue (dep == maxDepth qt))} 
  -> QuadTree t
mapLocation loc f qt {inside} {p} {q} = qtFromSafe $ mapLocationSafe loc (maxDepth qt) f (qtToSafe qt {p} {q}) {inside}
{-# COMPILE AGDA2HS mapLocation #-}