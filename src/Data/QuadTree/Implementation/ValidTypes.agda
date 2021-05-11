module Data.QuadTree.Implementation.ValidTypes where

open import Haskell.Prelude renaming (zero to Z; suc to S)
open import Data.Lens.Lens
open import Data.Logic
open import Data.QuadTree.Implementation.Definition

{-# FOREIGN AGDA2HS
{-# LANGUAGE Safe #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Rank2Types #-}
import Data.Nat
import Data.Lens.Lens
import Data.Logic

import Data.QuadTree.Implementation.Definition
#-}

---- Valid types

-- Calculates the depth of a quadrant
depth : {t : Set} -> Quadrant t -> Nat
depth (Leaf x) = 0
depth (Node a b c d) = 1 + max4 (depth a) (depth b) (depth c) (depth d)
{-# COMPILE AGDA2HS depth #-}

-- Calculates the maximum legal depth of a quadtree
maxDepth : {t : Set} -> QuadTree t -> Nat
maxDepth (Wrapper (w , h) _) = log2up (max w h)
{-# COMPILE AGDA2HS maxDepth #-}

-- Converts a tree to its root quadrant
treeToQuadrant : {t : Set} -> QuadTree t -> Quadrant t
treeToQuadrant (Wrapper _ qd) = qd
{-# COMPILE AGDA2HS treeToQuadrant #-}

-- Checks whether a quadrant is compressed
isCompressed : {t : Set} -> {{eqT : Eq t}} -> Quadrant t -> Bool
isCompressed (Leaf _) = true
isCompressed (Node (Leaf a) (Leaf b) (Leaf c) (Leaf d)) = not (a == b && b == c && c == d)
isCompressed (Node a b c d) = isCompressed a && isCompressed b && isCompressed c && isCompressed d
{-# COMPILE AGDA2HS isCompressed #-}

-- Checks whether the invariants of a quadrant hold
isValid : {t : Set} -> {{eqT : Eq t}} -> (dep : Nat) -> Quadrant t -> Bool
isValid dep qd = depth qd <= dep && isCompressed qd
{-# COMPILE AGDA2HS isValid #-}

-- A type that represents a valid quadrant
data VQuadrant (t : Set) {{eqT : Eq t}} {dep : Nat} : Set where
  CVQuadrant : (qd : Quadrant t) -> {.(IsTrue (isValid dep qd))} -> VQuadrant t {dep}
{-# FOREIGN AGDA2HS
newtype VQuadrant t = CVQuadrant (Quadrant t)
#-}

-- A type that represents a valid quadtree
data VQuadTree (t : Set) {{eqT : Eq t}} {dep : Nat} : Set where
  CVQuadTree : (qt : QuadTree t) -> {.(IsTrue (isValid dep (treeToQuadrant qt)))} -> {.(IsTrue (dep == maxDepth qt))} -> VQuadTree t {dep}
{-# FOREIGN AGDA2HS
newtype VQuadTree t = CVQuadTree (QuadTree t)
#-}

qtToSafe : {t : Set} {{eqT : Eq t}} {dep : Nat}
  -> (qt : QuadTree t) -> {.(IsTrue (isValid dep (treeToQuadrant qt)))} -> {.(IsTrue (dep == maxDepth qt))} 
  -> VQuadTree t {maxDepth qt}
qtToSafe {dep = dep} qt {p} {q} = CVQuadTree qt {useEq (cong (λ g -> isValid g (treeToQuadrant qt)) (eqToEquiv dep (maxDepth qt) q)) p} {eqReflexivity (maxDepth qt)}
{-# COMPILE AGDA2HS qtToSafe #-}

qtFromSafe : {t : Set} {{eqT : Eq t}} -> {dep : Nat} -> VQuadTree t {dep} -> QuadTree t
qtFromSafe (CVQuadTree qt) = qt
{-# COMPILE AGDA2HS qtFromSafe #-}