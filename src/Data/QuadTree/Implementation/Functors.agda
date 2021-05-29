module Data.QuadTree.Implementation.Functors where

open import Haskell.Prelude renaming (zero to Z; suc to S)
open import Data.Lens.Lens
open import Data.Logic
open import Data.QuadTree.Implementation.Definition
open import Data.QuadTree.Implementation.ValidTypes
open import Data.QuadTree.Implementation.QuadrantLenses

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
#-}

record FunctorEq (f : (y : Set) -> {{ eqT : Eq y }} -> Set) : Set₁ where
  field
    fmapₑ : {a b : Set} -> {{ eqA : Eq a }} {{ eqB : Eq b }} -> (a → b) → f a → f b 
open FunctorEq public
{-# COMPILE AGDA2HS FunctorEq class #-}

quadrantFunctor : (dep : Nat) -> FunctorEq (λ y -> VQuadrant y {dep})
quadrantFunctor dep .fmapₑ fn (CVQuadrant (Leaf v) {p}) = (CVQuadrant (Leaf $ fn v) {p})
quadrantFunctor (S dep) .fmapₑ fn (CVQuadrant (Node a b c d) {p}) = 
  (combine (fmapₑ (quadrantFunctor dep) fn sA) (fmapₑ (quadrantFunctor dep) fn sB) (fmapₑ (quadrantFunctor dep) fn sC) (fmapₑ (quadrantFunctor dep) fn sD)) where
  sA = CVQuadrant a {aSub a b c d p}
  sB = CVQuadrant b {bSub a b c d p}
  sC = CVQuadrant c {cSub a b c d p}
  sD = CVQuadrant d {dSub a b c d p}

toQt : {b : Set} -> {{ eqB : Eq b }}
  -> (dep w h : Nat) .(q : IsTrue (dep == log2up (if w < h then h else w))) -> VQuadrant b {dep} -> VQuadTree b {dep}
toQt dep w h q (CVQuadrant qd {p}) = CVQuadTree (Wrapper (w , h) qd) {p} {q}

quadtreeFunctor : (dep : Nat) -> FunctorEq (λ y -> VQuadTree y {dep})
quadtreeFunctor dep .fmapₑ {a} {b} fn (CVQuadTree (Wrapper (w , h) qd) {p} {q}) =
  toQt dep w h q (fmapₑ (quadrantFunctor dep) fn (CVQuadrant qd {p}))
