module Data.QuadTree.Implementation.QuadrantLenses where

open import Haskell.Prelude renaming (zero to Z; suc to S)
open import Data.Lens.Lens
open import Data.Logic
open import Data.QuadTree.Implementation.PropDepthRelation
open import Data.QuadTree.Implementation.Definition
open import Data.QuadTree.Implementation.ValidTypes

{-# FOREIGN AGDA2HS
{-# LANGUAGE Safe #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Rank2Types #-}
import Data.Nat
import Data.Lens.Lens
import Data.Logic

import Data.QuadTree.Implementation.Definition
import Data.QuadTree.Implementation.ValidTypes
#-}

---- Lenses

-- Lenses into a leaf of a depth zero quadrant
lensLeaf : {t : Set} {{eqT : Eq t}}
  -> Lens (VQuadrant t {0}) t
lensLeaf f (CVQuadrant (Leaf v)) = fmap (λ x -> CVQuadrant (Leaf x) {IsTrue.itsTrue}) (f v)
{-# COMPILE AGDA2HS lensLeaf #-}

-- A proof of the depth relation of a node and its children
propDepthRelationLte : {t : Set} -> (a b c d : Quadrant t) -> (dep : Nat) 
  -> ((depth a <= dep && depth b <= dep) && (depth c <= dep && depth d <= dep)) ≡ (depth (Node a b c d) <= (S dep))
propDepthRelationLte a b c d dep =
  begin 
    ((depth a <= dep && depth b <= dep) && (depth c <= dep && depth d <= dep))
  =⟨ propMaxLte4 (depth a) (depth b) (depth c) (depth d) dep ⟩
    (max (max (depth a) (depth b)) (max (depth c) (depth d)) <= dep)
  =⟨⟩
    (depth (Node a b c d) <= S dep)
  end

-- A proof of the compressed relation of a node and its children
propCompressedRelation : {t : Set} {{eqT : Eq t}} -> {a b c d : Quadrant t}
  -> IsTrue (isCompressed (Node a b c d))
  -> IsTrue (isCompressed a && isCompressed b && isCompressed c && isCompressed d)
propCompressedRelation {_} {Leaf a} {Leaf b} {Leaf c} {Leaf d} p = IsTrue.itsTrue
propCompressedRelation {_} {Node _ _ _ _} {b} {c} {d} p = p
propCompressedRelation {_} {Leaf _} {Node _ _ _ _} {c} {d} p = p
propCompressedRelation {_} {Leaf _} {Leaf _} {Node _ _ _ _} {d} p = p
propCompressedRelation {_} {Leaf _} {Leaf _} {Leaf _} {Node _ _ _ _} p = p

-- Combine 4 valid quadrants to a new valid quadrant
combine : {t : Set} {{eqT : Eq t}}
  -> {dep : Nat}
  -> (a b c d : VQuadrant t {dep})
  -> VQuadrant t {S dep}
combine {t} {dep} (CVQuadrant a@(Leaf va) {pa}) (CVQuadrant b@(Leaf vb) {pb}) (CVQuadrant c@(Leaf vc) {pc}) (CVQuadrant d@(Leaf vd) {pd})
  = ifc (va == vb && vb == vc && vc == vd)
    then CVQuadrant a {IsTrue.itsTrue}
    else (λ {{pn}} -> CVQuadrant (Node a b c d) {andCombine (zeroLteAny dep) (falseToNotTrue $ pn)})
-- The next 4 cases are all identical, but I could not figure out another way to convince agda
combine {t} {dep} (CVQuadrant a@(Node v1 v2 v3 v4) {pa}) (CVQuadrant b {pb}) (CVQuadrant c {pc}) (CVQuadrant d {pd}) 
  = CVQuadrant (Node a b c d) {andCombine 
    (useEq (propDepthRelationLte a b c d dep) ((propIsTrueCombine4 (andFst {depth a <= dep} pa) (andFst {depth b <= dep} pb) (andFst {depth c <= dep} pc) (andFst {depth d <= dep} pd)))) 
    (propIsTrueCombine4Alt (andSnd {depth a <= dep} pa) (andSnd {depth b <= dep} pb) (andSnd {depth c <= dep} pc) (andSnd {depth d <= dep} pd))
  }
combine {t} {dep} (CVQuadrant a@(Leaf va) {pa}) (CVQuadrant b@(Node v1 v2 v3 v4) {pb}) (CVQuadrant c {pc}) (CVQuadrant d {pd}) 
  = CVQuadrant (Node a b c d) {andCombine 
    (useEq (propDepthRelationLte a b c d dep) ((propIsTrueCombine4 (andFst {depth a <= dep} pa) (andFst {depth b <= dep} pb) (andFst {depth c <= dep} pc) (andFst {depth d <= dep} pd)))) 
    (propIsTrueCombine4Alt (andSnd {depth a <= dep} pa) (andSnd {depth b <= dep} pb) (andSnd {depth c <= dep} pc) (andSnd {depth d <= dep} pd))
  }
combine {t} {dep} (CVQuadrant a@(Leaf va) {pa}) (CVQuadrant b@(Leaf vb) {pb}) (CVQuadrant c@(Node v1 v2 v3 v4) {pc}) (CVQuadrant d {pd}) 
  = CVQuadrant (Node a b c d) {andCombine 
    (useEq (propDepthRelationLte a b c d dep) ((propIsTrueCombine4 (andFst {depth a <= dep} pa) (andFst {depth b <= dep} pb) (andFst {depth c <= dep} pc) (andFst {depth d <= dep} pd)))) 
    (propIsTrueCombine4Alt (andSnd {depth a <= dep} pa) (andSnd {depth b <= dep} pb) (andSnd {depth c <= dep} pc) (andSnd {depth d <= dep} pd))
  }
combine {t} {dep} (CVQuadrant a@(Leaf va) {pa}) (CVQuadrant b@(Leaf vb) {pb}) (CVQuadrant c@(Leaf vc) {pc}) (CVQuadrant d@(Node v1 v2 v3 v4) {pd}) 
  = CVQuadrant (Node a b c d) {andCombine 
    (useEq (propDepthRelationLte a b c d dep) ((propIsTrueCombine4 (andFst {depth a <= dep} pa) (andFst {depth b <= dep} pb) (andFst {depth c <= dep} pc) (andFst {depth d <= dep} pd)))) 
    (propIsTrueCombine4Alt (andSnd {depth a <= dep} pa) (andSnd {depth b <= dep} pb) (andSnd {depth c <= dep} pc) (andSnd {depth d <= dep} pd))
  }
{-# COMPILE AGDA2HS combine #-}

-- Goes from a valid quadrant to its a subquadrant
aSub : {t : Set} {{eqT : Eq t}} -> {dep : Nat} -> (a b c d : Quadrant t) 
  -> IsTrue (isValid (S dep) (Node a b c d)) -> IsTrue (isValid (dep) a)
aSub {_} {dep} a b c d p = andCombine 
  -- Convert depth proof using propDepthRelationLte
  (andFst $ andFst {(depth a <= dep && depth b <= dep)} $ useEq (sym (propDepthRelationLte a b c d dep)) (andFst p))
  -- Convert compressed proof using propCompressedRelation
  (and1 {isCompressed a} {isCompressed b} {isCompressed c} {isCompressed d} (propCompressedRelation {_} {a} (andSnd p)))

-- Goes from a valid quadrant to its b subquadrant
bSub : {t : Set} {{eqT : Eq t}} -> {dep : Nat} -> (a b c d : Quadrant t) 
  -> IsTrue (isValid (S dep) (Node a b c d)) -> IsTrue (isValid (dep) b)
bSub {_} {dep} a b c d p = andCombine 
  -- Convert depth proof using propDepthRelationLte
  (andSnd $ andFst {(depth a <= dep && depth b <= dep)} $ useEq (sym (propDepthRelationLte a b c d dep)) (andFst p))
  -- Convert compressed proof using propCompressedRelation
  (and2 {isCompressed a} {isCompressed b} {isCompressed c} {isCompressed d} (propCompressedRelation {_} {a} (andSnd p)))

-- Goes from a valid quadrant to its c subquadrant
cSub : {t : Set} {{eqT : Eq t}} -> {dep : Nat} -> (a b c d : Quadrant t) 
  -> IsTrue (isValid (S dep) (Node a b c d)) -> IsTrue (isValid (dep) c)
cSub {_} {dep} a b c d p = andCombine 
  -- Convert depth proof using propDepthRelationLte
  (andFst $ andSnd {(depth a <= dep && depth b <= dep)} $ useEq (sym (propDepthRelationLte a b c d dep)) (andFst p))
  -- Convert compressed proof using propCompressedRelation
  (and3 {isCompressed a} {isCompressed b} {isCompressed c} {isCompressed d} (propCompressedRelation {_} {a} (andSnd p)))

-- Goes from a valid quadrant to its d subquadrant
dSub : {t : Set} {{eqT : Eq t}} -> {dep : Nat} -> (a b c d : Quadrant t) 
  -> IsTrue (isValid (S dep) (Node a b c d)) -> IsTrue (isValid (dep) d)
dSub {_} {dep} a b c d p = andCombine 
  -- Convert depth proof using propDepthRelationLte
  (andSnd $ andSnd {(depth a <= dep && depth b <= dep)} $ useEq (sym (propDepthRelationLte a b c d dep)) (andFst p))
  -- Convert compressed proof using propCompressedRelation
  (and4 {isCompressed a} {isCompressed b} {isCompressed c} {isCompressed d} (propCompressedRelation {_} {a} (andSnd p)))

-- Lens into the a subquadrant
lensA : 
  {t : Set} {{eqT : Eq t}}
  -> {dep : Nat}
  -> Lens (VQuadrant t {S dep}) (VQuadrant t {dep})
lensA {_} {dep} f (CVQuadrant (Leaf v) {p}) = 
  let sub = CVQuadrant (Leaf v) {andCombine (zeroLteAny dep) IsTrue.itsTrue}
  in fmap (λ x -> combine x sub sub sub ) (f sub)
lensA {_} {dep} f (CVQuadrant (Node a b c d) {p}) = 
  let 
    sA = CVQuadrant a {aSub a b c d p}
    sB = CVQuadrant b {bSub a b c d p}
    sC = CVQuadrant c {cSub a b c d p}
    sD = CVQuadrant d {dSub a b c d p}
  in fmap (λ x -> combine x sB sC sD ) (f sA)
{-# COMPILE AGDA2HS lensA #-}

-- Lens into the b subquadrant
lensB : 
  {t : Set} {{eqT : Eq t}}
  -> {dep : Nat}
  -> Lens (VQuadrant t {S dep}) (VQuadrant t {dep})
lensB {_} {dep} f (CVQuadrant (Leaf v) {p}) = 
  let sub = CVQuadrant (Leaf v) {andCombine (zeroLteAny dep) IsTrue.itsTrue}
  in fmap (λ x -> combine sub x sub sub ) (f sub)
lensB {_} {dep} f (CVQuadrant (Node a b c d) {p}) = 
  let 
    sA = CVQuadrant a {aSub a b c d p}
    sB = CVQuadrant b {bSub a b c d p}
    sC = CVQuadrant c {cSub a b c d p}
    sD = CVQuadrant d {dSub a b c d p}
  in fmap (λ x -> combine sA x sC sD ) (f sB)
{-# COMPILE AGDA2HS lensB #-}

-- Lens into the c subquadrant
lensC : 
  {t : Set} {{eqT : Eq t}}
  -> {dep : Nat}
  -> Lens (VQuadrant t {S dep}) (VQuadrant t {dep})
lensC {_} {dep} f (CVQuadrant (Leaf v) {p}) = 
  let sub = CVQuadrant (Leaf v) {andCombine (zeroLteAny dep) IsTrue.itsTrue}
  in fmap (λ x -> combine sub sub x sub ) (f sub)
lensC {_} {dep} f (CVQuadrant (Node a b c d) {p}) = 
  let 
    sA = CVQuadrant a {aSub a b c d p}
    sB = CVQuadrant b {bSub a b c d p}
    sC = CVQuadrant c {cSub a b c d p}
    sD = CVQuadrant d {dSub a b c d p}
  in fmap (λ x -> combine sA sB x sD ) (f sC)
{-# COMPILE AGDA2HS lensC #-}

-- Lens into the d subquadrant
lensD : 
  {t : Set} {{eqT : Eq t}}
  -> {dep : Nat}
  -> Lens (VQuadrant t {S dep}) (VQuadrant t {dep})
lensD {_} {dep} f (CVQuadrant (Leaf v) {p}) = 
  let sub = CVQuadrant (Leaf v) {andCombine (zeroLteAny dep) IsTrue.itsTrue}
  in fmap (λ x -> combine sub sub sub x ) (f sub)
lensD {_} {dep} f (CVQuadrant (Node a b c d) {p}) = 
  let 
    sA = CVQuadrant a {aSub a b c d p}
    sB = CVQuadrant b {bSub a b c d p}
    sC = CVQuadrant c {cSub a b c d p}
    sD = CVQuadrant d {dSub a b c d p}
  in fmap (λ x -> combine sA sB sC x ) (f sD)
{-# COMPILE AGDA2HS lensD #-}