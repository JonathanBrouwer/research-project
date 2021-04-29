module Data.QuadTree.InternalAgda where

open import Haskell.Prelude renaming (zero to Z; suc to S)
open import Data.QuadTree.Lens
open import Data.QuadTree.Logic
open import Data.QuadTree.PropDepthRelation

{-# FOREIGN AGDA2HS
{-# LANGUAGE Safe #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Rank2Types #-}
import Data.Nat
import Data.QuadTree.Lens
import Data.QuadTree.Logic
#-}

---- Quadrants

data Quadrant (t : Set) : Set where
  Leaf : t -> Quadrant t
  Node : Quadrant t -> Quadrant t -> Quadrant t -> Quadrant t -> Quadrant t
{-# COMPILE AGDA2HS Quadrant deriving (Show, Eq) #-}

instance
  quadrantFunctor : Functor Quadrant
  quadrantFunctor .fmap fn (Leaf x) = Leaf (fn x)
  quadrantFunctor .fmap fn (Node a b c d) = Node (fmap fn a) (fmap fn b) (fmap fn c) (fmap fn d)
{-# COMPILE AGDA2HS quadrantFunctor #-}

---- QuadTree

data QuadTree (t : Set) : Set where
  -- wrappedTree, (width x height)
  Wrapper : (Nat × Nat) -> Quadrant t -> QuadTree t
{-# COMPILE AGDA2HS QuadTree deriving (Show, Eq) #-}

instance
  quadTreeFunctor : Functor QuadTree
  quadTreeFunctor .fmap fn (Wrapper (w , h) q) = Wrapper (w , h) (fmap fn q) 
{-# COMPILE AGDA2HS quadTreeFunctor #-}

---- Valid Quadrant

depth : {t : Set} -> Quadrant t -> Nat
depth (Leaf x) = 0
depth (Node a b c d) = 1 + max4 (depth a) (depth b) (depth c) (depth d)
{-# COMPILE AGDA2HS depth #-}

maxDepth : {t : Set} -> QuadTree t -> Nat
maxDepth (Wrapper (w , h) _) = log2up (max w h)
{-# COMPILE AGDA2HS maxDepth #-}

isCompressed : {t : Set} -> {{eqT : Eq t}} -> Quadrant t -> Bool
isCompressed (Leaf _) = true
isCompressed (Node (Leaf a) (Leaf b) (Leaf c) (Leaf d)) = not (a == b && b == c && c == d)
isCompressed (Node a b c d) = isCompressed a && isCompressed b && isCompressed c && isCompressed d
{-# COMPILE AGDA2HS isCompressed #-}

isValid : {t : Set} -> {{eqT : Eq t}} -> (dep : Nat) -> Quadrant t -> Bool
isValid dep qd = (depth qd <= dep) && isCompressed qd
{-# COMPILE AGDA2HS isValid #-}

data VQuadrant (t : Set) {{eqT : Eq t}} {dep : Nat} : Set where
  CVQuadrant : (qd : Quadrant t) -> {.(IsTrue (isValid dep qd))} -> VQuadrant t {dep}
{-# FOREIGN AGDA2HS
newtype VQuadrant t = CVQuadrant (Quadrant t)
#-}

---- Lenses

lensWrappedTree : {t : Set} {{eqT : Eq t}}
  -> CLens (QuadTree t) (Quadrant t)
lensWrappedTree fun (Wrapper (w , h) qd) = 
  fmap 
    (λ qd → (Wrapper (w , h) qd))
    (fun qd)
{-# COMPILE AGDA2HS lensWrappedTree #-}

lensLeaf : {t : Set} {{eqT : Eq t}}
  -> CLens (Quadrant t) t
lensLeaf f (Leaf v) = fmap Leaf (f v)
lensLeaf f (Node a b c d) = impossible --TODO: Impossible
{-# COMPILE AGDA2HS lensLeaf #-}


propDepthRelationEq : {t : Set} -> (a b c d : Quadrant t) -> depth (Node a b c d) ≡ S (max4 (depth a) (depth b) (depth c) (depth d))
propDepthRelationEq a b c d = refl

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

propCompressedRelation : {t : Set} {{eqT : Eq t}} -> {a b c d : Quadrant t}
  -> IsTrue (isCompressed (Node a b c d))
  -> IsTrue (isCompressed a && isCompressed b && isCompressed c && isCompressed d)
propCompressedRelation {_} {Leaf a} {Leaf b} {Leaf c} {Leaf d} p = IsTrue.itsTrue
propCompressedRelation {_} {Node _ _ _ _} {b} {c} {d} p = p
propCompressedRelation {_} {Leaf _} {Node _ _ _ _} {c} {d} p = p
propCompressedRelation {_} {Leaf _} {Leaf _} {Node _ _ _ _} {d} p = p
propCompressedRelation {_} {Leaf _} {Leaf _} {Leaf _} {Node _ _ _ _} p = p

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

aSub : {t : Set} {{eqT : Eq t}} -> {dep : Nat} -> (a b c d : Quadrant t) 
  -> IsTrue (isValid (S dep) (Node a b c d)) -> IsTrue (isValid (dep) a)
aSub {_} {dep} a b c d p = andCombine 
  -- Convert depth proof using propDepthRelationLte
  (andFst $ andFst {(depth a <= dep && depth b <= dep)} $ useEq (sym (propDepthRelationLte a b c d dep)) (andFst p))
  -- Convert compressed proof using propCompressedRelation
  (and1 {isCompressed a} {isCompressed b} {isCompressed c} {isCompressed d} (propCompressedRelation {_} {a} (andSnd p)))

bSub : {t : Set} {{eqT : Eq t}} -> {dep : Nat} -> (a b c d : Quadrant t) 
  -> IsTrue (isValid (S dep) (Node a b c d)) -> IsTrue (isValid (dep) b)
bSub {_} {dep} a b c d p = andCombine 
  -- Convert depth proof using propDepthRelationLte
  (andSnd $ andFst {(depth a <= dep && depth b <= dep)} $ useEq (sym (propDepthRelationLte a b c d dep)) (andFst p))
  -- Convert compressed proof using propCompressedRelation
  (and2 {isCompressed a} {isCompressed b} {isCompressed c} {isCompressed d} (propCompressedRelation {_} {a} (andSnd p)))

cSub : {t : Set} {{eqT : Eq t}} -> {dep : Nat} -> (a b c d : Quadrant t) 
  -> IsTrue (isValid (S dep) (Node a b c d)) -> IsTrue (isValid (dep) c)
cSub {_} {dep} a b c d p = andCombine 
  -- Convert depth proof using propDepthRelationLte
  (andFst $ andSnd {(depth a <= dep && depth b <= dep)} $ useEq (sym (propDepthRelationLte a b c d dep)) (andFst p))
  -- Convert compressed proof using propCompressedRelation
  (and3 {isCompressed a} {isCompressed b} {isCompressed c} {isCompressed d} (propCompressedRelation {_} {a} (andSnd p)))

dSub : {t : Set} {{eqT : Eq t}} -> {dep : Nat} -> (a b c d : Quadrant t) 
  -> IsTrue (isValid (S dep) (Node a b c d)) -> IsTrue (isValid (dep) d)
dSub {_} {dep} a b c d p = andCombine 
  -- Convert depth proof using propDepthRelationLte
  (andSnd $ andSnd {(depth a <= dep && depth b <= dep)} $ useEq (sym (propDepthRelationLte a b c d dep)) (andFst p))
  -- Convert compressed proof using propCompressedRelation
  (and4 {isCompressed a} {isCompressed b} {isCompressed c} {isCompressed d} (propCompressedRelation {_} {a} (andSnd p)))

lensA : 
  {t : Set} {{eqT : Eq t}}
  -> {dep : Nat}
  -> CLens (VQuadrant t {S dep}) (VQuadrant t {dep})
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

-- lensB : 
--   {t : Set} {{eqT : Eq t}}
--   -> CLens (Quadrant t) (Quadrant t)
-- lensB f l@(Leaf v) = 
--   fmap (λ x -> combine l x l l ) (f l)
-- lensB f (Node a b c d) = 
--   fmap (λ x -> combine a x c d ) (f b)
-- {-# COMPILE AGDA2HS lensB #-}

-- lensC : 
--   {t : Set} {{eqT : Eq t}}
--   -> CLens (Quadrant t) (Quadrant t)
-- lensC f l@(Leaf v) = 
--   fmap (λ x -> combine l l x l ) (f l)
-- lensC f (Node a b c d) = 
--   fmap (λ x -> combine a b x d ) (f c)
-- {-# COMPILE AGDA2HS lensC #-}

-- lensD : 
--   {t : Set} {{eqT : Eq t}}
--   -> CLens (Quadrant t) (Quadrant t)
-- lensD f l@(Leaf v) = 
--   fmap (λ x -> combine l l l x ) (f l)
-- lensD f (Node a b c d) = 
--   fmap (λ x -> combine a b c x ) (f d)
-- {-# COMPILE AGDA2HS lensD #-}

-- ---- Data access

-- go : {t : Set} {{eqT : Eq t}}
--   -> (Nat × Nat) -> (dep : Nat)
--   -> CLens (Quadrant t) t
-- go _ Z = lensLeaf
-- go (x , y) (S deps) = ifc (y < mid) 
--   then (ifc x < mid 
--     then (             lensA ∘ go (x                 , y                ) deps)
--     else (λ {{xgt}} -> lensB ∘ go (_-_ x mid {{xgt}} , y                ) deps))
--   else (λ {{ygt}} -> (ifc x < mid
--     then (             lensC ∘ go (x                 , _-_ y mid {{ygt}}) deps)
--     else (λ {{xgt}} -> lensD ∘ go (_-_ x mid {{xgt}} , _-_ y mid {{ygt}}) deps)))
--   where
--     mid = pow 2 deps
-- {-# COMPILE AGDA2HS go #-}

-- ---- Agda safe functions

-- makeTree : {t : Set} {{eqT : Eq t}} -> (size : Nat × Nat) -> (v : t) -> QuadTree t
-- makeTree (w , h) v = Wrapper (w , h) (Leaf v) 
-- {-# COMPILE AGDA2HS makeTree #-}

-- atLocation : {t : Set} {{eqT : Eq t}}
--   -> (Nat × Nat)
--   -> CLens (QuadTree t) t
-- atLocation index f qt = (lensWrappedTree ∘ (go index (maxDepth qt))) f qt
-- {-# COMPILE AGDA2HS atLocation #-}

-- getLocation : {t : Set} {{eqT : Eq t}}
--   -> (Nat × Nat)
--   -> QuadTree t -> t
-- getLocation index = view (atLocation index)
-- {-# COMPILE AGDA2HS getLocation #-}

-- setLocation : {t : Set} {{eqT : Eq t}}
--   -> (Nat × Nat)
--   -> t -> QuadTree t -> QuadTree t
-- setLocation index = set (atLocation index)
-- {-# COMPILE AGDA2HS setLocation #-}

-- mapLocation : {t : Set} {{eqT : Eq t}}
--   -> (Nat × Nat)
--   -> (t -> t) -> QuadTree t -> QuadTree t
-- mapLocation index = over (atLocation index)
-- {-# COMPILE AGDA2HS mapLocation #-}