module Data.QuadTree.InternalAgda where

open import Haskell.Prelude
open import Data.QuadTree.Lens
open import Data.QuadTree.Logic
open import Data.QuadTree.PropDepthRelation

{-# FOREIGN AGDA2HS
{-# LANGUAGE Safe #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Rank2Types #-}
import Data.QuadTree.Lens
import Data.QuadTree.Logic
#-}

---- Quadrants

data Quadrant (t : Set) : Set where
  Leaf : t -> Quadrant t
  Node : Quadrant t -> Quadrant t -> Quadrant t -> Quadrant t -> Quadrant t
{-# COMPILE AGDA2HS Quadrant deriving (Show, Read, Eq) #-}

instance
  quadrantFunctor : Functor Quadrant
  quadrantFunctor .fmap fn (Leaf x) = Leaf (fn x)
  quadrantFunctor .fmap fn (Node a b c d) = Node (fmap fn a) (fmap fn b) (fmap fn c) (fmap fn d)
{-# COMPILE AGDA2HS quadrantFunctor #-}

---- QuadTree

data QuadTree (t : Set) : Set where
  -- wrappedTree, (width x height)
  Wrapper : Quadrant t -> (Nat × Nat) -> QuadTree t
{-# COMPILE AGDA2HS QuadTree deriving (Show, Read, Eq) #-}

instance
  quadTreeFunctor : Functor QuadTree
  quadTreeFunctor .fmap fn (Wrapper q (w , h)) = Wrapper (fmap fn q) (w , h)
{-# COMPILE AGDA2HS quadTreeFunctor #-}

---- Compressed validation

isCompressed : {t : Set} -> {{eqT : Eq t}} -> Quadrant t -> Bool
isCompressed (Leaf _) = true
isCompressed (Node (Leaf a) (Leaf b) (Leaf c) (Leaf d)) = not (a == b && b == c && c == d)
isCompressed (Node a b c d) = isCompressed a && isCompressed b && isCompressed c && isCompressed d
{-# COMPILE AGDA2HS isCompressed #-}

---- Depth validation

depth : {t : Set} -> Quadrant t -> Nat
depth (Leaf x) = 0
depth (Node a b c d) = 1 + max (max (depth a) (depth b)) (max(depth c) (depth d))
{-# COMPILE AGDA2HS depth #-}

maxDepth : {t : Set} -> QuadTree t -> Nat
maxDepth (Wrapper _ (w , h)) = log2up (max w h)
{-# COMPILE AGDA2HS maxDepth #-}

treeToQuadrant : {t : Set} -> QuadTree t -> Quadrant t
treeToQuadrant (Wrapper qd _) = qd
{-# COMPILE AGDA2HS treeToQuadrant #-}

---- Validation

isValid : {t : Set} -> {{eqT : Eq t}} -> (dep : Nat) -> Quadrant t -> Bool
isValid dep qd = (depth qd <= dep) && isCompressed qd
{-# COMPILE AGDA2HS isValid #-}

data ValidQuadrant (t : Set) {{eqT : Eq t}} {dep : Nat} : Set where
  CValidQuadrant : (qd : Quadrant t) -> {IsTrue (isValid dep qd)} -> ValidQuadrant t {dep}
{-# FOREIGN AGDA2HS
newtype ValidQuadrant t = CValidQuadrant (Quadrant t)
#-}

data ValidQuadTree (t : Set) {{eqT : Eq t}} {dep : Nat} : Set where
  CValidQuadTree : (qt : QuadTree t) -> {IsTrue (isValid dep (treeToQuadrant qt))} -> ValidQuadTree t {dep}
{-# FOREIGN AGDA2HS
newtype ValidQuadTree t = CValidQuadTree (QuadTree t)
#-}

---- Proofs about Quadrants

propDepthRelationEq : {t : Set} -> (a b c d : Quadrant t) -> depth (Node a b c d) ≡ (1 + (max (max (depth a) (depth b)) (max (depth c) (depth d))))
propDepthRelationEq a b c d = refl

propDepthRelationLte : {t : Set} -> (a b c d : Quadrant t) -> (dep : Nat) 
  -> ((depth a <= dep && depth b <= dep) && (depth c <= dep && depth d <= dep)) ≡ (depth (Node a b c d) <= (suc dep))
propDepthRelationLte a b c d dep =
  begin 
    ((depth a <= dep && depth b <= dep) && (depth c <= dep && depth d <= dep))
  =⟨ propMaxLte4 (depth a) (depth b) (depth c) (depth d) dep ⟩
    (max (max (depth a) (depth b)) (max (depth c) (depth d)) <= dep)
  =⟨⟩
    (depth (Node a b c d) <= suc dep)
  end

propCompressedRelation : {t : Set} {{eqT : Eq t}} -> {a b c d : Quadrant t}
  -> IsTrue (isCompressed (Node a b c d))
  -> IsTrue (isCompressed a && isCompressed b && isCompressed c && isCompressed d)
propCompressedRelation {_} {Leaf a} {Leaf b} {Leaf c} {Leaf d} p = IsTrue.itsTrue
propCompressedRelation {_} {Node _ _ _ _} {b} {c} {d} p = p
propCompressedRelation {_} {Leaf _} {Node _ _ _ _} {c} {d} p = p
propCompressedRelation {_} {Leaf _} {Leaf _} {Node _ _ _ _} {d} p = p
propCompressedRelation {_} {Leaf _} {Leaf _} {Leaf _} {Node _ _ _ _} p = p

---- Fuse

combine : {t : Set} {{eqT : Eq t}} -> {dep : Nat}
  -> (a b c d : ValidQuadrant t {dep})
  -> (ValidQuadrant t {suc dep})
combine {t} {dep} (CValidQuadrant a@(Leaf va) {pa}) (CValidQuadrant b@(Leaf vb) {pb}) (CValidQuadrant c@(Leaf vc) {pc}) (CValidQuadrant d@(Leaf vd) {pd}) 
  = ifc (isCompressed (Node a b c d)) 
    then (λ {{pn}} -> CValidQuadrant (Node a b c d) {andCombine (zeroLteAny dep) pn} )
    else (λ {{pn}} -> CValidQuadrant a {IsTrue.itsTrue})

-- The next 4 cases are all identical, but I could not figure out another way to convince agda
combine {t} {dep} (CValidQuadrant a@(Node v1 v2 v3 v4) {pa}) (CValidQuadrant b {pb}) (CValidQuadrant c {pc}) (CValidQuadrant d {pd}) 
  = CValidQuadrant (Node a b c d) {andCombine 
    (useEq (propDepthRelationLte a b c d dep) ((propIsTrueCombine4 (andFst {depth a <= dep} pa) (andFst {depth b <= dep} pb) (andFst {depth c <= dep} pc) (andFst {depth d <= dep} pd)))) 
    (propIsTrueCombine4Alt (andSnd {depth a <= dep} pa) (andSnd {depth b <= dep} pb) (andSnd {depth c <= dep} pc) (andSnd {depth d <= dep} pd))
  }
combine {t} {dep} (CValidQuadrant a@(Leaf va) {pa}) (CValidQuadrant b@(Node v1 v2 v3 v4) {pb}) (CValidQuadrant c {pc}) (CValidQuadrant d {pd}) 
  = CValidQuadrant (Node a b c d) {andCombine 
    (useEq (propDepthRelationLte a b c d dep) ((propIsTrueCombine4 (andFst {depth a <= dep} pa) (andFst {depth b <= dep} pb) (andFst {depth c <= dep} pc) (andFst {depth d <= dep} pd)))) 
    (propIsTrueCombine4Alt (andSnd {depth a <= dep} pa) (andSnd {depth b <= dep} pb) (andSnd {depth c <= dep} pc) (andSnd {depth d <= dep} pd))
  }
combine {t} {dep} (CValidQuadrant a@(Leaf va) {pa}) (CValidQuadrant b@(Leaf vb) {pb}) (CValidQuadrant c@(Node v1 v2 v3 v4) {pc}) (CValidQuadrant d {pd}) 
  = CValidQuadrant (Node a b c d) {andCombine 
    (useEq (propDepthRelationLte a b c d dep) ((propIsTrueCombine4 (andFst {depth a <= dep} pa) (andFst {depth b <= dep} pb) (andFst {depth c <= dep} pc) (andFst {depth d <= dep} pd)))) 
    (propIsTrueCombine4Alt (andSnd {depth a <= dep} pa) (andSnd {depth b <= dep} pb) (andSnd {depth c <= dep} pc) (andSnd {depth d <= dep} pd))
  }
combine {t} {dep} (CValidQuadrant a@(Leaf va) {pa}) (CValidQuadrant b@(Leaf vb) {pb}) (CValidQuadrant c@(Leaf vc) {pc}) (CValidQuadrant d@(Node v1 v2 v3 v4) {pd}) 
  = CValidQuadrant (Node a b c d) {andCombine 
    (useEq (propDepthRelationLte a b c d dep) ((propIsTrueCombine4 (andFst {depth a <= dep} pa) (andFst {depth b <= dep} pb) (andFst {depth c <= dep} pc) (andFst {depth d <= dep} pd)))) 
    (propIsTrueCombine4Alt (andSnd {depth a <= dep} pa) (andSnd {depth b <= dep} pb) (andSnd {depth c <= dep} pc) (andSnd {depth d <= dep} pd))
  }
{-# COMPILE AGDA2HS combine #-}

---- Lenses

lensWrappedTree : {t : Set} {{eqT : Eq t}}
  -> {dep : Nat}
  -> CLens (ValidQuadTree t {dep}) (ValidQuadrant t {dep})
lensWrappedTree {dep = dep} fun (CValidQuadTree (Wrapper qd (w , h)) {p}) = 
  fmap 
    (λ where (CValidQuadrant qd {p}) → CValidQuadTree (Wrapper qd (w , h)) {p})
    (fun (CValidQuadrant qd {p}))
{-# COMPILE AGDA2HS lensWrappedTree #-}

aSub : {t : Set} {{eqT : Eq t}} -> {dep : Nat} -> (a b c d : Quadrant t) 
  -> IsTrue (isValid (suc dep) (Node a b c d)) -> IsTrue (isValid (dep) a)
aSub {_} {dep} a b c d p = andCombine 
  -- Convert depth proof using propDepthRelationLte
  (andFst $ andFst {(depth a <= dep && depth b <= dep)} $ useEq (sym (propDepthRelationLte a b c d dep)) (andFst p))
  -- Convert compressed proof using propCompressedRelation
  (and1 {isCompressed a} {isCompressed b} {isCompressed c} {isCompressed d} (propCompressedRelation {_} {a} (andSnd p)))

bSub : {t : Set} {{eqT : Eq t}} -> {dep : Nat} -> (a b c d : Quadrant t) 
  -> IsTrue (isValid (suc dep) (Node a b c d)) -> IsTrue (isValid (dep) b)
bSub {_} {dep} a b c d p = andCombine 
  -- Convert depth proof using propDepthRelationLte
  (andSnd $ andFst {(depth a <= dep && depth b <= dep)} $ useEq (sym (propDepthRelationLte a b c d dep)) (andFst p))
  -- Convert compressed proof using propCompressedRelation
  (and2 {isCompressed a} {isCompressed b} {isCompressed c} {isCompressed d} (propCompressedRelation {_} {a} (andSnd p)))

cSub : {t : Set} {{eqT : Eq t}} -> {dep : Nat} -> (a b c d : Quadrant t) 
  -> IsTrue (isValid (suc dep) (Node a b c d)) -> IsTrue (isValid (dep) c)
cSub {_} {dep} a b c d p = andCombine 
  -- Convert depth proof using propDepthRelationLte
  (andFst $ andSnd {(depth a <= dep && depth b <= dep)} $ useEq (sym (propDepthRelationLte a b c d dep)) (andFst p))
  -- Convert compressed proof using propCompressedRelation
  (and3 {isCompressed a} {isCompressed b} {isCompressed c} {isCompressed d} (propCompressedRelation {_} {a} (andSnd p)))

dSub : {t : Set} {{eqT : Eq t}} -> {dep : Nat} -> (a b c d : Quadrant t) 
  -> IsTrue (isValid (suc dep) (Node a b c d)) -> IsTrue (isValid (dep) d)
dSub {_} {dep} a b c d p = andCombine 
  -- Convert depth proof using propDepthRelationLte
  (andSnd $ andSnd {(depth a <= dep && depth b <= dep)} $ useEq (sym (propDepthRelationLte a b c d dep)) (andFst p))
  -- Convert compressed proof using propCompressedRelation
  (and4 {isCompressed a} {isCompressed b} {isCompressed c} {isCompressed d} (propCompressedRelation {_} {a} (andSnd p)))

lensA : 
  {t : Set} {{eqT : Eq t}}
  -> {dep : Nat}
  -> CLens (ValidQuadrant t {suc dep}) (ValidQuadrant t {dep})
lensA {_} {dep} f (CValidQuadrant (Leaf v) {p}) = 
  let sub = CValidQuadrant (Leaf v) {andCombine (zeroLteAny dep) IsTrue.itsTrue}
  in fmap (λ x -> combine x sub sub sub ) (f sub)
lensA {_} {dep} f (CValidQuadrant (Node a b c d) {p}) = 
  let 
    sA = CValidQuadrant a {aSub a b c d p}
    sB = CValidQuadrant b {bSub a b c d p}
    sC = CValidQuadrant c {cSub a b c d p}
    sD = CValidQuadrant d {dSub a b c d p}
  in fmap (λ x -> combine x sB sC sD ) (f sA)
{-# COMPILE AGDA2HS lensA #-}

lensB : 
  {t : Set} {{eqT : Eq t}}
  -> {dep : Nat}
  -> CLens (ValidQuadrant t {suc dep}) (ValidQuadrant t {dep})
lensB {_} {dep} f (CValidQuadrant (Leaf v) {p}) = 
  let sub = CValidQuadrant (Leaf v) {andCombine (zeroLteAny dep) IsTrue.itsTrue}
  in fmap (λ x -> combine sub x sub sub ) (f sub)
lensB {_} {dep} f (CValidQuadrant (Node a b c d) {p}) = 
  let 
    sA = CValidQuadrant a {aSub a b c d p}
    sB = CValidQuadrant b {bSub a b c d p}
    sC = CValidQuadrant c {cSub a b c d p}
    sD = CValidQuadrant d {dSub a b c d p}
  in fmap (λ x -> combine sA x sC sD ) (f sB)
{-# COMPILE AGDA2HS lensB #-}

lensC : 
  {t : Set} {{eqT : Eq t}}
  -> {dep : Nat}
  -> CLens (ValidQuadrant t {suc dep}) (ValidQuadrant t {dep})
lensC {_} {dep} f (CValidQuadrant (Leaf v) {p}) = 
  let sub = CValidQuadrant (Leaf v) {andCombine (zeroLteAny dep) IsTrue.itsTrue}
  in fmap (λ x -> combine sub sub x sub ) (f sub)
lensC {_} {dep} f (CValidQuadrant (Node a b c d) {p}) = 
  let 
    sA = CValidQuadrant a {aSub a b c d p}
    sB = CValidQuadrant b {bSub a b c d p}
    sC = CValidQuadrant c {cSub a b c d p}
    sD = CValidQuadrant d {dSub a b c d p}
  in fmap (λ x -> combine sA sB x sD ) (f sC)
{-# COMPILE AGDA2HS lensC #-}

lensD : 
  {t : Set} {{eqT : Eq t}}
  -> {dep : Nat}
  -> CLens (ValidQuadrant t {suc dep}) (ValidQuadrant t {dep})
lensD {_} {dep} f (CValidQuadrant (Leaf v) {p}) = 
  let sub = CValidQuadrant (Leaf v) {andCombine (zeroLteAny dep) IsTrue.itsTrue}
  in fmap (λ x -> combine sub sub sub x ) (f sub)
lensD {_} {dep} f (CValidQuadrant (Node a b c d) {p}) = 
  let 
    sA = CValidQuadrant a {aSub a b c d p}
    sB = CValidQuadrant b {bSub a b c d p}
    sC = CValidQuadrant c {cSub a b c d p}
    sD = CValidQuadrant d {dSub a b c d p}
  in fmap (λ x -> combine sA sB sC x ) (f sD)
{-# COMPILE AGDA2HS lensD #-}

lensLeaf : {t : Set} {{eqT : Eq t}}
  -> CLens (ValidQuadrant t {0}) t
lensLeaf f (CValidQuadrant (Leaf v)) = fmap (λ x -> CValidQuadrant (Leaf x) {IsTrue.itsTrue}) (f v)
{-# COMPILE AGDA2HS lensLeaf #-}

---- Data access


-- toZeroMaxDepth : {t : Set} {{eqT : Eq t}} -> {dep : Nat} -> (qd : ValidQuadrant t {dep}) -> {IsTrue (dep == 0)} -> ValidQuadrant t {0}
-- toZeroMaxDepth {dep = zero} qd {p} = qd
-- -- Agda2hs does not compile this function correctly because of pattern matching on nats
-- {-# FOREIGN AGDA2HS toZeroMaxDepth = id #-}

-- -- This is terminating, since dep always decreases when calling recursively
-- -- Agda would understand this if we could match on Nats...
-- {-# TERMINATING #-}
-- go : {t : Set} {{eqT : Eq t}}
--   -> (Nat × Nat) -> (dep : Nat)
--   -> CLens (ValidQuadrant t {dep}) t
-- go {t} (x , y) dep = matchnat dep
--   ifzero ( λ {{p1}} g qd →
--     fmap 
--       -- fmap result from f (CValidQuadrant qd 0) to f (CValidQuadrant qd dep), so we can return it.
--       (λ where (CValidQuadrant qd {p2}) -> CValidQuadrant qd {lteTransitive (depth qd) 0 dep p2 (zeroLteAny dep)})
--       -- Call lensLeaf, using the fact that depth = 0 to proof that this is a leaf
--       (lensLeaf g (toZeroMaxDepth {dep = dep} qd {p1}))
--   ) 
--   ifsuc ( λ {{p1}} g vqd -> 
--     let
--       -- ds is dep - 1
--       deps = _-_ dep 1 {{propZeroImpliesLtOne dep p1}}
--       -- Find the middle of [0, dep]
--       mid = pow 2 deps

--       -- Figure out which lens to use based on (x , y)
--       -- TODO: Proof correctness of this part
--       lensToUse = ifc y < mid then
--           ifc x < mid then         lensA {t} {deps} (go (x , y) deps g)
--           else (λ {{x_gt_mid}} ->  lensB {t} {deps} (go (_-_ x mid {{x_gt_mid}} , y) deps g))
--         else (λ {{y_gt_mid}} ->
--           ifc x < mid then         lensC {t} {deps} (go (x , _-_ y mid {{y_gt_mid}}) deps g)
--           else (λ {{x_gt_mid}} ->  lensD {t} {deps} (go (_-_ x mid {{x_gt_mid}} , _-_ y mid {{y_gt_mid}}) deps g)))

--       -- Convert (ValidQuadrant t dep) to (ValidQuadrant t (suc deps))
--       -- dep = suc deps, but I was not able to convince agda that this is true
--       vqdm : ValidQuadrant t {suc deps}
--       vqdm = case vqd of λ where
--         (CValidQuadrant qd {p2}) → CValidQuadrant qd {transformLteRight (natPlusMinNat dep {{(propZeroImpliesLtOne dep p1)}}) p2 }

--       -- Apply the lens to v1dm
--       intermediate = lensToUse vqdm

--       -- Convert back from (ValidQuadrant t (suc deps)) to (ValidQuadrant t dep)
--       bqdm = fmap (λ where 
--         (CValidQuadrant qd {p2}) -> CValidQuadrant qd {transformLteRight (sym $ natPlusMinNat dep {{(propZeroImpliesLtOne dep p1)}}) p2}) intermediate
--     in
--       bqdm
--   ) 
-- {-# COMPILE AGDA2HS go #-}

-- ---- Agda safe functions

-- makeTreeAgda : {t : Set} {{eqT : Eq t}} -> (size : Nat × Nat) -> t -> ValidQuadTree t {log2up $ max (fst size) (snd size)}
-- makeTreeAgda (w , h) v = CValidQuadTree (Wrapper (Leaf v) (w , h)) {zeroLteAny (log2up $ max w h)}
-- {-# COMPILE AGDA2HS makeTreeAgda #-}

-- atLocationAgda : {t : Set} {{eqT : Eq t}}
--   -> (Nat × Nat) -> (dep : Nat)
--   -> CLens (ValidQuadTree t {dep}) t
-- atLocationAgda index dep = lensWrappedTree ∘ (go index dep)
-- {-# COMPILE AGDA2HS atLocationAgda #-}

-- getLocationAgda : {t : Set} {{eqT : Eq t}}
--   -> (Nat × Nat) -> (dep : Nat)
--   -> ValidQuadTree t {dep} -> t
-- getLocationAgda index dep = view (atLocationAgda index dep)
-- {-# COMPILE AGDA2HS getLocationAgda #-}

-- setLocationAgda : {t : Set} {{eqT : Eq t}}
--   -> (Nat × Nat) -> (dep : Nat) 
--   -> t -> ValidQuadTree t {dep} -> ValidQuadTree t {dep}
-- setLocationAgda index dep = set (atLocationAgda index dep)
-- {-# COMPILE AGDA2HS setLocationAgda #-}

-- mapLocationAgda : {t : Set} {{eqT : Eq t}}
--   -> (Nat × Nat) -> (dep : Nat)
--   -> (t -> t) -> ValidQuadTree t {dep} -> ValidQuadTree t {dep}
-- mapLocationAgda index dep = over (atLocationAgda index dep)
-- {-# COMPILE AGDA2HS mapLocationAgda #-}

-- ---- Haskell safe functions

-- postulate invalidQuadTree : {t : Set} {{eqT : Eq t}} -> {dep : Nat} -> ValidQuadTree t {dep}
-- {-# FOREIGN AGDA2HS invalidQuadTree = error "Invalid quadtree given" #-}

-- qtToAgda : {t : Set} {{eqT : Eq t}} -> (qt : QuadTree t) -> ValidQuadTree t {maxDepth qt}
-- qtToAgda qt = ifc (depth $ treeToQuadrant qt) <= maxDepth qt
--   then (λ {{p}} -> CValidQuadTree qt {p} )
--   else invalidQuadTree
-- {-# COMPILE AGDA2HS qtToAgda #-}

-- qtFromAgda : {t : Set} {{eqT : Eq t}} -> {dep : Nat} -> ValidQuadTree t {dep} -> QuadTree t
-- qtFromAgda (CValidQuadTree qt) = qt
-- {-# COMPILE AGDA2HS qtFromAgda #-}

-- makeTree : {t : Set} {{eqT : Eq t}} -> (size : Nat × Nat) -> t -> QuadTree t
-- makeTree size v = qtFromAgda $ makeTreeAgda size v
-- {-# COMPILE AGDA2HS makeTree #-}

-- getLocation : {t : Set} {{eqT : Eq t}} -> (Nat × Nat) -> QuadTree t -> t
-- getLocation loc qt = getLocationAgda loc (maxDepth qt) $ qtToAgda qt
-- {-# COMPILE AGDA2HS getLocation #-}

-- setLocation : {t : Set} {{eqT : Eq t}} -> (Nat × Nat) -> t -> QuadTree t -> QuadTree t
-- setLocation loc v qt = qtFromAgda $ setLocationAgda loc (maxDepth qt) v $ qtToAgda qt
-- {-# COMPILE AGDA2HS setLocation #-}

-- mapLocation : {t : Set} {{eqT : Eq t}} -> (Nat × Nat) -> (t -> t) -> QuadTree t -> QuadTree t
-- mapLocation loc f qt = qtFromAgda $ mapLocationAgda loc (maxDepth qt) f $ qtToAgda qt
-- {-# COMPILE AGDA2HS mapLocation #-}
