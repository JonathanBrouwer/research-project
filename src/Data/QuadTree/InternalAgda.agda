module Data.QuadTree.InternalAgda where

open import Haskell.Prelude renaming (zero to Z; suc to S)
open import Data.Lens.Lens
open import Data.Logic
open import Data.QuadTree.PropDepthRelation

{-# FOREIGN AGDA2HS
{-# LANGUAGE Safe #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Rank2Types #-}
import Data.Nat
import Data.Lens.Lens
import Data.Logic
#-}

---- Quadrants
-- A quadrant is either a leaf or a node with 4 sub-quadrants

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
-- A quadtree is the width/height + the root quadrant

data QuadTree (t : Set) : Set where
  Wrapper : (Nat × Nat) -> Quadrant t -> QuadTree t
{-# COMPILE AGDA2HS QuadTree deriving (Show, Eq) #-}

instance
  quadTreeFunctor : Functor QuadTree
  quadTreeFunctor .fmap fn (Wrapper (w , h) q) = Wrapper (w , h) (fmap fn q) 
{-# COMPILE AGDA2HS quadTreeFunctor #-}

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
  -> (qt : QuadTree t) -> {IsTrue (isValid dep (treeToQuadrant qt))} -> {IsTrue (dep == maxDepth qt)} 
  -> VQuadTree t {maxDepth qt}
qtToSafe {dep = dep} qt {p} {q} = CVQuadTree qt {useEq (cong (λ g -> isValid g (treeToQuadrant qt)) (eqToEquiv dep (maxDepth qt) q)) p} {eqReflexivity (maxDepth qt)}
{-# COMPILE AGDA2HS qtToSafe #-}

qtFromSafe : {t : Set} {{eqT : Eq t}} -> {dep : Nat} -> VQuadTree t {dep} -> QuadTree t
qtFromSafe (CVQuadTree qt) = qt
{-# COMPILE AGDA2HS qtFromSafe #-}

isInsideQuadTree : {t : Set} -> (Nat × Nat) -> QuadTree t -> Bool
isInsideQuadTree (x , y) (Wrapper (w , h) x₂) = x < w && y < h

isInsidePow : (Nat × Nat) -> Nat -> Bool
isInsidePow (x , y) deps = x < pow 2 deps && y < pow 2 deps

insideQTtoInsidePow : {t : Set} {{eqT : Eq t}} -> (loc : Nat × Nat) -> {dep : Nat} -> (vqt : VQuadTree t {dep})
  -> IsTrue (isInsideQuadTree loc (qtFromSafe vqt))
  -> IsTrue (isInsidePow loc dep)
insideQTtoInsidePow (x , y) {dep} (CVQuadTree (Wrapper (w , h) qd) {p} {q}) it =
  let
    p1 : IsTrue (pow 2 dep >= (max w h))
    p1 = log2upPow dep (max w h) (eqToGte dep (log2up (max w h)) q)

    p2 : IsTrue ((max w h) <= pow 2 dep)
    p2 = gteInvert (pow 2 dep) (max w h) p1

    p3 : IsTrue (w <= pow 2 dep && h <= pow 2 dep)
    p3 = useEq (sym $ propMaxLte w h (pow 2 dep)) p2
  in andCombine 
    ( ltLteTransitive x w (pow 2 dep) (andFst {x < w} it) (andFst p3) )
    ( ltLteTransitive y h (pow 2 dep) (andSnd {x < w} it) (andSnd p3) )
  
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

---- Data access

-- Lens into the leaf quadrant corresponding to a location in a quadrant
go : {t : Set} {{eqT : Eq t}}
  -> (loc : Nat × Nat) -> (dep : Nat)
  -> {.(IsTrue (isInsidePow loc dep))}
  -> Lens (VQuadrant t {dep}) t
go _ Z = lensLeaf
go {t} (x , y) (S deps) =
  if (y < mid) 
    then if x < mid 
      then (lensA ∘ gorec)
      else (lensB ∘ gorec)
    else if x < mid
      then (lensC ∘ gorec)
      else (lensD ∘ gorec)
  where
    mid = pow 2 deps
    gorec = go {t} (mod x mid {pow_not_zero_cv deps} , mod y mid {pow_not_zero_cv deps}) deps 
      {andCombine (modLt x mid {pow_not_zero_cv deps}) (modLt y mid {pow_not_zero_cv deps})}
{-# COMPILE AGDA2HS go #-}

-- Lenses into the root quadrant of a quadtree
lensWrappedTree : {t : Set} {{eqT : Eq t}}
  -> {dep : Nat}
  -> Lens (VQuadTree t {dep}) (VQuadrant t {dep})
lensWrappedTree fun (CVQuadTree (Wrapper (w , h) qd) {p} {q}) = 
  fmap 
    (λ where (CVQuadrant qd {p}) → CVQuadTree (Wrapper (w , h) qd) {p} {q})
    (fun (CVQuadrant qd {p}))
{-# COMPILE AGDA2HS lensWrappedTree #-}

-- Lens into the leaf quadrant corresponding to a location in a quadtree
atLocation : {t : Set} {{eqT : Eq t}}
  -> (loc : Nat × Nat) -> (dep : Nat)
  -> {.(IsTrue (isInsidePow loc dep))}
  -> Lens (VQuadTree t {dep}) t
atLocation index dep {p} = lensWrappedTree ∘ (go index dep {p})
{-# COMPILE AGDA2HS atLocation #-}

---- Safe functions

makeTreeSafe : {t : Set} {{eqT : Eq t}} -> (size : Nat × Nat) -> (v : t) -> VQuadTree t {maxDepth $ Wrapper size (Leaf v)}
makeTreeSafe (w , h) v = CVQuadTree (Wrapper (w , h) (Leaf v)) {andCombine (zeroLteAny (log2up $ max w h)) IsTrue.itsTrue} {eqReflexivity (maxDepth $ Wrapper (w , h) (Leaf v))}
{-# COMPILE AGDA2HS makeTreeSafe #-}

getLocationSafe : {t : Set} {{eqT : Eq t}}
  -> (loc : Nat × Nat) -> (dep : Nat)
  -> (qt : VQuadTree t {dep})
  -> {IsTrue (isInsideQuadTree loc (qtFromSafe qt))} 
  -> t
getLocationSafe index dep vqt {inside} = view (atLocation index dep {insideQTtoInsidePow index vqt inside}) vqt
{-# COMPILE AGDA2HS getLocationSafe #-}

setLocationSafe : {t : Set} {{eqT : Eq t}}
  -> (loc : Nat × Nat) -> (dep : Nat) 
  -> t -> (qt : VQuadTree t {dep}) 
  -> {IsTrue (isInsideQuadTree loc (qtFromSafe qt))} 
  -> VQuadTree t {dep}
setLocationSafe index dep v vqt {inside} = set (atLocation index dep {insideQTtoInsidePow index vqt inside}) v vqt
{-# COMPILE AGDA2HS setLocationSafe #-}

mapLocationSafe : {t : Set} {{eqT : Eq t}}
  -> (loc : Nat × Nat) -> (dep : Nat)
  -> (t -> t) -> (qt : VQuadTree t {dep}) 
  -> {IsTrue (isInsideQuadTree loc (qtFromSafe qt))} 
  -> VQuadTree t {dep}
mapLocationSafe index dep f vqt {inside} = over (atLocation index dep {insideQTtoInsidePow index vqt inside}) f vqt
{-# COMPILE AGDA2HS mapLocationSafe #-}

---- Unsafe functions (Original)

makeTree : {t : Set} {{eqT : Eq t}} -> (size : Nat × Nat) -> t -> QuadTree t
makeTree size v = qtFromSafe $ makeTreeSafe size v
{-# COMPILE AGDA2HS makeTree #-}

getLocation : {t : Set} {{eqT : Eq t}} 
  -> (loc : Nat × Nat) -> {dep : Nat}
  -> (qt : QuadTree t) 
  -> {IsTrue (isInsideQuadTree loc qt)}
  -> {IsTrue (isValid dep (treeToQuadrant qt))} -> {IsTrue (dep == maxDepth qt)} 
  -> t
getLocation loc qt {inside} {p} {q} = getLocationSafe loc (maxDepth qt) (qtToSafe qt {p} {q}) {inside}
{-# COMPILE AGDA2HS getLocation #-}

setLocation : {t : Set} {{eqT : Eq t}} 
  -> (loc : Nat × Nat) -> t
  -> {dep : Nat} -> (qt : QuadTree t) 
  -> {IsTrue (isInsideQuadTree loc qt)}
  -> {IsTrue (isValid dep (treeToQuadrant qt))} -> {IsTrue (dep == maxDepth qt)} 
  -> QuadTree t
setLocation loc v qt {inside} {p} {q} = qtFromSafe $ setLocationSafe loc (maxDepth qt) v (qtToSafe qt {p} {q}) {inside}
{-# COMPILE AGDA2HS setLocation #-}

mapLocation : {t : Set} {{eqT : Eq t}} 
  -> (loc : Nat × Nat) -> (t -> t) 
  -> {dep : Nat} -> (qt : QuadTree t) 
  -> {IsTrue (isInsideQuadTree loc qt)}
  -> {IsTrue (isValid dep (treeToQuadrant qt))} -> {IsTrue (dep == maxDepth qt)} 
  -> QuadTree t
mapLocation loc f qt {inside} {p} {q} = qtFromSafe $ mapLocationSafe loc (maxDepth qt) f (qtToSafe qt {p} {q}) {inside}
{-# COMPILE AGDA2HS mapLocation #-}