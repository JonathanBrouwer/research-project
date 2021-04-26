module Data.QuadTree.InternalAgda where

open import Haskell.Prelude
open import Data.QuadTree.Functors
open import Data.QuadTree.Logic
open import Data.QuadTree.PropDepthRelation

{-# FOREIGN AGDA2HS
{-# LANGUAGE Safe #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Rank2Types #-}
import Data.QuadTree.Functors
import Data.QuadTree.Logic
#-}

---- Lens

CLens : Set -> Set -> Set₁
CLens s a = {f : Set -> Set} {{ff : Functor f}} -> (a -> f a) -> s -> f s
{-# FOREIGN AGDA2HS type CLens s a = forall f. Functor f => (a -> f a) -> s -> f s #-}

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
  -- wrappedTree, treeLength, treeWidth
  Wrapper : Quadrant t -> Nat -> Nat -> QuadTree t
{-# COMPILE AGDA2HS QuadTree deriving (Show, Read, Eq) #-}

instance
  quadTreeFunctor : Functor QuadTree
  quadTreeFunctor .fmap fn (Wrapper q l w) = Wrapper (fmap fn q) l w
{-# COMPILE AGDA2HS quadTreeFunctor #-}

makeTree : {t : Set} {{eqT : Eq t}} -> (Nat × Nat) -> t -> QuadTree t
makeTree (w , h) v = Wrapper (Leaf v) w h
{-# COMPILE AGDA2HS makeTree #-}

---- Check if valid

depth : {t : Set} -> Quadrant t -> Nat
depth (Leaf x) = 0
depth (Node a b c d) = 1 + max (max (depth a) (depth b)) (max(depth c) (depth d))
{-# COMPILE AGDA2HS depth #-}

treeToQuadrant : {t : Set} -> QuadTree t -> Quadrant t
treeToQuadrant (Wrapper qd _ _) = qd
{-# COMPILE AGDA2HS treeToQuadrant #-}

data ValidQuadrant (t : Set) {{eqT : Eq t}} {d : Nat} : Set where
  CValidQuadrant : (qd : Quadrant t) -> {IsTrue (depth qd <= d)} -> ValidQuadrant t {d}
{-# FOREIGN AGDA2HS
newtype ValidQuadrant t = CValidQuadrant (Quadrant t)
#-}

data ValidQuadTree (t : Set) {{eqT : Eq t}} {d : Nat} : Set where
  CValidQuadTree : (qt : QuadTree t) -> {IsTrue (depth (treeToQuadrant qt) <= d)} -> ValidQuadTree t
{-# FOREIGN AGDA2HS
newtype ValidQuadTree t = CValidQuadTree (QuadTree t)
#-}

---- Fuse function

fuse : {t : Set} -> {{eqT : Eq t}}
  -> {dep : Nat}
  -> ValidQuadrant t {dep} -> ValidQuadrant t {dep}
fuse {t} {dep} old@(CValidQuadrant (Node (Leaf a) (Leaf b) (Leaf c) (Leaf d)) {p}) = 
  if a == b && b == c && c == d 
    then CValidQuadrant (Leaf a) {zeroLteAny dep} 
    else old
fuse old = old
{-# COMPILE AGDA2HS fuse #-}

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

---- Lenses

lensWrappedTree : {t : Set} {{eqT : Eq t}}
  -> {dep : Nat}
  -> CLens (ValidQuadTree t {dep}) (ValidQuadrant t {dep})
lensWrappedTree {dep = dep} fun (CValidQuadTree (Wrapper qd l w) {p}) = 
  fmap 
    (λ where (CValidQuadrant qd {p}) → CValidQuadTree (Wrapper qd l w) {p})
    (fun (CValidQuadrant qd {p}))
{-# COMPILE AGDA2HS lensWrappedTree #-}

combine : {t : Set} {{eqT : Eq t}} -> {dep : Nat}
  -> (a b c d : ValidQuadrant t {dep})
  -> (ValidQuadrant t {suc dep})
combine {t} {dep} (CValidQuadrant a {pa}) (CValidQuadrant b {pb}) (CValidQuadrant c {pc}) (CValidQuadrant d {pd}) 
  = CValidQuadrant (Node a b c d) {useEq (propDepthRelationLte a b c d dep) (propIsTrueCombine4 pa pb pc pd)}
{-# COMPILE AGDA2HS combine #-}

lensA : 
  {t : Set} {{eqT : Eq t}}
  -> {dep : Nat}
  -> CLens (ValidQuadrant t {suc dep}) (ValidQuadrant t {dep})
lensA {_} {dep} f (CValidQuadrant (Leaf v) {p}) = 
  let sub = CValidQuadrant (Leaf v) {zeroLteAny dep}
  in fmap (λ x -> fuse (combine x sub sub sub) ) (f sub)
lensA {_} {dep} f (CValidQuadrant (Node a b c d) {p}) = 
  let sub = CValidQuadrant a {andFst $ andFst {(depth a <= dep && depth b <= dep)} $ useEq (sym (propDepthRelationLte a b c d dep)) p}
  in fmap (λ x -> fuse (combine x sub sub sub) ) (f sub)
{-# COMPILE AGDA2HS lensA #-}

lensB : 
  {t : Set} {{eqT : Eq t}}
  -> {dep : Nat}
  -> CLens (ValidQuadrant t {suc dep}) (ValidQuadrant t {dep})
lensB {_} {dep} f (CValidQuadrant (Leaf v) {p}) = 
  let sub = CValidQuadrant (Leaf v) {zeroLteAny dep}
  in fmap (λ x -> fuse (combine sub x sub sub) ) (f sub)
lensB {_} {dep} f (CValidQuadrant (Node a b c d) {p}) = 
  let sub = CValidQuadrant b { andSnd $ andFst {(depth a <= dep && depth b <= dep)} $ useEq (sym (propDepthRelationLte a b c d dep)) p }
  in fmap (λ x -> fuse (combine sub x sub sub) ) (f sub)
{-# COMPILE AGDA2HS lensB #-}

lensC : 
  {t : Set} {{eqT : Eq t}}
  -> {dep : Nat}
  -> CLens (ValidQuadrant t {suc dep}) (ValidQuadrant t {dep})
lensC {_} {dep} f (CValidQuadrant (Leaf v) {p}) = 
  let sub = CValidQuadrant (Leaf v) {zeroLteAny dep}
  in fmap (λ x -> fuse (combine sub sub x sub) ) (f sub)
lensC {_} {dep} f (CValidQuadrant (Node a b c d) {p}) = 
  let sub = CValidQuadrant c {andFst $ andSnd {(depth a <= dep && depth b <= dep)} $ useEq (sym (propDepthRelationLte a b c d dep)) p}
  in fmap (λ x -> fuse (combine sub sub x sub) ) (f sub)
{-# COMPILE AGDA2HS lensC #-}

lensD : 
  {t : Set} {{eqT : Eq t}}
  -> {dep : Nat}
  -> CLens (ValidQuadrant t {suc dep}) (ValidQuadrant t {dep})
lensD {_} {dep} f (CValidQuadrant (Leaf v) {p}) = 
  let sub = CValidQuadrant (Leaf v) {zeroLteAny dep}
  in fmap (λ x -> fuse (combine sub sub sub x) ) (f sub)
lensD {_} {dep} f (CValidQuadrant (Node a b c d) {p}) = 
  let sub = CValidQuadrant d {andSnd $ andSnd {(depth a <= dep && depth b <= dep)} $ useEq (sym (propDepthRelationLte a b c d dep)) p}
  in fmap (λ x -> fuse (combine sub sub sub x) ) (f sub)
{-# COMPILE AGDA2HS lensD #-}

lensLeaf : {t : Set} {{eqT : Eq t}}
  -> CLens (ValidQuadrant t {0}) t
lensLeaf f (CValidQuadrant (Leaf v)) = fmap (λ x -> CValidQuadrant (Leaf x) {IsTrue.itsTrue}) (f v)
{-# COMPILE AGDA2HS lensLeaf #-}

---- Data access


toZeroMaxDepth : {t : Set} {{eqT : Eq t}} -> {dep : Nat} -> (qd : ValidQuadrant t {dep}) -> {IsTrue (dep == 0)} -> ValidQuadrant t {0}
toZeroMaxDepth {dep = zero} qd {p} = qd
-- Agda2hs does not compile this function correctly because of pattern matching on nats
{-# FOREIGN AGDA2HS toZeroMaxDepth = id #-}

-- This is terminating, since dep always decreases when calling recursively
-- Agda would understand this if we could match on Nats...
{-# TERMINATING #-}
go : {t : Set} {{eqT : Eq t}}
  -> (Nat × Nat) -> (dep : Nat)
  -> CLens (ValidQuadrant t {dep}) t
go {t} (x , y) dep = matchnat dep
  ifzero ( λ {{p1}} g qd →
    fmap 
      -- fmap result from f (CValidQuadrant qd 0) to f (CValidQuadrant qd dep), so we can return it.
      (λ where (CValidQuadrant qd {p2}) -> CValidQuadrant qd {lteTransitive (depth qd) 0 dep p2 (zeroLteAny dep)})
      -- Call lensLeaf, using the fact that depth = 0 to proof that this is a leaf
      (lensLeaf g (toZeroMaxDepth {dep = dep} qd {p1}))
  ) 
  ifsuc ( λ {{p1}} g vqd -> 
    let
      -- ds is dep - 1
      deps = _-_ dep 1 {{propZeroImpliesLtOne dep p1}}
      -- Find the middle of [0, dep]
      mid = pow 2 deps

      -- Figure out which lens to use based on (x , y)
      -- TODO: Proof correctness of this part
      lensToUse = ifc y < mid then
          ifc x < mid then         lensA {t} {deps} (go (x , y) deps g)
          else (λ {{x_gt_mid}} ->  lensB {t} {deps} (go (_-_ x mid {{x_gt_mid}} , y) deps g))
        else (λ {{y_gt_mid}} ->
          ifc x < mid then         lensC {t} {deps} (go (x , _-_ y mid {{y_gt_mid}}) deps g)
          else (λ {{x_gt_mid}} ->  lensD {t} {deps} (go (_-_ x mid {{x_gt_mid}} , _-_ y mid {{y_gt_mid}}) deps g)))

      -- Convert (ValidQuadrant t dep) to (ValidQuadrant t (suc deps))
      -- dep = suc deps, but I was not able to convince agda that this is true
      vqdm : ValidQuadrant t {suc deps}
      vqdm = case vqd of λ where
        (CValidQuadrant qd {p2}) → CValidQuadrant qd {transformLteRight (natPlusMinNat dep {{(propZeroImpliesLtOne dep p1)}}) p2 }

      -- Apply the lens to v1dm
      intermediate = lensToUse vqdm

      -- Convert back from (ValidQuadrant t (suc deps)) to (ValidQuadrant t dep)
      bqdm = fmap (λ where 
        (CValidQuadrant qd {p2}) -> CValidQuadrant qd {transformLteRight (sym $ natPlusMinNat dep {{(propZeroImpliesLtOne dep p1)}}) p2}) intermediate
    in
      bqdm
  ) 
{-# COMPILE AGDA2HS go #-}


-- Eq a => (Nat, Nat) -> CLens (QuadTree a) a
atLocation : {t : Set} {{eqT : Eq t}}
  -> (Nat × Nat) -> (dep : Nat)
  -> CLens (ValidQuadTree t {dep}) t
atLocation index dep = lensWrappedTree ∘ (go index dep)
{-# COMPILE AGDA2HS atLocation #-}

-- ---- Functions using functors

getLocationAgda : {t : Set} {{eqT : Eq t}}
  -> (Nat × Nat) -> (dep : Nat) 
  -> ValidQuadTree t {dep} -> t
getLocationAgda index dep qt = getConst $ atLocation index dep CConst qt
{-# COMPILE AGDA2HS getLocationAgda #-}

setLocationAgda : {t : Set} {{eqT : Eq t}}
  -> (Nat × Nat) -> (dep : Nat) 
  -> t -> ValidQuadTree t {dep} -> ValidQuadTree t {dep}
setLocationAgda index dep v qt = runIdentity $ atLocation index dep (λ _ -> CIdentity v) qt
{-# COMPILE AGDA2HS setLocationAgda #-}

mapLocationAgda : {t : Set} {{eqT : Eq t}}
  -> (Nat × Nat) -> (dep : Nat)
  -> (t -> t) -> ValidQuadTree t {dep} -> ValidQuadTree t {dep}
mapLocationAgda index dep f qt = runIdentity $ atLocation index dep (CIdentity ∘ f) qt
{-# COMPILE AGDA2HS mapLocationAgda #-}