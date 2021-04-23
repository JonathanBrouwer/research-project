module Data.QuadTree.InternalAgda where

open import Haskell.Prelude
open import Data.QuadTree.Functors
open import Data.QuadTree.Logic
open import Data.QuadTree.PropDepthRelation

{-# FOREIGN AGDA2HS
import Data.QuadTree.Functors
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

lensWrappedTree : {t : Set} {{eqT : Eq t}} {f : Set -> Set} {{fFunctor : Functor f}}
  -> {dep : Nat}
  -> ((ValidQuadrant t {dep}) -> f (ValidQuadrant t {dep})) 
  -> ValidQuadTree t {dep} -> f (ValidQuadTree t {dep})
lensWrappedTree {dep = dep} fun (CValidQuadTree (Wrapper qd l w) {p}) = 
  (fmap qdToQt (fun (CValidQuadrant qd {p}))) where
    qdToQt : {t : Set} {{eqT : Eq t}} -> ValidQuadrant t {dep} -> ValidQuadTree t {dep}
    qdToQt (CValidQuadrant qd {p}) = CValidQuadTree (Wrapper qd l w) {p}
{-# COMPILE AGDA2HS lensWrappedTree #-}

combine : {t : Set} {{eqT : Eq t}} -> {dep : Nat}
  -> (a b c d : ValidQuadrant t {dep})
  -> (ValidQuadrant t {suc dep})
combine {t} {dep} (CValidQuadrant a {pa}) (CValidQuadrant b {pb}) (CValidQuadrant c {pc}) (CValidQuadrant d {pd}) 
  = CValidQuadrant (Node a b c d) {useEq (propDepthRelationLte a b c d dep) (propIsTrueCombine4 pa pb pc pd)}
{-# COMPILE AGDA2HS combine #-}

lensA : 
  {t : Set} {{eqT : Eq t}} {f : Set -> Set} {{fFunctor : Functor f}}
  -> {dep : Nat}
  -> ((ValidQuadrant t {dep}) -> f (ValidQuadrant t {dep})) 
  -> ValidQuadrant t {suc dep} -> f (ValidQuadrant t {suc dep})
lensA {_} {_} {dep} f (CValidQuadrant (Leaf v) {p}) = 
  let sub = CValidQuadrant (Leaf v) {zeroLteAny dep}
  in fmap (λ x -> fuse (combine x sub sub sub) ) (f sub)
lensA {_} {_} {dep} f (CValidQuadrant (Node a b c d) {p}) = 
  let sub = CValidQuadrant a {andFst $ andFst {(depth a <= dep && depth b <= dep)} $ useEq (sym (propDepthRelationLte a b c d dep)) p}
  in fmap (λ x -> fuse (combine x sub sub sub) ) (f sub)
{-# COMPILE AGDA2HS lensA #-}

lensB : 
  {t : Set} {{eqT : Eq t}} {f : Set -> Set} {{fFunctor : Functor f}}
  -> {dep : Nat}
  -> ((ValidQuadrant t {dep}) -> f (ValidQuadrant t {dep})) 
  -> ValidQuadrant t {suc dep} -> f (ValidQuadrant t {suc dep})
lensB {_} {_} {dep} f (CValidQuadrant (Leaf v) {p}) = 
  let sub = CValidQuadrant (Leaf v) {zeroLteAny dep}
  in fmap (λ x -> fuse (combine sub x sub sub) ) (f sub)
lensB {_} {_} {dep} f (CValidQuadrant (Node a b c d) {p}) = 
  let sub = CValidQuadrant b { andSnd $ andFst {(depth a <= dep && depth b <= dep)} $ useEq (sym (propDepthRelationLte a b c d dep)) p }
  in fmap (λ x -> fuse (combine sub x sub sub) ) (f sub)
{-# COMPILE AGDA2HS lensB #-}

lensC : 
  {t : Set} {{eqT : Eq t}} {f : Set -> Set} {{fFunctor : Functor f}}
  -> {dep : Nat}
  -> ((ValidQuadrant t {dep}) -> f (ValidQuadrant t {dep})) 
  -> ValidQuadrant t {suc dep} -> f (ValidQuadrant t {suc dep})
lensC {_} {_} {dep} f (CValidQuadrant (Leaf v) {p}) = 
  let sub = CValidQuadrant (Leaf v) {zeroLteAny dep}
  in fmap (λ x -> fuse (combine sub sub x sub) ) (f sub)
lensC {_} {_} {dep} f (CValidQuadrant (Node a b c d) {p}) = 
  let sub = CValidQuadrant c {andFst $ andSnd {(depth a <= dep && depth b <= dep)} $ useEq (sym (propDepthRelationLte a b c d dep)) p}
  in fmap (λ x -> fuse (combine sub sub x sub) ) (f sub)
{-# COMPILE AGDA2HS lensC #-}

lensD : 
  {t : Set} {{eqT : Eq t}} {f : Set -> Set} {{fFunctor : Functor f}}
  -> {dep : Nat}
  -> ((ValidQuadrant t {dep}) -> f (ValidQuadrant t {dep})) 
  -> ValidQuadrant t {suc dep} -> f (ValidQuadrant t {suc dep})
lensD {_} {_} {dep} f (CValidQuadrant (Leaf v) {p}) = 
  let sub = CValidQuadrant (Leaf v) {zeroLteAny dep}
  in fmap (λ x -> fuse (combine sub sub sub x) ) (f sub)
lensD {_} {_} {dep} f (CValidQuadrant (Node a b c d) {p}) = 
  let sub = CValidQuadrant d {andSnd $ andSnd {(depth a <= dep && depth b <= dep)} $ useEq (sym (propDepthRelationLte a b c d dep)) p}
  in fmap (λ x -> fuse (combine sub sub sub x) ) (f sub)
{-# COMPILE AGDA2HS lensD #-}

lensLeaf : {t : Set} {{eqT : Eq t}} {f : Set -> Set} {{fFunctor : Functor f}}
  -> (t -> f t)
  -> (ValidQuadrant t {0}) -> f (ValidQuadrant t {0})
lensLeaf f (CValidQuadrant (Leaf v)) = fmap (λ x -> CValidQuadrant (Leaf x) {IsTrue.itsTrue}) (f v)
{-# COMPILE AGDA2HS lensLeaf #-}



---- Data access

-- bottom = ⊥

-- readLeaf : {t : Set} {{eqT : Eq t}} -> (qd : Quadrant t) -> {MaxDepth qd 0} -> t
-- readLeaf (Leaf v) {md} = v
-- readLeaf (Node a b c d) {maxDepth .(Node a b c d) .0 ()}
-- {-# COMPILE AGDA2HS readLeaf #-}

-- transformMaxDepth : {t : Set} {{eqT : Eq t}} -> (qd : Quadrant t) -> (d : Nat) -> {MaxDepth qd d} -> {IsTrue (d == 0)} -> MaxDepth qd 0
-- transformMaxDepth qd zero {maxDepth .qd .0 x} {d0} = maxDepth qd 0 x

-- af : Bool -> {Bool} -> (Bool × Bool)
-- af y = (y , y)

-- {-# COMPILE AGDA2HS af #-}
-- -- Eq a => (Nat, Nat) -> Nat -> CLens (QuadTree a) a
-- {-# TERMINATING #-}
-- go : {a : Set} {{eqT : Eq a}}
--   -> {f : Set -> Set} {{fFunctor : Functor f}}
--   -> (Nat × Nat) -> (d : Nat)
--   -> (a -> f a) -> (qd : Quadrant a) -> {MaxDepth qd d} -> f (Quadrant a)
-- go (x , y) d = matchnat d
--   ifzero ( λ {{p}} ->
--     -- Uses readLeaf and transformMaxDepth to proof that qd must be a Leaf, and not a Node
--     λ f qd {md} -> Leaf <$> (f $ readLeaf qd { transformMaxDepth qd d {md} {p} })
--   )
--   ifsuc ( λ {{p}} ->
--     let
--       -- Subtract one from d (d sub), using the fact that d > 0 from ifsuc
--       ds = _-_ d 1 {{propNotZeroImpliesLtOne d p}}
--       mid = pow 2 ds
--     in
--       {!   !}
--     --   ifc y < mid then
--     --     ifc x < mid then         lensA ∘ (go (x , y) ds)
--     --     else (λ {{x_gt_mid}} ->  lensB ∘ (go (_-_ x mid {{x_gt_mid}} , y) ds)   )
--     --   else (λ {{y_gt_mid}} ->
--     --     ifc x < mid then         lensC ∘ (go (x , _-_ y mid {{y_gt_mid}}) ds)
--     --     else (λ {{x_gt_mid}} ->  lensD ∘ (go (_-_ x mid {{x_gt_mid}} , _-_ y mid {{y_gt_mid}}) ds)   )
--     --   ) 
--   )
-- {-# COMPILE AGDA2HS go #-}

-- Eq a => (Nat, Nat) -> CLens (QuadTree a) a
-- atLocation : {a : Set} {{eqT : Eq a}}
--   -> {f : Set -> Set} {{fFunctor : Functor f}}
--   -> (Nat × Nat)
--   -> (a -> f a) -> (qt : QuadTree a) -> {{IsValid qt}} -> f (QuadTree a)
-- atLocation index fn qt@(Wrapper qd l w d) ⦃ valid .(Wrapper qd l w d) x ⦄ = (lensWrappedTree ∘ (go index d)) fn {!  !}
-- {-# COMPILE AGDA2HS atLocation #-}

---- Functions using functors

-- getLocation : {a : Set} {{eqT : Eq a}}
--   -> (Nat × Nat) -> QuadTree a -> a
-- getLocation index qt = getConst (atLocation index CConst qt)
-- {-# COMPILE AGDA2HS getLocation #-}

-- setLocation : {a : Set} {{eqT : Eq a}}
--   -> (Nat × Nat) -> a -> QuadTree a -> QuadTree a
-- setLocation index v qt = runIdentity (atLocation index (λ _ -> CIdentity v) qt)
-- {-# COMPILE AGDA2HS setLocation #-}

-- mapLocation : {a : Set} {{eqT : Eq a}}
--   -> (Nat × Nat) -> (a -> a) -> QuadTree a -> QuadTree a
-- mapLocation index f qt = runIdentity (atLocation index (CIdentity ∘ f) qt)
-- {-# COMPILE AGDA2HS mapLocation #-}

