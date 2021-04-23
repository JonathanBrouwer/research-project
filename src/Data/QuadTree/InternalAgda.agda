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
  -- wrappedTree, treeLength, treeWidth, treeDepth
  Wrapper : Quadrant t -> Nat -> Nat -> Nat -> QuadTree t
{-# COMPILE AGDA2HS QuadTree deriving (Show, Read, Eq) #-}

instance
  quadTreeFunctor : Functor QuadTree
  quadTreeFunctor .fmap fn (Wrapper q l w d) = Wrapper (fmap fn q) l w d
{-# COMPILE AGDA2HS quadTreeFunctor #-}

makeTree : {t : Set} {{eqT : Eq t}} -> (Nat × Nat) -> t -> QuadTree t
makeTree (w , h) v = Wrapper (Leaf v) w h (log2up (max w h) )
{-# COMPILE AGDA2HS makeTree #-}

---- Check if valid

depth : {t : Set} -> Quadrant t -> Nat
depth (Leaf x) = 0
depth (Node a b c d) = 1 + max (max (depth a) (depth b)) (max(depth c) (depth d))
{-# COMPILE AGDA2HS depth #-}

isValidQuadTree : {t : Set} {{eqT : Eq t}} -> QuadTree t -> Bool
isValidQuadTree (Wrapper qd _ _ d) = depth qd <= d
{-# COMPILE AGDA2HS isValidQuadTree #-}

data ValidQuadrant (t : Set) {{eqT : Eq t}} {d : Nat} : Set where
  CValidQuadrant : (qd : Quadrant t) -> {IsTrue (depth qd <= d)} -> ValidQuadrant t {d}
{-# FOREIGN AGDA2HS
data ValidQuadrant t = CValidQuadrant (Quadrant t)
#-}

data ValidQuadTree (t : Set) {{eqT : Eq t}} : Set where
  CValidQuadTree : (qt : QuadTree t) -> {IsTrue (isValidQuadTree qt)} -> ValidQuadTree t
{-# FOREIGN AGDA2HS
data ValidQuadTree t = CValidQuadTree (QuadTree t)
#-}

---- Temp test

qd = Node (Leaf true) (Leaf true) (Leaf false) (Leaf false)

vqd : ValidQuadrant Bool {1}
vqd = CValidQuadrant qd {IsTrue.itsTrue}

qt = Wrapper qd 2 2 1
vqt : ValidQuadTree Bool
vqt = CValidQuadTree qt {IsTrue.itsTrue}

{-# COMPILE AGDA2HS qd #-}
{-# COMPILE AGDA2HS vqd #-}
{-# COMPILE AGDA2HS qt #-}
{-# COMPILE AGDA2HS vqt #-}

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

combine : {t : Set} {{eqT : Eq t}} -> {dep : Nat}
  -> (a b c d : ValidQuadrant t {dep})
  -> (ValidQuadrant t {suc dep})
combine {t} {dep} (CValidQuadrant a {pa}) (CValidQuadrant b {pb}) (CValidQuadrant c {pc}) (CValidQuadrant d {pd}) 
  = CValidQuadrant (Node a b c d) {useEq (propDepthRelationLte a b c d dep) (propIsTrueCombine4 pa pb pc pd)}
{-# COMPILE AGDA2HS combine #-}

lensA : 
  {t : Set} {{eqT : Eq t}} {f : Set -> Set} {{fFunctor : Functor f}}
  -> (dep : Nat)
  -> ((ValidQuadrant t {dep}) -> f (ValidQuadrant t {dep})) 
  -> ValidQuadrant t {suc dep} -> f (ValidQuadrant t {suc dep})
lensA {t} dep f (CValidQuadrant (Leaf v) {p}) = 
  let sub = CValidQuadrant (Leaf v) {zeroLteAny dep}
  in fmap (λ x -> fuse (combine x sub sub sub) ) (f sub) where
lensA {t} dep f (CValidQuadrant (Node a b c d) {p}) = 
  let sub = CValidQuadrant a {andFst $ andFst {(depth a <= dep && depth b <= dep)} $ useEq (sym (propDepthRelationLte a b c d dep)) p}
  in fmap (λ x -> fuse (combine x sub sub sub) ) (f sub) where
{-# COMPILE AGDA2HS lensA #-}

lensB : 
  {t : Set} {{eqT : Eq t}} {f : Set -> Set} {{fFunctor : Functor f}}
  -> (dep : Nat)
  -> ((ValidQuadrant t {dep}) -> f (ValidQuadrant t {dep})) 
  -> ValidQuadrant t {suc dep} -> f (ValidQuadrant t {suc dep})
lensB {t} dep f (CValidQuadrant (Leaf v) {p}) = 
  let sub = CValidQuadrant (Leaf v) {zeroLteAny dep}
  in fmap (λ x -> fuse (combine sub x sub sub) ) (f sub) where
lensB {t} dep f (CValidQuadrant (Node a b c d) {p}) = 
  let sub = CValidQuadrant b { andSnd $ andFst {(depth a <= dep && depth b <= dep)} $ useEq (sym (propDepthRelationLte a b c d dep)) p }
  in fmap (λ x -> fuse (combine sub x sub sub) ) (f sub) where
{-# COMPILE AGDA2HS lensB #-}

lensC : 
  {t : Set} {{eqT : Eq t}} {f : Set -> Set} {{fFunctor : Functor f}}
  -> (dep : Nat)
  -> ((ValidQuadrant t {dep}) -> f (ValidQuadrant t {dep})) 
  -> ValidQuadrant t {suc dep} -> f (ValidQuadrant t {suc dep})
lensC {t} dep f (CValidQuadrant (Leaf v) {p}) = 
  let sub = CValidQuadrant (Leaf v) {zeroLteAny dep}
  in fmap (λ x -> fuse (combine sub sub x sub) ) (f sub) where
lensC {t} dep f (CValidQuadrant (Node a b c d) {p}) = 
  let sub = CValidQuadrant c {andFst $ andSnd {(depth a <= dep && depth b <= dep)} $ useEq (sym (propDepthRelationLte a b c d dep)) p}
  in fmap (λ x -> fuse (combine sub sub x sub) ) (f sub) where
{-# COMPILE AGDA2HS lensC #-}

lensD : 
  {t : Set} {{eqT : Eq t}} {f : Set -> Set} {{fFunctor : Functor f}}
  -> (dep : Nat)
  -> ((ValidQuadrant t {dep}) -> f (ValidQuadrant t {dep})) 
  -> ValidQuadrant t {suc dep} -> f (ValidQuadrant t {suc dep})
lensD {t} dep f (CValidQuadrant (Leaf v) {p}) = 
  let sub = CValidQuadrant (Leaf v) {zeroLteAny dep}
  in fmap (λ x -> fuse (combine sub sub sub x) ) (f sub) where
lensD {t} dep f (CValidQuadrant (Node a b c d) {p}) = 
  let sub = CValidQuadrant d {andSnd $ andSnd {(depth a <= dep && depth b <= dep)} $ useEq (sym (propDepthRelationLte a b c d dep)) p}
  in fmap (λ x -> fuse (combine sub sub sub x) ) (f sub) where
{-# COMPILE AGDA2HS lensD #-}


-- Can we define a type with an implicit argument, and define a different haskell type??6
-- propLensA : {a : Set} {{eqT : Eq a}} {f : Set -> Set} {{fFunctor : Functor f}} ->
--   (qd : Quadrant a) -> lensA f qd ≡ lensA f qd
-- propLensA = {!   !}

-- -- Eq a => CLens (Quadrant a) (Quadrant a)
-- lensB : {a : Set} {{eqT : Eq a}} {f : Set -> Set} {{fFunctor : Functor f}}
--          -> ((Quadrant a) -> f (Quadrant a)) -> Quadrant a -> f (Quadrant a)
-- lensB f (Node a b c d) = fmap (λ x -> fuse ( Node a x c d)) (f b)
-- lensB f l = fmap ((λ x -> fuse $  Node l x l l)) (f l)
-- {-# COMPILE AGDA2HS lensB #-}

-- -- Eq a => CLens (Quadrant a) (Quadrant a)
-- lensC : {a : Set} {{eqT : Eq a}} {f : Set -> Set} {{fFunctor : Functor f}}
--          -> ((Quadrant a) -> f (Quadrant a)) -> Quadrant a -> f (Quadrant a)
-- lensC f (Node a b c d) = fmap (λ x -> fuse ( Node a b x d)) (f c)
-- lensC f l = fmap ((λ x -> fuse $  Node l l x l)) (f l)
-- {-# COMPILE AGDA2HS lensC #-}

-- -- Eq a => CLens (Quadrant a) (Quadrant a)
-- lensD : {a : Set} {{eqT : Eq a}} {f : Set -> Set} {{fFunctor : Functor f}}
--          -> ((Quadrant a) -> f (Quadrant a)) -> Quadrant a -> f (Quadrant a)
-- lensD f (Node a b c d) = fmap (λ x -> fuse ( Node a b c x)) (f d)
-- lensD f l = fmap ((λ x -> fuse $ Node l l l x)) (f l)
-- {-# COMPILE AGDA2HS lensD #-}

-- lensWrappedTree : {a : Set} {f : Set -> Set} {{fFunctor : Functor f}}
--         -> ((Quadrant a) -> f (Quadrant a)) -> QuadTree a -> f (QuadTree a)
-- lensWrappedTree f (Wrapper quad l w d) = fmap (λ q -> (Wrapper q l w d)) (f quad)
-- {-# COMPILE AGDA2HS lensWrappedTree #-}

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

