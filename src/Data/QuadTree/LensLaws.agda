module Data.QuadTree.LensLaws where

open import Haskell.Prelude renaming (zero to Z; suc to S)
open import Data.QuadTree.Lens
open import Data.QuadTree.Logic
open import Data.QuadTree.PropDepthRelation
open import Data.QuadTree.InternalAgda


---- Generic lens laws

ViewSet : {a b : Set} -> (l : CLens a b) -> Set
ViewSet {a} {b} l = (v : b) (s : a) -> view l (set l v s) ≡ v

SetView : {a b : Set} -> (l : CLens a b) -> Set
SetView {a} {b} l = (s : a) -> set l (view l s) s ≡ s

SetSet : {a b : Set} -> (l : CLens a b) -> Set
SetSet {a} {b} l = (v1 v2 : b) (s : a) -> set l v2 (set l v1 s) ≡ set l v2 s

---- Lens laws for lensWrappedTree

prop_WrappedTree_ViewSet : 
    {t : Set} {{eqT : Eq t}} (dep : Nat) 
    -> ViewSet (lensWrappedTree {t} {dep})
prop_WrappedTree_ViewSet {t} dep (CValidQuadrant qdn {pn}) (CValidQuadTree (Wrapper qdo (w , h)) {p} {q}) = refl

prop_WrappedTree_SetView : 
    {t : Set} {{eqT : Eq t}} (dep : Nat) 
    -> SetView (lensWrappedTree {t} {dep})
prop_WrappedTree_SetView {t} dep (CValidQuadTree (Wrapper qdo (w , h)) {p} {q}) = refl

prop_WrappedTree_SetSet : 
    {t : Set} {{eqT : Eq t}} (dep : Nat) 
    -> SetSet (lensWrappedTree {t} {dep})
prop_WrappedTree_SetSet {t} dep (CValidQuadrant qd1 {p1}) (CValidQuadrant qd2 {p2}) (CValidQuadTree (Wrapper qdo (w , h)) {p} {q}) = refl

--- Lens laws for lensLeaf

prop_Leaf_ViewSet : 
    {t : Set} {{eqT : Eq t}}
    -> ViewSet (lensLeaf {t})
prop_Leaf_ViewSet {t} v (CValidQuadrant (Leaf lv) {pn}) = refl

prop_Leaf_SetView : 
    {t : Set} {{eqT : Eq t}}
    -> SetView (lensLeaf {t})
prop_Leaf_SetView {t} (CValidQuadrant (Leaf lv) {IsTrue.itsTrue}) = refl

prop_Leaf_SetSet : 
    {t : Set} {{eqT : Eq t}}
    -> SetSet (lensLeaf {t})
prop_Leaf_SetSet {t} v1 v2 (CValidQuadrant (Leaf lv) {pn}) = refl