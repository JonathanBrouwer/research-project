module Data.QuadTree.LensLaws where

open import Haskell.Prelude renaming (zero to Z; suc to S)
open import Data.QuadTree.Lens
open import Data.QuadTree.Logic
open import Data.QuadTree.PropDepthRelation
open import Data.QuadTree.InternalAgda


---- Generic lens laws

ViewSet = {a b : Set} -> (l : CLens a b) -> (v : b) (s : a) -> view l (set l v s) ≡ v
SetView = {a b : Set} -> (l : CLens a b) -> (s : a) -> set l (view l s) s ≡ s
SetSet = {a b : Set} -> (l : CLens a b) -> (v1 v2 : b) (s : a) -> set l v2 (set l v1 s) ≡ set l v2 s

---- Lens laws for lensWrappedTree

prop_WrappedTree_ViewSet : 
    -- Arguments for lensWrappedTree
    {t : Set} {{eqT : Eq t}} (dep : Nat) 
    -- Arguments for law
    -> (v : (ValidQuadrant t {dep})) (s : (ValidQuadTree t {dep})) 
    -- Law
    -> view (lensWrappedTree {t} {dep}) (set (lensWrappedTree {t} {dep}) v s) ≡ v
prop_WrappedTree_ViewSet {t} dep (CValidQuadrant qdn {pn}) (CValidQuadTree (Wrapper qdo (w , h)) {p} {q}) = refl

prop_WrappedTree_SetView : 
    -- Arguments for lensWrappedTree
    {t : Set} {{eqT : Eq t}} (dep : Nat) 
    -- Arguments for law
    -> (s : (ValidQuadTree t {dep})) 
    -- Law
    -> set (lensWrappedTree {t} {dep}) (view (lensWrappedTree {t} {dep}) s) s ≡ s
prop_WrappedTree_SetView {t} dep (CValidQuadTree (Wrapper qdo (w , h)) {p} {q}) = refl

prop_WrappedTree_SetSet : 
    -- Arguments for lensWrappedTree
    {t : Set} {{eqT : Eq t}} (dep : Nat) 
    -- Arguments for law
    -> (v1 : (ValidQuadrant t {dep})) (v2 : (ValidQuadrant t {dep})) (s : (ValidQuadTree t {dep})) 
    -- Law
    -> set (lensWrappedTree {t} {dep}) v2 (set (lensWrappedTree {t} {dep}) v1 s) ≡ set (lensWrappedTree {t} {dep}) v2 s
prop_WrappedTree_SetSet {t} dep (CValidQuadrant qd1 {p1}) (CValidQuadrant qd2 {p2}) (CValidQuadTree (Wrapper qdo (w , h)) {p} {q}) = refl