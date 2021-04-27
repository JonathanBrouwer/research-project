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

data ValidLens (a b : Set) : Set₁ where
  CValidLens : (l : CLens a b) -> ViewSet l -> SetView l -> SetSet l -> ValidLens a b

toLens : ValidLens a b -> CLens a b
toLens (CValidLens l _ _ _) = l

---- Lens postulates
-- These are provable using the isomorphism to the getter+setter style

postulate 
    prop_view_compose : {a b c : Set} 
        -> (l1 : ValidLens a b)
        -> (l2 : ValidLens b c)
        -> (v : a)
        -> (view ((toLens l1) ∘ (toLens l2))) v ≡ (view (toLens l2) ∘ view (toLens l1)) v
    prop_set_compose : {a b c : Set} 
        -> (l1 : ValidLens a b)
        -> (l2 : ValidLens b c)
        -> (v : a) (t : c)
        -> (set ((toLens l1) ∘ (toLens l2))) t v ≡ over (toLens l1) (set (toLens l2) t) v
    prop_over_is_setget : {a b : Set} 
        -> (l : ValidLens a b)
        -> (f : b -> b) (v : a)
        -> over (toLens l) f v ≡ set (toLens l) (f (view (toLens l) v)) v

prop_set_compose_dir : {a b c : Set} 
    -> (l1 : ValidLens a b)
    -> (l2 : ValidLens b c)
    -> (v : a) (t : c)
    -> (set ((toLens l1) ∘ (toLens l2))) t v ≡ set (toLens l1) ((set (toLens l2) t) (view (toLens l1) v)) v
prop_set_compose_dir vl1@(CValidLens l1 vs1 sv1 ss1) vl2@(CValidLens l2 vs2 sv2 ss2) v t =
    begin
        set (l1 ∘ l2) t v
    =⟨ prop_set_compose vl1 vl2 v t ⟩
        over l1 (set l2 t) v
    =⟨ prop_over_is_setget vl1 (set l2 t) v ⟩
        set l1 ((set l2 t) (view l1 v)) v
    end

prop_Merge_ViewSet : {a b c : Set} 
    -> (l1 : ValidLens a b)
    -> (l2 : ValidLens b c)
    -> ViewSet ((toLens l1) ∘ (toLens l2))
prop_Merge_ViewSet {a} {b} {c} vl1@(CValidLens l1 vs1 sv1 ss1) vl2@(CValidLens l2 vs2 sv2 ss2) v s = 
    begin 
        view (l1 ∘ l2) (set (l1 ∘ l2) v s) 
    =⟨ prop_view_compose vl1 vl2 (set (l1 ∘ l2) v s) ⟩
        view l2 ( view l1 (set (l1 ∘ l2) v s))
    =⟨ cong (view l2 ∘ view l1) (prop_set_compose_dir vl1 vl2 s v) ⟩
        view l2 ( view l1 (set l1 ((set l2 v) (view l1 s)) s))
    =⟨ cong (view l2) (vs1 ((set l2 v) (view l1 s)) s) ⟩
        view l2 (set l2 v (view l1 s))
    =⟨ vs2 v (view l1 s) ⟩
        v 
    end

prop_Merge_SetView : {a b c : Set} 
    -> (l1 : ValidLens a b)
    -> (l2 : ValidLens b c)
    -> SetView ((toLens l1) ∘ (toLens l2))
prop_Merge_SetView {a} {b} {c} vl1@(CValidLens l1 vs1 sv1 ss1) vl2@(CValidLens l2 vs2 sv2 ss2) s = 
    begin 
        set (l1 ∘ l2) (view (l1 ∘ l2) s) s
    =⟨ cong (λ x -> set (l1 ∘ l2) x s) (prop_view_compose vl1 vl2 s) ⟩
        set (l1 ∘ l2) (view l2 (view l1 s)) s 
    =⟨ prop_set_compose_dir vl1 vl2 s (view l2 (view l1 s)) ⟩
        set l1 (set l2 (view l2 (view l1 s)) (view l1 s)) s
    =⟨ cong (λ x -> set l1 x s) (sv2 (view l1 s)) ⟩
        set l1 (view l1 s) s
    =⟨ sv1 s ⟩
        s 
    end

prop_Merge_SetSet : {a b c : Set} 
    -> (l1 : ValidLens a b)
    -> (l2 : ValidLens b c)
    -> SetSet ((toLens l1) ∘ (toLens l2))
prop_Merge_SetSet {a} {b} {c} vl1@(CValidLens l1 vs1 sv1 ss1) vl2@(CValidLens l2 vs2 sv2 ss2) v1 v2 s =
    begin 
        set (l1 ∘ l2) v2 (set (l1 ∘ l2) v1 s)
    =⟨ cong (set (l1 ∘ l2) v2) (prop_set_compose_dir vl1 vl2 s v1) ⟩
        set (l1 ∘ l2) v2 (set l1 (set l2 v1 (view l1 s)) s)
    =⟨ prop_set_compose_dir vl1 vl2 (set l1 ((set l2 v1) (view l1 s)) s) v2 ⟩
        set l1 
            (set l2 
                v2 
                (view l1 
                    (set l1 ((set l2 v1) (view l1 s)) s)
                )
            ) 
            (set l1 (set l2 v1 (view l1 s)) s)
    =⟨ cong (λ x -> set l1 (set l2 v2 x) (set l1 ((set l2 v1) (view l1 s)) s)) (vs1 ((set l2 v1) (view l1 s)) s) ⟩
        set l1 
            (set l2 
                v2 
                (set l2 v1 (view l1 s))
            ) 
            (set l1 (set l2 v1 (view l1 s)) s)
    =⟨ cong (λ x -> set l1 x (set l1 (set l2 v1 (view l1 s)) s)) (ss2 v1 v2 (view l1 s)) ⟩
        set l1 
            (set l2 
                v2 
                (view l1 s)
            ) 
            (set l1 (set l2 v1 (view l1 s)) s)
    =⟨ ss1 ((set l2 v1 (view l1 s))) ((set l2 v2 (view l1 s))) s ⟩
        set l1 
            (set l2 
                v2 
                (view l1 s)
            ) 
            s
    =⟨ sym (prop_set_compose_dir vl1 vl2 s v2) ⟩
        set (l1 ∘ l2) v2 s
    end

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
