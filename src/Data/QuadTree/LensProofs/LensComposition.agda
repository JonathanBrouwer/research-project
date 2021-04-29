module Data.QuadTree.LensProofs.LensComposition where

open import Haskell.Prelude renaming (zero to Z; suc to S)
open import Data.QuadTree.Lens
open import Data.QuadTree.Logic
open import Data.QuadTree.InternalAgda
open import Agda.Primitive
open import Data.QuadTree.LensProofs.LensLaws
open import Data.QuadTree.LensProofs.LensPostulates

-- We proof that if we have 2 valid lenses l1 and l2, that l1 ∘ l2 is also valid
-- We do this law by law

prop-Composition-ViewSet : {a b c : Set} 
    -> (l1 : ValidLens a b)
    -> (l2 : ValidLens b c)
    -> ViewSet ((toLens l1) ∘ (toLens l2))
prop-Composition-ViewSet {a} {b} {c} vl1@(CValidLens l1 vs1 sv1 ss1) vl2@(CValidLens l2 vs2 sv2 ss2) v s = 
    begin 
        view (l1 ∘ l2) (set (l1 ∘ l2) v s) 
    =⟨ prop-view-compose vl1 vl2 (set (l1 ∘ l2) v s) ⟩
        view l2 ( view l1 (set (l1 ∘ l2) v s))
    =⟨ cong (view l2 ∘ view l1) (prop-set-compose-dir vl1 vl2 s v) ⟩
        view l2 ( view l1 (set l1 ((set l2 v) (view l1 s)) s))
    =⟨ cong (view l2) (vs1 ((set l2 v) (view l1 s)) s) ⟩
        view l2 (set l2 v (view l1 s))
    =⟨ vs2 v (view l1 s) ⟩
        v 
    end

prop-Composition-SetView : {a b c : Set} 
    -> (l1 : ValidLens a b)
    -> (l2 : ValidLens b c)
    -> SetView ((toLens l1) ∘ (toLens l2))
prop-Composition-SetView {a} {b} {c} vl1@(CValidLens l1 vs1 sv1 ss1) vl2@(CValidLens l2 vs2 sv2 ss2) s = 
    begin 
        set (l1 ∘ l2) (view (l1 ∘ l2) s) s
    =⟨ cong (λ x -> set (l1 ∘ l2) x s) (prop-view-compose vl1 vl2 s) ⟩
        set (l1 ∘ l2) (view l2 (view l1 s)) s 
    =⟨ prop-set-compose-dir vl1 vl2 s (view l2 (view l1 s)) ⟩
        set l1 (set l2 (view l2 (view l1 s)) (view l1 s)) s
    =⟨ cong (λ x -> set l1 x s) (sv2 (view l1 s)) ⟩
        set l1 (view l1 s) s
    =⟨ sv1 s ⟩
        s 
    end

prop-Composition-SetSet : {a b c : Set} 
    -> (l1 : ValidLens a b)
    -> (l2 : ValidLens b c)
    -> SetSet ((toLens l1) ∘ (toLens l2))
prop-Composition-SetSet {a} {b} {c} vl1@(CValidLens l1 vs1 sv1 ss1) vl2@(CValidLens l2 vs2 sv2 ss2) v1 v2 s =
    begin 
        set (l1 ∘ l2) v2 (set (l1 ∘ l2) v1 s)
    =⟨ cong (set (l1 ∘ l2) v2) (prop-set-compose-dir vl1 vl2 s v1) ⟩
        set (l1 ∘ l2) v2 (set l1 (set l2 v1 (view l1 s)) s)
    =⟨ prop-set-compose-dir vl1 vl2 (set l1 ((set l2 v1) (view l1 s)) s) v2 ⟩
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
    =⟨ sym (prop-set-compose-dir vl1 vl2 s v2) ⟩
        set (l1 ∘ l2) v2 s
    end

-- Create a function that does the composition
composeLens : {a b c : Set} -> (ValidLens a b) -> (ValidLens b c) -> (ValidLens a c)
composeLens vl1@(CValidLens l1 vs1 sv1 ss1) vl2@(CValidLens l2 vs2 sv2 ss2) 
    = CValidLens (l1 ∘ l2) (prop-Composition-ViewSet vl1 vl2) (prop-Composition-SetView vl1 vl2) (prop-Composition-SetSet vl1 vl2)