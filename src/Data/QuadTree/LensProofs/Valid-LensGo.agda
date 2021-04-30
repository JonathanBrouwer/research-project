-- {-# OPTIONS --show-implicit --show-irrelevant #-}
module Data.QuadTree.LensProofs.Valid-LensGo where

open import Haskell.Prelude renaming (zero to Z; suc to S)
open import Data.Lens.Lens
open import Data.Logic
open import Data.QuadTree.InternalAgda
open import Agda.Primitive
open import Data.Lens.Proofs.LensLaws
open import Data.Lens.Proofs.LensPostulates
open import Data.Lens.Proofs.LensComposition
open import Data.QuadTree.LensProofs.Valid-LensLeaf
open import Data.QuadTree.LensProofs.Valid-LensA
open import Data.QuadTree.LensProofs.Valid-LensBCD
open import Axiom.Extensionality.Propositional


---- Lens laws for go

convertA : {t : Set} {{eqT : Eq t}}
    -> (loc : Nat × Nat) -> (deps : Nat)
    -> IsTrue (fst loc < pow 2 deps) -> IsTrue (snd loc < pow 2 deps)
    -> {f : Set -> Set} {{ff : Functor f}} -> (g : t -> f t) -> (v : VQuadrant t {S deps})
    -> (go loc (S deps) {f} g v) ≡ (lensA {t} {deps} ∘ go loc deps {f}) g v
convertA {t} (x , y) deps px py {f} g v =
    begin
        (go (x , y) (S deps) {f} g v)
    =⟨ trans (ifcTrue (y < pow 2 deps) py) (ifcTrue (x < pow 2 deps) px) ⟩
        lensA (go (x , y) deps g) v
    end

convertB : {t : Set} {{eqT : Eq t}}
    -> (loc : Nat × Nat) -> (deps : Nat)
    -> (px : IsFalse (fst loc < pow 2 deps)) -> (py : IsTrue (snd loc < pow 2 deps))
    -> {f : Set -> Set} {{ff : Functor f}} -> (g : t -> f t) -> (v : VQuadrant t {S deps})
    -> (go loc (S deps) {f} g v) ≡ (lensB {t} {deps} ∘ go (_-_ (fst loc) (pow 2 deps) {{px}} , snd loc) deps {f}) g v
convertB {t} (x , y) deps px py {f} g v =
    begin
        (go (x , y) (S deps) {f} g v)
    =⟨ trans (ifcTrue (y < pow 2 deps) py) (ifcFalse (x < pow 2 deps) px) ⟩
        (lensB {t} {deps} ∘ go (_-_ x (pow 2 deps) {{px}} , y) deps {f}) g v
    end

convertC : {t : Set} {{eqT : Eq t}}
    -> (loc : Nat × Nat) -> (deps : Nat)
    -> (px : IsTrue (fst loc < pow 2 deps)) -> (py : IsFalse (snd loc < pow 2 deps))
    -> {f : Set -> Set} {{ff : Functor f}} -> (g : t -> f t) -> (v : VQuadrant t {S deps})
    -> (go loc (S deps) {f} g v) ≡ (lensC {t} {deps} ∘ go (fst loc , _-_ (snd loc) (pow 2 deps) {{py}} ) deps {f}) g v
convertC {t} (x , y) deps px py {f} g v =
    begin
        (go (x , y) (S deps) {f} g v)
    =⟨ trans (ifcFalse (y < pow 2 deps) py) (ifcTrue (x < pow 2 deps) px) ⟩
        (lensC {t} {deps} ∘ go (x , _-_ y (pow 2 deps) {{py}} ) deps {f}) g v
    end

convertD : {t : Set} {{eqT : Eq t}}
    -> (loc : Nat × Nat) -> (deps : Nat)
    -> (px : IsFalse (fst loc < pow 2 deps)) -> (py : IsFalse (snd loc < pow 2 deps))
    -> {f : Set -> Set} {{ff : Functor f}} -> (g : t -> f t) -> (v : VQuadrant t {S deps})
    -> (go loc (S deps) {f} g v) ≡ (lensD {t} {deps} ∘ go (_-_ (fst loc) (pow 2 deps) {{px}} , _-_ (snd loc) (pow 2 deps) {{py}} ) deps {f}) g v
convertD {t} (x , y) deps px py {f} g v =
    begin
        (go (x , y) (S deps) {f} g v)
    =⟨ trans (ifcFalse (y < pow 2 deps) py) (ifcFalse (x < pow 2 deps) px) ⟩
        (lensD {t} {deps} ∘ go (_-_ x (pow 2 deps) {{px}} , _-_ y (pow 2 deps) {{py}} ) deps {f}) g v
    end

    -- =⟨⟩
    --     (ifc y < pow 2 deps then
    --         ifc x < pow 2 deps 
    --             then lensA (go (x , y) deps g) v
    --             else lensB (go ((x - pow 2 deps) , y) deps g) v
    --     else
    --         ifc x < pow 2 deps 
    --             then lensC (go (x , (y - pow 2 deps)) deps g) v
    --             else lensD (go ((x - pow 2 deps) , (y - pow 2 deps)) deps g) v)

postulate 
    ValidLens-go-ViewSet : 
        {t : Set} {{eqT : Eq t}}
        -> (loc : Nat × Nat) -> (dep : Nat)
        -> ViewSet (go {t} loc dep)
    ValidLens-go-SetView : 
        {t : Set} {{eqT : Eq t}}
        -> (loc : Nat × Nat) -> (dep : Nat)
        -> SetView (go {t} loc dep)
    ValidLens-go-SetSet : 
        {t : Set} {{eqT : Eq t}}
        -> (loc : Nat × Nat) -> (dep : Nat)
        -> SetSet (go {t} loc dep)

ValidLens-go : {t : Set} {{eqT : Eq t}}
    -> (loc : Nat × Nat) -> (dep : Nat)
    -> ValidLens (VQuadrant t {dep}) t
ValidLens-go {t} {{eqT}} (x , y) dep = CValidLens (go (x , y) dep) (ValidLens-go-ViewSet (x , y) dep) (ValidLens-go-SetView (x , y) dep) (ValidLens-go-SetSet (x , y) dep)
