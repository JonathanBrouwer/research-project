{-# OPTIONS --show-implicit --show-irrelevant #-}
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

-- ExtensionalityTest : (a b : Level) → Set _
-- ExtensionalityTest a b =
--   {A : Set a} {B : A → Set b} {f g : {{x : A}} → B x} →
--   (∀ {x} → f {{x}} ≡ g {{x}}) → (λ {{x}} → f {{x}}) ≡ (λ {{x}} → g {{x}})

---- I think this is provable without extensionality, but assuming it makes it a lot easier
postulate
    ext0 : Extensionality lzero lzero
    ext0-impl : ExtensionalityImplicit lzero lzero


ValidLens-go : {t : Set} {{eqT : Eq t}}
    -> (loc : Nat × Nat) -> (dep : Nat)
    -> ValidLens (VQuadrant t {dep}) t

---- Lens laws for go

convertA : {t : Set} {{eqT : Eq t}}
    -> (loc : Nat × Nat) -> (deps : Nat)
    -> IsTrue (fst loc < pow 2 deps) -> IsTrue (snd loc < pow 2 deps)
    -> {f : Set -> Set} {{ff : Functor f}} 
    -> (go loc (S deps)) ≡ (lensA {t} {deps} ∘ go loc deps)
convertA {t} (x , y) deps px py {f} =
    ext0 (λ (g : t -> f t) -> ext0 (λ (v : VQuadrant t {S deps}) -> trans (ifcTrue (y < pow 2 deps) py) (ifcTrue (x < pow 2 deps) px)))

convertB : {t : Set} {{eqT : Eq t}}
    -> (loc : Nat × Nat) -> (deps : Nat)
    -> (px : IsFalse (fst loc < pow 2 deps)) -> (py : IsTrue (snd loc < pow 2 deps))
    -> {f : Set -> Set} {{ff : Functor f}}
    -> (go loc (S deps) {f}) ≡ (lensB {t} {deps} ∘ go (_-_ (fst loc) (pow 2 deps) {{px}} , snd loc) deps {f})
convertB {t} (x , y) deps px py {f} =
    ext0 (λ (g : t -> f t) -> 
    ext0 (λ (v : VQuadrant t {S deps}) -> 
        trans (ifcTrue (y < pow 2 deps) py) (ifcFalse (x < pow 2 deps) px)))

convertC : {t : Set} {{eqT : Eq t}}
    -> (loc : Nat × Nat) -> (deps : Nat)
    -> (px : IsTrue (fst loc < pow 2 deps)) -> (py : IsFalse (snd loc < pow 2 deps))
    -> {f : Set -> Set} {{ff : Functor f}}
    -> (go loc (S deps) {f}) ≡ (lensC {t} {deps} ∘ go (fst loc , _-_ (snd loc) (pow 2 deps) {{py}} ) deps {f})
convertC {t} (x , y) deps px py {f} =
    ext0 (λ (g : t -> f t) -> 
    ext0 (λ (v : VQuadrant t {S deps}) -> 
        trans (ifcFalse (y < pow 2 deps) py) (ifcTrue (x < pow 2 deps) px)))

convertD : {t : Set} {{eqT : Eq t}}
    -> (loc : Nat × Nat) -> (deps : Nat)
    -> (px : IsFalse (fst loc < pow 2 deps)) -> (py : IsFalse (snd loc < pow 2 deps))
    -> {f : Set -> Set} {{ff : Functor f}}
    -> (go loc (S deps) {f}) ≡ (lensD {t} {deps} ∘ go (_-_ (fst loc) (pow 2 deps) {{px}} , _-_ (snd loc) (pow 2 deps) {{py}} ) deps {f})
convertD {t} (x , y) deps px py {f} =
    ext0 (λ (g : t -> f t) -> 
    ext0 (λ (v : VQuadrant t {S deps}) -> 
        trans (ifcFalse (y < pow 2 deps) py) (ifcFalse (x < pow 2 deps) px)))

-- convert : {t : Set} {{eqT : Eq t}}
--     -> (loc : Nat × Nat) -> (deps : Nat)
--     -> {f : Set -> Set} {{ff : Functor f}}
--     -> (go loc (S deps) {f}) ≡ {!   !}
-- convert {t} (x , y) deps {f} = {!  go (x , y) deps  !}

--CLens (VQuadrant {S deps}) (VQuadrant {deps})
--CLens (VQuadrant {deps}) t

-- ValidLens-go-ViewSet-Sub :
--     {t : Set} {{eqT : Eq t}}
--     -> (loc : Nat × Nat) -> (dep : Nat)
--     -> ViewSet (go {t} loc dep)
-- ValidLens-go-ViewSet-Sub loc Z v cvq@(CVQuadrant (Leaf x)) = refl
-- ValidLens-go-ViewSet-Sub {t} loc@(x , y) dep@(S deps) v cvq@(CVQuadrant qd) =
--     begin
--         (view (go loc dep) (set (go loc dep) v cvq))
--     =⟨⟩
--         {!   !}
--     =⟨ {!   !} ⟩
--         v
--     end

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

ValidLens-go {t} {{eqT}} (x , y) dep = CValidLens (go (x , y) dep) (ValidLens-go-ViewSet (x , y) dep) (ValidLens-go-SetView (x , y) dep) (ValidLens-go-SetSet (x , y) dep)
