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

---- In order to proof this we need some form of Extensionality
-- Because this is quite a complicated application of Extensionality, I did not proof it from generic Extensionality, but just postulated it seperately.
-- It is needed because Agda eagerly applies implicit arguments at the start of a function, which I don't want it to do
-- This can be used to reverse agda doing that

postulate
    FunctorExtensionality : 
        {t : Set} {{eqT : Eq t}} -> {deps : Nat} ->
        {la lb : CLens (VQuadrant t {S deps}) t}
        -> ({f : Set -> Set} -> {{ff : Functor f}} -> (la {f} {{ff}} ≡ lb {f} {{ff}}))
        -> (λ {f} ⦃ ff ⦄ → la {f} {{ff}}) ≡ (λ {f} ⦃ ff ⦄ → lb {f} {{ff}})

---- Lens laws for go

ValidLens-go-ViewSet : 
    {t : Set} {{eqT : Eq t}}
    -> (loc : Nat × Nat) -> (dep : Nat)
    -> ViewSet (go {t} loc dep)
postulate 
    ValidLens-go-SetView : 
        {t : Set} {{eqT : Eq t}}
        -> (loc : Nat × Nat) -> (dep : Nat)
        -> SetView (go {t} loc dep)
postulate 
    ValidLens-go-SetSet : 
        {t : Set} {{eqT : Eq t}}
        -> (loc : Nat × Nat) -> (dep : Nat)
        -> SetSet (go {t} loc dep)

ValidLens-go : {t : Set} {{eqT : Eq t}}
    -> (loc : Nat × Nat) -> (dep : Nat)
    -> ValidLens (VQuadrant t {dep}) t
ValidLens-go {t} {{eqT}} loc dep = CValidLens (go loc dep) (ValidLens-go-ViewSet loc dep) (ValidLens-go-SetView loc dep) (ValidLens-go-SetSet loc dep)


ValidLens-go-ViewSet loc Z v cvq@(CVQuadrant (Leaf x) {p}) = refl
ValidLens-go-ViewSet {t} (x , y) dep@(S deps) v cvq@(CVQuadrant qd {p}) =
    begin
        view 
            (λ {f} ⦃ ff ⦄ → (ifc y < mid
                then (lensA ∘ go {t} (mod x mid {pow_not_zero_cv deps} , mod y mid {pow_not_zero_cv deps}) deps ⦃ ff ⦄  )
                else (lensC ∘ go {t} (mod x mid {pow_not_zero_cv deps} , mod y mid {pow_not_zero_cv deps}) deps ⦃ ff ⦄  )))
            (set 
                (λ {f} ⦃ ff ⦄ → (ifc y < mid
                    then (lensA ∘ go {t} (mod x mid {pow_not_zero_cv deps} , mod y mid {pow_not_zero_cv deps}) deps ⦃ ff ⦄  )
                    else (lensC ∘ go {t} (mod x mid {pow_not_zero_cv deps} , mod y mid {pow_not_zero_cv deps}) deps ⦃ ff ⦄  )))
                v cvq)
    =⟨ cong {x = (λ {f} ⦃ ff ⦄ → (ifc y < mid
                then (lensA ∘ go {t} (mod x mid {pow_not_zero_cv deps} , mod y mid {pow_not_zero_cv deps}) deps {f} ⦃ ff ⦄  )
                else (lensC ∘ go {t} (mod x mid {pow_not_zero_cv deps} , mod y mid {pow_not_zero_cv deps}) deps {f} ⦃ ff ⦄  )))} 
            {y = (λ {f} ⦃ ff ⦄ → (lensA ∘ go {t} (mod x mid {pow_not_zero_cv deps} , mod y mid {pow_not_zero_cv deps}) deps {f} ⦃ ff ⦄))}
            (λ (g : CLens (VQuadrant t {dep}) t) -> view g (set g v cvq)) 
            (FunctorExtensionality (ifcTrue (y < mid) yeet)) ⟩
        view 
            (λ {f} ⦃ ff ⦄ → (lensA ∘ go {t} (mod x mid {pow_not_zero_cv deps} , mod y mid {pow_not_zero_cv deps}) deps {f} ⦃ ff ⦄))
            (set 
                (λ {f} ⦃ ff ⦄ → (lensA ∘ go {t} (mod x mid {pow_not_zero_cv deps} , mod y mid {pow_not_zero_cv deps}) deps {f} ⦃ ff ⦄  ))
                v cvq)
    =⟨ prop-Composition-ViewSet (ValidLens-LensA) (ValidLens-go (mod x (pow 2 deps) , mod y (pow 2 deps)) deps) v cvq ⟩
        v
    end

    where
        mid = pow 2 deps
        postulate yeet : IsTrue (y < mid)