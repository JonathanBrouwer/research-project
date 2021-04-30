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

ValidLens-go-ViewSet-Sub :
    {t : Set} {{eqT : Eq t}}
    -> (loc : Nat × Nat) -> (dep : Nat)
    -> {f : Set -> Set} {{ff : Functor f}} (v : t) (cvq : VQuadrant t {dep}) 
    -> (view (go loc dep) (set (go loc dep) v cvq)) ≡ v
    
ValidLens-go-ViewSet-Sub loc Z v cvq@(CVQuadrant (Leaf x)) = refl
ValidLens-go-ViewSet-Sub {t} loc@(x , y) dep@(S deps) v cvq@(CVQuadrant qd) =
    begin
        (view (go loc dep) (set (go loc dep) v cvq))
    =⟨⟩
        {! ifc (y < pow 2 deps) 
  then (ifc x < pow 2 deps 
    then (             (lensA ∘ go (x                 , y                ) deps) f v)
    else (λ {{xgt}} -> (lensB ∘ go (_-_ x mid {{xgt}} , y                ) deps) f v))
  else (λ {{ygt}} -> (ifc x < pow 2 deps
    then (             (lensC ∘ go (x                 , _-_ y mid {{ygt}}) deps) f v)
    else (λ {{xgt}} -> (lensD ∘ go (_-_ x mid {{xgt}} , _-_ y mid {{ygt}}) deps) f v)))  !}
    =⟨ {!   !} ⟩
        v
    end
