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

{-
I spend close to 50 hours on this file, at the time of writing more than the rest of the lens proofs combined.
The file still looks horrible and there is very serious code duplication, but I honestly wish to never look at this file again.

In order to proof this we need some form of Extensionality
Because this is quite a complicated application of Extensionality, I did not proof it from generic Extensionality, but just postulated it seperately.
It is needed because Agda eagerly applies implicit arguments at the start of a function, which I don't want it to do
This can be used to reverse agda doing that
-}



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
ValidLens-go {t} {{eqT}} loc dep = CValidLens (go loc dep) (ValidLens-go-ViewSet loc dep) (ValidLens-go-SetView loc dep) (ValidLens-go-SetSet loc dep)


ValidLens-go-ViewSet loc Z v cvq@(CVQuadrant (Leaf x) {p}) = refl
ValidLens-go-ViewSet {t} (x , y) dep@(S deps) v cvq@(CVQuadrant qd {p}) =
    ifc y < mid then (λ {{py}} ->
        ifc x < mid then (λ {{px}} ->
            trans 
                (cong 
                    -- We need to explicitly provide the x, otherwise agda gets confused
                    {x = λ {f} ⦃ ff ⦄ → go (x , y) (S deps) {f} {{ff}} } 
                    -- We cong over the law, applying the transformation to go
                    (λ (g : CLens (VQuadrant t {dep}) t) -> view g (set g v cvq)) 
                    -- Select only the lensA branch
                    (FunctorExtensionality (trans (ifTrue (y < mid) py) (ifTrue (x < mid) px))))
                -- Then use the property of composition to proof the law
                (prop-Composition-ViewSet (ValidLens-LensA) (ValidLens-go (mod x mid , mod y mid) deps) v cvq)
        ) else (λ {{px}} ->
            trans 
                (cong 
                    -- We need to explicitly provide the x, otherwise agda gets confused
                    {x = λ {f} ⦃ ff ⦄ → go (x , y) (S deps) {f} {{ff}} } 
                    -- We cong over the law, applying the transformation to go
                    (λ (g : CLens (VQuadrant t {dep}) t) -> view g (set g v cvq)) 
                    -- Select only the lensB branch
                    (FunctorExtensionality (trans (ifTrue (y < mid) py) (ifFalse (x < mid) px))))
                -- Then use the property of composition to proof the law
                (prop-Composition-ViewSet (ValidLens-LensB) (ValidLens-go (mod x mid , mod y mid) deps) v cvq)
        )
    ) else (λ {{py}} ->
        ifc x < mid then (λ {{px}} ->
            trans 
                (cong 
                    -- We need to explicitly provide the x, otherwise agda gets confused
                    {x = λ {f} ⦃ ff ⦄ → go (x , y) (S deps) {f} {{ff}} } 
                    -- We cong over the law, applying the transformation to go
                    (λ (g : CLens (VQuadrant t {dep}) t) -> view g (set g v cvq)) 
                    -- Select only the lensC branch
                    (FunctorExtensionality (trans (ifFalse (y < mid) py) (ifTrue (x < mid) px))))
                -- Then use the property of composition to proof the law
                (prop-Composition-ViewSet (ValidLens-LensC) (ValidLens-go (mod x mid , mod y mid) deps) v cvq)
        ) else (λ {{px}} ->
            trans 
                (cong 
                    -- We need to explicitly provide the x, otherwise agda gets confused
                    {x = λ {f} ⦃ ff ⦄ → go (x , y) (S deps) {f} {{ff}} } 
                    -- We cong over the law, applying the transformation to go
                    (λ (g : CLens (VQuadrant t {dep}) t) -> view g (set g v cvq)) 
                    -- Select only the lensD branch
                    (FunctorExtensionality (trans (ifFalse (y < mid) py) (ifFalse (x < mid) px))))
                -- Then use the property of composition to proof the law
                (prop-Composition-ViewSet (ValidLens-LensD) (ValidLens-go (mod x mid , mod y mid) deps) v cvq)
        )
    )
    where
        mid = pow 2 deps

ValidLens-go-SetView loc Z cvq@(CVQuadrant (Leaf x) {p}) = refl
ValidLens-go-SetView {t} (x , y) dep@(S deps) cvq@(CVQuadrant qd {p}) =
    ifc y < mid then (λ {{py}} ->
        ifc x < mid then (λ {{px}} ->
            trans 
                (cong 
                    -- We need to explicitly provide the x, otherwise agda gets confused
                    {x = λ {f} ⦃ ff ⦄ → go (x , y) (S deps) {f} {{ff}} } 
                    -- We cong over the law, applying the transformation to go
                    (λ (g : CLens (VQuadrant t {dep}) t) -> set g (view g cvq) cvq) 
                    -- Select only the lensA branch
                    (FunctorExtensionality (trans (ifTrue (y < mid) py) (ifTrue (x < mid) px))))
                -- Then use the property of composition to proof the law
                (prop-Composition-SetView (ValidLens-LensA) (ValidLens-go (mod x mid , mod y mid) deps) cvq)
        ) else (λ {{px}} ->
            trans 
                (cong 
                    -- We need to explicitly provide the x, otherwise agda gets confused
                    {x = λ {f} ⦃ ff ⦄ → go (x , y) (S deps) {f} {{ff}} } 
                    -- We cong over the law, applying the transformation to go
                    (λ (g : CLens (VQuadrant t {dep}) t) -> set g (view g cvq) cvq) 
                    -- Select only the lensB branch
                    (FunctorExtensionality (trans (ifTrue (y < mid) py) (ifFalse (x < mid) px))))
                -- Then use the property of composition to proof the law
                (prop-Composition-SetView (ValidLens-LensB) (ValidLens-go (mod x mid , mod y mid) deps) cvq)
        )
    ) else (λ {{py}} ->
        ifc x < mid then (λ {{px}} ->
            trans 
                (cong 
                    -- We need to explicitly provide the x, otherwise agda gets confused
                    {x = λ {f} ⦃ ff ⦄ → go (x , y) (S deps) {f} {{ff}} } 
                    -- We cong over the law, applying the transformation to go
                    (λ (g : CLens (VQuadrant t {dep}) t) -> set g (view g cvq) cvq) 
                    -- Select only the lensC branch
                    (FunctorExtensionality (trans (ifFalse (y < mid) py) (ifTrue (x < mid) px))))
                -- Then use the property of composition to proof the law
                (prop-Composition-SetView (ValidLens-LensC) (ValidLens-go (mod x mid , mod y mid) deps) cvq)
        ) else (λ {{px}} ->
            trans 
                (cong 
                    -- We need to explicitly provide the x, otherwise agda gets confused
                    {x = λ {f} ⦃ ff ⦄ → go (x , y) (S deps) {f} {{ff}} } 
                    -- We cong over the law, applying the transformation to go
                    (λ (g : CLens (VQuadrant t {dep}) t) -> set g (view g cvq) cvq) 
                    -- Select only the lensD branch
                    (FunctorExtensionality (trans (ifFalse (y < mid) py) (ifFalse (x < mid) px))))
                -- Then use the property of composition to proof the law
                (prop-Composition-SetView (ValidLens-LensD) (ValidLens-go (mod x mid , mod y mid) deps) cvq)
        )
    )
    where
        mid = pow 2 deps

ValidLens-go-SetSet loc Z v1 v2 cvq@(CVQuadrant (Leaf x) {p}) = refl
ValidLens-go-SetSet {t} (x , y) dep@(S deps) v1 v2 cvq@(CVQuadrant qd {p}) =
    ifc y < mid then (λ {{py}} ->
        ifc x < mid then (λ {{px}} ->
            trans
                (cong 
                    -- We need to explicitly provide the x, otherwise agda gets confused
                    {x = λ {f} ⦃ ff ⦄ → go (x , y) (S deps) {f} {{ff}} } 
                    -- We cong over the law, applying the transformation to go
                    (λ (g : CLens (VQuadrant t {dep}) t) -> set g v2 (set g v1 cvq)) 
                    -- Select only the lensA branch
                    (FunctorExtensionality (trans (ifTrue (y < mid) py) (ifTrue (x < mid) px))))
                (trans
                    -- Then use the property of composition to proof the law
                    (prop-Composition-SetSet (ValidLens-LensA) (ValidLens-go (mod x mid , mod y mid) deps) v1 v2 cvq)
                    -- Finally, cong back over the law, applying the transformation to go
                    (sym $ cong {x = λ {f} ⦃ ff ⦄ → go (x , y) (S deps) {f} {{ff}}} 
                        (λ (g : CLens (VQuadrant t {dep}) t) -> set g v2 cvq) 
                        (FunctorExtensionality (trans (ifTrue (y < mid) py) (ifTrue (x < mid) px)))))
        ) else (λ {{px}} ->
            trans
                (cong 
                    -- We need to explicitly provide the x, otherwise agda gets confused
                    {x = λ {f} ⦃ ff ⦄ → go (x , y) (S deps) {f} {{ff}} } 
                    -- We cong over the law, applying the transformation to go
                    (λ (g : CLens (VQuadrant t {dep}) t) -> set g v2 (set g v1 cvq)) 
                    -- Select only the lensB branch
                    (FunctorExtensionality (trans (ifTrue (y < mid) py) (ifFalse (x < mid) px))))
                (trans
                    -- Then use the property of composition to proof the law
                    (prop-Composition-SetSet (ValidLens-LensB) (ValidLens-go (mod x mid , mod y mid) deps) v1 v2 cvq)
                    -- Finally, cong back over the law, applying the transformation to go
                    (sym $ cong {x = λ {f} ⦃ ff ⦄ → go (x , y) (S deps) {f} {{ff}}} 
                        (λ (g : CLens (VQuadrant t {dep}) t) -> set g v2 cvq) 
                        (FunctorExtensionality (trans (ifTrue (y < mid) py) (ifFalse (x < mid) px)))))
        )
    ) else (λ {{py}} ->
        ifc x < mid then (λ {{px}} ->
            trans
                (cong 
                    -- We need to explicitly provide the x, otherwise agda gets confused
                    {x = λ {f} ⦃ ff ⦄ → go (x , y) (S deps) {f} {{ff}} } 
                    -- We cong over the law, applying the transformation to go
                    (λ (g : CLens (VQuadrant t {dep}) t) -> set g v2 (set g v1 cvq)) 
                    -- Select only the lensC branch
                    (FunctorExtensionality (trans (ifFalse (y < mid) py) (ifTrue (x < mid) px))))
                (trans
                    -- Then use the property of composition to proof the law
                    (prop-Composition-SetSet (ValidLens-LensC) (ValidLens-go (mod x mid , mod y mid) deps) v1 v2 cvq)
                    -- Finally, cong back over the law, applying the transformation to go
                    (sym $ cong {x = λ {f} ⦃ ff ⦄ → go (x , y) (S deps) {f} {{ff}}} 
                        (λ (g : CLens (VQuadrant t {dep}) t) -> set g v2 cvq) 
                        (FunctorExtensionality (trans (ifFalse (y < mid) py) (ifTrue (x < mid) px)))))
        ) else (λ {{px}} ->
            trans
                (cong 
                    -- We need to explicitly provide the x, otherwise agda gets confused
                    {x = λ {f} ⦃ ff ⦄ → go (x , y) (S deps) {f} {{ff}} } 
                    -- We cong over the law, applying the transformation to go
                    (λ (g : CLens (VQuadrant t {dep}) t) -> set g v2 (set g v1 cvq)) 
                    -- Select only the lensD branch
                    (FunctorExtensionality (trans (ifFalse (y < mid) py) (ifFalse (x < mid) px))))
                (trans
                    -- Then use the property of composition to proof the law
                    (prop-Composition-SetSet (ValidLens-LensD) (ValidLens-go (mod x mid , mod y mid) deps) v1 v2 cvq)
                    -- Finally, cong back over the law, applying the transformation to go
                    (sym $ cong {x = λ {f} ⦃ ff ⦄ → go (x , y) (S deps) {f} {{ff}}} 
                        (λ (g : CLens (VQuadrant t {dep}) t) -> set g v2 cvq) 
                        (FunctorExtensionality (trans (ifFalse (y < mid) py) (ifFalse (x < mid) px)))))
        )
    )

    where
        mid = pow 2 deps
        postulate px : IsTrue (x < mid)
        postulate py : IsTrue (y < mid)
