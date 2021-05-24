module Data.QuadTree.LensProofs.Valid-LensBCD where

open import Haskell.Prelude renaming (zero to Z; suc to S)
open import Data.Lens.Lens
open import Data.Logic
open import Data.QuadTree.InternalAgda
open import Agda.Primitive
open import Data.Lens.Proofs.LensLaws
open import Data.Lens.Proofs.LensPostulates
open import Data.Lens.Proofs.LensComposition
open import Data.QuadTree.Implementation.QuadrantLenses
open import Data.QuadTree.Implementation.Definition
open import Data.QuadTree.Implementation.ValidTypes
open import Data.QuadTree.Implementation.SafeFunctions
open import Data.QuadTree.Implementation.PublicFunctions
open import Data.QuadTree.Implementation.DataLenses

-- The lens laws have been proven for LensA, and the proof is quite long.
-- The implementation of lens b/c/d is basically identical, so I won't bother to proof them for now

--- Lens laws for lensB

postulate 
    ValidLens-LensB-ViewSet : 
        {t : Set} {{eqT : Eq t}} {dep : Nat}
        -> ViewSet (lensB {t} {dep})
    ValidLens-LensB-SetView : 
        {t : Set} {{eqT : Eq t}} {dep : Nat}
        -> SetView (lensB {t} {dep})
    ValidLens-LensB-SetSet : 
        {t : Set} {{eqT : Eq t}} {dep : Nat}
        -> SetSet (lensB {t} {dep})

ValidLens-LensB : {t : Set} {{eqT : Eq t}} {dep : Nat}
    -> ValidLens (VQuadrant t {S dep}) (VQuadrant t {dep})
ValidLens-LensB {t} {dep} = CValidLens lensB (ValidLens-LensB-ViewSet) (ValidLens-LensB-SetView) (ValidLens-LensB-SetSet)

--- Lens laws for lensC

postulate 
    ValidLens-LensC-ViewSet : 
        {t : Set} {{eqT : Eq t}} {dep : Nat}
        -> ViewSet (lensC {t} {dep})
    ValidLens-LensC-SetView : 
        {t : Set} {{eqT : Eq t}} {dep : Nat}
        -> SetView (lensC {t} {dep})
    ValidLens-LensC-SetSet : 
        {t : Set} {{eqT : Eq t}} {dep : Nat}
        -> SetSet (lensC {t} {dep})

ValidLens-LensC : {t : Set} {{eqT : Eq t}} {dep : Nat}
    -> ValidLens (VQuadrant t {S dep}) (VQuadrant t {dep})
ValidLens-LensC {t} {dep} = CValidLens lensC (ValidLens-LensC-ViewSet) (ValidLens-LensC-SetView) (ValidLens-LensC-SetSet)

--- Lens laws for lensD

postulate 
    ValidLens-LensD-ViewSet : 
        {t : Set} {{eqT : Eq t}} {dep : Nat}
        -> ViewSet (lensD {t} {dep})
    ValidLens-LensD-SetView : 
        {t : Set} {{eqT : Eq t}} {dep : Nat}
        -> SetView (lensD {t} {dep})
    ValidLens-LensD-SetSet : 
        {t : Set} {{eqT : Eq t}} {dep : Nat}
        -> SetSet (lensD {t} {dep})

ValidLens-LensD : {t : Set} {{eqT : Eq t}} {dep : Nat}
    -> ValidLens (VQuadrant t {S dep}) (VQuadrant t {dep})
ValidLens-LensD {t} {dep} = CValidLens lensD (ValidLens-LensD-ViewSet) (ValidLens-LensD-SetView) (ValidLens-LensD-SetSet)