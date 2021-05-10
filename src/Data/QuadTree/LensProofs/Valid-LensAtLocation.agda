-- {-# OPTIONS --show-implicit --show-irrelevant #-}
module Data.QuadTree.LensProofs.Valid-LensAtLocation where

open import Haskell.Prelude renaming (zero to Z; suc to S)
open import Data.Lens.Lens
open import Data.Logic
open import Data.QuadTree.InternalAgda
open import Agda.Primitive
open import Data.Lens.Proofs.LensLaws
open import Data.Lens.Proofs.LensPostulates
open import Data.Lens.Proofs.LensComposition
open import Data.QuadTree.LensProofs.Valid-LensLeaf
open import Data.QuadTree.LensProofs.Valid-LensWrappedTree
open import Data.QuadTree.LensProofs.Valid-LensA
open import Data.QuadTree.LensProofs.Valid-LensBCD
open import Data.QuadTree.LensProofs.Valid-LensGo


---- Lens laws for go

ValidLens-AtLocation-ViewSet : 
    {t : Set} {{eqT : Eq t}}
    -> (loc : Nat × Nat) -> (dep : Nat)
    -> {ins : IsTrue (isInsidePow loc dep)}
    -> ViewSet (atLocation {t} loc dep {ins})
ValidLens-AtLocation-ViewSet (x , y) dep {ins} v s = trans refl (prop-Composition-ViewSet (ValidLens-WrappedTree) (ValidLens-go (x , y) dep {ins}) v s)

ValidLens-AtLocation-SetView : 
    {t : Set} {{eqT : Eq t}}
    -> (loc : Nat × Nat) -> (dep : Nat)
    -> {ins : IsTrue (isInsidePow loc dep)}
    -> SetView (atLocation {t} loc dep {ins})
ValidLens-AtLocation-SetView (x , y) dep {ins} s = trans refl (prop-Composition-SetView (ValidLens-WrappedTree) (ValidLens-go (x , y) dep {ins}) s)

ValidLens-AtLocation-SetSet : 
    {t : Set} {{eqT : Eq t}}
    -> (loc : Nat × Nat) -> (dep : Nat)
    -> {ins : IsTrue (isInsidePow loc dep)}
    -> SetSet (atLocation {t} loc dep {ins})
ValidLens-AtLocation-SetSet (x , y) dep {ins} v1 v2 s = trans refl (prop-Composition-SetSet (ValidLens-WrappedTree) (ValidLens-go (x , y) dep {ins}) v1 v2 s)

ValidLens-AtLocation : {t : Set} {{eqT : Eq t}}
    -> (loc : Nat × Nat) -> (dep : Nat)
    -> {ins : IsTrue (isInsidePow loc dep)}
    -> ValidLens (VQuadTree t {dep}) t
ValidLens-AtLocation {t} {{eqT}} (x , y) dep {ins} = CValidLens (atLocation (x , y) dep {ins}) (ValidLens-AtLocation-ViewSet (x , y) dep {ins}) (ValidLens-AtLocation-SetView (x , y) dep {ins}) (ValidLens-AtLocation-SetSet (x , y) dep {ins})

test : {.(a : Bool)} -> Bool
test = true