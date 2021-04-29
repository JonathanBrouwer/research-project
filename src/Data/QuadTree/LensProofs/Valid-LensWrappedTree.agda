module Data.QuadTree.LensProofs.Valid-LensWrappedTree where

open import Haskell.Prelude renaming (zero to Z; suc to S)
open import Data.QuadTree.Lens
open import Data.QuadTree.Logic
open import Data.QuadTree.InternalAgda
open import Agda.Primitive
open import Data.QuadTree.LensProofs.LensLaws
open import Data.QuadTree.LensProofs.LensPostulates
open import Data.QuadTree.LensProofs.LensComposition

---- Lens laws for lensWrappedTree

ValidLens-WrappedTree-ViewSet : 
    {t : Set} {{eqT : Eq t}} {dep : Nat}
    -> ViewSet (lensWrappedTree {t} {dep})
ValidLens-WrappedTree-ViewSet (CVQuadrant qdi) (CVQuadTree (Wrapper (w , h) qdo)) = refl

ValidLens-WrappedTree-SetView : 
    {t : Set} {{eqT : Eq t}} {dep : Nat}
    -> SetView (lensWrappedTree {t} {dep})
ValidLens-WrappedTree-SetView (CVQuadTree (Wrapper (w , h) qdo)) = refl

ValidLens-WrappedTree-SetSet : 
    {t : Set} {{eqT : Eq t}} {dep : Nat}
    -> SetSet (lensWrappedTree {t} {dep})
ValidLens-WrappedTree-SetSet (CVQuadrant qd1) (CVQuadrant qd2) (CVQuadTree (Wrapper (w , h) qdo)) = refl

ValidLens-WrappedTree :
    {t : Set} {{eqT : Eq t}} {dep : Nat}
    -> ValidLens (VQuadTree t {dep}) (VQuadrant t {dep})
ValidLens-WrappedTree = CValidLens lensWrappedTree (ValidLens-WrappedTree-ViewSet) (ValidLens-WrappedTree-SetView) (ValidLens-WrappedTree-SetSet)