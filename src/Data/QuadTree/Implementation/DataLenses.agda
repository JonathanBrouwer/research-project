module Data.QuadTree.Implementation.DataLenses where

open import Haskell.Prelude renaming (zero to Z; suc to S)
open import Data.Lens.Lens
open import Data.Logic
open import Data.QuadTree.Implementation.PropDepthRelation
open import Data.QuadTree.Implementation.Definition
open import Data.QuadTree.Implementation.ValidTypes
open import Data.QuadTree.Implementation.QuadrantLenses

{-# FOREIGN AGDA2HS
{-# LANGUAGE Safe #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Rank2Types #-}
import Data.Nat
import Data.Lens.Lens
import Data.Logic

import Data.QuadTree.Implementation.Definition
import Data.QuadTree.Implementation.ValidTypes
import Data.QuadTree.Implementation.QuadrantLenses
#-}

---- Functions for whether a coordinate is inside

isInsideQuadTree : {t : Set} -> (Nat × Nat) -> QuadTree t -> Bool
isInsideQuadTree (x , y) (Wrapper (w , h) _) = x < w && y < h

isInsidePow : (Nat × Nat) -> Nat -> Bool
isInsidePow (x , y) deps = x < pow 2 deps && y < pow 2 deps

insideQTtoInsidePow : {t : Set} {{eqT : Eq t}} -> (loc : Nat × Nat) -> {dep : Nat} -> (vqt : VQuadTree t {dep})
  -> IsTrue (isInsideQuadTree loc (qtFromSafe vqt))
  -> IsTrue (isInsidePow loc dep)
insideQTtoInsidePow (x , y) {dep} (CVQuadTree (Wrapper (w , h) qd) {p} {q}) it =
  let
    p1 : IsTrue (pow 2 dep >= (max w h))
    p1 = log2upPow dep (max w h) (eqToGte dep (log2up (max w h)) q)

    p2 : IsTrue ((max w h) <= pow 2 dep)
    p2 = gteInvert (pow 2 dep) (max w h) p1

    p3 : IsTrue (w <= pow 2 dep && h <= pow 2 dep)
    p3 = useEq (sym $ propMaxLte w h (pow 2 dep)) p2
  in andCombine 
    ( ltLteTransitive x w (pow 2 dep) (andFst {x < w} it) (andFst p3) )
    ( ltLteTransitive y h (pow 2 dep) (andSnd {x < w} it) (andSnd p3) )

---- Data access

-- Lens into the leaf quadrant corresponding to a location in a quadrant
go : {t : Set} {{eqT : Eq t}}
  -> (loc : Nat × Nat) -> (dep : Nat)
  -> {.(IsTrue (isInsidePow loc dep))}
  -> Lens (VQuadrant t {dep}) t
go _ Z = lensLeaf
go {t} (x , y) (S deps) =
  let
    mid = pow 2 deps
    gorec = go {t} (mod x mid {pow_not_zero_cv deps} , mod y mid {pow_not_zero_cv deps}) deps 
      {andCombine (modLt x mid {pow_not_zero_cv deps}) (modLt y mid {pow_not_zero_cv deps})}
  in
    if (y < mid) 
      then if x < mid 
        then (lensA ∘ gorec)
        else (lensB ∘ gorec)
      else if x < mid
        then (lensC ∘ gorec)
        else (lensD ∘ gorec)
{-# COMPILE AGDA2HS go #-}

-- Lenses into the root quadrant of a quadtree
lensWrappedTree : {t : Set} {{eqT : Eq t}}
  -> {dep : Nat}
  -> Lens (VQuadTree t {dep}) (VQuadrant t {dep})
lensWrappedTree fun (CVQuadTree (Wrapper (w , h) qd) {p} {q}) = 
  fmap 
    (λ where (CVQuadrant qd {p}) → CVQuadTree (Wrapper (w , h) qd) {p} {q})
    (fun (CVQuadrant qd {p}))
{-# COMPILE AGDA2HS lensWrappedTree #-}

-- Lens into the leaf quadrant corresponding to a location in a quadtree
atLocation : {t : Set} {{eqT : Eq t}}
  -> (loc : Nat × Nat) -> (dep : Nat)
  -> {.(IsTrue (isInsidePow loc dep))}
  -> Lens (VQuadTree t {dep}) t
atLocation index dep {p} = lensWrappedTree ∘ (go index dep {p})
{-# COMPILE AGDA2HS atLocation #-}