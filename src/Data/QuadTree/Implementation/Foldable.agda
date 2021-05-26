module Data.QuadTree.Implementation.Foldable where

open import Haskell.Prelude renaming (zero to Z; suc to S)
open import Data.Logic
open import Data.QuadTree.Implementation.Definition
open import Data.QuadTree.Implementation.ValidTypes
open import Data.QuadTree.Implementation.QuadrantLenses
open import Data.QuadTree.Implementation.SafeFunctions
open import Data.QuadTree.Implementation.PropDepthRelation

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

record FoldableEq (t : (y : Set) -> {{ eqT : Eq y }} -> Set) : Set₁ where
  field
    foldMapₑ : {a b : Set} -> {{ eqA : Eq a }} {{ eqB : Eq b }} 
        -> {{ monB : Monoid b }} → (a → b) → t a → b

  lengthₑ : {{eqA : Eq a}} -> t a → Nat
  lengthₑ = foldMapₑ ⦃ monB = MonoidSum ⦄ (const 1)
open FoldableEq public
{-# COMPILE AGDA2HS FoldableEq class #-}

data Region : Set where
    -- point 1: x, point 1: y, point 2: x, point 2: y
    RegionC : (p1 : Nat × Nat) (p2 : Nat × Nat) -> Region
{-# COMPILE AGDA2HS Region #-}

data Tile (t : Set) : Set where
    TileC : t -> Region -> Tile t
{-# COMPILE AGDA2HS Tile #-}

tilesQd : {t : Set} {{eqT : Eq t}} (dep : Nat) -> VQuadrant t {dep} 
    -> (reg : Region)
    -> List (Tile t)
tilesQd dep (CVQuadrant (Leaf v)) reg = TileC v reg ∷ []
tilesQd {t} (dep @ (S deps)) (CVQuadrant (Node a b c d) {p}) reg@(RegionC (x1 , y1) (x2 , y2)) =
    let
        mid = pow 2 deps
        sA : List (Tile t)
        sA = tilesQd deps (CVQuadrant a {aSub a b c d p}) (RegionC 
            (x1 , y1) 
            (min x2 (mid + x1) , min y2 (mid + y1)))
        sB : List (Tile t)
        sB = tilesQd deps (CVQuadrant b {bSub a b c d p}) (RegionC 
            (min x2 (mid + x1) , y1) 
            (x2 , min y2 (mid + y1)) )
        sC : List (Tile t)
        sC = tilesQd deps (CVQuadrant c {cSub a b c d p}) (RegionC 
            (x1 , min y2 (mid + y1)) 
            (min x2 (mid + x1) , y2) )
        sD : List (Tile t)
        sD = tilesQd deps (CVQuadrant d {dSub a b c d p}) (RegionC 
            (min x2 (mid + x1) , min y2 (mid + y1)) 
            (x2 , y2) )
    in sA ++ sB ++ sC ++ sD
{-# COMPILE AGDA2HS tilesQd #-}

tilesQt : {t : Set} {{eqT : Eq t}} (dep : Nat) -> VQuadTree t {dep} -> List (Tile t)
tilesQt dep (CVQuadTree (Wrapper wh qd) {p1} {p2}) = tilesQd dep (CVQuadrant qd {p1}) (RegionC (0 , 0) wh)
{-# COMPILE AGDA2HS tilesQt #-}

replicateₙ : {t : Set} -> Nat -> t -> List t
replicateₙ Z v = []
replicateₙ (S n) v = v ∷ replicateₙ n v
{-# COMPILE AGDA2HS replicateₙ #-}

expand : {t : Set} {{eqT : Eq t}} -> Tile t -> List t
expand (TileC v (RegionC (lx , ly) (ux , uy))) =
    replicateₙ (dx * dy) v where
        dx = diff ux lx
        dy = diff uy ly
{-# COMPILE AGDA2HS expand #-}

quadtreeFoldable : (dep : Nat) -> FoldableEq (λ y -> VQuadTree y {dep})
quadtreeFoldable dep .foldMapₑ f t = foldMap f $ concat $ map expand (tilesQt dep t)


qt : VQuadTree Bool {3}
qt = CVQuadTree (Wrapper (2 , 8) (Node (Leaf false) (Leaf false) (Leaf true) (Leaf true))) {IsTrue.itsTrue} {IsTrue.itsTrue}

