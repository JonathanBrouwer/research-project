module Data.QuadTree.Implementation.Folding where

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
    foldEqMap : {a b : Set} -> {{ eqA : Eq a }} {{ eqB : Eq b }} {{ monB : Monoid b }} → (a → b) → t a → b
open FoldableEq public
{-# COMPILE AGDA2HS FoldableEq class #-}

data Region : Set where
    -- lower x, lower y, upper x, upper y
    RegionC : (lx : Nat) -> (ly : Nat) -> (ux : Nat) -> (uy : Nat)
            -> {{ .( IsTrue (lx <= ux) ) }}
            -> {{ .( IsTrue (ly <= uy) ) }}
            -> Region

_region<=_ : Region -> (Nat × Nat) -> Bool
RegionC lx1 ly1 ux1 uy1 region<= (w , h) 
    = (sub ux1 lx1) <= w && (sub uy1 ly1) <= h

_region>=_ : Region -> (Nat × Nat) -> Bool
RegionC lx1 ly1 ux1 uy1 region>= (w , h) 
    = (sub ux1 lx1) >= w && (sub uy1 ly1) >= h

data Tile (t : Set) : Set where
    TileC : t -> Region -> Tile t

postulate
    xx : Nat

tilesQd : {t : Set} {{eqT : Eq t}} {dep : Nat} -> VQuadrant t {dep} 
    -> (reg : Region) -> { .( IsTrue (reg region>= (pow 2 dep , pow 2 dep)) )}
    -> List (Tile t)
tilesQd {dep} (CVQuadrant (Leaf v)) reg = TileC v reg ∷ []
tilesQd {t} {dep = dep @ (S deps)} (CVQuadrant (Node a b c d) {p}) reg@(RegionC xl yl xh yh {{px}} {{py}}) =
    let
        mid = pow 2 deps
        sA : List (Tile t)
        sA = tilesQd (CVQuadrant a {aSub a b c d p}) 
            (RegionC xl yl (mid + xl) (mid + yl) 
            {{lteSumOne xl xl mid (lteSelf xl)}} 
            {{lteSumOne yl yl mid (lteSelf yl)}})
            {{!   !}}
        sB : List (Tile t)
        sB = tilesQd (CVQuadrant b {bSub a b c d p}) 
            (RegionC (mid + xl) yl (mid + (mid + xl)) (mid + yl) 
            {{lteSumOne (mid + xl) (mid + xl) mid (lteSelf (mid + xl))}} 
            {{lteSumOne yl yl mid (lteSelf yl)}})
            {{!   !}}
        sC : List (Tile t)
        sC = tilesQd (CVQuadrant c {cSub a b c d p})
            (RegionC xl (mid + yl) (mid + xl) (mid + (mid + yl)) 
            {{lteSumOne xl xl mid (lteSelf xl)}} 
            {{lteSumOne (mid + yl) (mid + yl) mid (lteSelf (mid + yl))}})
            {{!   !}}
        sD : List (Tile t)
        sD = tilesQd (CVQuadrant d {dSub a b c d p})
            (RegionC (mid + xl) (mid + yl) (mid + (mid + xl)) (mid + (mid + yl)) 
            {{lteSumOne (mid + xl) (mid + xl) mid (lteSelf (mid + xl))}} 
            {{lteSumOne (mid + yl) (mid + yl) mid (lteSelf (mid + yl))}})
            {{!   !}}
    in sA ++ sB ++ sC ++ sD

tilesQt : {t : Set} {{eqT : Eq t}} {dep : Nat} -> VQuadTree t {dep} -> List (Tile t)
tilesQt (CVQuadTree (Wrapper (w , h) qd) {p1} {p2}) = tilesQd (CVQuadrant qd {p1}) (RegionC 0 0 w h {{zeroLteAny w}} {{zeroLteAny h}})

replicate : {t : Set} -> Nat -> t -> List t
replicate Z v = []
replicate (S n) v = v ∷ replicate n v

expand : {t : Set} {{eqT : Eq t}} -> Tile t -> List t
expand (TileC v (RegionC lx ly ux uy {{px}} {{py}})) =
    replicate (dx * dy) v where
        dx = sub ux lx
        dy = sub uy ly

instance
  quadtreeFoldable : {dep : Nat} -> FoldableEq (λ y -> VQuadTree y {dep})
  quadtreeFoldable {dep} .foldEqMap f t = foldMap f $ concat $ map expand (tilesQt t)
{-# COMPILE AGDA2HS quadtreeFoldable #-}