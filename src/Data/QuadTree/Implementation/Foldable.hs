{-# LANGUAGE Safe #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Rank2Types #-}

module Data.QuadTree.Implementation.Foldable where




import Data.Nat
import Data.Lens.Lens
import Data.Logic
import Data.QuadTree.Implementation.Definition
import Data.QuadTree.Implementation.ValidTypes
import Data.QuadTree.Implementation.QuadrantLenses

class FoldableEq t where
    foldMapₑ :: Eq a => Eq b => Monoid b => (a -> b) -> t a -> b

data Region = RegionC (Nat, Nat) (Nat, Nat)

data Tile t = TileC t Region

tilesQd :: Eq t => Nat -> VQuadrant t -> Region -> [Tile t]
tilesQd dep (CVQuadrant (Leaf v)) reg = [TileC v reg]
tilesQd (S deps) (CVQuadrant (Node a b c d))
  (RegionC (xl, yl) (xh, yh))
  = tilesQd deps (CVQuadrant a)
      (RegionC (xl, yl) (pow 2 deps + xl, pow 2 deps + yl))
      ++
      tilesQd deps (CVQuadrant b)
        (RegionC (pow 2 deps + xl, yl)
           (diff (pow 2 deps) xh + (pow 2 deps + xl), pow 2 deps + yl))
        ++
        tilesQd deps (CVQuadrant c)
          (RegionC (xl, pow 2 deps + yl)
             (pow 2 deps + xl, diff (pow 2 deps) yh + (pow 2 deps + yl)))
          ++
          tilesQd deps (CVQuadrant d)
            (RegionC (pow 2 deps + xl, pow 2 deps + yl)
               (diff (pow 2 deps) xh + (pow 2 deps + xl),
                diff (pow 2 deps) yh + (pow 2 deps + yl)))
tilesQd Z (CVQuadrant (Node qd qd₁ qd₂ qd₃)) reg
  = error "tilesQd: impossible"

tilesQt :: Eq t => Nat -> VQuadTree t -> [Tile t]
tilesQt dep (CVQuadTree (Wrapper wh qd))
  = tilesQd dep (CVQuadrant qd) (RegionC (0, 0) wh)

replicateₙ :: Nat -> t -> [t]
replicateₙ Z v = []
replicateₙ (S n) v = v : replicateₙ n v

expand :: Eq t => Tile t -> [t]
expand (TileC v (RegionC (lx, ly) (ux, uy)))
  = replicateₙ (dx * dy) v
  where
    dx :: Nat
    dx = diff ux lx
    dy :: Nat
    dy = diff uy ly

