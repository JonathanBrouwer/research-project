{-# OPTIONS_HADDOCK show-extensions #-}

{-# LANGUAGE Safe #-}

{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.QuadTree (
  -- QuadTree + Constructor
  QuadTree (Wrapper), makeTree,
  -- Quadrant + Constructors
  Quadrant (Node, Leaf),
  -- Index access
  getLocation, setLocation, mapLocation
  ) where

import Data.QuadTree.Implementation.Definition
import Data.QuadTree.Implementation.ValidTypes
import Data.QuadTree.Implementation.QuadrantLenses
import Data.QuadTree.Implementation.DataLenses
import Data.QuadTree.Implementation.SafeFunctions
import Data.QuadTree.Implementation.PublicFunctions