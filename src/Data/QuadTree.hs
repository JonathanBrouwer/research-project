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
  atLocation, getLocation, setLocation, mapLocation
  ) where

import Data.QuadTree.InternalAgda