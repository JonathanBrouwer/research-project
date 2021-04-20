module Project where

-- we import the Haskell prelude provided by agda2hs
-- It mimics the real Haskell prelude, so agda2hs doesn't compile
-- the agda2hs prelude to Haskell code but uses the Haskell prelude directly
open import Haskell.Prelude
  hiding (List; concat; length; map; concatMap)
open import Agda.Builtin.Equality


-- {-# FOREIGN AGDA2HS #-} blocks allow you to write Haskell code directly
-- Here, we hide concat & length from the Prelude
{-# FOREIGN AGDA2HS
import Prelude hiding (concat, length, map, concatMap)
#-}


data List (a : Set) : Set where
  Nil  : List a
  Cons : a → List a → List a

-- You can specify which definitions are compiled to Haskell
-- with a {-# COMPILE AGDA2HS #-} directive
{-# COMPILE AGDA2HS List deriving (Show, Eq) #-}
-- ^ Here we specify which Haskell instances should be derived