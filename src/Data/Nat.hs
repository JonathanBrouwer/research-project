{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE Safe               #-}

-- | 'Nat' numbers.
--
-- This module is designed to be imported qualified.
--
module Data.Nat (
    -- * Natural, Nat numbers
    Nat(..),
    toNatural,
    fromNatural,
    cata,
    -- * Showing
    explicitShow,
    explicitShowsPrec,
    ) where

import Data.Data       (Data)
import Data.Typeable   (Typeable)
import GHC.Exception   (ArithException (..), throw)
import Numeric.Natural (Natural)

import qualified Test.QuickCheck     as QC

-- $setup

-------------------------------------------------------------------------------
-- Nat
-------------------------------------------------------------------------------

-- | Nat natural numbers.
--
-- Better than GHC's built-in 'GHC.TypeLits.Nat' for some use cases.
--
data Nat = Z | S Nat deriving (Eq, Typeable, Data)

-- | 'Nat' is printed as 'Natural'.
--
-- To see explicit structure, use 'explicitShow' or 'explicitShowsPrec'
--
instance Show Nat where
    showsPrec d = showsPrec d . toNatural

instance Ord Nat where
    compare Z     Z     = EQ
    compare Z     (S _) = LT
    compare (S _) Z     = GT
    compare (S n) (S m) = compare n m

    Z   < Z   = False
    Z   < S _ = True
    S _ < Z   = False
    S n < S m = n < m

    Z   <= Z   = True
    Z   <= S _ = True
    S _ <= Z   = False
    S n <= S m = n <= m

    min Z     Z     = Z
    min Z     (S _) = Z
    min (S _) Z     = Z
    min (S n) (S m) = S (min n m)

    max Z       Z       = Z
    max Z       m@(S _) = m
    max n@(S _) Z       = n
    max (S n)   (S m)   = S (max n m)

instance Num Nat where
    fromInteger = fromNatural . fromInteger

    Z   + m = m
    S n + m = S (n + m)

    n - Z = n
    Z - _ = error "Negation negative"
    (S n) - (S m) = n - m

    Z   * _ = Z
    S n * m = (n * m) + m

    abs = id

    signum Z     = Z
    signum (S _) = S Z

    negate _ = error "negate @Nat"

instance Real Nat where
    toRational = toRational . toInteger

divhelper :: Nat -> Nat -> Nat -> Nat -> Nat
divhelper k m  Z    j      = k
divhelper k m (S n)  Z   = divhelper (S k) m n m
divhelper k m (S n) (S j) = divhelper k       m n j

modhelper :: Nat -> Nat -> Nat -> Nat -> Nat
modhelper k m  Z    j      = k
modhelper k m (S n)  Z   = modhelper 0       m n m
modhelper k m (S n) (S j) = modhelper (S k) m n j

instance Integral Nat where
    toInteger = cata 0 succ

    quotRem _ Z = throw DivideByZero
    quotRem m (S n) = (divhelper 0 n m n, modhelper 0 n m n)

    divMod _ Z = throw DivideByZero
    divMod m (S n) = (divhelper 0 n m n, modhelper 0 n m n)

instance Enum Nat where
    toEnum n
        | n < 0     = throw Underflow
        | otherwise = iterate S Z !! n

    fromEnum = cata 0 succ

    succ       = S
    pred Z     = throw Underflow
    pred (S n) = n

-------------------------------------------------------------------------------
-- QuickCheck
-------------------------------------------------------------------------------

instance QC.Arbitrary Nat where
    arbitrary = fmap fromNatural QC.arbitrarySizedNatural

    shrink Z     = []
    shrink (S n) = n : QC.shrink n

instance QC.CoArbitrary Nat where
    coarbitrary Z     = QC.variant (0 :: Int)
    coarbitrary (S n) = QC.variant (1 :: Int) . QC.coarbitrary n

instance QC.Function Nat where
    function = QC.functionIntegral

-------------------------------------------------------------------------------
-- Showing
-------------------------------------------------------------------------------

-- | 'show' displaying a structure of 'Nat'.
--
-- >>> explicitShow 0
-- "Z"
--
-- >>> explicitShow 2
-- "S (S Z)"
--
explicitShow :: Nat -> String
explicitShow n = explicitShowsPrec 0 n ""

-- | 'showsPrec' displaying a structure of 'Nat'.
explicitShowsPrec :: Int -> Nat -> ShowS
explicitShowsPrec _ Z     = showString "Z"
explicitShowsPrec d (S n) = showParen (d > 10)
    $ showString "S "
    . explicitShowsPrec 11 n

-------------------------------------------------------------------------------
-- Conversions
-------------------------------------------------------------------------------

-- | Fold 'Nat'.
--
-- >>> cata [] ('x' :) 2
-- "xx"
--
cata :: a -> (a -> a) -> Nat -> a
cata z f = go where
    go Z     = z
    go (S n) = f (go n)

-- | Convert 'Nat' to 'Natural'
--
-- >>> toNatural 0
-- 0
--
-- >>> toNatural 2
-- 2
--
-- >>> toNatural $ S $ S $ Z
-- 2
--
toNatural :: Nat -> Natural
toNatural Z = 0
toNatural (S n) = succ (toNatural n)

-- | Convert 'Natural' to 'Nat'
--
-- >>> fromNatural 4
-- 4
--
-- >>> explicitShow (fromNatural 4)
-- "S (S (S (S Z)))"
--
fromNatural :: Natural -> Nat
fromNatural 0 = Z
fromNatural n = S (fromNatural (pred n))