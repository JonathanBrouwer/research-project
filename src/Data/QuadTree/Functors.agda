module Data.QuadTree.Functors where

open import Haskell.Prelude

data Const (a : Set) (b : Set) : Set where
  CConst : a -> Const a b

getConst : {a : Set} {b : Set} -> Const a b -> a
getConst (CConst a) = a

instance
  constFunctor : {a : Set} -> Functor (Const a)
  constFunctor .fmap f (CConst v) = CConst v

{-# COMPILE AGDA2HS Const #-}
{-# COMPILE AGDA2HS getConst #-}
{-# COMPILE AGDA2HS constFunctor #-}

data Identity (a : Set) : Set where
  CIdentity : a -> Identity a

runIdentity : {a : Set} -> Identity a -> a
runIdentity (CIdentity a) = a

instance
  identityFunctor : Functor Identity
  identityFunctor .fmap f (CIdentity v) = CIdentity (f v)

{-# COMPILE AGDA2HS Identity #-}
{-# COMPILE AGDA2HS runIdentity #-}
{-# COMPILE AGDA2HS identityFunctor #-}