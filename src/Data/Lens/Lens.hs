{-# LANGUAGE Rank2Types #-}

module Data.Lens.Lens where

data Const a b = CConst a

getConst :: Const a b -> a
getConst (CConst a) = a

instance Functor (Const a) where
    fmap f (CConst v) = CConst v

data Identity a = CIdentity a

runIdentity :: Identity a -> a
runIdentity (CIdentity a) = a

instance Functor Identity where
    fmap f (CIdentity v) = CIdentity (f v)

type CLens s a = forall f. Functor f => (a -> f a) -> s -> f s

view :: CLens a b -> a -> b
view lens v = getConst $ lens CConst v

set :: CLens a b -> b -> a -> a
set lens to v = runIdentity $ lens (\ _ -> CIdentity to) v

over :: CLens a b -> (b -> b) -> a -> a
over lens f v = runIdentity $ lens (CIdentity . f) v

