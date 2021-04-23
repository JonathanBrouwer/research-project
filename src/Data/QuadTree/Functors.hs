module Data.QuadTree.Functors where

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

