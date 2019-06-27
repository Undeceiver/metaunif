{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
module HaskellPlus where

import Data.Bifunctor
import Data.Maybe
import Data.Functor.Fixedpoint
import Control.Unification
import Control.Monad.Except

-- Here I put functions/types that I feel should be part of Haskell but aren't. It is likely that at least half of them ACTUALLY are part of Haskell, but I wasn't smart enough to find them.

type Preshow = () -> String

preshow :: Show t => t -> Preshow
preshow x = unshow (show x)

unshow :: String -> Preshow
unshow str = (\_ -> str)

instance Show Preshow where
	show f = f ()

newtype FlippedFunctor (t :: k) (f :: k -> *) = FlippedFunctor (f t)
fromFlippedFunctor :: FlippedFunctor t f -> f t
fromFlippedFunctor (FlippedFunctor x) = x

newtype FlippedBifunctor (b :: k1 -> k2 -> *) (t :: k2) (f :: k1) = FlippedBifunctor (b f t)
fromFlippedBifunctor :: FlippedBifunctor b t f -> b f t
fromFlippedBifunctor (FlippedBifunctor x) = x

instance Bifunctor b => Bifunctor (FlippedBifunctor b) where
	bimap f g (FlippedBifunctor x) = FlippedBifunctor (bimap g f x)

--instance Bifunctor f => Functor (f t) where
--	fmap = bimap id

show_as_args :: (t -> String) -> [t] -> String
show_as_args _ [] = ""
show_as_args sh [x] = sh x
show_as_args sh (x:xs) = sh x ++ ", " ++ (show_as_args sh xs)

class Fixpoint (fx :: (* -> *) -> *) where
	fixp :: forall (t :: * -> *). Functor t => t (fx t) -> fx t

instance Fixpoint Fix where
	fixp = Fix

instance Fixpoint (FlippedBifunctor UTerm v) where
	fixp = FlippedBifunctor . UTerm . (fmap fromFlippedBifunctor)

-- Take some initial information (e.g. a head) and an already built functor (such as a list) that is used on the constructor of another functor, and map it to its fixed point.
build_functor_fix :: (Fixpoint fx, Functor t) => (forall f. h -> l f -> t f) -> h -> l (fx t) -> fx t
build_functor_fix b h s = fixp (b h s)

-- Just to avoid flipping and unflipping excessively when using the above function with UTerms.
build_functor_fix_uterm :: (Functor t, Functor l) => (forall f. h -> l f -> t f) -> h -> l (UTerm t v) -> UTerm t v
build_functor_fix_uterm b h s = fromFlippedBifunctor (build_functor_fix b h (fmap FlippedBifunctor s))

instance (Eq v, Eq (t (UTerm t v))) => Eq (UTerm t v) where
	(UVar x) == (UVar y) = x == y
	(UTerm x) == (UTerm y) = x == y
	_ == _ = False

floatExceptT :: (Show e, Monad m) => (ExceptT e m) a -> m a
floatExceptT exc = (runExceptT exc) >>= (\x -> case x of {Left e -> error (show e); Right y -> return y})

clear_value :: Monad m => m a -> m ()
clear_value = (>> (return ()))
