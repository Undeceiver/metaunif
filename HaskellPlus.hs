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
module HaskellPlus where

import Data.Bifunctor
import Data.Maybe

-- Here I put functions/types that I feel should be part of Haskell but aren't. It is likely that at least half of them ACTUALLY are part of Haskell, but I wasn't smart enough to find them.

type Preshow = () -> String

preshow :: Show t => t -> Preshow
preshow x = unshow (show x)

unshow :: String -> Preshow
unshow str = (\_ -> str)

instance Show Preshow where
	show f = f ()

newtype FlippedFunctor t f = FlippedFunctor (f t)
fromFlippedFunctor :: FlippedFunctor t f -> f t
fromFlippedFunctor (FlippedFunctor x) = x

newtype FlippedBifunctor b t f = FlippedBifunctor (b f t)
fromFlippedBifunctor :: FlippedBifunctor b t f -> b f t
fromFlippedBifunctor (FlippedBifunctor x) = x

instance Bifunctor b => Bifunctor (FlippedBifunctor b) where
	bimap f g (FlippedBifunctor x) = FlippedBifunctor (bimap g f x)

instance Bifunctor f => Functor (f t) where
	fmap = bimap id
