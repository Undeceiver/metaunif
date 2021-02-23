{-# LANGUAGE GADTs #-}
{-# LANGUAGE DatatypeContexts #-}
module DatatypeContextsExample where

import Data.Map
import Data.Bifunctor

data Ord t => Foo t where
	Foo :: Ord t => Map t t -> Foo t

instance Functor Foo where
	fmap f (Foo m) = Foo (fromList (fmap (bimap f f) (toList m)))
