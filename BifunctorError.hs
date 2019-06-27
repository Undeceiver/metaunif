{-# LANGUAGE FlexibleInstances #-}
module BifunctorError where

import Data.Bifunctor

instance Bifunctor f => Functor (f t) where
	fmap = bimap id

data Provenance p t = Provenance p t

--instance Functor (Provenance p) where
--	fmap f (Provenance p x) = Provenance p (f x)
