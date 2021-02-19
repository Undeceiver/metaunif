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
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
-- I have looked high and low and could not find any standard library that would allow me to do anything like this. It is very related to lenses, with the big difference that lenses only look at one thing at a time, never more.
-- Zippers also come close, but there is not a standard zipper library, and related to this, zippers are more specific and concrete in that they allow you to traverse an individual structure step by step.
-- In some sense, Zippers on a structure would allow you to do analogy; but in many structures you can do analogy without needing to define all the technicalities needed for zippers.
-- This is where Analogous stays: it provides the technicalities to be able to compare structures of the same type and look at certain parts inside of them and do something with them.
-- A perfect simple example application is extending list zipping to arbitrary structures.
-- Another simple example is alpha equivalence in term structures.
--
-- An important thing to explain is why we do not define this on pairs, and instead do it directly on lists (which should be seen as sets for all intents and purposes, but Haskell does not have a convenient set type).
-- There are two important reasons, having to do with generality, for this. One has to do with the "inner type" (a/b), and the other has to do with the "outer type" (s/t)
-- With respect to the "inner type", in many applications an analogy matches more than one element from each side. Analogy is more abstract than a general structural literal equivalence, and so it could match multiple elements from either side and transitively combine them or something of the sort. While we could imagine ways to "fold" pairs into sets in different circumstances, the main issue is that the combining function that we wish to hand to the analogy may not even work properly for pairs, and defining it on pairs would be limiting. Thus, we use lists/sets for the inner type.
--
-- With respect to the "outer type", apart from keeping the structure of the inner type, a more important reason is that while we could think that a pairwise combination of large structures could be <folded> into a list/set-wise operation of large structures, this would involve assuming foldability (semigroup/monoid structure) of both the functor and the result type of the analogy. On the other hand, leaving the result as a list/set gives the control over all of this to the user of the module.
module Analogous where

import HaskellPlus
import Data.Functor.Identity
import Control.Monad.Except
import GHC.Base

-- Unlike Traversal, it is absurd to guarantee that we can perform analogy on any set of instances of a type.
-- Thus, we need to consider errors as part of the whole type system.

data AnalogyError = NonAnalogous | NoStructure deriving Show

instance Semigroup AnalogyError where
	NonAnalogous <> NonAnalogous = NonAnalogous
	NonAnalogous <> NoStructure = NoStructure
	NoStructure <> NoStructure = NoStructure
	NoStructure <> NonAnalogous = NoStructure

-- Please, be an adult.
type AnalError = SimpleMonadError AnalogyError

nonanalogous :: AnalError a
nonanalogous = throwError NonAnalogous

nostructure :: AnalError a
nostructure = throwError NoStructure


type Analogy (f :: k -> *) s (t :: k) a (b :: k) = ([a] -> f b) -> [s] -> AnalError (f t)
type Analogy' f s a = Analogy f s s a a

type FAnalogy s t a b = forall f. Functor f => ([a] -> f b) -> [s] -> AnalError (f t)
type FAnalogy' s a = FAnalogy s s a a

type AAnalogy s t a b = forall f. Applicative f => ([a] -> f b) -> [s] -> AnalError (f t)
type AAnalogy' s a = AAnalogy s s a a

type MAnalogy s t a b = forall f. Monad f => ([a] -> f b) -> [s] -> AnalError (f t)
type MAnalogy' s a = MAnalogy s s a a

class Foldable t => Analogous t where
	analogy :: AAnalogy (t a) (t b) a b

instance Analogous [] where
	analogy f ls | all Prelude.null ls = return (pure [])
	-- If not all are empty, but one is empty, then this is a non-analogy.
	analogy f ls | any Prelude.null ls = nonanalogous
	-- Otherwise we may assume they all have a head.
	analogy f ls = analogy f (tail <$> ls) >>= (\tail -> return $ liftA2 (:) (f (head <$> ls)) tail)	


-- Please, be an adult.
analzip_spec :: Analogy Identity s t a [a] -> [s] -> t
analzip_spec an ss = runIdentity $ fromSME $ an Identity ss

analzip :: Analogous t => [t a] -> t [a]
analzip = analzip_spec analogy
