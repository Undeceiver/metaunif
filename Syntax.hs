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
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
module Syntax where

import Control.Unification
import Control.Unification.IntVar
import HaskellPlus
import Data.Functor.Fixedpoint
import Data.Bifunctor
import Data.Either
import Data.Functor.Const

class Variabilizable t where
	get_var :: t -> IntVar

read_arity :: String -> (Int,String)
read_arity ('[':xs) = (let r = (head (reads xs))
			in ((fst r),(tail (snd r))))

class HasArity t where
	arity :: t -> Int

-- A type providing base cases for a functor structure
class FunctorBase b where
	isBase :: (b f t) -> Bool
	fromBase :: (b f t) -> (b g t)
	fromRec :: Functor f => (b f t) -> f (b f t)

fromRecSafe :: (Functor f, FunctorBase b) => f (b f t) -> (b f t) -> f (b f t)
fromRecSafe def r = if (isBase r) then def else (fromRec r)

-- Wrapper that takes a syntactic element and a type of meta-variables and creates syntactic elements which may also contain meta-variables in places.
type Metawrapper m v = Either v m
type Metawrap m (b :: (* -> *) -> * -> *) (f :: * -> *) v = b f (Metawrapper m v)

show_metawrap :: (Show (b f Preshow), Functor (b f), Show v, Show m) => Metawrap m b f v -> String
show_metawrap b = show (fmap (\x -> case x of {Left y -> preshow y; Right y -> preshow y}) b)

instance (Show (b f Preshow), Functor (b f), Show v, Show m) => Show (Metawrap m b f v) where
	show b = show_metawrap b

mw :: Functor (b f) => b f v -> Metawrap m b f v
mw = fmap Left

umw :: Functor (b f) => v -> Metawrap m b f v -> b f v
umw x = fmap (fromLeft x)

mv :: Functor (b f) => b f m -> Metawrap m b f v
mv = fmap Right

umv :: Functor (b f) => m -> Metawrap m b f v -> b f m
umv x = fmap (fromRight x)

data Predicabilize (a :: * -> *) f = Atom (a f) | Term f deriving (Eq, Ord, Functor, Foldable, Traversable)

instance (Show (a f), Show f) => Show (Predicabilize a f) where
	show (Atom x) = show x
	show (Term x) = show x

instance Unifiable a => Unifiable (Predicabilize a) where
	zipMatch (Atom a1) (Atom a2) = (zipMatch a1 a2) >>= (Just . Atom)
	zipMatch (Term t1) (Term t2) = Just (Term (Right (t1,t2)))


-- Metawrap a predicabilized structure, allowing meta-variables at the atom level too.
data Metapredicabilize (a :: * -> *) av tv = MAtomV av | MAtom (a tv) | MTerm tv deriving (Eq, Ord)

instance Functor a => Bifunctor (Metapredicabilize a) where
	bimap f g (MAtomV av) = MAtomV (f av)
	bimap f g (MAtom x) = MAtom (fmap g x)
	bimap f g (MTerm x) = MTerm (g x)

instance (Show av, Show (a tv), Show tv) => Show (Metapredicabilize a av tv) where
	show (MAtomV av) = show av
	show (MAtom x) = show x
	show (MTerm x) = show x

-- We could implement a Unifiable instance of Metapredicabilize (only for term variables), but it's not useful as Unifier (first-order unification) is useless for entities containing meta-variables.


-- Atom meta-variables are easy because they have no recursive structure, so we added them in Metapredicabilize. To add term-metavariables, we need to use Metawrap. We add an alias for doing both things.
type PredMetawrap mt ma (b :: (* -> *) -> * -> *) (a :: * -> *) (t :: * -> *) v = Metapredicabilize a ma (Metawrap mt b t v)

apmv :: ma -> PredMetawrap mt ma b a t v
apmv mx = MAtomV mx

