{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module Provenance where

import Control.Exception
import Data.Semigroup
import Control.Monad.Trans
import Control.Monad.Morph

-- Provenance information for enumeration procedures
-- It is implemented as a wrapper to offer useful functions for seamless use without having to worry too much about the provenance and its handling.
data Provenance p t = Provenance t p

type (t :- p) = Provenance p t
infix 8 :-

instance (Show t, Show p) => Show (Provenance p t) where
	show (Provenance x p) = (show x) ++ " (" ++ (show p) ++ ")"

instance Eq t => Eq (Provenance p t) where
	(Provenance x1 _) == (Provenance x2 _) = x1 == x2

instance Functor (Provenance p) where
	fmap f (Provenance x p) = Provenance (f x) p

raw :: Provenance p t -> t
raw (Provenance x _) = x

(>:) :: t -> p -> Provenance p t
x >: p = Provenance x p
infixl 6 >:

-- Short-hand operator for inserting provenance through functors.
($>:) :: Functor f => f a -> p -> f (a :- p)
x $>: p = (>: p) <$> x
infixl 6 $>:

(>>:) :: Semigroup p => Provenance p t -> p -> Provenance p t
(Provenance x p1) >>: p2 = Provenance x (p1 <> p2)
infixl 6 >>:

(>:>) :: Semigroup p => p -> Provenance p t -> Provenance p t
p1 >:> (Provenance x p2) = Provenance x (p1 <> p2)
infixr 6 >:>

flatten_provenance :: Semigroup p => Provenance p (Provenance p t) -> Provenance p t
flatten_provenance (Provenance x p1) = p1 >:> x


instance Monoid p => Applicative (Provenance p) where
	pure x = x >: mempty
	(Provenance f p1) <*> (Provenance x p2) = (f x) >: (p1 <> p2)

instance Monoid p => Monad (Provenance p) where
	return = pure
	(Provenance x p1) >>= f = p1 >:> (f x)

instance Foldable (Provenance p) where
	foldr f z (Provenance x p1) = f x z

instance Traversable (Provenance p) where
	sequenceA (Provenance x p1) = (pure (>: p1)) <*> x


-- Transformer
newtype ProvenanceT p m t = ProvenanceT {fromProvenanceT :: m (Provenance p t)}

instance Monoid p => MonadTrans (ProvenanceT p) where
	lift x = ProvenanceT (x >>= (return . return))

instance Functor m => Functor (ProvenanceT p m) where
	fmap f (ProvenanceT x) = ProvenanceT (fmap (fmap f) x)

instance (Applicative m, Monoid p) => Applicative (ProvenanceT p m) where
	pure x = ProvenanceT (pure (pure x))
	(ProvenanceT fs) <*> (ProvenanceT xs) = ProvenanceT (((<*>) <$> fs) <*> xs)

instance (Monad m, Monoid p) => Monad (ProvenanceT p m) where
	return = pure
	(ProvenanceT a) >>= f = ProvenanceT (a >>= (\(Provenance aa p) -> ((fromProvenanceT . f) aa) >>= (\bp -> return (p >:> bp))))

instance Monoid p => MFunctor (ProvenanceT p) where
	hoist f (ProvenanceT x) = ProvenanceT (f x)







