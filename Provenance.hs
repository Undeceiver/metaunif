{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module Provenance where

import Control.Exception
import Data.Semigroup
import EnumProc

-- Provenance information for enumeration procedures
-- It is implemented as a wrapper to offer useful functions for seamless use without having to worry too much about the provenance and its handling.
data Provenance p t = Provenance t p

type (t :- p) = Provenance p t
infix 8 :-

instance (Show t, Show p) => Show (Provenance p t) where
	show (Provenance x p) = (show x) ++ " (" ++ (show p) ++ ")"

instance Eq t => Eq (Provenance p t) where
	(Provenance x1 _) == (Provenance x2 _) = x1 == x2

instance {-# OVERLAPPING #-} Functor (Provenance p) where
	fmap f (Provenance x p) = Provenance (f x) p

raw :: Provenance p t -> t
raw (Provenance x _) = x

(>:) :: t -> p -> Provenance p t
x >: p = Provenance x p
infixl 6 >:

(>>:) :: Semigroup p => Provenance p t -> p -> Provenance p t
(Provenance x p1) >>: p2 = Provenance x (p1 <> p2)
infixl 6 >>:

(>:>) :: Semigroup p => p -> Provenance p t -> Provenance p t
p1 >:> (Provenance x p2) = Provenance x (p1 <> p2)
infixr 6 >:>

flatten_provenance :: Semigroup p => Provenance p (Provenance p t) -> Provenance p t
flatten_provenance (Provenance x p1) = p1 >:> x

type ProvEnumProc p t = EnumProc (Provenance p t)

fflatten_provenance :: (Semigroup p,Functor f) => Provenance p (f (Provenance p t)) -> f (Provenance p t)
fflatten_provenance (Provenance c p) = fmap ((>:>) p) c

diagonalize_with_prov :: Semigroup p => ProvEnumProc p (ProvEnumProc p t) -> ProvEnumProc p t
diagonalize_with_prov = diagonalize_enumproc . (fmap fflatten_provenance)

econcat_with_prov :: Semigroup p => ProvEnumProc p (ProvEnumProc p t) -> ProvEnumProc p t
econcat_with_prov = es_econcat . (fmap fflatten_provenance)


-- Apply a function and append to the provenance indicating something
apply_with_prov :: Semigroup p => (a -> b) -> (a -> p) -> Provenance p a -> Provenance p b
apply_with_prov f prov (Provenance ax px) = (f ax) >: px >>: (prov ax)

($:) :: Semigroup p => (a -> Provenance p b) -> Provenance p a -> Provenance p b
f $: x = flatten_provenance (fmap f x)
infixl 0 $:

-- The standard way to use the above is on functors
fmap_with_prov :: (Functor f, Semigroup p) => (a -> b) -> (a -> p) -> f (Provenance p a) -> f (Provenance p b)
fmap_with_prov f prov = fmap (apply_with_prov f prov)

-- Put everything together. Apply the function on all elements in the first enumeration, and introduce provenance information for this operation
diagonalize_apply_with_prov :: Semigroup p => (a -> ProvEnumProc p b) -> (a -> p) -> ProvEnumProc p a -> ProvEnumProc p b
diagonalize_apply_with_prov f prov en = econcat_with_prov (fmap_with_prov f prov en)

(->:) :: (a -> ProvEnumProc p b) -> (a -> p) -> ((a -> ProvEnumProc p b),(a -> p))
(->:) = (,)

(>>=:) :: Semigroup p => ProvEnumProc p a -> ((a -> ProvEnumProc p b),(a -> p)) -> ProvEnumProc p b
e1 >>=: (f,fp) = diagonalize_apply_with_prov f fp e1
infixl 7 >>=:
