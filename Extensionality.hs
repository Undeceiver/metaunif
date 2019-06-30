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
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE QuantifiedConstraints #-}
module Extensionality where

import HaskellPlus

data Extensional t = Ext (forall a. ((t -> a) -> a))

extensional :: t -> Extensional t
extensional x = Ext (\f -> f x)

coextensional :: (t -> a) -> Extensional t -> a
coextensional f (Ext x) = x f

($<>) :: (t -> a) -> Extensional t -> a
($<>) = coextensional

infixl 7 $<>

-- If we have an extensional value for a function type, we can consider evaluation the other way around.
(<>$) :: Extensional (a -> b) -> a -> b
f <>$ x = (\g -> g x) $<> f

infixl 7 <>$

-- And both at the same time
(>$<) :: Extensional (a -> b) -> Extensional a -> b
f >$< x = (f <>$) $<> x


-- Extensional composition
(>.<) :: Extensional (b -> c) -> Extensional (a -> b) -> Extensional (a -> c)
f >.< g = extensional (\x -> f <>$ (g <>$ x))

infixl 9 >.<

instance Functor Extensional where
	fmap f x = extensional (f $<> x)



-- Literally every kind * instance that could be made of type t can be made of type Extensional t. We add them as we need them.
instance Show t => Show (Extensional t) where
	show x = show $<> x





-- Here is where things get more interesting: Relative extensionality. This means, we need a value of type v to really have a value of type t.
-- This is basically a function, but where the arguments are treated seemlessly, essentially like a monad, accumulating them but without needing to carry them around.
data RExtensional v t = RExt (v -> Extensional t)

type (t |: v) = RExtensional v t

-- Make a value that is relatively extensional to itself. Easy peasy, ain't it?
type RIdExtensional t = RExtensional t t
idrext :: RIdExtensional t
idrext = RExt (extensional . id)

type RBaseExtensional t = RExtensional (t :* ()) t
baserext :: RBaseExtensional t
baserext = RExt (extensional . id . thead)


eval_rextensional :: v -> RExtensional v t -> Extensional t
eval_rextensional v (RExt x) = x v

(|:) :: RExtensional v t -> v -> Extensional t
x |: v = eval_rextensional v x

infix 7 |:

(|<>:) :: RExtensional v t -> Extensional v -> Extensional t
x |<>: v = (x |:) $<> v

infix 7 |<>:

rextensional :: (v -> t) -> RExtensional v t
rextensional f = RExt (extensional . f)

rextensionalf :: (v -> Extensional t) -> RExtensional v t
rextensionalf f = RExt f

rcoextensional :: (t -> a) -> RExtensional v t -> RExtensional v a
rcoextensional f x = RExt (\v -> extensional (f $<> (x |: v)))

($|<>) :: (t -> a) -> RExtensional v t -> RExtensional v a
($|<>) = rcoextensional

infixl 7 $|<>

(|<>$) :: RExtensional v (a -> b) -> a -> RExtensional v b
f |<>$ x = (\g -> g x) $|<> f

infixl 7 |<>$

flatten_rext :: RExtensional r (RExtensional v0 a) -> RExtensional (v0 :* r) a
flatten_rext f = rextensionalf (\(v0,r) -> ((|: v0) $<> (f |: r)))

(|>$<) :: RExtensional v0 (a -> b) -> RExtensional r a -> RExtensional (v0 :* r) b
f |>$< x = (flatten_rext . ((f |<>$) $|<>)) x
infixl 7 |>$<

-- Another case of second-order type inference. I'd like to do this:
-- unrext :: (forall v. RExtensional v (a v)) -> Extensional (a ())
-- unrext x = x |: ()
-- Which I can, but then it only works for precise a's and v's, and in my particular use case it doesn't work for prext1 onwards.
unrext1 :: RExtensional (() :* ()) (v0 :* ()) -> Extensional (v0 :* ())
unrext1 x = x |: (() *: ())

unrext2 :: RExtensional (() :* () :* ()) (v0 :* v1 :* ()) -> Extensional (v0 :* v1 :* ())
unrext2 x = x |: (() *: () *: ())

unrext3 :: RExtensional (() :* () :* () :* ()) (v0 :* v1 :* v2 :* ()) -> Extensional (v0 :* v1 :* v2 :* ())
unrext3 x = x |: (() *: () *: () *: ())

unrext4 :: RExtensional (() :* () :* () :* () :* ()) (v0 :* v1 :* v2 :* v3 :* ()) -> Extensional (v0 :* v1 :* v2 :* v3 :* ())
unrext4 x = x |: (() *: () *: () *: () *: ())

unrext5 :: RExtensional (() :* () :* () :* () :* () :* ()) (v0 :* v1 :* v2 :* v3 :* v4 :* ()) -> Extensional (v0 :* v1 :* v2 :* v3 :* v4 :* ())
unrext5 x = x |: (() *: () *: () *: () *: () *: ())

unrext6 :: RExtensional (() :* () :* () :* () :* () :* () :* ()) (v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* ()) -> Extensional (v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* ())
unrext6 x = x |: (() *: () *: () *: () *: () *: () *: ())

unrext7 :: RExtensional (() :* () :* () :* () :* () :* () :* () :* ()) (v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* v6 :* ()) -> Extensional (v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* v6 :* ())
unrext7 x = x |: (() *: () *: () *: () *: () *: () *: () *: ())

unrext8 :: RExtensional (() :* () :* () :* () :* () :* () :* () :* () :* ()) (v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* v6 :* v7 :* ()) -> Extensional (v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* v6 :* v7 :* ())
unrext8 x = x |: (() *: () *: () *: () *: () *: () *: () *: () *: ())

unrext9 :: RExtensional (() :* () :* () :* () :* () :* () :* () :* () :* () :* ()) (v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* v6 :* v7 :* v8 :* ()) -> Extensional (v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* v6 :* v7 :* v8 :* ())
unrext9 x = x |: (() *: () *: () *: () *: () *: () *: () *: () *: () *: ())

-- When we combine several relative extensionals, we get more dependencies. Let's treat them comfortably with type lists
-- Partial evaluation. We separate providing the value from partially evaluating a relative extensional.
prext0 :: v0 -> RExtensional (v0 :* r) t -> RExtensional (() :* r) t
prext0 v0 p = rextensionalf (\o -> p |: (v0 *: (ttail o)))

prext1 :: v1 -> RExtensional (v0 :* v1 :* r) t -> RExtensional (v0 :* () :* r) t
prext1 v1 p = rextensionalf (\o -> p |: ((tget0 o) *: v1 *: (ttail1 o)))

prext2 :: v2 -> RExtensional (v0 :* v1 :* v2 :* r) t -> RExtensional (v0 :* v1 :* () :* r) t
prext2 v2 p = rextensionalf (\o -> p |: ((tget0 o) *: (tget1 o) *: v2 *: (ttail2 o)))

prext3 :: v3 -> RExtensional (v0 :* v1 :* v2 :* v3 :* r) t -> RExtensional (v0 :* v1 :* v2 :* () :* r) t
prext3 v3 p = rextensionalf (\o -> p |: ((tget0 o) *: (tget1 o) *: (tget2 o) *: v3 *: (ttail3 o)))

prext4 :: v4 -> RExtensional (v0 :* v1 :* v2 :* v3 :* v4 :* r) t -> RExtensional (v0 :* v1 :* v2 :* v3 :* () :* r) t
prext4 v4 p = rextensionalf (\o -> p |: ((tget0 o) *: (tget1 o) *: (tget2 o) *: (tget3 o) *: v4 *: (ttail4 o)))

prext5 :: v5 -> RExtensional (v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* r) t -> RExtensional (v0 :* v1 :* v2 :* v3 :* v4 :* () :* r) t
prext5 v5 p = rextensionalf (\o -> p |: ((tget0 o) *: (tget1 o) *: (tget2 o) *: (tget3 o) *: (tget4 o) *: v5 *: (ttail5 o)))

prext6 :: v6 -> RExtensional (v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* v6 :* r) t -> RExtensional (v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* () :* r) t
prext6 v6 p = rextensionalf (\o -> p |: ((tget0 o) *: (tget1 o) *: (tget2 o) *: (tget3 o) *: (tget4 o) *: (tget5 o) *: v6 *: (ttail6 o)))

prext7 :: v7 -> RExtensional (v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* v6 :* v7 :* r) t -> RExtensional (v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* v6 :* () :* r) t
prext7 v7 p = rextensionalf (\o -> p |: ((tget0 o) *: (tget1 o) *: (tget2 o) *: (tget3 o) *: (tget4 o) *: (tget5 o) *: (tget6 o) *: v7 *: (ttail7 o)))

prext8 :: v8 -> RExtensional (v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* v6 :* v7 :* v8 :* r) t -> RExtensional (v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* v6 :* v7 :* () :* r) t
prext8 v8 p = rextensionalf (\o -> p |: ((tget0 o) *: (tget1 o) *: (tget2 o) *: (tget3 o) *: (tget4 o) *: (tget5 o) *: (tget6 o) *: (tget7 o) *: v8 *: (ttail8 o)))

prext9 :: v9 -> RExtensional (v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* v6 :* v7 :* v8 :* v9 :* r) t -> RExtensional (v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* v6 :* v7 :* v8 :* () :* r) t
prext9 v9 p = rextensionalf (\o -> p |: ((tget0 o) *: (tget1 o) *: (tget2 o) *: (tget3 o) *: (tget4 o) *: (tget5 o) *: (tget6 o) *: (tget7 o) *: (tget8 o) *: v9 *: (ttail9 o)))

instance Functor (RExtensional v) where
	fmap f x = RExt (\v -> extensional (f $<> (x |: v)))

instance Applicative (RExtensional v) where
	pure x = RExt (\v -> extensional x)
	f <*> x = RExt (\v -> extensional ((f |: v) >$< (x |: v)))

instance Monad (RExtensional v) where
	return x = RExt (\v -> extensional x)
	f1 >>= f2 = RExt (\v -> (f2 $<> (f1 |: v)) |: v)
