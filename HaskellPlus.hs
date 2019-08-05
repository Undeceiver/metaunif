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

collapse_mb :: Maybe (Maybe t) -> Maybe t
collapse_mb Nothing = Nothing
collapse_mb (Just Nothing) = Nothing
collapse_mb (Just (Just x)) = (Just x)

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

mb_from_exceptT :: Monad m => (ExceptT e m) a -> m (Maybe a)
mb_from_exceptT exc = (runExceptT exc) >>= (\x -> case x of {Left e -> return Nothing; Right y -> return (Just y)})

clear_value :: Monad m => m a -> m ()
clear_value = (>> (return ()))


-- Type lists
type a :* b = (a,b)
infixr 7 :*

totlist :: a -> a :* ()
totlist x = x *: ()

(*:) :: a -> b -> (a :* b)
a *: b = (a,b)
infixr 7 *:

(*::) :: a -> b -> (a :* b :* ())
a *:: b = a *: b *: ()
infixr 7 *::

-- Provide functions to use them nicely. Unfortunately we cannot do one function to obtain any given of them, but we can do the first ten.
thead :: a :* b -> a
thead (a,b) = a

ttail :: a :* b -> b
ttail (a,b) = b

tget0 :: a :* _ -> a
tget0 = thead

tget1 :: _ :* a :* _ -> a
tget1 = thead . ttail

tget2 :: _ :* _ :* a :* _ -> a
tget2 = thead . ttail . ttail

tget3 :: _ :* _ :* _ :* a :* _ -> a
tget3 = thead . ttail . ttail . ttail

tget4 :: _ :* _ :* _ :* _ :* a :* _ -> a
tget4 = thead . ttail . ttail . ttail . ttail

tget5 :: _ :* _ :* _ :* _ :* _ :* a :* _ -> a
tget5 = thead . ttail . ttail . ttail . ttail . ttail

tget6 :: _ :* _ :* _ :* _ :* _ :* _ :* a :* _ -> a
tget6 = thead . ttail . ttail . ttail . ttail . ttail . ttail

tget7 :: _ :* _ :* _ :* _ :* _ :* _ :* _ :* a :* _ -> a
tget7 = thead . ttail . ttail . ttail . ttail . ttail . ttail . ttail

tget8 :: _ :* _ :* _ :* _ :* _ :* _ :* _ :* _ :* a :* _ -> a
tget8 = thead . ttail . ttail . ttail . ttail . ttail . ttail . ttail . ttail

tget9 :: _ :* _ :* _ :* _ :* _ :* _ :* _ :* _ :* _ :* a :* _ -> a
tget9 = thead . ttail . ttail . ttail . ttail . ttail . ttail . ttail . ttail . ttail

ttail0 :: _ :* r -> r
ttail0 = ttail

ttail1 :: _ :* _ :* r -> r
ttail1 = ttail . ttail

ttail2 :: _ :* _ :* _ :* r -> r
ttail2 = ttail . ttail . ttail

ttail3 :: _ :* _ :* _ :* _ :* r -> r
ttail3 = ttail . ttail . ttail . ttail

ttail4 :: _ :* _ :* _ :* _ :* _ :* r -> r
ttail4 = ttail . ttail . ttail . ttail . ttail

ttail5 :: _ :* _ :* _ :* _ :* _ :* _ :* r -> r
ttail5 = ttail . ttail . ttail . ttail . ttail . ttail

ttail6 :: _ :* _ :* _ :* _ :* _ :* _ :* _ :* r -> r
ttail6 = ttail . ttail . ttail . ttail . ttail . ttail . ttail

ttail7 :: _ :* _ :* _ :* _ :* _ :* _ :* _ :* _ :* r -> r
ttail7 = ttail . ttail . ttail . ttail . ttail . ttail . ttail . ttail

ttail8 :: _ :* _ :* _ :* _ :* _ :* _ :* _ :* _ :* _ :* r -> r
ttail8 = ttail . ttail . ttail . ttail . ttail . ttail . ttail . ttail . ttail

ttail9 :: _ :* _ :* _ :* _ :* _ :* _ :* _ :* _ :* _ :* _ :* r -> r
ttail9 = ttail . ttail . ttail . ttail . ttail . ttail . ttail . ttail . ttail . ttail


-- Utility to normalize to a certain list length for compatibility with other functions
tinsert0 :: v0 -> r -> v0 :* r
tinsert0 v0 r = v0 *: r

tfill0 :: r -> () :* r
tfill0 = tinsert0 ()

tinsert1 :: v1 -> v0 :* r -> v0 :* v1 :* r
tinsert1 v1 r = (thead r) *: (tinsert0 v1 (ttail r))

tfill1 :: v0 :* r -> v0 :* () :* r
tfill1 = tinsert1 ()

tinsert2 :: v2 -> v0 :* v1 :* r -> v0 :* v1 :* v2 :* r
tinsert2 v2 r = (thead r) *: (tinsert1 v2 (ttail r))

tfill2 :: v0 :* v1 :* r -> v0 :* v1 :* () :* r
tfill2 = tinsert2 ()

tinsert3 :: v3 -> v0 :* v1 :* v2 :* r -> v0 :* v1 :* v2 :* v3 :* r
tinsert3 v3 r = (thead r) *: (tinsert2 v3 (ttail r))

tfill3 :: v0 :* v1 :* v2 :* r -> v0 :* v1 :* v2 :* () :* r
tfill3 = tinsert3 ()

tinsert4 :: v4 -> v0 :* v1 :* v2 :* v3 :* r -> v0 :* v1 :* v2 :* v3 :* v4 :* r
tinsert4 v4 r = (thead r) *: (tinsert3 v4 (ttail r))

tfill4 :: v0 :* v1 :* v2 :* v3 :* r -> v0 :* v1 :* v2 :* v3 :* () :* r
tfill4 = tinsert4 ()

tinsert5 :: v5 -> v0 :* v1 :* v2 :* v3 :* v4 :* r -> v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* r
tinsert5 v5 r = (thead r) *: (tinsert4 v5 (ttail r))

tfill5 :: v0 :* v1 :* v2 :* v3 :* v4 :* r -> v0 :* v1 :* v2 :* v3 :* v4 :* () :* r
tfill5 = tinsert5 ()

tinsert6 :: v6 -> v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* r -> v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* v6 :* r
tinsert6 v6 r = (thead r) *: (tinsert5 v6 (ttail r))

tfill6 :: v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* r -> v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* () :* r
tfill6 = tinsert6 ()

tinsert7 :: v7 -> v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* v6 :* r -> v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* v6 :* v7 :* r
tinsert7 v7 r = (thead r) *: (tinsert6 v7 (ttail r))

tfill7 :: v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* v6 :* r -> v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* v6 :* () :* r
tfill7 = tinsert7 ()

tinsert8 :: v8 -> v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* v6 :* v7 :* r -> v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* v6 :* v7 :* v8 :* r
tinsert8 v8 r = (thead r) *: (tinsert7 v8 (ttail r))

tfill8 :: v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* v6 :* v7 :* r -> v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* v6 :* v7 :* () :* r
tfill8 = tinsert8 ()

tinsert9 :: v9 -> v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* v6 :* v7 :* v8 :* r -> v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* v6 :* v7 :* v8 :* v9 :* r
tinsert9 v9 r = (thead r) *: (tinsert8 v9 (ttail r))

tfill9 :: v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* v6 :* v7 :* v8 :* r -> v0 :* v1 :* v2 :* v3 :* v4 :* v5 :* v6 :* v7 :* v8 :* () :* r
tfill9 = tinsert9 ()




-- Types that are essentially functions with added functionality.
class Functional t a b where
	tofun :: t -> a -> b
