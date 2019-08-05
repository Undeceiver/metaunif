{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
module LogicVsEnumProc where

import Control.Monad.Logic
import Control.Monad.Logic.Class
import EnumProc

type ChurchList a = (forall r. (a -> r -> r) -> r -> r)

church_nil :: ChurchList a
church_nil f r = r

church_cons :: a -> ChurchList a -> ChurchList a
church_cons x xs f r = f x (xs f r)

church_map :: (a -> b) -> ChurchList a -> ChurchList b
church_map f l g r = l (\h -> \t -> g (f h) t) r

log_multiples :: Int -> Logic Int
log_multiples n = logic (log_multiples_fn n)

log_multiples_fn :: Int -> ChurchList Int
log_multiples_fn n = church_cons n (church_map (+n) (log_multiples_fn n))

log_naturals :: Logic Int
log_naturals = log_multiples 1

log_powers :: Int -> Logic Int
log_powers n = logic (log_powers_fn n)

log_powers_fn :: Int -> ChurchList Int
log_powers_fn n = church_cons n (church_map (*n) (log_powers_fn n))

log_allmultiples :: Logic Int
log_allmultiples = (log_powers 100) >>- log_multiples

log_filter :: (a -> Bool) -> Logic a -> Logic a
log_filter f l = l >>- (\x -> if (f x) then (return x) else mzero)

log_somefiltered :: Logic Int
log_somefiltered = log_naturals >>- (\x -> log_filter odd (log_powers x))

log_somefiltered2 :: Logic Int
log_somefiltered2 = log_naturals >>- (\x -> log_filter even (log_multiples x))


enum_multiples :: Int -> EnumProc Int
enum_multiples n = uns_enum_from_list (map (n*) [1..])

enum_naturals :: EnumProc Int
enum_naturals = enum_multiples 1

enum_powers :: Int -> EnumProc Int
enum_powers n = uns_enum_from_list (map (n^) [1..])

enum_allmultiples :: EnumProc Int
enum_allmultiples = (enum_powers 100) >>= enum_multiples

enum_somefiltered :: EnumProc Int
enum_somefiltered = enum_naturals >>= (\x -> efilter odd (enum_powers x))

enum_somefiltered2 :: EnumProc Int
enum_somefiltered2 = enum_naturals >>= (\x -> efilter even (enum_multiples x))
