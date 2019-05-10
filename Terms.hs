{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module Terms where

import Data.Semigroup
import Data.Map.Strict
import Data.Maybe

-- All terms must be either composites or variables.
-- Composites include constants, which just have no sub-elements
class (Eq t, Ord t) => STerm t where
	is_var :: t -> Bool
	sub_terms :: t -> [t]
	-- Law 1: If is_var t = True then sub_terms t = []
	tmap :: (t -> t) -> t -> t
	-- Law 2: sub_terms (tmap f t) = map f (sub_terms t)

type SSubst t = Map t t

(!$) :: STerm t => SSubst t -> t -> t
s !$ t | is_var t = fromMaybe t (Data.Map.Strict.lookup t s)
s !$ t = tmap (s !$) t
infix !$

(~>) :: STerm t => t -> t -> SSubst t
x ~> v = singleton x v
infix ~>

(~~) :: STerm t => t -> t -> Maybe (SSubst t)


