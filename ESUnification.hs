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
-- Existential second-order unification (with instantiation set results, performing batch unification (multiple unifiers and equations at once))
module ESUnification where

import Control.Exception
import Data.Functor.Compose
import Data.Functor.Identity
import Control.Unification
import Control.Unification.IntVar
import Control.Unification.Types
import Control.Monad.Trans
import Control.Monad.Trans.Class
import Control.Monad.Trans.Identity
import Control.Monad.Error.Class
import HaskellPlus
import Syntax
import Data.Functor.Fixedpoint
import Data.List
import Data.Map
import AnswerSet
import EnumProc

-- Our objectives:
-- type SOMetaterm = SOMetawrap CTermF OFunction OVariable SOMVariable


data TermDependant t fn v sov uv = TDDirect (SOMetawrap t fn v sov) | TDUnif uv (TermDependant t fn v sov uv)
data UnifEquation t fn v sov uv = TermUnif (TermDependant t fn v sov uv) (TermDependant t fn v sov uv) -- Pending adding atom unification here when we are ready.

type UnifSystem t fn v sov uv = [UnifEquation t fn v sov uv]

-- The solution to a single unifier is simply an instantiation set of the variables (both first and second-order) to elements in the Herbrand universe.
-- We define things individually, and use the AnswerSet monad to do things the right way. An explicit solution is a map from variables to ground terms (both first and second-order)
data UnifSolution t fn v sov = UnifSolution {fosol :: Map v (GroundT t fn), sosol :: Map sov (GroundSOT t fn)} -- Pending adding predicate variables!!!
type UnifSysSolution t fn v sov uv = Map uv (UnifSolution t fn v sov)

-- A system of equations is an implicit solution to a system of unification equations
instance Implicit (UnifSystem t fn v sov uv) (UnifSysSolution t fn v sov uv) where
	checkImplicit = undefined
	enumImplicit = undefined

-- A dependency graph is another implicit solution to a system of unification equations (an intermediate one)
-- instance Implicit **DEPENDENCY GRAPH** (UnifSysSolution t fn v sov uv) where

-- Finally, a most general unifier is an almost explicit solution to a system of unification equations.
-- instance Implicit **MOST GENERAL UNIFIERS** (UnifSysSolution t fn v sov uv) where

-- Wildcard (as opposed to variable, but we represent them with variables) representation of most general unifiers.

