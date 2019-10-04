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
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
-- This module defines exclusively the notion of a query. It does *not* implement solvers for queries.
-- It also does so in as much a polymorphic way as possible, leaving things like first-order, second-order and specific term structures open to the user.
module CESQLogic where

import Control.Unification
import Control.Unification.IntVar
import HaskellPlus
import Data.Either
import Control.Unification.Types
import Data.List
import Data.Maybe
import Data.Map.Strict
import Syntax
import AnswerSet
import QueryLogic

-- Here are all our assumptions / simplifications:
--	- A literal is either an atom or its negation.
--	- A clause is a disjunction of literals.
--	- A CNF is a conjunction of clauses.
--	- A theory is a CNF.
--	- A goal is a CNF, and must be the negation of the formula that we wish to have proven.
--	- Any free first-order variable in a CNF is considered to be universally quantified.
--	- Any free second-order variable in a CNF will be considered part of the query result (conceptually existentially quantified). Some of these will be part of the select clause and others won't. The others will simply be discarded.
--	- Note that if we wish to add first-order variables to the query, we can effectively do so by adding 0-ary second-order query variables.

data Literal t = PosLit t | NegLit t
type VarLiteral (a :: * -> * -> *) (t :: * -> * -> *) pd fn v pmv fmv = Literal (SOMetawrapA a t pd fn v pmv fmv)
type GroundLiteral (a :: * -> * -> *) (t :: * -> * -> *) pd fn = Literal (GroundA a t pd fn)
-- type GroundT t fn

type Clause (a :: * -> * -> *) (t :: * -> * -> *) pd fn v pmv fmv = [VarLiteral a t pd fn v pmv fmv]
type CNF (a :: * -> * -> *) (t :: * -> * -> *) pd fn v pmv fmv = [Clause a t pd fn v pmv fmv]

type CESQVar pmv fmv = Either pmv fmv
type CESQSol pd fn = Either (GroundSOA pd fn) (GroundSOT fn)
type BaseCESQuery (a :: * -> * -> *) (t :: * -> * -> *) pd fn v pmv fmv = LogicQuery (CNF a t pd fn v pmv fmv)
type CESQuery (a :: * -> * -> *) (t :: * -> * -> *) pd fn v pmv fmv = Query (BaseCESQuery a t pd fn v pmv fmv) (CESQVar pmv fmv) (CESQSol pd fn)
