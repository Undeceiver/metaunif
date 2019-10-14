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
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE StandaloneDeriving #-}
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

data Literal t = PosLit t | NegLit t deriving Functor

instance Read t => Read (Literal t) where
	readsPrec _ xs =
		case stripPrefix "+" xs of
		{
			Just rest -> (let r = (head (reads rest)::(t,String))
				in [(PosLit (fst r), (snd r))]);
			Nothing ->
		case stripPrefix "-" xs of
		{
			Just rest -> (let r = (head (reads rest)::(t,String))
				in [(NegLit (fst r), (snd r))]);
			Nothing -> error ("Cannot read literal: " ++ xs)
		}}

newtype NormalizeLiteral t = NormalizeLiteral {fromNormalizeLiteral :: Literal t}
instance Normalizable a b => Normalizable (NormalizeLiteral a) (NormalizeLiteral b) where
	inject_normal (NormalizeLiteral (PosLit x)) = NormalizeLiteral (PosLit (inject_normal x))
	inject_normal (NormalizeLiteral (NegLit x)) = NormalizeLiteral (NegLit (inject_normal x))
	normalize (NormalizeLiteral (PosLit x)) = NormalizeLiteral (PosLit (normalize x))
	normalize (NormalizeLiteral (NegLit x)) = NormalizeLiteral (NegLit (normalize x))

type VarLiteral (a :: * -> * -> *) (t :: * -> * -> *) pd fn v pmv fmv = Literal (SOMetawrapA a t pd fn v pmv fmv)
type GroundLiteral (a :: * -> * -> *) (t :: * -> * -> *) pd fn = Literal (GroundA a t pd fn)
-- type GroundT t fn

type Clause (a :: * -> * -> *) (t :: * -> * -> *) pd fn v pmv fmv = [VarLiteral a t pd fn v pmv fmv]
type CNF (a :: * -> * -> *) (t :: * -> * -> *) pd fn v pmv fmv = [Clause a t pd fn v pmv fmv]

newtype CESQVar pmv fmv = CESQVar {fromCESQVar :: Either pmv fmv} deriving (Eq)
newtype CESQSol pd fn = CESQSol {fromCESQSol :: Either (GroundSOA pd fn) (GroundSOT fn)} deriving (Eq)
type BaseCESQuery (a :: * -> * -> *) (t :: * -> * -> *) pd fn v pmv fmv = LogicQuery (CNF a t pd fn v pmv fmv)
type CESQuery (a :: * -> * -> *) (t :: * -> * -> *) pd fn v pmv fmv = Query (BaseCESQuery a t pd fn v pmv fmv) (CESQVar pmv fmv) (CESQSol pd fn)

instance Show t => Show (Literal t) where
	show (PosLit x) = "+" ++ (show x)
	show (NegLit x) = "-" ++ (show x)

instance (Show pmv, Show fmv) => Show (CESQVar pmv fmv) where
	show (CESQVar (Left x)) = show x
	show (CESQVar (Right x)) = show x

instance (Show pd, Show fn) => Show (CESQSol pd fn) where
	show (CESQSol (Left x)) = show x
	show (CESQSol (Right x)) = show x

instance (Ord pmv, Ord fmv, Eq pmv, Eq fmv) => Ord (CESQVar pmv fmv) where
	compare (CESQVar a) (CESQVar b) = compare a b

-- Placeholder. Need to replace when I know what the proper type I will use is.
type ImplicitInstantiation pd fn pmv fmv = ()

instance Implicit (ImplicitInstantiation pd fn pmv fmv) (CESQVar pmv fmv := CESQSol pd fn) where
	checkImplicit = undefined
	enumImplicit = undefined

instance Queriable (BaseCESQuery a t pd fn v pmv fmv) (CESQVar pmv fmv) (CNF a t pd fn v pmv fmv) (CESQSol pd fn) (ImplicitInstantiation pd fn pmv fmv) where
	runBaseQ t sel q = undefined

instance Substitutable (CESQSol pd fn) (CESQVar pmv fmv) (CESQSol pd fn) where
	subst _ _ = id

instance Substitutable (SOMetawrapA a t pd fn v pmv fmv) (CESQVar pmv fmv) (CESQSol pd fn) where
	subst = undefined

instance Substitutable (VarLiteral a t pd fn v pmv fmv) (CESQVar pmv fmv) (CESQSol pd fn) where
	subst = subst_fmap

instance Substitutable (Clause a t pd fn v pmv fmv) (CESQVar pmv fmv) (CESQSol pd fn) where
	subst = subst_fmap

instance Substitutable (CNF a t pd fn v pmv fmv) (CESQVar pmv fmv) (CESQSol pd fn) where
	subst = subst_fmap

instance Substitutable (BaseCESQuery a t pd fn v pmv fmv) (CESQVar pmv fmv) (CESQSol pd fn) where
	subst = subst_fmap

-- This is actually unlikely to happen, because meta-variables have arity, which means they are not just an Int.
instance (Variabilizable pmv, Variabilizable fmv) => Variabilizable (CESQVar pmv fmv) where
	from_var (IntVar i) | mod i 2 == 0 = CESQVar (Left (from_var (IntVar (quot i 2))))
	from_var (IntVar i) = CESQVar (Right (from_var (IntVar (quot (i-1) 2))))
	get_var (CESQVar (Left i)) = IntVar (2 * (getVarID_gen i))
	get_var (CESQVar (Right i)) = IntVar (2 * (getVarID_gen i) + 1)

instance (Ord pmv, Ord fmv, Eq pmv, Eq fmv, Implicit (ImplicitInstantiation pd fn pmv fmv) (CESQVar pmv fmv := CESQSol pd fn)) => ImplicitF (ImplicitInstantiation pd fn pmv fmv) (CESQVar pmv fmv := CESQSol pd fn) (ImplicitInstantiation pd fn pmv fmv) (CESQVar pmv fmv := CESQSol pd fn) (BaseQueryInput (BaseCESQuery a t pd fn v pmv fmv) (CESQVar pmv fmv) (CNF a t pd fn v pmv fmv) (CESQSol pd fn)) where
	composeImplicit = composeImplicitDefault

instance (Implicit (ImplicitInstantiation pd fn pmv fmv) (CESQVar pmv fmv := CESQSol pd fn)) => ImplicitF (ImplicitInstantiation pd fn pmv fmv) (CESQVar pmv fmv := CESQSol pd fn) (ImplicitInstantiation pd fn pmv fmv) (CESQVar pmv fmv := CESQSol pd fn) (CESQVar pmv fmv :->= CESQSol pd fn) where
	composeImplicit = composeImplicitDefault

instance (Eq pmv, Eq pd, Eq fmv, Eq fn, Ord pmv, Ord fmv) => ImplicitF (AnswerSet (ImplicitInstantiation pd fn pmv fmv) (CESQVar pmv fmv := CESQSol pd fn), AnswerSet (ImplicitInstantiation pd fn pmv fmv) (CESQVar pmv fmv := CESQSol pd fn)) (CESQVar pmv fmv := CESQSol pd fn, CESQVar pmv fmv := CESQSol pd fn) (ImplicitInstantiation pd fn pmv fmv) (CESQVar pmv fmv := CESQSol pd fn) ProductQOP where
	composeImplicit = composeImplicitDefault

testtypes :: (Eq pmv, Eq pd, Eq fmv, Eq fn, Ord pmv, Ord fmv) => CNF a t pd fn v pmv fmv -> Query (BaseCESQuery a t pd fn v pmv fmv) (CESQVar pmv fmv) (CESQSol pd fn) -> AnswerSet (ImplicitInstantiation pd fn pmv fmv) (CESQVar pmv fmv := CESQSol pd fn)
testtypes = runQuery


