{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
--{-# LANGUAGE UndecidableInstances #-}
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
{-# LANGUAGE DerivingVia #-}
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
import Equiv
import Similarity
import Algorithm

-- Here are all our assumptions / simplifications:
--	- A literal is either an atom or its negation.
--	- A clause is a disjunction of literals.
--	- A CNF is a conjunction of clauses.
--	- A theory is a CNF.
--	- A goal is a CNF, and must be the negation of the formula that we wish to have proven.
--	- Any free first-order variable in a CNF is considered to be universally quantified.
--	- Any free second-order variable in a CNF will be considered part of the query result (conceptually existentially quantified). Some of these will be part of the select clause and others won't. The others will simply be discarded.
--	- Note that if we wish to add first-order variables to the query, we can effectively do so by adding 0-ary second-order query variables.

type VarLiteral (a :: * -> * -> *) (t :: * -> * -> *) mpd pd fn v pmv fmv = Literal (CombSOAtom a t LambdaCNF mpd pd fn v pmv fmv)
type GroundLiteral (a :: * -> * -> *) (t :: * -> * -> *) pd fn = Literal (GroundA a t pd fn)
-- type GroundT t fn

-- Should probablymaybe implement permutation invariant equalities for clauses and CNFs, same as LambdaClauses and LambdaCNFs.
type Clause (a :: * -> * -> *) (t :: * -> * -> *) mpd pd fn v pmv fmv = [VarLiteral a t mpd pd fn v pmv fmv]
type CNF (a :: * -> * -> *) (t :: * -> * -> *) mpd pd fn v pmv fmv = [Clause a t mpd pd fn v pmv fmv]

newtype CESQVar pmv fmv = CESQVar {fromCESQVar :: Either pmv fmv} deriving (Eq)
newtype CESQSol pd fn = CESQSol {fromCESQSol :: Either (LambdaCNF (GroundSOA pd fn)) (GroundSOT fn)} deriving (Eq)
newtype ParcCESQSol pd fn pmv fmv = ParcCESQSol {fromParcCESQSol :: Either (LambdaCNF (SOAtom pd fn pmv fmv)) (SOTerm fn fmv)}
type BaseCESQuery (a :: * -> * -> *) (t :: * -> * -> *) mpd pd fn v pmv fmv = LogicQuery (CNF a t mpd pd fn v pmv fmv) (SOMetawrapA a t pd fn v pmv fmv)
type CESQuery (a :: * -> * -> *) (t :: * -> * -> *) mpd pd fn v pmv fmv = Query (BaseCESQuery a t mpd pd fn v pmv fmv) (CESQVar pmv fmv) (CESQSol pd fn)

instance (Show pmv, Show fmv) => Show (CESQVar pmv fmv) where
	show (CESQVar (Left x)) = show x
	show (CESQVar (Right x)) = show x

instance (Show pd, Show fn) => Show (CESQSol pd fn) where
	show (CESQSol (Left x)) = show x
	show (CESQSol (Right x)) = show x

instance (Show pd, Show fn, Show pmv, Show fmv) => Show (ParcCESQSol pd fn pmv fmv)

instance (Ord pmv, Ord fmv, Eq pmv, Eq fmv) => Ord (CESQVar pmv fmv) where
	compare (CESQVar a) (CESQVar b) = compare a b

-- Placeholder. Need to replace when I know what the proper type I will use is.
type ImplicitInstantiation pd fn pmv fmv = ()

instance Implicit (ImplicitInstantiation pd fn pmv fmv) (CESQVar pmv fmv := CESQSol pd fn) where
	checkImplicit = undefined
	enumImplicit = undefined

instance Queriable (BaseCESQuery a t mpd pd fn v pmv fmv) (CESQVar pmv fmv) (CNF a t mpd pd fn v pmv fmv) (CESQSol pd fn) (ImplicitInstantiation pd fn pmv fmv) where
	runBaseQ t sel q = undefined

instance Substitutable (CESQSol pd fn) (CESQVar pmv fmv) (CESQSol pd fn) where
	subst = undefined

instance Substitutable (SOMetawrap t fn v fmv) (CESQVar pmv fmv) (CESQSol pd fn) where
	subst = undefined

instance Substitutable (SOMetawrapA a t pd fn v pmv fmv) (CESQVar pmv fmv) (CESQSol pd fn) where
	subst = undefined

instance Substitutable (FirstSOAAtom a LambdaCNF mpd pd fn pmv fmv) (CESQVar pmv fmv) (CESQSol pd fn) where
	subst = undefined

instance Substitutable (CombSOAtom a t LambdaCNF mpd pd fn v pmv fmv) (CESQVar pmv fmv) (CESQSol pd fn) where
	subst = undefined

instance Substitutable (VarLiteral a t mpd pd fn v pmv fmv) (CESQVar pmv fmv) (CESQSol pd fn) where
	subst = subst_fmap

instance Substitutable (Clause a t mpd pd fn v pmv fmv) (CESQVar pmv fmv) (CESQSol pd fn) where
	subst = subst_fmap

instance Substitutable (CNF a t mpd pd fn v pmv fmv) (CESQVar pmv fmv) (CESQSol pd fn) where
	subst = subst_fmap

instance Substitutable (BaseCESQuery a t mpd pd fn v pmv fmv) (CESQVar pmv fmv) (CESQSol pd fn) where
	subst = subst_bimap



instance Substitutable (ParcCESQSol pd fn pmv fmv) (CESQVar pmv fmv) (CESQVar pmv fmv) where
	subst = undefined

instance Substitutable (SOMetawrap t fn v fmv) (CESQVar pmv fmv) (CESQVar pmv fmv) where
	subst = undefined

instance Substitutable (SOMetawrapA a t pd fn v pmv fmv) (CESQVar pmv fmv) (CESQVar pmv fmv) where
	subst = undefined

instance Substitutable (FirstSOAAtom a LambdaCNF mpd pd fn pmv fmv) (CESQVar pmv fmv) (CESQVar pmv fmv) where
	subst = undefined

instance Substitutable (CombSOAtom a t LambdaCNF mpd pd fn v pmv fmv) (CESQVar pmv fmv) (CESQVar pmv fmv) where
	subst = undefined

instance Substitutable (VarLiteral a t mpd pd fn v pmv fmv) (CESQVar pmv fmv) (CESQVar pmv fmv) where
	subst = subst_fmap

instance Substitutable (Clause a t mpd pd fn v pmv fmv) (CESQVar pmv fmv) (CESQVar pmv fmv) where
	subst = subst_fmap

instance Substitutable (CNF a t mpd pd fn v pmv fmv) (CESQVar pmv fmv) (CESQVar pmv fmv) where
	subst = subst_fmap

instance Substitutable (BaseCESQuery a t mpd pd fn v pmv fmv) (CESQVar pmv fmv) (CESQVar pmv fmv) where
	subst = subst_bimap


-- This is actually unlikely to happen, because meta-variables have arity, which means they are not just an Int.
instance (Variabilizable pmv, Variabilizable fmv) => Variabilizable (CESQVar pmv fmv) where
	from_var (IntVar i) | mod i 2 == 0 = CESQVar (Left (from_var (IntVar (quot i 2))))
	from_var (IntVar i) = CESQVar (Right (from_var (IntVar (quot (i-1) 2))))
	get_var (CESQVar (Left i)) = IntVar (2 * (getVarID_gen i))
	get_var (CESQVar (Right i)) = IntVar (2 * (getVarID_gen i) + 1)

instance (Ord pmv, Ord fmv, Eq pmv, Eq fmv, Implicit (ImplicitInstantiation pd fn pmv fmv) (CESQVar pmv fmv := CESQSol pd fn)) => ImplicitF (ImplicitInstantiation pd fn pmv fmv) (ImplicitInstantiation pd fn pmv fmv) (CESQVar pmv fmv := CESQSol pd fn) (BaseQueryInput (BaseCESQuery a t mpd pd fn v pmv fmv) (CESQVar pmv fmv) (CNF a t mpd pd fn v pmv fmv) (CESQSol pd fn)) where
	composeImplicit = composeImplicitDefault

instance (Implicit (ImplicitInstantiation pd fn pmv fmv) (CESQVar pmv fmv := CESQSol pd fn)) => ImplicitF (ImplicitInstantiation pd fn pmv fmv) (ImplicitInstantiation pd fn pmv fmv) (CESQVar pmv fmv := CESQSol pd fn) (CESQVar pmv fmv :->= CESQSol pd fn) where
	composeImplicit = composeImplicitDefault

instance (Eq pmv, Eq pd, Eq fmv, Eq fn, Ord pmv, Ord fmv) => ImplicitF (AnswerSet (ImplicitInstantiation pd fn pmv fmv) (CESQVar pmv fmv := CESQSol pd fn), AnswerSet (ImplicitInstantiation pd fn pmv fmv) (CESQVar pmv fmv := CESQSol pd fn)) (ImplicitInstantiation pd fn pmv fmv) (CESQVar pmv fmv := CESQSol pd fn) ProductQOP where
	composeImplicit = composeImplicitDefault

testtypes :: (Eq pmv, Eq pd, Eq fmv, Eq fn, Ord pmv, Ord fmv) => CNF a t mpd pd fn v pmv fmv -> Query (BaseCESQuery a t mpd pd fn v pmv fmv) (CESQVar pmv fmv) (CESQSol pd fn) -> AnswerSet (ImplicitInstantiation pd fn pmv fmv) (CESQVar pmv fmv := CESQSol pd fn)
testtypes = runQuery



-- Lambda CNFs : Predicates (functions from variables to atoms) with conjunctions, disjunctions and negations, but in CNF form. The reason why we force CNF form here is not very strong. It just is possible and it seems a regularity that might be useful in the future. But better reasons might make us change this decision.
-- Note that this *does not* include second-order atoms within it. We can choose to layer these two things either way we want, but usually they will be two clearly separate layers.
type LambdaLiteral pd = Literal pd

-- These newtypes are so unnecessary though.
newtype LambdaClause pd = LambdaClause [LambdaLiteral pd] 
newtype LambdaCNF pd = LambdaCNF [LambdaClause pd]

-- These equalities should be replaced by permutation-invariant equality.
deriving instance Eq pd => Eq (LambdaClause pd)
deriving instance Ord pd => Ord (LambdaClause pd)
deriving instance Functor LambdaClause
deriving instance Foldable LambdaClause
deriving instance Traversable LambdaClause
deriving instance Eq pd => Eq (LambdaCNF pd)
deriving instance Ord pd => Ord (LambdaCNF pd)
deriving instance Functor LambdaCNF
deriving instance Foldable LambdaCNF
deriving instance Traversable LambdaCNF

instance Similarity Literal where
	similarities (PosLit l1) (PosLit l2) = comp (((Left l1) =:~ (Right l2)) $ empty_equiv)
	similarities (NegLit l1) (NegLit l2) = comp (((Left l1) =:~ (Right l2)) $ empty_equiv)
	similarities _ _ = emptycomp

instance Similarity LambdaClause where
	similarities (LambdaClause cl1) (LambdaClause cl2) = composite_similarities (SetSimilarList cl1) (SetSimilarList cl2)

instance Similarity LambdaCNF where
	similarities (LambdaCNF cnf1) (LambdaCNF cnf2) = composite_similarities (SetSimilarList cnf1) (SetSimilarList cnf2)

instance Show pd => Show (LambdaClause pd) where
	show (LambdaClause x) = show x

instance Read pd => Read (LambdaClause pd) where
	readsPrec i xs = case (readsPrec i xs) of ((x,rst):_) -> [(LambdaClause x,rst)]

instance Show pd => Show (LambdaCNF pd) where
	show (LambdaCNF x) = show x

instance Read pd => Read (LambdaCNF pd) where
	readsPrec i xs = case (readsPrec i xs) of ((x,rst):_) -> [(LambdaCNF x,rst)]

deriving via FoldableArity Literal pd instance HasArity pd => HasArity (LambdaLiteral pd)
deriving via FoldableArity [] (LambdaLiteral pd) instance HasArity pd => HasArity (LambdaClause pd)
deriving via FoldableArity [] (LambdaClause pd) instance HasArity pd => HasArity (LambdaCNF pd)

-- Note that these Unifiable instances are not complete: They unify the CNFs only if they are syntactically exactly equal: Same ordering, same signs. They do not do any fancy stuff with the potential reorderings of the CNF, or variables that may be negated, or variables that may stand for a composite. This is a work of its own, that can be done, but which we do not have time to carry out here.
instance Unifiable LambdaClause where
	zipMatch (LambdaClause ll) (LambdaClause rl) = LambdaClause <$> traverse (uncurry zipMatch) (zip ll rl)
	
instance Unifiable LambdaCNF where
	zipMatch (LambdaCNF ll) (LambdaCNF rl) = LambdaCNF <$> traverse (uncurry zipMatch) (zip ll rl)

-- TODO: Here we will provide functions for, at the very least, evaluating a lambda CNF into a CNF given a set of variables. Other functionalities will likely also be relevant.
