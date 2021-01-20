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
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
-- Very abstract resolution search library. As abstract as we can reasonably do without making it overly hard to make it precise later.
module Resolution where

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
import Data.Map.Strict
import AnswerSet
import EnumProc
import Data.Maybe
import Data.Graph
import Data.Bifunctor
import Control.Lens
import Control.Monad.State
import Control.Monad.Morph
import Algorithm
import Provenance
import CESQResolutionProvenance
import DependencyGraph
import Identifier
import Control.Monad.ST
import Operable
import Data.Tuple
import Debug.Trace
import Safe (maximumMay, minimumMay)
import GlobalTrace
import Heuristics
import Extensionality

type ResClause l = [Literal l]
type ResCNF l = [ResClause l]

-- l is the literal type
-- r is the constraint type generated when resolving
class Monoid r => ResLiteral h l r m | h -> m, h l -> r where
	-- resolvable works directly on the atoms, not on the literals, so that we can compare literals from the same clause for factorization.
	-- Thus, at this level we can only actually resolve two literals with exactly opposite signs.
	-- It is also an initial check. If false, it means they cannot be resolved. If true, it merely means a constraint can be generated, but that constraint may later on turn unsatisfiable.
	-- It assumes commutativity: if (resolvable a b) is true, then (resolvable b a) is true.
	resolvable :: h -> l -> l -> m Bool
	-- resolve works on two lists of atoms, the positive and the negative ones, and produces a constraint AND a function that modifies other atoms (the "unifier").
	resolve :: h -> [l] -> [l] -> m ((r,l -> l),h)

-- Attached to the CNF, we keep lists of 1) pairs of literals that are resolvable within each CNF and 2) pairs of literals that are resolvable in different CNFs; so that we do not need to recalculate them each time, but we can also choose from amongst all the pairs in the entire CNF.
data ResFactPair l = ResFactPair {resfactpair_clause :: ResClause l, resfactpair_left :: l, resfactpair_right :: l} deriving (Eq, Ord)
data ResResPair l = ResResPair {resrespair_pos :: l, resrespair_neg :: l, resrespair_pos_clause :: ResClause l, resrespair_right_clause :: ResClause l} deriving (Eq, Ord)

data ResPair l = RFP (ResFactPair l) | RRP (ResResPair l) deriving (Eq, Ord)

is_resfactpair :: ResPair l -> Bool
is_resfactpair (RFP _) = True
is_resfactpair (RRP _) = False

is_resrespair :: ResPair l -> Bool
is_resrespair (RFP _) = False
is_resrespair (RRP _) = False

from_resfactpair :: ResPair l -> ResFactPair l
from_resfactpair (RFP x) = x
from_resfactpair (RRP x) = error "It's not a ResFactPair"

from_resrespair :: ResPair l -> ResResPair l
from_resrespair (RFP x) = error "It's not a ResResPair"
from_resrespair (RRP x) = x

data ResStep l = ResStep {resstep_pos :: [l], resstep_neg :: [l]}

type ResLocalHeuristics h li l r m = (Heuristics h (ResPair l) li (ResStep l) m, ResLiteral h l r m)

data ResState l r = ResState {resst_cnf :: ResCNF l, resst_f_pairs :: [ResFactPair l], resst_r_pairs :: [ResResPair l], resst_cstr :: r}

lens_resst_cnf :: Lens' (ResState l r) (ResCNF l)
lens_resst_cnf f resst = fmap (\rcnf -> ResState rcnf (resst_f_pairs resst) (resst_r_pairs resst) (resst_cstr resst)) (f (resst_cnf resst))

lens_resst_f_pairs :: Lens' (ResState l r) [ResFactPair l]
lens_resst_f_pairs f resst = fmap (\rpairs -> ResState (resst_cnf resst) rpairs (resst_r_pairs resst) (resst_cstr resst)) (f (resst_f_pairs resst))

lens_resst_r_pairs :: Lens' (ResState l r) [ResResPair l]
lens_resst_r_pairs f resst = fmap (\rpairs -> ResState (resst_cnf resst) (resst_f_pairs resst) rpairs (resst_cstr resst)) (f (resst_r_pairs resst))

lens_resst_cstr :: Lens' (ResState l r) r
lens_resst_cstr f resst = fmap (\rr -> ResState (resst_cnf resst) (resst_f_pairs resst) (resst_r_pairs resst) rr) (f (resst_cstr resst))

generate_resstate :: ResLocalHeuristics h li l r m => h -> ResCNF l -> m (ResState l r)
generate_resstate h cnf = do
	{
		factpairs <- generate_fact_pairs_cnf h cnf;
		respairs <- generate_res_pairs_cnf h cnf;

		return (ResState cnf factpairs respairs mempty)
	}

generate_res_pairs_cnf :: ResLocalHeuristics h li l r m => h -> ResCNF l -> m [ResResPair l]
generate_res_pairs_cnf h cnf = generate_res_pairs_cnf_rec h cnf

generate_res_pairs_cnf_rec :: ResLocalHeuristics h li l r m => h -> [ResClause l] -> m [ResResPair l]
generate_res_pairs_cnf_rec h (cl:cls) = do
	{
		rcl <- m_concat (generate_res_pairs_clause_clause h cl) cls;
		rcls <- generate_res_pairs_cnf_rec h cls;

		return (rcl ++ rcls)
	}

generate_fact_pairs_cnf :: ResLocalHeuristics h li l r m => h -> ResCNF l -> m [ResFactPair l]
generate_fact_pairs_cnf h cnf = m_concat (generate_fact_pairs_clause h) cnf

generate_res_pairs_clause_clause :: ResLocalHeuristics h li l r m => h -> ResClause l -> ResClause l -> m [ResResPair l]
generate_res_pairs_clause_clause h lcl rcl = m_concat (generate_res_pairs_literal_clause h lcl rcl) lcl

generate_res_pairs_literal_clause :: ResLocalHeuristics h li l r m => h -> ResClause l -> ResClause l -> Literal l -> m [ResResPair l]
generate_res_pairs_literal_clause h lcl rcl ll = m_concat (generate_res_pairs_literal_literal h lcl ll rcl) rcl

generate_fact_pairs_clause :: ResLocalHeuristics h li l r m => h -> ResClause l -> m [ResFactPair l]
generate_fact_pairs_clause h cl = generate_fact_pairs_clause_rec h cl cl

generate_fact_pairs_clause_rec :: ResLocalHeuristics h li l r m => h -> ResClause l -> [Literal l] -> m [ResFactPair l]
generate_fact_pairs_clause_rec h cl (l:ls) = do
	{
		rl <- m_concat (generate_fact_pairs_literal_literal h cl l) ls;
		rls <- generate_fact_pairs_clause_rec h cl ls;

		return (rl ++ rls)
	}

generate_res_pairs_literal_literal :: ResLocalHeuristics h li l r m => h -> ResClause l -> Literal l -> ResClause l -> Literal l -> m [ResResPair l]
generate_res_pairs_literal_literal h lcl (PosLit x) rcl (PosLit y) = return []
generate_res_pairs_literal_literal h lcl (PosLit x) rcl (NegLit y) = do
	{
		pairs <- generate_pairs_atom_atom h x y;

		return ((\(lr,rr) -> ResResPair lr rr lcl rcl) <$> pairs)
	}
generate_res_pairs_literal_literal h lcl (NegLit x) rcl (PosLit y) = do
	{
		pairs <- generate_pairs_atom_atom h x y;

		return ((\(lr,rr) -> ResResPair rr lr rcl lcl) <$> pairs)
	}
generate_res_pairs_literal_literal h lcl (NegLit x) rcl (NegLit y) = return []

generate_fact_pairs_literal_literal :: ResLocalHeuristics h li l r m => h -> ResClause l -> Literal l -> Literal l -> m [ResFactPair l]
generate_fact_pairs_literal_literal h cl (PosLit x) (PosLit y) = do
	{
		pairs <- generate_pairs_atom_atom h x y;

		return ((\(lr,rr) -> ResFactPair cl lr rr) <$> pairs)
	}
generate_fact_pairs_literal_literal h cl (PosLit x) (NegLit y) = return []
generate_fact_pairs_literal_literal h cl (NegLit x) (PosLit y) = return []
generate_fact_pairs_literal_literal h cl (NegLit x) (NegLit y) = do
	{
		pairs <- generate_pairs_atom_atom h x y;

		return ((\(lr,rr) -> ResFactPair cl lr rr) <$> pairs)
	}

generate_pairs_atom_atom :: ResLocalHeuristics h li l r m => h -> l -> l -> m [(l,l)]
generate_pairs_atom_atom h la ra = do
	{
		r <- resolvable h la ra;
		if r then (return [(la,ra)]) else (return [])
	}

data ResMHeuristic li l r a = ResMHeuristic {fromResMHeuristic :: (forall h m. ResLocalHeuristics h li l r m => StateT (ResState l r) (StateT h m) a)}

-- I don't think we will need this function, so I won't bother implementing it. It CAN be implemented, though.
--resMHeuristic_toMHeuristic :: ResMHeuristic li l r a -> ResCNF l -> MHeuristic (ResPair l) li (ResStep l) a

instance Functor (ResMHeuristic li l r) where
	fmap f (ResMHeuristic st) = ResMHeuristic (fmap f st)

instance Applicative (ResMHeuristic li l r) where
	pure a = ResMHeuristic (pure a)
	(ResMHeuristic f) <*> (ResMHeuristic a) = ResMHeuristic (f <*> a)

instance Monad (ResMHeuristic li l r) where
	(ResMHeuristic sta) >>= f = ResMHeuristic (do {a <- sta; let {(ResMHeuristic b) = f a}; b})

res_lift_mheuristic :: MHeuristic (ResPair l) li (ResStep l) a -> ResMHeuristic li l r a
res_lift_mheuristic (MHeuristic x) = ResMHeuristic (lift x)

res_parclift_mheuristic :: ResLocalHeuristics h li l r m => MHeuristic (ResPair l) li (ResStep l) a -> StateT (ResState l r) (StateT h m) a
res_parclift_mheuristic = fromResMHeuristic . res_lift_mheuristic

startResState :: ResCNF l -> ResMHeuristic li l r ()
startResState cnf = ResMHeuristic (do
	{
		h <- lift (get);
		resst <- lift . lift $ generate_resstate h cnf;
		put resst
	})

res_addclause :: ResClause l -> ResMHeuristic li l r ()
res_addclause cl = ResMHeuristic (do
	{
		h <- lift (get);
		resst <- get;
		let {cnf = resst_cnf resst; f_pairs = resst_f_pairs resst; r_pairs = resst_r_pairs resst; cstr = resst_cstr resst};
		let {new_cnf = cl:cnf};

		new_f_pairs <- lift . lift $ generate_fact_pairs_clause h cl;
		new_r_pairs <- lift . lift $ m_concat (generate_res_pairs_clause_clause h cl) cnf;

		let {new_pairs = (RFP <$> new_f_pairs) ++ (RRP <$> new_r_pairs)};

		res_parclift_mheuristic $ traverse m_heur_inform new_pairs;

		put (ResState new_cnf (f_pairs ++ new_f_pairs) (r_pairs ++ new_r_pairs) cstr)
	})

-- This might come back to bite our asses in terms of performance.
-- For now, it's not worth it going the extra mile.
generate_step_options :: Eq l => ResState l r -> [ResStep l]
generate_step_options resst = concat (fmap (\pos -> concat (fmap (\neg -> fposneg pos neg) neglcls)) poslcls)
	where
		cnf = resst_cnf resst;
		poslcls = (\cl -> (cl,generate_step_options_clause resst True cl)) <$> cnf;
		neglcls = (\cl -> (cl,generate_step_options_clause resst False cl)) <$> cnf;
		fposneg = (\(pcl,plss) -> (\(ncl,nlss) -> generate_step_options_posneg resst pcl plss ncl nlss))

generate_step_options_clause :: Eq l => ResState l r -> Bool -> ResClause l -> [[l]]
generate_step_options_clause resst ispos cl = generate_step_options_clause_rec resst ispos cl [] cl

-- Given a list of literals of the same clause assumed compatible, traverse the remainder of the clause to check which other literals can be added.
-- The boolean indicates whether the literals are positive (true) or negative (false).
generate_step_options_clause_rec :: Eq l => ResState l r -> Bool -> ResClause l -> [l] -> [Literal l] -> [[l]]
generate_step_options_clause_rec _ _ _ ls [] = [ls]
generate_step_options_clause_rec resst True cl ls ((NegLit l):lits) = generate_step_options_clause_rec resst True cl ls lits
generate_step_options_clause_rec resst True cl ls ((PosLit l):lits) | (fvalid l) = (generate_step_options_clause_rec resst True cl ls lits) ++ (generate_step_options_clause_rec resst True cl (l:ls) lits)
	where
		fpairs = resst_f_pairs resst;
		ffind = (\l1 -> \l2 -> (any (== (ResFactPair cl l1 l2)) fpairs) || (any (== (ResFactPair cl l2 l1)) fpairs));
		fvalid = (\l -> all (ffind l) ls)
generate_step_options_clause_rec resst False cl ls ((PosLit l):lits) = generate_step_options_clause_rec resst False cl ls lits
generate_step_options_clause_rec resst False cl ls ((NegLit l):lits) = (generate_step_options_clause_rec resst False cl ls lits) ++ (generate_step_options_clause_rec resst False cl (l:ls) lits)
	where
		fpairs = resst_f_pairs resst;
		ffind = (\l1 -> \l2 -> (any (== (ResFactPair cl l1 l2)) fpairs) || (any (== (ResFactPair cl l2 l1)) fpairs));
		fvalid = (\l -> all (ffind l) ls)

-- Given two lists of lists of compatible literals, one for positive and one for negative literals, select the pairs of lists that are fully compatible.
generate_step_options_posneg :: Eq l => ResState l r -> ResClause l -> [[l]] -> ResClause l -> [[l]] -> [ResStep l]
generate_step_options_posneg resst poscl poss negcl negss = (\(pos,neg) -> ResStep pos neg) <$> filteredpairs
	where
		rpairs = resst_r_pairs resst;
		ffind = (\lpos -> \lneg -> any (== (ResResPair lpos lneg poscl negcl)) rpairs);
		fsingle = (\pos -> \neg -> all (\lpos -> all (\lneg -> ffind lpos lneg) neg) pos);
		allpairs = concat (fmap (\pos -> fmap (\neg -> (pos,neg)) negss) poss);
		filteredpairs = Data.List.filter (uncurry fsingle) allpairs

{-|
res_choosepair :: li -> ResFullMonad l r li (Maybe (ResPair l r))
res_choosepair li = do
	{
		resst <- get;
		
		lift (m_heur_choose li (resst_pairs resst))
	}

res_compute :: (ResLiteral l r, ResLocalHeuristics h li l r m) => h -> ResFullMonad l r li a -> ResCNF l -> m a
res_compute h rfl cnf = m_heur_compute h (fst <$> (runStateT rfl (startResState cnf)))

res_resolve :: ResLiteral l r => ResPair l r -> ResFullMonad l r li (ResClause l)
res_resolve pair = do
	{
		let {ll = respair_left pair; rl = respair_right pair; lcl = respair_left_clause pair; rcl = respair_right_clause pair; cstr = respair_cstr pair};

		-- The constraint is pre-generated, we only need to use it.
		-- But we need to produce the resolvent.
	}

|-}
