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
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
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

-- We save the references to the literals in the clause as integers (indices). This removes any weird ambiguity that may appear.
-- Each element in resclause_compatibles is a list of indices of literals such that they can all in principle be resolved together.
data ResClause l = ResClause {resclause_lits :: [Literal l], resclause_compatibles :: [[Int]]}
-- rescnf_steps are all the possible resolutions that we can carry on this CNF.
-- This data structure has the following rationale:
--	- Clauses are not modified once they are added to the CNF. This is why we do not need lenses for clauses.
--	- Thus, the sets of potentially unifiable literals in each clause do not change.
--	- Possible resolutions to carry are added each time a clause is added, by comparing this new clause to the existing clauses, and using their respective compatible sets.
--	- Possible resolutions are only removed when they are actually carried out: When a resolution is taken, we remove it so that we do not do it again. We do not remove any others when doing this.
data ResStep l = ResStep {resstep_poscl :: Int, resstep_poslits :: [Int], resstep_negcl :: Int, resstep_neglits :: [Int], resstep_clauses :: [ResClause l]}
data ResCNF l = ResCNF {rescnf_clauses :: [ResClause l], rescnf_steps :: [ResStep l]}

lens_rescnf_clauses :: Lens' (ResCNF l) [ResClause l]
lens_rescnf_clauses f rescnf = fmap (\rclauses -> ResCNF rclauses (rescnf_steps rescnf)) (f (rescnf_clauses rescnf))

lens_rescnf_steps :: Lens' (ResCNF l) [ResStep l]
lens_rescnf_steps f rescnf = fmap (\rsteps -> ResCNF (rescnf_clauses rescnf) rsteps) (f (rescnf_steps rescnf))


-- l is the atom type
-- r is the constraint type generated when resolving
-- I don't really like this entirely, but mt is a Monad Transformer that's also a Monad Functor
class PreResLiteral l where
	-- resolvable works directly on the atoms, not on the literals, so that we can compare literals from the same clause for factorization.
	-- Thus, at this level we can only actually resolve two literals with exactly opposite signs.
	-- It is also an initial check. If false, it means they cannot be resolved. If true, it merely means a constraint can be generated, but that constraint may later on turn unsatisfiable.
	-- It assumes commutativity: if (resolvable a b) is true, then (resolvable b a) is true.	
	resolvable :: l -> l -> Bool

class (Monoid r, MonadTrans mt, MFunctor mt, forall n. Monad n => Monad (mt n), PreResLiteral l) => ResLiteral l r (mt :: (* -> *) -> * -> *) | l r -> mt where
	-- resolve works on two lists of atoms, the positive and the negative ones, and produces a constraint AND a function that modifies other atoms (the "unifier").
	resolve :: Monad m => [l] -> [l] -> mt m (r,l -> l)

data ResState l r = ResState {resst_cnf :: ResCNF l, resst_cstr :: r}

lens_resst_cnf :: Lens' (ResState l r) (ResCNF l)
lens_resst_cnf f resst = fmap (\rcnf -> ResState rcnf (resst_cstr resst)) (f (resst_cnf resst))

lens_resst_cstr :: Lens' (ResState l r) r
lens_resst_cstr f resst = fmap (\rr -> ResState (resst_cnf resst) rr) (f (resst_cstr resst))

-- The boolean indicates whether we are checking for literals in the same clause (True) or literals in different clauses (False)
literals_resolvable :: PreResLiteral l => Bool -> Literal l -> Literal l -> Bool
literals_resolvable True (PosLit l1) (PosLit l2) = resolvable l1 l2
literals_resolvable True (PosLit l1) (NegLit l2) = False
literals_resolvable True (NegLit l1) (PosLit l2) = False
literals_resolvable True (NegLit l1) (NegLit l2) = resolvable l1 l2
literals_resolvable False (PosLit l1) (PosLit l2) = False
literals_resolvable False (PosLit l1) (NegLit l2) = resolvable l1 l2
literals_resolvable False (NegLit l1) (PosLit l2) = resolvable l1 l2
literals_resolvable False (NegLit l1) (NegLit l2) = False


-- This is cool, but we are actually generating all combinations to later on undo them and then do them again later, so we just do not calculate maximals but instead all combinations that are compatible.
--generate_clause_maximals :: ResLiteral l r => [Literal l] -> [[Int]]
--generate_clause_maximals cl = Data.List.filter (\sl -> not (any (\bl -> ((length bl) > (length sl)) && (all (\e -> elem e bl) sl)) totals)) totals
--	where totals = generate_clause_maximals_rec cl (length cl) 0 []

generate_full_clause :: PreResLiteral l => [Literal l] -> ResClause l
generate_full_clause ls = ResClause ls (generate_clause_compatibles ls)

generate_clause_compatibles :: PreResLiteral l => [Literal l] -> [[Int]]
generate_clause_compatibles cl = Data.List.filter (not . Prelude.null) (generate_clause_compatibles_rec cl (length cl) 0 [])


-- The first Int is the length of the clause.
-- The second Int is the index we are currently checking of the list to see more compatibility.
-- The list of Ints is a set we have identified as compatible so far.
generate_clause_compatibles_rec :: PreResLiteral l => [Literal l] -> Int -> Int -> [Int] -> [[Int]]
generate_clause_compatibles_rec _ len idx r | idx >= len = [r]
generate_clause_compatibles_rec cl len idx r = concat (generate_clause_compatibles_rec cl len (idx+1) <$> (if compatible then [r,(idx:r)] else [r]))
	where		
		compatible = all (\pidx -> literals_resolvable True (cl !! idx) (cl !! pidx)) r

generate_crossclause_compatibles :: PreResLiteral l => ResCNF l -> Int -> Int -> [ResStep l]
generate_crossclause_compatibles cnf lcl rcl = concat (fmap (\lcomp -> fmap (\rcomp -> build_resstep cnf lcl lcomp rcl rcomp) (Data.List.filter (fcheck lcomp) (resclause_compatibles arcl))) (resclause_compatibles alcl))
	where
		alcl = (rescnf_clauses cnf) !! lcl;
		arcl = (rescnf_clauses cnf) !! rcl;
		lcomps = resclause_compatibles alcl;
		rcomps = resclause_compatibles arcl;
		fcheck = (\lcomp -> \rcomp -> posneg_compatibles cnf lcl lcomp rcl rcomp);

posneg_compatibles :: PreResLiteral l => ResCNF l -> Int -> [Int] -> Int -> [Int] -> Bool
posneg_compatibles cnf lcl lcomp rcl rcomp = all (\ll -> all (\rl -> literals_resolvable False ll rl) (((resclause_lits ((rescnf_clauses cnf) !! rcl)) !!) <$> rcomp)) (((resclause_lits ((rescnf_clauses cnf) !! lcl)) !!) <$> lcomp)

-- Assumes compatibility and one element, and checks only one element.
build_resstep :: ResCNF l -> Int -> [Int] -> Int -> [Int] -> ResStep l
build_resstep cnf lcl lidxs rcl ridxs = case ((resclause_lits ((rescnf_clauses cnf) !! lcl)) !! (head lidxs)) of {PosLit _ -> ResStep lcl lidxs rcl ridxs (rescnf_clauses cnf); NegLit _ -> ResStep rcl ridxs lcl lidxs (rescnf_clauses cnf)}

generate_rescnf :: PreResLiteral l => [[Literal l]] -> ResCNF l
generate_rescnf pcnf = ResCNF cls steps
	where
		cls = generate_full_clause <$> pcnf;
		tcnf = ResCNF cls [];
		steps = concat (fmap (\lcl -> concat (fmap (\rcl -> generate_crossclause_compatibles tcnf lcl rcl) (Data.List.filter (> lcl) [0..((length cls) - 1)]))) [0..((length cls) - 1)])

generate_resstate :: ResLiteral l r mt => [[Literal l]] -> ResState l r
generate_resstate pcnf = ResState (generate_rescnf pcnf) mempty

type ResMHeuristic l r mt = mt (StateT (ResState l r) (MHeuristic [Literal l] () (ResStep l)))

res_compute :: (ResLiteral l r mt, Heuristics h [Literal l] () (ResStep l) m) => h -> ResState l r -> ResMHeuristic l r mt a -> mt m a
res_compute h resst resmh = hoist (\iresmh -> m_heur_compute h (fst <$> runStateT iresmh resst)) resmh

res_addclause :: ResLiteral l r mt => [Literal l] -> ResMHeuristic l r mt Int
res_addclause cl = do
	{
		resst <- lift (get);

		let {rcl = generate_full_clause cl};
		
		let {ccnf = resst_cnf resst; ccls = rescnf_clauses ccnf; cncls = length ccls; rclidx = cncls};

		let {tcnf = lens_rescnf_clauses ..~ (++ [rcl]) $ ccnf};

		let {rsteps = concat (fmap (\pcl -> generate_crossclause_compatibles tcnf pcl rclidx) [0..(cncls -1)])};

		let {rcnf = lens_rescnf_steps ..~ (++ rsteps) $ tcnf};
		
		let {rresst = lens_resst_cnf .~ rcnf $ resst};

		lift (put rresst);

		(lift . lift) (m_heur_inform cl);

		return rclidx
	}

res_choosestep :: ResLiteral l r mt => ResMHeuristic l r mt (Maybe Int)
res_choosestep = do
	{
		resst <- lift (get);
		
		(lift . lift) (m_heur_choose () (rescnf_steps (resst_cnf resst)))
	}

-- We indicate the index of the step, rather than the step itself.
-- Return the index of the new clause
-- Note that the index of steps changes after this, so how we combine this and res_choosestep must be done with care!
-- Indices of literals and clauses does not change.
res_resolve :: ResLiteral l r mt => Int -> ResMHeuristic l r mt Int
res_resolve stepidx = do
	{
		resst <- lift (get);

		let {step = ((rescnf_steps . resst_cnf) resst) !! stepidx; posclidx = resstep_poscl step; poslitsidx = resstep_poslits step; negclidx = resstep_negcl step; neglitsidx = resstep_neglits step};
		let {cnf = resst_cnf resst; cls = rescnf_clauses cnf};
		let {poscl = cls !! posclidx; negcl = cls !! negclidx};
		let {poslits = ((resclause_lits poscl) !!) <$> poslitsidx; neglits = ((resclause_lits negcl) !!) <$> neglitsidx};
		let {posatoms = atom_from_literal <$> poslits; negatoms = atom_from_literal <$> neglits};

		-- Resolve (over the m Monad)
		(newcstr,unif) <- resolve posatoms negatoms;

		-- Update the constraint
		let {resst2 = lens_resst_cstr ..~ (<> newcstr) $ resst};
		
		-- Do not forget to remove the step from the list of possible steps
		let {resst3 = (lens_resst_cnf . lens_rescnf_steps) ..~ (removeAt stepidx) $ resst2};
		lift (put resst3);

		-- Generate the resolvent
		-- First, take the union of the positive and negative clauses, except the resolved literals.
		let {remposlits = ((resclause_lits poscl) !!) <$> (Data.List.filter (not . (\idx -> elem idx poslitsidx)) [0..((length (resclause_lits poscl))-1)]); remneglits = ((resclause_lits negcl) !!) <$> (Data.List.filter (not . (\idx -> elem idx neglitsidx)) [0..((length (resclause_lits negcl))-1)])};
		let {remlits = remposlits ++ remneglits};
		-- Then, apply the unifier to them.
		let {uremlits = (unif <$>) <$> remlits};		

		-- Finally, formally add the resolvent clause to the cnf.
		res_addclause uremlits
	}

-- Returns Nothing if the empty clause cannot be found.
res_resolveall :: ResLiteral l r mt => ResMHeuristic l r mt (Maybe r)
res_resolveall = do
	{
		resst <- lift (get);

		-- Check if there is an empty clause. If there is, we are finished.
		let {cls = (rescnf_clauses . resst_cnf) resst; lss = resclause_lits <$> cls};
		if (any Prelude.null lss) then (return (Just (resst_cstr resst))) else do
		{
			mb_step <- res_choosestep;
			case mb_step of
			{
				Nothing -> return Nothing;
				Just stepidx -> do
				{
					res_resolve stepidx;
					res_resolveall;
				}
			}
		}
	}

res_computeresolve :: (ResLiteral l r mt, Heuristics h [Literal l] () (ResStep l) m) => h -> [[Literal l]] -> mt m (Maybe r)
res_computeresolve h cnf = res_compute h (generate_resstate cnf) res_resolveall
