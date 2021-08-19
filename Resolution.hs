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
import Data.HashMap
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
-- We have a constraint on each clause so that we only build the final constraint from the clauses that we needed to use.
data ResClause l r = ResClause {resclause_lits :: [Literal l], resclause_compatibles :: [[Int]], resclause_cstr :: r, resclause_proof :: [ResProofStep l r]}
-- rescnf_steps are all the possible resolutions that we can carry on this CNF.
-- This data structure has the following rationale:
--	- Clauses are not modified once they are added to the CNF. This is why we do not need lenses for clauses.
--	- Thus, the sets of potentially unifiable literals in each clause do not change.
--	- Possible resolutions to carry are added each time a clause is added, by comparing this new clause to the existing clauses, and using their respective compatible sets.
--	- Possible resolutions are only removed when they are actually carried out: When a resolution is taken, we remove it so that we do not do it again. We do not remove any others when doing this.
data ResStep l r = ResStep {resstep_poscl :: Int, resstep_poslits :: [Int], resstep_negcl :: Int, resstep_neglits :: [Int], resstep_clauses :: [ResClause l r]}
data ResCNF l r = ResCNF {rescnf_clauses :: [ResClause l r], rescnf_steps :: [ResStep l r]}

lens_rescnf_clauses :: Lens' (ResCNF l r) [ResClause l r]
lens_rescnf_clauses f rescnf = fmap (\rclauses -> ResCNF rclauses (rescnf_steps rescnf)) (f (rescnf_clauses rescnf))

lens_rescnf_steps :: Lens' (ResCNF l r) [ResStep l r]
lens_rescnf_steps f rescnf = fmap (\rsteps -> ResCNF (rescnf_clauses rescnf) rsteps) (f (rescnf_steps rescnf))


-- l is the atom type
-- r is the constraint type generated when resolving
class PreResLiteral l where
	-- resolvable works directly on the atoms, not on the literals, so that we can compare literals from the same clause for factorization.
	-- Thus, at this level we can only actually resolve two literals with exactly opposite signs.
	-- It is also an initial check. If false, it means they cannot be resolved. If true, it merely means a constraint can be generated, but that constraint may later on turn unsatisfiable.
	-- It assumes commutativity: if (resolvable a b) is true, then (resolvable b a) is true.	
	resolvable :: l -> l -> Bool
	-- Full resolvable is used right before resolving to avoid going down useless paths. An acceptable (but slow) implementation is to just return True.
	fullresolvable :: [l] -> [l] -> Bool

-- I don't really like this entirely, but mt is a Monad Transformer that's also a Monad Functor
class (Monoid r, MonadTrans mt, MFunctor mt, forall n. Monad n => Monad (mt n), PreResLiteral l) => ResLiteral l r (mt :: (* -> *) -> * -> *) | l r -> mt where
	-- resolve works on two lists of atoms, the positive and the negative ones, and produces a constraint AND a function that modifies other atoms (the "unifier").
	resolve :: Monad m => [l] -> [l] -> mt m (r,l -> l)

data ResProofStep l r = ResProofStep {respstep_poscl :: [Literal l], respstep_poslits :: [Literal l], respstep_negcl :: [Literal l], respstep_neglits :: [Literal l], respstep_cnf :: [[Literal l]], respstep_resolvent :: [Literal l], respstep_cstr :: r}

build_proofstep :: ResCNF l r -> ResStep l r -> r -> [Literal l] -> ResProofStep l r
build_proofstep cnf step cstr resolvent = ResProofStep poscl poslits negcl neglits rcnf resolvent cstr
	where
		poscl = resclause_lits ((rescnf_clauses cnf) !! (resstep_poscl step));
		negcl = resclause_lits ((rescnf_clauses cnf) !! (resstep_negcl step));
		poslits = (poscl !!) <$> (resstep_poslits step);
		neglits = (negcl !!) <$> (resstep_neglits step);
		rcnf = resclause_lits <$> (rescnf_clauses cnf);

instance (Show l, Show r) => Show (ResProofStep l r) where
	show respstep = "Positive literals " ++ (show (respstep_poslits respstep)) ++ " from clause " ++ (show (respstep_poscl respstep)) ++
		"\nwere resolved with" ++
		"\nNegative literals " ++ (show (respstep_neglits respstep)) ++ " from clause " ++ (show (respstep_negcl respstep)) ++
		"\nfrom CNF " ++ (show (respstep_cnf respstep)) ++
		"\nto produce resolvent " ++ (show (respstep_resolvent respstep)) ++
		"\nwith constraints " ++ (show (respstep_cstr respstep)) ++ "\n\n"

show_resproof :: (Show l, Show r) => [ResProofStep l r] -> String
show_resproof [] = "\nEnd proof\n"
show_resproof (s:ss) = (show s) ++ "-----\n\n" ++ (show_resproof ss)

-- This used to have more fields, but we moved them to the clauses. We could remove it, but we may add back some things later on so...
data ResState l r = ResState {resst_cnf :: ResCNF l r}

lens_resst_cnf :: Lens' (ResState l r) (ResCNF l r)
lens_resst_cnf f resst = fmap (\rcnf -> ResState rcnf) (f (resst_cnf resst))

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

generate_full_clause :: PreResLiteral l => r -> [ResProofStep l r] -> [Literal l] -> ResClause l r
generate_full_clause cstr proof ls = ResClause ls (generate_clause_compatibles ls) cstr proof

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

generate_crossclause_compatibles :: PreResLiteral l => ResCNF l r -> Int -> Int -> [ResStep l r]
generate_crossclause_compatibles cnf lcl rcl = concat (fmap (\lcomp -> fmap (\rcomp -> build_resstep cnf lcl lcomp rcl rcomp) (Data.List.filter (fcheck lcomp) (resclause_compatibles arcl))) (resclause_compatibles alcl))
	where
		alcl = (rescnf_clauses cnf) !! lcl;
		arcl = (rescnf_clauses cnf) !! rcl;
		lcomps = resclause_compatibles alcl;
		rcomps = resclause_compatibles arcl;
		fcheck = (\lcomp -> \rcomp -> posneg_compatibles cnf lcl lcomp rcl rcomp);

posneg_compatibles :: PreResLiteral l => ResCNF l r -> Int -> [Int] -> Int -> [Int] -> Bool
posneg_compatibles cnf lcl lcomp rcl rcomp = all (\ll -> all (\rl -> literals_resolvable False ll rl) (((resclause_lits ((rescnf_clauses cnf) !! rcl)) !!) <$> rcomp)) (((resclause_lits ((rescnf_clauses cnf) !! lcl)) !!) <$> lcomp)

-- Assumes compatibility and one element, and checks only one element.
build_resstep :: ResCNF l r -> Int -> [Int] -> Int -> [Int] -> ResStep l r
build_resstep cnf lcl lidxs rcl ridxs = case ((resclause_lits ((rescnf_clauses cnf) !! lcl)) !! (head lidxs)) of {PosLit _ -> ResStep lcl lidxs rcl ridxs (rescnf_clauses cnf); NegLit _ -> ResStep rcl ridxs lcl lidxs (rescnf_clauses cnf)}

generate_rescnf :: ResLiteral l r mt => [[Literal l]] -> ResCNF l r
generate_rescnf pcnf = ResCNF cls steps
	where
		cls = generate_full_clause mempty [] <$> pcnf;
		tcnf = ResCNF cls [];
		steps = concat (fmap (\lcl -> concat (fmap (\rcl -> generate_crossclause_compatibles tcnf lcl rcl) (Data.List.filter (> lcl) [0..((length cls) - 1)]))) [0..((length cls) - 1)])

generate_resstate :: ResLiteral l r mt => [[Literal l]] -> ResState l r
generate_resstate pcnf = ResState (generate_rescnf pcnf)

type ResMHeuristic l r mt = mt (StateT (ResState l r) (MHeuristic [Literal l] () (ResStep l r)))

res_compute :: (ResLiteral l r mt, Heuristics h [Literal l] () (ResStep l r) m) => h -> ResState l r -> ResMHeuristic l r mt a -> mt m a
res_compute h resst resmh = hoist (\iresmh -> m_heur_compute h (fst <$> runStateT iresmh resst)) resmh

res_addclause :: ResLiteral l r mt => r -> [ResProofStep l r] -> [Literal l] -> ResMHeuristic l r mt Int
res_addclause cstr proof cl = do
	{
		resst <- lift (get);

		let {rcl = generate_full_clause cstr proof cl};
		
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
		
		mb_step <- (lift . lift) (m_heur_choose () (rescnf_steps (resst_cnf resst)));

--		return mb_step

		gtraceM False "MB STEP";
		gtraceM False (show mb_step);
		
		case mb_step of
		{
			Nothing -> return Nothing;
			Just stepidx -> do
			{
				let {step = ((rescnf_steps . resst_cnf) resst) !! stepidx; posclidx = resstep_poscl step; poslitsidx = resstep_poslits step; negclidx = resstep_negcl step; neglitsidx = resstep_neglits step};
				let {cnf = resst_cnf resst; cls = rescnf_clauses cnf};
				let {poscl = cls !! posclidx; negcl = cls !! negclidx};
				let {poslits = ((resclause_lits poscl) !!) <$> poslitsidx; neglits = ((resclause_lits negcl) !!) <$> neglitsidx};
				let {posatoms = atom_from_literal <$> poslits; negatoms = atom_from_literal <$> neglits};

				if (fullresolvable posatoms negatoms) then (gtrace False "YES!" (return mb_step))
				else do
				{
					-- Remove this step, since it's no good.
					let {resst2 = (lens_resst_cnf . lens_rescnf_steps) ..~ (removeAt stepidx) $ resst};
					lift (put resst2);

					gtraceM False "NO!";

					-- Roll again
					res_choosestep;
				}
			}
		}


	}		

		

-- We indicate the index of the step, rather than the step itself.
-- Return the resulting constraint
-- Note that the index of steps changes after this, so how we combine this and res_choosestep must be done with care!
-- Indices of literals and clauses does not change.
res_resolve :: ResLiteral l r mt => Int -> ResMHeuristic l r mt r
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

		-- Generate the resolvent
		-- First, take the union of the positive and negative clauses, except the resolved literals.
		let {remposlits = ((resclause_lits poscl) !!) <$> (Data.List.filter (not . (\idx -> elem idx poslitsidx)) [0..((length (resclause_lits poscl))-1)]); remneglits = ((resclause_lits negcl) !!) <$> (Data.List.filter (not . (\idx -> elem idx neglitsidx)) [0..((length (resclause_lits negcl))-1)])};
		let {remlits = remposlits ++ remneglits};
		-- Then, apply the unifier to them.
		let {uremlits = (unif <$>) <$> remlits};

		-- Update the proof
		let {proofstep = build_proofstep cnf step newcstr uremlits};
		let {resproof = (resclause_proof poscl) ++ (resclause_proof negcl) ++ [proofstep]};
		
		-- Update the constraint
		let {rescstr = (resclause_cstr poscl) <> (resclause_cstr negcl) <> newcstr};		
		
		-- Do not forget to remove the step from the list of possible steps
		let {resst2 = (lens_resst_cnf . lens_rescnf_steps) ..~ (removeAt stepidx) $ resst};
		lift (put resst2);
		
		-- Finally, formally add the resolvent clause to the cnf.
		res_addclause rescstr resproof uremlits;

		return rescstr
	}

-- Returns Nothing if the empty clause cannot be found.
res_resolveall :: ResLiteral l r mt => ResMHeuristic l r mt (Maybe (r,[ResProofStep l r]))
res_resolveall = do
	{
		resst <- lift (get);

		-- Check if there is an empty clause. If there is, we are finished.
		let {cls = (rescnf_clauses . resst_cnf) resst; rcls = Prelude.filter (\cl -> Prelude.null (resclause_lits cl)) cls};
		case rcls of
		{			
			(cl:_) -> gtrace True "Found an empty clause!" (return (Just (resclause_cstr cl,resclause_proof cl)));
			[] -> do
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
	}

res_computeresolve :: (ResLiteral l r mt, Heuristics h [Literal l] () (ResStep l r) m) => h -> [[Literal l]] -> mt m (Maybe (r,[ResProofStep l r]))
res_computeresolve h cnf = res_compute h (generate_resstate cnf) res_resolveall
