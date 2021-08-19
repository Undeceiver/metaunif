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
{-# LANGUAGE QuantifiedConstraints #-}
module SOResolution where

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
import ESUnification
import Heuristics
import Resolution

type ResConstraintsU uv = (Variable uv, Variabilizable uv)
type ResConstraintsALL a t ss mpd pd fn v pmv fmv uv = (ESMGUConstraintsALL a t ss mpd pd fn v pmv fmv uv, ResConstraintsU uv)

instance ResConstraintsALL a t ss mpd pd fn v pmv fmv uv => PreResLiteral (AtomDependant a t ss mpd pd fn v pmv fmv uv) where
	--resolvable :: AtomDependant a t ss mpd pd fn v pmv fmv uv -> AtomDependant a t ss mpd pd fn v pmv fmv uv -> Bool
	resolvable lad rad = isJust (resolvable_nounif la ra) where (_,la) = decompose_ad lad; (_,ra) = decompose_ad rad
	--fullresolvable lads rads = gtrace False ("LADS: " ++ (show lads) ++ "RADS: " ++ (show rads) ++ "\n") (if ((any isNothing mb_lahs) || (any isNothing mb_rahs)) then (gtrace False "FALSE\n" False) else (gtrace False ("FINAL RES: " ++ (show finalres) ++ "\n") finalres)) where mb_lahs = (resolvable_geth . snd . decompose_ad) <$> lads; mb_rahs = (resolvable_geth . snd . decompose_ad) <$> rads; lahs = fromJust <$> mb_lahs; rahs = fromJust <$> mb_rahs; finalres = isJust (Prelude.foldr resolvable_nounif_max (Just (Left ())) (lahs ++ rahs))
	fullresolvable lads rads = True


resolvable_geth :: ESMGUConstraintsAMpdSs a t ss mpd pd fn v pmv fmv => CombSOAtom a t ss mpd pd fn v pmv fmv -> Maybe (SOAtom pd fn pmv fmv)
resolvable_geth (FSOAtom _) = Nothing
resolvable_geth (NSOAtom nsoa) = Just h
	where
		nnsoa = normalize nsoa;
		(h,_) = unbuild_term (fromSOMetawrapA nsoa)

-- The unifiers do not affect the heads of atoms, and we are only looking at the heads of atoms to check unifiability, so this is really about looking under the unifier variables.
resolvable_nounif :: ESMGUConstraintsAMpdSs a t ss mpd pd fn v pmv fmv => CombSOAtom a t ss mpd pd fn v pmv fmv -> CombSOAtom a t ss mpd pd fn v pmv fmv -> Maybe (Either () pd)
resolvable_nounif (FSOAtom _) (NSOAtom _) = Nothing
resolvable_nounif (NSOAtom _) (FSOAtom _) = Nothing
-- "First second-order atoms" are only unifiable if they have the same head. That's how far we check here.
resolvable_nounif (FSOAtom (FirstSOAAtom lfsoa)) (FSOAtom (FirstSOAAtom rfsoa)) | lh == rh = Just (Left ()) where (lh,_) = unbuild_term lfsoa; (rh,_) = unbuild_term rfsoa
resolvable_nounif (FSOAtom (FirstSOAAtom lfsoa)) (FSOAtom (FirstSOAAtom rfsoa)) = Nothing
resolvable_nounif (NSOAtom lnsoa) (NSOAtom rnsoa) = resolvable_nounif_max lh (resolvable_nounif_max rh (Just (Left ())))
	where
		nlnsoa = normalize lnsoa;
		nrnsoa = normalize rnsoa;
		(lh,_) = unbuild_term (fromSOMetawrapA nlnsoa);
		(rh,_) = unbuild_term (fromSOMetawrapA nrnsoa);

-- For actual second-order atoms, we check the head of the normalized atoms and compare them.
-- Variables are unifiable with anything.
-- Projections cannot appear in atoms.
-- Constants are only unifiable with themselves.
-- Compositions cannot appear on normalized terms.
-- So if it's not a variable, it needs to be exactly the same.
resolvable_nounif_max :: ESMGUConstraintsPdFnPmvFmv pd fn pmv fmv => SOAtom pd fn pmv fmv -> Maybe (Either () pd) -> Maybe (Either () pd)
resolvable_nounif_max h prev = case prev of
				{
					Nothing -> Nothing;
					Just (Left ()) -> case h of
					{
						UVar _ -> Just (Left ());
						UTerm (SOP (ConstF pd)) -> Just (Right pd);
						_ -> error "resolvable_nounif_max: Unexpected normalized atom does not have variable or constant as head!"
					};
					Just (Right pdprev) -> case h of
					{
						UVar _ -> Just (Right pdprev);
						UTerm (SOP (ConstF pd)) | pdprev == pd -> Just (Right pdprev);
						UTerm (SOP (ConstF pd)) -> Nothing;
						_ -> error "resolvable_nounif_max: Unexpected normalized atom does not have variable or constant as head!"
					}
				}


instance ResConstraintsALL a t ss mpd pd fn v pmv fmv uv => ResLiteral (AtomDependant a t ss mpd pd fn v pmv fmv uv) (UnifSystem a t ss mpd pd fn v pmv fmv uv) (StateT uv) where
	--resolve :: Monad m => [AtomDependant a t ss mpd pd fn v pmv fmv uv] -> [AtomDependant a t ss mpd pd fn v pmv fmv uv] -> StateT uv m (UnifSystem a t ss mpd pd fn v pmv fmv uv,AtomDependant a t ss mpd pd fn v pmv fmv uv -> AtomDependant a t ss mpd pd fn v pmv fmv uv)
	resolve poslits neglits = do
		{
			uv <- get;
			
			let {(mlit:rposlits) = poslits};

			let {r = fmap (\lit -> AtomUnif (ADUnif uv lit) (ADUnif uv mlit)) (rposlits++neglits)};

			let {u = ADUnif uv};

			let {nuv = next_uv uv};
			put nuv;

			return (r,u)
		}

next_uv :: ResConstraintsU uv => uv -> uv
next_uv uv = update_var (+1) uv

data SOResGreedyFactorH a t ss mpd pd fn v pmv fmv uv = SOResGreedyFactorH

instance HeuristicsI (SOResGreedyFactorH a t ss mpd pd fn v pmv fmv uv) [Literal (AtomDependant a t ss mpd pd fn v pmv fmv uv)] Computation where
	heur_inform h _ = return h

instance HeuristicsC (SOResGreedyFactorH a t ss mpd pd fn v pmv fmv uv) () (ResStep (AtomDependant a t ss mpd pd fn v pmv fmv uv) (UnifSystem a t ss mpd pd fn v pmv fmv uv)) Computation where
	heur_choose h _ steps = if (Prelude.null wstepidxs_ord) then (return (Nothing,h)) else (ecomp (uns_enum_from_list (((,h) . Just) <$> wstepidxs_ord)))
		where
			wsteps = build_soresgreedyfactorstep <$> steps;
			wstepidxs = [0..((length wsteps) - 1)];
			wstepidxs_ord = sortOn (wsteps !!) wstepidxs;

-- We look for the step which leaves the smallest possible clause.
greedyfactor_step_measure :: ResStep (AtomDependant a t ss mpd pd fn v pmv fmv uv) (UnifSystem a t ss mpd pd fn v pmv fmv uv) -> Int
greedyfactor_step_measure step = poscl_len - poscl_rem + negcl_len - negcl_rem where poscl_len = length (resclause_lits ((resstep_clauses step) !! (resstep_poscl step))); negcl_len = length (resclause_lits ((resstep_clauses step) !! (resstep_negcl step))); poscl_rem = length (resstep_poslits step); negcl_rem = length (resstep_neglits step)

data SOResGreedyFactorStep a t ss mpd pd fn v pmv fmv uv = SOResGreedyFactorStep {fromSOResGreedyFactorStep :: ResStep (AtomDependant a t ss mpd pd fn v pmv fmv uv) (UnifSystem a t ss mpd pd fn v pmv fmv uv), mSOResGreedyFactorStep :: Int}

build_soresgreedyfactorstep :: ResStep (AtomDependant a t ss mpd pd fn v pmv fmv uv) (UnifSystem a t ss mpd pd fn v pmv fmv uv) -> SOResGreedyFactorStep a t ss mpd pd fn v pmv fmv uv
build_soresgreedyfactorstep step = SOResGreedyFactorStep step (greedyfactor_step_measure step)

instance Eq (SOResGreedyFactorStep a t ss mpd pd fn v pmv fmv uv) where
	s1 == s2 = (mSOResGreedyFactorStep s1) == (mSOResGreedyFactorStep s2)

instance Ord (SOResGreedyFactorStep a t ss mpd pd fn v pmv fmv uv) where
	s1 <= s2 = (mSOResGreedyFactorStep s1) <= (mSOResGreedyFactorStep s2)

instance Heuristics (SOResGreedyFactorH a t ss mpd pd fn v pmv fmv uv) [Literal (AtomDependant a t ss mpd pd fn v pmv fmv uv)] () (ResStep (AtomDependant a t ss mpd pd fn v pmv fmv uv) (UnifSystem a t ss mpd pd fn v pmv fmv uv)) Computation where

soresolve_to_constraints :: forall a t ss mpd pd fn v pmv fmv uv. ResConstraintsALL a t ss mpd pd fn v pmv fmv uv => SOSignature mpd pd fn v pmv fmv -> [[Literal (CombSOAtom a t ss mpd pd fn v pmv fmv)]] -> Computation (Maybe ([UnifEquation a t ss mpd pd fn v pmv fmv uv],[ResProofStep (AtomDependant a t ss mpd pd fn v pmv fmv uv) [UnifEquation a t ss mpd pd fn v pmv fmv uv]]))
soresolve_to_constraints sig cnf = result
	where
		f1 = (ADDirect <$>);
		f2 = (f1 <$>);
		f3 = (f2 <$>);
		ucnf = f3 cnf;
		h = SOResGreedyFactorH :: SOResGreedyFactorH a t ss mpd pd fn v pmv fmv uv;
		resolved = res_computeresolve h ucnf;
		runstated = runStateT resolved (from_var (IntVar 0));
		result = fst <$> runstated

soresolve_to_constraints_only :: ResConstraintsALL a t ss mpd pd fn v pmv fmv uv => SOSignature mpd pd fn v pmv fmv -> [[Literal (CombSOAtom a t ss mpd pd fn v pmv fmv)]] -> Computation (Maybe [UnifEquation a t ss mpd pd fn v pmv fmv uv])
soresolve_to_constraints_only sig cnf = (fst <$>) <$> soresolve_to_constraints sig cnf

-- This function does not provide any level of normalization on the resulting graph
soresolve_to_dgraph :: ResConstraintsALL a t ss mpd pd fn v pmv fmv uv => SOSignature mpd pd fn v pmv fmv -> [[Literal (CombSOAtom a t ss mpd pd fn v pmv fmv)]] -> Computation (Maybe (RESUnifVDGraph t mpd pd fn v pmv fmv uv))
--soresolve_to_dgraph sig cnf = ((\usys -> doRESUnifVDGraph sig (dgraph_from_usys sig usys)) <$>) <$> (soresolve_to_constraints_only sig cnf)
soresolve_to_dgraph sig cnf = ((\usys -> doRESUnifVDGraph sig (dgraph_from_usys sig usys)) <$>) <$> (do
					{
						mb_eqs <- soresolve_to_constraints_only sig cnf;
						gtraceM True (show mb_eqs);
						return mb_eqs
					})

soresolve_to_dgraph_filter :: ResConstraintsALL a t ss mpd pd fn v pmv fmv uv => SOSignature mpd pd fn v pmv fmv -> [[Literal (CombSOAtom a t ss mpd pd fn v pmv fmv)]] -> Computation (RESUnifVDGraph t mpd pd fn v pmv fmv uv)
soresolve_to_dgraph_filter sig cnf = algalgfilter (soresolve_to_dgraph sig cnf)

soresolve_to_dgraph_nub :: (ResConstraintsALL a t ss mpd pd fn v pmv fmv uv, ExecOrder xt) => xt -> SOSignature mpd pd fn v pmv fmv -> [[Literal (CombSOAtom a t ss mpd pd fn v pmv fmv)]] -> Computation (Maybe (RESUnifVDGraph t mpd pd fn v pmv fmv uv))
--soresolve_to_dgraph sig cnf = ((\usys -> doRESUnifVDGraph sig (dgraph_from_usys sig usys)) <$>) <$> (soresolve_to_constraints_only sig cnf)
soresolve_to_dgraph_nub x sig cnf = ((\usys -> doRESUnifVDGraph sig (dgraph_from_usys sig usys)) <$>) <$> (do
					{
						mb_eqs <- fenum_alg x enub (soresolve_to_constraints_only sig cnf);
						gtraceM True (show mb_eqs);
						return mb_eqs
					})

soresolve_to_dgraph_filter_nub :: (ResConstraintsALL a t ss mpd pd fn v pmv fmv uv, ExecOrder xt) => xt -> SOSignature mpd pd fn v pmv fmv -> [[Literal (CombSOAtom a t ss mpd pd fn v pmv fmv)]] -> Computation (RESUnifVDGraph t mpd pd fn v pmv fmv uv)
soresolve_to_dgraph_filter_nub x sig cnf = algalgfilter (soresolve_to_dgraph_nub x sig cnf)

