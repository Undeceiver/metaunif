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
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
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
import ESUnification
import EnumProc
import Resolution
import SOResolution
import Control.Monad.State
import Control.Monad.ST
import Data.Functor.Fixedpoint
import Data.Bifunctor

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
type BaseCESQuery (a :: * -> * -> *) (t :: * -> * -> *) mpd pd fn v pmv fmv = FullLogicQuery (SOSignature mpd pd fn v pmv fmv) (CNF a t mpd pd fn v pmv fmv) (SOMetawrapA a t pd fn v pmv fmv)
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

lambdacnf_to_gsoa :: LambdaCNF (GroundSOA pd fn) -> GroundSOA pd fn
lambdacnf_to_gsoa (LambdaCNF [LambdaClause [PosLit l]]) = l
lambdacnf_to_gsoa _ = error "lambdacnf_to_gsoa: LambdaCNFs are currently not supported in solutions to systems"

-- It is important to explain how this is to be understood.
-- For exact graph instantiations, the instantiations are those encompassed by the indicated graph.
-- For minmax graph instantiations, the semantics are as follows:
--	- All the instantiations of MaxGraphInst are instantiations of the minmax.
--	- If the combination of MinGraphInst and MinCondGraphInst yields any results within a global constant boundary, then there's no more results to be presented.
--	- If the combination of MinGraphinst and MinCondGraphInst does not yield results within a global constant boundary, then all the results of MinGraphInst are results of the minmax.
--	- Conceptually, this is to be understood as: All the results of MinGraphInst that are not results of MinCondGraphInst, except we do the check globally rather than individually on each result.
--	- Note that for checkImplicit, we do actually have the correct semantics where we check if the element is part of MinGraphInst but not of MinCondGraphInst.
data ImplicitInstantiationV pd fn pmv fmv = forall t mpd v uv. ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ExactGraphInst {fromExactGraphInst :: RESUnifVDGraph t mpd pd fn v pmv fmv uv} | forall t mpd v uv. ESMGUConstraintsUPmv t pd fn v pmv fmv uv => MinMaxGraphInst {fromMinGraphInst :: RESUnifVDGraph t mpd pd fn v pmv fmv uv, fromMinCondGraphInst :: RESUnifVDGraph t mpd pd fn v pmv fmv uv, fromMaxGraphInst :: RESUnifVDGraph t mpd pd fn v pmv fmv uv}

-- These are used as global constants for the algorithm. Ideally, this would be either an argument or a monad-like thing, but we are just going to skip that at this point.
implicitInst_mincond_depth :: Int
implicitInst_mincond_depth = 5000

implicitInst_tounifsol :: (Ord pmv, Ord fmv) => (CESQVar pmv fmv := CESQSol pd fn) -> UnifSysSolution pd fn pmv fmv
implicitInst_tounifsol m = UnifSysSolution recf recp where (recf, recp) = implicitInst_tounifsol_rec (toList m)

-- Right now, we do not have the ability to use LambdaCNFs for this at all: we assume they are one positive literal and nothing else.
implicitInst_tounifsol_rec :: (Ord pmv, Ord fmv) => [(CESQVar pmv fmv, CESQSol pd fn)] -> (fmv := GroundSOT fn, pmv := GroundSOA pd fn)
implicitInst_tounifsol_rec [] = (Data.Map.Strict.empty, Data.Map.Strict.empty)
implicitInst_tounifsol_rec ((CESQVar (Left pmv), CESQSol (Left (LambdaCNF [LambdaClause [PosLit soa]]))):sols) = (recf, Data.Map.Strict.insert pmv soa recp) where (recf,recp) = implicitInst_tounifsol_rec sols
implicitInst_tounifsol_rec ((CESQVar (Left pmv), CESQSol (Left _)):sols) = error "implicitInst_tounifsol_rec: LambdaCNFs are currently not supported in solutions to systems"
implicitInst_tounifsol_rec ((CESQVar (Right fmv), CESQSol (Right sot)):sols) = (Data.Map.Strict.insert fmv sot recf, recp) where (recf,recp) = implicitInst_tounifsol_rec sols
implicitInst_tounif_sol_rec _ = error "Found an association which does not match variable types in the CESQ solution"

implicitInst_fromunifsol :: (Ord pmv, Ord fmv) => UnifSysSolution pd fn pmv fmv -> (CESQVar pmv fmv := CESQSol pd fn)
implicitInst_fromunifsol (UnifSysSolution fsol psol) = Data.List.foldr (\(fk,fv) -> Data.Map.Strict.insert (CESQVar (Right fk)) (CESQSol (Right fv))) (Data.List.foldr (\(pk,pv) -> Data.Map.Strict.insert (CESQVar (Left pk)) (CESQSol (Left (LambdaCNF [LambdaClause [PosLit pv]])))) Data.Map.Strict.empty (toList psol)) (toList fsol)

instance Implicit (ImplicitInstantiationV pd fn pmv fmv) (CESQVar pmv fmv := CESQSol pd fn) where
	checkImplicit (ExactGraphInst inst) cesqsol = checkImplicit inst usol where usol = implicitInst_tounifsol cesqsol
	checkImplicit (MinMaxGraphInst mininst mincondinst maxinst) cesqsol = (checkImplicit maxinst usol) >>=| ((checkImplicit mininst usol) >>=& (not <$> (checkImplicit mincondinst usol))) where usol = implicitInst_tounifsol cesqsol
	enumImplicit (ExactGraphInst inst) = implicitInst_fromunifsol <$> (enumImplicit inst)
	-- To implement this, we need to implement the functionality of merging two dependency graphs. This needs to be done "manually".
	-- Pick all nodes, add them to the new graph (with all their elements), then add all the edges, then add all the vertical edges.
	-- Should test this separately.
	enumImplicit (MinMaxGraphInst mininst mincondinst maxinst) = if mergedtest then resmax else (resmax .+. resmin)
		where
			resmax = implicitInst_fromunifsol <$> (enumImplicit maxinst);
			mergedmax = mergeRESUnifVDGraph mininst mincondinst;
			-- We use diagonalization here. This is an arbitrary choice, but one that works for this particular purpose absolutely fine.
			mergedtest = Prelude.null (get_nstep implicitInst_mincond_depth ((enumImplicit mergedmax) \$ ()));
			resmin = implicitInst_fromunifsol <$> (enumImplicit mininst);

data ImplicitInstantiation pd fn pmv fmv = ImplicitInstantiation {getImplicitInstantiationV :: ImplicitInstantiationV pd fn pmv fmv, getImplicitInstantiationSel :: [CESQVar pmv fmv |<- CESQSol pd fn]}

instance Implicit (ImplicitInstantiation pd fn pmv fmv) (CESQVar pmv fmv =<- CESQSol pd fn) where
	-- For checking, it's enough to just check the solution directly, ignoring the select clause. I mean, we could verify that the solution only contains variables in the select clause, but this is kind of pointless. The point is, if it does, then the checkImplicit underneath will only check the variables in the cesqsol variable, by construction.
	checkImplicit (ImplicitInstantiation impv seli) (QResultSet sele cesqsol) = checkImplicit impv cesqsol
	enumImplicit (ImplicitInstantiation impv sel) = (QResultSet sel) <$> (enumImplicit impv)

cesq_resolution_execorder :: DFS
cesq_resolution_execorder = DFS

-- This class represents something that, once a unifier variable type is specified, has an instance of Queriable.
class QueriableWithUV q v t r s uv | q v t -> r s where
	runBaseQWithUV :: Erase uv -> t -> [v |<- r] -> q -> AnswerSet s (v =<- r)

instance forall a t mpd pd fn v pmv fmv uv. ResConstraintsALL a t LambdaCNF mpd pd fn v pmv fmv uv => QueriableWithUV (BaseCESQuery a t mpd pd fn v pmv fmv) (CESQVar pmv fmv) (CNF a t mpd pd fn v pmv fmv) (CESQSol pd fn) (ImplicitInstantiation pd fn pmv fmv) uv where
	runBaseQWithUV _ tcnf sel (FLogicQuery sig (Entails ecnf)) = ExplicitAS einsts
		where
			compresuvdgs = soresolve_to_dgraph_filter sig (tcnf ++ ecnf) :: Computation (RESUnifVDGraph t mpd pd fn v pmv fmv uv);
			eresuvdgs = runcomp cesq_resolution_execorder compresuvdgs;
			finsts = (\resuvdg -> ImplicitAS (ImplicitInstantiation (ExactGraphInst resuvdg) sel));
			einsts = finsts <$> eresuvdgs;
	runBaseQWithUV _ tcnf sel (FLogicQuery sig (Satisfies ecnf satcnf)) = ExplicitAS einsts
		where
			compresuvdgs_ecnf = soresolve_to_dgraph_filter sig (tcnf ++ ecnf) :: Computation (RESUnifVDGraph t mpd pd fn v pmv fmv uv);
			compresuvdgs_mincnf = soresolve_to_dgraph_filter sig tcnf :: Computation (RESUnifVDGraph t mpd pd fn v pmv fmv uv);
			compresuvdgs_mincondcnf = soresolve_to_dgraph_filter sig (tcnf ++ satcnf) :: Computation (RESUnifVDGraph t mpd pd fn v pmv fmv uv);
			eresuvdgs_ecnf = runcomp cesq_resolution_execorder compresuvdgs_ecnf;
			eresuvdgs_mincnf = runcomp cesq_resolution_execorder compresuvdgs_mincnf;
			eresuvdgs_mincondcnf = runcomp cesq_resolution_execorder compresuvdgs_mincondcnf;
			einsts = do
				{
					resuvdgs_ecnf <- eresuvdgs_ecnf;
					resuvdgs_mincnf <- eresuvdgs_mincnf;
					resuvdgs_mincondcnf <- eresuvdgs_mincondcnf;

					return (ImplicitAS (ImplicitInstantiation (MinMaxGraphInst resuvdgs_mincnf resuvdgs_mincondcnf resuvdgs_ecnf) sel))
				};
	runBaseQWithUV _ tcnf sel (FLogicQuery sig (Equals a1 a2)) = ExplicitAS einsts
		where
			a1w = ADDirect (NSOAtom a1);
			a2w = ADDirect (NSOAtom a2);
			eq = AtomUnif a1w a2w :: UnifEquation a t LambdaCNF mpd pd fn v pmv fmv uv;
			resuvdg = doRESUnifVDGraph sig (dgraph_from_ueq sig eq);
			comptresuvdgs = soresolve_to_dgraph_filter sig tcnf :: Computation (RESUnifVDGraph t mpd pd fn v pmv fmv uv);
			etresuvdgs = runcomp cesq_resolution_execorder comptresuvdgs;
			rresuvdgs = mergeRESUnifVDGraph resuvdg <$> etresuvdgs;
			finsts = (\resuvdg -> ImplicitAS (ImplicitInstantiation (ExactGraphInst resuvdg) sel));
			einsts = finsts <$> rresuvdgs;
	runBaseQWithUV _ tcnf sel (FLogicQuery sig (NotEquals a1 a2)) = ExplicitAS einsts
		where
			a1w = ADDirect (NSOAtom a1);
			a2w = ADDirect (NSOAtom a2);
			eq = AtomUnif a1w a2w :: UnifEquation a t LambdaCNF mpd pd fn v pmv fmv uv;
			resuvdg = doRESUnifVDGraph sig (dgraph_from_ueq sig eq);
			compresuvdgs_mincnf = soresolve_to_dgraph_filter sig tcnf :: Computation (RESUnifVDGraph t mpd pd fn v pmv fmv uv);
			resuvdg_max = failedRESUnifVDGraph sig :: RESUnifVDGraph t mpd pd fn v pmv fmv uv;
			eresuvdgs_mincnf = runcomp cesq_resolution_execorder compresuvdgs_mincnf;
			eresuvdgs_mincondcnf = mergeRESUnifVDGraph resuvdg <$> eresuvdgs_mincnf;
			einsts = do
				{
					resuvdgs_mincnf <- eresuvdgs_mincnf;
					resuvdgs_mincondcnf <- eresuvdgs_mincondcnf;

					return (ImplicitAS (ImplicitInstantiation (MinMaxGraphInst resuvdgs_mincnf resuvdgs_mincondcnf resuvdg_max) sel))
				};
	runBaseQWithUV _ t sel q = error "Unexpected type of CESQ query!!!"

type CESQConstraintsOutNoPd fn pmv fmv = (Ord pmv, Ord fmv, Eq pmv, Eq fmv, Eq fn, Ord fn) 
type CESQConstraintsOut pd fn pmv fmv = (CESQConstraintsOutNoPd fn pmv fmv, Eq pd, Ord pd)
type CESQConstraintsInT t pd fn pmv fmv = (CESQConstraintsOut pd fn pmv fmv, SimpleTerm t, Bifunctor t)
type CESQConstraintsInV v = (Eq v, Ord v)
type CESQConstraintsInTV t pd fn v pmv fmv = (CESQConstraintsInT t pd fn pmv fmv, CESQConstraintsInV v)
type CESQConstraintsInTVNoPd t fn v pmv fmv = (CESQConstraintsOutNoPd fn pmv fmv, SimpleTerm t, CESQConstraintsInV v)
type CESQConstraintsInA a pd fn pmv fmv = (CESQConstraintsOut pd fn pmv fmv, SimpleTerm a)
type CESQConstraintsInAT a t pd fn pmv fmv = (CESQConstraintsInA a pd fn pmv fmv, CESQConstraintsInT t pd fn pmv fmv)
type CESQConstraintsInATV a t pd fn v pmv fmv = (CESQConstraintsInAT a t pd fn pmv fmv, CESQConstraintsInV v)
type CESQConstraintsIn a t mpd pd fn v pmv fmv = (CESQConstraintsInATV a t pd fn v pmv fmv, Queriable (BaseCESQuery a t mpd pd fn v pmv fmv) (CESQVar pmv fmv) (CNF a t mpd pd fn v pmv fmv) (CESQSol pd fn) (ImplicitInstantiation pd fn pmv fmv), ImplicitF (ImplicitInstantiation pd fn pmv fmv) (ImplicitInstantiation pd fn pmv fmv) (CESQVar pmv fmv =<- CESQSol pd fn) (BaseQueryInput (BaseCESQuery a t mpd pd fn v pmv fmv) (CESQVar pmv fmv) (CNF a t mpd pd fn v pmv fmv) (CESQSol pd fn)))

-- This instance is void, since the solutions already do not have any variables!!!
-- Keep in mind if this is used to produce substitution of variables when combining queries, this leads to problems!!
-- It should not, though...
instance Substitutable (CESQSol pd fn) (CESQVar pmv fmv) (CESQSol pd fn) where
	subst v r sol = sol

instance CESQConstraintsOut pd fn pmv fmv => Substitutable (SOTerm fn fmv) (CESQVar pmv fmv) (CESQSol pd fn) where
	subst (CESQVar (Left pmv)) (CESQSol (Left gsoa)) sot = sot
	subst (CESQVar (Right fmv)) (CESQSol (Right gsot)) (UVar fmv2) | fmv == fmv2 = inject_groundsot gsot
	subst (CESQVar (Right fmv)) (CESQSol (Right gsot)) (UVar fmv2) = UVar fmv2
	subst (CESQVar (Right fmv)) (CESQSol (Right gsot)) (UTerm (SOF (ConstF fn))) = UTerm (SOF (ConstF fn))
	subst (CESQVar (Right fmv)) (CESQSol (Right gsot)) (UTerm (SOF (Proj idx))) = UTerm (SOF (Proj idx))
	subst v r (UTerm (SOF (CompF h sts))) = UTerm (SOF (CompF (subst v r h) (subst_fmap v r sts)))
	subst _ _ _ = error "Unexpected case on subst for SOTerm"

instance CESQConstraintsInTV t pd fn v pmv fmv => Substitutable (SOMetawrap t fn v fmv) (CESQVar pmv fmv) (CESQSol pd fn) where
	subst (CESQVar (Left pmv)) (CESQSol (Left gsoa)) somw = somw
	subst (CESQVar (Right fmv)) (CESQSol (Right gsot)) (SOMetawrap (UVar v)) = SOMetawrap (UVar v)
	subst v r (SOMetawrap (UTerm t)) = SOMetawrap (UTerm (build_term (subst v r h) (fmap (\st -> fromSOMetawrap (subst v r (SOMetawrap st))) sts))) where (h,sts) = unbuild_term t
	subst _ _ _ = error "Unexpected case on subst for SOMetawrap"

instance CESQConstraintsOut pd fn pmv fmv => Substitutable (SOAtom pd fn pmv fmv) (CESQVar pmv fmv) (CESQSol pd fn) where
	subst (CESQVar (Left pmv)) (CESQSol (Left gsoa)) (UVar pmv2) | pmv == pmv2 = inject_groundsoa . lambdacnf_to_gsoa $ gsoa
	subst (CESQVar (Left pmv)) (CESQSol (Left gsoa)) (UVar pmv2) = UVar pmv2
	subst (CESQVar (Right fmv)) (CESQSol (Right gsot)) (UVar pmv2) = UVar pmv2
	subst _ _ (UTerm (SOP (ConstF pd))) = UTerm (SOP (ConstF pd))
	subst _ _ (UTerm (SOP (Proj idx))) = UTerm (SOP (Proj idx))
	subst v r (UTerm (SOP (CompF h sts))) = UTerm (SOP (CompF (subst v r h) (subst_fmap v r sts)))
	subst _ _ _ = error "Unexpected case on subst for SOAtom"

instance CESQConstraintsInATV a t pd fn v pmv fmv => Substitutable (SOMetawrapA a t pd fn v pmv fmv) (CESQVar pmv fmv) (CESQSol pd fn) where
	subst v r (SOMetawrapA soa) = SOMetawrapA (build_term (subst v r p) (subst_fmap v r sts)) where (p,sts) = unbuild_term soa

instance CESQConstraintsInA a pd fn pmv fmv => Substitutable (FirstSOAAtom a LambdaCNF mpd pd fn pmv fmv) (CESQVar pmv fmv) (CESQSol pd fn) where
	subst v r (FirstSOAAtom fsoa) = FirstSOAAtom (build_term mpd (subst_fmap v r <$> lcnfs)) where (mpd,lcnfs) = unbuild_term fsoa

instance CESQConstraintsInATV a t pd fn v pmv fmv => Substitutable (CombSOAtom a t LambdaCNF mpd pd fn v pmv fmv) (CESQVar pmv fmv) (CESQSol pd fn) where
	subst v r (NSOAtom somwa) = NSOAtom (subst v r somwa)
	subst v r (FSOAtom fsoa) = FSOAtom (subst v r fsoa)

instance CESQConstraintsInATV a t pd fn v pmv fmv => Substitutable (VarLiteral a t mpd pd fn v pmv fmv) (CESQVar pmv fmv) (CESQSol pd fn) where
	subst = subst_fmap

instance CESQConstraintsInATV a t pd fn v pmv fmv => Substitutable (Clause a t mpd pd fn v pmv fmv) (CESQVar pmv fmv) (CESQSol pd fn) where
	subst = subst_fmap

instance CESQConstraintsInATV a t pd fn v pmv fmv => Substitutable (CNF a t mpd pd fn v pmv fmv) (CESQVar pmv fmv) (CESQSol pd fn) where
	subst = subst_fmap

instance CESQConstraintsIn a t mpd pd fn v pmv fmv => Substitutable (BaseCESQuery a t mpd pd fn v pmv fmv) (CESQVar pmv fmv) (CESQSol pd fn) where
	subst = subst_bimap	



--instance Substitutable (ParcCESQSol pd fn pmv fmv) (CESQVar pmv fmv) (CESQVar pmv fmv) where
--	subst = undefined

instance CESQConstraintsOutNoPd fn pmv fmv => Substitutable (SOTerm fn fmv) (CESQVar pmv fmv) (CESQVar pmv fmv) where
	subst (CESQVar (Left pmv)) (CESQVar (Left rpmv)) sot = sot
	subst (CESQVar (Right fmv)) (CESQVar (Right rfmv)) (UVar fmv2) | fmv == fmv2 = UVar rfmv
	subst (CESQVar (Right fmv)) (CESQVar (Right rfmv)) (UVar fmv2) = UVar fmv2
	subst (CESQVar (Right fmv)) (CESQVar (Right rfmv)) (UTerm (SOF (ConstF fn))) = UTerm (SOF (ConstF fn))
	subst (CESQVar (Right fmv)) (CESQVar (Right rfmv)) (UTerm (SOF (Proj idx))) = UTerm (SOF (Proj idx))
	subst v r (UTerm (SOF (CompF h sts))) = UTerm (SOF (CompF (subst v r h) (subst_fmap v r sts)))
	subst _ _ _ = error "Unexpected case on subst for SOTerm"

instance CESQConstraintsInTVNoPd t fn v pmv fmv => Substitutable (SOMetawrap t fn v fmv) (CESQVar pmv fmv) (CESQVar pmv fmv) where
	subst (CESQVar (Left pmv)) (CESQVar (Left rpmv)) somw = somw
	subst (CESQVar (Right fmv)) (CESQVar (Right rfmv)) (SOMetawrap (UVar v)) = SOMetawrap (UVar v)
	subst v r (SOMetawrap (UTerm t)) = SOMetawrap (UTerm (build_term (subst v r h) (fmap (\st -> fromSOMetawrap (subst v r (SOMetawrap st))) sts))) where (h,sts) = unbuild_term t
	subst _ _ _ = error "Unexpected case on subst for SOMetawrap"

instance CESQConstraintsOut pd fn pmv fmv => Substitutable (SOAtom pd fn pmv fmv) (CESQVar pmv fmv) (CESQVar pmv fmv) where
	subst (CESQVar (Left pmv)) (CESQVar (Left rpmv)) (UVar pmv2) | pmv == pmv2 = UVar rpmv
	subst (CESQVar (Left pmv)) (CESQVar (Left rpmv)) (UVar pmv2) = UVar pmv2
	subst (CESQVar (Right fmv)) (CESQVar (Right rfmv)) (UVar pmv2) = UVar pmv2
	subst _ _ (UTerm (SOP (ConstF pd))) = UTerm (SOP (ConstF pd))
	subst _ _ (UTerm (SOP (Proj idx))) = UTerm (SOP (Proj idx))
	subst v r (UTerm (SOP (CompF h sts))) = UTerm (SOP (CompF (subst v r h) (subst_fmap v r sts)))
	subst _ _ _ = error "Unexpected case on subst for SOAtom"

instance CESQConstraintsInATV a t pd fn v pmv fmv => Substitutable (SOMetawrapA a t pd fn v pmv fmv) (CESQVar pmv fmv) (CESQVar pmv fmv) where
	subst v r (SOMetawrapA soa) = SOMetawrapA (build_term (subst v r p) (subst_fmap v r sts)) where (p,sts) = unbuild_term soa

instance CESQConstraintsInA a pd fn pmv fmv => Substitutable (FirstSOAAtom a LambdaCNF mpd pd fn pmv fmv) (CESQVar pmv fmv) (CESQVar pmv fmv) where
	subst v r (FirstSOAAtom fsoa) = FirstSOAAtom (build_term mpd (subst_fmap v r <$> lcnfs)) where (mpd,lcnfs) = unbuild_term fsoa

instance CESQConstraintsInATV a t pd fn v pmv fmv => Substitutable (CombSOAtom a t LambdaCNF mpd pd fn v pmv fmv) (CESQVar pmv fmv) (CESQVar pmv fmv) where
	subst v r (NSOAtom somwa) = NSOAtom (subst v r somwa)
	subst v r (FSOAtom fsoa) = FSOAtom (subst v r fsoa)

instance CESQConstraintsInATV a t pd fn v pmv fmv => Substitutable (VarLiteral a t mpd pd fn v pmv fmv) (CESQVar pmv fmv) (CESQVar pmv fmv) where
	subst = subst_fmap

instance CESQConstraintsInATV a t pd fn v pmv fmv => Substitutable (Clause a t mpd pd fn v pmv fmv) (CESQVar pmv fmv) (CESQVar pmv fmv) where
	subst = subst_fmap

instance CESQConstraintsInATV a t pd fn v pmv fmv => Substitutable (CNF a t mpd pd fn v pmv fmv) (CESQVar pmv fmv) (CESQVar pmv fmv) where
	subst = subst_fmap

instance CESQConstraintsIn a t mpd pd fn v pmv fmv => Substitutable (BaseCESQuery a t mpd pd fn v pmv fmv) (CESQVar pmv fmv) (CESQVar pmv fmv) where
	subst = subst_bimap


-- This is actually unlikely to happen, because meta-variables have arity, which means they are not just an Int.
instance (Variabilizable pmv, Variabilizable fmv) => Variabilizable (CESQVar pmv fmv) where
	from_var (IntVar i) | mod i 2 == 0 = CESQVar (Left (from_var (IntVar (quot i 2))))
	from_var (IntVar i) = CESQVar (Right (from_var (IntVar (quot (i-1) 2))))
	get_var (CESQVar (Left i)) = IntVar (2 * (getVarID_gen i))
	get_var (CESQVar (Right i)) = IntVar (2 * (getVarID_gen i) + 1)

class ImplicitFWithUV sa sb b f uv | f sa -> sb where
	composeImplicitWithUV :: Erase uv -> sa -> f -> AnswerSet sb b

-- IMPORTANT NOTE: We completely ignore the select clause for the first query, since it doesn't really change the graph itself and there's no real danger of specific meta-variables colliding. Or that's what I think now. This note is here as a beacon in case problems arise from this assumption turning out wrong.
instance forall a t mpd pd fn v pmv fmv uv. ResConstraintsALL a t LambdaCNF mpd pd fn v pmv fmv uv => ImplicitFWithUV (ImplicitInstantiation pd fn pmv fmv) (ImplicitInstantiation pd fn pmv fmv) (CESQVar pmv fmv =<- CESQSol pd fn) (BaseQueryInput (BaseCESQuery a t mpd pd fn v pmv fmv) (CESQVar pmv fmv) (CNF a t mpd pd fn v pmv fmv) (CESQSol pd fn)) uv where
	composeImplicitWithUV _ (ImplicitInstantiation (ExactGraphInst resuvdg) sel) (tcnf,sel2,FLogicQuery sig (Entails ecnf)) = undefined
		where
			compresuvdgs = soresolve_to_dgraph_filter sig (tcnf ++ ecnf) :: Computation (RESUnifVDGraph t mpd pd fn v pmv fmv uv);
			eresuvdgs = runcomp cesq_resolution_execorder compresuvdgs;
			finsts = (\resuvdg2 -> ImplicitAS (ImplicitInstantiation (ExactGraphInst (mergeRESUnifVDGraph resuvdg resuvdg2)) sel));
			einsts = finsts <$> eresuvdgs;

instance ImplicitF (ImplicitInstantiation pd fn pmv fmv) (ImplicitInstantiation pd fn pmv fmv) (CESQVar pmv fmv =<- CESQSol pd fn) (CESQVar pmv fmv :->= CESQSol pd fn) where
	composeImplicit = composeImplicitDefault

instance CESQConstraintsOut pd fn pmv fmv => ImplicitF (AnswerSet (ImplicitInstantiation pd fn pmv fmv) (CESQVar pmv fmv =<- CESQSol pd fn), AnswerSet (ImplicitInstantiation pd fn pmv fmv) (CESQVar pmv fmv =<- CESQSol pd fn)) (ImplicitInstantiation pd fn pmv fmv) (CESQVar pmv fmv =<- CESQSol pd fn) ProductQOP where
	composeImplicit = composeImplicitDefault

testtypes :: CESQConstraintsIn a t mpd pd fn v pmv fmv => CNF a t mpd pd fn v pmv fmv -> Query (BaseCESQuery a t mpd pd fn v pmv fmv) (CESQVar pmv fmv) (CESQSol pd fn) -> AnswerSet (ImplicitInstantiation pd fn pmv fmv) (CESQVar pmv fmv =<- CESQSol pd fn)
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


