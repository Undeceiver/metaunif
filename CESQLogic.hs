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
import DependencyGraph

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

gsoa_to_lambdacnf :: GroundSOA pd fn -> LambdaCNF (GroundSOA pd fn)
gsoa_to_lambdacnf gsoa = LambdaCNF [LambdaClause [PosLit gsoa]]

-- It is important to explain how this is to be understood.
-- For exact graph instantiations, the instantiations are those encompassed by the indicated graph.
-- For minmax graph instantiations, the semantics are as follows:
--	- All the instantiations of MaxGraphInst are instantiations of the minmax.
--	- If MinCondGraphInst yields any results within a global constant boundary, then there's no more results to be presented.
--	- If MinCondGraphInst does not yield results within a global constant boundary, then all the results of MinGraphInst are results of the minmax.
--	- Conceptually, this is to be understood as: All the results of MinGraphInst that are not results of MinCondGraphInst, except we do the check globally rather than individually on each result.
--	- Note that for checkImplicit, we do actually have the correct semantics where we check if the element is part of MinGraphInst but not of MinCondGraphInst.
data ImplicitInstantiationV t mpd pd fn v pmv fmv uv = ExactGraphInst {fromExactGraphInst :: RESUnifVDGraph t mpd pd fn v pmv fmv uv} | MinMaxGraphInst {fromMinGraphInst :: RESUnifVDGraph t mpd pd fn v pmv fmv uv, fromMinCondGraphInst :: RESUnifVDGraph t mpd pd fn v pmv fmv uv, fromMaxGraphInst :: RESUnifVDGraph t mpd pd fn v pmv fmv uv}

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

instance ESMGUConstraintsUPmv t pd fn v pmv fmv uv => Implicit (ImplicitInstantiationV t mpd pd fn v pmv fmv uv) (CESQVar pmv fmv := CESQSol pd fn) where
	checkImplicit (ExactGraphInst inst) cesqsol = checkImplicit inst usol where usol = implicitInst_tounifsol cesqsol
	checkImplicit (MinMaxGraphInst mininst mincondinst maxinst) cesqsol = (checkImplicit maxinst usol) >>=| ((checkImplicit mininst usol) >>=& (not <$> (checkImplicit mincondinst usol))) where usol = implicitInst_tounifsol cesqsol
	enumImplicit (ExactGraphInst inst) = implicitInst_fromunifsol <$> (enumImplicit inst)
	-- To implement this, we need to implement the functionality of merging two dependency graphs. This needs to be done "manually".
	-- Pick all nodes, add them to the new graph (with all their elements), then add all the edges, then add all the vertical edges.
	-- Should test this separately.
	enumImplicit (MinMaxGraphInst mininst mincondinst maxinst) = if mergedtest then resmax else (resmax .+. resmin)
		where
			-- This may potentially be problematic
			sig = sig_RESUnifVDGraph mininst;
			resmax = implicitInst_fromunifsol <$> (enumImplicit maxinst);
			mergedmax = mergeRESUnifVDGraph sig mininst mincondinst;
			-- We use diagonalization here. This is an arbitrary choice, but one that works for this particular purpose absolutely fine.
			mergedtest = Prelude.null (get_nstep implicitInst_mincond_depth ((enumImplicit mincondinst) \$ ()));
			resmin = implicitInst_fromunifsol <$> (enumImplicit mininst);

data ImplicitInstantiation t mpd pd fn v pmv fmv uv = ImplicitInstantiation {getImplicitInstantiationV :: ImplicitInstantiationV t mpd pd fn v pmv fmv uv, getImplicitInstantiationSel :: [CESQVar pmv fmv |<- CESQSol pd fn]}

instance ESMGUConstraintsUPmv t pd fn v pmv fmv uv => Implicit (ImplicitInstantiation t mpd pd fn v pmv fmv uv) (CESQVar pmv fmv =<- CESQSol pd fn) where
	-- For checking, it's enough to just check the solution directly, ignoring the select clause. I mean, we could verify that the solution only contains variables in the select clause, but this is kind of pointless. The point is, if it does, then the checkImplicit underneath will only check the variables in the cesqsol variable, by construction.
	checkImplicit (ImplicitInstantiation impv seli) (QResultSet sele cesqsol) = checkImplicit impv cesqsol
	enumImplicit (ImplicitInstantiation impv sel) = (QResultSet sel) <$> (enumImplicit impv)

cesq_resolution_execorder :: DFS
cesq_resolution_execorder = DFS

-- This class represents something that, once a unifier variable type is specified, has an instance of Queriable.
class QueriableWithUV q v t r s uv | q v t uv -> r s where
	runBaseQWithUV :: Erase uv -> t -> [v |<- r] -> q -> AnswerSet s (v =<- r)

instance forall a t mpd pd fn v pmv fmv uv. ResConstraintsALL a t LambdaCNF mpd pd fn v pmv fmv uv => QueriableWithUV (BaseCESQuery a t mpd pd fn v pmv fmv) (CESQVar pmv fmv) (CNF a t mpd pd fn v pmv fmv) (CESQSol pd fn) (ImplicitInstantiation t mpd pd fn v pmv fmv uv) uv where
	runBaseQWithUV _ tcnf sel (FLogicQuery sig (Entails ecnf)) = ExplicitAS einsts
		where
			compresuvdgs = soresolve_to_dgraph_filter sig (tcnf ++ ecnf) :: Computation (RESUnifVDGraph t mpd pd fn v pmv fmv uv);
			eresuvdgs = runcomp cesq_resolution_execorder compresuvdgs;
			finsts = (\resuvdg -> ImplicitAS (ImplicitInstantiation (ExactGraphInst resuvdg) sel));
			einsts = finsts <$> eresuvdgs;
	runBaseQWithUV _ tcnf sel (FLogicQuery sig (Satisfies ecnf satcnf)) = ExplicitAS einsts
		where
			compresuvdgs_ecnf = soresolve_to_dgraph_filter sig (tcnf ++ ecnf) :: Computation (RESUnifVDGraph t mpd pd fn v pmv fmv uv);
			compresuvdgs_mincondcnf = soresolve_to_dgraph_filter sig (tcnf ++ satcnf) :: Computation (RESUnifVDGraph t mpd pd fn v pmv fmv uv);
			eresuvdgs_ecnf = runcomp cesq_resolution_execorder compresuvdgs_ecnf;
			eresuvdgs_mincondcnf = runcomp cesq_resolution_execorder compresuvdgs_mincondcnf;
			resuvdg_min = emptyRESUnifVDGraph sig :: RESUnifVDGraph t mpd pd fn v pmv fmv uv;
			einsts = do
				{
					resuvdgs_ecnf <- eresuvdgs_ecnf;
					resuvdgs_mincondcnf <- eresuvdgs_mincondcnf;

					return (ImplicitAS (ImplicitInstantiation (MinMaxGraphInst resuvdg_min resuvdgs_mincondcnf resuvdgs_ecnf) sel))
				};
-- Note that in Equals and NotEquals we completely ignore the theory, we are only doing a syntactic check!
	runBaseQWithUV _ tcnf sel (FLogicQuery sig (Equals a1 a2)) = inst
		where
			a1w = ADDirect (NSOAtom a1);
			a2w = ADDirect (NSOAtom a2);
			eq = AtomUnif a1w a2w :: UnifEquation a t LambdaCNF mpd pd fn v pmv fmv uv;
			resuvdg = doRESUnifVDGraph sig (dgraph_from_ueq sig eq);			
			inst = ImplicitAS (ImplicitInstantiation (ExactGraphInst resuvdg) sel);
	runBaseQWithUV _ tcnf sel (FLogicQuery sig (NotEquals a1 a2)) = inst
		where
			a1w = ADDirect (NSOAtom a1);
			a2w = ADDirect (NSOAtom a2);
			eq = AtomUnif a1w a2w :: UnifEquation a t LambdaCNF mpd pd fn v pmv fmv uv;
			resuvdg_mincond = doRESUnifVDGraph sig (dgraph_from_ueq sig eq);
			resuvdg_max = failedRESUnifVDGraph sig :: RESUnifVDGraph t mpd pd fn v pmv fmv uv;
			resuvdg_min = emptyRESUnifVDGraph sig :: RESUnifVDGraph t mpd pd fn v pmv fmv uv;
			inst = ImplicitAS (ImplicitInstantiation (MinMaxGraphInst resuvdg_min resuvdg_mincond resuvdg_max) sel);
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
type CESQConstraintsIn a t mpd pd fn v pmv fmv uv = (CESQConstraintsInATV a t pd fn v pmv fmv, Queriable (BaseCESQuery a t mpd pd fn v pmv fmv) (CESQVar pmv fmv) (CNF a t mpd pd fn v pmv fmv) (CESQSol pd fn) (ImplicitInstantiation t mpd pd fn v pmv fmv uv), ImplicitF (ImplicitInstantiation t mpd pd fn v pmv fmv uv) (ImplicitInstantiation t mpd pd fn v pmv fmv uv) (CESQVar pmv fmv =<- CESQSol pd fn) (BaseQueryInput (BaseCESQuery a t mpd pd fn v pmv fmv) (CESQVar pmv fmv) (CNF a t mpd pd fn v pmv fmv) (CESQSol pd fn)))
type CESQConstraintsALL a t mpd pd fn v pmv fmv uv = (CESQConstraintsIn a t mpd pd fn v pmv fmv uv, ESMGUConstraintsALL a t LambdaCNF mpd pd fn v pmv fmv uv)

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

instance CESQConstraintsInATV a t pd fn v pmv fmv => Substitutable (BaseCESQuery a t mpd pd fn v pmv fmv) (CESQVar pmv fmv) (CESQSol pd fn) where
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

instance CESQConstraintsInATV a t pd fn v pmv fmv => Substitutable (BaseCESQuery a t mpd pd fn v pmv fmv) (CESQVar pmv fmv) (CESQVar pmv fmv) where
	subst = subst_bimap


-- This is actually unlikely to happen, because meta-variables have arity, which means they are not just an Int.
instance (Variabilizable pmv, Variabilizable fmv) => Variabilizable (CESQVar pmv fmv) where
	from_var (IntVar i) | mod i 2 == 0 = CESQVar (Left (from_var (IntVar (quot i 2))))
	from_var (IntVar i) = CESQVar (Right (from_var (IntVar (quot (i-1) 2))))
	get_var (CESQVar (Left i)) = IntVar (2 * (getVarID_gen i))
	get_var (CESQVar (Right i)) = IntVar (2 * (getVarID_gen i) + 1)
	update_var f (CESQVar (Left pmv)) = CESQVar (Left (update_var f pmv))
	update_var f (CESQVar (Right fmv)) = CESQVar (Right (update_var f fmv))

-- IMPORTANT NOTE: We completely ignore the select clause for the first query, since it doesn't really change the graph itself and there's no real danger of specific meta-variables colliding. Or that's what I think now. This note is here as a beacon in case problems arise from this assumption turning out wrong.
instance forall a t mpd pd fn v pmv fmv uv. ResConstraintsALL a t LambdaCNF mpd pd fn v pmv fmv uv => ImplicitF (ImplicitInstantiation t mpd pd fn v pmv fmv uv) (ImplicitInstantiation t mpd pd fn v pmv fmv uv) (CESQVar pmv fmv =<- CESQSol pd fn) (BaseQueryInput (BaseCESQuery a t mpd pd fn v pmv fmv) (CESQVar pmv fmv) (CNF a t mpd pd fn v pmv fmv) (CESQSol pd fn)) where
	composeImplicit (ImplicitInstantiation (ExactGraphInst resuvdg) sel) (tcnf,sel2,FLogicQuery sig (Entails ecnf)) = ExplicitAS einsts
		where
			compresuvdgs = soresolve_to_dgraph_filter sig (tcnf ++ ecnf) :: Computation (RESUnifVDGraph t mpd pd fn v pmv fmv uv);
			eresuvdgs = runcomp cesq_resolution_execorder compresuvdgs;
			finsts = (\resuvdg2 -> ImplicitAS (ImplicitInstantiation (ExactGraphInst (mergeRESUnifVDGraph sig resuvdg resuvdg2)) sel2));
			einsts = finsts <$> eresuvdgs;
	composeImplicit (ImplicitInstantiation (ExactGraphInst resuvdg) sel) (tcnf,sel2,FLogicQuery sig (Satisfies ecnf satcnf)) = ExplicitAS einsts
		where
			compresuvdgs_ecnf = soresolve_to_dgraph_filter sig (tcnf ++ ecnf) :: Computation (RESUnifVDGraph t mpd pd fn v pmv fmv uv);
			compresuvdgs_mincondcnf = soresolve_to_dgraph_filter sig (tcnf ++ satcnf) :: Computation (RESUnifVDGraph t mpd pd fn v pmv fmv uv);
			eresuvdgs_ecnf = runcomp cesq_resolution_execorder compresuvdgs_ecnf;
			eresuvdgs_mincondcnf = runcomp cesq_resolution_execorder compresuvdgs_mincondcnf;
			einsts = do
				{
					resuvdgs_ecnf <- eresuvdgs_ecnf;
					resuvdgs_mincondcnf <- eresuvdgs_mincondcnf;

					return (ImplicitAS (ImplicitInstantiation (MinMaxGraphInst resuvdg (mergeRESUnifVDGraph sig resuvdg resuvdgs_mincondcnf) (mergeRESUnifVDGraph sig resuvdg resuvdgs_ecnf)) sel2))
				};
	composeImplicit (ImplicitInstantiation (ExactGraphInst resuvdg) sel) (tcnf,sel2,FLogicQuery sig (Equals a1 a2)) = inst
		where
			a1w = ADDirect (NSOAtom a1);
			a2w = ADDirect (NSOAtom a2);
			eq = AtomUnif a1w a2w :: UnifEquation a t LambdaCNF mpd pd fn v pmv fmv uv;
			resuvdg2 = doRESUnifVDGraph sig (dgraph_from_ueq sig eq);			
			inst = ImplicitAS (ImplicitInstantiation (ExactGraphInst (mergeRESUnifVDGraph sig resuvdg resuvdg2)) sel2);
	composeImplicit (ImplicitInstantiation (ExactGraphInst resuvdg) sel) (tcnf,sel2,FLogicQuery sig (NotEquals a1 a2)) = inst
		where
			a1w = ADDirect (NSOAtom a1);
			a2w = ADDirect (NSOAtom a2);
			eq = AtomUnif a1w a2w :: UnifEquation a t LambdaCNF mpd pd fn v pmv fmv uv;
			resuvdg_mincond = doRESUnifVDGraph sig (dgraph_from_ueq sig eq);
			resuvdg_max = failedRESUnifVDGraph sig :: RESUnifVDGraph t mpd pd fn v pmv fmv uv;
			inst = ImplicitAS (ImplicitInstantiation (MinMaxGraphInst resuvdg (mergeRESUnifVDGraph sig resuvdg resuvdg_mincond) resuvdg_max) sel2);
	composeImplicit (ImplicitInstantiation (MinMaxGraphInst resuvdg_min resuvdg_mincond resuvdg_max) sel) (tcnf,sel2,FLogicQuery sig (Entails ecnf)) = ExplicitAS einsts
		where
			compresuvdgs = soresolve_to_dgraph_filter sig (tcnf ++ ecnf) :: Computation (RESUnifVDGraph t mpd pd fn v pmv fmv uv);
			eresuvdgs = runcomp cesq_resolution_execorder compresuvdgs;
			finsts = (\resuvdg2 -> ImplicitAS (ImplicitInstantiation (MinMaxGraphInst (mergeRESUnifVDGraph sig resuvdg_min resuvdg2) (mergeRESUnifVDGraph sig resuvdg_mincond resuvdg2) (mergeRESUnifVDGraph sig resuvdg_max resuvdg2)) sel2));
			einsts = finsts <$> eresuvdgs;
	composeImplicit (ImplicitInstantiation (MinMaxGraphInst resuvdg_min resuvdg_mincond resuvdg_max) sel) (tcnf,sel2,FLogicQuery sig (Satisfies ecnf satcnf)) = ExplicitAS einsts
		where
			compresuvdgs_ecnf = soresolve_to_dgraph_filter sig (tcnf ++ ecnf) :: Computation (RESUnifVDGraph t mpd pd fn v pmv fmv uv);
			compresuvdgs_mincondcnf = soresolve_to_dgraph_filter sig (tcnf ++ satcnf) :: Computation (RESUnifVDGraph t mpd pd fn v pmv fmv uv);
			eresuvdgs_ecnf = runcomp cesq_resolution_execorder compresuvdgs_ecnf;
			eresuvdgs_mincondcnf = runcomp cesq_resolution_execorder compresuvdgs_mincondcnf;
			einsts = do
				{
					resuvdgs_ecnf <- eresuvdgs_ecnf;
					resuvdgs_mincondcnf <- eresuvdgs_mincondcnf;

					return (ImplicitAS (ImplicitInstantiation (MinMaxGraphInst resuvdg_min (mergeRESUnifVDGraph sig resuvdg_mincond resuvdgs_mincondcnf) (mergeRESUnifVDGraph sig resuvdg_max resuvdgs_ecnf)) sel2))
				};
	composeImplicit (ImplicitInstantiation (MinMaxGraphInst resuvdg_min resuvdg_mincond resuvdg_max) sel) (tcnf,sel2,FLogicQuery sig (Equals a1 a2)) = inst
		where
			a1w = ADDirect (NSOAtom a1);
			a2w = ADDirect (NSOAtom a2);
			eq = AtomUnif a1w a2w :: UnifEquation a t LambdaCNF mpd pd fn v pmv fmv uv;
			resuvdg2 = doRESUnifVDGraph sig (dgraph_from_ueq sig eq);			
			inst = ImplicitAS (ImplicitInstantiation (MinMaxGraphInst (mergeRESUnifVDGraph sig resuvdg_min resuvdg2) (mergeRESUnifVDGraph sig resuvdg_mincond resuvdg2) (mergeRESUnifVDGraph sig resuvdg_max resuvdg2)) sel2);
	composeImplicit (ImplicitInstantiation (MinMaxGraphInst resuvdg_min resuvdg_mincond resuvdg_max) sel) (tcnf,sel2,FLogicQuery sig (NotEquals a1 a2)) = inst
		where
			a1w = ADDirect (NSOAtom a1);
			a2w = ADDirect (NSOAtom a2);
			eq = AtomUnif a1w a2w :: UnifEquation a t LambdaCNF mpd pd fn v pmv fmv uv;
			resuvdg_mincond2 = doRESUnifVDGraph sig (dgraph_from_ueq sig eq);
			resuvdg_max2 = failedRESUnifVDGraph sig :: RESUnifVDGraph t mpd pd fn v pmv fmv uv;
			inst = ImplicitAS (ImplicitInstantiation (MinMaxGraphInst resuvdg_min (mergeRESUnifVDGraph sig resuvdg_mincond resuvdg_mincond2) resuvdg_max2) sel2);
	composeImplicit _ _ = error "Error on composeImplicit for ImplicitInstantiations and Queries: Case not considered!!!"

-- Note that the way we use SOTerm and SOAtom here is overloading: Here they are actually third-order elements, but we can express them like second-order elements seamlessly. It's important to keep these two scopes separate, or really weird things could happen.
-- Specifically, we do not use projections here and use the second-order variables themselves to stand in for replacing them for their values.
data CESQArgumentMap pd fn pmv fmv = CESQFAM fmv (SOTerm fn fmv) | CESQPAM pmv (SOAtom pd fn pmv fmv) deriving (Eq, Ord, Show)

-- Note: It is possible we are calling this function too often and this is a performance issue. I don't think so, though.
instance (Ord pmv, Ord fmv) => Transformable [CESQArgumentMap pd fn pmv fmv] (CESQVar pmv fmv :->= CESQSol pd fn) where
	transform am = fromList (transform_single_cesqam <$> am)

transform_single_cesqam :: (Ord pmv, Ord fmv) => CESQArgumentMap pd fn pmv fmv -> (CESQVar pmv fmv,((CESQVar pmv fmv =<- CESQSol pd fn) -> CESQSol pd fn))
transform_single_cesqam (CESQFAM fmv sot) = (CESQVar (Right fmv), transform_sot_cesqam sot)
transform_single_cesqam (CESQPAM pmv soa) = (CESQVar (Left pmv), transform_soa_cesqam soa)

transform_sot_cesqam :: (Ord pmv, Ord fmv) => SOTerm fn fmv -> CESQVar pmv fmv =<- CESQSol pd fn -> CESQSol pd fn
transform_sot_cesqam (UVar fmv) rs = rsmap !# (CESQVar (Right fmv)) $ "Error on transform_sot_cesqam. Found a second-order variable that is not part of the result set!" where rsmap = qresultset_result rs
transform_sot_cesqam (UTerm (SOF (ConstF fn))) rs = CESQSol (Right (Fix (SOF (ConstF fn))))
transform_sot_cesqam (UTerm (SOF (Proj idx))) rs = error "Found a projection on a third/second-order term when transforming!"
transform_sot_cesqam (UTerm (SOF (CompF h sts))) rs = CESQSol (Right (Fix (SOF (CompF rh rsts)))) where (CESQSol (Right rh)) = transform_sot_cesqam h rs; frsts = (\(CESQSol (Right rst)) -> rst); rsts = frsts . (\st -> transform_sot_cesqam st rs) <$> sts

transform_soa_cesqam :: (Ord pmv, Ord fmv) => SOAtom pd fn pmv fmv -> CESQVar pmv fmv =<- CESQSol pd fn -> CESQSol pd fn
transform_soa_cesqam (UVar pmv) rs = rsmap !# (CESQVar (Left pmv)) $ "Error on transform_soa_cesqam. Found a second-order variable that is not part of the result set!" where rsmap = qresultset_result rs
transform_soa_cesqam (UTerm (SOP (ConstF pd))) rs = CESQSol (Left (gsoa_to_lambdacnf (Fix (SOP (ConstF pd)))))
transform_soa_cesqam (UTerm (SOP (Proj idx))) rs = error "Found a projection on a third/second-order term when transforming!"
transform_soa_cesqam (UTerm (SOP (CompF h sts))) rs = CESQSol (Left (gsoa_to_lambdacnf (Fix (SOP (CompF rrh rsts))))) where (CESQSol (Left rh)) = transform_soa_cesqam h rs; rrh = lambdacnf_to_gsoa rh; frsts = (\(CESQSol (Right rst)) -> rst); rsts = frsts . (\st -> transform_sot_cesqam st rs) <$> sts

instance forall t mpd pd fn v pmv fmv uv. (Ord pmv, Ord fmv) => Functional [CESQArgumentMap pd fn pmv fmv] (CESQVar pmv fmv =<- CESQSol pd fn) (AnswerSet (ImplicitInstantiation t mpd pd fn v pmv fmv uv) (CESQVar pmv fmv =<- CESQSol pd fn)) where
	tofun am = tofun (transform am::CESQVar pmv fmv :->= CESQSol pd fn)

instance CESQConstraintsOut pd fn pmv fmv => Substitutable [CESQArgumentMap pd fn pmv fmv] (CESQVar pmv fmv) (CESQSol pd fn) where
	subst = subst_fmap

instance forall pd fn pmv fmv. CESQConstraintsOut pd fn pmv fmv => Substitutable (CESQArgumentMap pd fn pmv fmv) (CESQVar pmv fmv) (CESQSol pd fn) where
	subst (CESQVar (Left pmv)) (CESQSol (Left lcnf)) (CESQPAM rpmv soa) = CESQPAM rpmv (subst (CESQVar (Left pmv)::CESQVar pmv fmv) (CESQSol (Left lcnf)) soa)

-- Note that the result of this is weird when it comes to the select clause, but we always use this before composing with another query which will override the select clause.
instance forall a t mpd pd fn v pmv fmv uv. ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ImplicitF (ImplicitInstantiation t mpd pd fn v pmv fmv uv) (ImplicitInstantiation t mpd pd fn v pmv fmv uv) (CESQVar pmv fmv =<- CESQSol pd fn) [CESQArgumentMap pd fn pmv fmv] where
	composeImplicit (ImplicitInstantiation (ExactGraphInst resuvdg) sel) am = ImplicitAS (ImplicitInstantiation (ExactGraphInst rresuvdg) sel)
		where
			(mpmv, mfmv) = implicitinst_am_maxvars am;
			sig = sig_RESUnifVDGraph resuvdg;
			-- In order to work, this assumes that the function re-assignation done here is the same as when merging the graphs.
			-- It should, as it's just the maximum of one graph + 1, but it's worth making clear here.
			fpmv = implicitinst_am_substvars mpmv::pmv -> pmv;
			ffmv = implicitinst_am_substvars mfmv::fmv -> fmv;
			fam = implicitinst_am_transformam fpmv ffmv sig;
			-- To standardize apart the variables of the original graph, we create a new graph which simply has the variables in the argument map and no edges, and we merge the original graph unto it. Then, we add the additional equations
			empty_sig = SOSignature (fosig sig) EnumProc.Empty EnumProc.Empty (sopreds sig);
			new_sig = Prelude.foldr implicitinst_am_addtosig empty_sig am;
			new_resuvdg = doRESUnifVDGraph new_sig (Prelude.foldr (\ame -> \st -> st >> implicitinst_am_addam ame) (put (emptyVDGraph new_sig)) am) :: RESUnifVDGraph t mpd pd fn v pmv fmv uv;
			merged_resuvdg = mergeRESUnifVDGraph empty_sig resuvdg new_resuvdg;
			rsig = sig_RESUnifVDGraph merged_resuvdg;
			rresuvdg = doRESUnifVDGraph rsig (Prelude.foldr (\ame -> \st -> st >> implicitinst_am_addedge (fam ame)) (unRESUnifVDGraph merged_resuvdg) am);
	composeImplicit (ImplicitInstantiation (MinMaxGraphInst resuvdg_min resuvdg_mincond resuvdg_max) sel) am = ImplicitAS (ImplicitInstantiation (MinMaxGraphInst rresuvdg_min rresuvdg_mincond rresuvdg_max) sel)
		where
			(mpmv, mfmv) = implicitinst_am_maxvars am;
			sig_min = sig_RESUnifVDGraph resuvdg_min;
			sig_mincond = sig_RESUnifVDGraph resuvdg_mincond;
			sig_max = sig_RESUnifVDGraph resuvdg_max;
			-- In order to work, this assumes that the function re-assignation done here is the same as when merging the graphs.
			-- It should, as it's just the maximum of one graph + 1, but it's worth making clear here.
			fpmv = implicitinst_am_substvars mpmv::pmv -> pmv;
			ffmv = implicitinst_am_substvars mfmv::fmv -> fmv;
			fam_min = implicitinst_am_transformam fpmv ffmv sig_min;
			fam_mincond = implicitinst_am_transformam fpmv ffmv sig_mincond;
			fam_max = implicitinst_am_transformam fpmv ffmv sig_max;
			-- To standardize apart the variables of the original graph, we create a new graph which simply has the variables in the argument map and no edges, and we merge the original graph unto it. Then, we add the additional equations
			empty_sig_min = SOSignature (fosig sig_min) EnumProc.Empty EnumProc.Empty (sopreds sig_min);
			empty_sig_mincond = SOSignature (fosig sig_mincond) EnumProc.Empty EnumProc.Empty (sopreds sig_mincond);
			empty_sig_max = SOSignature (fosig sig_max) EnumProc.Empty EnumProc.Empty (sopreds sig_max);
			new_sig_min = Prelude.foldr implicitinst_am_addtosig empty_sig_min am;
			new_sig_mincond = Prelude.foldr implicitinst_am_addtosig empty_sig_mincond am;
			new_sig_max = Prelude.foldr implicitinst_am_addtosig empty_sig_max am;
			new_resuvdg_min = doRESUnifVDGraph new_sig_min (Prelude.foldr (\ame -> \st -> st >> implicitinst_am_addam ame) (put (emptyVDGraph new_sig_min)) am) :: RESUnifVDGraph t mpd pd fn v pmv fmv uv;
			new_resuvdg_mincond = doRESUnifVDGraph new_sig_mincond (Prelude.foldr (\ame -> \st -> st >> implicitinst_am_addam ame) (put (emptyVDGraph new_sig_mincond)) am) :: RESUnifVDGraph t mpd pd fn v pmv fmv uv;
			new_resuvdg_max = doRESUnifVDGraph new_sig_max (Prelude.foldr (\ame -> \st -> st >> implicitinst_am_addam ame) (put (emptyVDGraph new_sig_max)) am) :: RESUnifVDGraph t mpd pd fn v pmv fmv uv;
			merged_resuvdg_min = mergeRESUnifVDGraph empty_sig_min resuvdg_min new_resuvdg_min;
			merged_resuvdg_mincond = mergeRESUnifVDGraph empty_sig_mincond resuvdg_mincond new_resuvdg_mincond;
			merged_resuvdg_max = mergeRESUnifVDGraph empty_sig_max resuvdg_max new_resuvdg_max;
			rsig_min = sig_RESUnifVDGraph merged_resuvdg_min;
			rsig_mincond = sig_RESUnifVDGraph merged_resuvdg_mincond;
			rsig_max = sig_RESUnifVDGraph merged_resuvdg_max;
			rresuvdg_min = doRESUnifVDGraph rsig_min (Prelude.foldr (\ame -> \st -> st >> implicitinst_am_addedge (fam_min ame)) (unRESUnifVDGraph merged_resuvdg_min) am);
			rresuvdg_mincond = doRESUnifVDGraph rsig_mincond (Prelude.foldr (\ame -> \st -> st >> implicitinst_am_addedge (fam_mincond ame)) (unRESUnifVDGraph merged_resuvdg_mincond) am);
			rresuvdg_max = doRESUnifVDGraph rsig_max (Prelude.foldr (\ame -> \st -> st >> implicitinst_am_addedge (fam_max ame)) (unRESUnifVDGraph merged_resuvdg_max) am);
	composeImplicit _ _ = error "Found unimplemented case for ImplicitF instance of ArgumentMap on ImplicitInstantiation"

implicitinst_am_maxvars :: (Variable pmv, Variable fmv) => [CESQArgumentMap pd fn pmv fmv] -> (Int,Int)
implicitinst_am_maxvars [] = (0,0)
implicitinst_am_maxvars ((CESQFAM fmv _):am) = (mpmv, max ifmv mfmv) where (mpmv, mfmv) = implicitinst_am_maxvars am; ifmv = getVarID fmv
implicitinst_am_maxvars ((CESQPAM pmv _):am) = (max ipmv mpmv, mfmv) where (mpmv, mfmv) = implicitinst_am_maxvars am; ipmv = getVarID pmv

implicitinst_am_substvars :: (Variable v, Variabilizable v) => Int -> v -> v
implicitinst_am_substvars max v = update_var (+(max+1)) v

implicitinst_am_addam :: (Ord pd, Ord pmv, Ord fn, Ord fmv) => CESQArgumentMap pd fn pmv fmv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) ()
implicitinst_am_addam (CESQFAM fmv _) = mzoom lens_esunifdgraph_dgraph $ newEqDGSONode (FSONode (UVar fmv)) >> pass
implicitinst_am_addam (CESQPAM pmv _) = mzoom lens_esunifdgraph_dgraph $ newEqDGSONode (PSONode (UVar pmv)) >> pass

implicitinst_am_addtosig :: CESQArgumentMap pd fn pmv fmv -> SOSignature mpd pd fn v pmv fmv -> SOSignature mpd pd fn v pmv fmv
implicitinst_am_addtosig (CESQFAM fmv _) sosig = SOSignature (fosig sosig) (fmv --> sovars sosig) (pvars sosig) (sopreds sosig)
implicitinst_am_addtosig (CESQPAM pmv _) sosig = SOSignature (fosig sosig) (sovars sosig) (pmv --> pvars sosig) (sopreds sosig)

-- Creates a function that replaces the second-order variables in the signature within an argument map.
implicitinst_am_transformam :: forall mpd pd fn v pmv fmv. (Ord pmv, Ord fmv) => (pmv -> pmv) -> (fmv -> fmv) -> SOSignature mpd pd fn v pmv fmv -> CESQArgumentMap pd fn pmv fmv -> CESQArgumentMap pd fn pmv fmv
implicitinst_am_transformam fpmv ffmv sosig (CESQFAM rfmv sot) = CESQFAM rfmv (subst_all fsubsts $ sot) where fmvs = sovars sosig; pmvs = pvars sosig; fsubsts = fromList . list_from_enum $ ((\fmv -> (fmv,UVar (ffmv fmv)::SOTerm fn fmv)) <$> fmvs)
implicitinst_am_transformam fpmv ffmv sosig (CESQPAM rpmv soa) = CESQPAM rpmv (subst_all fsubsts . implicitinst_am_substall_pmv psubsts $ soa) where fmvs = sovars sosig; pmvs = pvars sosig; fsubsts = fromList . list_from_enum $ ((\fmv -> (fmv,UVar (ffmv fmv)::SOTerm fn fmv)) <$> fmvs); psubsts = fromList . list_from_enum $ ((\pmv -> (pmv,fpmv pmv)) <$> pmvs)

implicitinst_am_substall_pmv :: Eq pmv => (pmv := pmv) -> SOAtom pd fn pmv fmv -> SOAtom pd fn pmv fmv
implicitinst_am_substall_pmv = subst_all

implicitinst_am_addedge :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => CESQArgumentMap pd fn pmv fmv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) ()
implicitinst_am_addedge (CESQFAM fmv sot) = do
	{
		fmvid <- grab_sonode (UVar fmv);
		sotid <- grab_sonode sot;
		mzoom lens_esunifdgraph_dgraph $ mergeEqDGSONodes fmvid sotid;

		pass
	}
implicitinst_am_addedge (CESQPAM pmv soa) = do
	{
		pmvid <- grab_asonode (UVar pmv);
		soaid <- grab_asonode soa;
		mzoom lens_esunifdgraph_dgraph $ mergeEqDGSONodes pmvid soaid;

		pass
	}

instance forall a t mpd pd fn v pmv fmv uv. ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ImplicitF (AnswerSet (ImplicitInstantiation t mpd pd fn v pmv fmv uv) (CESQVar pmv fmv =<- CESQSol pd fn), AnswerSet (ImplicitInstantiation t mpd pd fn v pmv fmv uv) (CESQVar pmv fmv =<- CESQSol pd fn)) (ImplicitInstantiation t mpd pd fn v pmv fmv uv) (CESQVar pmv fmv =<- CESQSol pd fn) ProductQOP where
	-- First, the recursive cases
	composeImplicit (ExplicitAS e1,as2) ProductQOP = ExplicitAS ((\as1 -> composeImplicit (as1,as2) ProductQOP) <$> e1)
	composeImplicit (as1,ExplicitAS e2) ProductQOP = ExplicitAS ((\as2 -> composeImplicit (as1,as2) ProductQOP) <$> e2)
	-- Now the base cases with implicit instantiations
	composeImplicit (ImplicitAS (ImplicitInstantiation (ExactGraphInst resuvdg1) sel1), ImplicitAS (ImplicitInstantiation (ExactGraphInst resuvdg2) sel2)) ProductQOP = ImplicitAS (ImplicitInstantiation (ExactGraphInst rresuvdg) (rsel1 ++ sel2))
		where
			-- This one's easy. We just need to merge the graphs with an empty signature, so that they are completely standardized apart; and combine the two select clauses.
			-- We do, however, have to adapt the select clause of the first query to reflect the standardization. 
			-- Yet again, we introduce some coupling by assuming we know how the standardization apart happens underneath, and applying that to the select clauses.
			sig2 = sig_RESUnifVDGraph resuvdg2;
			mpmv = implicitinst_productqop_maxvar (pvars sig2);
			mfmv = implicitinst_productqop_maxvar (sovars sig2);
			rsel1 = implicitinst_productqop_std_sel mpmv mfmv sel1;
			emptysig = SOSignature (Signature [] [] EnumProc.Empty) EnumProc.Empty EnumProc.Empty EnumProc.Empty;
			rresuvdg = mergeRESUnifVDGraph emptysig resuvdg1 resuvdg2;
	composeImplicit (ImplicitAS (ImplicitInstantiation (ExactGraphInst resuvdg1) sel1), ImplicitAS (ImplicitInstantiation (MinMaxGraphInst resuvdg2_min resuvdg2_mincond resuvdg2_max) sel2)) ProductQOP = ImplicitAS (ImplicitInstantiation (MinMaxGraphInst rresuvdg_min rresuvdg_mincond rresuvdg_max) (rsel1 ++ sel2))
		where
			sig2_min = sig_RESUnifVDGraph resuvdg2_min;
			sig2_mincond = sig_RESUnifVDGraph resuvdg2_mincond;
			sig2_max = sig_RESUnifVDGraph resuvdg2_max;
			-- Because there is a single select clause, here we manually standardize apart all graphs before merging, so that they still share the same variable numberings.
			-- We do this by first creating an empty graph with all the variables in all of the graphs, and nothing else, and then merging unto that, preserving variables in the case of resuvdg2.
			allpmvs = eunionAll (pvars sig2_min --> pvars sig2_mincond --> pvars sig2_max --> EnumProc.Empty);
			allfmvs = eunionAll (sovars sig2_min --> sovars sig2_mincond --> sovars sig2_max --> EnumProc.Empty);
			mpmv_min = implicitinst_productqop_maxvar (pvars sig2_min);
			mpmv_mincond = implicitinst_productqop_maxvar (pvars sig2_mincond);
			mpmv_max = implicitinst_productqop_maxvar (pvars sig2_max);
			mpmv = maximum [mpmv_min,mpmv_mincond,mpmv_max];
			mfmv_min = implicitinst_productqop_maxvar (sovars sig2_min);
			mfmv_mincond = implicitinst_productqop_maxvar (sovars sig2_mincond);
			mfmv_max = implicitinst_productqop_maxvar (sovars sig2_max);
			mfmv = maximum [mpmv_min,mpmv_mincond,mpmv_max];			
			rsel1 = implicitinst_productqop_std_sel mpmv mfmv sel1;
			baserresuvdg = implicitinst_productqop_createbaseresuvdg allpmvs allfmvs sig2_max :: RESUnifVDGraph t mpd pd fn v pmv fmv uv;
			basesig = sig_RESUnifVDGraph baserresuvdg;
			emptysig = SOSignature (Signature [] [] EnumProc.Empty) EnumProc.Empty EnumProc.Empty EnumProc.Empty;
			rresuvdg_min = mergeRESUnifVDGraph emptysig resuvdg1 (mergeRESUnifVDGraph basesig resuvdg2_min baserresuvdg);
			rresuvdg_mincond = mergeRESUnifVDGraph emptysig resuvdg1 (mergeRESUnifVDGraph basesig resuvdg2_mincond baserresuvdg);
			rresuvdg_max = mergeRESUnifVDGraph emptysig resuvdg1 (mergeRESUnifVDGraph basesig resuvdg2_max baserresuvdg);
	composeImplicit (ImplicitAS (ImplicitInstantiation (MinMaxGraphInst resuvdg2_min resuvdg2_mincond resuvdg2_max) sel2), ImplicitAS (ImplicitInstantiation (ExactGraphInst resuvdg1) sel1)) ProductQOP = ImplicitAS (ImplicitInstantiation (MinMaxGraphInst rresuvdg_min rresuvdg_mincond rresuvdg_max) (rsel1 ++ sel2))
		where
			sig2_min = sig_RESUnifVDGraph resuvdg2_min;
			sig2_mincond = sig_RESUnifVDGraph resuvdg2_mincond;
			sig2_max = sig_RESUnifVDGraph resuvdg2_max;
			-- Because there is a single select clause, here we manually standardize apart all graphs before merging, so that they still share the same variable numberings.
			-- We do this by first creating an empty graph with all the variables in all of the graphs, and nothing else, and then merging unto that, preserving variables in the case of resuvdg2.
			allpmvs = eunionAll (pvars sig2_min --> pvars sig2_mincond --> pvars sig2_max --> EnumProc.Empty);
			allfmvs = eunionAll (sovars sig2_min --> sovars sig2_mincond --> sovars sig2_max --> EnumProc.Empty);
			mpmv_min = implicitinst_productqop_maxvar (pvars sig2_min);
			mpmv_mincond = implicitinst_productqop_maxvar (pvars sig2_mincond);
			mpmv_max = implicitinst_productqop_maxvar (pvars sig2_max);
			mpmv = maximum [mpmv_min,mpmv_mincond,mpmv_max];
			mfmv_min = implicitinst_productqop_maxvar (sovars sig2_min);
			mfmv_mincond = implicitinst_productqop_maxvar (sovars sig2_mincond);
			mfmv_max = implicitinst_productqop_maxvar (sovars sig2_max);
			mfmv = maximum [mpmv_min,mpmv_mincond,mpmv_max];			
			rsel1 = implicitinst_productqop_std_sel mpmv mfmv sel1;
			baserresuvdg = implicitinst_productqop_createbaseresuvdg allpmvs allfmvs sig2_max :: RESUnifVDGraph t mpd pd fn v pmv fmv uv;
			basesig = sig_RESUnifVDGraph baserresuvdg;
			emptysig = SOSignature (Signature [] [] EnumProc.Empty) EnumProc.Empty EnumProc.Empty EnumProc.Empty;
			rresuvdg_min = mergeRESUnifVDGraph emptysig resuvdg1 (mergeRESUnifVDGraph basesig resuvdg2_min baserresuvdg);
			rresuvdg_mincond = mergeRESUnifVDGraph emptysig resuvdg1 (mergeRESUnifVDGraph basesig resuvdg2_mincond baserresuvdg);
			rresuvdg_max = mergeRESUnifVDGraph emptysig resuvdg1 (mergeRESUnifVDGraph basesig resuvdg2_max baserresuvdg);
	composeImplicit (ImplicitAS (ImplicitInstantiation (MinMaxGraphInst resuvdg1_min resuvdg1_mincond resuvdg1_max) sel1), ImplicitAS (ImplicitInstantiation (MinMaxGraphInst resuvdg2_min resuvdg2_mincond resuvdg2_max) sel2)) ProductQOP = ImplicitAS (ImplicitInstantiation (MinMaxGraphInst rresuvdg_min rresuvdg_mincond rresuvdg_max) (rsel1 ++ sel2))
		where
			sig2_min = sig_RESUnifVDGraph resuvdg2_min;
			sig2_mincond = sig_RESUnifVDGraph resuvdg2_mincond;
			sig2_max = sig_RESUnifVDGraph resuvdg2_max;
			-- Because there is a single select clause, here we manually standardize apart all graphs before merging, so that they still share the same variable numberings.
			-- We do this by first creating an empty graph with all the variables in all of the graphs, and nothing else, and then merging unto that, preserving variables in the case of resuvdg2.
			allpmvs = eunionAll (pvars sig2_min --> pvars sig2_mincond --> pvars sig2_max --> EnumProc.Empty);
			allfmvs = eunionAll (sovars sig2_min --> sovars sig2_mincond --> sovars sig2_max --> EnumProc.Empty);
			mpmv_min = implicitinst_productqop_maxvar (pvars sig2_min);
			mpmv_mincond = implicitinst_productqop_maxvar (pvars sig2_mincond);
			mpmv_max = implicitinst_productqop_maxvar (pvars sig2_max);
			mpmv = maximum [mpmv_min,mpmv_mincond,mpmv_max];
			mfmv_min = implicitinst_productqop_maxvar (sovars sig2_min);
			mfmv_mincond = implicitinst_productqop_maxvar (sovars sig2_mincond);
			mfmv_max = implicitinst_productqop_maxvar (sovars sig2_max);
			mfmv = maximum [mpmv_min,mpmv_mincond,mpmv_max];			
			rsel1 = implicitinst_productqop_std_sel mpmv mfmv sel1;
			baserresuvdg = implicitinst_productqop_createbaseresuvdg allpmvs allfmvs sig2_max :: RESUnifVDGraph t mpd pd fn v pmv fmv uv;
			basesig = sig_RESUnifVDGraph baserresuvdg;
			emptysig = SOSignature (Signature [] [] EnumProc.Empty) EnumProc.Empty EnumProc.Empty EnumProc.Empty;
			rresuvdg_min = mergeRESUnifVDGraph emptysig resuvdg1_min (mergeRESUnifVDGraph basesig resuvdg2_min baserresuvdg);
			rresuvdg_mincond = mergeRESUnifVDGraph emptysig resuvdg1_mincond (mergeRESUnifVDGraph basesig resuvdg2_mincond baserresuvdg);
			rresuvdg_max = mergeRESUnifVDGraph emptysig resuvdg1_max (mergeRESUnifVDGraph basesig resuvdg2_max baserresuvdg);
	-- If there are explicit (single) instantiations, we just use Default
	composeImplicit s ProductQOP = composeImplicitDefault s ProductQOP

-- We use the signature of resuvdg2 as base for constant symbols.
implicitinst_productqop_createbaseresuvdg :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => EnumProc pmv -> EnumProc fmv -> SOSignature mpd pd fn v pmv fmv -> RESUnifVDGraph t mpd pd fn v pmv fmv uv
implicitinst_productqop_createbaseresuvdg allpmvs allfmvs sosig = doRESUnifVDGraph rsig (Prelude.foldr fpmv (Prelude.foldr ffmv (put (emptyVDGraph rsig) >> pass) allfmvs >> pass) allpmvs >> pass)
	where
		rsig = SOSignature (fosig sosig) allfmvs allpmvs (sopreds sosig);
		fpmv = (\pmv -> \st -> st >> (mzoom lens_esunifdgraph_dgraph $ newEqDGSONode (PSONode (UVar pmv))));
		ffmv = (\fmv -> \st -> st >> (mzoom lens_esunifdgraph_dgraph $ newEqDGSONode (FSONode (UVar fmv))));

implicitinst_productqop_maxvar :: Variable v => EnumProc v -> Int
implicitinst_productqop_maxvar EnumProc.Empty = 0
implicitinst_productqop_maxvar Halt = 0
implicitinst_productqop_maxvar (Error str) = error ("Throwing enumeration error at implicitinst_productqop_maxvar: " ++ str)
implicitinst_productqop_maxvar (Continue x) = implicitinst_productqop_maxvar x
implicitinst_productqop_maxvar (Produce v x) = max (getVarID v) (implicitinst_productqop_maxvar x)

implicitinst_productqop_std_sel :: (Variable pmv, Variabilizable pmv, Variable fmv, Variabilizable fmv) => Int -> Int -> [CESQVar pmv fmv |<- CESQSol pd fn] -> [CESQVar pmv fmv |<- CESQSol pd fn]
implicitinst_productqop_std_sel _ _ [] = []
implicitinst_productqop_std_sel mpmv mfmv ((QVar (CESQVar (Left pmv))):sel) = (QVar (CESQVar (Left (update_var (+(mpmv+1)) pmv)))):(implicitinst_productqop_std_sel mpmv mfmv sel)
implicitinst_productqop_std_sel mpmv mfmv ((QVar (CESQVar (Right fmv))):sel) = (QVar (CESQVar (Right (update_var (+(mfmv+1)) fmv)))):(implicitinst_productqop_std_sel mpmv mfmv sel)
implicitinst_productqop_std_sel mpmv mfmv ((QConst x):sel) = (QConst x):(implicitinst_productqop_std_sel mpmv mfmv sel)

testtypes :: CESQConstraintsALL a t mpd pd fn v pmv fmv uv => CNF a t mpd pd fn v pmv fmv -> Query (BaseCESQuery a t mpd pd fn v pmv fmv) (CESQVar pmv fmv) [CESQArgumentMap pd fn pmv fmv] (CESQSol pd fn) -> AnswerSet (ImplicitInstantiation t mpd pd fn v pmv fmv uv) (CESQVar pmv fmv =<- CESQSol pd fn)
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


