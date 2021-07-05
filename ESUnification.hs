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


data TermDependant t fn v sov uv = TDDirect (SOMetawrap t fn v sov) | TDUnif uv (TermDependant t fn v sov uv)
-- This one makes no sense. Second order terms always appear free of unifiers, since they do not affect them directly.
--data SOTermDependant fn sov uv = SOTDDirect (SOTerm fn sov) | SOTDUnif uv (SOTermDependant fn sov uv)

is_tdunif :: TermDependant t fn v sov uv -> Bool
is_tdunif (TDDirect _) = False
is_tdunif (TDUnif _ _) = True

from_tdunif :: TermDependant t fn v sov uv -> TermDependant t fn v sov uv
from_tdunif (TDUnif _ x) = x

get_tdunif :: TermDependant t fn v sov uv -> uv
get_tdunif (TDUnif uv _) = uv

decompose_td :: TermDependant t fn v sov uv -> ([uv],SOMetawrap t fn v sov)
decompose_td (TDDirect som) = ([],som)
decompose_td (TDUnif u r) = (u:ruvs,som) where (ruvs,som) = decompose_td r

compose_td :: [uv] -> SOMetawrap t fn v sov -> TermDependant t fn v sov uv
compose_td [] som = TDDirect som
compose_td (u:us) som = TDUnif u (compose_td us som)

-- Only defined for simple dependants!
is_td_var :: TermDependant t fn v sov uv -> Bool
is_td_var (TDDirect (SOMetawrap (UVar _))) = True
is_td_var (TDDirect _) = False
is_td_var (TDUnif _ x) = is_td_var x

instance (Show (t (SOTerm fn sov) (UTerm (t (SOTerm fn sov)) v)), Show uv, Show v, Show fn, Show sov) => Show (TermDependant t fn v sov uv) where
	show (TDDirect somw) = show somw
	show (TDUnif uv td) = (show uv) ++ " " ++ (show td)

--instance (Show uv, Show fn, Show sov) => Show (SOTermDependant fn sov uv) where
--	show (SOTDDirect sot) = show sot
--	show (SOTDUnif uv td) = (show uv) ++ " " ++ (show td)

deriving instance (Eq v, Eq (t (SOTerm fn sov) (UTerm (t (SOTerm fn sov)) v)), Eq sov, Eq uv) => Eq (TermDependant t fn v sov uv)
deriving instance (Ord v, Ord (t (SOTerm fn sov) (UTerm (t (SOTerm fn sov)) v)), Ord fn, Ord sov, Ord uv) => Ord (TermDependant t fn v sov uv)

--deriving instance (Eq sov, Eq uv, Eq fn) => Eq (SOTermDependant fn sov uv)
--deriving instance (Ord fn, Ord sov, Ord uv) => Ord (SOTermDependant fn sov uv)

data AtomDependant a t ss mpd pd fn v pmv fmv uv = ADDirect (CombSOAtom a t ss mpd pd fn v pmv fmv) | ADUnif uv (AtomDependant a t ss mpd pd fn v pmv fmv uv)

is_adunif :: AtomDependant a t s mpd pd fn v pmv fmv uv -> Bool
is_adunif (ADDirect _) = False
is_adunif (ADUnif _ _) = True

from_adunif :: AtomDependant a t s mpd pd fn v pmv fmv uv -> AtomDependant a t s mpd pd fn v pmv fmv uv
from_adunif (ADUnif _ x) = x

get_adunif :: AtomDependant a t s mpd pd fn v pmv fmv uv -> uv
get_adunif (ADUnif uv _) = uv

decompose_ad :: AtomDependant a t s mpd pd fn v pmv fmv uv -> ([uv],CombSOAtom a t s mpd pd fn v pmv fmv)
decompose_ad (ADDirect soa) = ([],soa)
decompose_ad (ADUnif u r) = (u:ruvs,soa) where (ruvs,soa) = decompose_ad r

compose_ad :: [uv] -> CombSOAtom a t s mpd pd fn v pmv fmv -> AtomDependant a t s mpd pd fn v pmv fmv uv
compose_ad [] soa = ADDirect soa
compose_ad (u:us) soa = ADUnif u (compose_ad us soa)

instance (Show (a mpd (s (SOAtom pd fn pmv fmv))), Show (a (SOAtom pd fn pmv fmv) (SOMetawrap t fn v fmv)), Show uv, Show v, Show fn, Show pmv, Show fmv) => Show (AtomDependant a t s mpd pd fn v pmv fmv uv) where
	show (ADDirect soa) = show soa
	show (ADUnif uv ad) = (show uv) ++ " " ++ (show ad)

deriving instance (Eq (a (SOAtom pd fn pmv fmv) (SOMetawrap t fn v fmv)), Eq (a mpd (s (SOAtom pd fn pmv fmv))), Eq pmv, Eq fmv, Eq uv) => Eq (AtomDependant a t s mpd pd fn v pmv fmv uv)
deriving instance (Ord (a (SOAtom pd fn pmv fmv) (SOMetawrap t fn v fmv)), Ord (a mpd (s (SOAtom pd fn pmv fmv))), Ord pmv, Ord fmv, Ord uv) => Ord (AtomDependant a t s mpd pd fn v pmv fmv uv)



data UnifEquation a t ss mpd pd fn v pmv fmv uv = TermUnif (TermDependant t fn v fmv uv) (TermDependant t fn v fmv uv) | AtomUnif (AtomDependant a t ss mpd pd fn v pmv fmv uv) (AtomDependant a t ss mpd pd fn v pmv fmv uv) 

deriving instance ESMGUConstraintsALL a t ss mpd pd fn v pmv fmv uv => Eq (UnifEquation a t ss mpd pd fn v pmv fmv uv)

instance (Show (AtomDependant a t s mpd pd fn v pmv fmv uv), Show (TermDependant t fn v fmv uv)) => Show (UnifEquation a t s mpd pd fn v pmv fmv uv) where
	show (TermUnif ltd rtd) = (show ltd) ++ " = " ++ (show rtd)
	show (AtomUnif lad rad) = (show lad) ++ " = " ++ (show rad)

type UnifSystem a t ss mpd pd fn v pmv fmv uv = [UnifEquation a t ss mpd pd fn v pmv fmv uv]
data FullUnifSystem a t ss mpd pd fn v pmv fmv uv = USys {us_sig :: SOSignature mpd pd fn v pmv fmv, us_eqs :: UnifSystem a t ss mpd pd fn v pmv fmv uv}

instance (Show (AtomDependant a t s mpd pd fn v pmv fmv uv), Show (TermDependant t fn v fmv uv), Show mpd, Show pd, Show fn, Show v, Show pmv, Show fmv, Show uv) => Show (FullUnifSystem a t s mpd pd fn v pmv fmv uv) where
	show usys = (show (us_eqs usys)) ++ "\n with signature {" ++ (show (us_sig usys)) ++ "}"



-- We make the choice here to only worry about second-order variables. This simplifies quite a few things.
-- However, if we find it absolutely necessary, it shouldn't be incredibly hard to include first-order variables here.
data UnifSysSolution pd fn pmv fmv = UnifSysSolution {uss_fnsol :: fmv := GroundSOT fn, uss_pdsol :: pmv := GroundSOA pd fn} deriving Eq

check_ueq_usol :: ESMGUConstraintsALL a t ss mpd pd fn v pmv fmv uv => UnifSysSolution pd fn pmv fmv -> UnifEquation a t ss mpd pd fn v pmv fmv uv -> Bool
check_ueq_usol usol ueq = case (apply_usol usol ueq) of {TermUnif ltd rtd -> ltd == rtd; AtomUnif lad rad -> lad == rad}

check_usys_usol :: ESMGUConstraintsALL a t ss mpd pd fn v pmv fmv uv => UnifSysSolution pd fn pmv fmv -> UnifSystem a t ss mpd pd fn v pmv fmv uv -> Bool
check_usys_usol usol usys = all (check_ueq_usol usol) usys

instance (Show fmv, Show fn, Show pmv, Show pd) => Show (UnifSysSolution pd fn pmv fmv) where
	show (UnifSysSolution fnsol pdsol) = "\nFuncs: " ++ (show fnsol) ++ "\nPreds: " ++ (show pdsol) ++ "\n\n"

instance ESMGUConstraintsU t pd fn v fmv uv => Substitutable (TermDependant t fn v fmv uv) fmv (SOTerm fn fmv) where
	subst sov sot (TDDirect somw) = TDDirect (subst sov sot somw)
	subst sov sot (TDUnif uv td) = TDUnif uv (subst sov sot td)

instance ESMGUConstraintsU t pd fn v fmv uv => Substitutable (TermDependant t fn v fmv uv) fmv (GroundSOT fn) where
	subst sov sot (TDDirect somw) = TDDirect (subst sov sot somw)
	subst sov sot (TDUnif uv td) = TDUnif uv (subst sov sot td)

instance (ESMGUConstraintsU t pd fn v fmv uv, ESMGUConstraintsSS s, ESMGUConstraintsAMpd a mpd) => Substitutable (AtomDependant a t s mpd pd fn v pmv fmv uv) fmv (SOTerm fn fmv) where
	subst sov sot (ADDirect csoa) = ADDirect (subst sov sot csoa)
	subst sov sot (ADUnif uv ad) = ADUnif uv (subst sov sot ad)

instance (ESMGUConstraintsU t pd fn v fmv uv, ESMGUConstraintsSS s, ESMGUConstraintsAMpd a mpd) => Substitutable (AtomDependant a t s mpd pd fn v pmv fmv uv) fmv (GroundSOT fn) where
	subst sov sot (ADDirect csoa) = ADDirect (subst sov sot csoa)
	subst sov sot (ADUnif uv ad) = ADUnif uv (subst sov sot ad)

instance (ESMGUConstraintsU t pd fn v fmv uv, ESMGUConstraintsSS s, ESMGUConstraintsAMpd a mpd) => Substitutable (UnifEquation a t s mpd pd fn v pmv fmv uv) fmv (SOTerm fn fmv) where
	subst sov sot (TermUnif ltd rtd) = TermUnif (subst sov sot ltd) (subst sov sot rtd)
	subst sov sot (AtomUnif lad rad) = AtomUnif (subst sov sot lad) (subst sov sot rad)

instance (ESMGUConstraintsU t pd fn v fmv uv, ESMGUConstraintsSS s, ESMGUConstraintsAMpd a mpd) => Substitutable (UnifEquation a t s mpd pd fn v pmv fmv uv) fmv (GroundSOT fn) where
	subst sov sot (TermUnif ltd rtd) = TermUnif (subst sov sot ltd) (subst sov sot rtd)
	subst sov sot (AtomUnif lad rad) = AtomUnif (subst sov sot lad) (subst sov sot rad)

apply_usol :: Substitutable t fmv (GroundSOT fn) => UnifSysSolution pd fn pmv fmv -> t -> t
apply_usol usol = subst_all (uss_fnsol usol)

newtype SubstFMVESUnifDGSONode pd fn pmv fmv = SubFMV {fromSubstFMVESUnifDGSONode :: ESUnifDGSONode pd fn pmv fmv}
instance forall pd fn pmv fmv. Eq fmv => Substitutable (SubstFMVESUnifDGSONode pd fn pmv fmv) fmv fmv where
	subst fmv rfmv (SubFMV (FSONode sot)) = SubFMV (FSONode (subst fmv rsot sot)) where rsot = UVar rfmv :: SOTerm fn fmv
	subst fmv rfmv (SubFMV (PSONode soa)) = SubFMV (PSONode (subst fmv rsot soa)) where rsot = UVar rfmv :: SOTerm fn fmv

newtype SubstPMVESUnifDGSONode pd fn pmv fmv = SubPMV {fromSubstPMVESUnifDGSONode :: ESUnifDGSONode pd fn pmv fmv}
instance forall pd fn pmv fmv . Eq pmv => Substitutable (SubstPMVESUnifDGSONode pd fn pmv fmv) pmv pmv where
	subst pmv rpmv (SubPMV (FSONode sot)) = SubPMV (FSONode sot)
	subst pmv rpmv (SubPMV (PSONode soa)) = SubPMV (PSONode (subst pmv rpmv soa))


-- A system of equations is a highly implicit solution to a system of unification equations
instance (ESMGUConstraintsALL a t ss mpd pd fn v pmv fmv uv) => Implicit (FullUnifSystem a t ss mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv) where
	checkImplicit usys usol = checkImplicit resuvdg usol where sig = us_sig usys; resuvdg = doRESUnifVDGraph sig (dgraph_from_usys sig (us_eqs usys))
	enumImplicit usys = enumImplicit resuvdg where sig = us_sig usys; resuvdg = doRESUnifVDGraph sig (dgraph_from_usys sig (us_eqs usys))

-- This is really just a fold but whatever.
dgraph_from_usys :: ESMGUConstraintsALL a t ss mpd pd fn v pmv fmv uv => SOSignature mpd pd fn v pmv fmv -> UnifSystem a t ss mpd pd fn v pmv fmv uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) ()
dgraph_from_usys sig [] = pass
dgraph_from_usys sig (eq:eqs) = dgraph_from_ueq sig eq >> dgraph_from_usys sig eqs

dgraph_from_ueq :: ESMGUConstraintsALL a t ss mpd pd fn v pmv fmv uv => SOSignature mpd pd fn v pmv fmv -> UnifEquation a t ss mpd pd fn v pmv fmv uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) ()
dgraph_from_ueq sig (TermUnif ltd rtd) = do
	{
		ln <- grab_fonode ltd;
		rn <- grab_fonode rtd;
		
		mzoom lens_esunifdgraph_dgraph (mergeEqDGFONodes ln rn);

		pass
	}
dgraph_from_ueq sig (AtomUnif lad rad) = do
	{
		-- We consider the FirstSOAAtom case separately here.
		let {(lus,lcs) = decompose_ad lad; (rus,rcs) = decompose_ad rad};
		case lcs of
		{
			FSOAtom (FirstSOAAtom lfsoa) -> case rcs of
			{
				FSOAtom (FirstSOAAtom rfsoa) -> do
				{
					let {(lmpd,lmt) = unbuild_term lfsoa; (rmpd,rmt) = unbuild_term rfsoa};
					if ((lmpd /= rmpd) || ((length lmt) /= (length rmt))) then (failVDGraphTrace True "Fail because meta-atom heads or length of arguments do not match") else do
					{
						let {mb_matches = uncurry zipMatch <$> (zip lmt rmt)};
						let {fpair = (\(lsoa :: SOAtom pd fn pmv fmv,rsoa :: SOAtom pd fn pmv fmv) -> do
							{
								-- SOAtom pd fn pmv fmv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) (ESUnifRelSoId s t pd fn v pmv fmv uv)
								ln <- grab_asonode lsoa;
								rn <- grab_asonode rsoa;

								-- ln, rn :: ESUnifRelSoId s t pd fn v pmv fmv uv
								-- mergeEqDGSONodes :: EqDGRelSoId s fot sot -> EqDGRelSoId s fot sot -> StateT (EqDGraph s fot sot) (ST s) (EqDGRelSoId s fot sot)
								-- mergeEqDGSONodes :: EqDGRelSoId s (TermDependant t fn v fmv uv) (ESUnifDGSONode pd fn pmv fmv) -> EqDGRelSoId s (TermDependant t fn v fmv uv) (ESUnifDGSONode pd fn pmv fmv) -> StateT (EqDGraph s (TermDependant t fn v fmv uv) (ESUnifDGSONode pd fn pmv fmv))
								
								mzoom lens_esunifdgraph_dgraph (mergeEqDGSONodes ln rn);

								pass
							})};						
						let {feither = (\ei -> case ei of
							{
								-- They are exactly the same. Then, no need to do anything in the graph. The equation is satisfied.
								Left _ -> pass;
								Right pair -> fpair pair;
							})};
						let {fmbmatch = (\mb_match -> case mb_match of
						{
							-- No match: Fail.
							Nothing -> failVDGraphTrace True "Fail because meta-atom arguments do not match";
							-- Match: Apply the equations.
							Just rst -> do {traverse feither rst; pass}
						})};
						do {traverse fmbmatch mb_matches; pass}
					}
				};
				NSOAtom _ -> failVDGraphTrace True "Fail because trying to match meta-atom with regular atom"
			};
			NSOAtom lsoa -> case rcs of
			{
				FSOAtom _ -> failVDGraphTrace True "Fail because trying to match regular atom with meta-atom";
				NSOAtom rsoa -> do
				{
					ln <- grab_afonode lad;
					rn <- grab_afonode rad;

					mzoom lens_esunifdgraph_dgraph (mergeEqDGFONodes ln rn);

					pass
				}
			}
		}
	}


type ESMGUConstraints t pd fn v sov = (Ord sov, SimpleTerm t, Eq fn, HasArity fn, HasArity sov, ChangeArity sov, Functor (t (SOTerm fn sov)), Functor (t fn), Bifunctor t, Traversable (t (GroundSOT fn)), Unifiable (t (SOTerm fn sov)), Variabilizable v, Variable v, Variabilizable sov, Variable sov, Ord v, Functor (t (GroundSOT fn)), Eq (t fn (Fix (t fn))), Show sov, Show fn, Show v, Show (t (SOTerm fn sov) (UTerm (t (SOTerm fn sov)) v)), Show (t (GroundSOT fn) (UTerm (t (GroundSOT fn)) v)), Ord fn, Ord (t (SOTerm fn sov) (UTerm (t (SOTerm fn sov)) v)))





-- We work with a clear mapping between levels and unifier variables. This makes things a lot easier.
type ESMGUConstraintsU t pd fn v sov uv = (ESMGUConstraints t pd fn v sov, Show uv, Ord uv, Variable uv, Variabilizable uv)
type ESMGUConstraintsPdPmv pd pmv = (Ord pd, Ord pmv, Eq pd, Eq pmv, Show pmv, Show pd, HasArity pd, HasArity pmv, Variable pmv, Variabilizable pmv, ChangeArity pmv)
type ESMGUConstraintsFnFmv fn fmv = (Ord fn, Ord fmv, Eq fn, Eq fmv, Show fmv, Show fn, HasArity fn, HasArity fmv, Variable fmv, Variabilizable fmv, ChangeArity fmv)
type ESMGUConstraintsPdFnPmvFmv pd fn pmv fmv = (ESMGUConstraintsPdPmv pd pmv, ESMGUConstraintsFnFmv fn fmv)
type ESMGUConstraintsUPmv t pd fn v pmv fmv uv = (ESMGUConstraintsU t pd fn v fmv uv, ESMGUConstraintsPdPmv pd pmv)
type ESMGUConstraintsA a = (SimpleTerm a)
type ESMGUConstraintsAMpd a mpd = (ESMGUConstraintsA a, Functor (a mpd), Eq mpd, Ord mpd)
type ESMGUConstraintsSS ss = (Functor ss, Unifiable ss)
type ESMGUConstraintsAMpdSs a t ss mpd pd fn v pmv fmv = (ESMGUConstraints t pd fn v fmv, ESMGUConstraintsSS ss, ESMGUConstraintsAMpd a mpd, Eq (a mpd (ss (SOAtom pd fn pmv fmv))), Eq (a (SOAtom pd fn pmv fmv) (SOMetawrap t fn v fmv)), ESMGUConstraintsPdPmv pd pmv, Show (a mpd (ss (SOAtom pd fn pmv fmv))), Show (a (SOAtom pd fn pmv fmv) (SOMetawrap t fn v fmv)))
type ESMGUConstraintsALL a t ss mpd pd fn v pmv fmv uv = (ESMGUConstraintsU t pd fn v fmv uv, ESMGUConstraintsAMpdSs a t ss mpd pd fn v pmv fmv)

-- As first order nodes we use TermDependants, but we use empty ones for atoms, since we do not have atom variables anyway.
data ESUnifDGSONode pd fn pmv fmv = FSONode (SOTerm fn fmv) | PSONode (SOAtom pd fn pmv fmv) deriving (Ord, Eq)

is_fsonode :: ESUnifDGSONode pd fn pmv fmv -> Bool
is_fsonode (FSONode _) = True
is_fsonode _ = False

from_fsonode :: ESUnifDGSONode pd fn pmv fmv -> SOTerm fn fmv
from_fsonode (FSONode x) = x
from_fsonode _ = error "Trying to extract a function node from a predicate node"

is_psonode :: ESUnifDGSONode pd fn pmv fmv -> Bool
is_psonode (PSONode _) = True
is_psonode _ = False

from_psonode :: ESUnifDGSONode pd fn pmv fmv -> SOAtom pd fn pmv fmv
from_psonode (PSONode x) = x
from_psonode _ = error "Trying to extract a predicate node from a function node"

instance (HasArity fn, HasArity pd, HasArity fmv, HasArity pmv) => HasArity (ESUnifDGSONode pd fn pmv fmv) where
	arity (FSONode sot) = arity sot
	arity (PSONode soa) = arity soa

type ESUnifDGraph s t pd fn v pmv fmv uv = EqDGraph s (TermDependant t fn v fmv uv) (ESUnifDGSONode pd fn pmv fmv)
type ESUnifRelFoId s t pd fn v pmv fmv uv = EqDGRelFoId s (TermDependant t fn v fmv uv) (ESUnifDGSONode pd fn pmv fmv)
type ESUnifRelSoId s t pd fn v pmv fmv uv = EqDGRelSoId s (TermDependant t fn v fmv uv) (ESUnifDGSONode pd fn pmv fmv)
data ESUnifVFoEdge s t pd fn v pmv fmv uv = ESUnifVFoEdge {esunifvfoedge_source :: ESUnifRelFoId s t pd fn v pmv fmv uv, esunifvfoedge_target :: ESUnifRelFoId s t pd fn v pmv fmv uv, esunifvfoedge_level :: uv}

instance (Show (SOTerm fn fmv), Show (SOAtom pd fn pmv fmv)) => Show (ESUnifDGSONode pd fn pmv fmv) where
	show (FSONode x) = show x
	show (PSONode x) = show x

eqUnifVFoEdge :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifVFoEdge s t pd fn v pmv fmv uv -> ESUnifVFoEdge s t pd fn v pmv fmv uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) Bool
eqUnifVFoEdge e1 e2 = (mzoom (lens_esunifdgraph_dgraph) (eqSTRelativeEqDGFoIds s1 s2)) >>= (\v1 -> if v1 then (mzoom (lens_esunifdgraph_dgraph) (eqSTRelativeEqDGFoIds t1 t2)) else (return False)) where s1 = esunifvfoedge_source e1; t1 = esunifvfoedge_target e1; s2 = esunifvfoedge_source e2; t2 = esunifvfoedge_target e2

mshow_esunifvfoedge :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifVFoEdge s t pd fn v pmv fmv uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) String
mshow_esunifvfoedge e = do
	{
		let {s = esunifvfoedge_source e; t = esunifvfoedge_target e; uv = esunifvfoedge_level e};
		
		sid <- mzoom lens_esunifdgraph_dgraph (getSTRelativeEqDGFoId s);
		tid <- mzoom lens_esunifdgraph_dgraph (getSTRelativeEqDGFoId t);

		return ("[" ++ (show uv) ++ "]: " ++ (show sid) ++ " -> " ++ (show tid))
	}

-- Nothing indicates that it's at the base (no unifier) level.
-- This function is inherently flawed in the whole approach to the algorithm that we have currently: It is possible, through constants, that nodes have different unifier levels in them at the same time.
{-|
getEqDGLevel :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifRelFoId s t pd fn v pmv fmv uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) (Maybe uv)
getEqDGLevel n = do
	{
		mb_td <- mzoom lens_esunifdgraph_dgraph (getSTRelativeEqDGFoCoId n);
		case mb_td of
		{
			Just (TDDirect _) -> return Nothing;
			Just (TDUnif uv _) -> return (Just uv);
			Nothing -> do
			{
				-- If it does not have dependants, then it must have incoming horizontal edges. Anything else is absolutely incorrect, and should never happen. We signal it with an error.
				-- WAS: "We assume that all sources of all incoming horizontal edges have the same level, so we just pick an arbitrary one."
				-- The above is WRONG. But only when some of these have the base level. A node can have incoming edges from the base level and incoming edges from other levels. Its level is the non-base level.
				ines <- mzoom lens_esunifdgraph_dgraph (st_searchInEqDGFOEdges [] [] n);
				case ines of
				{
					[] -> do
					{
						str <- show_esuvdg;
						gtraceM False str;
						error "Trying to get the unifier level of a node with no dependants and no incoming horizontal edges!!";
					};
					_ -> do
					{
						sss <- concat <$> mzoom lens_esunifdgraph_dgraph (traverse eqDGFOEdge_sources ines);
						case sss of
						{
							-- Extreme case: No sources. So it is a constant function. We determine the level based on incoming vertical edges.
							[] -> do
							{
								invs <- inVFoEdges n;
								case invs of
								{
									[] -> return Nothing;
									((ESUnifVFoEdge _ _ uv):_) -> return (Just uv)
								}
							};
							-- Here we find an edge with a level that is not base, or rely on vertical edges.
							ss -> do
							{
								slvls <- traverse getEqDGLevel ss;
								let {aslvls = Prelude.filter isJust slvls};
								if (Prelude.null aslvls) then do
								{
									invs <- inVFoEdges n;
									case invs of
									{
										[] -> return Nothing;
										((ESUnifVFoEdge _ _ uv):_) -> return (Just uv)
									}
								}
								else do
								{
									return (head aslvls)
								}
							}
						}
					}
				}
			} 
		}
	}
|-}

-- The levels are assumed ordered and correctly indexed, so that 0-indexed level contains elements with no unifier variables, 1-indexed level contains elements with only the first unifier variable, and so on.
-- The failed flag is a flag that indicates that something before already noted that this graph has no solutions. We should check it when it makes sense.
data ESUnifVDGraph s t mpd pd fn v pmv fmv uv = ESUnifVDGraph {esunifdgraph :: ESUnifDGraph s t pd fn v pmv fmv uv, esunifdgraph_vfoedges :: [ESUnifVFoEdge s t pd fn v pmv fmv uv], esunifdgraph_sosig :: SOSignature mpd pd fn v pmv fmv, esunifdgraph_failed :: Bool}

lens_esunifdgraph_vfoedges :: Lens' (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) [ESUnifVFoEdge s t pd fn v pmv fmv uv]
lens_esunifdgraph_vfoedges f esudg = fmap (\rvfoes -> ESUnifVDGraph (esunifdgraph esudg) rvfoes (esunifdgraph_sosig esudg) (esunifdgraph_failed esudg)) (f (esunifdgraph_vfoedges esudg))

lens_esunifdgraph_dgraph :: Lens' (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ESUnifDGraph s t pd fn v pmv fmv uv)
lens_esunifdgraph_dgraph f esudg = fmap (\rdgraph -> ESUnifVDGraph rdgraph (esunifdgraph_vfoedges esudg) (esunifdgraph_sosig esudg) (esunifdgraph_failed esudg)) (f (esunifdgraph esudg))

lens_esunifdgraph_sosig :: Lens' (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (SOSignature mpd pd fn v pmv fmv)
lens_esunifdgraph_sosig f esudg = fmap (\rsosig -> ESUnifVDGraph (esunifdgraph esudg) (esunifdgraph_vfoedges esudg) rsosig (esunifdgraph_failed esudg)) (f (esunifdgraph_sosig esudg))

lens_esunifdgraph_failed :: Lens' (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) Bool
lens_esunifdgraph_failed f esudg = fmap (\rfailed -> ESUnifVDGraph (esunifdgraph esudg) (esunifdgraph_vfoedges esudg) (esunifdgraph_sosig esudg) rfailed) (f (esunifdgraph_failed esudg))

emptyVDGraph :: SOSignature mpd pd fn v pmv fmv -> ESUnifVDGraph s t mpd pd fn v pmv fmv uv
emptyVDGraph sosig = ESUnifVDGraph emptyEqDG [] sosig False

emptyRESUnifVDGraph :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => SOSignature mpd pd fn v pmv fmv -> RESUnifVDGraph t mpd pd fn v pmv fmv uv
emptyRESUnifVDGraph sosig = doRESUnifVDGraph sosig (put (emptyVDGraph sosig))

-- For now, we keep the old graph just in case there are some things we need to see from it or something.
failVDGraph :: StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) ()
failVDGraph = do
	{
		esuvdg <- get;
		put (lens_esunifdgraph_failed .~ True $ esuvdg)
	}

failVDGraphTrace :: Bool -> String -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) ()
failVDGraphTrace flag str = gtrace flag str failVDGraph

failedRESUnifVDGraph :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => SOSignature mpd pd fn v pmv fmv -> RESUnifVDGraph t mpd pd fn v pmv fmv uv
failedRESUnifVDGraph sig = doRESUnifVDGraph sig failVDGraph

show_esuvdg :: (ESMGUConstraintsUPmv t pd fn v pmv fmv uv) => StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) String
show_esuvdg = do
	{
		esuvdg <- get;
		let {dgraph = show_eqdgraph (esunifdgraph esuvdg); sfailed = show (esunifdgraph_failed esuvdg)};
		vedges <- show_esuvdg_vedges;		
		return ("Horizontal:\n\n" ++ dgraph ++ "\n\nVertical:\n\n" ++ vedges ++ "\n\nFailed: " ++ sfailed)
	}

show_esuvdg_vedges :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) String
show_esuvdg_vedges = StateT (\vdg -> ((_2) ..~ (\dg -> ESUnifVDGraph dg (esunifdgraph_vfoedges vdg) (esunifdgraph_sosig vdg) (esunifdgraph_failed vdg))) <$> (f_show_esuvdg_vedges (esunifdgraph vdg) (esunifdgraph_vfoedges vdg)))

f_show_esuvdg_vedges :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifDGraph s t pd fn v pmv fmv uv -> [ESUnifVFoEdge s t pd fn v pmv fmv uv] -> ST s (String,ESUnifDGraph s t pd fn v pmv fmv uv)
f_show_esuvdg_vedges dg [] = return ("",dg)
f_show_esuvdg_vedges dg (e:es) = do {(estr,dg2) <- f_show_esuvdg_vedge dg e; (esstr,dg3) <- f_show_esuvdg_vedges dg2 es; return (estr ++ "\n" ++ esstr,dg3)}

f_show_esuvdg_vedge :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifDGraph s t pd fn v pmv fmv uv -> ESUnifVFoEdge s t pd fn v pmv fmv uv -> ST s (String,ESUnifDGraph s t pd fn v pmv fmv uv)
f_show_esuvdg_vedge dg e = do {let {s = esunifvfoedge_source e; t = esunifvfoedge_target e}; (mb_sfot,dg2) <- runStateT (getSTRelativeEqDGFoCoId s) dg; (mb_tfot,dg3) <- runStateT (getSTRelativeEqDGFoCoId t) dg2; let {sstr = if (isNothing mb_sfot) then "()" else (show (fromJust mb_sfot)); tstr = if (isNothing mb_tfot) then "()" else (show (fromJust mb_tfot))}; return (sstr ++ " -> " ++ tstr,dg3)}

-- Dealing with vertical edges
-- The edge is added anyway. If it already existed, this is a mistake, but it should be dealt with at a higher level.
-- Note that we ensure that the nodes exist in the graph when doing this.
addVFoEdge :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifRelFoId s t pd fn v pmv fmv uv -> ESUnifRelFoId s t pd fn v pmv fmv uv -> uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) (ESUnifVFoEdge s t pd fn v pmv fmv uv)
addVFoEdge s t uv = mzoom lens_esunifdgraph_dgraph (do {mb_sfot <- getSTRelativeEqDGFoCoId s; mb_tfot <- getSTRelativeEqDGFoCoId t; if (isJust mb_sfot) then (newEqDGFONode (fromJustErr "addVFoEdge sfot" mb_sfot)) else pass; if (isJust mb_tfot) then (newEqDGFONode (fromJustErr "addVFoEdge tfot" mb_tfot)) else pass}) >> (StateT (f_addVFoEdge s t uv))

f_addVFoEdge :: ESUnifRelFoId s t pd fn v pmv fmv uv -> ESUnifRelFoId s t pd fn v pmv fmv uv -> uv -> (ESUnifVDGraph s t mpd pd fn v pmv fmv uv -> ST s (ESUnifVFoEdge s t pd fn v pmv fmv uv, ESUnifVDGraph s t mpd pd fn v pmv fmv uv))
f_addVFoEdge s t uv esuvdg = return (ve, lens_esunifdgraph_vfoedges ..~ (ve:) $ esuvdg) where ve = ESUnifVFoEdge s t uv

-- When we delete, we delete all copies of that edge. There should only really be one, but you can never be safe enough.
deleteVFoEdge :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifRelFoId s t pd fn v pmv fmv uv -> ESUnifRelFoId s t pd fn v pmv fmv uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) ()
deleteVFoEdge s t = StateT (f_deleteVFoEdge s t)

f_deleteVFoEdge :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifRelFoId s t pd fn v pmv fmv uv -> ESUnifRelFoId s t pd fn v pmv fmv uv -> (ESUnifVDGraph s t mpd pd fn v pmv fmv uv -> ST s ((),ESUnifVDGraph s t mpd pd fn v pmv fmv uv))
f_deleteVFoEdge s t esudg = tocombine <$> (runStateT st_res esudg) where fe = ESUnifVFoEdge s t (error "The unifier variable should be irrelevant when deleting a vertical edge"); es = esunifdgraph_vfoedges esudg; tofold = (\e -> \rstes -> rstes >>= (\res -> (\rb -> if rb then res else (e:res)) <$> (eqUnifVFoEdge e fe))); st_res = Prelude.foldr tofold (return []) es; tocombine = (\(rres,resudg) -> ((),lens_esunifdgraph_vfoedges .~ rres $ resudg))


-- Check if a vertical edge exists.
checkVFoEdge :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifRelFoId s t pd fn v pmv fmv uv -> ESUnifRelFoId s t pd fn v pmv fmv uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) Bool
checkVFoEdge s t = StateT (f_checkVFoEdge s t)

f_checkVFoEdge :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifRelFoId s t pd fn v pmv fmv uv -> ESUnifRelFoId s t pd fn v pmv fmv uv -> (ESUnifVDGraph s t mpd pd fn v pmv fmv uv -> ST s (Bool,ESUnifVDGraph s t mpd pd fn v pmv fmv uv))
f_checkVFoEdge s t esudg = runStateT st_rb esudg where fe = ESUnifVFoEdge s t (error "The unifier variable should be irrelevant when checking a vertical edge"); es = esunifdgraph_vfoedges esudg; tofold = (\e -> \rstb -> rstb >>= (\rb -> if rb then (return True) else (eqUnifVFoEdge e fe))); st_rb = Prelude.foldr tofold (return False) es

outVFoEdges :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifRelFoId s t pd fn v pmv fmv uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) [ESUnifVFoEdge s t pd fn v pmv fmv uv]
outVFoEdges s = StateT (f_outVFoEdges s)

f_outVFoEdges :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifRelFoId s t pd fn v pmv fmv uv -> (ESUnifVDGraph s t mpd pd fn v pmv fmv uv -> ST s ([ESUnifVFoEdge s t pd fn v pmv fmv uv],ESUnifVDGraph s t mpd pd fn v pmv fmv uv))
f_outVFoEdges s esudg = runStateT (monadfilter tofilter es) esudg where es = esunifdgraph_vfoedges esudg; tofilter = (\e -> mzoom lens_esunifdgraph_dgraph (eqSTRelativeEqDGFoIds (esunifvfoedge_source e) s))

singleOutVFoEdge :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => uv -> ESUnifRelFoId s t pd fn v pmv fmv uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) (ESUnifVFoEdge s t pd fn v pmv fmv uv)
singleOutVFoEdge uv s = do
	{
		esudg <- get;
		let {es = esunifdgraph_vfoedges esudg};
		let {tofilter = (\e -> (mzoom lens_esunifdgraph_dgraph (eqSTRelativeEqDGFoIds (esunifvfoedge_source e) s)) >>=& (return ((esunifvfoedge_level e) == uv)))};

		ves <- monadfilter tofilter es;
		
		-- If there is more than one edge, we assume that their targets are all the same. Maybe this could be handled better by removing duplicates, but we will go with this for now.
		--if ((length ves) > 1) then (error "More than one outgoing vertical edge with the same unifier level found!") else
		if (Prelude.null ves) then do
		{
			-- It is empty: Create it.
			t <- mzoom lens_esunifdgraph_dgraph newAnonEqDGFONode;
			ve <- addVFoEdge s t uv;

			return ve
		}
		else (return (head ves))		
	}

inVFoEdges :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifRelFoId s t pd fn v pmv fmv uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) [ESUnifVFoEdge s t pd fn v pmv fmv uv]
inVFoEdges t = StateT (f_inVFoEdges t)

f_inVFoEdges :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifRelFoId s t pd fn v pmv fmv uv -> (ESUnifVDGraph s t mpd pd fn v pmv fmv uv -> ST s ([ESUnifVFoEdge s t pd fn v pmv fmv uv],ESUnifVDGraph s t mpd pd fn v pmv fmv uv))
f_inVFoEdges t esudg = runStateT (monadfilter tofilter es) esudg where es = esunifdgraph_vfoedges esudg; tofilter = (\e -> mzoom lens_esunifdgraph_dgraph (eqSTRelativeEqDGFoIds (esunifvfoedge_target e) t))


-- We assume and ensure that a vertical edge is always between two dependants only one unifier variable in difference
factorizeVFoEdge :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifVFoEdge s t pd fn v pmv fmv uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) uv
factorizeVFoEdge e = do
	{
		return (esunifvfoedge_level e);
	}

divideOverVFoEdge :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifVFoEdge s t pd fn v pmv fmv uv -> ESUnifRelFoId s t pd fn v pmv fmv uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) (ESUnifRelFoId s t pd fn v pmv fmv uv)
divideOverVFoEdge e sid = do
	{
		mb_std <- mzoom lens_esunifdgraph_dgraph (getSTRelativeEqDGFoCoId sid);
		uv <- factorizeVFoEdge e;

		case mb_std of
		{
			Just std -> return (relbwEqDGFoId (TDUnif uv std));
			Nothing -> do
			{
				ve <- singleOutVFoEdge uv sid;
				let {t = esunifvfoedge_target ve};

				return t
			}
		}
	}

divideDepOverVFoEdge :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifVFoEdge s t pd fn v pmv fmv uv -> TermDependant t fn v fmv uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) (TermDependant t fn v fmv uv)
divideDepOverVFoEdge e fot = do {uv <- factorizeVFoEdge e; return (TDUnif uv fot)}

mergeRESUnifVDGraph :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => SOSignature mpd pd fn v pmv fmv -> RESUnifVDGraph t mpd pd fn v pmv fmv uv -> RESUnifVDGraph t mpd pd fn v pmv fmv uv -> RESUnifVDGraph t mpd pd fn v pmv fmv uv
mergeRESUnifVDGraph sig resuvdg1 resuvdg2 = doRESUnifVDGraph sig rresuvdg -- Note that passing the big signature to this should be no problem, since it's overwritten with the signature of the merge.
	where
		rresuvdg = mergeESUnifVDGraph sig (unRESUnifVDGraph resuvdg1) (unRESUnifVDGraph resuvdg2)		

-- Merges g1 unto g2
-- The given signature indicates the elements that are common to both. Anything appearing in the signatures of the respective graphs will be standardised away.
-- The resulting signature will reflect this as well
-- data ESUnifVDGraph s t mpd pd fn v pmv fmv uv = ESUnifVDGraph {esunifdgraph :: ESUnifDGraph s t pd fn v pmv fmv uv, esunifdgraph_vfoedges :: [ESUnifVFoEdge s t pd fn v pmv fmv uv], esunifdgraph_sosig :: SOSignature mpd pd fn v pmv fmv, esunifdgraph_failed :: Bool}
mergeESUnifVDGraph :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => SOSignature mpd pd fn v pmv fmv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) x -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) y -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) ()
mergeESUnifVDGraph sig g1 g2 = do
	{
		st <- get;
		withLeftStateT (do
			{				
				onLeftStateT $ g1;
				onRightStateT $ g2;	

				gtraceM False "1";
				sg1 <- onLeftStateT $ get;
				sg2 <- onRightStateT $ get;

				let {sig1 = esunifdgraph_sosig sg1; sig2 = esunifdgraph_sosig sg2};
				let {(rsig, fsovars, fpvars) = mergeESUnifVDGraph_mergesigs sig sig1 sig2};

				let {fsovarsubsts = (\sov -> (sov,fsovars sov)); fpvarsubsts = (\pv -> (pv,fpvars pv)); sovars1 = sovars sig1; pvars1 = pvars sig1; sovarsubsts = fromList . list_from_enum $ fsovarsubsts <$> sovars1; pvarsubsts = fromList . list_from_enum $ fpvarsubsts <$> pvars1};

				let {sovars2 = sovars sig2; csovars = sovars sig};

				gtraceM False "CSOVARS";
				gtraceM False (show csovars);
				gtraceM False "SOVARS2";
				gtraceM False (show sovars2);
				gtraceM False "SOVARS1";
				gtraceM False (show sovars1);
				gtraceM False "PVARS1";
				gtraceM False (show pvars1);
				gtraceM False "SOVARSUBSTS";
				gtraceM False (show sovarsubsts);
				gtraceM False "PVARSUBSTS";
				gtraceM False (show pvarsubsts);
				
				let {eqdg1 = esunifdgraph sg1; foelements1 = eqdg_foelements eqdg1; fonodes1 = get_fonode_ids (eqdgraph eqdg1); soelements1 = eqdg_soelements eqdg1; sonodes1 = get_sonode_ids (eqdgraph eqdg1)};
				-- Find the maximum unifier variable on 2, and shift all the unifier variables in 1 after that one.
				let {maxuv = mergeESUnifVDGraph_maxuv (snd <$> toList foelements1)};
				-- Move over all the nodes and the elements they contain.								
				gtraceM False "2";
				rfoidpairs <- traverse (mergeESUnifVDGraph_ffonode maxuv foelements1) fonodes1;
				rsoidpairs <- traverse (mergeESUnifVDGraph_fsonode sovarsubsts pvarsubsts soelements1) sonodes1;
				show1 <- onRightStateT $ show_esuvdg;
				gtraceM False "SHOW1";
				gtraceM False show1;
				gtraceM False "SOIDPAIRS";
				gtraceM False (show rsoidpairs);
				gtraceM False "3";
				let {rfoids = fromList rfoidpairs; rsoids = fromList rsoidpairs};
				-- Move over horizontal edges.				
				traverse (mergeESUnifVDGraph_fsonodeedges rfoids rsoids) sonodes1;
				show2 <- onRightStateT $ show_esuvdg;
				gtraceM False "SHOW2";
				gtraceM False show2;
				-- Move over vertical edges.
				gtraceM False "4";
				let {vfoedges1 = esunifdgraph_vfoedges sg1};				
				traverse (mergeESUnifVDGraph_vfoedge maxuv rfoids) vfoedges1;
				-- Finally, check the failed flag. We maybe should do this first and avoid the rest if it's a fail?
				show3 <- onRightStateT $ show_esuvdg;
				gtraceM False "SHOW3";
				gtraceM False show3;
				gtraceM False "5";
				let {failed1 = esunifdgraph_failed sg1};
				sg2 <- onRightStateT $ get;
				let {rsg2 = lens_esunifdgraph_failed ..~ (failed1 ||) $ sg2};
				-- Don't forget the signature!
				let {rsgsig = lens_esunifdgraph_sosig .~ rsig $ rsg2};
				onRightStateT $ put rsgsig;

				gtraceM False "6";
				
				pass
			}) st;
		pass;
	}

-- We only actually merge meta-variables, everything else we assume is joint and the same. This is important!
mergeESUnifVDGraph_mergesigs :: (Variable pmv, Variable fmv, Variabilizable pmv, Variabilizable fmv) => SOSignature mpd pd fn v pmv fmv -> SOSignature mpd pd fn v pmv fmv -> SOSignature mpd pd fn v pmv fmv -> (SOSignature mpd pd fn v pmv fmv, fmv -> fmv, pmv -> pmv)
mergeESUnifVDGraph_mergesigs csig sig1 sig2 = (SOSignature (Signature cpreds cfuncs cvars) rsovars rpvars csopreds, fsovars, fpvars)
	where
		cpreds = preds . fosig $ csig;
		cfuncs = funcs . fosig $ csig;
		cvars = vars . fosig $ csig;
		csovars = sovars csig;
		sovars1 = sovars sig1;
		sovars2 = sovars sig2;
		cpvars = pvars csig;
		pvars1 = pvars sig1;
		pvars2 = pvars sig2;
		csopreds = sopreds csig;
		sopreds1 = sopreds sig1;
		sopreds2 = sopreds sig2;
		(rsovars,fsovars) = mergeESUnifVDGraph_mergevars csovars sovars1 sovars2;
		(rpvars,fpvars) = mergeESUnifVDGraph_mergevars cpvars pvars1 pvars2

mergeESUnifVDGraph_mergevars :: forall v. (Variable v, Variabilizable v) => EnumProc v -> EnumProc v -> EnumProc v -> (EnumProc v,v -> v)
mergeESUnifVDGraph_mergevars cvs vs1 vs2 = (enub (vs2 ..+ (ff <$> vs1)), ff)
	where
		maxvid = maximum (getVarID <$> vs2);
		ff = (\v -> if (uns_produce_next (eelem v cvs)) then v else (update_var (+(maxvid+1)) v))

mergeESUnifVDGraph_maxuv :: (Variable uv, Ord uv) => [[TermDependant t fn v fmv uv]] -> Int
mergeESUnifVDGraph_maxuv [] = 0
mergeESUnifVDGraph_maxuv ([]:tdss) = mergeESUnifVDGraph_maxuv tdss
mergeESUnifVDGraph_maxuv (((TDDirect _):tds):tdss) = mergeESUnifVDGraph_maxuv (tds:tdss)
mergeESUnifVDGraph_maxuv (((TDUnif uv _):tds):tdss) = max (getVarID uv) (mergeESUnifVDGraph_maxuv (tds:tdss))

mergeESUnifVDGraph_refreshfo :: (Variable uv, Ord uv, Variabilizable uv) => Int -> TermDependant t fn v fmv uv -> TermDependant t fn v fmv uv
mergeESUnifVDGraph_refreshfo maxuv (TDDirect x) = TDDirect x
mergeESUnifVDGraph_refreshfo maxuv (TDUnif uv x) = TDUnif (update_var (+(maxuv+1)) uv) (mergeESUnifVDGraph_refreshfo maxuv x)

mergeESUnifVDGraph_vfoedge :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => Int -> Map Int Int -> ESUnifVFoEdge s t pd fn v pmv fmv uv -> TwoStateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) ()
mergeESUnifVDGraph_vfoedge maxuv nmap ve = do
	{
		let {s = esunifvfoedge_source ve; t = esunifvfoedge_target ve; uv = esunifvfoedge_level ve};

		rs <- mergeESUnifVDGraph_getrfonode nmap s;
		rt <- mergeESUnifVDGraph_getrfonode nmap t;

		let {ruv = update_var (+(maxuv+1)) uv};

		onRightStateT $ addVFoEdge rs rt ruv;

		pass
	}

mergeESUnifVDGraph_ffonode :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => Int -> Map Int [TermDependant t fn v fmv uv] -> Int -> TwoStateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) (Int,Int)
mergeESUnifVDGraph_ffonode maxuv foelements1 nid = onRightStateT $ mzoom lens_esunifdgraph_dgraph $ do
	{
		let {fots = foelements1 !< nid $ []; rfots = mergeESUnifVDGraph_refreshfo maxuv <$> fots};
		n <- newAnonEqDGFONode;
		traverse (mergeESUnifVDGraph_mergefonode n) rfots;
		rnid <- getSTRelativeEqDGFoId n;

		return (nid,rnid);
	}

mergeESUnifVDGraph_mergefonode :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifRelFoId s t pd fn v pmv fmv uv -> TermDependant t fn v fmv uv -> StateT (ESUnifDGraph s t pd fn v pmv fmv uv) (ST s) ()
mergeESUnifVDGraph_mergefonode n fot = do
	{
		nfot <- newEqDGFONode fot;
		mergeEqDGFONodes n nfot;

		pass
	}

mergeESUnifVDGraph_fsonode :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => Map fmv fmv -> Map pmv pmv -> Map Int [ESUnifDGSONode pd fn pmv fmv] -> Int -> TwoStateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) (Int,Int)
mergeESUnifVDGraph_fsonode sovarsubsts pvarsubsts soelements1 nid = onRightStateT $ mzoom lens_esunifdgraph_dgraph $ do
	{
		let {sots = soelements1 !< nid $ []};
		n <- newAnonEqDGSONode;

		let {rsots1 = fromSubstFMVESUnifDGSONode . subst_all sovarsubsts . SubFMV <$> sots; rsots2 = fromSubstPMVESUnifDGSONode . subst_all pvarsubsts . SubPMV <$> rsots1};

		traverse (mergeESUnifVDGraph_mergesonode n) rsots2;
		rnid <- getSTRelativeEqDGSoId n;

		return (nid,rnid);
	}

mergeESUnifVDGraph_mergesonode :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifRelSoId s t pd fn v pmv fmv uv -> ESUnifDGSONode pd fn pmv fmv -> StateT (ESUnifDGraph s t pd fn v pmv fmv uv) (ST s) ()
mergeESUnifVDGraph_mergesonode n sot = do
	{
		nsot <- newEqDGSONode sot;
		mergeEqDGSONodes n nsot;

		pass
	}


mergeESUnifVDGraph_getrfonode :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => Map Int Int -> ESUnifRelFoId s t pd fn v pmv fmv uv -> TwoStateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) (ESUnifRelFoId s t pd fn v pmv fmv uv)
mergeESUnifVDGraph_getrfonode nmap nrid = do
	{
		nid <- onLeftStateT $ mzoom lens_esunifdgraph_dgraph $ getSTRelativeEqDGFoId nrid;
		let {rid = nmap !< nid $ nid};
		eqdg <- onRightStateT $ mzoom lens_esunifdgraph_dgraph $ get;
		return (directEqDGFoId (getEqDGFORId eqdg rid))
	}

mergeESUnifVDGraph_getrsonode :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => Map Int Int -> ESUnifRelSoId s t pd fn v pmv fmv uv -> TwoStateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) (ESUnifRelSoId s t pd fn v pmv fmv uv)
mergeESUnifVDGraph_getrsonode nmap nrid = do
	{
		nid <- onLeftStateT $ mzoom lens_esunifdgraph_dgraph $ getSTRelativeEqDGSoId nrid;
		gtraceM False ("NID: " ++ (show nid));
		gtraceM False ("NMAP: " ++ (show nmap));
		let {rid = nmap !< nid $ nid};
		gtraceM False ("RID: " ++ (show rid));
		eqdg <- onRightStateT $ mzoom lens_esunifdgraph_dgraph $ get;
		return (directEqDGSoId (getEqDGSORId eqdg rid))
	}

mergeESUnifVDGraph_ffoedge :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => Map Int Int -> Map Int Int -> Int -> TwoStateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) ()
mergeESUnifVDGraph_ffoedge fonmap sonmap eid = do
	{
		ss <- onLeftStateT $ mzoom lens_esunifdgraph_dgraph $ eqDGFOEdge_sources eid;
		h <- onLeftStateT $ mzoom lens_esunifdgraph_dgraph $ eqDGFOEdge_head eid;
		t <- onLeftStateT $ mzoom lens_esunifdgraph_dgraph $ eqDGFOEdge_target eid;

		rss <- traverse (mergeESUnifVDGraph_getrfonode fonmap) ss;
		rh <- mergeESUnifVDGraph_getrsonode sonmap h;
		rt <- mergeESUnifVDGraph_getrfonode fonmap t;

		ssid <- onLeftStateT $ mzoom lens_esunifdgraph_dgraph $ traverse getSTRelativeEqDGFoId ss;
		hid <- onLeftStateT $ mzoom lens_esunifdgraph_dgraph $ getSTRelativeEqDGSoId h;
		tid <- onLeftStateT $ mzoom lens_esunifdgraph_dgraph $ getSTRelativeEqDGFoId t;

		rssid <- onRightStateT $ mzoom lens_esunifdgraph_dgraph $ traverse getSTRelativeEqDGFoId rss;
		rhid <- onRightStateT $ mzoom lens_esunifdgraph_dgraph $ getSTRelativeEqDGSoId rh;
		rtid <- onRightStateT $ mzoom lens_esunifdgraph_dgraph $ getSTRelativeEqDGFoId rt;

		gtraceM False ("SSID: " ++ (show ssid));
		gtraceM False ("HID: " ++ (show hid));
		gtraceM False ("TID: " ++ (show tid));
		gtraceM False ("RSSID: " ++ (show rssid));
		gtraceM False ("RHID: " ++ (show rhid));
		gtraceM False ("RTID: " ++ (show rtid));

		onRightStateT $ mzoom lens_esunifdgraph_dgraph $ newEqDGFOEdge rh rss rt;

		pass;
	}

mergeESUnifVDGraph_fsoedge :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => Map Int Int -> Int -> TwoStateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) ()
mergeESUnifVDGraph_fsoedge nmap eid = do
	{
		ss <- onLeftStateT $ mzoom lens_esunifdgraph_dgraph $ eqDGSOEdge_sources eid;
		h <- onLeftStateT $ mzoom lens_esunifdgraph_dgraph $ eqDGSOEdge_head eid;
		t <- onLeftStateT $ mzoom lens_esunifdgraph_dgraph $ eqDGSOEdge_target eid;

		rss <- traverse (mergeESUnifVDGraph_getrsonode nmap) ss;
		rh <- mergeESUnifVDGraph_getrsonode nmap h;
		rt <- mergeESUnifVDGraph_getrsonode nmap t;		

		onRightStateT $ mzoom lens_esunifdgraph_dgraph $ newEqDGSOEdge rh rss rt;

		pass;
	}


mergeESUnifVDGraph_fsonodeedges :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => Map Int Int -> Map Int Int -> Int -> TwoStateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) ()
mergeESUnifVDGraph_fsonodeedges fonmap sonmap hid = do
	{
		eqdg <- onLeftStateT $ mzoom lens_esunifdgraph_dgraph $ get;
		let {hrelid = directEqDGSoId (getEqDGSORId eqdg hid)};
		foeids <- onLeftStateT $ mzoom lens_esunifdgraph_dgraph $ st_searchAllHEqDGFOEdges [] [] hrelid;
		soeids <- onLeftStateT $ mzoom lens_esunifdgraph_dgraph $ st_searchAllHEqDGSOEdges [] [] hrelid;

		traverse (mergeESUnifVDGraph_ffoedge fonmap sonmap) foeids;
		traverse (mergeESUnifVDGraph_fsoedge sonmap) soeids;

		pass;
	}

-- Operation types for unification dependency graphs
-- We have two levels of operations.
-- The low level ones work directly on the graph itself and are for propagating changes until everything that needs to be done is done, in a relatively efficient manner. These are formalized with the Operable types.
-- The high level ones work on a graph with a normalization level and are for expressing things that we do when working with a dependency graph representation of a unification system. These are not formalized with the Operable types, and simply are a set of functions that can be used to navigate these normal types in different ways.

data ESUnifDGOp (s :: *) (t :: * -> * -> *) (mpd :: *) (pd :: *) (fn :: *) (v :: *) (pmv :: *) (fmv :: *) (uv :: *) = ESUVCommuteEqFo (ESUnifVFoEdge s t pd fn v pmv fmv uv) | ESUVCommuteFo (ESUnifVFoEdge s t pd fn v pmv fmv uv) | ESUVAlign (ESUnifRelFoId s t pd fn v pmv fmv uv) | ESUSOZip Int | ESUFOZip Int | ESUFOSimpProj Int | ESUSOSimpProj Int | ESUFODump Int | ESUSODump Int

instance Eq (ESUnifDGOp s t mpd pd fn v pmv fmv uv) where
	op1 == op2 = esunifdg_prio op1 == esunifdg_prio op2

instance Ord (ESUnifDGOp s t mpd pd fn v pmv fmv uv) where
	op1 <= op2 | esunifdg_prio op1 < esunifdg_prio op2 = True
	op1 <= op2 | esunifdg_prio op2 < esunifdg_prio op1 = False
	-- Default case for operations with no further comparisons.
	op1 <= op2 = True

esunifdg_prio :: (ESUnifDGOp s t mpd pd fn v pmv fmv uv) -> Int
esunifdg_prio (ESUVCommuteEqFo _) = 80
esunifdg_prio (ESUVCommuteFo _) = 100
esunifdg_prio (ESUVAlign _) = 50
esunifdg_prio (ESUSOZip _) = 300
esunifdg_prio (ESUFOZip _) = 500
esunifdg_prio (ESUSOSimpProj _) = 800
esunifdg_prio (ESUFOSimpProj _) = 1000
esunifdg_prio (ESUSODump _) = 1300
esunifdg_prio (ESUFODump _) = 1500

-- IMPORTANT NOTE: We do not do this for now, but it may be a good idea to ensure correctness to run vertical alignment before any other operation to ensure that it is there. This rule is assumed to always be exhausted.
instance ESMGUConstraintsUPmv t pd fn v pmv fmv uv => StateTOperation (ST s) (ESUnifDGOp s t mpd pd fn v pmv fmv uv) (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) where
	runStateTOp (ESUVCommuteEqFo foe) = do {foestr <- mshow_esunifvfoedge foe; gtraceM False ("VCommuteEq: " ++ foestr); esuvdg <- show_esuvdg; gtraceM False esuvdg; esu_vertical_commute_eq_fo_edge foe}
	runStateTOp (ESUVCommuteFo foe) = do {foestr <- mshow_esunifvfoedge foe; gtraceM False ("VCommute: " ++ foestr); esuvdg <- show_esuvdg; gtraceM False esuvdg; esu_vertical_commute_fo_edge foe}
	runStateTOp (ESUVAlign fot) = do {gtraceM False "BEFORE getrelid ESUVAlign"; preesuvdg <- show_esuvdg; gtraceM False preesuvdg; foid <- mzoom lens_esunifdgraph_dgraph (getSTRelativeEqDGFoId fot); gtraceM False ("ESUVAlign: " ++ (show foid)); esuvdg <- show_esuvdg; gtraceM False esuvdg; esu_vertical_align_fot fot}
	runStateTOp (ESUSOZip soe) = do {gtraceM False ("SOZip: " ++ (show soe)); esuvdg <- show_esuvdg; gtraceM False esuvdg; esu_sozip_soe soe}
	runStateTOp (ESUFOZip foe) = do {gtraceM False ("FOZip: " ++ (show foe)); esuvdg <- show_esuvdg; gtraceM False esuvdg; esu_fozip_foe foe}
	runStateTOp (ESUSOSimpProj soe) = do {gtraceM False ("ESUSOSimpProj: " ++ (show soe)); esuvdg <- show_esuvdg; gtraceM False esuvdg; esu_so_simplify_proj_soe soe}
	runStateTOp (ESUFOSimpProj foe) = do {gtraceM False ("ESUFOSimpProj: " ++ (show foe)); esuvdg <- show_esuvdg; gtraceM False esuvdg; esu_fo_simplify_proj_foe foe}
	runStateTOp (ESUSODump soe) = do {gtraceM False ("ESUSODump: " ++ (show soe)); esuvdg <- show_esuvdg; gtraceM False esuvdg; r <- esu_so_dump_soe soe; aesuvdg <- show_esuvdg; gtraceM False "AFTER ESUSODump Op"; gtraceM False aesuvdg; return r}
	runStateTOp (ESUFODump foe) = do {gtraceM False ("ESUFODump: " ++ (show foe)); esuvdg <- show_esuvdg; gtraceM False esuvdg; r <- esu_fo_dump_foe foe; aesuvdg <- show_esuvdg; gtraceM False "AFTER ESUFODump Op"; gtraceM False aesuvdg; return r}

newtype RESUnifVDGraph t mpd pd fn v pmv fmv uv = RESUnifVDGraph {fromRESUnifVDGraph :: forall s. ST s (ESUnifVDGraph s t mpd pd fn v pmv fmv uv)}

-- NOTE THAT THIS STATET IGNORES ANY PREVIOUS STATE!!!
unRESUnifVDGraph :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => RESUnifVDGraph t mpd pd fn v pmv fmv uv -> (forall s. StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) ())
unRESUnifVDGraph resuvdg = StateT (\_ -> do {esuvdg <- (fromRESUnifVDGraph resuvdg); return ((),esuvdg)})

doRESUnifVDGraph :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => SOSignature mpd pd fn v pmv fmv -> (forall s. StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) a) -> RESUnifVDGraph t mpd pd fn v pmv fmv uv
doRESUnifVDGraph sig st = RESUnifVDGraph (snd <$> (runStateT st (emptyVDGraph sig)))

sig_RESUnifVDGraph :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => RESUnifVDGraph t mpd pd fn v pmv fmv uv -> SOSignature mpd pd fn v pmv fmv
sig_RESUnifVDGraph resuvdg = runST (esunifdgraph_sosig <$> fromRESUnifVDGraph resuvdg)

instance ESMGUConstraintsUPmv t pd fn v pmv fmv uv => Show (RESUnifVDGraph t mpd pd fn v pmv fmv uv) where
	show resuvdg = runST (do
		{
			esuvdg <- fromRESUnifVDGraph resuvdg;
			fst <$> runStateT show_esuvdg esuvdg
		})

instance ESMGUConstraintsUPmv t pd fn v pmv fmv uv => Implicit (RESUnifVDGraph t mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv) where
	checkImplicit resuvdg us = if (resuvdg_checkfailed resuvdg) then (return False) else (comp (check_unifsolution resuvdg us))
	enumImplicit resuvdg = if (resuvdg_checkfailed resuvdg) then emptycomp else (enumAS (bimap_as EnRESUnifVDGraph id ((depgraph_normalize (ImplicitAS resuvdg)) ?>>= EnumRootSOV)))

-- Simply a wrapper indicating that it has already been enumerated. This is to implement the implicit instance recursively.
newtype EnRESUnifVDGraph t mpd pd fn v pmv fmv uv = EnRESUnifVDGraph {fromEnRESUnifVDGraph :: RESUnifVDGraph t mpd pd fn v pmv fmv uv}

instance ESMGUConstraintsUPmv t pd fn v pmv fmv uv => Implicit (EnRESUnifVDGraph t mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv) where
	checkImplicit (EnRESUnifVDGraph resuvdg) us = error "The checkImplicit implementation for the enumerated unification dependency graph should not be used!"
	-- enumImplicit assumes full normalization and enumeration of root second-order variables
	enumImplicit (EnRESUnifVDGraph resuvdg) = if (resuvdg_checkfailed resuvdg) then emptycomp else return (extract_unifsolution resuvdg)

resuvdg_checkfailed :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => RESUnifVDGraph t mpd pd fn v pmv fmv uv -> Bool
resuvdg_checkfailed resuvdg = runST (fst <$> runStateT (do {unRESUnifVDGraph resuvdg; esuvdg <- get; return (esunifdgraph_failed esuvdg)}) (emptyVDGraph (sig_RESUnifVDGraph resuvdg)))

check_unifsolution :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => RESUnifVDGraph t mpd pd fn v pmv fmv uv -> UnifSysSolution pd fn pmv fmv -> Bool
check_unifsolution resuvdg usol = not (nullAS as3)
	where
	resuvdg2 = RESUnifVDGraph (do
	{
		esuvdg <- fromRESUnifVDGraph resuvdg;
		snd <$> runStateT (check_unifsolution_esuvdg usol) esuvdg
	});
	as1 = ImplicitAS resuvdg2;
	as2 = depgraph_quasinormalize as1;
	as3 = validate_all_consistency as2

check_unifsolution_esuvdg :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => UnifSysSolution pd fn pmv fmv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) ()
check_unifsolution_esuvdg usol = do
	{
		let {ffmv = (\(fmv,vfmv) -> so_unify_depgraph (UVar fmv) (inject_groundsot vfmv))};
		let {fpmv = (\(pmv,vpmv) -> aso_unify_depgraph (UVar pmv) (inject_groundsoa vpmv))};
		traverse ffmv (assocs (uss_fnsol usol));
		traverse fpmv (assocs (uss_pdsol usol));
		pass;
	}

-- This function should ONLY be applied on a graph that not only is normalized, but also has had all root second-order variables enumerated. Otherwise, results may be impredictable!
extract_unifsolution :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => RESUnifVDGraph t mpd pd fn v pmv fmv uv -> UnifSysSolution pd fn pmv fmv
extract_unifsolution resuvdg = runST (do
	{
		esuvdg <- fromRESUnifVDGraph resuvdg;
		let {sovars = esuvdg ^. (lens_esunifdgraph_sosig . lens_sovars); pvars = esuvdg ^. (lens_esunifdgraph_sosig . lens_pvars)};
		-- We make MANY assumptions here, and throw some errors if we find that any are not met (but we do not do exhaustive checks for them, though).
		-- First, we assume that each second-order variable is either equivalent to a constant second-order function or has incoming second-order edges. This should be ensured through the enumeration of root second-order variables that we carried so far.
		-- Second, we assume that if both it is equivalent to a constant AND has an incoming edge, then those two things are totally compatible and equivalent. We will then focus only on the equivalence.
		-- Third, we assume that all equivalent constant functions and all second-order edges are fully compatible and equivalent between them. Again, this should be ensured through everything that has happened before.
		
		let {fsovar = (\sov -> do
		{
			let {nodeid = relbwEqDGSoId (FSONode (UVar sov))};
			vsov <- extract_fmv_value nodeid;
			return (sov,vsov)
		})};
		let {sovpairsr = runStateT (traverse fsovar sovars) esuvdg};
		esuvdg2 <- snd <$> sovpairsr;
		sovpairs <- (list_from_enum . fst) <$> sovpairsr;

		let {psovar = (\pv -> do
		{
			let {nodeid = relbwEqDGSoId (PSONode (UVar pv))};
			vpv <- extract_pmv_value nodeid;
			return (pv,vpv)
		})};
		let {ppairsr = runStateT (traverse psovar pvars) esuvdg2};		
		ppairs <- (list_from_enum . fst) <$> ppairsr;
		return (UnifSysSolution (Data.Map.Strict.fromList sovpairs) (Data.Map.Strict.fromList ppairs))
	})

extract_fmv_value :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifRelSoId s t pd fn v pmv fmv uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) (GroundSOT fn)
extract_fmv_value nodeid = do
	{
		eqns <- mzoom lens_esunifdgraph_dgraph (getEquivDGSONodes nodeid);
		let {feqns = Prelude.map from_fsonode (Prelude.filter is_fsonode eqns)};
		let {nveqns = Prelude.filter (not . isvar_sot) feqns};
		if (Prelude.null nveqns) then do
		{
			ines <- mzoom lens_esunifdgraph_dgraph (st_searchInEqDGSOEdges [] [] nodeid);
			if ((length ines) /= 1) then do
			{
				gtraceM False "Tracing error situation";
				str <- show_esuvdg;
				gtraceM False str;
				error ("Trying to extract second-order function variable from a node with " ++ (show (length ines)) ++ " incoming edges (and no equivalent function constant).")
			}
			else do
			{
				let {ine = head ines};
				ss <- mzoom lens_esunifdgraph_dgraph (eqDGSOEdge_sources ine);
				h <- mzoom lens_esunifdgraph_dgraph (eqDGSOEdge_head ine);
				vss <- traverse extract_fmv_value ss;
				vh <- extract_fmv_value h;
				return (Fix (SOF (CompF vh vss)))
			}
		}
		else (return (to_groundsot (head nveqns)))
	}

extract_pmv_value :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifRelSoId s t pd fn v pmv fmv uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) (GroundSOA pd fn)
extract_pmv_value nodeid = do
	{
		eqns <- mzoom lens_esunifdgraph_dgraph (getEquivDGSONodes nodeid);
		let {peqns = Prelude.map from_psonode (Prelude.filter is_psonode eqns)};
		let {nveqns = Prelude.filter (not . isvar_soa) peqns};
		if (Prelude.null nveqns) then do
		{
			ines <- mzoom lens_esunifdgraph_dgraph (st_searchInEqDGSOEdges [] [] nodeid);
			if ((length ines) /= 1) then do
			{
				gtraceM False "Tracing error situation";
				str <- show_esuvdg;
				gtraceM False str;
				error ("Trying to extract second-order predicate variable from a node with " ++ (show (length ines)) ++ " incoming edges (and no equivalent predicate constant).")
			}
			else do
			{
				let {ine = head ines};
				ss <- mzoom lens_esunifdgraph_dgraph (eqDGSOEdge_sources ine);
				h <- mzoom lens_esunifdgraph_dgraph (eqDGSOEdge_head ine);
				vss <- traverse extract_fmv_value ss;
				vh <- extract_pmv_value h;
				return (Fix (SOP (CompF vh vss)))
			}
		}
		else (return (to_groundsoa (head nveqns)))
	}

-- Again, recursion through operations.
enumerate_all_root_sovs :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => RESUnifVDGraph t mpd pd fn v pmv fmv uv -> AnswerSet (RESUnifVDGraph t mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv)
enumerate_all_root_sovs resuvdg = enumerate_all_root_sovs_choice (do
	{
		esuvdg <- fromRESUnifVDGraph resuvdg;
		enumerate_all_root_sovs_esuvdg esuvdg
	})

enumerate_all_root_sovs_choice :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => (forall s. ST s (Bool,AnswerSet (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv))) -> AnswerSet (RESUnifVDGraph t mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv)
enumerate_all_root_sovs_choice stas = if (runST (fst <$> stas)) then (st_as_commute_esuvdg (((bimap_as return id) . snd) <$> stas) ?>>= EnumRootSOV) else (st_as_commute_esuvdg (((bimap_as return id) . snd) <$> stas))

enumerate_all_root_sovs_esuvdg :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifVDGraph s t mpd pd fn v pmv fmv uv -> ST s (Bool,AnswerSet (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv))
enumerate_all_root_sovs_esuvdg esuvdg = do
	{
		(mb_sov,esuvdg2) <- runStateT find_root_sov esuvdg;
		str_esuvdg <- fst <$> runStateT show_esuvdg esuvdg2;
		gtraceM False ("Looking for root second-order variable. Graph: \n\n");
		gtraceM False str_esuvdg;
		gtraceM False ("Found: " ++ (show mb_sov));
		case mb_sov of
		{
			Nothing -> return (False,ImplicitAS esuvdg2);
			Just (Left sov) -> do
			{
				let {ffunc = (\fn -> snd <$> runStateT (factorize_in_flexrigid_fn sov (inject_groundsot fn)) esuvdg2); fproj = (\idx -> snd <$> runStateT (factorize_in_proj sov idx) esuvdg2)};
				enprojs <- sequence (fproj <$> (uns_enum_from_list [0..((arity sov) - 1)]));
				enflexrigids <- sequence (ffunc <$> enum_all_constfofuncs (esunifdgraph_sosig esuvdg2));
				return (True,ExplicitAS (ImplicitAS <$> (uns_append enprojs enflexrigids)))
			};
			Just (Right psov) -> do
			{
				let {ffunc = (\pd -> snd <$> runStateT (factorize_in_flexrigid_pd psov (inject_groundsoa pd)) esuvdg2)};
				enflexrigids <- sequence (ffunc <$> enum_all_constfopreds (esunifdgraph_sosig esuvdg2));
				return (True,ExplicitAS (ImplicitAS <$> enflexrigids))
			}
		}
	}

-- To produce the final enumeration, we need functions that take a normalized dependency graph, enumerate root second-order variables and collect the dependent values.
find_root_sov :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) (Maybe (Either fmv pmv))
find_root_sov = do
	{
		esuvdg <- get;
		let {sovars = esuvdg ^. (lens_esunifdgraph_sosig . lens_sovars); pvars = esuvdg ^. (lens_esunifdgraph_sosig . lens_pvars)};
		let {ffilt = (\sov -> do
			{
				let {nodeid = relbwEqDGSoId (FSONode (UVar sov))};
				eqns <- mzoom lens_esunifdgraph_dgraph (getEquivDGSONodes nodeid);
				let {feqns = Prelude.map from_fsonode (Prelude.filter is_fsonode eqns)};				
				ines <- mzoom lens_esunifdgraph_dgraph (st_searchInEqDGSOEdges [] [] nodeid);
				return ((all isvar_sot feqns) && (Prelude.null ines))
			})};
		let {pfilt = (\psov -> do
			{
				let {nodeid = relbwEqDGSoId (PSONode (UVar psov))};
				eqns <- mzoom lens_esunifdgraph_dgraph (getEquivDGSONodes nodeid);
				let {peqns = Prelude.map from_psonode (Prelude.filter is_psonode eqns)};
				ines <- mzoom lens_esunifdgraph_dgraph (st_searchInEqDGSOEdges [] [] nodeid);
				return ((all isvar_soa peqns) && (Prelude.null ines))
			})};
		fsovars <- m_efilter ffilt sovars;
		psovars <- m_efilter pfilt pvars;
		if (Prelude.null fsovars) then (if (Prelude.null psovars) then (return Nothing) else (return (Just (Right (uns_produce_next psovars))))) else (return (Just (Left (uns_produce_next fsovars))))
	}

-- This instance is NEVER to be used. It is only a structural thing that we need to transform into the instance above, because of the impredicative b***s**t.
instance Implicit (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv) where
	checkImplicit = error "The implicit ESUnifVDGraph instance should never be used!!"
	enumImplicit = error "The implicit ESUnifVDGraph instance should never be used!!"

instance Implicit (ST s (ESUnifVDGraph s t mpd pd fn v pmv fmv uv)) (UnifSysSolution pd fn pmv fmv) where
	checkImplicit = error "The implicit ESUnifVDGraph instance should never be used!!"
	enumImplicit = error "The implicit ESUnifVDGraph instance should never be used!!"


data ESUnifGlobalOp = SOTConsistency | FOTConsistency | HeadAritySO | HeadArityFO | OccursCheckSO | OccursCheckFO | FODump | SODump | SOSimplifyProjections | FOSimplifyProjections | VerticalCommuteEq | VerticalCommute | VerticalAlign | FOZip | SOZip | Prenormalize | ZFactorize | SFactorize | MFactorize | EnumRootSOV deriving (Show,Eq,Ord)

instance Functional ESUnifGlobalOp (UnifSysSolution pd fn pmv fmv) (AnswerSet (RESUnifVDGraph t mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv)) where
	-- Not sure if this will remain correct, but I think it should.
	-- In principle, all global DG operations leave the set of solutions of the dependency graph unchanged. If that set happens to be a single solution, that is also the case.
	tofun _ us = SingleAS us

instance ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ImplicitF (RESUnifVDGraph t mpd pd fn v pmv fmv uv) (RESUnifVDGraph t mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv) ESUnifGlobalOp where
	composeImplicit resuvdg SOTConsistency = validate_sot_consistency resuvdg
	composeImplicit resuvdg FOTConsistency = validate_fot_consistency resuvdg
	composeImplicit resuvdg HeadAritySO = validate_head_arity_so resuvdg
	composeImplicit resuvdg HeadArityFO = validate_head_arity_fo resuvdg
	composeImplicit resuvdg OccursCheckSO = validate_occurs_check_so resuvdg
	composeImplicit resuvdg OccursCheckFO = validate_occurs_check_fo resuvdg
	composeImplicit resuvdg FODump = as_esu_fo_dump resuvdg
	composeImplicit resuvdg SODump = as_esu_so_dump resuvdg
	composeImplicit resuvdg SOSimplifyProjections = as_esu_so_simplify_projections resuvdg
	composeImplicit resuvdg FOSimplifyProjections = as_esu_fo_simplify_projections resuvdg
	composeImplicit resuvdg VerticalCommuteEq = as_esu_vertical_commute_eq resuvdg
	composeImplicit resuvdg VerticalCommute = as_esu_vertical_commute resuvdg
	composeImplicit resuvdg VerticalAlign = as_esu_vertical_align resuvdg
	composeImplicit resuvdg FOZip = as_esu_fozip resuvdg
	composeImplicit resuvdg SOZip = as_esu_sozip resuvdg
	-- This operation includes all the previous ones, except it streamlines all at the same time. This should be more efficient.
	composeImplicit resuvdg Prenormalize = as_esu_prenormalize resuvdg
	composeImplicit resuvdg ZFactorize = zero_factorize resuvdg
	composeImplicit resuvdg SFactorize = single_factorize resuvdg
	composeImplicit resuvdg MFactorize = multi_factorize resuvdg
	composeImplicit resuvdg EnumRootSOV = enumerate_all_root_sovs resuvdg

-- Actions on the ESUnifVDGraph, enhanced with their propagation operations.
-- These include checking what has actually changed on the graph and what has not, to prevent excessive operations but more importantly to prevent looping.
prop_newEqDGFOEdge :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifRelSoId s t pd fn v pmv fmv uv -> [ESUnifRelFoId s t pd fn v pmv fmv uv] -> ESUnifRelFoId s t pd fn v pmv fmv uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) [ESUnifDGOp s t mpd pd fn v pmv fmv uv]
prop_newEqDGFOEdge h ss t = do
	{
		let {result = []};
		-- This may create the head, source and target nodes!
		-- In particular, checking if nodes exist is whiffy because they are created on the go as part of the monadic operations. Instead, *and only for this particular operation*, whenever a node that previously did not exist may be created, we perform cascade operations from it anyway.
		result2 <- ((return result) >>=++ (justprop_newEqDGFONode t));

		result3 <- ((return result2) >>=++ (justprop_newEqDGSONode h));

		result4 <- ((return result3) >>=++ (concat <$> traverse justprop_newEqDGFONode ss));

		-- Check that the edge does not already exist.
		exist <- mzoom lens_esunifdgraph_dgraph (st_checkAllEqDGFOEdge h ss t);
		result5 <- if exist then (return []) else (do
		{			
			eid <- mzoom lens_esunifdgraph_dgraph (newEqDGFOEdge h ss t);
			(return result4) >>=++ (justprop_newEqDGFOEdge eid)
		});
		return result5
	}

prop_newEqDGSOEdge :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifRelSoId s t pd fn v pmv fmv uv -> [ESUnifRelSoId s t pd fn v pmv fmv uv] -> ESUnifRelSoId s t pd fn v pmv fmv uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) [ESUnifDGOp s t mpd pd fn v pmv fmv uv]
prop_newEqDGSOEdge h ss t = do
	{
		let {result = []};
		-- This may create the head, source and target nodes!
		-- In particular, checking if nodes exist is whiffy because they are created on the go as part of the monadic operations. Instead, *and only for this particular operation*, whenever a node that previously did not exist may be created, we perform cascade operations from it anyway.
		result2 <- ((return result) >>=++ (justprop_newEqDGSONode t));

		result3 <- ((return result2) >>=++ (justprop_newEqDGSONode h));

		result4 <- ((return result3) >>=++ (concat <$> traverse justprop_newEqDGSONode ss));

		-- Check that the edge does not already exist.
		exist <- mzoom lens_esunifdgraph_dgraph (st_checkAllEqDGSOEdge h ss t);
		result5 <- if exist then (return []) else (do
		{			
			eid <- mzoom lens_esunifdgraph_dgraph (newEqDGSOEdge h ss t);
			(return result4) >>=++ (justprop_newEqDGSOEdge eid)
		});
		return result5
	}

prop_addVFoEdge :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifRelFoId s t pd fn v pmv fmv uv -> ESUnifRelFoId s t pd fn v pmv fmv uv -> uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) [ESUnifDGOp s t mpd pd fn v pmv fmv uv]
prop_addVFoEdge s t uv = do
	{
		let {result = []};

		-- This may create the source and target nodes!
		result2 <- ((return result) >>=++ (justprop_newEqDGFONode s));

		result3 <- ((return result2) >>=++ (justprop_newEqDGFONode t));

		exist <- checkVFoEdge s t;
		if exist then (return []) else (do
		{
			addVFoEdge s t uv;
			(return result3) >>=++ (justprop_addVFoEdge s t uv);
		})		
	}

prop_mergeEqDGFONodes :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifRelFoId s t pd fn v pmv fmv uv -> ESUnifRelFoId s t pd fn v pmv fmv uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) [ESUnifDGOp s t mpd pd fn v pmv fmv uv]
prop_mergeEqDGFONodes n1 n2 = do
	{
		let {result = []};

		-- This may create the nodes!
		result2 <- ((return result) >>=++ (justprop_newEqDGFONode n1));

		result3 <- ((return result2) >>=++ (justprop_newEqDGFONode n2));

		equal <- mzoom lens_esunifdgraph_dgraph (eqSTRelativeEqDGFoIds n1 n2);
		if equal then (return []) else (do
		{
			mzoom lens_esunifdgraph_dgraph (mergeEqDGFONodes n1 n2);
			(return result3) >>=++ (justprop_mergeEqDGFONodes n1 n2);
		})
	}

prop_mergeEqDGSONodes :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifRelSoId s t pd fn v pmv fmv uv -> ESUnifRelSoId s t pd fn v pmv fmv uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) [ESUnifDGOp s t mpd pd fn v pmv fmv uv]
prop_mergeEqDGSONodes n1 n2 = do
	{		
		let {result = []};

		-- This may create the nodes!
		result2 <- ((return result) >>=++ (justprop_newEqDGSONode n1));
		
		result3 <- ((return result2) >>=++ (justprop_newEqDGSONode n2));
		
		equal <- mzoom lens_esunifdgraph_dgraph (eqSTRelativeEqDGSoIds n1 n2);
		if equal then (return []) else (do
		{
			mzoom lens_esunifdgraph_dgraph (mergeEqDGSONodes n1 n2);
			(return result3) >>=++ (justprop_mergeEqDGSONodes n1 n2);			
		})
	}

prop_deleteEqDGSOEdge :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => Int -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) [ESUnifDGOp s t mpd pd fn v pmv fmv uv]
prop_deleteEqDGSOEdge soe = do
	{
		-- Check that the edge still exists!
		eex <- mzoom lens_esunifdgraph_dgraph (checkAllEqDGSOEdge soe);
		if (not eex) then (return []) else do
		{
			ops <- justprop_deleteEqDGSOEdge soe;
			mzoom lens_esunifdgraph_dgraph (deleteEqDGSOEdge soe);
			return ops
		}
	}

prop_doDeleteEqDGSOEdge :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => Int -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) [ESUnifDGOp s t mpd pd fn v pmv fmv uv]
prop_doDeleteEqDGSOEdge soe = do
	{
		-- Check that the edge still exists!
		eex <- mzoom lens_esunifdgraph_dgraph (checkAllEqDGSOEdge soe);
		if (not eex) then (return []) else do
		{
			ops <- justprop_doDeleteEqDGSOEdge soe;
			mzoom lens_esunifdgraph_dgraph (doDeleteEqDGSOEdge soe);
			return ops
		}
	}


prop_deleteEqDGFOEdge :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => Int -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) [ESUnifDGOp s t mpd pd fn v pmv fmv uv]
prop_deleteEqDGFOEdge foe = do
	{
		-- Check that the edge still exists!
		eex <- mzoom lens_esunifdgraph_dgraph (checkAllEqDGFOEdge foe);
		if (not eex) then (return []) else do
		{
			ops <- justprop_deleteEqDGFOEdge foe;
			mzoom lens_esunifdgraph_dgraph (deleteEqDGFOEdge foe);
			return ops
		}
	}

prop_doDeleteEqDGFOEdge :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => Int -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) [ESUnifDGOp s t mpd pd fn v pmv fmv uv]
prop_doDeleteEqDGFOEdge foe = do
	{
		-- Check that the edge still exists!
		eex <- mzoom lens_esunifdgraph_dgraph (checkAllEqDGFOEdge foe);
		if (not eex) then (return []) else do
		{
			ops <- justprop_doDeleteEqDGFOEdge foe;
			mzoom lens_esunifdgraph_dgraph (doDeleteEqDGFOEdge foe);
			return ops
		}
	}


prop_newAnonEqDGFOEdge :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifRelSoId s t pd fn v pmv fmv uv -> [ESUnifRelFoId s t pd fn v pmv fmv uv] -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) (ESUnifRelFoId s t pd fn v pmv fmv uv,[ESUnifDGOp s t mpd pd fn v pmv fmv uv])
prop_newAnonEqDGFOEdge h ss = do
	{
		let {result = []};
		
		t <- mzoom lens_esunifdgraph_dgraph (newAnonEqDGFOEdge h ss);
		ines <- mzoom lens_esunifdgraph_dgraph (st_searchInEqDGFOEdges [] [] t);
		-- There must be exactly one incoming edge!
		if ((length ines) /= 1) then (error ("We found " ++ (show (length ines)) ++ " incoming edges on a newly created anonymized node!!!")) else do
		{		
			let {eid = head ines};			

			-- This may create the head and source nodes. It definitely creates the target!
			-- In particular, checking if nodes exist is whiffy because they are created on the go as part of the monadic operations. Instead, *and only for this particular operation*, whenever a node that previously did not exist may be created, we perform cascade operations from it anyway.
			result2 <- ((return result) >>=++ (justprop_newEqDGFONode t));

			result3 <- ((return result2) >>=++ (justprop_newEqDGSONode h));

			result4 <- ((return result3) >>=++ (concat <$> traverse justprop_newEqDGFONode ss));

			result5 <- ((return result4) >>=++ (justprop_newEqDGFOEdge eid));			

			return (t,result5)
		}
	}

prop_newAnonEqDGSOEdge :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifRelSoId s t pd fn v pmv fmv uv -> [ESUnifRelSoId s t pd fn v pmv fmv uv] -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) (ESUnifRelSoId s t pd fn v pmv fmv uv,[ESUnifDGOp s t mpd pd fn v pmv fmv uv])
prop_newAnonEqDGSOEdge h ss = do
	{
		let {result = []};
		
		t <- mzoom lens_esunifdgraph_dgraph (newAnonEqDGSOEdge h ss);
		ines <- mzoom lens_esunifdgraph_dgraph (st_searchInEqDGSOEdges [] [] t);
		-- There must be exactly one incoming edge!
		if ((length ines) /= 1) then (error ("We found " ++ (show (length ines)) ++ " incoming edges on a newly created anonymized node!!!")) else do
		{		
			let {eid = head ines};			

			-- This may create the head and source nodes. It definitely creates the target!
			-- In particular, checking if nodes exist is whiffy because they are created on the go as part of the monadic operations. Instead, *and only for this particular operation*, whenever a node that previously did not exist may be created, we perform cascade operations from it anyway.
			result2 <- ((return result) >>=++ (justprop_newEqDGSONode t));

			result3 <- ((return result2) >>=++ (justprop_newEqDGSONode h));

			result4 <- ((return result3) >>=++ (concat <$> traverse justprop_newEqDGSONode ss));

			result5 <- ((return result4) >>=++ (justprop_newEqDGSOEdge eid));			

			return (t,result5)
		}
	}

justprop_deleteEqDGFOEdge :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => Int -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) [ESUnifDGOp s t mpd pd fn v pmv fmv uv]
justprop_deleteEqDGFOEdge foe = return []

justprop_doDeleteEqDGFOEdge :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => Int -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) [ESUnifDGOp s t mpd pd fn v pmv fmv uv]
justprop_doDeleteEqDGFOEdge foe = return []

justprop_deleteEqDGSOEdge :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => Int -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) [ESUnifDGOp s t mpd pd fn v pmv fmv uv]
justprop_deleteEqDGSOEdge soe = do
	{
		-- If the target now only has one incoming edge, dump all edges for which it is a head.
		-- I don't particularly like the fragility of this trigger, but it works for now.
		t <- mzoom lens_esunifdgraph_dgraph (eqDGSOEdge_target soe);
		ines <- mzoom lens_esunifdgraph_dgraph (st_searchInEqDGSOEdges [] [] t);
		if ((length ines) == 1) then do
		{
			hfoes <- mzoom lens_esunifdgraph_dgraph (st_searchHEqDGFOEdges [] [] t);
			hsoes <- mzoom lens_esunifdgraph_dgraph (st_searchHEqDGSOEdges [] [] t);
			return ((Prelude.map ESUFODump hfoes) ++ (Prelude.map ESUSODump hsoes))
		}
		else (return [])
	}

justprop_doDeleteEqDGSOEdge :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => Int -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) [ESUnifDGOp s t mpd pd fn v pmv fmv uv]
justprop_doDeleteEqDGSOEdge soe = do
	{
		-- If the target now only has one incoming edge, dump all edges for which it is a head.
		-- I don't particularly like the fragility of this trigger, but it works for now.
		t <- mzoom lens_esunifdgraph_dgraph (eqDGSOEdge_target soe);
		ines <- mzoom lens_esunifdgraph_dgraph (st_searchInEqDGSOEdges [] [] t);
		if ((length ines) == 1) then do
		{
			hfoes <- mzoom lens_esunifdgraph_dgraph (st_searchHEqDGFOEdges [] [] t);
			hsoes <- mzoom lens_esunifdgraph_dgraph (st_searchHEqDGSOEdges [] [] t);
			return ((Prelude.map ESUFODump hfoes) ++ (Prelude.map ESUSODump hsoes))
		}
		else (return [])
	}


justprop_mergeEqDGSONodes :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifRelSoId s t pd fn v pmv fmv uv -> ESUnifRelSoId s t pd fn v pmv fmv uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) [ESUnifDGOp s t mpd pd fn v pmv fmv uv]
justprop_mergeEqDGSONodes n1 n2 = do
	{
		-- We assume the nodes have already been merged (i.e. they are equivalent).
		-- Any outgoing horizontal edge of the resulting merged node must be checked for zipping.
		hes <- mzoom lens_esunifdgraph_dgraph (st_searchOutEqDGSOEdges [] [] n1);
		let {result = Prelude.map ESUSOZip hes};

		-- Any edges of which this node is a head must be checked for simplify projections and dump. (Note we do not check here whether the node contains a projection, that is checked when performing the operation).
		hfoes <- mzoom lens_esunifdgraph_dgraph (st_searchHEqDGFOEdges [] [] n1);
		let {result2 = result ++ (Prelude.map ESUFOSimpProj hfoes) ++ (Prelude.map ESUFODump hfoes)};
		
		hsoes <- mzoom lens_esunifdgraph_dgraph (st_searchHEqDGSOEdges [] [] n1);
		let {result3 = result2 ++ (Prelude.map ESUSOSimpProj hsoes) ++ (Prelude.map ESUSODump hsoes)};

		return result3
	}

justprop_mergeEqDGFONodes :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifRelFoId s t pd fn v pmv fmv uv -> ESUnifRelFoId s t pd fn v pmv fmv uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) [ESUnifDGOp s t mpd pd fn v pmv fmv uv]
justprop_mergeEqDGFONodes n1 n2 = do
	{
		-- We assume the nodes have already been merged (i.e. they are equivalent).
		-- For any outgoing vertical edges of the resulting merged node, create a vertical commute instance, just in case.
		ves <- outVFoEdges n1;
		let {result = Prelude.map ESUVCommuteFo ves};

		-- Similarly, any outgoing horizontal edge of the resulting merged node must be checked for zipping.
		hes <- mzoom lens_esunifdgraph_dgraph (st_searchOutEqDGFOEdges [] [] n1);
		let {result2 = result ++ (Prelude.map ESUFOZip hes)};

		let {result3 = result2 ++ (Prelude.map ESUVCommuteEqFo ves)};

		return result3
	}

justprop_addVFoEdge :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifRelFoId s t pd fn v pmv fmv uv -> ESUnifRelFoId s t pd fn v pmv fmv uv -> uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) [ESUnifDGOp s t mpd pd fn v pmv fmv uv]
justprop_addVFoEdge s t uv = return [ESUVCommuteFo (ESUnifVFoEdge s t uv), ESUVCommuteEqFo (ESUnifVFoEdge s t uv)]

justprop_newEqDGFONode :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifRelFoId s t pd fn v pmv fmv uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) [ESUnifDGOp s t mpd pd fn v pmv fmv uv]
justprop_newEqDGFONode foid = return [ESUVAlign foid]

justprop_newEqDGSONode :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifRelSoId s t pd fn v pmv fmv uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) [ESUnifDGOp s t mpd pd fn v pmv fmv uv]
justprop_newEqDGSONode soid = return []

justprop_newEqDGFOEdge :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => Int -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) [ESUnifDGOp s t mpd pd fn v pmv fmv uv]
justprop_newEqDGFOEdge eid = do
	{
		-- For any outgoing vertical edges of the target of the edge, create a vertical commute instance.
		t <- mzoom lens_esunifdgraph_dgraph (eqDGFOEdge_target eid);
		ves <- outVFoEdges t;
		let {result = Prelude.map ESUVCommuteFo ves};

		let {result2 = Prelude.map ESUVCommuteEqFo ves};

		-- Check for zipping of the edge.
		let {result3 = (ESUFOZip eid):result2};

		-- Check for projection simplifying of the edge.
		let {result4 = (ESUFOSimpProj eid):result3};

		-- Check for dumping of the edge.
		let {result5 = (ESUFODump eid):result4};

		return result5
	}

justprop_newEqDGSOEdge :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => Int -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) [ESUnifDGOp s t mpd pd fn v pmv fmv uv]
justprop_newEqDGSOEdge eid = do
	{
		-- In the case of second-order edges, there's no need to do vertical commute, because that only happens on the first-order nodes.
		
		-- Check for zipping of the edge.
		let {result = [ESUSOZip eid]};

		-- Check for projection simplifying of the edge.
		let {result2 = (ESUSOSimpProj eid):result};

		-- Check for dumping of the edge.
		let {result3 = (ESUSODump eid):result2};

		-- Check for dumping and projection simplifying of any edge for which the target is a head of.
		t <- mzoom lens_esunifdgraph_dgraph (eqDGSOEdge_target eid);
		hfoes <- mzoom lens_esunifdgraph_dgraph (st_searchHEqDGFOEdges [] [] t);
		hsoes <- mzoom lens_esunifdgraph_dgraph (st_searchHEqDGSOEdges [] [] t);

		let {result4 = result3 ++ (Prelude.map ESUFODump hfoes) ++ (Prelude.map ESUSODump hsoes)};

		return result4
	}

getStateTSTESUnifVDGraph :: (forall s. StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) a) -> RESUnifVDGraph t mpd pd fn v pmv fmv uv -> a
getStateTSTESUnifVDGraph st resuvdg = runST (do {esuvdg <- fromRESUnifVDGraph resuvdg; fst <$> runStateT st esuvdg})

getStateTSTESUnifVDGraphState :: (forall s. StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) a) -> RESUnifVDGraph t mpd pd fn v pmv fmv uv -> RESUnifVDGraph t mpd pd fn v pmv fmv uv
getStateTSTESUnifVDGraphState st resuvdg = RESUnifVDGraph (do {esuvdg <- fromRESUnifVDGraph resuvdg; snd <$> runStateT st esuvdg})

-- ZeroFactorize means all heads are constants.
-- HalfFactorizeF means there is a constant function that has incoming horizontal edges.
-- HalfFactorizeP means there is a projection that has incoming horizontal edges.
-- SingleFactorize means there are constant heads, but also variable heads. We choose a variable and factorize that one using the constant heads.
-- MultiFactorize means all heads are variables. We choose one variable and enumerate potential heads for it (including projection).
data FactorizeCandidateS s t pd fn v pmv fmv uv = NoFactorize | ZeroFactorizeFO (ESUnifRelFoId s t pd fn v pmv fmv uv) | ZeroFactorizeSO (ESUnifRelSoId s t pd fn v pmv fmv uv) | HalfFactorizeF (ESUnifRelSoId s t pd fn v pmv fmv uv) | HalfFactorizeP Int | HalfFactorizeFO Int fmv | SingleFactorizeFOF (ESUnifRelFoId s t pd fn v pmv fmv uv) fmv | SingleFactorizeFOP (ESUnifRelFoId s t pd fn v pmv fmv uv) pmv | SingleFactorizeSOF (ESUnifRelSoId s t pd fn v pmv fmv uv) fmv | SingleFactorizeSOP (ESUnifRelSoId s t pd fn v pmv fmv uv) pmv | MultiFactorizeF fmv Int | MultiFactorizeP pmv Int
newtype FactorizeCandidate t pd fn v pmv fmv uv = FC {fromFC :: forall s. ST s (FactorizeCandidateS s t pd fn v pmv fmv uv)} -- deriving (Ord,Eq)
data FactorizeType = NoFactorizeT | ZeroFactorizeT | HalfFactorizeT | SingleFactorizeT | MultiFactorizeT deriving Show

-- The Eq and Ord instances of FactorizeCandidate refer to their relative priority in solving. So there may be "equal" factorize candidates that are not actually equal in what they mean! They just have equal priority.
instance Eq (FactorizeCandidateS s t pd fn v pmv fmv uv) where	
	(ZeroFactorizeFO _) == (ZeroFactorizeFO _) = True
	(ZeroFactorizeSO _) == (ZeroFactorizeSO _) = True
	(HalfFactorizeF _) == (HalfFactorizeF _) = True
	(HalfFactorizeP _) == (HalfFactorizeP _) = True
	(HalfFactorizeFO _ _) == (HalfFactorizeFO _ _) = True
	(SingleFactorizeFOF _ _) == (SingleFactorizeFOF _ _) = True
	(SingleFactorizeFOP _ _) == (SingleFactorizeFOP _ _) = True
	(SingleFactorizeSOF _ _) == (SingleFactorizeSOF _ _) = True
	(SingleFactorizeSOP _ _) == (SingleFactorizeSOP _ _) = True
	(MultiFactorizeF _ x) == (MultiFactorizeF _ y) = x == y
	(MultiFactorizeP _ x) == (MultiFactorizeP _ y) = x == y
	NoFactorize == NoFactorize = True
	_ == _ = False

instance Eq (FactorizeCandidate t pd fn v pmv fmv uv) where
	fc1 == fc2 = runST (do {vfc1 <- fromFC fc1; vfc2 <- fromFC fc2; return (vfc1 == vfc2)})

instance Ord (FactorizeCandidateS s t pd fn v pmv fmv uv) where
	(ZeroFactorizeFO _) <= (ZeroFactorizeFO _) = True
	(ZeroFactorizeFO _) <= (ZeroFactorizeSO _) = True
	(ZeroFactorizeFO _) <= (HalfFactorizeF _) = True
	(ZeroFactorizeFO _) <= (HalfFactorizeP _) = True
	(ZeroFactorizeFO _) <= (HalfFactorizeFO _ _) = True
	(ZeroFactorizeFO _) <= (SingleFactorizeFOF _ _) = True
	(ZeroFactorizeFO _) <= (SingleFactorizeFOP _ _) = True
	(ZeroFactorizeFO _) <= (SingleFactorizeSOF _ _) = True
	(ZeroFactorizeFO _) <= (SingleFactorizeSOP _ _) = True
	(ZeroFactorizeFO _) <= (MultiFactorizeF _ _) = True
	(ZeroFactorizeFO _) <= (MultiFactorizeP _ _) = True
	(ZeroFactorizeFO _) <= NoFactorize = True
	(ZeroFactorizeSO _) <= (ZeroFactorizeSO _) = True
	(ZeroFactorizeSO _) <= (HalfFactorizeF _) = True
	(ZeroFactorizeSO _) <= (HalfFactorizeP _) = True
	(ZeroFactorizeSO _) <= (HalfFactorizeFO _ _) = True
	(ZeroFactorizeSO _) <= (SingleFactorizeFOF _ _) = True
	(ZeroFactorizeSO _) <= (SingleFactorizeFOP _ _) = True
	(ZeroFactorizeSO _) <= (SingleFactorizeSOF _ _) = True
	(ZeroFactorizeSO _) <= (SingleFactorizeSOP _ _) = True
	(ZeroFactorizeSO _) <= (MultiFactorizeF _ _) = True
	(ZeroFactorizeSO _) <= (MultiFactorizeP _ _) = True
	(ZeroFactorizeSO _) <= NoFactorize = True
	(HalfFactorizeF _) <= (HalfFactorizeF _) = True
	(HalfFactorizeF _) <= (HalfFactorizeP _) = True
	(HalfFactorizeF _) <= (HalfFactorizeFO _ _) = True
	(HalfFactorizeF _) <= (SingleFactorizeFOF _ _) = True
	(HalfFactorizeF _) <= (SingleFactorizeFOP _ _) = True
	(HalfFactorizeF _) <= (SingleFactorizeSOF _ _) = True
	(HalfFactorizeF _) <= (SingleFactorizeSOP _ _) = True
	(HalfFactorizeF _) <= (MultiFactorizeF _ _) = True
	(HalfFactorizeF _) <= (MultiFactorizeP _ _) = True
	(HalfFactorizeF _) <= NoFactorize = True
	(HalfFactorizeP _) <= (HalfFactorizeP _) = True
	(HalfFactorizeP _) <= (HalfFactorizeFO _ _) = True
	(HalfFactorizeP _) <= (SingleFactorizeFOF _ _) = True
	(HalfFactorizeP _) <= (SingleFactorizeFOP _ _) = True
	(HalfFactorizeP _) <= (SingleFactorizeSOF _ _) = True
	(HalfFactorizeP _) <= (SingleFactorizeSOP _ _) = True
	(HalfFactorizeP _) <= (MultiFactorizeF _ _) = True
	(HalfFactorizeP _) <= (MultiFactorizeP _ _) = True
	(HalfFactorizeP _) <= NoFactorize = True	
	(HalfFactorizeFO _ _) <= (HalfFactorizeFO _ _) = True
	(HalfFactorizeFO _ _) <= (SingleFactorizeFOF _ _) = True
	(HalfFactorizeFO _ _) <= (SingleFactorizeFOP _ _) = True
	(HalfFactorizeFO _ _) <= (SingleFactorizeSOF _ _) = True
	(HalfFactorizeFO _ _) <= (SingleFactorizeSOP _ _) = True
	(HalfFactorizeFO _ _) <= (MultiFactorizeF _ _) = True
	(HalfFactorizeFO _ _) <= (MultiFactorizeP _ _) = True
	(HalfFactorizeFO _ _) <= NoFactorize = True
	(SingleFactorizeFOF _ _) <= (SingleFactorizeFOF _ _) = True
	(SingleFactorizeFOF _ _) <= (SingleFactorizeFOP _ _) = True
	(SingleFactorizeFOF _ _) <= (SingleFactorizeSOF _ _) = True
	(SingleFactorizeFOF _ _) <= (SingleFactorizeSOP _ _) = True
	(SingleFactorizeFOF _ _) <= (MultiFactorizeF _ _) = True
	(SingleFactorizeFOF _ _) <= (MultiFactorizeP _ _) = True
	(SingleFactorizeFOF _ _) <= NoFactorize = True
	(SingleFactorizeFOP _ _) <= (SingleFactorizeFOP _ _) = True
	(SingleFactorizeFOP _ _) <= (SingleFactorizeSOF _ _) = True
	(SingleFactorizeFOP _ _) <= (SingleFactorizeSOP _ _) = True
	(SingleFactorizeFOP _ _) <= (MultiFactorizeF _ _) = True
	(SingleFactorizeFOP _ _) <= (MultiFactorizeP _ _) = True
	(SingleFactorizeFOP _ _) <= NoFactorize = True
	(SingleFactorizeSOF _ _) <= (SingleFactorizeSOF _ _) = True
	(SingleFactorizeSOF _ _) <= (SingleFactorizeSOP _ _) = True
	(SingleFactorizeSOF _ _) <= (MultiFactorizeF _ _) = True
	(SingleFactorizeSOF _ _) <= (MultiFactorizeP _ _) = True
	(SingleFactorizeSOF _ _) <= NoFactorize = True
	(SingleFactorizeSOP _ _) <= (SingleFactorizeSOP _ _) = True
	(SingleFactorizeSOP _ _) <= (MultiFactorizeF _ _) = True
	(SingleFactorizeSOP _ _) <= (MultiFactorizeP _ _) = True
	(SingleFactorizeSOP _ _) <= NoFactorize = True
	(MultiFactorizeF _ x) <= (MultiFactorizeF _ y) = x <= y
	(MultiFactorizeF _ x) <= (MultiFactorizeP _ y) = x <= y
	(MultiFactorizeF _ _) <= NoFactorize = True
	(MultiFactorizeP _ x) <= (MultiFactorizeP _ y) = x <= y
	(MultiFactorizeP _ _) <= NoFactorize = True
	NoFactorize <= NoFactorize = True
	_ <= _ = False

instance Ord (FactorizeCandidate t pd fn v pmv fmv uv) where
	fc1 <= fc2 = runST (do {vfc1 <- fromFC fc1; vfc2 <- fromFC fc2; return (vfc1 <= vfc2)})

-- All of the following section is disgusting, but Haskell is at fault.
-- None of this should be necessary at all.
data STASCommuteType = SingleASCommute | ImplicitASCommute | ExplicitASCommute

forall_fmap_enum_fromcontinue :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => (forall s. EnumProc (ST s (AnswerSet (ST s (ESUnifVDGraph s t mpd pd fn v pmv fmv uv)) (UnifSysSolution pd fn pmv fmv)))) -> (forall s. EnumProc (ST s (AnswerSet (ST s (ESUnifVDGraph s t mpd pd fn v pmv fmv uv)) (UnifSysSolution pd fn pmv fmv))))
forall_fmap_enum_fromcontinue (Continue x) = x

forall_fmap_enum_fromproduce :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => (forall s. EnumProc (ST s (AnswerSet (ST s (ESUnifVDGraph s t mpd pd fn v pmv fmv uv)) (UnifSysSolution pd fn pmv fmv)))) -> (forall s. EnumProc (ST s (AnswerSet (ST s (ESUnifVDGraph s t mpd pd fn v pmv fmv uv)) (UnifSysSolution pd fn pmv fmv))))
forall_fmap_enum_fromproduce (Produce v x) = x

forall_fmap_enum_fromproduce_value :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => (forall s. EnumProc (ST s (AnswerSet (ST s (ESUnifVDGraph s t mpd pd fn v pmv fmv uv)) (UnifSysSolution pd fn pmv fmv)))) -> (forall s. ST s (AnswerSet (ST s (ESUnifVDGraph s t mpd pd fn v pmv fmv uv)) (UnifSysSolution pd fn pmv fmv)))
forall_fmap_enum_fromproduce_value (Produce v x) = v

forall_fmap_enum_resuvdg :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => (forall s. EnumProc (ST s (AnswerSet (ST s (ESUnifVDGraph s t mpd pd fn v pmv fmv uv)) (UnifSysSolution pd fn pmv fmv)))) -> EnumProc (AnswerSet (RESUnifVDGraph t mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv))
forall_fmap_enum_resuvdg EnumProc.Empty = EnumProc.Empty
forall_fmap_enum_resuvdg Halt = Halt
forall_fmap_enum_resuvdg (Error str) = Error str
forall_fmap_enum_resuvdg x | case x of {Continue _ -> True; _ -> False} = Continue (forall_fmap_enum_resuvdg (forall_fmap_enum_fromcontinue x))
forall_fmap_enum_resuvdg x | case x of {Produce _ _ -> True; _ -> False} = Produce (st_as_commute_esuvdg (forall_fmap_enum_fromproduce_value x)) (forall_fmap_enum_resuvdg (forall_fmap_enum_fromproduce x))

st_as_commute_esuvdg_from_explicit :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => (forall s. ST s (AnswerSet (ST s (ESUnifVDGraph s t mpd pd fn v pmv fmv uv)) (UnifSysSolution pd fn pmv fmv))) -> (forall s. ST s (EnumProc (AnswerSet (ST s (ESUnifVDGraph s t mpd pd fn v pmv fmv uv)) (UnifSysSolution pd fn pmv fmv))))
st_as_commute_esuvdg_from_explicit expl = do {(ExplicitAS x) <- expl; return x}

st_as_commute_esuvdg_en_commute :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => (forall s. ST s (AnswerSet (ST s (ESUnifVDGraph s t mpd pd fn v pmv fmv uv)) (UnifSysSolution pd fn pmv fmv))) -> (forall s. EnumProc (ST s (AnswerSet (ST s (ESUnifVDGraph s t mpd pd fn v pmv fmv uv)) (UnifSysSolution pd fn pmv fmv))))
st_as_commute_esuvdg_en_commute stas = st_en_commute_as (st_as_commute_esuvdg_from_explicit stas)

st_en_commute_as :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => (forall s. ST s (EnumProc (AnswerSet (ST s (ESUnifVDGraph s t mpd pd fn v pmv fmv uv)) (UnifSysSolution pd fn pmv fmv)))) -> (forall s. EnumProc (ST s (AnswerSet (ST s (ESUnifVDGraph s t mpd pd fn v pmv fmv uv)) (UnifSysSolution pd fn pmv fmv))))
st_en_commute_as sten = case comtype of
	{
		EmptyCom -> EnumProc.Empty;
		HaltCom -> Halt;
		ErrorCom -> Error (runST (do {(Error str) <- sten; return str}));
		ContinueCom -> Continue (st_en_commute_as (do {(Continue x) <- sten; return x}));
		ProduceCom -> Produce (do {(Produce v x) <- sten; return v}) (st_en_commute_as (do {(Produce v x) <- sten; return x}))
	}
	where
		comtype = runST (do
		{
			en <- sten;
			case en of
			{
				EnumProc.Empty -> return EmptyCom;
				Halt -> return HaltCom;
				Error str -> return ErrorCom;
				Continue x -> return ContinueCom;
				Produce v x -> return ProduceCom
			}
		})

st_as_commute_esuvdg :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => (forall s. ST s (AnswerSet (ST s (ESUnifVDGraph s t mpd pd fn v pmv fmv uv)) (UnifSysSolution pd fn pmv fmv))) -> AnswerSet (RESUnifVDGraph t mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv)
st_as_commute_esuvdg stas = case comtype of
			{
				SingleASCommute -> SingleAS (runST (do {(SingleAS x) <- stas; return x}));
				ImplicitASCommute -> ImplicitAS (RESUnifVDGraph (do {(ImplicitAS x) <- stas; x}));
				ExplicitASCommute -> ExplicitAS (forall_fmap_enum_resuvdg (st_as_commute_esuvdg_en_commute stas))
			}
	where comtype = runST (do
		{
			as <- stas;
			case as of
			{
				SingleAS x -> return SingleASCommute;
				ImplicitAS x -> return ImplicitASCommute;
				ExplicitAS x -> return ExplicitASCommute 
			}
		})

aso_unify_depgraph :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => SOAtom pd fn pmv fmv -> SOAtom pd fn pmv fmv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) (ESUnifRelSoId s t pd fn v pmv fmv uv)
aso_unify_depgraph lad rad = do
	{
		lid <- grab_asonode lad;
		rid <- grab_asonode rad;

		ops <- prop_mergeEqDGSONodes lid rid;

		runStateTOps ops;

		return lid
	}

so_unify_depgraph :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => SOTerm fn fmv -> SOTerm fn fmv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) (ESUnifRelSoId s t pd fn v pmv fmv uv)
so_unify_depgraph ltd rtd = do
	{
		lid <- grab_sonode ltd;
		rid <- grab_sonode rtd;
		
		ops <- prop_mergeEqDGSONodes lid rid;

		runStateTOps ops;

		-- Left or right don't matter, we just merged them.
		return lid
	}

afo_unify_depgraph :: ESMGUConstraintsALL a t ss mpd pd fn v pmv fmv uv => AtomDependant a t ss mpd pd fn v pmv fmv uv -> AtomDependant a t ss mpd pd fn v pmv fmv uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) (ESUnifRelFoId s t pd fn v pmv fmv uv)
afo_unify_depgraph lad rad = do
	{
		lid <- grab_afonode lad;
		rid <- grab_afonode rad;

		ops <- prop_mergeEqDGFONodes lid rid;

		runStateTOps ops;

		return lid
	}

fo_unify_depgraph :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => TermDependant t fn v fmv uv -> TermDependant t fn v fmv uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) (ESUnifRelFoId s t pd fn v pmv fmv uv)
fo_unify_depgraph ltd rtd = do
	{
		lid <- grab_fonode ltd;
		rid <- grab_fonode rtd;
		
		ops <- prop_mergeEqDGFONodes lid rid;

		runStateTOps ops;

		-- Left or right don't matter, we just merged them.
		return lid
	}

-- These are redundant with grab_fonode and so on. We have deprecated them. We will keep them around for a bit, in case of errors. REMOVE if you see this and do not know what this is about.
--introduce_fot_depgraph :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => TermDependant t fn v fmv uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) (ESUnifRelFoId s t fn v fmv uv)
--introduce_fot_depgraph td = introduce_fot_depgraph_us us (fromSOMetawrap somw) where (us,somw) = decompose_td td

--introduce_fot_depgraph_us :: ESMGUConstraintsU t pd fn v fmv uv => [uv] -> UTerm (t (SOTerm fn fmv)) v -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) (ESUnifRelFoId s t fn v fmv uv)
--introduce_fot_depgraph_us us (UVar v) = return (relbwEqDGFoId (compose_td us (SOMetawrap (UVar v))))
--introduce_fot_depgraph_us us (UTerm t) = do
--	{
--		fnid <- introduce_sot_depgraph fn;
--		ss <- traverse (introduce_fot_depgraph_us us) sts;
--		(nid,ops) <- prop_newAnonEqDGFOEdge fnid ss;
--
--		runStateTOps ops;
--		
--		return nid
--	}
--	where
--		(fn,sts) = unbuild_term t 

-- NOTE that we do assume that the SOTerm is normalized here!
--introduce_sot_depgraph :: ESMGUConstraintsU t pd fn v fmv uv => SOTerm fn fmv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) (ESUnifRelSoId s t fn v fmv uv)
--introduce_sot_depgraph (UVar v) = return (relbwEqDGSoId (UVar v))
--introduce_sot_depgraph (UTerm (SOF (ConstF fn))) = return (relbwEqDGSoId (UTerm (SOF (ConstF fn))))
--introduce_sot_depgraph (UTerm (SOF (Proj idx))) = return (relbwEqDGSoId (UTerm (SOF (Proj idx))))
--introduce_sot_depgraph (UTerm (SOF (CompF h sfns))) = do
--	{
--		hid <- introduce_sot_depgraph h;
--		ss <- traverse introduce_sot_depgraph sfns;
--		(nid,ops) <- prop_newAnonEqDGSOEdge hid ss;
--
--		runStateTOps ops;
--
--		return nid
--	}

-- These functions produce recursion through implicit composition.

multi_factorize :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => RESUnifVDGraph t mpd pd fn v pmv fmv uv -> AnswerSet (RESUnifVDGraph t mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv)
multi_factorize resuvdg = case ctype of
	{
		ZeroFactorizeT -> validate_all_consistency ((factorize_candidate cand resuvdg) ?>>= MFactorize);
		HalfFactorizeT -> validate_all_consistency ((factorize_candidate cand resuvdg) ?>>= MFactorize);
		SingleFactorizeT -> validate_all_consistency ((factorize_candidate cand resuvdg) ?>>= MFactorize);
		MultiFactorizeT -> validate_all_consistency ((factorize_candidate cand resuvdg) ?>>= MFactorize);
		_ -> ImplicitAS resuvdg
	}
	where
		cand = factorize_get_least resuvdg;
		ctype = factorize_type cand;	

single_factorize :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => RESUnifVDGraph t mpd pd fn v pmv fmv uv -> AnswerSet (RESUnifVDGraph t mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv)
single_factorize resuvdg = case ctype of
	{
		ZeroFactorizeT -> validate_all_consistency ((factorize_candidate cand resuvdg) ?>>= SFactorize);
		HalfFactorizeT -> validate_all_consistency ((factorize_candidate cand resuvdg) ?>>= SFactorize);
		SingleFactorizeT -> validate_all_consistency ((factorize_candidate cand resuvdg) ?>>= SFactorize);
		_ -> ImplicitAS resuvdg
	}
	where
		cand = 	factorize_get_least resuvdg;
		ctype = factorize_type cand;	

zero_factorize :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => RESUnifVDGraph t mpd pd fn v pmv fmv uv -> AnswerSet (RESUnifVDGraph t mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv)
zero_factorize resuvdg = case ctype of
	{
		ZeroFactorizeT -> validate_all_consistency ((factorize_candidate cand resuvdg) ?>>= ZFactorize);
		_ -> ImplicitAS resuvdg
	}
	where
		cand = factorize_get_least resuvdg;
		ctype = factorize_type cand

factorize_type :: FactorizeCandidate t pd fn v pmv fmv uv -> FactorizeType
factorize_type fc = runST (do
	{
		rfc <- fromFC fc;
		case rfc of
		{
			NoFactorize -> return NoFactorizeT;
			ZeroFactorizeFO _ -> return ZeroFactorizeT;
			ZeroFactorizeSO _ -> return ZeroFactorizeT;
			HalfFactorizeF _ -> return HalfFactorizeT;
			HalfFactorizeP _ -> return HalfFactorizeT;
			HalfFactorizeFO _ _ -> return HalfFactorizeT;
			SingleFactorizeFOF _ _ -> return SingleFactorizeT;
			SingleFactorizeFOP _ _ -> return SingleFactorizeT;			
			SingleFactorizeSOF _ _ -> return SingleFactorizeT;
			SingleFactorizeSOP _ _ -> return SingleFactorizeT;
			MultiFactorizeF _ _ -> return MultiFactorizeT;
			MultiFactorizeP _ _ -> return MultiFactorizeT
		}
	})

factorize_candidate :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => FactorizeCandidate t pd fn v pmv fmv uv -> RESUnifVDGraph t mpd pd fn v pmv fmv uv -> AnswerSet (RESUnifVDGraph t mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv)
factorize_candidate fc resuvdg = gtrace False ("FACTORIZING\n\nBEFORE:\n" ++ (show resuvdg) ++ "\nAFTER:\n" ++ (show (implicitOnly res \$ ())) ++ "\nDONE\n") res
	where res = st_as_commute_esuvdg (do
		{		
			esuvdg <- fromRESUnifVDGraph resuvdg;
			rfc <- fromFC fc;
			case rfc of
			{
				NoFactorize -> return (ImplicitAS (return esuvdg));
				ZeroFactorizeFO t -> do
				{
					(res_factorized,res_st) <- runStateT (factorize_in_fot_rigid t) esuvdg;
					case res_factorized of
					{
						Inexistent -> return (ExplicitAS EnumProc.Empty);
						Distinct -> return (ExplicitAS EnumProc.Empty);
						Exist _ -> return (ImplicitAS (return res_st))
					}
				};
				ZeroFactorizeSO t -> do
				{
					(res_factorized,res_st) <- runStateT (factorize_in_sot_rigid t) esuvdg;
					case res_factorized of
					{
						Inexistent -> return (ExplicitAS EnumProc.Empty);
						Distinct -> return (ExplicitAS EnumProc.Empty);
						Exist _ -> return (ImplicitAS (return res_st))
					}
				};
				HalfFactorizeF t -> do
				{
					(es,esuvdg2) <- runStateT (mzoom lens_esunifdgraph_dgraph (st_searchInEqDGSOEdges [] [] t)) esuvdg;
					-- Check that there are still some incoming edges. This is to avoid duplication of stuff.
					if (Prelude.null es) then (return (ImplicitAS (return esuvdg2)))
					else do
					{
						(nt,esuvdg3) <- runStateT (mzoom lens_esunifdgraph_dgraph newAnonEqDGSONode) esuvdg2;
						(tid,esuvdg4) <- runStateT (mzoom lens_esunifdgraph_dgraph (getSTRelativeEqDGSoId t)) esuvdg3;
						(mb_d,esuvdg5) <- runStateT (mzoom lens_esunifdgraph_dgraph (st_getEqDGSORep tid)) esuvdg4;
						let {d = fromJustErr "No representative element for the node target of a half factorization of function symbols!" mb_d; aty = arity d; ss = Prelude.map (relbwEqDGSoId . FSONode . UTerm . SOF . Proj) [0..(aty-1)]};
						(ops,esuvdg6) <- runStateT (prop_newEqDGSOEdge t ss nt) esuvdg5;
						let {fne = (\e -> do
							{
								ss <- mzoom lens_esunifdgraph_dgraph (eqDGSOEdge_sources e);
								h <- mzoom lens_esunifdgraph_dgraph (eqDGSOEdge_head e);
								prop_newEqDGSOEdge h ss nt
							})};
						(opss2,esuvdg7) <- runStateT (traverse fne es) esuvdg6;
						(opss3,esuvdg8) <- runStateT (traverse prop_deleteEqDGSOEdge es) esuvdg7;

						let {ops2 = concat opss2; ops3 = concat opss3};

						(_,esuvdg9) <- runStateT (runStateTOps (ops ++ ops2 ++ ops3)) esuvdg8;

						return (ImplicitAS (return esuvdg9))
					}
					
				};
				HalfFactorizeP e -> do
				{
					-- Check that the edge is still non-redundant in the graph.
					(r,esuvdg2) <- runStateT (mzoom lens_esunifdgraph_dgraph (checkEqDGSOEdge e)) esuvdg;
					if (not r) then (return (ImplicitAS (return esuvdg2))) else do
					{
						(ss,esuvdg3) <- runStateT (mzoom lens_esunifdgraph_dgraph (eqDGSOEdge_sources e)) esuvdg2;
						(h,esuvdg4) <- runStateT (mzoom lens_esunifdgraph_dgraph (eqDGSOEdge_head e)) esuvdg3;
						let {aty = length ss; hs = Prelude.map (relbwEqDGSoId . FSONode . UTerm . SOF . Proj) [0..(aty - 1)]};
						let {fproj = (\n -> snd <$> runStateT (do {ops <- prop_mergeEqDGSONodes h n; runStateTOps ops}) esuvdg4)};
						let {enprojs = fmap fproj (uns_enum_from_list hs)};
						
						return (ExplicitAS (ImplicitAS <$> enprojs))
					}				
				};
				HalfFactorizeFO e sov -> do
				{
					-- Check that the edge is still non-redundant in the graph.
					(r,esuvdg2) <- runStateT (mzoom lens_esunifdgraph_dgraph (checkEqDGFOEdge e)) esuvdg;
					if (not r) then (return (ImplicitAS (return esuvdg2))) else do
					{
						-- Check that the head contains only variables.
						(h,esuvdg3) <- runStateT (mzoom lens_esunifdgraph_dgraph (eqDGFOEdge_head e)) esuvdg2;
						(sots,esuvdg4) <- runStateT (mzoom lens_esunifdgraph_dgraph (getEquivDGSONodes h)) esuvdg3;
						let {fsots = Prelude.map from_fsonode sots};
						if ((any (not . is_fsonode) sots) || (any (not . isvar_sot) fsots)) then (return (ExplicitAS EnumProc.Empty)) else do
						{
							-- Check which of the sources of the edge are the same as the target
							(t,esuvdg5) <- runStateT (mzoom lens_esunifdgraph_dgraph (eqDGFOEdge_target e)) esuvdg4;
							(ss,esuvdg6) <- runStateT (mzoom lens_esunifdgraph_dgraph (eqDGFOEdge_sources e)) esuvdg5;
							let {fils = (\idx -> eqSTRelativeEqDGFoIds t (errAt "HalfFactorizeFO !!" ss idx))};
							(rsis,esuvdg7) <- runStateT (mzoom lens_esunifdgraph_dgraph (m_filter fils [0..((length ss) - 1)])) esuvdg6;							
							let {fproj = (\idx -> snd <$> runStateT (factorize_in_proj sov idx) esuvdg7)};
							let {enprojs = fmap fproj (uns_enum_from_list rsis)};
							let {res_nd = snd <$> runStateT (factorize_in_nondep sov rsis) esuvdg7};
							
							-- This may bite my ass in the future, but I do not think so right now.
							-- If all the sources are the same as the target, there is no point in creating the edge with no sources, it will lead to nothing, and produces some cycles with the current implementation.
							if ((length rsis) == (length ss)) then (return (ExplicitAS (ImplicitAS <$> enprojs))) else (return (ExplicitAS (uns_append (ImplicitAS <$> enprojs) (single_enum (ImplicitAS res_nd)))))
						}
					}
				};				
				SingleFactorizeFOF t sov -> do
				{
					-- Let's just try all projections for the variable's arity. The arity checks should remove any that don't match.
					let {fproj = (\idx -> snd <$> runStateT (factorize_in_proj sov idx) esuvdg)};
					let {enprojs = fmap fproj (uns_enum_from_list [0..((arity sov) - 1)])};
					(res_factorized,res_st) <- runStateT (factorize_in_fot_rigid t) esuvdg;				
					case res_factorized of
					{
						Inexistent -> return (ExplicitAS EnumProc.Empty);
						Distinct -> return (ExplicitAS EnumProc.Empty);
						Exist (Left ch) -> do
						{
							let {res_hst = snd <$> runStateT (factorize_in_flexrigid_fn sov ch) esuvdg};
							--return (ExplicitAS (ImplicitAS res_hst --> (ImplicitAS <$> enprojs)))
							-- This ordering is important, as it makes the simplest solutions come first.
							return (ExplicitAS (uns_append (ImplicitAS <$> enprojs) (single_enum (ImplicitAS res_hst))))
						};
						Exist (Right _) -> error "Found a predicate when factorizing a function node!!!"
					}
				};
				SingleFactorizeFOP t psov -> do
				{
					(res_factorized,res_st) <- runStateT (factorize_in_fot_rigid t) esuvdg;				
					case res_factorized of
					{
						Inexistent -> return (ExplicitAS EnumProc.Empty);
						Distinct -> return (ExplicitAS EnumProc.Empty);
						Exist (Right ch) -> do
						{
							let {res_hst = snd <$> runStateT (factorize_in_flexrigid_pd psov ch) esuvdg};
							return (ImplicitAS res_hst)
						};
						Exist (Left _) -> error "Found a function when factorizing a predicate node!!!"
					}
				};
				SingleFactorizeSOF t sov -> do
				{
					-- Let's just try all projections for the variable's arity. The arity checks should remove any that don't match.
					let {fproj = (\idx -> snd <$> runStateT (factorize_in_proj sov idx) esuvdg)};
					let {enprojs = fmap fproj (uns_enum_from_list [0..((arity sov) - 1)])};
					(res_factorized,res_st) <- runStateT (factorize_in_sot_rigid t) esuvdg;
					case res_factorized of
					{
						Inexistent -> return (ExplicitAS EnumProc.Empty);
						Distinct -> return (ExplicitAS EnumProc.Empty);
						Exist (Left ch) -> do
						{
							let {res_hst = snd <$> runStateT (factorize_in_flexrigid_fn sov ch) esuvdg};
							--return (ExplicitAS (ImplicitAS res_hst --> (ImplicitAS <$> enprojs)))
							-- This ordering is important, as it makes the simplest solutions come first.
							return (ExplicitAS (uns_append (ImplicitAS <$> enprojs) (single_enum (ImplicitAS res_hst))))
						};
						Exist (Right _) -> error "Found a predicate when factorizing a function node!!!"
					}
				};
				SingleFactorizeSOP t psov -> do
				{
					(res_factorized,res_st) <- runStateT (factorize_in_sot_rigid t) esuvdg;
					case res_factorized of
					{
						Inexistent -> return (ExplicitAS EnumProc.Empty);
						Distinct -> return (ExplicitAS EnumProc.Empty);
						Exist (Right ch) -> do
						{
							let {res_hst = snd <$> runStateT (factorize_in_flexrigid_pd psov ch) esuvdg};
							return (ImplicitAS res_hst)
						};
						Exist (Left _) -> error "Found a function when factorizing a predicate node!!!"
					}
				};
				MultiFactorizeF sov nvars -> do
				{
					let {fns = funcs (esuvdg ^. (lens_esunifdgraph_sosig . lens_fosig)); aty = arity sov; vfns = econcat (Prelude.map fromJust (Prelude.filter isJust (Prelude.map (fns !!?) [0..aty])))};
					let {ffn = (\fn -> snd <$> runStateT (factorize_in_flexrigid_fn sov (UTerm (SOF (ConstF fn)))) esuvdg)};
					let {ren = fmap ffn vfns};
					let {r = (ExplicitAS (ImplicitAS <$> ren))};
					return r
				};
				MultiFactorizeP psov nvars -> do
				{
					let {pds = preds (esuvdg ^. (lens_esunifdgraph_sosig . lens_fosig)); aty = arity psov; vpds = econcat (Prelude.map fromJust (Prelude.filter isJust (Prelude.map (pds !!?) [0..aty])))};
					let {fpd = (\pd -> snd <$> runStateT (factorize_in_flexrigid_pd psov (UTerm (SOP (ConstF pd)))) esuvdg)};
					let {ren = fmap fpd vpds};
					let {r = (ExplicitAS (ImplicitAS <$> ren))};
					return r
				}
			}
		})

factorize_get_least :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => RESUnifVDGraph t mpd pd fn v pmv fmv uv -> FactorizeCandidate t pd fn v pmv fmv uv
factorize_get_least resuvdg = FC (do
	{
		esuvdg <- fromRESUnifVDGraph resuvdg;
		let {fonodes = Prelude.map (DirectId . EqDGFoId .  dgid . fromJust) (Prelude.filter isJust (esuvdg ^. (lens_esunifdgraph_dgraph . lens_eqdgraph . lens_fonodes)))};
		let {sonodes = Prelude.map (DirectId . EqDGSoId .  dgid . fromJust) (Prelude.filter isJust (esuvdg ^. (lens_esunifdgraph_dgraph . lens_eqdgraph . lens_sonodes)))};

		let {stfocands = traverse factorize_get_fo_candidate fonodes; stsocands = traverse factorize_get_so_candidate sonodes; stsoecands = traverse factorize_get_soe_candidate sonodes; stfoecands = traverse factorize_get_foe_candidate fonodes; stallcands = stfocands >>=++ stsocands >>=++ stsoecands >>=++ stfoecands};		
		(cands,_) <- runStateT stallcands esuvdg;
		let {mb_cand = minimumMay cands; cand = fromMaybe NoFactorize mb_cand};
		
		return cand
	})

factorize_get_foe_candidate :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifRelFoId s t pd fn v pmv fmv uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) (FactorizeCandidateS s t pd fn v pmv fmv uv)
factorize_get_foe_candidate fot = do
	{
		ines <- mzoom lens_esunifdgraph_dgraph (st_searchInEqDGFOEdges [] [] fot);
		gtraceM False "factorize_get_foe_candidate - ines:";
		gtraceM False (show ines);
		let {ffil = (\ine -> do {ss <- mzoom lens_esunifdgraph_dgraph (eqDGFOEdge_sources ine); t <- mzoom lens_esunifdgraph_dgraph (eqDGFOEdge_target ine); mzoom lens_esunifdgraph_dgraph (m_any (eqSTRelativeEqDGFoIds t) ss)})};
		rines <- m_filter ffil ines;
		gtraceM False "factorize_get_foe_candidate - rines:";
		gtraceM False (show rines);
		-- We assume here that all nodes either have a dependant or incoming horizontal edges.
		let {ffil2 = (\ine -> do
			{
				h <- mzoom lens_esunifdgraph_dgraph (eqDGFOEdge_head ine);
				hts <- mzoom lens_esunifdgraph_dgraph (getEquivDGSONodes h);
				let {fhts = Prelude.map from_fsonode (Prelude.filter is_fsonode hts); phts = Prelude.map from_psonode (Prelude.filter is_psonode hts)};
				hines <- mzoom lens_esunifdgraph_dgraph (st_searchInEqDGSOEdges [] [] h);
				gtraceM False "factorize_get_foe_candidate - ine:";
				gtraceM False (show ine);
				gtraceM False "factorize_get_foe_candidate - fhts:";
				gtraceM False (show fhts);
				gtraceM False "factorize_get_foe_candidate - phts:";
				gtraceM False (show phts);
				return ((Prelude.null hines) && (all isvar_sot fhts) && (all isvar_soa phts))
			})};
		rrines <- m_filter ffil2 rines;
		
		if (Prelude.null rrines) then (return NoFactorize) else (do
		{
			let {e = head rrines};
			eh <- mzoom lens_esunifdgraph_dgraph (eqDGFOEdge_head e);
			hts <- mzoom lens_esunifdgraph_dgraph (getEquivDGSONodes eh);
			let {fhts = Prelude.map from_fsonode (Prelude.filter is_fsonode hts); phts = Prelude.map from_psonode (Prelude.filter is_psonode hts)};
			-- It should be the case here that there is at least one dependant in the node, and it is a variable.
			if (not (Prelude.null fhts)) then do
			{
				let {afvar = case (headErr "factorize_get_foe_candidate: No function dependants" fhts) of {UVar x -> x; _ -> error "factorize_get_foe_candidate: Non-variable function dependant"}};
				gtraceM False "HALFFACTORIZEFO";
				gtraceM False "Current graph:";
				gg <- show_esuvdg;
				gtraceM False gg;
				gtraceM False ("ines: " ++ (show ines));
				gtraceM False ("rines: " ++ (show rines));
				gtraceM False ("rrines: " ++ (show rrines));
				et <- mzoom lens_esunifdgraph_dgraph (eqDGFOEdge_target e);
				hid <- mzoom lens_esunifdgraph_dgraph (getSTRelativeId eh);
				gtraceM False ("Head: " ++ (show hid));
				tid <- mzoom lens_esunifdgraph_dgraph (getSTRelativeId et);
				gtraceM False ("Target: " ++ (show tid));
				return (HalfFactorizeFO e afvar)
			}
			-- I believe this should be an error. We are looking for edges whose source is equal to the target. These can never have a predicate as head.
			else if (not (Prelude.null phts)) then (error "Cyclic first-order edge with predicate as head!")
			else (error "Cyclic first-order edge with no elements in the head!")
		})
	}

factorize_get_soe_candidate :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifRelSoId s t pd fn v pmv fmv uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) (FactorizeCandidateS s t pd fn v pmv fmv uv)
factorize_get_soe_candidate sot = do
	{
		sots <- mzoom lens_esunifdgraph_dgraph (getEquivDGSONodes sot);
		let {fsots = Prelude.map from_fsonode (Prelude.filter is_fsonode sots); psots = Prelude.map from_psonode (Prelude.filter is_psonode sots)};
		ines <- mzoom lens_esunifdgraph_dgraph (st_searchInEqDGSOEdges [] [] sot);
		if (((all isvar_sot fsots) && (all isvar_soa psots)) || (Prelude.null ines))
		then (return NoFactorize)
		else 	(if (any isproj_sot fsots)
			-- Any one edge works here.
			then (return (HalfFactorizeP (head ines)))
			-- If not all are variables and none is a projection, then at least one must be a function or predicate symbol.
			else (return (HalfFactorizeF sot)))
	}

factorize_get_fo_candidate :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifRelFoId s t pd fn v pmv fmv uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) (FactorizeCandidateS s t pd fn v pmv fmv uv)
factorize_get_fo_candidate fot = do
	{
		ines <- mzoom lens_esunifdgraph_dgraph (st_searchInEqDGFOEdges [] [] fot);
		if ((length ines) <= 1) then (return NoFactorize) else do
		{			
			inhs <- mzoom lens_esunifdgraph_dgraph (traverse eqDGFOEdge_head ines);
			inhsots <- mzoom lens_esunifdgraph_dgraph (traverse getEquivDGSONodes inhs);
			-- Either all of the heads are functions, or all are predicates. If not, throw an error.
			if (all (all is_fsonode) inhsots) then do
			{
				let {infhsots = ((Prelude.map from_fsonode) . (Prelude.filter is_fsonode)) <$> inhsots};
				if (all (any (not . isvar_sot)) infhsots) then (return (ZeroFactorizeFO fot))
				else if (any (any (not . isvar_sot)) infhsots) then do
				{
					let {avar = case (fromJustErr "Outer fromJust factorize_get_fo_candidate function" (find isvar_sot (fromJustErr "Inner fromJust factorize_get_fo_candidate function" (find (all isvar_sot) infhsots)))) of {UVar x -> x}};
					return (SingleFactorizeFOF fot avar)
				}
				else do
				{
					let {avar = case (head (head infhsots)) of {UVar x -> x}; nvars = length infhsots};
					return (MultiFactorizeF avar nvars)
				}				
			}
			else if (all (all is_psonode) inhsots) then do
			{
				let {inphsots = ((Prelude.map from_psonode) . (Prelude.filter is_psonode)) <$> inhsots};
				if (all (any (not . isvar_soa)) inphsots) then (return (ZeroFactorizeFO fot))
				else if (any (any (not . isvar_soa)) inphsots) then do
				{
					let {avar = case (fromJustErr "Outer fromJust factorize_get_fo_candidate predicate" (find isvar_soa (fromJustErr "Inner fromJust factorize_get_fo_candidate predicate" (find (all isvar_soa) inphsots)))) of {UVar x -> x}};
					return (SingleFactorizeFOP fot avar)
				}
				else do
				{
					let {avar = case (head (head inphsots)) of {UVar x -> x}; nvars = length inphsots};
					return (MultiFactorizeP avar nvars)
				}
			}
			else (error "factorize_get_fo_candidate: Some of the heads are functions and some are predicates!")
		}
	}

factorize_get_so_candidate :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifRelSoId s t pd fn v pmv fmv uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) (FactorizeCandidateS s t pd fn v pmv fmv uv)
factorize_get_so_candidate sot = do
	{
		ines <- mzoom lens_esunifdgraph_dgraph (st_searchInEqDGSOEdges [] [] sot);
		if ((length ines) <= 1) then (return NoFactorize) else do
		{
			inhs <- mzoom lens_esunifdgraph_dgraph (traverse eqDGSOEdge_head ines);
			inhsots <- mzoom lens_esunifdgraph_dgraph (m_concat getEquivDGSONodes inhs);
			-- Either all of the heads are functions, or all are predicates. If not, throw an error.
			if (all is_fsonode inhsots) then do
			{
				let {infhsots = Prelude.map from_fsonode (Prelude.filter is_fsonode inhsots)};
				if (all (not . isvar_sot) infhsots) then (return (ZeroFactorizeSO sot))
				else if (any (not . isvar_sot) infhsots) then do
				{
					let {avar = case (fromJust (find isvar_sot infhsots)) of {UVar x -> x}};
					return (SingleFactorizeSOF sot avar)
				}
				else do
				{
					let {avar = case (head infhsots) of {UVar x -> x}; nvars = length infhsots};
					return (MultiFactorizeF avar nvars)
				}
			}
			else if (all is_psonode inhsots) then do
			{
				let {inphsots = Prelude.map from_psonode (Prelude.filter is_psonode inhsots)};
				if (all (not . isvar_soa) inphsots) then (return (ZeroFactorizeSO sot))
				else if (any (not . isvar_soa) inphsots) then do
				{
					let {avar = case (fromJust (find isvar_soa inphsots)) of {UVar x -> x}};
					return (SingleFactorizeSOP sot avar)
				}
				else do
				{
					let {avar = case (head inphsots) of {UVar x -> x}; nvars = length inphsots};
					return (MultiFactorizeP avar nvars)
				}
			}
			else (error "factorize_get_so_candidate: Some of the heads are functions and some are predicates!")
		}
	}

-- Partially instantiates a variable to remove the dependency to some of its arguments. This is used for half factorization of first-order nodes.
-- The list of indices are those arguments to REMOVE from the dependency.
factorize_in_nondep :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => fmv -> [Int] -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) ()
factorize_in_nondep sov rems = do
	{
		let {aty = arity sov; keeps = Prelude.filter (not . (\x -> elem x rems)) [0..(aty -1)]};
		let {vsot = UVar sov; vsotid = relbwEqDGSoId (FSONode vsot)};
		let {naty = length keeps};
		nsov <- mzoom lens_esunifdgraph_sosig (new_sovar naty);
		let {nvsot = UVar nsov; nvsotid = relbwEqDGSoId (FSONode nvsot)};
		let {fproj = (\idx -> relbwEqDGSoId (FSONode (UTerm (SOF (Proj idx)))))};
		let {nss = fproj <$> keeps};

		ops <- prop_newEqDGSOEdge nvsotid nss vsotid;

		runStateTOps ops
	}

-- We assume the second-order term being given is indeed simple (not a composition), and non-variable. This should be true in every case anyway.
factorize_in_flexrigid_fn :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => fmv -> SOTerm fn fmv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) ()
factorize_in_flexrigid_fn sov sot = do
	{
		gtraceM False "Factorizing flexrigid";
		--strb <- show_esuvdg;
		gtraceM False "BEFORE:";
		--gtraceM False strb;
		let {vsot = UVar sov; vsotid = relbwEqDGSoId (FSONode vsot); vaty = arity sov};
		let {aty = arity sot; sotid = relbwEqDGSoId (FSONode sot)};		
		let {fnewvar = mzoom lens_esunifdgraph_sosig (new_sovar vaty); fnewnode = (\_ -> relbwEqDGSoId . FSONode . UVar <$> fnewvar)};
		gtraceM False "BEFORE TRAVERSE FNEWNODE";
		str1 <- show_esuvdg;
		gtraceM False str1;
		newss <- traverse fnewnode [0..(aty-1)];
		gtraceM False "AFTER TRAVERSE FNEWNODE";
		str2 <- show_esuvdg;
		gtraceM False str2;
		gtraceM False "BEFORE NEW EDGE";
		str3 <- show_esuvdg;
		gtraceM False str3;
		ops <- prop_newEqDGSOEdge sotid newss vsotid;
		gtraceM False "AFTER NEW EDGE";
		str4 <- show_esuvdg;
		gtraceM False str4;
		
		stra <- show_esuvdg;
		gtraceM False "AFTER:";
		gtraceM False stra;

		runStateTOps ops
	}

factorize_in_flexrigid_pd :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => pmv -> SOAtom pd fn pmv fmv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) ()
factorize_in_flexrigid_pd psov soa = do
	{
		gtraceM False "Factorizing flexrigid";
		strb <- mzoom lens_esunifdgraph_dgraph st_dump_eqdgraph;
		gtraceM False "BEFORE:";
		gtraceM False strb;
		let {vsoa = UVar psov; vsoaid = relbwEqDGSoId (PSONode vsoa); vaty = arity psov};
		let {aty = arity soa; soaid = relbwEqDGSoId (PSONode soa)};		
		let {fnewvar = mzoom lens_esunifdgraph_sosig (new_sovar vaty); fnewnode = (\_ -> relbwEqDGSoId . FSONode . UVar <$> fnewvar)};
		newss <- traverse fnewnode [0..(aty-1)];
		gtraceM False "BEFORE NEW EDGE";
		ops <- prop_newEqDGSOEdge soaid newss vsoaid;
		gtraceM False "AFTER NEW EDGE";
		
		stra <- mzoom lens_esunifdgraph_dgraph st_dump_eqdgraph;
		gtraceM False "AFTER:";
		gtraceM False stra;

		runStateTOps ops
	}


factorize_in_proj :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => fmv -> Int -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) ()
factorize_in_proj sov idx = do
	{
		gtraceM False "Factorizing proj";
		strb <- mzoom lens_esunifdgraph_dgraph st_dump_eqdgraph;
		gtraceM False "BEFORE:";
		gtraceM False strb;
		let {sot = UVar sov; sotid = relbwEqDGSoId (FSONode sot)};
		let {projt = UTerm (SOF (Proj idx)); projid = relbwEqDGSoId (FSONode projt)};
		
		ops <- prop_mergeEqDGSONodes sotid projid;
		
		stra <- mzoom lens_esunifdgraph_dgraph st_dump_eqdgraph;
		gtraceM False "AFTER:";
		gtraceM False stra;

		runStateTOps ops
	}

-- Factorizes all rigid incoming heads to the node, merging them into one.
-- It also merges the sources of all the edges with these heads coming into the target node.
-- There may be no rigid incoming head, or multiple incompatible ones, so we use ExistUnique to indicate this.
-- This does not do anything with variable incoming heads. Therefore, the result is deterministic (except for potentially generating incompatibilities).
factorize_in_sot_rigid :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifRelSoId s t pd fn v pmv fmv uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) (ExistUnique (Either (SOTerm fn fmv) (SOAtom pd fn pmv fmv)))
factorize_in_sot_rigid sot = do
	{
		ines <- mzoom lens_esunifdgraph_dgraph (st_searchInEqDGSOEdges [] [] sot);
		inhs <- mzoom lens_esunifdgraph_dgraph (traverse eqDGSOEdge_head ines);
		inhsots <- mzoom lens_esunifdgraph_dgraph (m_concat getEquivDGSONodes inhs);
		let {fhsots = Prelude.map from_fsonode (Prelude.filter is_fsonode inhsots); phsots = Prelude.map from_psonode (Prelude.filter is_psonode inhsots); nvfhsots = Prelude.filter (not . isvar_sot) fhsots; nvphsots = Prelude.filter (not . isvar_soa) phsots};
		if ((not . Prelude.null) fhsots) then do
		{
			if ((not . Prelude.null) phsots) then (return Distinct) else do
			{			
				if (allEq nvfhsots) then do
				{
					if (Prelude.null nvfhsots) then (return Inexistent)
					else do
					{
						let {(mainh:otherhs) = nvfhsots; mainhid = relbwEqDGSoId (FSONode mainh)};
						-- let {otherhids = Prelude.map (relbwEqDGSoId . FSONode) otherhs};
						(maine:otheres) <- mzoom lens_esunifdgraph_dgraph (st_searchInEqDGSOEdges [mainhid] [] sot);
						let {fgetss = (\e -> mzoom lens_esunifdgraph_dgraph (do {re <- st_getCurEqDGSOEdge e; eqDGSOEdge_sources re}))};
						mainss <- fgetss maine;
						--otheres <- mzoom lens_esunifdgraph_dgraph (traverse (\h -> head <$> st_searchInEqDGSOEdges [h] [] sot) otherhids);
						let {freme = (\e -> do {re <- mzoom lens_esunifdgraph_dgraph (st_getCurEqDGSOEdge e); prop_deleteEqDGSOEdge re})};
						let {fdoss = (\e -> do {ss <- fgetss e; ops1 <- m_concat (uncurry prop_mergeEqDGSONodes) (zip mainss ss); ops2 <- freme e; return (ops1++ops2)})};
						
						ops <- m_concat fdoss otheres;

						-- We do not need to merge the heads because they are already equal, and that SHOULD mean that they are equivalent nodes in the graph. If they are not, we got ourselves some trouble.
						--ops2 <- m_concat (prop_mergeEqDGSONodes mainhid) otherhids;

						runStateTOps ops;

						return (Exist (Left mainh))
					}
				}
				else (return Distinct)
			}
		}
		else if ((not . Prelude.null) phsots) then do
		{
			if (allEq nvphsots) then do
			{
				if (Prelude.null nvphsots) then (return Inexistent)
				else do
				{
					let {(mainh:otherhs) = nvphsots; mainhid = relbwEqDGSoId (PSONode mainh)};
					-- let {otherhids = Prelude.map (relbwEqDGSoId . PSONode) otherhs};
					(maine:otheres) <- mzoom lens_esunifdgraph_dgraph (st_searchInEqDGSOEdges [mainhid] [] sot);
					let {fgetss = (\e -> mzoom lens_esunifdgraph_dgraph (do {re <- st_getCurEqDGSOEdge e; eqDGSOEdge_sources re}))};
					mainss <- fgetss maine;
					--otheres <- mzoom lens_esunifdgraph_dgraph (traverse (\h -> head <$> st_searchInEqDGSOEdges [h] [] sot) otherhids);
					let {freme = (\e -> do {re <- mzoom lens_esunifdgraph_dgraph (st_getCurEqDGSOEdge e); prop_deleteEqDGSOEdge re})};
					let {fdoss = (\e -> do {ss <- fgetss e; ops1 <- m_concat (uncurry prop_mergeEqDGSONodes) (zip mainss ss); ops2 <- freme e; return (ops1++ops2)})};
					
					ops <- m_concat fdoss otheres;

					-- We do not need to merge the heads because they are already equal, and that SHOULD mean that they are equivalent nodes in the graph. If they are not, we got ourselves some trouble.
					--ops2 <- m_concat (prop_mergeEqDGSONodes mainhid) otherhids;

					runStateTOps ops;

					return (Exist (Right mainh))
				}
			}
			else (return Distinct)
		}
		else (return Inexistent)
	}

factorize_in_fot_rigid :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifRelFoId s t pd fn v pmv fmv uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) (ExistUnique (Either (SOTerm fn fmv) (SOAtom pd fn pmv fmv)))
factorize_in_fot_rigid fot = do
	{
		ines <- mzoom lens_esunifdgraph_dgraph (st_searchInEqDGFOEdges [] [] fot);
		inhs <- mzoom lens_esunifdgraph_dgraph (traverse eqDGFOEdge_head ines);
		inhsots <- mzoom lens_esunifdgraph_dgraph (m_concat getEquivDGSONodes inhs);
		let {fhsots = Prelude.map from_fsonode (Prelude.filter is_fsonode inhsots); phsots = Prelude.map from_psonode (Prelude.filter is_psonode inhsots); nvfhsots = Prelude.filter (not . isvar_sot) fhsots; nvphsots = Prelude.filter (not . isvar_soa) phsots};
		if ((not . Prelude.null) fhsots) then do
		{
			if ((not . Prelude.null) phsots) then (return Distinct) else do
			{
				if (allEq nvfhsots) then do
				{
					if (Prelude.null nvfhsots) then (return Inexistent)
					else do
					{
						let {(mainh:otherhs) = nvfhsots; mainhid = relbwEqDGSoId (FSONode mainh)};
						-- let {otherhids = Prelude.map (relbwEqDGSoId . FSONode) otherhs};
						(maine:otheres) <- mzoom lens_esunifdgraph_dgraph (st_searchInEqDGFOEdges [mainhid] [] fot);
						let {fgetss = (\e -> mzoom lens_esunifdgraph_dgraph (do {re <- st_getCurEqDGFOEdge e; eqDGFOEdge_sources re}))};
						mainss <- fgetss maine;
						--otheres <- mzoom lens_esunifdgraph_dgraph (traverse (\h -> (head . (Prelude.filter (/= maine))) <$> st_searchInEqDGFOEdges [h] [] fot) otherhids);
						let {freme = (\e -> do {re <- mzoom lens_esunifdgraph_dgraph (st_getCurEqDGFOEdge e); prop_deleteEqDGFOEdge re})};
						let {fdoss = (\e -> do {ss <- fgetss e; ops1 <- m_concat (uncurry prop_mergeEqDGFONodes) (zip mainss ss); ops2 <- freme e; return (ops1++ops2)})};
						
						ops <- m_concat fdoss otheres;

						-- We do not need to merge the heads because they are already equal, and that SHOULD mean that they are equivalent nodes in the graph. If they are not, we got ourselves some trouble.
						--ops2 <- m_concat (prop_mergeEqDGSONodes mainhid) otherhids;

						runStateTOps ops;

						return (Exist (Left mainh))
					}
				}
				else (return Distinct)
			}
		}
		else if ((not . Prelude.null) phsots) then do
		{
			if (allEq nvphsots) then do
			{
				if (Prelude.null nvphsots) then (return Inexistent)
				else do
				{
					let {(mainh:otherhs) = nvphsots; mainhid = relbwEqDGSoId (PSONode mainh)};
					-- let {otherhids = Prelude.map (relbwEqDGSoId . PSONode) otherhs};
					(maine:otheres) <- mzoom lens_esunifdgraph_dgraph (st_searchInEqDGFOEdges [mainhid] [] fot);
					let {fgetss = (\e -> mzoom lens_esunifdgraph_dgraph (do {re <- st_getCurEqDGFOEdge e; eqDGFOEdge_sources re}))};
					mainss <- fgetss maine;
					--otheres <- mzoom lens_esunifdgraph_dgraph (traverse (\h -> (head . (Prelude.filter (/= maine))) <$> st_searchInEqDGFOEdges [h] [] fot) otherhids);
					let {freme = (\e -> do {re <- mzoom lens_esunifdgraph_dgraph (st_getCurEqDGFOEdge e); prop_deleteEqDGFOEdge re})};
					let {fdoss = (\e -> do {ss <- fgetss e; ops1 <- m_concat (uncurry prop_mergeEqDGFONodes) (zip mainss ss); ops2 <- freme e; return (ops1++ops2)})};
					
					ops <- m_concat fdoss otheres;

					-- We do not need to merge the heads because they are already equal, and that SHOULD mean that they are equivalent nodes in the graph. If they are not, we got ourselves some trouble.
					--ops2 <- m_concat (prop_mergeEqDGSONodes mainhid) otherhids;

					runStateTOps ops;

					return (Exist (Right mainh))
				}
			}
			else (return Distinct)
		}
		else (return Inexistent)		
	}

validate_all_consistency :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => AnswerSet (RESUnifVDGraph t mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv) -> AnswerSet (RESUnifVDGraph t mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv)
validate_all_consistency as = as ?>>= SOTConsistency ?>>= FOTConsistency ?>>= HeadAritySO ?>>= HeadArityFO ?>>= OccursCheckSO ?>>= OccursCheckFO

validate_occurs_check_fo :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => RESUnifVDGraph t mpd pd fn v pmv fmv uv -> AnswerSet (RESUnifVDGraph t mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv)
validate_occurs_check_fo resuvdg = if consistent then (ImplicitAS resuvdg) else (ExplicitAS EnumProc.Empty)
	where
		checked = occurs_check_fo;
		consistent = getStateTSTESUnifVDGraph checked resuvdg

occurs_check_fo :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) Bool
occurs_check_fo = do
	{
		esuvdg <- get;
		let {nodes = Prelude.map (DirectId . EqDGFoId . dgid . fromJust) (Prelude.filter isJust (esuvdg ^. (lens_esunifdgraph_dgraph . lens_eqdgraph . lens_fonodes)))};
		cycle_up <- traverse_collect ff (check_cycle_up_fot [] []) nodes;		
		
		case cycle_up of
		{
			(False,_) -> return True;
			(True,setpairs) -> m_any (\(downhs,downs) -> do
				{
					downhts <- mzoom lens_esunifdgraph_dgraph (m_concat getEquivDGSONodes downhs);
					downts <- mzoom lens_esunifdgraph_dgraph (m_concat getEquivDGFONodes downs);
					let {fdownhts = Prelude.filter (\sot -> ((is_fsonode sot) && ((not . isvar_sot . from_fsonode) sot) && ((not . isproj_sot . from_fsonode) sot)) || ((is_psonode sot) && ((not . isvar_soa . from_psonode) sot))) downhts};
					let {sdownts = nub downts};
					
					if (not (Prelude.null fdownhts)) then (return False) else (if (not ((length sdownts) <= 1)) then (return False) else (return True))
				}) setpairs
		}
	}
	where 
		f = (\(f1,t1) -> \(f2,t2) -> (f1 || f2,t1++t2));
		ff = Prelude.foldr f (False,[])

-- The values in the return type indicate:
--	Bool: Has a cycle been found or not?
--	List: Each pair refers to a particular path that has been found. The values of these pair are:
--		First value: List of all the heads on the path.
--		Second value: List of all the targets/sources on the path.
check_cycle_up_fot :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => [ESUnifRelSoId s t pd fn v pmv fmv uv] -> [ESUnifRelFoId s t pd fn v pmv fmv uv] -> ESUnifRelFoId s t pd fn v pmv fmv uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) (Bool,[([ESUnifRelSoId s t pd fn v pmv fmv uv],[ESUnifRelFoId s t pd fn v pmv fmv uv])])
check_cycle_up_fot downhs downs fot = do
	{
		cycle <- mzoom lens_esunifdgraph_dgraph (m_any (eqSTRelativeEqDGFoIds fot) downs);
		if cycle then (return (True,[(downhs,downs)])) else do
		{
			ines <- mzoom lens_esunifdgraph_dgraph (st_searchInEqDGFOEdges [] [] fot);
			-- For occurs check purposes, edges whose head contains variables are not relevant.
			let {ffil = (\e -> do
				{
					h <- mzoom lens_esunifdgraph_dgraph (eqDGFOEdge_head e);
					hels <- mzoom lens_esunifdgraph_dgraph (getEquivDGSONodes h);
					let {fhels = Prelude.map from_fsonode (Prelude.filter is_fsonode hels); phels = Prelude.map from_psonode (Prelude.filter is_psonode hels)};
					if (not (Prelude.null fhels)) then (return (any (not . isvar_sot) fhels))
					else if (not (Prelude.null phels)) then (return (any (not . isvar_soa) phels))
					else (return False)
				})};
			let {ffil_v = (\e -> do
				{
					h <- mzoom lens_esunifdgraph_dgraph (eqDGFOEdge_head e);
					hels <- mzoom lens_esunifdgraph_dgraph (getEquivDGSONodes h);
					let {fhels = Prelude.map from_fsonode (Prelude.filter is_fsonode hels); phels = Prelude.map from_psonode (Prelude.filter is_psonode hels)};
					if (not (Prelude.null fhels)) then (return (all isvar_sot fhels))
					else if (not (Prelude.null phels)) then (return (all isvar_soa phels))
					else (return True)
				})};
			rines <- m_filter ffil ines;
			rines_v <- m_filter ffil_v ines;
			ssh <- mzoom lens_esunifdgraph_dgraph (traverse fh rines);
			ssh_v <- mzoom lens_esunifdgraph_dgraph (traverse fh_v rines_v);
			ups <- traverse_collect ff ffd ssh;
			ups_v <- traverse_collect ff ffd_v ssh_v;
			return (f ups ups_v)
		}
	}
	where 
		f = (\(f1,t1) -> \(f2,t2) -> (f1 || f2,t1++t2));
		ff = Prelude.foldr f (False,[]);
		fh = (\e -> do {h <- eqDGFOEdge_head e; ss <- eqDGFOEdge_sources e; return (h,ss)});
		fh_v = (\e -> do {h <- eqDGFOEdge_head e; ss <- eqDGFOEdge_sources e; return (h,ss)});
		fd = (\h -> \s -> check_cycle_up_fot (h:downhs) (fot:downs) s);
		ffd = (\(h,ss) -> traverse_collect ff (fd h) ss);
		fd_v = (\h -> \s -> check_cycle_up_fot downhs (fot:downs) s);
		ffd_v = (\(h,ss) -> traverse_collect ff (fd_v h) ss);

validate_occurs_check_so :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => RESUnifVDGraph t mpd pd fn v pmv fmv uv -> AnswerSet (RESUnifVDGraph t mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv)
validate_occurs_check_so resuvdg = if consistent then (ImplicitAS resuvdg) else (ExplicitAS EnumProc.Empty)
	where
		checked = occurs_check_so;
		consistent = getStateTSTESUnifVDGraph checked resuvdg

occurs_check_so :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) Bool
occurs_check_so = do
	{
		esuvdg <- get;
		let {nodes = Prelude.map (DirectId . EqDGSoId . dgid . fromJust) (Prelude.filter isJust (esuvdg ^. (lens_esunifdgraph_dgraph . lens_eqdgraph . lens_sonodes)))};
		cycle_up <- traverse_collect ff (check_cycle_up_sot [] []) nodes;		
		
		case cycle_up of
		{
			(False,_) -> return True;
			(True,setpairs) -> m_any (\(downhs,downs) -> do
				{
					downhts <- mzoom lens_esunifdgraph_dgraph (m_concat getEquivDGSONodes downhs);
					downts <- mzoom lens_esunifdgraph_dgraph (m_concat getEquivDGSONodes downs);
					let {fdownts = Prelude.filter (\sot -> ((is_fsonode sot) && ((not . isvar_sot . from_fsonode) sot) && ((not . isproj_sot . from_fsonode) sot)) || ((is_psonode sot) && ((not . isvar_soa . from_psonode) sot))) (downhts ++ downts)};
					let {sdownts = nub fdownts};
					
					if (not ((length sdownts) <= 1)) then (return False) else (return True)
				}) setpairs
		}
	}
	where 
		f = (\(f1,t1) -> \(f2,t2) -> (f1 || f2,t1++t2));
		ff = Prelude.foldr f (False,[])

-- The values in the return type indicate:
--	Bool: Has a cycle been found or not?
--	List: Each pair refers to a particular path that has been found. The values of these pair are:
--		First value: List of all the heads on the path.
--		Second value: List of all the targets/sources on the path.
check_cycle_up_sot :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => [ESUnifRelSoId s t pd fn v pmv fmv uv] -> [ESUnifRelSoId s t pd fn v pmv fmv uv] -> ESUnifRelSoId s t pd fn v pmv fmv uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) (Bool,[([ESUnifRelSoId s t pd fn v pmv fmv uv],[ESUnifRelSoId s t pd fn v pmv fmv uv])])
check_cycle_up_sot downhs downs sot = do
	{		
		cycle <- mzoom lens_esunifdgraph_dgraph (m_any (eqSTRelativeEqDGSoIds sot) downs);
		-- If the current node only contains variables, do not count it for occurs check.
		allv <- do
			{
				els <- mzoom lens_esunifdgraph_dgraph (getEquivDGSONodes sot);
				let {fels = Prelude.map from_fsonode (Prelude.filter is_fsonode els); pels = Prelude.map from_psonode (Prelude.filter is_psonode els)};
				if (not (Prelude.null fels)) then (return (all isvar_sot fels))
				else if (not (Prelude.null pels)) then (return (all isvar_soa pels))
				else (return True)
			};
		if ((not allv) && cycle) then (return (True,[(downhs,downs)])) else do
		{
			ines <- mzoom lens_esunifdgraph_dgraph (st_searchInEqDGSOEdges [] [] sot);
			-- For occurs check purposes, edges whose head contains variables are not relevant.
			let {ffil = (\e -> do
				{
					h <- mzoom lens_esunifdgraph_dgraph (eqDGSOEdge_head e);
					hels <- mzoom lens_esunifdgraph_dgraph (getEquivDGSONodes h);
					let {fhels = Prelude.map from_fsonode (Prelude.filter is_fsonode hels); phels = Prelude.map from_psonode (Prelude.filter is_psonode hels)};
					if (not (Prelude.null fhels)) then (return (any (not . isvar_sot) fhels))
					else if (not (Prelude.null phels)) then (return (any (not . isvar_soa) phels))
					else (return False)
				})};
			let {ffil_v = (\e -> do
				{
					h <- mzoom lens_esunifdgraph_dgraph (eqDGSOEdge_head e);
					hels <- mzoom lens_esunifdgraph_dgraph (getEquivDGSONodes h);
					let {fhels = Prelude.map from_fsonode (Prelude.filter is_fsonode hels); phels = Prelude.map from_psonode (Prelude.filter is_psonode hels)};
					if (not (Prelude.null fhels)) then (return (all isvar_sot fhels))
					else if (not (Prelude.null phels)) then (return (all isvar_soa phels))
					else (return True)
				})};
			rines <- m_filter ffil ines;
			rines_v <- m_filter ffil_v ines;
			ssh <- mzoom lens_esunifdgraph_dgraph (traverse fh rines);
			ups <- traverse_collect ff ffd ssh;
			ssh_v <- mzoom lens_esunifdgraph_dgraph (traverse fh_v rines_v);
			ups_v <- traverse_collect ff ffd_v ssh_v;
			return (f ups ups_v)
		}
	}
	where 
		f = (\(f1,t1) -> \(f2,t2) -> (f1 || f2,t1++t2));
		ff = Prelude.foldr f (False,[]);
		fh = (\e -> do {h <- eqDGSOEdge_head e; ss <- eqDGSOEdge_sources e; return (h,ss)});
		fh_v = (\e -> do {h <- eqDGSOEdge_head e; ss <- eqDGSOEdge_sources e; return (h,ss)});
		fd = (\h -> \s -> check_cycle_up_sot (h:downhs) (sot:downs) s);		
		ffd = (\(h,ss) -> do {rss <- traverse_collect ff (fd h) ss; rh <- check_cycle_up_sot downhs (sot:downs) h; return (f rss rh)});
		fd_v = (\h -> \s -> check_cycle_up_sot downhs (sot:downs) s);
		ffd_v = (\(h,ss) -> do {rss <- traverse_collect ff (fd_v h) ss; rh <- check_cycle_up_sot downhs (sot:downs) h; return (f rss rh)});

validate_target_arity_so :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => RESUnifVDGraph t mpd pd fn v pmv fmv uv -> AnswerSet (RESUnifVDGraph t mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv)
validate_target_arity_so resuvdg = if consistent then (ImplicitAS resuvdg) else (ExplicitAS EnumProc.Empty)
	where
		sots = getStateTSTESUnifVDGraph (do
		{
			esuvdg <- get;
			let {eqdg = eqdgraph . esunifdgraph $ esuvdg; nodes = eqdg ^. lens_sonodes; filtered = Prelude.filter isJust nodes; ids = Prelude.map (DirectId . EqDGSoId . dgid . fromJust) filtered};
			return ids
		}) resuvdg;
		checked = all id <$> traverse check_target_arity_sot sots;
		consistent = getStateTSTESUnifVDGraph checked resuvdg

validate_target_arity_sot :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => (forall s. ESUnifRelSoId s t pd fn v pmv fmv uv) -> RESUnifVDGraph t mpd pd fn v pmv fmv uv -> AnswerSet (RESUnifVDGraph t mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv)
validate_target_arity_sot sot resuvdg = if consistent then (ImplicitAS resuvdg) else (ExplicitAS EnumProc.Empty) where consistent = getStateTSTESUnifVDGraph (check_target_arity_sot sot) resuvdg

check_target_arity_so :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) Bool
check_target_arity_so = (StateT (\esuvdg -> runStateT (all id <$> traverse check_target_arity_sot (Prelude.map (DirectId . EqDGSoId . dgid . fromJust) (Prelude.filter isJust ((eqdgraph (esunifdgraph esuvdg)) ^. lens_sonodes)))) esuvdg))

check_target_arity_sot :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifRelSoId s t pd fn v pmv fmv uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) Bool
check_target_arity_sot sot = mzoom lens_esunifdgraph_dgraph (do
	{
		sots <- getEquivDGSONodes sot;
		let {fsots = Prelude.map from_fsonode (Prelude.filter is_fsonode sots); psots = Prelude.map from_psonode (Prelude.filter is_psonode sots)};
		-- They must all be variables! If they are not, then all incoming edges must have variable heads; and as long as that's true, it's correct.
		if (not ((all isvar_sot fsots) && (all isvar_soa psots))) then do
		{
			ines <- st_searchInEqDGSOEdges [] [] sot;
			inhs <- traverse eqDGSOEdge_head ines;
			inhsots <- m_concat getEquivDGSONodes inhs;
			let {infhsots = Prelude.map from_fsonode (Prelude.filter is_fsonode inhsots); inphsots = Prelude.map from_psonode (Prelude.filter is_psonode inhsots)};
			return ((all isvar_sot infhsots) && (all isvar_soa inphsots))
		}
		else do
		{
			sott <- getSTRelativeEqDGSoCoId sot;
			let {sota = (\asott -> case asott of { FSONode fsott -> arity fsott; PSONode psott -> arity psott }) <$> sott};
			
			nodea <- getNodeArity sot;
			
			case nodea of
			{
				Nothing -> return True;
				Just rnodea -> case sota of
				{
					Nothing -> return True;
					Just rsota -> return (rsota >= rnodea)
				}
			}
		}
	})

getSOTArity :: (HasArity fn, HasArity fmv) => Maybe (SOTerm fn fmv) -> Maybe Int
getSOTArity = fmap sot_min_arity

getSOAArity :: (HasArity fn, HasArity pd, HasArity pmv, HasArity fmv) => Maybe (SOAtom pd fn pmv fmv) -> Maybe Int
getSOAArity = fmap soa_min_arity

getSOTAArity :: (HasArity fn, HasArity pd, HasArity pmv, HasArity fmv) => Maybe (ESUnifDGSONode pd fn pmv fmv) -> Maybe Int
getSOTAArity Nothing = Nothing
getSOTAArity (Just (FSONode x)) = getSOTArity (Just x)
getSOTAArity (Just (PSONode x)) = getSOAArity (Just x)

getNodeArity :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifRelSoId s t pd fn v pmv fmv uv -> StateT (ESUnifDGraph s t pd fn v pmv fmv uv) (ST s) (Maybe Int)
getNodeArity sot = do
	{
		ines <- st_searchInEqDGSOEdges [] [] sot;
		if (Data.List.null ines) then do
		{
			rep <- getSTRelativeEqDGSoCoId sot;
			return (getSOTAArity rep)
		}
		else do
		{
			let {fe = (\ine -> do
			{
				ss <- eqDGSOEdge_sources ine;
				ars <- traverse getNodeArity ss;
				let {fars = Prelude.map fromJust (Prelude.filter isJust ars)};
				return (maximumMay fars)
			})};
			arss <- traverse fe ines;
			let {farss = Prelude.map fromJust (Prelude.filter isJust arss)};
			return (maximumMay farss)
		}
	}

validate_head_arity_fo :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => RESUnifVDGraph t mpd pd fn v pmv fmv uv -> AnswerSet (RESUnifVDGraph t mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv)
validate_head_arity_fo resuvdg = if consistent then (ImplicitAS resuvdg) else (ExplicitAS EnumProc.Empty) 
	where
		foes = getStateTSTESUnifVDGraph (do
		{
			esuvdg <- get;
			let {eqdg = eqdgraph . esunifdgraph $ esuvdg; edges = eqdg ^. lens_foedges; filtered = Prelude.filter isJust edges; ids = Prelude.map (dgid . fromJust) filtered};
			return ids
		}) resuvdg;
		checked = all id <$> traverse check_head_arity_foe foes;
		consistent = getStateTSTESUnifVDGraph checked resuvdg

validate_head_arity_foe :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => Int -> RESUnifVDGraph t mpd pd fn v pmv fmv uv -> AnswerSet (RESUnifVDGraph t mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv)
validate_head_arity_foe foe resuvdg = if consistent then (ImplicitAS resuvdg) else (ExplicitAS EnumProc.Empty) where consistent = getStateTSTESUnifVDGraph (check_head_arity_foe foe) resuvdg

check_head_arity_fo :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) Bool
check_head_arity_fo = (StateT (\esuvdg -> runStateT (all id <$> traverse check_head_arity_foe (Prelude.map (dgid . fromJust) (Prelude.filter isJust ((eqdgraph (esunifdgraph esuvdg)) ^. lens_foedges)))) esuvdg))

check_head_arity_foe :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => Int -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) Bool
check_head_arity_foe foe = do
	{
		h <- mzoom lens_esunifdgraph_dgraph (eqDGFOEdge_head foe);
		sots <- mzoom lens_esunifdgraph_dgraph (getEquivDGSONodes h);
		let {fsots = Prelude.map from_fsonode (Prelude.filter is_fsonode sots); psots = Prelude.map from_psonode (Prelude.filter is_psonode sots)};
		let {farities = Prelude.map sot_min_arity fsots; parities = Prelude.map soa_min_arity psots; arities = farities ++ parities; arity = Prelude.foldr (\i -> \m -> max i m) 0 arities};
		ss <- mzoom lens_esunifdgraph_dgraph (eqDGFOEdge_sources foe);
		return ((length ss) >= arity)
	}

validate_head_arity_so :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => RESUnifVDGraph t mpd pd fn v pmv fmv uv -> AnswerSet (RESUnifVDGraph t mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv)
validate_head_arity_so resuvdg = if consistent then (ImplicitAS resuvdg) else (ExplicitAS EnumProc.Empty)
	where
		soes = getStateTSTESUnifVDGraph (do
		{
			esuvdg <- get;
			let {eqdg = eqdgraph . esunifdgraph $ esuvdg; edges = eqdg ^. lens_soedges; filtered = Prelude.filter isJust edges; ids = Prelude.map (dgid . fromJust) filtered};
			return ids
		}) resuvdg;
		checked = all id <$> traverse check_head_arity_soe soes;
		consistent = getStateTSTESUnifVDGraph checked resuvdg

validate_head_arity_soe :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => Int -> RESUnifVDGraph t mpd pd fn v pmv fmv uv -> AnswerSet (RESUnifVDGraph t mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv)
validate_head_arity_soe soe resuvdg = if consistent then (ImplicitAS resuvdg) else (ExplicitAS EnumProc.Empty) where consistent = getStateTSTESUnifVDGraph (check_head_arity_soe soe) resuvdg

check_head_arity_so :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) Bool
check_head_arity_so = (StateT (\esuvdg -> runStateT (all id <$> traverse check_head_arity_soe (Prelude.map (dgid . fromJust) (Prelude.filter isJust ((eqdgraph (esunifdgraph esuvdg)) ^. lens_soedges)))) esuvdg))

-- IMPORTANT NOTE: We leave this as is for now, since it is likely it is enough for the implementation. However, if we want to be more accurate to the theory, what needs to happen here is that we need to re-add the arity to the projections and be strict about it, INCLUDING when handling second-order variables and consider the issue with compositions of second-order variables and projections etc.
check_head_arity_soe :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => Int -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) Bool
check_head_arity_soe soe = do
	{
		h <- mzoom lens_esunifdgraph_dgraph (eqDGSOEdge_head soe);
		sots <- mzoom lens_esunifdgraph_dgraph (getEquivDGSONodes h);
		let {fsots = Prelude.map from_fsonode (Prelude.filter is_fsonode sots); psots = Prelude.map from_psonode (Prelude.filter is_psonode sots)};
		let {farities = Prelude.map sot_min_arity fsots; parities = Prelude.map soa_min_arity psots; arities = farities ++ parities; arity = Prelude.foldr (\i -> \m -> max i m) 0 arities};
		ss <- mzoom lens_esunifdgraph_dgraph (eqDGSOEdge_sources soe);
		return ((length ss) >= arity)
	}

validate_sot_consistency :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => RESUnifVDGraph t mpd pd fn v pmv fmv uv -> AnswerSet (RESUnifVDGraph t mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv)
validate_sot_consistency resuvdg = if consistent then (ImplicitAS resuvdg) else (ExplicitAS EnumProc.Empty)
	where
		sots = getStateTSTESUnifVDGraph (do
		{
			esuvdg <- get;
			let {eqdg = eqdgraph . esunifdgraph $ esuvdg; nodes = eqdg ^. lens_sonodes; filtered = Prelude.filter isJust nodes; ids = Prelude.map (DirectId . EqDGSoId . dgid . fromJust) filtered};
			return ids
		}) resuvdg;
		checked = all id <$> traverse check_sot_consistency_sot sots;
		consistent = getStateTSTESUnifVDGraph checked resuvdg

validate_sot_consistency_sot :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => (forall s. ESUnifRelSoId s t pd fn v pmv fmv uv) -> RESUnifVDGraph t mpd pd fn v pmv fmv uv -> AnswerSet (RESUnifVDGraph t mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv)
validate_sot_consistency_sot sot resuvdg = if consistent then (ImplicitAS resuvdg) else (ExplicitAS EnumProc.Empty) where consistent = getStateTSTESUnifVDGraph (check_sot_consistency_sot sot) resuvdg

check_sot_consistency :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) Bool
check_sot_consistency = (StateT (\esuvdg -> runStateT (all id <$> traverse check_sot_consistency_sot (Prelude.map (DirectId . EqDGSoId . dgid . fromJust) (Prelude.filter isJust ((eqdgraph (esunifdgraph esuvdg)) ^. lens_sonodes)))) esuvdg))

check_sot_consistency_sot :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifRelSoId s t pd fn v pmv fmv uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) Bool
check_sot_consistency_sot sot = do
	{
		sots <- mzoom lens_esunifdgraph_dgraph (getEquivDGSONodes sot);
		let {fsots = Prelude.map from_fsonode (Prelude.filter is_fsonode sots); psots = Prelude.map from_psonode (Prelude.filter is_psonode sots)};
		if (not (Prelude.null fsots)) then do
		{
			if (not (Prelude.null psots)) then (return False) else do
			{
				let {nvsots = Prelude.filter (not . isvar_sot) fsots};
				-- NOTE: I could consider checking that all variables in the node have the same arity here. We do not do this for now, as it may be incorrect (I don't remember exactly right now) and I believe it is not necessary. But this note is a witness that this is a thing worth thinking about if it may be a source of errors.
				return (allEq nvsots)
			}
		}
		else if (not (Prelude.null psots)) then do
		{
			let {nvsots = Prelude.filter (not . isvar_soa) psots};
			
			-- NOTE: I could consider checking that all variables in the node have the same arity here. We do not do this for now, as it may be incorrect (I don't remember exactly right now) and I believe it is not necessary. But this note is a witness that this is a thing worth thinking about if it may be a source of errors.

			return (allEq nvsots)
		}
		else (return True)
	}

validate_fot_consistency :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => RESUnifVDGraph t mpd pd fn v pmv fmv uv -> AnswerSet (RESUnifVDGraph t mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv)
validate_fot_consistency resuvdg = if consistent then (ImplicitAS resuvdg) else (ExplicitAS EnumProc.Empty)
	where
		fots = getStateTSTESUnifVDGraph (do
		{
			esuvdg <- get;
			let {eqdg = eqdgraph . esunifdgraph $ esuvdg; nodes = eqdg ^. lens_fonodes; filtered = Prelude.filter isJust nodes; ids = Prelude.map (DirectId . EqDGFoId . dgid . fromJust) filtered};
			return ids
		}) resuvdg;
		checked = all id <$> traverse check_fot_consistency_fot fots;
		consistent = getStateTSTESUnifVDGraph checked resuvdg

validate_fot_consistency_fot :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => (forall s. ESUnifRelFoId s t pd fn v pmv fmv uv) -> RESUnifVDGraph t mpd pd fn v pmv fmv uv -> AnswerSet (RESUnifVDGraph t mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv)
validate_fot_consistency_fot fot resuvdg = if consistent then (ImplicitAS resuvdg) else (ExplicitAS EnumProc.Empty) where consistent = getStateTSTESUnifVDGraph (check_fot_consistency_fot fot) resuvdg

check_fot_consistency :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) Bool
check_fot_consistency = (StateT (\esuvdg -> runStateT (all id <$> traverse check_fot_consistency_fot (Prelude.map (DirectId . EqDGFoId . dgid . fromJust) (Prelude.filter isJust ((eqdgraph (esunifdgraph esuvdg)) ^. lens_fonodes)))) esuvdg))

check_fot_consistency_fot :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifRelFoId s t pd fn v pmv fmv uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) Bool
check_fot_consistency_fot fot = do
	{
		fots <- mzoom lens_esunifdgraph_dgraph (getEquivDGFONodes fot);
		let {nvfots = Prelude.filter (not . is_td_var) fots};
		return (allEq nvfots)
	}

as_esu_prenormalize :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => RESUnifVDGraph t mpd pd fn v pmv fmv uv -> AnswerSet (RESUnifVDGraph t mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv)
as_esu_prenormalize resuvdg = ImplicitAS (getStateTSTESUnifVDGraphState esu_prenormalize resuvdg)

esu_prenormalize :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) ()
esu_prenormalize = (StateT (\esuvdg -> runStateT (runStateTOps (allops esuvdg)) esuvdg)) >> pass where allops = (\esuvdg -> (esu_fo_dump_ops esuvdg) ++ (esu_so_dump_ops esuvdg) ++ (esu_so_simplify_projections_ops esuvdg) ++ (esu_fo_simplify_projections_ops esuvdg) ++ (esu_vertical_commute_ops esuvdg) ++ (esu_vertical_commute_eq_ops esuvdg) ++ (esu_vertical_align_ops esuvdg) ++ (esu_sozip_ops esuvdg) ++ (esu_fozip_ops esuvdg))

as_esu_fo_dump :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => RESUnifVDGraph t mpd pd fn v pmv fmv uv -> AnswerSet (RESUnifVDGraph t mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv)
as_esu_fo_dump resuvdg = gtrace False ("BEFORE FODUMP: \n\n" ++ (show resuvdg) ++ "\n\nAFTER FODUMP: \n\n" ++ (show r) ++ "\n") rr 
	where r = getStateTSTESUnifVDGraphState esu_fo_dump resuvdg;
		rr = ImplicitAS r

esu_fo_dump :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) ()
esu_fo_dump = (StateT (\esuvdg -> runStateT (runStateTOps (esu_fo_dump_ops esuvdg)) esuvdg)) >> pass

esu_fo_dump_ops :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifVDGraph s t mpd pd fn v pmv fmv uv -> [ESUnifDGOp s t mpd pd fn v pmv fmv uv]
esu_fo_dump_ops esuvdg = Prelude.map (ESUFODump . dgid . fromJust) (Prelude.filter isJust ((eqdgraph (esunifdgraph esuvdg)) ^. lens_foedges))

esu_fo_dump_foe :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => Int -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) [ESUnifDGOp s t mpd pd fn v pmv fmv uv]
esu_fo_dump_foe foe = do
	{
		gtraceM False "BEFORE FODUMP";
		esuvdg <- get;
		let {sig = esunifdgraph_sosig esuvdg};
		show1 <- show_esuvdg;
		gtraceM False show1;
		-- First check if the edge still exists!
		eex <- mzoom lens_esunifdgraph_dgraph (checkEqDGFOEdge foe);
		if (not eex) then (gtrace False "ABORTED BECAUSE NO EDGE\n" (return [])) else do
		{
			-- IMPORTANT CHOICE: We only dump when the head of an edge has EXACTLY ONE incoming edge. If it has none there's no dump to be made of course, but more importantly, if it has several, we won't dump until we factorize them. Since factorizing is the central and not always done operation, this choice has implications on what a partly normalized graph looks like.
			-- It also means that after factorizing a second-order node we need to check for dumping on all the edges it's a head of.
			h <- mzoom lens_esunifdgraph_dgraph (eqDGFOEdge_head foe);
			ss <- mzoom lens_esunifdgraph_dgraph (eqDGFOEdge_sources foe);
			t <- mzoom lens_esunifdgraph_dgraph (eqDGFOEdge_target foe);
			ines <- mzoom lens_esunifdgraph_dgraph (st_searchInEqDGSOEdges [] [] h);
			gtraceM False ("EDGES INCOMING TO HEAD: " ++ (show ines));
			if ((length ines) /= 1) then (gtrace False "ABORTED BECAUSE MULTIPLE EDGES\n" (return [])) else do
			{
				let {ine = head ines};
				rh <- mzoom lens_esunifdgraph_dgraph (eqDGSOEdge_head ine);
				rss <- mzoom lens_esunifdgraph_dgraph (eqDGSOEdge_sources ine);
				let {nsf = (\s -> prop_newAnonEqDGFOEdge s ss)};
				let {comb = (\(ns,ops) -> \(nss,opss) -> (ns:nss,ops++opss))};
				(nss,result1) <- Prelude.foldr comb ([],[]) <$> traverse nsf rss;

				result2 <- (return result1) >>=++ (prop_newEqDGFOEdge rh nss t);

				result3 <- (return result2) >>=++ (prop_deleteEqDGFOEdge foe);

				gtraceM False "AFTER FODUMP";
				show2 <- show_esuvdg;
				gtraceM False show2;

				return result3
			}
		}
	}

as_esu_so_dump :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => RESUnifVDGraph t mpd pd fn v pmv fmv uv -> AnswerSet (RESUnifVDGraph t mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv)
as_esu_so_dump resuvdg = ImplicitAS (getStateTSTESUnifVDGraphState esu_so_dump resuvdg)

esu_so_dump :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) ()
esu_so_dump = (StateT (\esuvdg -> runStateT (runStateTOps (esu_so_dump_ops esuvdg)) esuvdg)) >> pass

esu_so_dump_ops :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifVDGraph s t mpd pd fn v pmv fmv uv -> [ESUnifDGOp s t mpd pd fn v pmv fmv uv]
esu_so_dump_ops esuvdg = Prelude.map (ESUSODump . dgid . fromJust) (Prelude.filter isJust ((eqdgraph (esunifdgraph esuvdg)) ^. lens_soedges))

esu_so_dump_soe :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => Int -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) [ESUnifDGOp s t mpd pd fn v pmv fmv uv]
esu_so_dump_soe soe = do
	{
		-- First check if the edge still exists!
		eex <- mzoom lens_esunifdgraph_dgraph (checkEqDGSOEdge soe);
		if (not eex) then (return []) else do
		{
			-- IMPORTANT CHOICE: We only dump when the head of an edge has EXACTLY ONE incoming edge. If it has none there's no dump to be made of course, but more importantly, if it has several, we won't dump until we factorize them. Since factorizing is the central and not always done operation, this choice has implications on what a partly normalized graph looks like.
			-- It also means that after factorizing a second-order node we need to check for dumping on all the edges it's a head of.
			h <- mzoom lens_esunifdgraph_dgraph (eqDGSOEdge_head soe);
			ss <- mzoom lens_esunifdgraph_dgraph (eqDGSOEdge_sources soe);
			t <- mzoom lens_esunifdgraph_dgraph (eqDGSOEdge_target soe);
			ines <- mzoom lens_esunifdgraph_dgraph (st_searchInEqDGSOEdges [] [] h);
			if ((length ines) /= 1) then (return []) else do
			{
				let {ine = head ines};
				rh <- mzoom lens_esunifdgraph_dgraph (eqDGSOEdge_head ine);
				-- Check that the head does not contain a projection!
				hts <- mzoom lens_esunifdgraph_dgraph (getEquivDGSONodes rh);
				let {fhts = Prelude.map from_fsonode (Prelude.filter is_fsonode hts)};
				gtraceM False (show hts);
				if (any isproj_sot fhts) then (return []) else do
				{
					-- Also check that the head is not the same as the target!
					heq <- mzoom lens_esunifdgraph_dgraph (eqSTRelativeEqDGSoIds h t);
					if heq then (return []) else do
					{
						g <- show_esuvdg;
						gtraceM False "SODUMP BEFORE";
						gtraceM False g;
						gtraceM False "SODUMP AFTER";
						rss <- mzoom lens_esunifdgraph_dgraph (eqDGSOEdge_sources ine);
						let {nsf = (\s -> prop_newAnonEqDGSOEdge s ss)};
						let {comb = (\(ns,ops) -> \(nss,opss) -> (ns:nss,ops++opss))};
						(nss,result1) <- Prelude.foldr comb ([],[]) <$> traverse nsf rss;

						result2 <- (return result1) >>=++ (prop_newEqDGSOEdge rh nss t);

						result3 <- (return result2) >>=++ (prop_deleteEqDGSOEdge soe);

						return result3
					}
				}
			}
		}
	}

as_esu_so_simplify_projections :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => RESUnifVDGraph t mpd pd fn v pmv fmv uv -> AnswerSet (RESUnifVDGraph t mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv)
as_esu_so_simplify_projections resuvdg = ImplicitAS (getStateTSTESUnifVDGraphState esu_so_simplify_projections resuvdg)

esu_so_simplify_projections :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) ()
esu_so_simplify_projections = (StateT (\esuvdg -> runStateT (runStateTOps (esu_so_simplify_projections_ops esuvdg)) esuvdg)) >> pass

esu_so_simplify_projections_ops :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifVDGraph s t mpd pd fn v pmv fmv uv -> [ESUnifDGOp s t mpd pd fn v pmv fmv uv]
esu_so_simplify_projections_ops esuvdg = Prelude.map (ESUSOSimpProj . dgid . fromJust) (Prelude.filter isJust ((eqdgraph (esunifdgraph esuvdg)) ^. lens_soedges))

esu_so_simplify_proj_soe :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => Int -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) [ESUnifDGOp s t mpd pd fn v pmv fmv uv]
esu_so_simplify_proj_soe soe = do
	{
		-- First check if the edge still exists!
		eex <- mzoom lens_esunifdgraph_dgraph (checkEqDGSOEdge soe);
		if (not eex) then (return []) else do
		{
			-- We check if indeed the head contains projections
			h <- mzoom lens_esunifdgraph_dgraph (eqDGSOEdge_head soe);
			sots <- mzoom lens_esunifdgraph_dgraph (getEquivDGSONodes h);
			let {fsots = Prelude.map from_fsonode (Prelude.filter is_fsonode sots)};
			let {mb_proj = find isproj_sot fsots; proj = fromJustErr "esu_so_simplify_proj_soe mb_proj" mb_proj; idx = case proj of {UTerm (SOF (Proj idx)) -> idx}};
			if (isJust mb_proj) then do
			{				
				ss <- mzoom lens_esunifdgraph_dgraph (eqDGSOEdge_sources soe);
				t <- mzoom lens_esunifdgraph_dgraph (eqDGSOEdge_target soe);
				-- Note that we do not flag the incompatibility here if it so happens that there are not enough inputs to the projection, we simply do nothing if that happens. This needs to be checked outside anyway.
				-- if (length ss) <= idx then (return [])) else do
				--if (length ss) <= idx then (trace ("Projection does not have enough inputs! Has: " ++ (show (length ss)) ++ ", but is looking for " ++ (show idx) ++ "th projection.") (return [])) else do
				if (length ss) <= idx then (return []) else do
				{
					--result1 <- prop_mergeEqDGSONodes (ss !! idx) t;
					result1 <- prop_mergeEqDGSONodes (errAt "esu_so_simplify_proj_soe !!" ss idx) t;
					result2 <- (return result1) >>=++ (prop_deleteEqDGSOEdge soe);

					return result2
				}
			}
			else (return [])
		}
	}

as_esu_fo_simplify_projections :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => RESUnifVDGraph t mpd pd fn v pmv fmv uv -> AnswerSet (RESUnifVDGraph t mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv)
as_esu_fo_simplify_projections resuvdg = ImplicitAS (getStateTSTESUnifVDGraphState esu_fo_simplify_projections resuvdg)

esu_fo_simplify_projections :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) ()
esu_fo_simplify_projections = (StateT (\esuvdg -> runStateT (runStateTOps (esu_fo_simplify_projections_ops esuvdg)) esuvdg)) >> pass

esu_fo_simplify_projections_ops :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifVDGraph s t mpd pd fn v pmv fmv uv -> [ESUnifDGOp s t mpd pd fn v pmv fmv uv]
esu_fo_simplify_projections_ops esuvdg = Prelude.map (ESUFOSimpProj . dgid . fromJust) (Prelude.filter isJust ((eqdgraph (esunifdgraph esuvdg)) ^. lens_foedges))

esu_fo_simplify_proj_foe :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => Int -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) [ESUnifDGOp s t mpd pd fn v pmv fmv uv]
esu_fo_simplify_proj_foe foe = do
	{
		-- First check if the edge still exists!
		eex <- mzoom lens_esunifdgraph_dgraph (checkEqDGFOEdge foe);
		if (not eex) then (return []) else do
		{
			-- We check if indeed the head contains projections
			h <- mzoom lens_esunifdgraph_dgraph (eqDGFOEdge_head foe);
			sots <- mzoom lens_esunifdgraph_dgraph (getEquivDGSONodes h);
			let {fsots = Prelude.map from_fsonode (Prelude.filter is_fsonode sots)};
			let {mb_proj = find isproj_sot fsots; proj = fromJustErr "esu_fo_simplify_proj_foe mb_proj" mb_proj; idx = case proj of {UTerm (SOF (Proj idx)) -> idx}};
			if (isJust mb_proj) then do
			{
				ss <- mzoom lens_esunifdgraph_dgraph (eqDGFOEdge_sources foe);
				t <- mzoom lens_esunifdgraph_dgraph (eqDGFOEdge_target foe);
				-- Note that we do not flag the incompatibility here if it so happens that there are not enough inputs to the projection, we simply do nothing if that happens. This needs to be checked outside anyway.
				-- if (length ss) <= idx then (return [])) else do
				--if (length ss) <= idx then (trace ("Projection does not have enough inputs! Has: " ++ (show (length ss)) ++ ", but is looking for " ++ (show idx) ++ "th projection.") (return [])) else do
				if (length ss) <= idx then (return []) else do
				{
					--result1 <- prop_mergeEqDGFONodes (ss !! idx) t;
					result1 <- prop_mergeEqDGFONodes (errAt "esu_fo_simplify_proj_foe !!" ss idx) t;
					result2 <- (return result1) >>=++ (prop_deleteEqDGFOEdge foe);

					return result2
				}
			}
			else (return [])
		}
	}

as_esu_vertical_commute :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => RESUnifVDGraph t mpd pd fn v pmv fmv uv -> AnswerSet (RESUnifVDGraph t mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv)
as_esu_vertical_commute resuvdg = ImplicitAS (getStateTSTESUnifVDGraphState esu_vertical_commute resuvdg)

esu_vertical_commute :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) ()
esu_vertical_commute = (StateT (\esuvdg -> runStateT (runStateTOps (esu_vertical_commute_ops esuvdg)) esuvdg)) >> pass

esu_vertical_commute_ops :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifVDGraph s t mpd pd fn v pmv fmv uv -> [ESUnifDGOp s t mpd pd fn v pmv fmv uv]
esu_vertical_commute_ops esuvdg = Prelude.map ESUVCommuteFo (esunifdgraph_vfoedges esuvdg)

esu_vertical_commute_fo_edge :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifVFoEdge s t pd fn v pmv fmv uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) [ESUnifDGOp s t mpd pd fn v pmv fmv uv]
esu_vertical_commute_fo_edge e = do
	{
		let {s = esunifvfoedge_source e; t = esunifvfoedge_target e};
		sines <- mzoom lens_esunifdgraph_dgraph (st_searchAllInEqDGFOEdges [] [] s);
		soutes <- mzoom lens_esunifdgraph_dgraph (st_searchAllOutEqDGFOEdges [] [] s);
		result1 <- concat <$> (traverse (esu_vertical_commute_fo_edge_hedge e) sines);
		result2 <- (return result1) >>=++ (concat <$> (traverse (esu_vertical_commute_fo_edge_hedge e) soutes));

		return result2
	}

-- Check if a specific horizontal edge that has the source node of the vertical edge as a target/source has a corresponding one with the target of the vertical edge as a target/source, and if it does not, then create it.
-- Arguments: Vertical edge, identifier of the horizontal edge.
esu_vertical_commute_fo_edge_hedge :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifVFoEdge s t pd fn v pmv fmv uv -> Int -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) [ESUnifDGOp s t mpd pd fn v pmv fmv uv]
esu_vertical_commute_fo_edge_hedge ve he = do
	{
		-- First verify that the horizontal edge still exists in the graph!
		eex <- mzoom lens_esunifdgraph_dgraph (checkAllEqDGFOEdge he);
		if (not eex) then (return []) else do
		{
			sss <- mzoom lens_esunifdgraph_dgraph (eqDGFOEdge_sources he);
			st <- mzoom lens_esunifdgraph_dgraph (eqDGFOEdge_target he);
			tss <- sequence (Prelude.map (divideOverVFoEdge ve) sss);
			h <- mzoom lens_esunifdgraph_dgraph (eqDGFOEdge_head he);					
			tt <- divideOverVFoEdge ve st;
			ex <- mzoom lens_esunifdgraph_dgraph (st_checkAllEqDGFOEdge h tss tt);
			uv <- factorizeVFoEdge ve;
			if ex then (return [])
			else do
			{
				result <- prop_newEqDGFOEdge h tss tt;
				let {zipped = zip sss tss};
				
				result2 <- (return result) >>=++ (concat <$> traverse (\(s,t) -> prop_addVFoEdge s t uv) zipped);

				result3 <- (return result2) >>=++ (prop_addVFoEdge st tt uv);

				return result3				
			}
		}
	}

as_esu_vertical_commute_eq :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => RESUnifVDGraph t mpd pd fn v pmv fmv uv -> AnswerSet (RESUnifVDGraph t mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv)
as_esu_vertical_commute_eq resuvdg = ImplicitAS (getStateTSTESUnifVDGraphState esu_vertical_commute_eq resuvdg)

esu_vertical_commute_eq :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) ()
esu_vertical_commute_eq = (StateT (\esuvdg -> runStateT (runStateTOps (esu_vertical_commute_eq_ops esuvdg)) esuvdg)) >> pass

esu_vertical_commute_eq_ops :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifVDGraph s t mpd pd fn v pmv fmv uv -> [ESUnifDGOp s t mpd pd fn v pmv fmv uv]
esu_vertical_commute_eq_ops esuvdg = Prelude.map ESUVCommuteEqFo (esunifdgraph_vfoedges esuvdg)

esu_vertical_commute_eq_fo_edge :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifVFoEdge s t pd fn v pmv fmv uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) [ESUnifDGOp s t mpd pd fn v pmv fmv uv]
esu_vertical_commute_eq_fo_edge e = do
	{
		let {s = esunifvfoedge_source e; t = esunifvfoedge_target e};
		fots <- mzoom lens_esunifdgraph_dgraph (getEquivDGFONodes s);
		if (Prelude.null fots) then (return [])
		else do
		{
			let {(foth:fott) = fots};
			tfoth <- divideDepOverVFoEdge e foth;
			tfott <- traverse (divideDepOverVFoEdge e) fott;
			
			result <- concat <$> traverse (esu_vertical_commute_eq_fo_dep tfoth) tfott;

			return result
		}
	}

esu_vertical_commute_eq_fo_dep :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => TermDependant t fn v fmv uv -> TermDependant t fn v fmv uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) [ESUnifDGOp s t mpd pd fn v pmv fmv uv]
esu_vertical_commute_eq_fo_dep lfot rfot = do
	{
		-- Check if the two dependants are on the same node.
		let {lid = relbwEqDGFoId lfot; rid = relbwEqDGFoId rfot};
		eq <- mzoom lens_esunifdgraph_dgraph (eqSTRelativeEqDGFoIds lid rid);
		if eq then (return [])
		else do
		{
			result <- prop_mergeEqDGFONodes lid rid;

			return result
		}
	}

as_esu_vertical_align :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => RESUnifVDGraph t mpd pd fn v pmv fmv uv -> AnswerSet (RESUnifVDGraph t mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv)
as_esu_vertical_align resuvdg = ImplicitAS (getStateTSTESUnifVDGraphState esu_vertical_align resuvdg)

esu_vertical_align :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) ()
esu_vertical_align = (StateT (\esuvdg -> runStateT (runStateTOps (esu_vertical_align_ops esuvdg)) esuvdg)) >> pass

esu_vertical_align_ops :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifVDGraph s t mpd pd fn v pmv fmv uv -> [ESUnifDGOp s t mpd pd fn v pmv fmv uv]
esu_vertical_align_ops esuvdg = Prelude.map (ESUVAlign . directEqDGFoId . dgid . fromJust) (Prelude.filter isJust ((eqdgraph (esunifdgraph esuvdg)) ^. lens_fonodes))

esu_vertical_align_fot :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifRelFoId s t pd fn v pmv fmv uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) [ESUnifDGOp s t mpd pd fn v pmv fmv uv]
esu_vertical_align_fot fot = do
	{
		rtds <- mzoom lens_esunifdgraph_dgraph (getEquivDGFONodes fot);
		let {frtd = (\rtd -> if (not (is_tdunif rtd)) then (return []) else do
		{
			let {(TDUnif uv intd) = rtd; intd_id = relbwEqDGFoId intd};
			exist <- checkVFoEdge intd_id fot;
			if exist then (return [])
			else do
			{
				prop_addVFoEdge intd_id fot uv
			}
		})};
		m_concat frtd rtds
	}

as_esu_sozip :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => RESUnifVDGraph t mpd pd fn v pmv fmv uv -> AnswerSet (RESUnifVDGraph t mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv)
as_esu_sozip resuvdg = ImplicitAS (getStateTSTESUnifVDGraphState esu_sozip resuvdg)

esu_sozip :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) ()
esu_sozip = (StateT (\esuvdg -> runStateT (runStateTOps (esu_sozip_ops esuvdg)) esuvdg)) >> pass

esu_sozip_ops :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifVDGraph s t mpd pd fn v pmv fmv uv -> [ESUnifDGOp s t mpd pd fn v pmv fmv uv]
esu_sozip_ops esuvdg = Prelude.map (ESUSOZip . dgid . fromJust) (Prelude.filter isJust ((eqdgraph (esunifdgraph esuvdg)) ^. lens_soedges))

esu_sozip_soe :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => Int -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) [ESUnifDGOp s t mpd pd fn v pmv fmv uv]
esu_sozip_soe soe = do
	{
		-- First check that the edge still exists in the graph!
		eex <- mzoom lens_esunifdgraph_dgraph (checkEqDGSOEdge soe);
		if (not eex) then (return []) else do
		{
			eh <- mzoom lens_esunifdgraph_dgraph (eqDGSOEdge_head soe);
			ess <- mzoom lens_esunifdgraph_dgraph (eqDGSOEdge_sources soe);
			et <- mzoom lens_esunifdgraph_dgraph (eqDGSOEdge_target soe);
			es <- mzoom lens_esunifdgraph_dgraph (st_searchHEqDGSOEdges ess [] eh);
			let {che = (\pe -> do
			{
				pess <- eqDGSOEdge_sources pe;
				let {zipped = zip ess pess; sscs = Prelude.map (uncurry eqSTRelativeEqDGSoIds) zipped};
				Prelude.foldr (>>=&) (return (length ess == length pess)) sscs
			})};
			let {fe = (\pe -> do
			{
				ch <- che pe;
				if ch then do
				{
					pet <- eqDGSOEdge_target pe;
					-- We cannot merge here because that produces the removal of some edges, which we are traversing. We build a list of nodes to merge and merge them all in the end.
					--mergeEqDGSONodes et pet;				
					return (Just (pe,pet))
				}
				else return (Nothing)
			})};
			eres <- mzoom lens_esunifdgraph_dgraph (traverse fe es);
			let {tomerges = Prelude.map fromJust (Prelude.filter isJust eres)};			
			rsoe <- mzoom lens_esunifdgraph_dgraph (st_getCurEqDGSOEdge soe);
			let {te = (\(pe,pet) -> do
			{
				rpe <- mzoom lens_esunifdgraph_dgraph (st_getCurEqDGSOEdge pe);
				if (rsoe == rpe) then (return []) else do
				{
					sresult1 <- prop_mergeEqDGSONodes et pet;
					sresult2 <- (return sresult1) >>=++ (prop_doDeleteEqDGSOEdge rpe);

					return sresult2
				}
			})};
			result <- concat <$> traverse te tomerges;
			return result
		}
	}

as_esu_fozip :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => RESUnifVDGraph t mpd pd fn v pmv fmv uv -> AnswerSet (RESUnifVDGraph t mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv)
as_esu_fozip resuvdg = ImplicitAS (getStateTSTESUnifVDGraphState esu_fozip resuvdg)

esu_fozip :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) ()
esu_fozip = (StateT (\esuvdg -> runStateT (runStateTOps (esu_fozip_ops esuvdg)) esuvdg)) >> pass

esu_fozip_ops :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => ESUnifVDGraph s t mpd pd fn v pmv fmv uv -> [ESUnifDGOp s t mpd pd fn v pmv fmv uv]
esu_fozip_ops esuvdg = Prelude.map (ESUFOZip . dgid. fromJust) (Prelude.filter isJust ((eqdgraph (esunifdgraph esuvdg)) ^. lens_foedges))

esu_fozip_foe :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => Int -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) [ESUnifDGOp s t mpd pd fn v pmv fmv uv]
esu_fozip_foe foe = do
	{
		-- First check that the edge still exists in the graph!
		eex <- mzoom lens_esunifdgraph_dgraph (checkEqDGFOEdge foe);
		if (not eex) then (return []) else do
		{
			eh <- mzoom lens_esunifdgraph_dgraph (eqDGFOEdge_head foe);
			ess <- mzoom lens_esunifdgraph_dgraph (eqDGFOEdge_sources foe);
			et <- mzoom lens_esunifdgraph_dgraph (eqDGFOEdge_target foe);
			-- Added later: We only zip target nodes of the same level. This is necessary because of constant functions that blur out the levels dangerously.
			--elvl <- getEqDGLevel et;
			es <- mzoom lens_esunifdgraph_dgraph (st_searchHEqDGFOEdges ess [] eh);
			let {che = (\pe -> do
			{
				pess <- mzoom lens_esunifdgraph_dgraph $ eqDGFOEdge_sources pe;
				pet <- mzoom lens_esunifdgraph_dgraph $ eqDGFOEdge_target pe;
				--pelvl <- getEqDGLevel pet;

				let {zipped = zip ess pess; sscs = Prelude.map ((mzoom lens_esunifdgraph_dgraph) . (uncurry eqSTRelativeEqDGFoIds)) zipped};
				Prelude.foldr (>>=&) (return (length ess == length pess)) sscs				
			})};
			let {fe = (\pe -> do
			{
				ch <- che pe;
				if ch then do
				{
					pet <- mzoom lens_esunifdgraph_dgraph $ eqDGFOEdge_target pe;
					-- We cannot merge here because that produces the removal of some edges, which we are traversing. We build a list of nodes to merge and merge them all in the end.
					--mergeEqDGSONodes et pet;				
					return (Just (pe,pet))
				}
				else return (Nothing)
			})};
			eres <- traverse fe es;
			let {tomerges = Prelude.map fromJust (Prelude.filter isJust eres)};
			rfoe <- mzoom lens_esunifdgraph_dgraph (st_getCurEqDGFOEdge foe);
			let {te = (\(pe,pet) -> do
			{
				rpe <- mzoom lens_esunifdgraph_dgraph (st_getCurEqDGFOEdge pe);
				if (rfoe == rpe) then (return []) else do
				{
					sresult1 <- prop_mergeEqDGFONodes et pet;
					sresult2 <- (return sresult1) >>=++ (prop_doDeleteEqDGFOEdge rpe);

					return sresult2
				}
			})};
			result <- concat <$> traverse te tomerges;
			return result
		}
	}

-- This is used to write down expressions comprising multiple edges in a dependency graph in one go.
data FOTermDependantExp t pd fn v pmv fmv uv = FOTDExp (TermDependant t fn v fmv uv) | FOEdgeExp (ESUnifDGSONode pd fn pmv fmv) [FOTermDependantExp t pd fn v pmv fmv uv]
data SOTermDependantExp pd fn pmv fmv = SOTDExp (ESUnifDGSONode pd fn pmv fmv) | SOEdgeExp (ESUnifDGSONode pd fn pmv fmv) [SOTermDependantExp pd fn pmv fmv]

instance (Show (t (SOTerm fn fmv) (UTerm (t (SOTerm fn fmv)) v)), Show uv, Show v, Show fn, Show fmv, Show pd, Show pmv) => Show (FOTermDependantExp t pd fn v pmv fmv uv) where
	show (FOTDExp td) = show td
	show (FOEdgeExp fn ss) = (show fn) ++ "(" ++ (show_as_args (Prelude.map show ss)) ++ ")"

instance (Show fn, Show pd, Show pmv, Show fmv) => Show (SOTermDependantExp pd fn pmv fmv) where
	show (SOTDExp sotd) = show sotd
	show (SOEdgeExp fn ss) = (show fn) ++ "{" ++ (show_as_args (Prelude.map show ss)) ++ "}"

separate_sot_dependant_exp :: SOTerm fn fmv -> SOTermDependantExp pd fn pmv fmv
separate_sot_dependant_exp (UTerm (SOF (CompF h []))) = SOTDExp (FSONode h)
separate_sot_dependant_exp (UTerm (SOF (CompF h ss))) = SOEdgeExp (FSONode h) (Prelude.map separate_sot_dependant_exp ss)
separate_sot_dependant_exp sot = SOTDExp (FSONode sot)

separate_soa_dependant_exp :: SOAtom pd fn pmv fmv -> SOTermDependantExp pd fn pmv fmv
separate_soa_dependant_exp (UTerm (SOP (CompF h []))) = SOTDExp (PSONode h)
separate_soa_dependant_exp (UTerm (SOP (CompF h ss))) = SOEdgeExp (PSONode h) (Prelude.map separate_sot_dependant_exp ss)
separate_soa_dependant_exp soa = SOTDExp (PSONode soa)

grab_afonode :: ESMGUConstraintsALL a t ss mpd pd fn v pmv fmv uv => AtomDependant a t ss mpd pd fn v pmv fmv uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) (ESUnifRelFoId s t pd fn v pmv fmv uv)
grab_afonode ad = do
	{
		-- Decompose the atom dependant, and normalize the first-order atom
		let {(us,a) = decompose_ad ad; na = normalize a};
		case na of
		{
			FSOAtom _ -> error "Trying to produce a graph node from a first-second-order atom. These are meant to be dealt with at a higher level.";
			NSOAtom (SOMetawrapA a) -> do
			{
				let {(p,sts) = unbuild_term a; usts = compose_td us <$> sts};
				hid <- grab_asonode p;
				stids <- traverse grab_fonode usts;
				tid <- mzoom lens_esunifdgraph_dgraph (newAnonEqDGFOEdge hid stids);

				str <- show_esuvdg;
				gtraceM False str;

				return tid
			}
		}
	}

grab_fonode :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => TermDependant t fn v fmv uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) (ESUnifRelFoId s t pd fn v pmv fmv uv)
grab_fonode td = do
	{
		gtraceM False ("GRAB FONODE: " ++ (show td));

		-- Decompose the term dependant, and normalize the first-order term
		let {(us,t) = decompose_td td; nt = normalize t};
		case nt of
		{
			-- Base case => Dependant
			SOMetawrap (UVar v) -> do
			{
				let {rtd = compose_td us nt};
				return (relbwEqDGFoId rtd)
			};
			-- Recursive case => Create edges
			SOMetawrap (UTerm t) -> do
			{
				let {(h,sts) = unbuild_term t; usts = Prelude.map ((compose_td us) . SOMetawrap) sts};
				hid <- grab_sonode h;
				stids <- traverse grab_fonode usts;
				tid <- mzoom lens_esunifdgraph_dgraph (newAnonEqDGFOEdge hid stids);

				return tid
			}
		}
	}

grab_asonode :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => SOAtom pd fn pmv fmv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) (ESUnifRelSoId s t pd fn v pmv fmv uv)
grab_asonode soa = do
	{
		let {nsoa = normalize soa};
		case nsoa of
		{
			-- Base case => Variable
			UVar v -> do
			{
				return (relbwEqDGSoId (PSONode nsoa))
			};
			-- Base case => Predicate symbol
			UTerm (SOP (ConstF pd)) -> do
			{
				return (relbwEqDGSoId (PSONode nsoa))
			};
			-- Let's flag the specific error of a projection here...
			UTerm (SOP (Proj _)) -> error "A projection in a second-order atom!!!!";
			-- Recursive case => Create edges
			UTerm (SOP (CompF p sts)) -> do
			{
				hid <- grab_asonode p;
				sids <- traverse grab_sonode sts;
				tid <- mzoom lens_esunifdgraph_dgraph (newAnonEqDGSOEdge hid sids);

				return tid
			}
		}
	}

grab_sonode :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => SOTerm fn fmv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) (ESUnifRelSoId s t pd fn v pmv fmv uv)
grab_sonode sot = do
	{
		let {nsot = normalize sot};
		case nsot of
		{
			-- Base case => Variable
			UVar v -> do
			{
				return (relbwEqDGSoId (FSONode nsot))
			};
			-- Base case => Function symbol
			UTerm (SOF (ConstF fn)) -> do
			{
				return (relbwEqDGSoId (FSONode nsot))
			};
			-- Base case => Projection
			UTerm (SOF (Proj idx)) -> do
			{
				return (relbwEqDGSoId (FSONode nsot))
			};
			-- Recursive case => Create edges
			UTerm (SOF (CompF h ss)) -> do
			{
				hid <- grab_sonode h;
				sids <- traverse grab_sonode ss;
				tid <- mzoom lens_esunifdgraph_dgraph (newAnonEqDGSOEdge hid sids);

				return tid
			}
		}
	}


-- Case matching against an expression is done on an "exists" and a "first" basis: We look for some incoming edge that matches, not that all incoming edges match, and furthermore, if multiple edges match the head, we pick an arbitrary one of them, which may not match the remainder of the expression! Therefore, using this on non-factorized graphs should be done with care.
-- Of course, matching is direct matching, it does not consider what could "potentially unify with". It needs to be exactly that.

case_foexp :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => FOTermDependantExp t pd fn v pmv fmv uv -> ESUnifRelFoId s t pd fn v pmv fmv uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) (Maybe [(FOTermDependantExp t pd fn v pmv fmv uv,ESUnifRelFoId s t pd fn v pmv fmv uv)])
case_foexp (FOTDExp td) foid = mzoom lens_esunifdgraph_dgraph (do {r <- eqSTRelativeEqDGFoIds foid (relbwEqDGFoId td); if r then (return (Just [])) else (return Nothing)})
case_foexp (FOEdgeExp (FSONode h) []) foid = mzoom lens_esunifdgraph_dgraph (do {r <- eqSTRelativeEqDGFoIds foid (relbwEqDGFoId td); if r then (return (Just [])) else (return Nothing)}) where td = TDDirect (SOMetawrap (UTerm (build_term h [])))
-- A node that simply corresponds to a predicate applied to zero arguments should never contain any dependants. We just check this.
case_foexp (FOEdgeExp (PSONode p) []) foid = mzoom lens_esunifdgraph_dgraph (do {ns <- getEquivDGFONodes foid; if (Prelude.null ns) then (return (Just [])) else (return Nothing)})
case_foexp (FOEdgeExp h ss) foid = do
	{
		ines <- mzoom lens_esunifdgraph_dgraph (st_searchInEqDGFOEdges [relbwEqDGSoId h] [] foid);		
		if (Data.List.null ines) then (return Nothing) else do
		{
			let {ine = head ines};
			ess <- mzoom lens_esunifdgraph_dgraph (eqDGFOEdge_sources ine);
			if ((length ss) /= (length ess)) then (return Nothing) else (return (Just (zip ss ess)))
		}
	}

match_foexp :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => FOTermDependantExp t pd fn v pmv fmv uv -> ESUnifRelFoId s t pd fn v pmv fmv uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) Bool
match_foexp exp foid = do
	{
		sub <- case_foexp exp foid;
		case sub of
		{
			Nothing -> return False;
			Just subs -> do
			{
				rsubs <- traverse (uncurry match_foexp) subs;
				return (all id rsubs)
			}
		}
	}

case_soexp :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => SOTermDependantExp pd fn pmv fmv -> ESUnifRelSoId s t pd fn v pmv fmv uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) (Maybe [(SOTermDependantExp pd fn pmv fmv,ESUnifRelSoId s t pd fn v pmv fmv uv)])
case_soexp (SOTDExp sot) soid = mzoom lens_esunifdgraph_dgraph (do {r <- eqSTRelativeEqDGSoIds soid (relbwEqDGSoId sot); if r then (return (Just [])) else (return Nothing)})
case_soexp (SOEdgeExp h []) soid = mzoom lens_esunifdgraph_dgraph (do {r <- eqSTRelativeEqDGSoIds soid (relbwEqDGSoId h); if r then (return (Just [])) else (return Nothing)})
case_soexp (SOEdgeExp h ss) soid = do
	{
		ines <- mzoom lens_esunifdgraph_dgraph (st_searchInEqDGSOEdges [relbwEqDGSoId h] [] soid);
		if (Data.List.null ines) then (return Nothing) else do
		{
			let {ine = head ines};
			ess <- mzoom lens_esunifdgraph_dgraph (eqDGSOEdge_sources ine);
			if ((length ss) /= (length ess)) then (return Nothing) else (return (Just (zip ss ess)))
		}
	}

match_soexp :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => SOTermDependantExp pd fn pmv fmv -> ESUnifRelSoId s t pd fn v pmv fmv uv -> StateT (ESUnifVDGraph s t mpd pd fn v pmv fmv uv) (ST s) Bool
match_soexp exp soid = do
	{
		sub <- case_soexp exp soid;
		case sub of
		{
			Nothing -> return False;
			Just subs -> do
			{
				rsubs <- traverse (uncurry match_soexp) subs;
				return (all id rsubs)
			}
		}
	}

-- External-most functions to produce the different normal forms of dependency graphs
-- The order of the operations here is not essential, since these operations produce chain effects of the others. The order might affect the performance, though.
depgraph_prenormalize :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => AnswerSet (RESUnifVDGraph t mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv) -> AnswerSet (RESUnifVDGraph t mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv)
--depgraph_prenormalize as = validate_all_consistency (as ?>>= VerticalAlign ?>>= VerticalCommuteEq ?>>= VerticalCommute ?>>= SOSimplifyProjections ?>>= SODump ?>>= SOZip ?>>= FOSimplifyProjections ?>>= FODump ?>>= FOZip)
depgraph_prenormalize as = validate_all_consistency (as ?>>= Prenormalize)

depgraph_seminormalize :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => AnswerSet (RESUnifVDGraph t mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv) -> AnswerSet (RESUnifVDGraph t mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv)
--depgraph_seminormalize as = validate_all_consistency (as ?>>= VerticalAlign ?>>= VerticalCommuteEq ?>>= VerticalCommute ?>>= SOSimplifyProjections ?>>= SODump ?>>= SOZip ?>>= FOSimplifyProjections ?>>= FODump ?>>= FOZip ?>>= ZFactorize)
depgraph_seminormalize as = validate_all_consistency (as ?>>= Prenormalize ?>>= ZFactorize)

depgraph_quasinormalize :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => AnswerSet (RESUnifVDGraph t mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv) -> AnswerSet (RESUnifVDGraph t mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv)
--depgraph_quasinormalize as = validate_all_consistency (as ?>>= VerticalAlign ?>>= VerticalCommuteEq ?>>= VerticalCommute ?>>= SOSimplifyProjections ?>>= SODump ?>>= SOZip ?>>= FOSimplifyProjections ?>>= FODump ?>>= FOZip ?>>= SFactorize)
depgraph_quasinormalize as = validate_all_consistency (as ?>>= Prenormalize ?>>= SFactorize)

depgraph_normalize :: ESMGUConstraintsUPmv t pd fn v pmv fmv uv => AnswerSet (RESUnifVDGraph t mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv) -> AnswerSet (RESUnifVDGraph t mpd pd fn v pmv fmv uv) (UnifSysSolution pd fn pmv fmv)
--depgraph_normalize as = validate_all_consistency (as ?>>= VerticalAlign ?>>= VerticalCommuteEq ?>>= VerticalCommute ?>>= SOSimplifyProjections ?>>= SODump ?>>= SOZip ?>>= FOSimplifyProjections ?>>= FODump ?>>= FOZip ?>>= MFactorize)
depgraph_normalize as = validate_all_consistency (as ?>>= Prenormalize ?>>= MFactorize)



-- NOTE THAT EVERYTHING BELOW IS UNFINISHED, UNTESTED AND DEPRECATED. WE DEAL WITH THIS IN THE RESOLUTION STEP NOW, WE ONLY KEEP IT FOR FUTURE REFERENCE.

-- Note that while we allow a composite predicate structure here (argument s, that will typically stand for LambdaCNF), we do not unify this structure in a clever way here. This shall be done as part of the resolution step that happens ABOVE this. The unification that happens at this level is dumb: Assume syntactic equality in the most literal sense, with ordering and positive/negative signs mattering, and variables only possibly being instantiated to individual predicates.
-- We do consider here the flex/flex pair case, and produce the non-determinism associated with this (and related to the signature)
--data AUnifEquation a t s mpd pd fn v pmv fmv uv = AtomUnif (AtomDependant a t s mpd pd fn v pmv fmv uv) (AtomDependant a t s mpd pd fn v pmv fmv uv)

--instance Show (AtomDependant a t s mpd pd fn v pmv fmv uv) => Show (AUnifEquation a t s mpd pd fn v pmv fmv uv) where
--	show (AtomUnif lad rad) = (show lad) ++ " = " ++ (show rad)

--type AUnifSystem a t s mpd pd fn v pmv fmv uv = [AUnifEquation a t s mpd pd fn v pmv fmv uv]
--data AFullUnifSystem a t s mpd pd fn v pmv fmv uv = AUSys {a_us_sig :: SOSignature mpd pd fn v pmv fmv, a_us_eqs :: AUnifSystem a t s mpd pd fn v pmv fmv uv}

--instance (Show (AtomDependant a t s mpd pd fn v pmv fmv uv), Show mpd, Show pd, Show fn, Show v, Show pmv, Show fmv, Show uv) => Show (AFullUnifSystem a t s mpd --pd fn v pmv fmv uv) where
--	show usys = (show (a_us_eqs usys)) ++ "\n with signature {" ++ (show (a_us_sig usys)) ++ "}"




--type ComputingParcInstAUnifSystem a t s mpd pd fn v pmv fmv uv = CompPIAUS {comppiaus_sig :: SOSignature mpd pd fn v pmv fmv, comppiaus_ausys :: AUnifSystem a t s mpd pd fn v pmv fmv uv, comppiaus_usys :: UnifSystem t mpd pd fn v pmv fmv uv, comppiaus_parcsol :: ParcAUnifSysSolution pd fn pmv fmv}

--partialinstantiate_once :: (ESMGUConstraintsUPmv t pd fn v pmv fmv uv, Unifiable s) => ComputingParcInstAUnifSystem a t s mpd pd fn v pmv fmv uv -> Computation (ComputingParcInstAUnifSystem a t s mpd pd fn v pmv fmv uv)
--partialinstantiate_once comppiaus = if (null (comppiaus_ausys comppiaus)) then return comppiaus else undefined	
--	where
--		(aeq:rausys) = comppiaus_ausys comppiaus;
--		(AtomUnif lad rad) = aeq;
--		(lus,la) = decompose_ad lad;
--		(rus,ra) = decompose_ad rad;
--		rnew = case la of -- :: Computation ([UnifEquation t fn v sov uv],ParcAUnifSysSolution pd fn pmv fmv)
--		{
--			FSOAtom (FirstSOAAtom lfsoa) -> case ra of
--				{
--					FSOAtom (FirstSOAAtom rfsoa) -> case (zipMatch lfsoa rfsoa) of
--						{
--							Nothing -> emptycomp;
--							Just a -> let {(_,fsamatch) = unbuild_term a} in (case fsamatch of
--								{
--									-- If there is a direct match here, then there is no partial instantiation or anything to do for this equation. This equation is constant and is a match.
--									Left sa -> comp ([],Data.Map.empty);
--									Right (lsa, rsa) -> undefined -- TODO: zipMatch lsa with rsa and keep going downwards.
--								})
--						};
--					NSOAtom rsoa -> undefined;
--					_ -> error "Error (2) in partialinstantiate_once"
--				};
--			NSOAtom lsoa -> undefined;
--			_ -> error "Error (1) in partialinstantiate_once"
--		}

