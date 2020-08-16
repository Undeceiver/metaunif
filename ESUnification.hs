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


-- Heuristics
esunif_search_heuristic :: Diagonalize
esunif_search_heuristic = Diagonalize False False 1 1 False


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


data UnifEquation t fn v sov uv = TermUnif (TermDependant t fn v sov uv) (TermDependant t fn v sov uv) -- Pending adding atom unification here when we are ready.

type UnifSystem t fn v sov uv = [UnifEquation t fn v sov uv]

-- THE FOLLOWING IS DEPRECATED, SHOULD BE REMOVED AT SOME POINT.
-- The solution to a single unifier is simply an instantiation set of the variables (both first and second-order) to elements in the Herbrand universe.
-- We define things individually, and use the AnswerSet monad to do things the right way. An explicit solution is a map from variables to ground terms (both first and second-order)
-- It is important to note that in a system solution, a radical difference between first and second-order variables is that second-order variables cannot have incompatible values on different unifiers. When looking at it from the Herbrand universe perspective, this has to do with standardization. Second-order variables are not standardized and therefore in each final instantiation of the equation solutions in the Herbrand universe, they have a single value, whereas (universally quantified) first-order variables can have different ones for each equation because they can and have been standardized apart. This means that first-order unification of different solutions for second-order variables on different unifiers needs to be carried, and incompatibilities may arise. This is similar to our previous notion that second-order variables are replaced "before" unification happens, except we have now traced this down to standardization and therefore we can correctly assume that the unifier applies to the second-order variables, just not independently in different equations.
data UnifSolution t fn v sov = UnifSolution {fosol :: Map v (GroundT t fn), sosol :: Map sov (GroundSOT fn)} -- Pending adding predicate variables!!!

deriving instance ESMGUConstraints t pd fn v sov => Eq (UnifSolution t fn v sov)

instance (Show fn, Show v, Show sov, Show (t fn (GroundT t fn))) => Show (UnifSolution t fn v sov) where
	show us = show_unifsolution (assocs (fosol us)) (assocs (sosol us))

show_unifsolution :: forall v t fn sov. (Show fn, Show v, Show sov, Show (t fn (GroundT t fn))) => [(v,GroundT t fn)] -> [(sov,GroundSOT fn)] -> String
show_unifsolution [] [] = "\n"
show_unifsolution [] ((sov,gsot):sots) = (show sov) ++ " -> " ++ (show gsot) ++ "\n" ++ (show_unifsolution ([] :: [(v,GroundT t fn)]) sots)
show_unifsolution ((v,gt):ts) sots = (show v) ++ " -> " ++ (show gt) ++ "\n" ++ (show_unifsolution ts sots)





-- We make the choice here to only worry about second-order variables. This simplifies quite a few things.
-- However, if we find it absolutely necessary, it shouldn't be incredibly hard to include first-order variables here.
-- TODO: Note that we will need to extend this to add predicate variables.
type UnifSysSolution fn sov = sov := GroundSOT fn

-- A system of equations is a highly implicit solution to a system of unification equations
instance Implicit (UnifSystem t fn v sov uv) (UnifSysSolution fn sov) where
	checkImplicit = undefined
	enumImplicit = undefined



type ESMGUConstraints t pd fn v sov = (Ord sov, SimpleTerm t, Eq fn, HasArity fn, HasArity sov, ChangeArity sov, Functor (t (SOTerm fn sov)), Functor (t fn), Bifunctor t, Traversable (t (GroundSOT fn)), Unifiable (t (SOTerm fn sov)), Variabilizable v, Variable v, Variabilizable sov, Variable sov, Ord v, Functor (t (GroundSOT fn)), Eq (t fn (Fix (t fn))), Show sov, Show fn, Show v, Show (t (SOTerm fn sov) (UTerm (t (SOTerm fn sov)) v)), Show (t (GroundSOT fn) (UTerm (t (GroundSOT fn)) v)), Ord fn, Ord (t (SOTerm fn sov) (UTerm (t (SOTerm fn sov)) v)))





-- A dependency graph is another implicit solution to a system of unification equations (an intermediate one)
-- instance Implicit **DEPENDENCY GRAPH** (UnifSysSolution t fn v sov uv) where

-- We work with a clear mapping between levels and unifier variables. This makes things a lot easier.
type ESMGUConstraintsU t pd fn v sov uv = (ESMGUConstraints t pd fn v sov, Show uv, Ord uv)

type ESUnifDGraph s t fn v sov uv = EqDGraph s (TermDependant t fn v sov uv) (SOTerm fn sov)
type ESUnifRelFoId s t fn v sov uv = EqDGRelFoId s (TermDependant t fn v sov uv) (SOTerm fn sov)
type ESUnifRelSoId s t fn v sov uv = EqDGRelSoId s (TermDependant t fn v sov uv) (SOTerm fn sov)
data ESUnifVFoEdge s t fn v sov uv = ESUnifVFoEdge {esunifvfoedge_source :: ESUnifRelFoId s t fn v sov uv, esunifvfoedge_target :: ESUnifRelFoId s t fn v sov uv, esunifvfoedge_level :: uv}

eqUnifVFoEdge :: ESMGUConstraintsU t pd fn v sov uv => ESUnifVFoEdge s t fn v sov uv -> ESUnifVFoEdge s t fn v sov uv -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) Bool
eqUnifVFoEdge e1 e2 = (mzoom (lens_esunifdgraph_dgraph) (eqSTRelativeEqDGFoIds s1 s2)) >>= (\v1 -> if v1 then (mzoom (lens_esunifdgraph_dgraph) (eqSTRelativeEqDGFoIds t1 t2)) else (return False)) where s1 = esunifvfoedge_source e1; t1 = esunifvfoedge_target e1; s2 = esunifvfoedge_source e2; t2 = esunifvfoedge_target e2

mshow_esunifvfoedge :: ESMGUConstraintsU t pd fn v sov uv => ESUnifVFoEdge s t fn v sov uv -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) String
mshow_esunifvfoedge e = do
	{
		let {s = esunifvfoedge_source e; t = esunifvfoedge_target e; uv = esunifvfoedge_level e};
		
		sid <- mzoom lens_esunifdgraph_dgraph (getSTRelativeEqDGFoId s);
		tid <- mzoom lens_esunifdgraph_dgraph (getSTRelativeEqDGFoId t);

		return ("[" ++ (show uv) ++ "]: " ++ (show sid) ++ " -> " ++ (show tid))
	}

-- Nothing indicates that it's at the base (no unifier) level.
getEqDGLevel :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelFoId s t fn v sov uv -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) (Maybe uv)
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
				-- We assume that all sources of all incoming horizontal edges have the same level, so we just pick an arbitrary one.
				ines <- mzoom lens_esunifdgraph_dgraph (st_searchInEqDGFOEdges [] [] n);
				case ines of
				{
					[] -> error "Trying to get the unifier level of a node with no dependants and no incoming horizontal edges!!";
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
							(s:_) -> getEqDGLevel s
						}
					}
				}
			} 
		}
	}

-- The levels are assumed ordered and correctly indexed, so that 0-indexed level contains elements with no unifier variables, 1-indexed level contains elements with only the first unifier variable, and so on.
data ESUnifVDGraph s t pd fn v sov uv = ESUnifVDGraph {esunifdgraph :: ESUnifDGraph s t fn v sov uv, esunifdgraph_vfoedges :: [ESUnifVFoEdge s t fn v sov uv], esunifdgraph_sosig :: SOSignature pd fn v sov}

lens_esunifdgraph_vfoedges :: Lens' (ESUnifVDGraph s t pd fn v sov uv) [ESUnifVFoEdge s t fn v sov uv]
lens_esunifdgraph_vfoedges f esudg = fmap (\rvfoes -> ESUnifVDGraph (esunifdgraph esudg) rvfoes (esunifdgraph_sosig esudg)) (f (esunifdgraph_vfoedges esudg))

lens_esunifdgraph_dgraph :: Lens' (ESUnifVDGraph s t pd fn v sov uv) (ESUnifDGraph s t fn v sov uv)
lens_esunifdgraph_dgraph f esudg = fmap (\rdgraph -> ESUnifVDGraph rdgraph (esunifdgraph_vfoedges esudg) (esunifdgraph_sosig esudg)) (f (esunifdgraph esudg))

lens_esunifdgraph_sosig :: Lens' (ESUnifVDGraph s t pd fn v sov uv) (SOSignature pd fn v sov)
lens_esunifdgraph_sosig f esudg = fmap (\rsosig -> ESUnifVDGraph (esunifdgraph esudg) (esunifdgraph_vfoedges esudg) rsosig) (f (esunifdgraph_sosig esudg))

emptyVDGraph :: SOSignature pd fn v sov -> ESUnifVDGraph s t pd fn v sov uv
emptyVDGraph sosig = ESUnifVDGraph emptyEqDG [] sosig

show_esuvdg :: (ESMGUConstraintsU t pd fn v sov uv) => StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) String
show_esuvdg = do
	{
		esuvdg <- get;
		let {dgraph = show_eqdgraph (esunifdgraph esuvdg)};
		vedges <- show_esuvdg_vedges;
		return ("Horizontal:\n\n" ++ dgraph ++ "\n\nVertical:\n\n" ++ vedges ++ "\n\n")
	}

show_esuvdg_vedges :: (ESMGUConstraintsU t pd fn v sov uv) => StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) String
show_esuvdg_vedges = StateT (\vdg -> ((_2) ..~ (\dg -> ESUnifVDGraph dg (esunifdgraph_vfoedges vdg) (esunifdgraph_sosig vdg))) <$> (f_show_esuvdg_vedges (esunifdgraph vdg) (esunifdgraph_vfoedges vdg)))

f_show_esuvdg_vedges :: (ESMGUConstraintsU t pd fn v sov uv) => ESUnifDGraph s t fn v sov uv -> [ESUnifVFoEdge s t fn v sov uv] -> ST s (String,ESUnifDGraph s t fn v sov uv)
f_show_esuvdg_vedges dg [] = return ("",dg)
f_show_esuvdg_vedges dg (e:es) = do {(estr,dg2) <- f_show_esuvdg_vedge dg e; (esstr,dg3) <- f_show_esuvdg_vedges dg2 es; return (estr ++ "\n" ++ esstr,dg3)}

f_show_esuvdg_vedge :: (ESMGUConstraintsU t pd fn v sov uv) => ESUnifDGraph s t fn v sov uv -> ESUnifVFoEdge s t fn v sov uv -> ST s (String,ESUnifDGraph s t fn v sov uv)
f_show_esuvdg_vedge dg e = do {let {s = esunifvfoedge_source e; t = esunifvfoedge_target e}; (mb_sfot,dg2) <- runStateT (getSTRelativeEqDGFoCoId s) dg; (mb_tfot,dg3) <- runStateT (getSTRelativeEqDGFoCoId t) dg2; let {sstr = if (isNothing mb_sfot) then "()" else (show (fromJust mb_sfot)); tstr = if (isNothing mb_tfot) then "()" else (show (fromJust mb_tfot))}; return (sstr ++ " -> " ++ tstr,dg3)}

-- Dealing with vertical edges
-- The edge is added anyway. If it already existed, this is a mistake, but it should be dealt with at a higher level.
-- Note that we ensure that the nodes exist in the graph when doing this.
addVFoEdge :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelFoId s t fn v sov uv -> ESUnifRelFoId s t fn v sov uv -> uv -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) (ESUnifVFoEdge s t fn v sov uv)
addVFoEdge s t uv = mzoom lens_esunifdgraph_dgraph (do {mb_sfot <- getSTRelativeEqDGFoCoId s; mb_tfot <- getSTRelativeEqDGFoCoId t; if (isJust mb_sfot) then (newEqDGFONode (fromJustErr "addVFoEdge sfot" mb_sfot)) else pass; if (isJust mb_tfot) then (newEqDGFONode (fromJustErr "addVFoEdge tfot" mb_tfot)) else pass}) >> (StateT (f_addVFoEdge s t uv))

f_addVFoEdge :: ESUnifRelFoId s t fn v sov uv -> ESUnifRelFoId s t fn v sov uv -> uv -> (ESUnifVDGraph s t pd fn v sov uv -> ST s (ESUnifVFoEdge s t fn v sov uv, ESUnifVDGraph s t pd fn v sov uv))
f_addVFoEdge s t uv esuvdg = return (ve, lens_esunifdgraph_vfoedges ..~ (ve:) $ esuvdg) where ve = ESUnifVFoEdge s t uv

-- When we delete, we delete all copies of that edge. There should only really be one, but you can never be safe enough.
deleteVFoEdge :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelFoId s t fn v sov uv -> ESUnifRelFoId s t fn v sov uv -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) ()
deleteVFoEdge s t = StateT (f_deleteVFoEdge s t)

f_deleteVFoEdge :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelFoId s t fn v sov uv -> ESUnifRelFoId s t fn v sov uv -> (ESUnifVDGraph s t pd fn v sov uv -> ST s ((),ESUnifVDGraph s t pd fn v sov uv))
f_deleteVFoEdge s t esudg = tocombine <$> (runStateT st_res esudg) where fe = ESUnifVFoEdge s t (error "The unifier variable should be irrelevant when deleting a vertical edge"); es = esunifdgraph_vfoedges esudg; tofold = (\e -> \rstes -> rstes >>= (\res -> (\rb -> if rb then res else (e:res)) <$> (eqUnifVFoEdge e fe))); st_res = Prelude.foldr tofold (return []) es; tocombine = (\(rres,resudg) -> ((),lens_esunifdgraph_vfoedges .~ rres $ resudg))


-- Check if a vertical edge exists.
checkVFoEdge :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelFoId s t fn v sov uv -> ESUnifRelFoId s t fn v sov uv -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) Bool
checkVFoEdge s t = StateT (f_checkVFoEdge s t)

f_checkVFoEdge :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelFoId s t fn v sov uv -> ESUnifRelFoId s t fn v sov uv -> (ESUnifVDGraph s t pd fn v sov uv -> ST s (Bool,ESUnifVDGraph s t pd fn v sov uv))
f_checkVFoEdge s t esudg = runStateT st_rb esudg where fe = ESUnifVFoEdge s t (error "The unifier variable should be irrelevant when checking a vertical edge"); es = esunifdgraph_vfoedges esudg; tofold = (\e -> \rstb -> rstb >>= (\rb -> if rb then (return True) else (eqUnifVFoEdge e fe))); st_rb = Prelude.foldr tofold (return False) es

outVFoEdges :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelFoId s t fn v sov uv -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) [ESUnifVFoEdge s t fn v sov uv]
outVFoEdges s = StateT (f_outVFoEdges s)

f_outVFoEdges :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelFoId s t fn v sov uv -> (ESUnifVDGraph s t pd fn v sov uv -> ST s ([ESUnifVFoEdge s t fn v sov uv],ESUnifVDGraph s t pd fn v sov uv))
f_outVFoEdges s esudg = runStateT (monadfilter tofilter es) esudg where es = esunifdgraph_vfoedges esudg; tofilter = (\e -> mzoom lens_esunifdgraph_dgraph (eqSTRelativeEqDGFoIds (esunifvfoedge_source e) s))

singleOutVFoEdge :: ESMGUConstraintsU t pd fn v sov uv => uv -> ESUnifRelFoId s t fn v sov uv -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) (ESUnifVFoEdge s t fn v sov uv)
singleOutVFoEdge uv s = do
	{
		esudg <- get;
		let {es = esunifdgraph_vfoedges esudg};
		let {tofilter = (\e -> (mzoom lens_esunifdgraph_dgraph (eqSTRelativeEqDGFoIds (esunifvfoedge_source e) s)) >>=& (return ((esunifvfoedge_level e) == uv)))};

		ves <- monadfilter tofilter es;
		
		-- If there is more than one edge, something is wrong
		if ((length ves) > 1) then (error "More than one outgoing vertical edge with the same unifier level found!") else
		if (Prelude.null ves) then do
		{
			-- It is empty: Create it.
			t <- mzoom lens_esunifdgraph_dgraph newAnonEqDGFONode;
			ve <- addVFoEdge s t uv;

			return ve
		}
		else (return (head ves))		
	}

inVFoEdges :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelFoId s t fn v sov uv -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) [ESUnifVFoEdge s t fn v sov uv]
inVFoEdges t = StateT (f_inVFoEdges t)

f_inVFoEdges :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelFoId s t fn v sov uv -> (ESUnifVDGraph s t pd fn v sov uv -> ST s ([ESUnifVFoEdge s t fn v sov uv],ESUnifVDGraph s t pd fn v sov uv))
f_inVFoEdges t esudg = runStateT (monadfilter tofilter es) esudg where es = esunifdgraph_vfoedges esudg; tofilter = (\e -> mzoom lens_esunifdgraph_dgraph (eqSTRelativeEqDGFoIds (esunifvfoedge_target e) t))


-- We assume and ensure that a vertical edge is always between two dependants only one unifier variable in difference
factorizeVFoEdge :: ESMGUConstraintsU t pd fn v sov uv => ESUnifVFoEdge s t fn v sov uv -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) uv
factorizeVFoEdge e = do
	{
		let {t = esunifvfoedge_target e};
		mb_uv <- getEqDGLevel t;

		let {uv = fromJustErr "Found a vertical edge whose target is at the base level!" mb_uv};
		return uv;
	}

divideOverVFoEdge :: ESMGUConstraintsU t pd fn v sov uv => ESUnifVFoEdge s t fn v sov uv -> ESUnifRelFoId s t fn v sov uv -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) (ESUnifRelFoId s t fn v sov uv)
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

divideDepOverVFoEdge :: ESMGUConstraintsU t pd fn v sov uv => ESUnifVFoEdge s t fn v sov uv -> TermDependant t fn v sov uv -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) (TermDependant t fn v sov uv)
divideDepOverVFoEdge e fot = do {uv <- factorizeVFoEdge e; return (TDUnif uv fot)}

-- Operation types for unification dependency graphs
-- We have two levels of operations.
-- The low level ones work directly on the graph itself and are for propagating changes until everything that needs to be done is done, in a relatively efficient manner. These are formalized with the Operable types.
-- The high level ones work on a graph with a normalization level and are for expressing things that we do when working with a dependency graph representation of a unification system. These are not formalized with the Operable types, and simply are a set of functions that can be used to navigate these normal types in different ways.

data ESUnifDGOp (s :: *) (t :: * -> * -> *) (pd :: *) (fn :: *) (v :: *) (sov :: *) (uv :: *) = ESUVCommuteEqFo (ESUnifVFoEdge s t fn v sov uv) | ESUVCommuteFo (ESUnifVFoEdge s t fn v sov uv) | ESUVAlign (ESUnifRelFoId s t fn v sov uv) | ESUSOZip Int | ESUFOZip Int | ESUFOSimpProj Int | ESUSOSimpProj Int | ESUFODump Int | ESUSODump Int

instance Eq (ESUnifDGOp s t pd fn v sov uv) where
	op1 == op2 = esunifdg_prio op1 == esunifdg_prio op2

instance Ord (ESUnifDGOp s t pd fn v sov uv) where
	op1 <= op2 | esunifdg_prio op1 < esunifdg_prio op2 = True
	op1 <= op2 | esunifdg_prio op2 < esunifdg_prio op1 = False
	-- Default case for operations with no further comparisons.
	op1 <= op2 = True

esunifdg_prio :: (ESUnifDGOp s t pd fn v sov uv) -> Int
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
instance ESMGUConstraintsU t pd fn v sov uv => StateTOperation (ST s) (ESUnifDGOp s t pd fn v sov uv) (ESUnifVDGraph s t pd fn v sov uv) where
	runStateTOp (ESUVCommuteEqFo foe) = do {foestr <- mshow_esunifvfoedge foe; gtraceM True ("VCommuteEq: " ++ foestr); esu_vertical_commute_eq_fo_edge foe}
	runStateTOp (ESUVCommuteFo foe) = do {foestr <- mshow_esunifvfoedge foe; gtraceM True ("VCommute: " ++ foestr); esu_vertical_commute_fo_edge foe}
	runStateTOp (ESUVAlign fot) = do {foid <- mzoom lens_esunifdgraph_dgraph (getSTRelativeEqDGFoId fot); gtraceM True ("ESUVAlign: " ++ (show foid)); esu_vertical_align_fot fot}
	runStateTOp (ESUSOZip soe) = gtrace True ("SOZip: " ++ (show soe)) (esu_sozip_soe soe)
	runStateTOp (ESUFOZip foe) = gtrace True ("FOZip: " ++ (show foe)) (esu_fozip_foe foe)
	runStateTOp (ESUSOSimpProj soe) = gtrace True ("ESUSOSimpProj: " ++ (show soe)) (esu_so_simplify_proj_soe soe)
	runStateTOp (ESUFOSimpProj foe) = gtrace True ("ESUFOSimpProj: " ++ (show foe)) (esu_fo_simplify_proj_foe foe)
	runStateTOp (ESUSODump soe) = gtrace True ("ESUSODump: " ++ (show soe)) (esu_so_dump_soe soe)
	runStateTOp (ESUFODump foe) = gtrace True ("ESUFODump: " ++ (show foe)) (esu_fo_dump_foe foe)

newtype RESUnifVDGraph t pd fn v sov uv = RESUnifVDGraph {fromRESUnifVDGraph :: forall s. ST s (ESUnifVDGraph s t pd fn v sov uv)}

-- NOTE THAT THIS STATET IGNORES ANY PREVIOUS STATE!!!
unRESUnifVDGraph :: ESMGUConstraintsU t pd fn v sov uv => RESUnifVDGraph t pd fn v sov uv -> (forall s. StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) ())
unRESUnifVDGraph resuvdg = StateT (\_ -> do {esuvdg <- (fromRESUnifVDGraph resuvdg); return ((),esuvdg)})

doRESUnifVDGraph :: ESMGUConstraintsU t pd fn v sov uv => (forall s. StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) a) -> RESUnifVDGraph t pd fn v sov uv
doRESUnifVDGraph st = RESUnifVDGraph (snd <$> (runStateT st (emptyVDGraph sig))) where sig = runST (fst <$> (runStateT (do {st; esuvdg <- get; return (esunifdgraph_sosig esuvdg)}) (emptyVDGraph undefined)))

instance ESMGUConstraintsU t pd fn v sov uv => Show (RESUnifVDGraph t pd fn v sov uv) where
	show resuvdg = runST (do
		{
			esuvdg <- fromRESUnifVDGraph resuvdg;
			fst <$> runStateT show_esuvdg esuvdg
		})

instance ESMGUConstraintsU t pd fn v sov uv => Implicit (RESUnifVDGraph t pd fn v sov uv) (UnifSysSolution fn sov) where
	checkImplicit resuvdg us = comp (check_unifsolution resuvdg us)
	enumImplicit resuvdg = enumAS (bimap_as EnRESUnifVDGraph id ((depgraph_normalize (ImplicitAS resuvdg)) ?>>= EnumRootSOV))

-- Simply a wrapper indicating that it has already been enumerated. This is to implement the implicit instance recursively.
newtype EnRESUnifVDGraph t pd fn v sov uv = EnRESUnifVDGraph {fromEnRESUnifVDGraph :: RESUnifVDGraph t pd fn v sov uv}

instance ESMGUConstraintsU t pd fn v sov uv => Implicit (EnRESUnifVDGraph t pd fn v sov uv) (UnifSysSolution fn sov) where
	checkImplicit (EnRESUnifVDGraph resuvdg) us = error "The checkImplicit implementation for the enumerated unification dependency graph should not be used!"
	-- enumImplicit assumes full normalization and enumeration of root second-order variables
	enumImplicit (EnRESUnifVDGraph resuvdg) = return (extract_unifsolution resuvdg)

check_unifsolution :: ESMGUConstraintsU t pd fn v sov uv => RESUnifVDGraph t pd fn v sov uv -> UnifSysSolution fn sov -> Bool
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

check_unifsolution_esuvdg :: ESMGUConstraintsU t pd fn v sov uv => UnifSysSolution fn sov -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) ()
check_unifsolution_esuvdg usol = do
	{
		let {fsov = (\(sov,vsov) -> so_unify_depgraph (UVar sov) (inject_groundsot vsov))};
		traverse fsov (assocs usol);
		pass;
	}

-- This function should ONLY be applied on a graph that not only is normalized, but also has had all root second-order variables enumerated. Otherwise, results may be impredictable!
extract_unifsolution :: ESMGUConstraintsU t pd fn v sov uv => RESUnifVDGraph t pd fn v sov uv -> UnifSysSolution fn sov
extract_unifsolution resuvdg = runST (do
	{
		esuvdg <- fromRESUnifVDGraph resuvdg;
		let {sovars = esuvdg ^. (lens_esunifdgraph_sosig . lens_sovars)};
		-- We make MANY assumptions here, and throw some errors if we find that any are not met (but we do not do exhaustive checks for them, though).
		-- First, we assume that each second-order variable is either equivalent to a constant second-order function or has incoming second-order edges. This should be ensured through the enumeration of root second-order variables that we carried so far.
		-- Second, we assume that if both it is equivalent to a constant AND has an incoming edge, then those two things are totally compatible and equivalent. We will then focus only on the equivalence.
		-- Third, we assume that all equivalent constant functions and all second-order edges are fully compatible and equivalent between them. Again, this should be enough through everything that has happened before.
		
		let {fsovar = (\sov -> do
		{
			let {nodeid = relbwEqDGSoId (UVar sov)};
			vsov <- extract_sov_value nodeid;
			return (sov,vsov)
		})};
		sovpairs <- (list_from_enum . fst) <$> runStateT (traverse fsovar sovars) esuvdg;
		return (Data.Map.Strict.fromList sovpairs)
	})

extract_sov_value :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelSoId s t fn v sov uv -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) (GroundSOT fn)
extract_sov_value nodeid = do
	{
		eqns <- mzoom lens_esunifdgraph_dgraph (getEquivDGSONodes nodeid);
		let {nveqns = Prelude.filter (not . isvar_sot) eqns};
		if (Prelude.null nveqns) then do
		{
			ines <- mzoom lens_esunifdgraph_dgraph (st_searchInEqDGSOEdges [] [] nodeid);
			if ((length ines) /= 1) then (error ("Trying to extract second-order variable from a node with " ++ (show (length ines)) ++ " incoming edges (and no equivalent constant).")) else do
			{
				let {ine = head ines};
				ss <- mzoom lens_esunifdgraph_dgraph (eqDGSOEdge_sources ine);
				h <- mzoom lens_esunifdgraph_dgraph (eqDGSOEdge_head ine);
				vss <- traverse extract_sov_value ss;
				vh <- extract_sov_value h;
				return (Fix (SOF (CompF vh vss)))
			}
		}
		else (return (to_groundsot (head nveqns)))
	}

-- Again, recursion through operations.
enumerate_all_root_sovs :: ESMGUConstraintsU t pd fn v sov uv => RESUnifVDGraph t pd fn v sov uv -> AnswerSet (RESUnifVDGraph t pd fn v sov uv) (UnifSysSolution fn sov)
enumerate_all_root_sovs resuvdg = enumerate_all_root_sovs_choice (do
	{
		esuvdg <- fromRESUnifVDGraph resuvdg;
		enumerate_all_root_sovs_esuvdg esuvdg
	})

enumerate_all_root_sovs_choice :: ESMGUConstraintsU t pd fn v sov uv => (forall s. ST s (Bool,AnswerSet (ESUnifVDGraph s t pd fn v sov uv) (UnifSysSolution fn sov))) -> AnswerSet (RESUnifVDGraph t pd fn v sov uv) (UnifSysSolution fn sov)
enumerate_all_root_sovs_choice stas = if (runST (fst <$> stas)) then (st_as_commute_esuvdg (((bimap_as return id) . snd) <$> stas) ?>>= EnumRootSOV) else (st_as_commute_esuvdg (((bimap_as return id) . snd) <$> stas))

enumerate_all_root_sovs_esuvdg :: ESMGUConstraintsU t pd fn v sov uv => ESUnifVDGraph s t pd fn v sov uv -> ST s (Bool,AnswerSet (ESUnifVDGraph s t pd fn v sov uv) (UnifSysSolution fn sov))
enumerate_all_root_sovs_esuvdg esuvdg = do
	{
		(mb_sov,esuvdg2) <- runStateT find_root_sov esuvdg;
		case mb_sov of
		{
			Nothing -> return (False,ImplicitAS esuvdg2);
			Just sov -> do
			{
				let {ffunc = (\fn -> snd <$> runStateT (factorize_in_flexrigid sov (inject_groundsot fn)) esuvdg2)};
				enflexrigids <- sequence (ffunc <$> enum_constfofuncs (arity sov) (esunifdgraph_sosig esuvdg2));
				return (True,ExplicitAS (ImplicitAS <$> enflexrigids))
			}
		}
	}

-- To produce the final enumeration, we need functions that take a normalized dependency graph, enumerate root second-order variables and collect the dependent values.
find_root_sov :: ESMGUConstraintsU t pd fn v sov uv => StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) (Maybe sov)
find_root_sov = do
	{
		esuvdg <- get;
		let {sovars = esuvdg ^. (lens_esunifdgraph_sosig . lens_sovars)};
		let {filt = (\sov -> do
			{
				let {nodeid = relbwEqDGSoId (UVar sov)};
				eqns <- mzoom lens_esunifdgraph_dgraph (getEquivDGSONodes nodeid);				
				ines <- mzoom lens_esunifdgraph_dgraph (st_searchInEqDGSOEdges [] [] nodeid);
				return ((all isvar_sot eqns) && (Prelude.null ines))
			})};
		fsovars <- m_efilter filt sovars;
		if (Prelude.null fsovars) then (return Nothing) else (return (Just (uns_produce_next fsovars)))
	}

-- This instance is NEVER to be used. It is only a structural thing that we need to transform into the instance above, because of the impredicative b***s**t.
instance Implicit (ESUnifVDGraph s t pd fn v sov uv) (UnifSysSolution fn sov) where
	checkImplicit = error "The implicit ESUnifVDGraph instance should never be used!!"
	enumImplicit = error "The implicit ESUnifVDGraph instance should never be used!!"

instance Implicit (ST s (ESUnifVDGraph s t pd fn v sov uv)) (UnifSysSolution fn sov) where
	checkImplicit = error "The implicit ESUnifVDGraph instance should never be used!!"
	enumImplicit = error "The implicit ESUnifVDGraph instance should never be used!!"


data ESUnifGlobalOp = SOTConsistency | FOTConsistency | HeadAritySO | HeadArityFO | OccursCheckSO | OccursCheckFO | FODump | SODump | SOSimplifyProjections | FOSimplifyProjections | VerticalCommuteEq | VerticalCommute | VerticalAlign | FOZip | SOZip | Prenormalize | ZFactorize | SFactorize | MFactorize | EnumRootSOV deriving (Show,Eq,Ord)

instance Functional ESUnifGlobalOp (UnifSysSolution fn sov) (AnswerSet (RESUnifVDGraph t pd fn v sov uv) (UnifSysSolution fn sov)) where
	-- Not sure if this will remain correct, but I think it should.
	-- In principle, all global DG operations leave the set of solutions of the dependency graph unchanged. If that set happens to be a single solution, that is also the case.
	tofun _ us = SingleAS us

instance ESMGUConstraintsU t pd fn v sov uv => ImplicitF (RESUnifVDGraph t pd fn v sov uv) (UnifSysSolution fn sov) (RESUnifVDGraph t pd fn v sov uv) (UnifSysSolution fn sov) ESUnifGlobalOp where
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
prop_newEqDGFOEdge :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelSoId s t fn v sov uv -> [ESUnifRelFoId s t fn v sov uv] -> ESUnifRelFoId s t fn v sov uv -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) [ESUnifDGOp s t pd fn v sov uv]
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

prop_newEqDGSOEdge :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelSoId s t fn v sov uv -> [ESUnifRelSoId s t fn v sov uv] -> ESUnifRelSoId s t fn v sov uv -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) [ESUnifDGOp s t pd fn v sov uv]
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

prop_addVFoEdge :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelFoId s t fn v sov uv -> ESUnifRelFoId s t fn v sov uv -> uv -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) [ESUnifDGOp s t pd fn v sov uv]
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

prop_mergeEqDGFONodes :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelFoId s t fn v sov uv -> ESUnifRelFoId s t fn v sov uv -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) [ESUnifDGOp s t pd fn v sov uv]
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

prop_mergeEqDGSONodes :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelSoId s t fn v sov uv -> ESUnifRelSoId s t fn v sov uv -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) [ESUnifDGOp s t pd fn v sov uv]
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

prop_deleteEqDGSOEdge :: ESMGUConstraintsU t pd fn v sov uv => Int -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) [ESUnifDGOp s t pd fn v sov uv]
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

prop_doDeleteEqDGSOEdge :: ESMGUConstraintsU t pd fn v sov uv => Int -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) [ESUnifDGOp s t pd fn v sov uv]
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


prop_deleteEqDGFOEdge :: ESMGUConstraintsU t pd fn v sov uv => Int -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) [ESUnifDGOp s t pd fn v sov uv]
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

prop_doDeleteEqDGFOEdge :: ESMGUConstraintsU t pd fn v sov uv => Int -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) [ESUnifDGOp s t pd fn v sov uv]
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


prop_newAnonEqDGFOEdge :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelSoId s t fn v sov uv -> [ESUnifRelFoId s t fn v sov uv] -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) (ESUnifRelFoId s t fn v sov uv,[ESUnifDGOp s t pd fn v sov uv])
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

prop_newAnonEqDGSOEdge :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelSoId s t fn v sov uv -> [ESUnifRelSoId s t fn v sov uv] -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) (ESUnifRelSoId s t fn v sov uv,[ESUnifDGOp s t pd fn v sov uv])
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

justprop_deleteEqDGFOEdge :: ESMGUConstraintsU t pd fn v sov uv => Int -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) [ESUnifDGOp s t pd fn v sov uv]
justprop_deleteEqDGFOEdge foe = return []

justprop_doDeleteEqDGFOEdge :: ESMGUConstraintsU t pd fn v sov uv => Int -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) [ESUnifDGOp s t pd fn v sov uv]
justprop_doDeleteEqDGFOEdge foe = return []

justprop_deleteEqDGSOEdge :: ESMGUConstraintsU t pd fn v sov uv => Int -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) [ESUnifDGOp s t pd fn v sov uv]
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

justprop_doDeleteEqDGSOEdge :: ESMGUConstraintsU t pd fn v sov uv => Int -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) [ESUnifDGOp s t pd fn v sov uv]
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


justprop_mergeEqDGSONodes :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelSoId s t fn v sov uv -> ESUnifRelSoId s t fn v sov uv -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) [ESUnifDGOp s t pd fn v sov uv]
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

justprop_mergeEqDGFONodes :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelFoId s t fn v sov uv -> ESUnifRelFoId s t fn v sov uv -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) [ESUnifDGOp s t pd fn v sov uv]
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

justprop_addVFoEdge :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelFoId s t fn v sov uv -> ESUnifRelFoId s t fn v sov uv -> uv -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) [ESUnifDGOp s t pd fn v sov uv]
justprop_addVFoEdge s t uv = return [ESUVCommuteFo (ESUnifVFoEdge s t uv), ESUVCommuteEqFo (ESUnifVFoEdge s t uv)]

justprop_newEqDGFONode :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelFoId s t fn v sov uv -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) [ESUnifDGOp s t pd fn v sov uv]
justprop_newEqDGFONode foid = return [ESUVAlign foid]

justprop_newEqDGSONode :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelSoId s t fn v sov uv -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) [ESUnifDGOp s t pd fn v sov uv]
justprop_newEqDGSONode soid = return []

justprop_newEqDGFOEdge :: ESMGUConstraintsU t pd fn v sov uv => Int -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) [ESUnifDGOp s t pd fn v sov uv]
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

justprop_newEqDGSOEdge :: ESMGUConstraintsU t pd fn v sov uv => Int -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) [ESUnifDGOp s t pd fn v sov uv]
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

getStateTSTESUnifVDGraph :: (forall s. StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) a) -> RESUnifVDGraph t pd fn v sov uv -> a
getStateTSTESUnifVDGraph st resuvdg = runST (do {esuvdg <- fromRESUnifVDGraph resuvdg; fst <$> runStateT st esuvdg})

getStateTSTESUnifVDGraphState :: (forall s. StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) a) -> RESUnifVDGraph t pd fn v sov uv -> RESUnifVDGraph t pd fn v sov uv
getStateTSTESUnifVDGraphState st resuvdg = RESUnifVDGraph (do {esuvdg <- fromRESUnifVDGraph resuvdg; snd <$> runStateT st esuvdg})

-- ZeroFactorize means all heads are constants.
-- HalfFactorizeF means there is a constant function that has incoming horizontal edges.
-- HalfFactorizeP means there is a projection that has incoming horizontal edges.
-- SingleFactorize means there are constant heads, but also variable heads. We choose a variable and factorize that one using the constant heads.
-- MultiFactorize means all heads are variables. We choose one variable and enumerate potential heads for it (including projection).
data FactorizeCandidateS s t fn v sov uv = NoFactorize | ZeroFactorizeFO (ESUnifRelFoId s t fn v sov uv) | ZeroFactorizeSO (ESUnifRelSoId s t fn v sov uv) | HalfFactorizeF (ESUnifRelSoId s t fn v sov uv) | HalfFactorizeP Int | SingleFactorizeFO (ESUnifRelFoId s t fn v sov uv) sov | SingleFactorizeSO (ESUnifRelSoId s t fn v sov uv) sov | MultiFactorize sov Int
newtype FactorizeCandidate t fn v sov uv = FC {fromFC :: forall s. ST s (FactorizeCandidateS s t fn v sov uv)} -- deriving (Ord,Eq)
data FactorizeType = NoFactorizeT | ZeroFactorizeT | HalfFactorizeT | SingleFactorizeT | MultiFactorizeT deriving Show

-- The Eq and Ord instances of FactorizeCandidate refer to their relative priority in solving. So there may be "equal" factorize candidates that are not actually equal in what they mean! They just have equal priority.
instance Eq (FactorizeCandidateS s t fn v sov uv) where	
	(ZeroFactorizeFO _) == (ZeroFactorizeFO _) = True
	(ZeroFactorizeSO _) == (ZeroFactorizeSO _) = True
	(HalfFactorizeF _) == (HalfFactorizeF _) = True
	(HalfFactorizeP _) == (HalfFactorizeP _) = True
	(SingleFactorizeFO _ _) == (SingleFactorizeFO _ _) = True
	(SingleFactorizeSO _ _) == (SingleFactorizeSO _ _) = True
	(MultiFactorize _ x) == (MultiFactorize _ y) = x == y
	NoFactorize == NoFactorize = True
	_ == _ = False

instance Eq (FactorizeCandidate t fn v sov uv) where
	fc1 == fc2 = runST (do {vfc1 <- fromFC fc1; vfc2 <- fromFC fc2; return (vfc1 == vfc2)})

instance Ord (FactorizeCandidateS s t fn v sov uv) where
	(ZeroFactorizeFO _) <= (ZeroFactorizeFO _) = True
	(ZeroFactorizeFO _) <= (ZeroFactorizeSO _) = True
	(ZeroFactorizeFO _) <= (HalfFactorizeF _) = True
	(ZeroFactorizeFO _) <= (HalfFactorizeP _) = True
	(ZeroFactorizeFO _) <= (SingleFactorizeFO _ _) = True
	(ZeroFactorizeFO _) <= (SingleFactorizeSO _ _) = True
	(ZeroFactorizeFO _) <= (MultiFactorize _ _) = True
	(ZeroFactorizeFO _) <= NoFactorize = True
	(ZeroFactorizeSO _) <= (ZeroFactorizeSO _) = True
	(ZeroFactorizeSO _) <= (HalfFactorizeF _) = True
	(ZeroFactorizeSO _) <= (HalfFactorizeP _) = True
	(ZeroFactorizeSO _) <= (SingleFactorizeFO _ _) = True
	(ZeroFactorizeSO _) <= (SingleFactorizeSO _ _) = True
	(ZeroFactorizeSO _) <= (MultiFactorize _ _) = True
	(ZeroFactorizeSO _) <= NoFactorize = True
	(HalfFactorizeF _) <= (HalfFactorizeF _) = True
	(HalfFactorizeF _) <= (HalfFactorizeP _) = True
	(HalfFactorizeF _) <= (SingleFactorizeFO _ _) = True
	(HalfFactorizeF _) <= (SingleFactorizeSO _ _) = True
	(HalfFactorizeF _) <= (MultiFactorize _ _) = True
	(HalfFactorizeF _) <= NoFactorize = True
	(HalfFactorizeP _) <= (HalfFactorizeP _) = True
	(HalfFactorizeP _) <= (SingleFactorizeFO _ _) = True
	(HalfFactorizeP _) <= (SingleFactorizeSO _ _) = True
	(HalfFactorizeP _) <= (MultiFactorize _ _) = True
	(HalfFactorizeP _) <= NoFactorize = True	
	(SingleFactorizeFO _ _) <= (SingleFactorizeFO _ _) = True
	(SingleFactorizeFO _ _) <= (SingleFactorizeSO _ _) = True
	(SingleFactorizeFO _ _) <= (MultiFactorize _ _) = True
	(SingleFactorizeFO _ _) <= NoFactorize = True
	(SingleFactorizeSO _ _) <= (SingleFactorizeSO _ _) = True
	(SingleFactorizeSO _ _) <= (MultiFactorize _ _) = True
	(SingleFactorizeSO _ _) <= NoFactorize = True
	(MultiFactorize _ x) <= (MultiFactorize _ y) = x <= y
	(MultiFactorize _ _) <= NoFactorize = True
	NoFactorize <= NoFactorize = True
	_ <= _ = False

instance Ord (FactorizeCandidate t fn v sov uv) where
	fc1 <= fc2 = runST (do {vfc1 <- fromFC fc1; vfc2 <- fromFC fc2; return (vfc1 <= vfc2)})

-- All of the following section is disgusting, but Haskell is at fault.
-- None of this should be necessary at all.
data STASCommuteType = SingleASCommute | ImplicitASCommute | ExplicitASCommute

forall_fmap_enum_fromcontinue :: ESMGUConstraintsU t pd fn v sov uv => (forall s. EnumProc (ST s (AnswerSet (ST s (ESUnifVDGraph s t pd fn v sov uv)) (UnifSysSolution fn sov)))) -> (forall s. EnumProc (ST s (AnswerSet (ST s (ESUnifVDGraph s t pd fn v sov uv)) (UnifSysSolution fn sov))))
forall_fmap_enum_fromcontinue (Continue x) = x

forall_fmap_enum_fromproduce :: ESMGUConstraintsU t pd fn v sov uv => (forall s. EnumProc (ST s (AnswerSet (ST s (ESUnifVDGraph s t pd fn v sov uv)) (UnifSysSolution fn sov)))) -> (forall s. EnumProc (ST s (AnswerSet (ST s (ESUnifVDGraph s t pd fn v sov uv)) (UnifSysSolution fn sov))))
forall_fmap_enum_fromproduce (Produce v x) = x

forall_fmap_enum_fromproduce_value :: ESMGUConstraintsU t pd fn v sov uv => (forall s. EnumProc (ST s (AnswerSet (ST s (ESUnifVDGraph s t pd fn v sov uv)) (UnifSysSolution fn sov)))) -> (forall s. ST s (AnswerSet (ST s (ESUnifVDGraph s t pd fn v sov uv)) (UnifSysSolution fn sov)))
forall_fmap_enum_fromproduce_value (Produce v x) = v

forall_fmap_enum_resuvdg :: ESMGUConstraintsU t pd fn v sov uv => (forall s. EnumProc (ST s (AnswerSet (ST s (ESUnifVDGraph s t pd fn v sov uv)) (UnifSysSolution fn sov)))) -> EnumProc (AnswerSet (RESUnifVDGraph t pd fn v sov uv) (UnifSysSolution fn sov))
forall_fmap_enum_resuvdg EnumProc.Empty = EnumProc.Empty
forall_fmap_enum_resuvdg Halt = Halt
forall_fmap_enum_resuvdg (Error str) = Error str
forall_fmap_enum_resuvdg x | case x of {Continue _ -> True; _ -> False} = Continue (forall_fmap_enum_resuvdg (forall_fmap_enum_fromcontinue x))
forall_fmap_enum_resuvdg x | case x of {Produce _ _ -> True; _ -> False} = Produce (st_as_commute_esuvdg (forall_fmap_enum_fromproduce_value x)) (forall_fmap_enum_resuvdg (forall_fmap_enum_fromproduce x))

st_as_commute_esuvdg_from_explicit :: ESMGUConstraintsU t pd fn v sov uv => (forall s. ST s (AnswerSet (ST s (ESUnifVDGraph s t pd fn v sov uv)) (UnifSysSolution fn sov))) -> (forall s. ST s (EnumProc (AnswerSet (ST s (ESUnifVDGraph s t pd fn v sov uv)) (UnifSysSolution fn sov))))
st_as_commute_esuvdg_from_explicit expl = do {(ExplicitAS x) <- expl; return x}

st_as_commute_esuvdg_en_commute :: ESMGUConstraintsU t pd fn v sov uv => (forall s. ST s (AnswerSet (ST s (ESUnifVDGraph s t pd fn v sov uv)) (UnifSysSolution fn sov))) -> (forall s. EnumProc (ST s (AnswerSet (ST s (ESUnifVDGraph s t pd fn v sov uv)) (UnifSysSolution fn sov))))
st_as_commute_esuvdg_en_commute stas = st_en_commute_as (st_as_commute_esuvdg_from_explicit stas)

st_en_commute_as :: ESMGUConstraintsU t pd fn v sov uv => (forall s. ST s (EnumProc (AnswerSet (ST s (ESUnifVDGraph s t pd fn v sov uv)) (UnifSysSolution fn sov)))) -> (forall s. EnumProc (ST s (AnswerSet (ST s (ESUnifVDGraph s t pd fn v sov uv)) (UnifSysSolution fn sov))))
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

st_as_commute_esuvdg :: ESMGUConstraintsU t pd fn v sov uv => (forall s. ST s (AnswerSet (ST s (ESUnifVDGraph s t pd fn v sov uv)) (UnifSysSolution fn sov))) -> AnswerSet (RESUnifVDGraph t pd fn v sov uv) (UnifSysSolution fn sov)
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

so_unify_depgraph :: ESMGUConstraintsU t pd fn v sov uv => SOTerm fn sov -> SOTerm fn sov -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) (ESUnifRelSoId s t fn v sov uv)
so_unify_depgraph ltd rtd = do
	{
		lid <- introduce_sot_depgraph ltd;
		rid <- introduce_sot_depgraph rtd;
		
		ops <- prop_mergeEqDGSONodes lid rid;

		runStateTOps ops;

		-- Left or right don't matter, we just merged them.
		return lid
	}

fo_unify_depgraph :: ESMGUConstraintsU t pd fn v sov uv => TermDependant t fn v sov uv -> TermDependant t fn v sov uv -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) (ESUnifRelFoId s t fn v sov uv)
fo_unify_depgraph ltd rtd = do
	{
		lid <- introduce_fot_depgraph ltd;
		rid <- introduce_fot_depgraph rtd;
		
		ops <- prop_mergeEqDGFONodes lid rid;

		runStateTOps ops;

		-- Left or right don't matter, we just merged them.
		return lid
	}

introduce_fot_depgraph :: ESMGUConstraintsU t pd fn v sov uv => TermDependant t fn v sov uv -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) (ESUnifRelFoId s t fn v sov uv)
introduce_fot_depgraph td = introduce_fot_depgraph_us us (fromSOMetawrap somw) where (us,somw) = decompose_td td

introduce_fot_depgraph_us :: ESMGUConstraintsU t pd fn v sov uv => [uv] -> UTerm (t (SOTerm fn sov)) v -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) (ESUnifRelFoId s t fn v sov uv)
introduce_fot_depgraph_us us (UVar v) = return (relbwEqDGFoId (compose_td us (SOMetawrap (UVar v))))
introduce_fot_depgraph_us us (UTerm t) = do
	{
		fnid <- introduce_sot_depgraph fn;
		ss <- traverse (introduce_fot_depgraph_us us) sts;
		(nid,ops) <- prop_newAnonEqDGFOEdge fnid ss;

		runStateTOps ops;
		
		return nid
	}
	where
		(fn,sts) = unbuild_term t 

-- NOTE that we do assume that the SOTerm is normalized here!
introduce_sot_depgraph :: ESMGUConstraintsU t pd fn v sov uv => SOTerm fn sov -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) (ESUnifRelSoId s t fn v sov uv)
introduce_sot_depgraph (UVar v) = return (relbwEqDGSoId (UVar v))
introduce_sot_depgraph (UTerm (SOF (ConstF fn))) = return (relbwEqDGSoId (UTerm (SOF (ConstF fn))))
introduce_sot_depgraph (UTerm (SOF (Proj idx))) = return (relbwEqDGSoId (UTerm (SOF (Proj idx))))
introduce_sot_depgraph (UTerm (SOF (CompF h sfns))) = do
	{
		hid <- introduce_sot_depgraph h;
		ss <- traverse introduce_sot_depgraph sfns;
		(nid,ops) <- prop_newAnonEqDGSOEdge hid ss;

		runStateTOps ops;

		return nid
	}

-- These functions produce recursion through implicit composition.

multi_factorize :: ESMGUConstraintsU t pd fn v sov uv => RESUnifVDGraph t pd fn v sov uv -> AnswerSet (RESUnifVDGraph t pd fn v sov uv) (UnifSysSolution fn sov)
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

single_factorize :: ESMGUConstraintsU t pd fn v sov uv => RESUnifVDGraph t pd fn v sov uv -> AnswerSet (RESUnifVDGraph t pd fn v sov uv) (UnifSysSolution fn sov)
single_factorize resuvdg = case ctype of
	{
		ZeroFactorizeT -> validate_all_consistency ((factorize_candidate cand resuvdg) ?>>= SFactorize);
		HalfFactorizeT -> validate_all_consistency ((factorize_candidate cand resuvdg) ?>>= SFactorize);
		SingleFactorizeT -> validate_all_consistency ((factorize_candidate cand resuvdg) ?>>= SFactorize);
		_ -> ImplicitAS resuvdg
	}
	where
		cand = factorize_get_least resuvdg;
		ctype = factorize_type cand;	

zero_factorize :: ESMGUConstraintsU t pd fn v sov uv => RESUnifVDGraph t pd fn v sov uv -> AnswerSet (RESUnifVDGraph t pd fn v sov uv) (UnifSysSolution fn sov)
zero_factorize resuvdg = case ctype of
	{
		ZeroFactorizeT -> validate_all_consistency ((factorize_candidate cand resuvdg) ?>>= ZFactorize);
		_ -> ImplicitAS resuvdg
	}
	where
		cand = factorize_get_least resuvdg;
		ctype = factorize_type cand

factorize_type :: FactorizeCandidate t fn v sov uv -> FactorizeType
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
			SingleFactorizeFO _ _ -> return SingleFactorizeT;
			SingleFactorizeSO _ _ -> return SingleFactorizeT;
			MultiFactorize _ _ -> return MultiFactorizeT
		}
	})

factorize_candidate :: ESMGUConstraintsU t pd fn v sov uv => FactorizeCandidate t fn v sov uv -> RESUnifVDGraph t pd fn v sov uv -> AnswerSet (RESUnifVDGraph t pd fn v sov uv) (UnifSysSolution fn sov)
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
						let {d = fromJustErr "No representative element for the node target of a half factorization of function symbols!" mb_d; aty = arity d; ss = Prelude.map (relbwEqDGSoId . UTerm . SOF . Proj) [0..(aty-1)]};
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
						let {aty = length ss; hs = Prelude.map (relbwEqDGSoId . UTerm . SOF. Proj) [0..(aty - 1)]};
						let {fproj = (\n -> snd <$> runStateT (do {ops <- prop_mergeEqDGSONodes h n; runStateTOps ops}) esuvdg4)};
						let {enprojs = fmap fproj (uns_enum_from_list hs)};
						
						return (ExplicitAS (ImplicitAS <$> enprojs))
					}				
				};
				SingleFactorizeFO t sov -> do
				{
					-- Let's just try all projections for the variable's arity. The arity checks should remove any that don't match.
					let {fproj = (\idx -> snd <$> runStateT (factorize_in_proj sov idx) esuvdg)};
					let {enprojs = fmap fproj (uns_enum_from_list [0..((arity sov) - 1)])};
					(res_factorized,res_st) <- runStateT (factorize_in_fot_rigid t) esuvdg;				
					case res_factorized of
					{
						Inexistent -> return (ExplicitAS EnumProc.Empty);
						Distinct -> return (ExplicitAS EnumProc.Empty);
						Exist ch -> do
						{
							let {res_hst = snd <$> runStateT (factorize_in_flexrigid sov ch) esuvdg};
							--return (ExplicitAS (ImplicitAS res_hst --> (ImplicitAS <$> enprojs)))
							-- This ordering is important, as it makes the simplest solutions come first.
							return (ExplicitAS (uns_append (ImplicitAS <$> enprojs) (single_enum (ImplicitAS res_hst))))
						}
					}
				};
				SingleFactorizeSO t sov -> do
				{
					-- Let's just try all projections for the variable's arity. The arity checks should remove any that don't match.
					let {fproj = (\idx -> snd <$> runStateT (factorize_in_proj sov idx) esuvdg)};
					let {enprojs = fmap fproj (uns_enum_from_list [0..((arity sov) - 1)])};
					(res_factorized,res_st) <- runStateT (factorize_in_sot_rigid t) esuvdg;
					case res_factorized of
					{
						Inexistent -> return (ExplicitAS EnumProc.Empty);
						Distinct -> return (ExplicitAS EnumProc.Empty);
						Exist ch -> do
						{
							let {res_hst = snd <$> runStateT (factorize_in_flexrigid sov ch) esuvdg};
							--return (ExplicitAS (ImplicitAS res_hst --> (ImplicitAS <$> enprojs)))
							-- This ordering is important, as it makes the simplest solutions come first.
							return (ExplicitAS (uns_append (ImplicitAS <$> enprojs) (single_enum (ImplicitAS res_hst))))
						}
					}
				};
				MultiFactorize sov nvars -> do
				{
					let {fns = funcs (esuvdg ^. (lens_esunifdgraph_sosig . lens_fosig)); aty = arity sov; vfns = econcat (Prelude.map fromJust (Prelude.filter isJust (Prelude.map (fns !!?) [0..aty])))};
					let {ffn = (\fn -> snd <$> runStateT (factorize_in_flexrigid sov (UTerm (SOF (ConstF fn)))) esuvdg)};
					let {ren = fmap ffn vfns};
					let {r = (ExplicitAS (ImplicitAS <$> ren))};
					return r
				}
			}
		})

factorize_get_least :: ESMGUConstraintsU t pd fn v sov uv => RESUnifVDGraph t pd fn v sov uv -> FactorizeCandidate t fn v sov uv
factorize_get_least resuvdg = FC (do
	{
		esuvdg <- fromRESUnifVDGraph resuvdg;
		let {fonodes = Prelude.map (DirectId . EqDGFoId .  dgid . fromJust) (Prelude.filter isJust (esuvdg ^. (lens_esunifdgraph_dgraph . lens_eqdgraph . lens_fonodes)))};
		let {sonodes = Prelude.map (DirectId . EqDGSoId .  dgid . fromJust) (Prelude.filter isJust (esuvdg ^. (lens_esunifdgraph_dgraph . lens_eqdgraph . lens_sonodes)))};

		let {stfocands = traverse factorize_get_fo_candidate fonodes; stsocands = traverse factorize_get_so_candidate sonodes; stsoecands = traverse factorize_get_soe_candidate sonodes; stallcands = stfocands >>=++ stsocands >>=++ stsoecands};
		(cands,_) <- runStateT stallcands esuvdg;
		let {mb_cand = minimumMay cands; cand = fromMaybe NoFactorize mb_cand};
		
		return cand
	})

factorize_get_soe_candidate :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelSoId s t fn v sov uv -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) (FactorizeCandidateS s t fn v sov uv)
factorize_get_soe_candidate sot = do
	{
		sots <- mzoom lens_esunifdgraph_dgraph (getEquivDGSONodes sot);
		ines <- mzoom lens_esunifdgraph_dgraph (st_searchInEqDGSOEdges [] [] sot);
		if ((all isvar_sot sots) || (Prelude.null ines))
		then (return NoFactorize)
		else 	(if (any isproj_sot sots)
			-- Any one edge works here.
			then (return (HalfFactorizeP (head ines)))
			-- If not all are variables and none is a projection, then at least one must be a function symbol.
			else (return (HalfFactorizeF sot)))

	}

factorize_get_fo_candidate :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelFoId s t fn v sov uv -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) (FactorizeCandidateS s t fn v sov uv)
factorize_get_fo_candidate fot = do
	{
		ines <- mzoom lens_esunifdgraph_dgraph (st_searchInEqDGFOEdges [] [] fot);
		if ((length ines) <= 1) then (return NoFactorize) else do
		{
			inhs <- mzoom lens_esunifdgraph_dgraph (traverse eqDGFOEdge_head ines);
			inhsots <- mzoom lens_esunifdgraph_dgraph (m_concat getEquivDGSONodes inhs);
			if (all (not . isvar_sot) inhsots) then (return (ZeroFactorizeFO fot))
			else (if (any (not . isvar_sot) inhsots) then do
			{
				let {avar = case (fromJust (find isvar_sot inhsots)) of {UVar x -> x}};
				return (SingleFactorizeFO fot avar)
			}
			else do
			{
				let {avar = case (head inhsots) of {UVar x -> x}; nvars = length inhsots};
				return (MultiFactorize avar nvars)
			}
			)
		}
	}

factorize_get_so_candidate :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelSoId s t fn v sov uv -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) (FactorizeCandidateS s t fn v sov uv)
factorize_get_so_candidate sot = do
	{
		ines <- mzoom lens_esunifdgraph_dgraph (st_searchInEqDGSOEdges [] [] sot);
		if ((length ines) <= 1) then (return NoFactorize) else do
		{
			inhs <- mzoom lens_esunifdgraph_dgraph (traverse eqDGSOEdge_head ines);
			inhsots <- mzoom lens_esunifdgraph_dgraph (m_concat getEquivDGSONodes inhs);
			if (all (not . isvar_sot) inhsots) then (return (ZeroFactorizeSO sot))
			else (if (any (not . isvar_sot) inhsots) then do
			{
				let {avar = case (fromJust (find isvar_sot inhsots)) of {UVar x -> x}};
				return (SingleFactorizeSO sot avar)
			}
			else do
			{
				let {avar = case (head inhsots) of {UVar x -> x}; nvars = length inhsots};
				return (MultiFactorize avar nvars)
			}
			)
		}
	}

factorize_soe_consttarget_head :: ESMGUConstraintsU t pd fn v sov uv => Int -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) ()
factorize_soe_consttarget_head soe = do
	{
		h <- mzoom lens_esunifdgraph_dgraph (eqDGSOEdge_head soe);
		ss <- mzoom lens_esunifdgraph_dgraph (eqDGSOEdge_sources soe);
		t <- mzoom lens_esunifdgraph_dgraph (eqDGSOEdge_target soe);

		let {fss = (\(s,idx) -> prop_mergeEqDGSONodes s (relbwEqDGSoId (UTerm (SOF (Proj idx)))))};

		ops1 <- prop_deleteEqDGSOEdge soe;
		ops2 <- m_concat fss (zip ss [0..]);
		ops3 <- prop_mergeEqDGSONodes h t;

		runStateTOps (ops1 ++ ops2 ++ ops3)
	}

-- We assume the second-order term being given is indeed simple (not a composition), and non-variable. This should be true in every case anyway.
factorize_in_flexrigid :: ESMGUConstraintsU t pd fn v sov uv => sov -> SOTerm fn sov -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) ()
factorize_in_flexrigid sov sot = do
	{
		let {vsot = UVar sov; vsotid = relbwEqDGSoId vsot; vaty = arity sov};
		let {aty = arity sot; sotid = relbwEqDGSoId sot};		
		let {fnewvar = mzoom lens_esunifdgraph_sosig (new_sovar vaty); fnewnode = (\_ -> relbwEqDGSoId . UVar <$> fnewvar)};
		newss <- traverse fnewnode [0..(aty-1)];
		ops <- prop_newEqDGSOEdge sotid newss vsotid;
		
		runStateTOps ops
	}

factorize_in_proj :: ESMGUConstraintsU t pd fn v sov uv => sov -> Int -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) ()
factorize_in_proj sov idx = do
	{
		let {sot = UVar sov; sotid = relbwEqDGSoId sot};
		let {projt = UTerm (SOF (Proj idx)); projid = relbwEqDGSoId projt};
		
		ops <- prop_mergeEqDGSONodes sotid projid;
		
		runStateTOps ops
	}

-- Factorizes all rigid incoming heads to the node, merging them into one.
-- It also merges the sources of all the edges with these heads coming into the target node.
-- There may be no rigid incoming head, or multiple incompatible ones, so we use ExistUnique to indicate this.
-- This does not do anything with variable incoming heads. Therefore, the result is deterministic (except for potentially generating incompatibilities).
factorize_in_sot_rigid :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelSoId s t fn v sov uv -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) (ExistUnique (SOTerm fn sov))
factorize_in_sot_rigid sot = do
	{
		ines <- mzoom lens_esunifdgraph_dgraph (st_searchInEqDGSOEdges [] [] sot);
		inhs <- mzoom lens_esunifdgraph_dgraph (traverse eqDGSOEdge_head ines);
		inhsots <- mzoom lens_esunifdgraph_dgraph (m_concat getEquivDGSONodes inhs);
		let {nvhsots = Prelude.filter (not . isvar_sot) inhsots};
		if (allEq nvhsots) then do
		{
			if Prelude.null nvhsots then (return Inexistent)
			else do
			{
				let {(mainh:otherhs) = nvhsots; mainhid = relbwEqDGSoId mainh; otherhids = Prelude.map relbwEqDGSoId otherhs};
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

				return (Exist mainh)
			}
		}
		else (return Distinct)		
	}

factorize_in_fot_rigid :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelFoId s t fn v sov uv -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) (ExistUnique (SOTerm fn sov))
factorize_in_fot_rigid fot = do
	{
		ines <- mzoom lens_esunifdgraph_dgraph (st_searchInEqDGFOEdges [] [] fot);
		inhs <- mzoom lens_esunifdgraph_dgraph (traverse eqDGFOEdge_head ines);
		inhsots <- mzoom lens_esunifdgraph_dgraph (m_concat getEquivDGSONodes inhs);
		let {nvhsots = Prelude.filter (not . isvar_sot) inhsots};
		if (allEq nvhsots) then do
		{
			if Prelude.null nvhsots then (return Inexistent)
			else do
			{
				let {(mainh:otherhs) = nvhsots; mainhid = relbwEqDGSoId mainh; otherhids = Prelude.map relbwEqDGSoId otherhs};
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

				return (Exist mainh)
			}
		}
		else (return Distinct)
	}

validate_all_consistency :: ESMGUConstraintsU t pd fn v sov uv => AnswerSet (RESUnifVDGraph t pd fn v sov uv) (UnifSysSolution fn sov) -> AnswerSet (RESUnifVDGraph t pd fn v sov uv) (UnifSysSolution fn sov)
validate_all_consistency as = as ?>>= SOTConsistency ?>>= FOTConsistency ?>>= HeadAritySO ?>>= HeadArityFO ?>>= OccursCheckSO ?>>= OccursCheckFO

validate_occurs_check_fo :: ESMGUConstraintsU t pd fn v sov uv => RESUnifVDGraph t pd fn v sov uv -> AnswerSet (RESUnifVDGraph t pd fn v sov uv) (UnifSysSolution fn sov)
validate_occurs_check_fo resuvdg = if consistent then (ImplicitAS resuvdg) else (ExplicitAS EnumProc.Empty)
	where
		checked = occurs_check_fo;
		consistent = getStateTSTESUnifVDGraph checked resuvdg

occurs_check_fo :: ESMGUConstraintsU t pd fn v sov uv => StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) Bool
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
					let {fdownhts = Prelude.filter (\sot -> ((not . isvar_sot) sot) && ((not . isproj_sot) sot)) downhts};
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
check_cycle_up_fot :: ESMGUConstraintsU t pd fn v sov uv => [ESUnifRelSoId s t fn v sov uv] -> [ESUnifRelFoId s t fn v sov uv] -> ESUnifRelFoId s t fn v sov uv -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) (Bool,[([ESUnifRelSoId s t fn v sov uv],[ESUnifRelFoId s t fn v sov uv])])
check_cycle_up_fot downhs downs fot = do
	{
		cycle <- mzoom lens_esunifdgraph_dgraph (m_any (eqSTRelativeEqDGFoIds fot) downs);
		if cycle then (return (True,[(downhs,downs)])) else do
		{
			ines <- mzoom lens_esunifdgraph_dgraph (st_searchInEqDGFOEdges [] [] fot);
			ssh <- mzoom lens_esunifdgraph_dgraph (traverse fh ines);
			ups <- traverse_collect ff ffd ssh;
			return ups
		}
	}
	where 
		f = (\(f1,t1) -> \(f2,t2) -> (f1 || f2,t1++t2));
		ff = Prelude.foldr f (False,[]);
		fh = (\e -> do {h <- eqDGFOEdge_head e; ss <- eqDGFOEdge_sources e; return (h,ss)});
		fd = (\h -> \s -> check_cycle_up_fot (h:downhs) (fot:downs) s);
		ffd = (\(h,ss) -> traverse_collect ff (fd h) ss);

validate_occurs_check_so :: ESMGUConstraintsU t pd fn v sov uv => RESUnifVDGraph t pd fn v sov uv -> AnswerSet (RESUnifVDGraph t pd fn v sov uv) (UnifSysSolution fn sov)
validate_occurs_check_so resuvdg = if consistent then (ImplicitAS resuvdg) else (ExplicitAS EnumProc.Empty)
	where
		checked = occurs_check_so;
		consistent = getStateTSTESUnifVDGraph checked resuvdg

occurs_check_so :: ESMGUConstraintsU t pd fn v sov uv => StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) Bool
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
					let {fdownts = Prelude.filter (\sot -> ((not . isvar_sot) sot) && ((not . isproj_sot) sot)) (downhts ++ downts)};
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
check_cycle_up_sot :: ESMGUConstraintsU t pd fn v sov uv => [ESUnifRelSoId s t fn v sov uv] -> [ESUnifRelSoId s t fn v sov uv] -> ESUnifRelSoId s t fn v sov uv -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) (Bool,[([ESUnifRelSoId s t fn v sov uv],[ESUnifRelSoId s t fn v sov uv])])
check_cycle_up_sot downhs downs sot = do
	{
		cycle <- mzoom lens_esunifdgraph_dgraph (m_any (eqSTRelativeEqDGSoIds sot) downs);
		if cycle then (return (True,[(downhs,downs)])) else do
		{
			ines <- mzoom lens_esunifdgraph_dgraph (st_searchInEqDGSOEdges [] [] sot);
			ssh <- mzoom lens_esunifdgraph_dgraph (traverse fh ines);
			ups <- traverse_collect ff ffd ssh;
			return ups
		}
	}
	where 
		f = (\(f1,t1) -> \(f2,t2) -> (f1 || f2,t1++t2));
		ff = Prelude.foldr f (False,[]);
		fh = (\e -> do {h <- eqDGSOEdge_head e; ss <- eqDGSOEdge_sources e; return (h,ss)});
		fd = (\h -> \s -> check_cycle_up_sot (h:downhs) (sot:downs) s);
		ffd = (\(h,ss) -> do {rss <- traverse_collect ff (fd h) ss; rh <- check_cycle_up_sot downhs (sot:downs) h; return (f rss rh)});

validate_target_arity_so :: ESMGUConstraintsU t pd fn v sov uv => RESUnifVDGraph t pd fn v sov uv -> AnswerSet (RESUnifVDGraph t pd fn v sov uv) (UnifSysSolution fn sov)
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

validate_target_arity_sot :: ESMGUConstraintsU t pd fn v sov uv => (forall s. ESUnifRelSoId s t fn v sov uv) -> RESUnifVDGraph t pd fn v sov uv -> AnswerSet (RESUnifVDGraph t pd fn v sov uv) (UnifSysSolution fn sov)
validate_target_arity_sot sot resuvdg = if consistent then (ImplicitAS resuvdg) else (ExplicitAS EnumProc.Empty) where consistent = getStateTSTESUnifVDGraph (check_target_arity_sot sot) resuvdg

check_target_arity_so :: ESMGUConstraintsU t pd fn v sov uv => StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) Bool
check_target_arity_so = (StateT (\esuvdg -> runStateT (all id <$> traverse check_target_arity_sot (Prelude.map (DirectId . EqDGSoId . dgid . fromJust) (Prelude.filter isJust ((eqdgraph (esunifdgraph esuvdg)) ^. lens_sonodes)))) esuvdg))

check_target_arity_sot :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelSoId s t fn v sov uv -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) Bool
check_target_arity_sot sot = mzoom lens_esunifdgraph_dgraph (do
	{
		sots <- getEquivDGSONodes sot;
		-- They must all be variables! If they are not, then all incoming edges must have variable heads; and as long as that's true, it's correct.
		if (not (all isvar_sot sots)) then do
		{
			ines <- st_searchInEqDGSOEdges [] [] sot;
			inhs <- traverse eqDGSOEdge_head ines;
			inhsots <- m_concat getEquivDGSONodes inhs;
			let {innovhs = Prelude.filter (not . isvar_sot) inhsots};
			return (Data.List.null innovhs)
		}
		else do
		{
			sott <- getSTRelativeEqDGSoCoId sot;
			let {sota = arity <$> sott};
			
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

getSOTArity :: (HasArity fn, HasArity sov) => Maybe (SOTerm fn sov) -> Maybe Int
getSOTArity = fmap sot_min_arity

getNodeArity :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelSoId s t fn v sov uv -> StateT (ESUnifDGraph s t fn v sov uv) (ST s) (Maybe Int)
getNodeArity sot = do
	{
		ines <- st_searchInEqDGSOEdges [] [] sot;
		if (Data.List.null ines) then do
		{
			rep <- getSTRelativeEqDGSoCoId sot;
			return (getSOTArity rep)
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

validate_head_arity_fo :: ESMGUConstraintsU t pd fn v sov uv => RESUnifVDGraph t pd fn v sov uv -> AnswerSet (RESUnifVDGraph t pd fn v sov uv) (UnifSysSolution fn sov)
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

validate_head_arity_foe :: ESMGUConstraintsU t pd fn v sov uv => Int -> RESUnifVDGraph t pd fn v sov uv -> AnswerSet (RESUnifVDGraph t pd fn v sov uv) (UnifSysSolution fn sov)
validate_head_arity_foe foe resuvdg = if consistent then (ImplicitAS resuvdg) else (ExplicitAS EnumProc.Empty) where consistent = getStateTSTESUnifVDGraph (check_head_arity_foe foe) resuvdg

check_head_arity_fo :: ESMGUConstraintsU t pd fn v sov uv => StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) Bool
check_head_arity_fo = (StateT (\esuvdg -> runStateT (all id <$> traverse check_head_arity_foe (Prelude.map (dgid . fromJust) (Prelude.filter isJust ((eqdgraph (esunifdgraph esuvdg)) ^. lens_foedges)))) esuvdg))

check_head_arity_foe :: ESMGUConstraintsU t pd fn v sov uv => Int -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) Bool
check_head_arity_foe foe = do
	{
		h <- mzoom lens_esunifdgraph_dgraph (eqDGFOEdge_head foe);
		sots <- mzoom lens_esunifdgraph_dgraph (getEquivDGSONodes h);
		let {arities = Prelude.map sot_min_arity sots; arity = Prelude.foldr (\i -> \m -> max i m) 0 arities};
		ss <- mzoom lens_esunifdgraph_dgraph (eqDGFOEdge_sources foe);
		return ((length ss) >= arity)
	}

validate_head_arity_so :: ESMGUConstraintsU t pd fn v sov uv => RESUnifVDGraph t pd fn v sov uv -> AnswerSet (RESUnifVDGraph t pd fn v sov uv) (UnifSysSolution fn sov)
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

validate_head_arity_soe :: ESMGUConstraintsU t pd fn v sov uv => Int -> RESUnifVDGraph t pd fn v sov uv -> AnswerSet (RESUnifVDGraph t pd fn v sov uv) (UnifSysSolution fn sov)
validate_head_arity_soe soe resuvdg = if consistent then (ImplicitAS resuvdg) else (ExplicitAS EnumProc.Empty) where consistent = getStateTSTESUnifVDGraph (check_head_arity_soe soe) resuvdg

check_head_arity_so :: ESMGUConstraintsU t pd fn v sov uv => StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) Bool
check_head_arity_so = (StateT (\esuvdg -> runStateT (all id <$> traverse check_head_arity_soe (Prelude.map (dgid . fromJust) (Prelude.filter isJust ((eqdgraph (esunifdgraph esuvdg)) ^. lens_soedges)))) esuvdg))

-- IMPORTANT NOTE: We leave this as is for now, since it is likely it is enough for the implementation. However, if we want to be more accurate to the theory, what needs to happen here is that we need to re-add the arity to the projections and be strict about it, INCLUDING when handling second-order variables and consider the issue with compositions of second-order variables and projections etc.
check_head_arity_soe :: ESMGUConstraintsU t pd fn v sov uv => Int -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) Bool
check_head_arity_soe soe = do
	{
		h <- mzoom lens_esunifdgraph_dgraph (eqDGSOEdge_head soe);
		sots <- mzoom lens_esunifdgraph_dgraph (getEquivDGSONodes h);
		let {arities = Prelude.map sot_min_arity sots; arity = Prelude.foldr (\i -> \m -> max i m) 0 arities};
		ss <- mzoom lens_esunifdgraph_dgraph (eqDGSOEdge_sources soe);
		return ((length ss) >= arity)
	}

validate_sot_consistency :: ESMGUConstraintsU t pd fn v sov uv => RESUnifVDGraph t pd fn v sov uv -> AnswerSet (RESUnifVDGraph t pd fn v sov uv) (UnifSysSolution fn sov)
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

validate_sot_consistency_sot :: ESMGUConstraintsU t pd fn v sov uv => (forall s. ESUnifRelSoId s t fn v sov uv) -> RESUnifVDGraph t pd fn v sov uv -> AnswerSet (RESUnifVDGraph t pd fn v sov uv) (UnifSysSolution fn sov)
validate_sot_consistency_sot sot resuvdg = if consistent then (ImplicitAS resuvdg) else (ExplicitAS EnumProc.Empty) where consistent = getStateTSTESUnifVDGraph (check_sot_consistency_sot sot) resuvdg

check_sot_consistency :: ESMGUConstraintsU t pd fn v sov uv => StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) Bool
check_sot_consistency = (StateT (\esuvdg -> runStateT (all id <$> traverse check_sot_consistency_sot (Prelude.map (DirectId . EqDGSoId . dgid . fromJust) (Prelude.filter isJust ((eqdgraph (esunifdgraph esuvdg)) ^. lens_sonodes)))) esuvdg))

check_sot_consistency_sot :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelSoId s t fn v sov uv -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) Bool
check_sot_consistency_sot sot = do
	{
		sots <- mzoom lens_esunifdgraph_dgraph (getEquivDGSONodes sot);
		let {nvsots = Prelude.filter (not . isvar_sot) sots};
		-- NOTE: I could consider checking that all variables in the node have the same arity here. We do not do this for now, as it may be incorrect (I don't remember exactly right now) and I believe it is not necessary. But this note is a witness that this is a thing worth thinking about if it may be a source of errors.
		return (allEq nvsots)
	}

validate_fot_consistency :: ESMGUConstraintsU t pd fn v sov uv => RESUnifVDGraph t pd fn v sov uv -> AnswerSet (RESUnifVDGraph t pd fn v sov uv) (UnifSysSolution fn sov)
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

validate_fot_consistency_fot :: ESMGUConstraintsU t pd fn v sov uv => (forall s. ESUnifRelFoId s t fn v sov uv) -> RESUnifVDGraph t pd fn v sov uv -> AnswerSet (RESUnifVDGraph t pd fn v sov uv) (UnifSysSolution fn sov)
validate_fot_consistency_fot fot resuvdg = if consistent then (ImplicitAS resuvdg) else (ExplicitAS EnumProc.Empty) where consistent = getStateTSTESUnifVDGraph (check_fot_consistency_fot fot) resuvdg

check_fot_consistency :: ESMGUConstraintsU t pd fn v sov uv => StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) Bool
check_fot_consistency = (StateT (\esuvdg -> runStateT (all id <$> traverse check_fot_consistency_fot (Prelude.map (DirectId . EqDGFoId . dgid . fromJust) (Prelude.filter isJust ((eqdgraph (esunifdgraph esuvdg)) ^. lens_fonodes)))) esuvdg))

check_fot_consistency_fot :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelFoId s t fn v sov uv -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) Bool
check_fot_consistency_fot fot = do
	{
		fots <- mzoom lens_esunifdgraph_dgraph (getEquivDGFONodes fot);
		let {nvfots = Prelude.filter (not . is_td_var) fots};
		return (allEq nvfots)
	}

as_esu_prenormalize :: ESMGUConstraintsU t pd fn v sov uv => RESUnifVDGraph t pd fn v sov uv -> AnswerSet (RESUnifVDGraph t pd fn v sov uv) (UnifSysSolution fn sov)
as_esu_prenormalize resuvdg = ImplicitAS (getStateTSTESUnifVDGraphState esu_prenormalize resuvdg)

esu_prenormalize :: ESMGUConstraintsU t pd fn v sov uv => StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) ()
esu_prenormalize = (StateT (\esuvdg -> runStateT (runStateTOps (allops esuvdg)) esuvdg)) >> pass where allops = (\esuvdg -> (esu_fo_dump_ops esuvdg) ++ (esu_so_dump_ops esuvdg) ++ (esu_so_simplify_projections_ops esuvdg) ++ (esu_fo_simplify_projections_ops esuvdg) ++ (esu_vertical_commute_ops esuvdg) ++ (esu_vertical_commute_eq_ops esuvdg) ++ (esu_vertical_align_ops esuvdg) ++ (esu_sozip_ops esuvdg) ++ (esu_fozip_ops esuvdg))

as_esu_fo_dump :: ESMGUConstraintsU t pd fn v sov uv => RESUnifVDGraph t pd fn v sov uv -> AnswerSet (RESUnifVDGraph t pd fn v sov uv) (UnifSysSolution fn sov)
as_esu_fo_dump resuvdg = ImplicitAS (getStateTSTESUnifVDGraphState esu_fo_dump resuvdg)

esu_fo_dump :: ESMGUConstraintsU t pd fn v sov uv => StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) ()
esu_fo_dump = (StateT (\esuvdg -> runStateT (runStateTOps (esu_fo_dump_ops esuvdg)) esuvdg)) >> pass

esu_fo_dump_ops :: ESMGUConstraintsU t pd fn v sov uv => ESUnifVDGraph s t pd fn v sov uv -> [ESUnifDGOp s t pd fn v sov uv]
esu_fo_dump_ops esuvdg = Prelude.map (ESUFODump . dgid . fromJust) (Prelude.filter isJust ((eqdgraph (esunifdgraph esuvdg)) ^. lens_foedges))

esu_fo_dump_foe :: ESMGUConstraintsU t pd fn v sov uv => Int -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) [ESUnifDGOp s t pd fn v sov uv]
esu_fo_dump_foe foe = do
	{
		-- First check if the edge still exists!
		eex <- mzoom lens_esunifdgraph_dgraph (checkEqDGFOEdge foe);
		if (not eex) then (return []) else do
		{
			-- IMPORTANT CHOICE: We only dump when the head of an edge has EXACTLY ONE incoming edge. If it has none there's no dump to be made of course, but more importantly, if it has several, we won't dump until we factorize them. Since factorizing is the central and not always done operation, this choice has implications on what a partly normalized graph looks like.
			-- It also means that after factorizing a second-order node we need to check for dumping on all the edges it's a head of.
			h <- mzoom lens_esunifdgraph_dgraph (eqDGFOEdge_head foe);
			ss <- mzoom lens_esunifdgraph_dgraph (eqDGFOEdge_sources foe);
			t <- mzoom lens_esunifdgraph_dgraph (eqDGFOEdge_target foe);
			ines <- mzoom lens_esunifdgraph_dgraph (st_searchInEqDGSOEdges [] [] h);
			if ((length ines) /= 1) then (return []) else do
			{
				let {ine = head ines};
				rh <- mzoom lens_esunifdgraph_dgraph (eqDGSOEdge_head ine);
				rss <- mzoom lens_esunifdgraph_dgraph (eqDGSOEdge_sources ine);
				let {nsf = (\s -> prop_newAnonEqDGFOEdge s ss)};
				let {comb = (\(ns,ops) -> \(nss,opss) -> (ns:nss,ops++opss))};
				(nss,result1) <- Prelude.foldr comb ([],[]) <$> traverse nsf rss;

				result2 <- (return result1) >>=++ (prop_newEqDGFOEdge rh nss t);

				result3 <- (return result2) >>=++ (prop_deleteEqDGFOEdge foe);

				return result3
			}
		}
	}

as_esu_so_dump :: ESMGUConstraintsU t pd fn v sov uv => RESUnifVDGraph t pd fn v sov uv -> AnswerSet (RESUnifVDGraph t pd fn v sov uv) (UnifSysSolution fn sov)
as_esu_so_dump resuvdg = ImplicitAS (getStateTSTESUnifVDGraphState esu_so_dump resuvdg)

esu_so_dump :: ESMGUConstraintsU t pd fn v sov uv => StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) ()
esu_so_dump = (StateT (\esuvdg -> runStateT (runStateTOps (esu_so_dump_ops esuvdg)) esuvdg)) >> pass

esu_so_dump_ops :: ESMGUConstraintsU t pd fn v sov uv => ESUnifVDGraph s t pd fn v sov uv -> [ESUnifDGOp s t pd fn v sov uv]
esu_so_dump_ops esuvdg = Prelude.map (ESUSODump . dgid . fromJust) (Prelude.filter isJust ((eqdgraph (esunifdgraph esuvdg)) ^. lens_soedges))

esu_so_dump_soe :: ESMGUConstraintsU t pd fn v sov uv => Int -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) [ESUnifDGOp s t pd fn v sov uv]
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
				gtraceM False (show hts);
				if (any isproj_sot hts) then (return []) else do
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

as_esu_so_simplify_projections :: ESMGUConstraintsU t pd fn v sov uv => RESUnifVDGraph t pd fn v sov uv -> AnswerSet (RESUnifVDGraph t pd fn v sov uv) (UnifSysSolution fn sov)
as_esu_so_simplify_projections resuvdg = ImplicitAS (getStateTSTESUnifVDGraphState esu_so_simplify_projections resuvdg)

esu_so_simplify_projections :: ESMGUConstraintsU t pd fn v sov uv => StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) ()
esu_so_simplify_projections = (StateT (\esuvdg -> runStateT (runStateTOps (esu_so_simplify_projections_ops esuvdg)) esuvdg)) >> pass

esu_so_simplify_projections_ops :: ESMGUConstraintsU t pd fn v sov uv => ESUnifVDGraph s t pd fn v sov uv -> [ESUnifDGOp s t pd fn v sov uv]
esu_so_simplify_projections_ops esuvdg = Prelude.map (ESUSOSimpProj . dgid . fromJust) (Prelude.filter isJust ((eqdgraph (esunifdgraph esuvdg)) ^. lens_soedges))

esu_so_simplify_proj_soe :: ESMGUConstraintsU t pd fn v sov uv => Int -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) [ESUnifDGOp s t pd fn v sov uv]
esu_so_simplify_proj_soe soe = do
	{
		-- First check if the edge still exists!
		eex <- mzoom lens_esunifdgraph_dgraph (checkEqDGSOEdge soe);
		if (not eex) then (return []) else do
		{
			-- We check if indeed the head contains projections
			h <- mzoom lens_esunifdgraph_dgraph (eqDGSOEdge_head soe);
			sots <- mzoom lens_esunifdgraph_dgraph (getEquivDGSONodes h);
			let {mb_proj = find isproj_sot sots; proj = fromJustErr "esu_so_simplify_proj_soe mb_proj" mb_proj; idx = case proj of {UTerm (SOF (Proj idx)) -> idx}};
			if (isJust mb_proj) then do
			{				
				ss <- mzoom lens_esunifdgraph_dgraph (eqDGSOEdge_sources soe);
				t <- mzoom lens_esunifdgraph_dgraph (eqDGSOEdge_target soe);
				-- Note that we do not flag the incompatibility here if it so happens that there are not enough inputs to the projection, we simply do nothing if that happens. This needs to be checked outside anyway.
				-- if (length ss) <= idx then (return [])) else do
				--if (length ss) <= idx then (trace ("Projection does not have enough inputs! Has: " ++ (show (length ss)) ++ ", but is looking for " ++ (show idx) ++ "th projection.") (return [])) else do
				if (length ss) <= idx then (return []) else do
				{
					result1 <- prop_mergeEqDGSONodes (ss !! idx) t;
					result2 <- (return result1) >>=++ (prop_deleteEqDGSOEdge soe);

					return result2
				}
			}
			else (return [])
		}
	}

as_esu_fo_simplify_projections :: ESMGUConstraintsU t pd fn v sov uv => RESUnifVDGraph t pd fn v sov uv -> AnswerSet (RESUnifVDGraph t pd fn v sov uv) (UnifSysSolution fn sov)
as_esu_fo_simplify_projections resuvdg = ImplicitAS (getStateTSTESUnifVDGraphState esu_fo_simplify_projections resuvdg)

esu_fo_simplify_projections :: ESMGUConstraintsU t pd fn v sov uv => StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) ()
esu_fo_simplify_projections = (StateT (\esuvdg -> runStateT (runStateTOps (esu_fo_simplify_projections_ops esuvdg)) esuvdg)) >> pass

esu_fo_simplify_projections_ops :: ESMGUConstraintsU t pd fn v sov uv => ESUnifVDGraph s t pd fn v sov uv -> [ESUnifDGOp s t pd fn v sov uv]
esu_fo_simplify_projections_ops esuvdg = Prelude.map (ESUFOSimpProj . dgid . fromJust) (Prelude.filter isJust ((eqdgraph (esunifdgraph esuvdg)) ^. lens_foedges))

esu_fo_simplify_proj_foe :: ESMGUConstraintsU t pd fn v sov uv => Int -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) [ESUnifDGOp s t pd fn v sov uv]
esu_fo_simplify_proj_foe foe = do
	{
		-- First check if the edge still exists!
		eex <- mzoom lens_esunifdgraph_dgraph (checkEqDGFOEdge foe);
		if (not eex) then (return []) else do
		{
			-- We check if indeed the head contains projections
			h <- mzoom lens_esunifdgraph_dgraph (eqDGFOEdge_head foe);
			sots <- mzoom lens_esunifdgraph_dgraph (getEquivDGSONodes h);
			let {mb_proj = find isproj_sot sots; proj = fromJustErr "esu_fo_simplify_proj_foe mb_proj" mb_proj; idx = case proj of {UTerm (SOF (Proj idx)) -> idx}};
			if (isJust mb_proj) then do
			{
				ss <- mzoom lens_esunifdgraph_dgraph (eqDGFOEdge_sources foe);
				t <- mzoom lens_esunifdgraph_dgraph (eqDGFOEdge_target foe);
				-- Note that we do not flag the incompatibility here if it so happens that there are not enough inputs to the projection, we simply do nothing if that happens. This needs to be checked outside anyway.
				-- if (length ss) <= idx then (return [])) else do
				--if (length ss) <= idx then (trace ("Projection does not have enough inputs! Has: " ++ (show (length ss)) ++ ", but is looking for " ++ (show idx) ++ "th projection.") (return [])) else do
				if (length ss) <= idx then (return []) else do
				{
					result1 <- prop_mergeEqDGFONodes (ss !! idx) t;
					result2 <- (return result1) >>=++ (prop_deleteEqDGFOEdge foe);

					return result2
				}
			}
			else (return [])
		}
	}

as_esu_vertical_commute :: ESMGUConstraintsU t pd fn v sov uv => RESUnifVDGraph t pd fn v sov uv -> AnswerSet (RESUnifVDGraph t pd fn v sov uv) (UnifSysSolution fn sov)
as_esu_vertical_commute resuvdg = ImplicitAS (getStateTSTESUnifVDGraphState esu_vertical_commute resuvdg)

esu_vertical_commute :: ESMGUConstraintsU t pd fn v sov uv => StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) ()
esu_vertical_commute = (StateT (\esuvdg -> runStateT (runStateTOps (esu_vertical_commute_ops esuvdg)) esuvdg)) >> pass

esu_vertical_commute_ops :: ESMGUConstraintsU t pd fn v sov uv => ESUnifVDGraph s t pd fn v sov uv -> [ESUnifDGOp s t pd fn v sov uv]
esu_vertical_commute_ops esuvdg = Prelude.map ESUVCommuteFo (esunifdgraph_vfoedges esuvdg)

esu_vertical_commute_fo_edge :: ESMGUConstraintsU t pd fn v sov uv => ESUnifVFoEdge s t fn v sov uv -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) [ESUnifDGOp s t pd fn v sov uv]
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
esu_vertical_commute_fo_edge_hedge :: ESMGUConstraintsU t pd fn v sov uv => ESUnifVFoEdge s t fn v sov uv -> Int -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) [ESUnifDGOp s t pd fn v sov uv]
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

as_esu_vertical_commute_eq :: ESMGUConstraintsU t pd fn v sov uv => RESUnifVDGraph t pd fn v sov uv -> AnswerSet (RESUnifVDGraph t pd fn v sov uv) (UnifSysSolution fn sov)
as_esu_vertical_commute_eq resuvdg = ImplicitAS (getStateTSTESUnifVDGraphState esu_vertical_commute_eq resuvdg)

esu_vertical_commute_eq :: ESMGUConstraintsU t pd fn v sov uv => StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) ()
esu_vertical_commute_eq = (StateT (\esuvdg -> runStateT (runStateTOps (esu_vertical_commute_eq_ops esuvdg)) esuvdg)) >> pass

esu_vertical_commute_eq_ops :: ESMGUConstraintsU t pd fn v sov uv => ESUnifVDGraph s t pd fn v sov uv -> [ESUnifDGOp s t pd fn v sov uv]
esu_vertical_commute_eq_ops esuvdg = Prelude.map ESUVCommuteEqFo (esunifdgraph_vfoedges esuvdg)

esu_vertical_commute_eq_fo_edge :: ESMGUConstraintsU t pd fn v sov uv => ESUnifVFoEdge s t fn v sov uv -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) [ESUnifDGOp s t pd fn v sov uv]
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

esu_vertical_commute_eq_fo_dep :: ESMGUConstraintsU t pd fn v sov uv => TermDependant t fn v sov uv -> TermDependant t fn v sov uv -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) [ESUnifDGOp s t pd fn v sov uv]
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

as_esu_vertical_align :: ESMGUConstraintsU t pd fn v sov uv => RESUnifVDGraph t pd fn v sov uv -> AnswerSet (RESUnifVDGraph t pd fn v sov uv) (UnifSysSolution fn sov)
as_esu_vertical_align resuvdg = ImplicitAS (getStateTSTESUnifVDGraphState esu_vertical_align resuvdg)

esu_vertical_align :: ESMGUConstraintsU t pd fn v sov uv => StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) ()
esu_vertical_align = (StateT (\esuvdg -> runStateT (runStateTOps (esu_vertical_align_ops esuvdg)) esuvdg)) >> pass

esu_vertical_align_ops :: ESMGUConstraintsU t pd fn v sov uv => ESUnifVDGraph s t pd fn v sov uv -> [ESUnifDGOp s t pd fn v sov uv]
esu_vertical_align_ops esuvdg = Prelude.map (ESUVAlign . directEqDGFoId . dgid . fromJust) (Prelude.filter isJust ((eqdgraph (esunifdgraph esuvdg)) ^. lens_fonodes))

esu_vertical_align_fot :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelFoId s t fn v sov uv -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) [ESUnifDGOp s t pd fn v sov uv]
esu_vertical_align_fot fot = do
	{
		mb_rtd <- mzoom lens_esunifdgraph_dgraph (getSTRelativeEqDGFoCoId fot);
		if (isNothing mb_rtd) then (return []) else do
		{		
			let {rtd = fromJustErr "This should never happen. esu_vertical_align_fot" mb_rtd};
			if (not (is_tdunif rtd)) then (return []) else do
			{
				let {(TDUnif uv intd) = rtd; intd_id = relbwEqDGFoId intd};
				exist <- checkVFoEdge intd_id fot;
				if exist then (return [])
				else do
				{
					prop_addVFoEdge intd_id fot uv
				}
			}	
		}
	}

as_esu_sozip :: ESMGUConstraintsU t pd fn v sov uv => RESUnifVDGraph t pd fn v sov uv -> AnswerSet (RESUnifVDGraph t pd fn v sov uv) (UnifSysSolution fn sov)
as_esu_sozip resuvdg = ImplicitAS (getStateTSTESUnifVDGraphState esu_sozip resuvdg)

esu_sozip :: ESMGUConstraintsU t pd fn v sov uv => StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) ()
esu_sozip = (StateT (\esuvdg -> runStateT (runStateTOps (esu_sozip_ops esuvdg)) esuvdg)) >> pass

esu_sozip_ops :: ESMGUConstraintsU t pd fn v sov uv => ESUnifVDGraph s t pd fn v sov uv -> [ESUnifDGOp s t pd fn v sov uv]
esu_sozip_ops esuvdg = Prelude.map (ESUSOZip . dgid . fromJust) (Prelude.filter isJust ((eqdgraph (esunifdgraph esuvdg)) ^. lens_soedges))

esu_sozip_soe :: ESMGUConstraintsU t pd fn v sov uv => Int -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) [ESUnifDGOp s t pd fn v sov uv]
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

as_esu_fozip :: ESMGUConstraintsU t pd fn v sov uv => RESUnifVDGraph t pd fn v sov uv -> AnswerSet (RESUnifVDGraph t pd fn v sov uv) (UnifSysSolution fn sov)
as_esu_fozip resuvdg = ImplicitAS (getStateTSTESUnifVDGraphState esu_fozip resuvdg)

esu_fozip :: ESMGUConstraintsU t pd fn v sov uv => StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) ()
esu_fozip = (StateT (\esuvdg -> runStateT (runStateTOps (esu_fozip_ops esuvdg)) esuvdg)) >> pass

esu_fozip_ops :: ESMGUConstraintsU t pd fn v sov uv => ESUnifVDGraph s t pd fn v sov uv -> [ESUnifDGOp s t pd fn v sov uv]
esu_fozip_ops esuvdg = Prelude.map (ESUFOZip . dgid. fromJust) (Prelude.filter isJust ((eqdgraph (esunifdgraph esuvdg)) ^. lens_foedges))

esu_fozip_foe :: ESMGUConstraintsU t pd fn v sov uv => Int -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) [ESUnifDGOp s t pd fn v sov uv]
esu_fozip_foe foe = do
	{
		-- First check that the edge still exists in the graph!
		eex <- mzoom lens_esunifdgraph_dgraph (checkEqDGFOEdge foe);
		if (not eex) then (return []) else do
		{
			eh <- mzoom lens_esunifdgraph_dgraph (eqDGFOEdge_head foe);
			ess <- mzoom lens_esunifdgraph_dgraph (eqDGFOEdge_sources foe);
			et <- mzoom lens_esunifdgraph_dgraph (eqDGFOEdge_target foe);
			es <- mzoom lens_esunifdgraph_dgraph (st_searchHEqDGFOEdges ess [] eh);
			let {che = (\pe -> do
			{
				pess <- eqDGFOEdge_sources pe;
				let {zipped = zip ess pess; sscs = Prelude.map (uncurry eqSTRelativeEqDGFoIds) zipped};
				Prelude.foldr (>>=&) (return (length ess == length pess)) sscs
			})};
			let {fe = (\pe -> do
			{
				ch <- che pe;
				if ch then do
				{
					pet <- eqDGFOEdge_target pe;
					-- We cannot merge here because that produces the removal of some edges, which we are traversing. We build a list of nodes to merge and merge them all in the end.
					--mergeEqDGSONodes et pet;				
					return (Just (pe,pet))
				}
				else return (Nothing)
			})};
			eres <- mzoom lens_esunifdgraph_dgraph (traverse fe es);
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
data FOTermDependantExp t fn v sov uv = FOTDExp (TermDependant t fn v sov uv) | FOEdgeExp (SOTerm fn sov) [FOTermDependantExp t fn v sov uv]
data SOTermDependantExp fn sov = SOTDExp (SOTerm fn sov) | SOEdgeExp (SOTerm fn sov) [SOTermDependantExp fn sov]

instance (Show (t (SOTerm fn sov) (UTerm (t (SOTerm fn sov)) v)), Show uv, Show v, Show fn, Show sov) => Show (FOTermDependantExp t fn v sov uv) where
	show (FOTDExp td) = show td
	show (FOEdgeExp fn ss) = (show fn) ++ "(" ++ (show_as_args (Prelude.map show ss)) ++ ")"

instance (Show fn, Show sov) => Show (SOTermDependantExp fn sov) where
	show (SOTDExp sotd) = show sotd
	show (SOEdgeExp fn ss) = (show fn) ++ "{" ++ (show_as_args (Prelude.map show ss)) ++ "}"

separate_sot_dependant_exp :: SOTerm fn sov -> SOTermDependantExp fn sov
separate_sot_dependant_exp (UTerm (SOF (CompF h []))) = SOTDExp h
separate_sot_dependant_exp (UTerm (SOF (CompF h ss))) = SOEdgeExp h (Prelude.map separate_sot_dependant_exp ss)
separate_sot_dependant_exp sot = SOTDExp sot


grab_fonode :: ESMGUConstraintsU t pd fn v sov uv => TermDependant t fn v sov uv -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) (ESUnifRelFoId s t fn v sov uv)
grab_fonode td = do
	{
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

grab_sonode :: ESMGUConstraintsU t pd fn v sov uv => SOTerm fn sov -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) (ESUnifRelSoId s t fn v sov uv)
grab_sonode sot = do
	{
		let {nsot = normalize sot};
		case nsot of
		{
			-- Base case => Variable
			UVar v -> do
			{
				return (relbwEqDGSoId nsot)
			};
			-- Base case => Function symbol
			UTerm (SOF (ConstF fn)) -> do
			{
				return (relbwEqDGSoId nsot)
			};
			-- Base case => Projection
			UTerm (SOF (Proj idx)) -> do
			{
				return (relbwEqDGSoId nsot)
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

case_foexp :: ESMGUConstraintsU t pd fn v sov uv => FOTermDependantExp t fn v sov uv -> ESUnifRelFoId s t fn v sov uv -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) (Maybe [(FOTermDependantExp t fn v sov uv,ESUnifRelFoId s t fn v sov uv)])
case_foexp (FOTDExp td) foid = mzoom lens_esunifdgraph_dgraph (do {r <- eqSTRelativeEqDGFoIds foid (relbwEqDGFoId td); if r then (return (Just [])) else (return Nothing)})
case_foexp (FOEdgeExp h []) foid = mzoom lens_esunifdgraph_dgraph (do {r <- eqSTRelativeEqDGFoIds foid (relbwEqDGFoId td); if r then (return (Just [])) else (return Nothing)}) where td = TDDirect (SOMetawrap (UTerm (build_term h [])))
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

match_foexp :: ESMGUConstraintsU t pd fn v sov uv => FOTermDependantExp t fn v sov uv -> ESUnifRelFoId s t fn v sov uv -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) Bool
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

case_soexp :: ESMGUConstraintsU t pd fn v sov uv => SOTermDependantExp fn sov -> ESUnifRelSoId s t fn v sov uv -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) (Maybe [(SOTermDependantExp fn sov,ESUnifRelSoId s t fn v sov uv)])
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

match_soexp :: ESMGUConstraintsU t pd fn v sov uv => SOTermDependantExp fn sov -> ESUnifRelSoId s t fn v sov uv -> StateT (ESUnifVDGraph s t pd fn v sov uv) (ST s) Bool
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
depgraph_prenormalize :: ESMGUConstraintsU t pd fn v sov uv => AnswerSet (RESUnifVDGraph t pd fn v sov uv) (UnifSysSolution fn sov) -> AnswerSet (RESUnifVDGraph t pd fn v sov uv) (UnifSysSolution fn sov)
--depgraph_prenormalize as = validate_all_consistency (as ?>>= VerticalAlign ?>>= VerticalCommuteEq ?>>= VerticalCommute ?>>= SOSimplifyProjections ?>>= SODump ?>>= SOZip ?>>= FOSimplifyProjections ?>>= FODump ?>>= FOZip)
depgraph_prenormalize as = validate_all_consistency (as ?>>= Prenormalize)

depgraph_seminormalize :: ESMGUConstraintsU t pd fn v sov uv => AnswerSet (RESUnifVDGraph t pd fn v sov uv) (UnifSysSolution fn sov) -> AnswerSet (RESUnifVDGraph t pd fn v sov uv) (UnifSysSolution fn sov)
--depgraph_seminormalize as = validate_all_consistency (as ?>>= VerticalAlign ?>>= VerticalCommuteEq ?>>= VerticalCommute ?>>= SOSimplifyProjections ?>>= SODump ?>>= SOZip ?>>= FOSimplifyProjections ?>>= FODump ?>>= FOZip ?>>= ZFactorize)
depgraph_seminormalize as = validate_all_consistency (as ?>>= Prenormalize ?>>= ZFactorize)

depgraph_quasinormalize :: ESMGUConstraintsU t pd fn v sov uv => AnswerSet (RESUnifVDGraph t pd fn v sov uv) (UnifSysSolution fn sov) -> AnswerSet (RESUnifVDGraph t pd fn v sov uv) (UnifSysSolution fn sov)
--depgraph_quasinormalize as = validate_all_consistency (as ?>>= VerticalAlign ?>>= VerticalCommuteEq ?>>= VerticalCommute ?>>= SOSimplifyProjections ?>>= SODump ?>>= SOZip ?>>= FOSimplifyProjections ?>>= FODump ?>>= FOZip ?>>= SFactorize)
depgraph_quasinormalize as = validate_all_consistency (as ?>>= Prenormalize ?>>= SFactorize)

depgraph_normalize :: ESMGUConstraintsU t pd fn v sov uv => AnswerSet (RESUnifVDGraph t pd fn v sov uv) (UnifSysSolution fn sov) -> AnswerSet (RESUnifVDGraph t pd fn v sov uv) (UnifSysSolution fn sov)
--depgraph_normalize as = validate_all_consistency (as ?>>= VerticalAlign ?>>= VerticalCommuteEq ?>>= VerticalCommute ?>>= SOSimplifyProjections ?>>= SODump ?>>= SOZip ?>>= FOSimplifyProjections ?>>= FODump ?>>= FOZip ?>>= MFactorize)
depgraph_normalize as = validate_all_consistency (as ?>>= Prenormalize ?>>= MFactorize)
