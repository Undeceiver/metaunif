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
import Safe (maximumMay)


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



-- TODO: The following big section is deprecated and will need to be deleted.

-- An existential second-order most general unifier is a single most general unifier describing a range of different Herbrand Universe instantiations. Non-deterministicness on the mgu itself is provided by AnswerSet itself.
-- It has two main elements:
--	- founif is the first-order unifier for the first-order variable assignations (to elements potentially containing second-order variables).
--	- soinst contains explicit instantiations for second-order variables (potentially to other second-order variables)
--	- Originally, we considered having soeqs contains flex-flex equations (both sides' head is a second-order variable) expressed implicitly. The main reason why we dropped this idea is that we are always going to have to evaluate these equations in every case, because there is no simple way to determine which variables (both first and second-order) each equation may affect at first glance (save for a few special cases).
-- This type is in essence stateful and so it is generally always used within a State monad, potentially combining it with other additional types that reflect partial instantiations.
-- Another important note is that the first-order unifier treats all of its second-order variables as either wildcards or things that can be developed into other wildcards. For obvious reasons, it notably does not affect the second-order instantiation based on equations in the first-order unifier. This kind of cross first-second order reasoning needs to happen before the solutions are introduced into the ESMGU. The fact that second-order variables may appear in the first-order unifier here is just a convenience tool to allow for more implicitness. The Implicit instance of this class therefore assumes this and will not give correct results if certain first-order equations in the unifier do affect the second-order instantiation in ways that were not accounted for.
data ESMGU t pd fn v sov = ESMGU {founif :: MaybeUnifier (t (SOTerm fn sov)) v (UFailure (t (SOTerm fn sov)) v), soinst :: MaybeUnifier (SOTermF fn) sov (UFailure (SOTermF fn) sov), sig :: SOSignature pd fn v sov}

-- Simple short-hand operations to define an ESMGU
-- They are just state because conceptually no checking and no simplification is done here. This is the laziest version there is of these functions.
emptyESMGU :: ESMGUConstraints t pd fn v sov => SOSignature pd fn v sov -> ESMGU t pd fn v sov
emptyESMGU sig = ESMGU (return ()) (return ()) sig

emptyNESMGU :: ESMGUConstraints t pd fn v sov => SOSignature pd fn v sov -> NESMGU t pd fn v sov
emptyNESMGU sig = NESMGU (emptyESMGU sig)

runESMGU :: ESMGUConstraints t pd fn v sov => SOSignature pd fn v sov -> JState (ESMGU t pd fn v sov) -> ESMGU t pd fn v sov
runESMGU sig st = runJState st (emptyESMGU sig)

runNESMGU :: ESMGUConstraints t pd fn v sov => SOSignature pd fn v sov -> JState (NESMGU t pd fn v sov) -> NESMGU t pd fn v sov
runNESMGU sig st = runJState st (emptyNESMGU sig)

(>:=) :: ESMGUConstraints t pd fn v sov => SOMetawrap t fn v sov -> SOMetawrap t fn v sov -> JState (ESMGU t pd fn v sov)
t1 >:= t2 = jstate (assign_founif_esmgu t1 t2)
infix 4 >:=

assign_founif_esmgu :: ESMGUConstraints t pd fn v sov => SOMetawrap t fn v sov -> SOMetawrap t fn v sov -> (ESMGU t pd fn v sov -> ESMGU t pd fn v sov)
assign_founif_esmgu t1 t2 mgu = ESMGU (u >> ((fromSOMetawrap t1) =.= (fromSOMetawrap t2))) (soinst mgu) (sig mgu) where u = founif mgu

(>::=) :: ESMGUConstraints t pd fn v sov => SOTerm fn sov -> SOTerm fn sov -> JState (ESMGU t pd fn v sov)
t1 >::= t2 = jstate (assign_soinst_esmgu t1 t2)
infix 4 >::=

assign_soinst_esmgu :: ESMGUConstraints t pd fn v sov => SOTerm fn sov -> SOTerm fn sov -> (ESMGU t pd fn v sov -> ESMGU t pd fn v sov)
assign_soinst_esmgu t1 t2 mgu = ESMGU (founif mgu) (sou >> (t1 =.= t2)) (sig mgu) where sou = soinst mgu

-- An existential second-order mgu is in normal form if every second-order variable that appears on the instantiation of another second-order variable is totally free (is a wildcard). That is, it does not have an instantiation itself.
-- We use a newtype to distinguish the normal form from the non-normal form, because it is very important for correctness of the algorithm.
newtype NESMGU t pd fn v sov = NESMGU {fromNESMGU :: ESMGU t pd fn v sov }
nfounif :: NESMGU t pd fn v sov -> MaybeUnifier (t (SOTerm fn sov)) v (UFailure (t (SOTerm fn sov)) v)
nfounif = founif . fromNESMGU

nsoinst :: NESMGU t pd fn v sov -> MaybeUnifier (SOTermF fn) sov (UFailure (SOTermF fn) sov)
nsoinst = soinst . fromNESMGU

nsig :: NESMGU t pd fn v sov -> SOSignature pd fn v sov
nsig = sig . fromNESMGU

-- Displaying an ESMGU. First, it depends on the signature. Second, it affects the state of the NESMGU.
do_show_esmgu :: ESMGUConstraints t pd fn v sov => SOSignature pd fn v sov -> ESMGU t pd fn v sov -> String
do_show_esmgu sig mgu = fst (runState (show_esmgu sig) mgu)

do_show_nesmgu :: ESMGUConstraints t pd fn v sov => SOSignature pd fn v sov -> NESMGU t pd fn v sov -> String
do_show_nesmgu sig mgu = do_show_esmgu sig (fromNESMGU mgu)

show_esmgu :: ESMGUConstraints t pd fn v sov => SOSignature pd fn v sov -> State (ESMGU t pd fn v sov) String
show_esmgu sig = (\rr -> return ("\nFirst-order variables:\n\n" ++ rr)) =<< (Prelude.foldr (\nst -> \pst -> pst >>= (\pt -> nst >>= (\nt -> return (nt++pt)))) ((\rr -> return ("\nSecond-order variables:\n\n" ++ rr)) =<< (Prelude.foldr (\nst -> \pst -> pst >>= (\pt -> nst >>= (\nt -> return (nt++pt)))) (return "") (st_show_sov <$> (sovars sig)))) (st_show_var <$> (fovars sig))) where st_show_var = (\v -> state (show_esmgu_var_f v)); st_show_sov = (\v -> state (show_esmgu_sov_f sig v))

show_esmgu_var_f :: ESMGUConstraints t pd fn v sov => v -> (ESMGU t pd fn v sov -> (String,ESMGU t pd fn v sov))
show_esmgu_var_f v mgu = if (isNothing mb_r) then ("Occurs check!\n",rst) else (((show v) ++ " -> " ++ (show (fromJust mb_r)) ++ "\n"),rst) where mb_r = ((founif mgu) $= (UVar v)); rst = runJState ((SOMetawrap (UVar v)) >:= (SOMetawrap (fromJust mb_r))) mgu

show_esmgu_sov_f :: ESMGUConstraints t pd fn v sov => SOSignature pd fn v sov -> sov -> (ESMGU t pd fn v sov -> (String,ESMGU t pd fn v sov))
show_esmgu_sov_f sig sov mgu = if (isNothing mb_r) then ("Occurs check!\n",rst) else (((show sov) ++ " -> " ++ (show (fromJust mb_r)) ++ "\n"),rst) where mb_r = (apply_somvunif sig (soinst mgu) (UVar sov)); rst = runJState ((UVar sov) >::= (fromJust mb_r)) mgu

-- Lenses for ESMGUs and their normal versions
lens_founif :: Lens' (ESMGU t pd fn v sov) (MaybeUnifier (t (SOTerm fn sov)) v (UFailure (t (SOTerm fn sov)) v))
lens_founif = lens founif (\prev -> \new -> ESMGU new (soinst prev) (sig prev))

lens_soinst :: Lens' (ESMGU t pd fn v sov) (MaybeUnifier (SOTermF fn) sov (UFailure (SOTermF fn) sov))
lens_soinst = lens soinst (\prev -> \new -> ESMGU (founif prev) new (sig prev))

lens_sig :: Lens' (ESMGU t pd fn v sov) (SOSignature pd fn v sov)
lens_sig = lens sig (\prev -> \new -> ESMGU (founif prev) (soinst prev) new)

lens_fromNESMGU :: Lens' (NESMGU t pd fn v sov) (ESMGU t pd fn v sov)
lens_fromNESMGU = lens fromNESMGU (\prev -> \new -> NESMGU new)

lens_nfounif :: Lens' (NESMGU t pd fn v sov) (MaybeUnifier (t (SOTerm fn sov)) v (UFailure (t (SOTerm fn sov)) v))
lens_nfounif = lens_fromNESMGU . lens_founif

lens_nsoinst :: Lens' (NESMGU t pd fn v sov) (MaybeUnifier (SOTermF fn) sov (UFailure (SOTermF fn) sov))
lens_nsoinst = lens_fromNESMGU . lens_soinst

lens_nsig :: Lens' (NESMGU t pd fn v sov) (SOSignature pd fn v sov)
lens_nsig = lens_fromNESMGU . lens_sig

-- State transforming specific functions for ESMGU. We work directly on normal ones. While we lose normality in many cases, to be able to use the State monad adequately, we restore normality afterwards in all cases. This may be a potential source of inefficiency, so keep an eye out.
instance (Bifunctor t, Eq sov) => Substitutable (UTerm (t (SOTerm fn sov)) v) sov (SOTerm fn sov) where
	subst _ _ (UVar v) = UVar v
	subst sov sot (UTerm t) = UTerm (bimap (subst sov sot) (subst sov sot) t)

instance (Bifunctor t, Eq sov) => Substitutable (SOMetawrap t fn v sov) sov (SOTerm fn sov) where
	subst sov sot = SOMetawrap . (subst sov sot) . fromSOMetawrap

instance (Eq sov) => Mappable sov (GroundSOT fn) (SOTerm fn sov) (GroundSOT fn) where
	anymap f (UVar v) = f v
	anymap f (UTerm (SOF (ConstF h))) = Fix (SOF (ConstF h))
	anymap f (UTerm (SOF (Proj idx))) = Fix (SOF (Proj idx))
	anymap f (UTerm (SOF (CompF h sargs))) = Fix (SOF (CompF (anymap f h) (fmap (anymap f) sargs)))

instance (Bifunctor t, Eq sov) => Mappable sov (GroundSOT fn) (UTerm (t (SOTerm fn sov)) v) (UTerm (t (GroundSOT fn)) v) where
	anymap f (UVar v) = UVar v
	anymap f (UTerm t) = UTerm (bimap (anymap f) (anymap f) t)


find_sovars :: (SimpleTerm t, Eq sov) => UTerm (t (SOTerm fn sov)) v -> [sov]
find_sovars (UVar _) = []
find_sovars (UTerm t) = nub ((find_vars f) ++ (foldMap find_sovars ts)) where (f,ts) = unbuild_term t

-- Note that when no match occurs we return False, but we may return the unmodified MGU. Conceptually, we should (and sometimes do) replace the MGU with a "no MGU exists" representation, but the user of these functions must interpret the failed match in that way.
(>!:=) :: ESMGUConstraints t pd fn v sov => SOMetawrap t fn v sov -> SOMetawrap t fn v sov -> State (NESMGU t pd fn v sov) Bool
(>!:=) = st_match_with_sov_wildcards_fo
infix 4 >!:=

(>!::=) :: ESMGUConstraints t pd fn v sov => SOTerm fn sov -> SOTerm fn sov -> State (NESMGU t pd fn v sov) Bool
(>!::=) = st_match_with_sov_wildcards_so
infix 4 >!::=

st_match_with_sov_wildcards_fo :: ESMGUConstraints t pd fn v sov => SOMetawrap t fn v sov -> SOMetawrap t fn v sov -> State (NESMGU t pd fn v sov) Bool
st_match_with_sov_wildcards_fo t1 t2 = state (match_with_sov_wildcards_fo t1 t2)

match_with_sov_wildcards_fo :: ESMGUConstraints t pd fn v sov => SOMetawrap t fn v sov -> SOMetawrap t fn v sov -> (NESMGU t pd fn v sov -> (Bool,NESMGU t pd fn v sov))
match_with_sov_wildcards_fo t1 t2 mgu = match_with_sov_wildcards_fo_norm (normalize t1) (normalize t2) mgu

st_match_with_sov_wildcards_fo_norm :: ESMGUConstraints t pd fn v sov => SOMetawrap t fn v sov -> SOMetawrap t fn v sov -> State (NESMGU t pd fn v sov) Bool
st_match_with_sov_wildcards_fo_norm t1 t2 = state (match_with_sov_wildcards_fo_norm t1 t2)

-- When this function is called, the bindings in the unifier must have been applied, so that the second-order wildcards are all directly observable. However, the function itself may modify the unifier further.
match_with_sov_wildcards_fo_norm :: ESMGUConstraints t pd fn v sov => SOMetawrap t fn v sov -> SOMetawrap t fn v sov -> (NESMGU t pd fn v sov -> (Bool,NESMGU t pd fn v sov))
match_with_sov_wildcards_fo_norm (SOMetawrap (UVar v)) t2 mgu = if (isNothing nmgu) then (False,mgu) else (True,rnmgu) where u = nfounif mgu; soinst = nsoinst mgu; rfounif = u >> ((UVar v) =.= (fromSOMetawrap t2)); rmgu = ESMGU rfounif soinst (nsig mgu); nmgu = normalize_esmgu rmgu; rnmgu = fromJust nmgu
match_with_sov_wildcards_fo_norm t1 (SOMetawrap (UVar v)) mgu = match_with_sov_wildcards_fo_norm (SOMetawrap (UVar v)) t1 mgu
match_with_sov_wildcards_fo_norm (SOMetawrap (UTerm t1)) (SOMetawrap (UTerm t2)) mgu = if direct_res then (direct_res,direct_st) else (match_with_sov_wildcards_fo_norm_proj f1 f2 mws1 mws2 mgu) where (f1,ts1) = unbuild_term t1; (f2,ts2) = unbuild_term t2; mws1 = SOMetawrap <$> ts1; mws2 = SOMetawrap <$> ts2; (direct_res,direct_st) = runState (Data.List.foldr (\pair -> \prev -> prev >>=& (uncurry st_match_with_sov_wildcards_fo_norm pair)) (st_match_with_sov_wildcards_so f1 f2) (zip mws1 mws2)) mgu
match_with_sov_wildcards_fo_norm _ _ mgu = (False,mgu)

match_with_sov_wildcards_fo_norm_proj :: ESMGUConstraints t pd fn v sov => SOTerm fn sov -> SOTerm fn sov -> [SOMetawrap t fn v sov] -> [SOMetawrap t fn v sov] -> (NESMGU t pd fn v sov -> (Bool,NESMGU t pd fn v sov))
match_with_sov_wildcards_fo_norm_proj (UVar v) t2 mws1 mws2 mgu = match_with_sov_wildcards_fo_norm_doproj v mws1 (SOMetawrap (UTerm (build_term t2 (fromSOMetawrap <$> mws2)))) (arity v) mgu
match_with_sov_wildcards_fo_norm_proj t1 (UVar v) mws1 mws2 mgu = match_with_sov_wildcards_fo_norm_proj (UVar v) t1 mws2 mws1 mgu
-- This is only for matching variables with projections, so unless it is composites, they won't match through this path. But because the SOMetawrap's were normalized, the head may not be composites.
-- We specifically match against constant heads so that we get flagged up the non-exhaustive pattern matching if there is something wrong.
match_with_sov_wildcards_fo_norm_proj (UTerm (SOF (ConstF f1))) (UTerm (SOF (ConstF f2))) mws1 mws2 mgu = (False,mgu)

match_with_sov_wildcards_fo_norm_doproj :: forall t pd fn v sov. ESMGUConstraints t pd fn v sov => sov -> [SOMetawrap t fn v sov] -> SOMetawrap t fn v sov -> Int -> (NESMGU t pd fn v sov -> (Bool,NESMGU t pd fn v sov))
match_with_sov_wildcards_fo_norm_doproj v mws1 rmw 0 mgu = (False,mgu)
match_with_sov_wildcards_fo_norm_doproj v mws1 rmw idx mgu = if ((isNothing nmgu) || (not rec_res)) then (match_with_sov_wildcards_fo_norm_doproj v mws1 rmw (idx - 1) mgu) else (rec_res,rec_st) where u = nfounif mgu; soinst = nsoinst mgu; rsoinst = soinst >> ((UVar v) =.= (UTerm (SOF (Proj (idx - 1))))); rmgu = ESMGU u rsoinst (nsig mgu); nmgu = normalize_esmgu rmgu; rnmgu = fromJust nmgu; (rec_res,rec_st) = match_with_sov_wildcards_fo_norm (mws1 !! (idx - 1)) rmw rnmgu

st_match_with_sov_wildcards_so :: ESMGUConstraints t pd fn v sov => SOTerm fn sov -> SOTerm fn sov -> State (NESMGU t pd fn v sov) Bool
st_match_with_sov_wildcards_so t1 t2 = state (match_with_sov_wildcards_so t1 t2)

match_with_sov_wildcards_so :: ESMGUConstraints t pd fn v sov => SOTerm fn sov -> SOTerm fn sov -> (NESMGU t pd fn v sov -> (Bool,NESMGU t pd fn v sov))
match_with_sov_wildcards_so t1 t2 mgu = match_with_sov_wildcards_so_norm (normalize t1) (normalize t2) mgu

st_match_with_sov_wildcards_so_norm :: ESMGUConstraints t pd fn v sov => SOTerm fn sov -> SOTerm fn sov -> State (NESMGU t pd fn v sov) Bool
st_match_with_sov_wildcards_so_norm t1 t2 = state (match_with_sov_wildcards_so_norm t1 t2)

match_with_sov_wildcards_so_norm :: ESMGUConstraints t pd fn v sov => SOTerm fn sov -> SOTerm fn sov -> (NESMGU t pd fn v sov -> (Bool,NESMGU t pd fn v sov))
match_with_sov_wildcards_so_norm (UVar v) t2 mgu = if ((arity v) < (arity t2)) || (isNothing nmgu) then (False,mgu) else (True,rnmgu) where u = nfounif mgu; soinst = nsoinst mgu; rsoinst = soinst >> ((UVar v) =.= t2); rmgu = ESMGU u rsoinst (nsig mgu); nmgu = normalize_esmgu rmgu; rnmgu = fromJust nmgu
match_with_sov_wildcards_so_norm t1 (UVar v) mgu = match_with_sov_wildcards_so_norm (UVar v) t1 mgu
match_with_sov_wildcards_so_norm (UTerm (SOF (ConstF f1))) (UTerm (SOF (ConstF f2))) mgu | f1 == f2 = (True,mgu)
match_with_sov_wildcards_so_norm (UTerm (SOF (Proj i))) (UTerm (SOF (Proj j))) mgu | i == j = (True,mgu)
match_with_sov_wildcards_so_norm (UTerm (SOF (CompF f1 sfs1))) (UTerm (SOF (CompF f2 sfs2))) mgu = runState (Data.List.foldr (\pair -> \prev -> prev >>=& (uncurry st_match_with_sov_wildcards_so_norm pair)) (st_match_with_sov_wildcards_so_norm f1 f2) (zip sfs1 sfs2)) mgu
match_with_sov_wildcards_so_norm _ _ mgu = (False,mgu)




type ESMGUConstraints t pd fn v sov = (Ord sov, SimpleTerm t, Eq fn, HasArity fn, HasArity sov, ChangeArity sov, Functor (t (SOTerm fn sov)), Functor (t fn), Bifunctor t, Traversable (t (GroundSOT fn)), Unifiable (t (SOTerm fn sov)), Variabilizable v, Variable v, Variabilizable sov, Variable sov, Ord v, Functor (t (GroundSOT fn)), Eq (t fn (Fix (t fn))), Show sov, Show fn, Show v, Show (t (SOTerm fn sov) (UTerm (t (SOTerm fn sov)) v)), Show (t (GroundSOT fn) (UTerm (t (GroundSOT fn)) v)), Ord fn, Ord (t (SOTerm fn sov) (UTerm (t (SOTerm fn sov)) v)))
type SOFESMGUConstraints fn sov = (Ord sov, Eq fn, HasArity fn, HasArity sov)


-- NOTE: Should change the exception to DUFailure when I add atoms. It should be fairly simple by using with_lowfailure.
instance ESMGUConstraints t pd fn v sov => Normalizable (AnswerSet (ESMGU t pd fn v sov) (UnifSolution t fn v sov)) (AnswerSet (NESMGU t pd fn v sov) (UnifSolution t fn v sov)) where
	normalize (SingleAS sol) = SingleAS sol
	normalize (ExplicitAS e) = ExplicitAS (normalize <$> e)
	normalize (ImplicitAS mgu) = if (isNothing nmgu) then (ExplicitAS EnumProc.Empty) else (ImplicitAS (fromJust nmgu)) where nmgu = normalize_esmgu mgu
	inject_normal = bimap_as fromNESMGU id

normalize_esmgu :: ESMGUConstraints t pd fn v sov => ESMGU t pd fn v sov -> Maybe (NESMGU t pd fn v sov)
normalize_esmgu mgu = if ((isNothing mb_nsoinst) || (isNothing mb_nfounif)) then Nothing else (Just (NESMGU (ESMGU nfounif nsoinst (sig mgu)))) where mb_nsoinst = normalize_soinst (sig mgu) (soinst mgu); nsoinst = fromJust mb_nsoinst; mb_nfounif = normalize_founif (sig mgu) (founif mgu); nfounif = fromJust mb_nfounif

normalize_founif :: (Unifiable (t (SOTerm fn sov)), Variabilizable v, Variable v) => SOSignature pd fn v sov -> MaybeUnifier (t (SOTerm fn sov)) v (UFailure (t (SOTerm fn sov)) v) -> Maybe (MaybeUnifier (t (SOTerm fn sov)) v (UFailure (t (SOTerm fn sov)) v))
normalize_founif sig u = if r then (Just ru) else Nothing where (ru,r) = check_occurs (list_from_enum (fovars sig)) u

normalize_soinst :: (Eq fn, Variabilizable sov, Variable sov) => SOSignature pd fn v sov -> MaybeUnifier (SOTermF fn) sov (UFailure (SOTermF fn) sov) -> Maybe (MaybeUnifier (SOTermF fn) sov (UFailure (SOTermF fn) sov))
normalize_soinst sig soinst = if r then (Just ru) else Nothing where (ru,r) = check_occurs (list_from_enum (sovars sig)) soinst

-- We keep these here for now because they have not yet been uploaded to GitHub. But they should be gone, only to be kept for record just-in-case in the version control.
--normalize_soinst :: Ord sov => Map sov (SOTerm fn sov) -> Maybe (Map sov (SOTerm fn sov))
--normalize_soinst soinst = if occurs_check then Nothing else (Just (rebuild_soinst soinst top_sort)) where
--	vars = keys soinst;
--	full_vars = nub (vars ++ (concat ((find_vars . (soinst !)) <$> vars)));
--	deps = Data.List.map (\sov -> (sov, sov, find_vars (soinst ! sov))) full_vars;
--	(t_graph, nodeFromVertex, vertexFromKey) = graphFromEdges deps;
--	graph = transposeG t_graph;
--	occurs_check = not (acyclic graph);
--	top_sort = ((\(a,_,_) -> a) . nodeFromVertex) <$> (topSort graph)

--rebuild_soinst :: Ord sov => Map sov (SOTerm fn sov) -> [sov] -> Map sov (SOTerm fn sov)
--rebuild_soinst osoinst top_sort = rebuild_soinst_rec osoinst top_sort Data.Map.Strict.empty

--rebuild_soinst_rec :: Ord sov => Map sov (SOTerm fn sov) -> [sov] -> Map sov (SOTerm fn sov) -> Map sov (SOTerm fn sov)
--rebuild_soinst_rec _ [] rsoinst = rsoinst
--rebuild_soinst_rec osoinst (sov:sovs) rsoinst = rebuild_soinst_rec osoinst sovs (Data.Map.Strict.insert sov final_value rsoinst) where value = findWithDefault (UVar sov) sov osoinst; final_value = --dump_soinst rsoinst (find_vars value) value

dump_soinst :: (Eq fn, ChangeArity sov, Variabilizable sov, Variable sov, Substitutable t sov (SOTerm fn sov)) => SOSignature pd fn v sov -> MaybeUnifier (SOTermF fn) sov (UFailure (SOTermF fn) sov) -> [sov] -> t -> Maybe t
dump_soinst sig soinst vars value = Data.List.foldr (\osov -> \cval -> cval >>= (\rcval -> (\sovval -> subst osov sovval rcval) <$> (apply_somvunif sig soinst (UVar osov)))) (Just value) vars

instance ESMGUConstraints t pd fn v sov => Implicit (NESMGU t pd fn v sov) (UnifSolution t fn v sov) where
	checkImplicit mgu sol = fst (runState (rsosol >>=& rfosol) mgu) where rsosol = st_checkESMGUsosol_norm (nsig mgu) (sosol sol); rfosol = st_checkESMGUfosol_norm (nsig mgu) (fosol sol)
	enumImplicit mgu = undefined
	--enumImplicit mgu = raw <$> (fromProvenanceT (nesmgu_enumImplicit mgu))

nesmgu_enumImplicit :: ESMGUConstraints t pd fn v sov => NESMGU t pd fn v sov -> ProvenanceT CQRP EnumProc (UnifSolution t fn v sov)
nesmgu_enumImplicit mgu = ProvenanceT ((fst <$>) <$> (runcompprov esunif_search_heuristic (runStateT rfullsol mgu))) where rsosol = st_enumESMGUsosol_norm (nsig mgu); rfosol = st_enumESMGUfosol_norm (nsig mgu); rfullsol = rsosol >>= (\sosol -> rfosol >>= (\fosol -> return (UnifSolution fosol sosol)))

instance ESMGUConstraints t pd fn v sov => Implicit (ESMGU t pd fn v sov) (UnifSolution t fn v sov) where
	checkImplicit mgu sol = checkAS nmgu sol where nmgu = normalize (ImplicitAS mgu)
	enumImplicit mgu = enumAS nmgu where nmgu = normalize (ImplicitAS mgu)





st_checkESMGUfosol_norm :: ESMGUConstraints t pd fn v sov => SOSignature pd fn v sov -> Map v (GroundT t fn) -> State (NESMGU t pd fn v sov) Bool
st_checkESMGUfosol_norm sig m = foldMapBool traversal_assocs (uncurry (st_checkESMGUfovar_norm sig)) m

st_checkESMGUfovar_norm :: ESMGUConstraints t pd fn v sov => SOSignature pd fn v sov -> v -> GroundT t fn -> State (NESMGU t pd fn v sov) Bool
st_checkESMGUfovar_norm sig v t = state (checkESMGUfovar_norm sig v t)

checkESMGUfovar_norm :: ESMGUConstraints t pd fn v sov => SOSignature pd fn v sov -> v -> GroundT t fn -> (NESMGU t pd fn v sov -> (Bool,NESMGU t pd fn v sov))
checkESMGUfovar_norm sig v t mgu = runState ((return (isJust rtv)) >>=& (st_match_with_sov_wildcards_fo (SOMetawrap (fromJust rtv)) tt)) mgu where u = nfounif mgu; soinst = nsoinst mgu; tt = somw (inject_groundt t); tv = u $= (UVar v); rtv = tv >>= (\ptv -> dump_soinst sig soinst (find_sovars ptv) ptv)

st_checkESMGUsosol_norm :: ESMGUConstraints t pd fn v sov => SOSignature pd fn v sov -> Map sov (GroundSOT fn) -> State (NESMGU t pd fn v sov) Bool
st_checkESMGUsosol_norm sig m = foldMapBool traversal_assocs (uncurry (st_checkESMGUsovar_norm sig)) m

st_checkESMGUsovar_norm :: ESMGUConstraints t pd fn v sov => SOSignature pd fn v sov -> sov -> GroundSOT fn -> State (NESMGU t pd fn v sov) Bool
st_checkESMGUsovar_norm sig sov sot = state (checkESMGUsovar_norm sig sov sot)

checkESMGUsovar_norm :: ESMGUConstraints t pd fn v sov => SOSignature pd fn v sov -> sov -> GroundSOT fn -> (NESMGU t pd fn v sov -> (Bool,NESMGU t pd fn v sov))
checkESMGUsovar_norm sig sov sot mgu = runState ((return (isJust mb_sotv)) >>=& (st_match_with_sov_wildcards_so sott (fromJust mb_sotv))) mgu where soinst = nsoinst mgu; sott = inject_groundsot sot; mb_sotv = apply_somvunif sig soinst (UVar sov)


st_doenumESMGUsosol_norm :: ESMGUConstraints t pd fn v sov => SOSignature pd fn v sov -> StateT (NESMGU t pd fn v sov) (ProvenanceT CQRP EnumProc) (Map sov (GroundSOT fn))
st_doenumESMGUsosol_norm sig = hoist (ProvenanceT . (runcompprov esunif_search_heuristic)) (st_enumESMGUsosol_norm sig)

st_enumESMGUsosol_norm :: ESMGUConstraints t pd fn v sov => SOSignature pd fn v sov -> StateT (NESMGU t pd fn v sov) (ProvComputation CQRP) (Map sov (GroundSOT fn))
st_enumESMGUsosol_norm sig = st_enumESMGUsosol_norm_sovars sig (sovars sig)

st_enumESMGUsosol_norm_sovars :: ESMGUConstraints t pd fn v sov => SOSignature pd fn v sov -> EnumProc sov -> StateT (NESMGU t pd fn v sov) (ProvComputation CQRP) (Map sov (GroundSOT fn))
-- We use a single entry with an empty map as base case. It semantically makes more sense, but more importantly, it helps recursion work better.
st_enumESMGUsosol_norm_sovars sig EnumProc.Empty = lift (compprov (CQRPText "Enumerating second-order variables. Base case.") Data.Map.Strict.empty)
st_enumESMGUsosol_norm_sovars sig Halt = lift (algprov_halt (CQRPText "Halting enumeration of second-order variables."))
st_enumESMGUsosol_norm_sovars sig (Error str) = lift (algprov_error (CQRPText "Error found in the source enumeration of second-order variables.") str)
st_enumESMGUsosol_norm_sovars sig (Continue x) = hoist (algprov_continue (CQRPText "Step in enumeration of second-order variables.")) (st_enumESMGUsosol_norm_sovars sig x)
st_enumESMGUsosol_norm_sovars sig (Produce sov sovs) = firstvar >>= (\gsot -> Data.Map.Strict.insert sov gsot <$> rest) where firstvar = (st_enumESMGUsosol_norm_sov sig) .:&. (lift (compprov (CQRPText ("Next second-order variable in the enumeration is " ++ (show sov))) sov)); rest = st_enumESMGUsosol_norm_sovars sig sovs

st_enumESMGUsosol_norm_sov :: forall t pd fn v sov. ESMGUConstraints t pd fn v sov => SOSignature pd fn v sov -> StateT (NESMGU t pd fn v sov) (ProvAlgorithm CQRP sov) (GroundSOT fn)
st_enumESMGUsosol_norm_sov sig = ts .:&. posunif
	where
		posunif = StateT (\mgu -> algfilterprov_prov (\sov -> filter_enumESMGUsosol_norm_sov sig sov mgu $>: (CQRPText ("Applying unifier to second-order variable " ++ (show sov))))) :: StateT (NESMGU t pd fn v sov) (ProvAlgorithm CQRP sov) (SOTerm fn sov);
		ts = StateT (\mgu -> forkprov_prov (\t -> fork_enumESMGUsosol_norm_sotv sig t mgu $>: (CQRPText ("Enumerating wildcard instantiations for second-order term " ++ (show t))))) :: StateT (NESMGU t pd fn v sov) (ProvAlgorithm CQRP (SOTerm fn sov)) (GroundSOT fn)

filter_enumESMGUsosol_norm_sov :: ESMGUConstraints t pd fn v sov => SOSignature pd fn v sov -> sov -> (NESMGU t pd fn v sov -> Maybe (SOTerm fn sov,NESMGU t pd fn v sov))
filter_enumESMGUsosol_norm_sov sig sov mgu = if (isNothing mb_sotv) then Nothing else Just (fromJust mb_sotv,mgu) where soinst = nsoinst mgu; mb_sotv = apply_somvunif sig soinst (UVar sov)

fork_enumESMGUsosol_norm_sotv :: ESMGUConstraints t pd fn v sov => SOSignature pd fn v sov -> SOTerm fn sov -> (NESMGU t pd fn v sov -> EnumProc (GroundSOT fn,NESMGU t pd fn v sov))
fork_enumESMGUsosol_norm_sotv sig (UVar sov) mgu = efilter_mb ((\gsot -> enumESMGUsosol_norm_sotv_match sov gsot mgu) <$> (enum_fofuncs (arity sov) sig))
fork_enumESMGUsosol_norm_sotv sig (UTerm t) mgu = runStateT (Fix <$> (traverse (StateT . (fork_enumESMGUsosol_norm_sotv sig)) t)) mgu

enumESMGUsosol_norm_sotv_match :: ESMGUConstraints t pd fn v sov => sov -> GroundSOT fn -> (NESMGU t pd fn v sov -> Maybe (GroundSOT fn,NESMGU t pd fn v sov))
enumESMGUsosol_norm_sotv_match sov gsot mgu = if rchk then (Just (gsot,rmgu)) else Nothing where (rchk,rmgu) = match_with_sov_wildcards_so (UVar sov) (inject_groundsot gsot) mgu

st_doenumESMGUfosol_norm :: ESMGUConstraints t pd fn v sov => SOSignature pd fn v sov -> StateT (NESMGU t pd fn v sov) (ProvenanceT CQRP EnumProc) (Map v (GroundT t fn))
st_doenumESMGUfosol_norm sig = hoist (ProvenanceT . (runcompprov esunif_search_heuristic)) (st_enumESMGUfosol_norm sig)

st_enumESMGUfosol_norm :: ESMGUConstraints t pd fn v sov => SOSignature pd fn v sov -> StateT (NESMGU t pd fn v sov) (ProvComputation CQRP) (Map v (GroundT t fn))
st_enumESMGUfosol_norm sig = st_enumESMGUfosol_norm_vars sig (fovars sig)

st_enumESMGUfosol_norm_vars :: ESMGUConstraints t pd fn v sov => SOSignature pd fn v sov -> EnumProc v -> StateT (NESMGU t pd fn v sov) (ProvComputation CQRP) (Map v (GroundT t fn))
st_enumESMGUfosol_norm_vars sig EnumProc.Empty = lift (compprov (CQRPText "Enumerating first-order variables. Base case.") Data.Map.Strict.empty)
st_enumESMGUfosol_norm_vars sig Halt = lift (algprov_halt (CQRPText "Halting enumeration of first-order variables."))
st_enumESMGUfosol_norm_vars sig (Error str) = lift (algprov_error (CQRPText "Error found in the source enumeration of first-order variables.") str)
st_enumESMGUfosol_norm_vars sig (Continue x) = hoist (algprov_continue (CQRPText "Step in enumeration of first-order variables.")) (st_enumESMGUfosol_norm_vars sig x)
st_enumESMGUfosol_norm_vars sig (Produce v vs) = firstvar >>= (\gsot -> Data.Map.Strict.insert v gsot <$> rest) where firstvar = (st_enumESMGUfosol_norm_var sig) .:&. (lift (compprov (CQRPText ("Next first-order variable in the enumeration is " ++ (show v))) v)); rest = st_enumESMGUfosol_norm_vars sig vs

st_enumESMGUfosol_norm_var :: forall t pd fn v sov. ESMGUConstraints t pd fn v sov => SOSignature pd fn v sov -> StateT (NESMGU t pd fn v sov) (ProvAlgorithm CQRP v) (GroundT t fn)
st_enumESMGUfosol_norm_var sig = tvarenum .:&. sovarsenum .:&. soinstdump .:&. posunif
	where
		posunif = StateT (\mgu -> algfilterprov_prov (\v -> filter_enumESMGUfosol_norm_var sig v mgu $>: (CQRPText ("Applying unifier to first-order variable " ++ (show v))))) :: StateT (NESMGU t pd fn v sov) (ProvAlgorithm CQRP v) (UTerm (t (SOTerm fn sov)) v);
		soinstdump = StateT (\mgu -> algfilterprov_prov (\tv -> filter_enumESMGUfosol_norm_tvar_dumpsoinst sig tv mgu $>: (CQRPText ("Dumping the second-order instantiation on the term " ++ (show tv))))) :: StateT (NESMGU t pd fn v sov) (ProvAlgorithm CQRP (UTerm (t (SOTerm fn sov)) v)) (UTerm (t (SOTerm fn sov)) v);
		sovarsenum = enumESMGUfosol_norm_tvar_sovars sig :: StateT (NESMGU t pd fn v sov) (ProvAlgorithm CQRP (UTerm (t (SOTerm fn sov)) v)) (UTerm (t (GroundSOT fn)) v);
		tvarenum = StateT (\mgu -> withorderprov_prov mempty (\x -> \tv -> order_enumESMGUfosol_norm_tvar sig x tv mgu $>: (CQRPText ("Enumerating first-order variables in term " ++ (show tv))))) :: StateT (NESMGU t pd fn v sov) (ProvAlgorithm CQRP (UTerm (t (GroundSOT fn)) v)) (GroundT t fn)

filter_enumESMGUfosol_norm_var :: ESMGUConstraints t pd fn v sov => SOSignature pd fn v sov -> v -> (NESMGU t pd fn v sov -> Maybe (UTerm (t (SOTerm fn sov)) v,NESMGU t pd fn v sov))
filter_enumESMGUfosol_norm_var sig v mgu = if (isNothing mb_tv) then Nothing else Just (fromJust mb_tv,mgu) where founif = nfounif mgu; mb_tv = founif $= (UVar v)

filter_enumESMGUfosol_norm_tvar_dumpsoinst :: ESMGUConstraints t pd fn v sov => SOSignature pd fn v sov -> UTerm (t (SOTerm fn sov)) v -> (NESMGU t pd fn v sov -> Maybe (UTerm (t (SOTerm fn sov)) v,NESMGU t pd fn v sov))
filter_enumESMGUfosol_norm_tvar_dumpsoinst sig tv mgu = (,mgu) <$> (dump_soinst sig (nsoinst mgu) (find_sovars tv) tv)

enumESMGUfosol_norm_tvar_sovars :: forall t pd fn v sov. ESMGUConstraints t pd fn v sov => SOSignature pd fn v sov -> StateT (NESMGU t pd fn v sov) (ProvAlgorithm CQRP (UTerm (t (SOTerm fn sov)) v)) (UTerm (t (GroundSOT fn)) v)
enumESMGUfosol_norm_tvar_sovars sig = replace_all_vars
	where
		replace_var = StateT (\mgu -> forkprov_prov (\t -> fork_enumESMGUsosol_norm_sotv sig t mgu $>: (CQRPText ("Enumerating wildcard instantiations for second-order term " ++ (show t))))) :: StateT (NESMGU t pd fn v sov) (ProvAlgorithm CQRP (SOTerm fn sov)) (GroundSOT fn);
		replace_all_vars = st_algprov_traversal fntraversal replace_var :: StateT (NESMGU t pd fn v sov) (ProvAlgorithm CQRP (UTerm (t (SOTerm fn sov)) v)) (UTerm (t (GroundSOT fn)) v)
		


order_enumESMGUfosol_norm_tvar :: forall t pd fn v sov x. (ESMGUConstraints t pd fn v sov, ExecOrder x) => SOSignature pd fn v sov -> x -> UTerm (t (GroundSOT fn)) v -> (NESMGU t pd fn v sov -> EnumProc (GroundT t fn,NESMGU t pd fn v sov))
order_enumESMGUfosol_norm_tvar sig _ (UVar v) mgu = efilter_mb ((\gt -> enumESMGUfosol_norm_tvar_match v gt mgu) <$> (enum_foterms sig))
order_enumESMGUfosol_norm_tvar sig x (UTerm t) mgu = fixd
	where
		recalg = StateT (\mgu -> withorderprov mempty (\x -> \a -> order_enumESMGUfosol_norm_tvar sig x a mgu)) :: StateT (NESMGU t pd fn v sov) (ProvAlgorithm CQRP (UTerm (t (GroundSOT fn)) v)) (GroundT t fn);
		traversed = st_algprov_traverse recalg :: StateT (NESMGU t pd fn v sov) (ProvAlgorithm CQRP (t (GroundSOT fn) (UTerm (t (GroundSOT fn)) v))) (t (GroundSOT fn) (GroundT t fn));
		unstated = runStateT traversed mgu :: ProvAlgorithm CQRP (t (GroundSOT fn) (UTerm (t (GroundSOT fn)) v)) (t (GroundSOT fn) (GroundT t fn),NESMGU t pd fn v sov);
		run = runorderprov x unstated t :: EnumProc ((t (GroundSOT fn) (GroundT t fn),NESMGU t pd fn v sov) :- CQRP);
		unprovd = raw <$> run :: EnumProc (t (GroundSOT fn) (GroundT t fn),NESMGU t pd fn v sov);
		fixd = (\(r,s) -> (Fix (absorb_groundsot_into_groundt r),s)) <$> unprovd

enumESMGUfosol_norm_tvar_match :: ESMGUConstraints t pd fn v sov => v -> GroundT t fn -> (NESMGU t pd fn v sov -> Maybe (GroundT t fn,NESMGU t pd fn v sov))
enumESMGUfosol_norm_tvar_match v gt mgu = if rchk then (Just (gt,rmgu)) else Nothing where (rchk,rmgu) = match_with_sov_wildcards_fo (SOMetawrap (UVar v)) (somw . inject_groundt $ gt) mgu





-- A dependency graph is another implicit solution to a system of unification equations (an intermediate one)
-- instance Implicit **DEPENDENCY GRAPH** (UnifSysSolution t fn v sov uv) where

-- We work with a clear mapping between levels and unifier variables. This makes things a lot easier.
type ESMGUConstraintsU t pd fn v sov uv = (ESMGUConstraints t pd fn v sov, Show uv, Ord uv)

type ESUnifDGraph s t fn v sov uv = EqDGraph s (TermDependant t fn v sov uv) (SOTerm fn sov)
type ESUnifRelFoId s t fn v sov uv = EqDGRelFoId s (TermDependant t fn v sov uv) (SOTerm fn sov)
type ESUnifRelSoId s t fn v sov uv = EqDGRelSoId s (TermDependant t fn v sov uv) (SOTerm fn sov)
data ESUnifVFoEdge s t fn v sov uv = ESUnifVFoEdge {esunifvfoedge_source :: ESUnifRelFoId s t fn v sov uv, esunifvfoedge_target :: ESUnifRelFoId s t fn v sov uv}

eqUnifVFoEdge :: ESMGUConstraintsU t pd fn v sov uv => ESUnifVFoEdge s t fn v sov uv -> ESUnifVFoEdge s t fn v sov uv -> StateT (ESUnifVDGraph s t fn v sov uv) (ST s) Bool
eqUnifVFoEdge e1 e2 = (mzoom (lens_esunifdgraph_dgraph) (eqSTRelativeEqDGFoIds s1 s2)) >>= (\v1 -> if v1 then (mzoom (lens_esunifdgraph_dgraph) (eqSTRelativeEqDGFoIds t1 t2)) else (return False)) where s1 = esunifvfoedge_source e1; t1 = esunifvfoedge_target e1; s2 = esunifvfoedge_source e2; t2 = esunifvfoedge_target e2

-- The levels are assumed ordered and correctly indexed, so that 0-indexed level contains elements with no unifier variables, 1-indexed level contains elements with only the first unifier variable, and so on.
data ESUnifVDGraph s t fn v sov uv = ESUnifVDGraph {esunifdgraph :: ESUnifDGraph s t fn v sov uv, esunifdgraph_vfoedges :: [ESUnifVFoEdge s t fn v sov uv]}

lens_esunifdgraph_vfoedges :: Lens' (ESUnifVDGraph s t fn v sov uv) [ESUnifVFoEdge s t fn v sov uv]
lens_esunifdgraph_vfoedges f esudg = fmap (\rvfoes -> ESUnifVDGraph (esunifdgraph esudg) rvfoes) (f (esunifdgraph_vfoedges esudg))

lens_esunifdgraph_dgraph :: Lens' (ESUnifVDGraph s t fn v sov uv) (ESUnifDGraph s t fn v sov uv)
lens_esunifdgraph_dgraph f esudg = fmap (\rdgraph -> ESUnifVDGraph rdgraph (esunifdgraph_vfoedges esudg)) (f (esunifdgraph esudg))

emptyVDGraph :: ESUnifVDGraph s t fn v sov uv
emptyVDGraph = ESUnifVDGraph emptyEqDG []

show_esuvdg :: (ESMGUConstraintsU t pd fn v sov uv) => StateT (ESUnifVDGraph s t fn v sov uv) (ST s) String
show_esuvdg = do
	{
		esuvdg <- get;
		let {dgraph = show_eqdgraph (esunifdgraph esuvdg)};
		vedges <- show_esuvdg_vedges;
		return ("Horizonal:\n\n" ++ dgraph ++ "\n\nVertical:\n\n" ++ vedges ++ "\n\n")
	}

show_esuvdg_vedges :: (ESMGUConstraintsU t pd fn v sov uv) => StateT (ESUnifVDGraph s t fn v sov uv) (ST s) String
show_esuvdg_vedges = StateT (\vdg -> ((_2) ..~ (\dg -> ESUnifVDGraph dg (esunifdgraph_vfoedges vdg))) <$> (f_show_esuvdg_vedges (esunifdgraph vdg) (esunifdgraph_vfoedges vdg)))

f_show_esuvdg_vedges :: (ESMGUConstraintsU t pd fn v sov uv) => ESUnifDGraph s t fn v sov uv -> [ESUnifVFoEdge s t fn v sov uv] -> ST s (String,ESUnifDGraph s t fn v sov uv)
f_show_esuvdg_vedges dg [] = return ("",dg)
f_show_esuvdg_vedges dg (e:es) = do {(estr,dg2) <- f_show_esuvdg_vedge dg e; (esstr,dg3) <- f_show_esuvdg_vedges dg2 es; return (estr ++ "\n" ++ esstr,dg3)}

f_show_esuvdg_vedge :: (ESMGUConstraintsU t pd fn v sov uv) => ESUnifDGraph s t fn v sov uv -> ESUnifVFoEdge s t fn v sov uv -> ST s (String,ESUnifDGraph s t fn v sov uv)
f_show_esuvdg_vedge dg e = do {let {s = esunifvfoedge_source e; t = esunifvfoedge_target e}; (mb_sfot,dg2) <- runStateT (getSTRelativeEqDGFoCoId s) dg; (mb_tfot,dg3) <- runStateT (getSTRelativeEqDGFoCoId t) dg2; let {sstr = if (isNothing mb_sfot) then "()" else (show (fromJust mb_sfot)); tstr = if (isNothing mb_tfot) then "()" else (show (fromJust mb_tfot))}; return (sstr ++ " -> " ++ tstr,dg3)}

-- Dealing with vertical edges
-- The edge is added anyway. If it already existed, this is a mistake, but it should be dealt with at a higher level.
-- Note that we ensure that the nodes exist in the graph when doing this.
addVFoEdge :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelFoId s t fn v sov uv -> ESUnifRelFoId s t fn v sov uv -> StateT (ESUnifVDGraph s t fn v sov uv) (ST s) ()
addVFoEdge s t = mzoom lens_esunifdgraph_dgraph (do {mb_sfot <- getSTRelativeEqDGFoCoId s; mb_tfot <- getSTRelativeEqDGFoCoId t; if (isJust mb_sfot) then (newEqDGFONode (fromJustErr "addVFoEdge sfot" mb_sfot)) else pass; if (isJust mb_tfot) then (newEqDGFONode (fromJustErr "addVFoEdge tfot" mb_tfot)) else pass}) >> (StateT (f_addVFoEdge s t))

f_addVFoEdge :: ESUnifRelFoId s t fn v sov uv -> ESUnifRelFoId s t fn v sov uv -> (ESUnifVDGraph s t fn v sov uv -> ST s ((), ESUnifVDGraph s t fn v sov uv))
f_addVFoEdge s t esuvdg = return ((), lens_esunifdgraph_vfoedges ..~ ((ESUnifVFoEdge s t):) $ esuvdg)

-- When we delete, we delete all copies of that edge. There should only really be one, but you can never be safe enough.
deleteVFoEdge :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelFoId s t fn v sov uv -> ESUnifRelFoId s t fn v sov uv -> StateT (ESUnifVDGraph s t fn v sov uv) (ST s) ()
deleteVFoEdge s t = StateT (f_deleteVFoEdge s t)

f_deleteVFoEdge :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelFoId s t fn v sov uv -> ESUnifRelFoId s t fn v sov uv -> (ESUnifVDGraph s t fn v sov uv -> ST s ((),ESUnifVDGraph s t fn v sov uv))
f_deleteVFoEdge s t esudg = tocombine <$> (runStateT st_res esudg) where fe = ESUnifVFoEdge s t; es = esunifdgraph_vfoedges esudg; tofold = (\e -> \rstes -> rstes >>= (\res -> (\rb -> if rb then res else (e:res)) <$> (eqUnifVFoEdge e fe))); st_res = Prelude.foldr tofold (return []) es; tocombine = (\(rres,resudg) -> ((),lens_esunifdgraph_vfoedges .~ rres $ resudg))


-- Check if a vertical edge exists.
checkVFoEdge :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelFoId s t fn v sov uv -> ESUnifRelFoId s t fn v sov uv -> StateT (ESUnifVDGraph s t fn v sov uv) (ST s) Bool
checkVFoEdge s t = StateT (f_checkVFoEdge s t)

f_checkVFoEdge :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelFoId s t fn v sov uv -> ESUnifRelFoId s t fn v sov uv -> (ESUnifVDGraph s t fn v sov uv -> ST s (Bool,ESUnifVDGraph s t fn v sov uv))
f_checkVFoEdge s t esudg = runStateT st_rb esudg where fe = ESUnifVFoEdge s t; es = esunifdgraph_vfoedges esudg; tofold = (\e -> \rstb -> rstb >>= (\rb -> if rb then (return True) else (eqUnifVFoEdge e fe))); st_rb = Prelude.foldr tofold (return False) es

outVFoEdges :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelFoId s t fn v sov uv -> StateT (ESUnifVDGraph s t fn v sov uv) (ST s) [ESUnifVFoEdge s t fn v sov uv]
outVFoEdges s = StateT (f_outVFoEdges s)

f_outVFoEdges :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelFoId s t fn v sov uv -> (ESUnifVDGraph s t fn v sov uv -> ST s ([ESUnifVFoEdge s t fn v sov uv],ESUnifVDGraph s t fn v sov uv))
f_outVFoEdges s esudg = runStateT (monadfilter tofilter es) esudg where es = esunifdgraph_vfoedges esudg; tofilter = (\e -> mzoom lens_esunifdgraph_dgraph (eqSTRelativeEqDGFoIds (esunifvfoedge_source e) s))

inVFoEdges :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelFoId s t fn v sov uv -> StateT (ESUnifVDGraph s t fn v sov uv) (ST s) [ESUnifVFoEdge s t fn v sov uv]
inVFoEdges t = StateT (f_inVFoEdges t)

f_inVFoEdges :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelFoId s t fn v sov uv -> (ESUnifVDGraph s t fn v sov uv -> ST s ([ESUnifVFoEdge s t fn v sov uv],ESUnifVDGraph s t fn v sov uv))
f_inVFoEdges t esudg = runStateT (monadfilter tofilter es) esudg where es = esunifdgraph_vfoedges esudg; tofilter = (\e -> mzoom lens_esunifdgraph_dgraph (eqSTRelativeEqDGFoIds (esunifvfoedge_target e) t))


-- We assume and ensure that a vertical edge is always between two dependants only one unifier variable in difference
factorizeVFoEdge :: ESMGUConstraintsU t pd fn v sov uv => ESUnifVFoEdge s t fn v sov uv -> StateT (ESUnifVDGraph s t fn v sov uv) (ST s) uv
factorizeVFoEdge e = do
	{
		mb_tfot <- mzoom lens_esunifdgraph_dgraph (getSTRelativeEqDGFoCoId (esunifvfoedge_target e));
		let {tfot = fromJustErr "Found a vertical edge whose target has no elements!" mb_tfot};
		return (case tfot of {TDUnif uv _ -> uv})
	}

divideOverVFoEdge :: ESMGUConstraintsU t pd fn v sov uv => ESUnifVFoEdge s t fn v sov uv -> ESUnifRelFoId s t fn v sov uv -> StateT (ESUnifVDGraph s t fn v sov uv) (ST s) (ESUnifRelFoId s t fn v sov uv)
divideOverVFoEdge e sid = do {mb_std <- mzoom lens_esunifdgraph_dgraph (getSTRelativeEqDGFoCoId sid); uv <- factorizeVFoEdge e; let {std = fromJustErr "Trying to divide by a node with no elements!" mb_std}; return (relbwEqDGFoId (TDUnif uv std))}

-- Operation types for unification dependency graphs
-- We have two levels of operations.
-- The low level ones work directly on the graph itself and are for propagating changes until everything that needs to be done is done, in a relatively efficient manner. These are formalized with the Operable types.
-- The high level ones work on a graph with a normalization level and are for expressing things that we do when working with a dependency graph representation of a unification system. These are not formalized with the Operable types, and simply are a set of functions that can be used to navigate these normal types in different ways.

data ESUnifDGOp (s :: *) (t :: * -> * -> *) (fn :: *) (v :: *) (sov :: *) (uv :: *) = ESUVCommuteFo (ESUnifVFoEdge s t fn v sov uv) | ESUVAlign (ESUnifRelFoId s t fn v sov uv) | ESUSOZip Int | ESUFOZip Int | ESUFOSimpProj Int | ESUSOSimpProj Int | ESUFODump Int | ESUSODump Int

instance Eq (ESUnifDGOp s t fn v sov uv) where
	op1 == op2 = esunifdg_prio op1 == esunifdg_prio op2

instance Ord (ESUnifDGOp s t fn v sov uv) where
	op1 <= op2 | esunifdg_prio op1 < esunifdg_prio op2 = True
	op1 <= op2 | esunifdg_prio op2 < esunifdg_prio op1 = False
	-- Default case for operations with no further comparisons.
	op1 <= op2 = True

esunifdg_prio :: (ESUnifDGOp s t fn v sov uv) -> Int
esunifdg_prio (ESUVCommuteFo _) = 100
esunifdg_prio (ESUVAlign _) = 50
esunifdg_prio (ESUSOZip _) = 300
esunifdg_prio (ESUFOZip _) = 500
esunifdg_prio (ESUSOSimpProj _) = 800
esunifdg_prio (ESUFOSimpProj _) = 1000
esunifdg_prio (ESUSODump _) = 1300
esunifdg_prio (ESUFODump _) = 1500

instance ESMGUConstraintsU t pd fn v sov uv => StateTOperation (ST s) (ESUnifDGOp s t fn v sov uv) (ESUnifVDGraph s t fn v sov uv) where
	runStateTOp (ESUVCommuteFo foe) = esu_vertical_commute_fo_edge foe
	runStateTOp (ESUVAlign fot) = esu_vertical_align_fot fot
	runStateTOp (ESUSOZip soe) = esu_sozip_soe soe
	runStateTOp (ESUFOZip foe) = esu_fozip_foe foe
	runStateTOp (ESUSOSimpProj soe) = esu_so_simplify_proj_soe soe
	runStateTOp (ESUFOSimpProj foe) = esu_fo_simplify_proj_foe foe
	runStateTOp (ESUSODump soe) = esu_so_dump_soe soe
	runStateTOp (ESUFODump foe) = esu_fo_dump_foe foe

newtype RESUnifVDGraph t fn v sov uv = RESUnifVDGraph {fromRESUnifVDGraph :: forall s. ST s (ESUnifVDGraph s t fn v sov uv)}

instance Implicit (RESUnifVDGraph t fn v sov uv) (UnifSysSolution fn sov) where
	checkImplicit = undefined
	enumImplicit = undefined

-- TODO: Add the deterministic global operations here too.
data ESUnifGlobalOp = SOTConsistency | FOTConsistency | HeadAritySO | HeadArityFO | OccursCheckSO | OccursCheckFO deriving (Show,Eq,Ord)

instance Functional ESUnifGlobalOp (UnifSysSolution fn sov) (AnswerSet (RESUnifVDGraph t fn v sov uv) (UnifSysSolution fn sov)) where
	-- Not sure if this will remain correct, but I think it should.
	-- In principle, all global DG operations leave the set of solutions of the dependency graph unchanged. If that set happens to be a single solution, that is also the case.
	tofun _ us = SingleAS us

instance ESMGUConstraintsU t pd fn v sov uv => ImplicitF (RESUnifVDGraph t fn v sov uv) (UnifSysSolution fn sov) (RESUnifVDGraph t fn v sov uv) (UnifSysSolution fn sov) ESUnifGlobalOp where
	composeImplicit resuvdg SOTConsistency = validate_sot_consistency resuvdg
	composeImplicit resuvdg FOTConsistency = validate_fot_consistency resuvdg
	composeImplicit resuvdg HeadAritySO = validate_head_arity_so resuvdg
	composeImplicit resuvdg HeadArityFO = validate_head_arity_fo resuvdg
	composeImplicit resuvdg OccursCheckSO = validate_occurs_check_so resuvdg
	composeImplicit resuvdg OccursCheckFO = validate_occurs_check_fo resuvdg

-- Actions on the ESUnifVDGraph, enhanced with their propagation operations.
-- These include checking what has actually changed on the graph and what has not, to prevent excessive operations but more importantly to prevent looping.
prop_newEqDGFOEdge :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelSoId s t fn v sov uv -> [ESUnifRelFoId s t fn v sov uv] -> ESUnifRelFoId s t fn v sov uv -> StateT (ESUnifVDGraph s t fn v sov uv) (ST s) [ESUnifDGOp s t fn v sov uv]
prop_newEqDGFOEdge h ss t = do
	{
		let {result = []};
		-- This may create the head, source and target nodes!
		-- In particular, checking if nodes exist is whiffy because they are created on the go as part of the monadic operations. Instead, *and only for this particular operation*, whenever a node that previously did not exist may be created, we perform cascade operations from it anyway.
		result2 <- ((return result) >>=++ (justprop_newEqDGFONode t));

		result3 <- ((return result2) >>=++ (justprop_newEqDGSONode h));

		result4 <- ((return result3) >>=++ (concat <$> traverse justprop_newEqDGFONode ss));

		-- Check that the edge does not already exist.
		exist <- mzoom lens_esunifdgraph_dgraph (st_checkEqDGFOEdge h ss t);
		result5 <- if exist then (return []) else (do
		{			
			eid <- mzoom lens_esunifdgraph_dgraph (newEqDGFOEdge h ss t);
			(return result4) >>=++ (justprop_newEqDGFOEdge eid)
		});
		return result5
	}

prop_newEqDGSOEdge :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelSoId s t fn v sov uv -> [ESUnifRelSoId s t fn v sov uv] -> ESUnifRelSoId s t fn v sov uv -> StateT (ESUnifVDGraph s t fn v sov uv) (ST s) [ESUnifDGOp s t fn v sov uv]
prop_newEqDGSOEdge h ss t = do
	{
		let {result = []};
		-- This may create the head, source and target nodes!
		-- In particular, checking if nodes exist is whiffy because they are created on the go as part of the monadic operations. Instead, *and only for this particular operation*, whenever a node that previously did not exist may be created, we perform cascade operations from it anyway.
		result2 <- ((return result) >>=++ (justprop_newEqDGSONode t));

		result3 <- ((return result2) >>=++ (justprop_newEqDGSONode h));

		result4 <- ((return result3) >>=++ (concat <$> traverse justprop_newEqDGSONode ss));

		-- Check that the edge does not already exist.
		exist <- mzoom lens_esunifdgraph_dgraph (st_checkEqDGSOEdge h ss t);
		result5 <- if exist then (return []) else (do
		{			
			eid <- mzoom lens_esunifdgraph_dgraph (newEqDGSOEdge h ss t);
			(return result4) >>=++ (justprop_newEqDGSOEdge eid)
		});
		return result5
	}

prop_addVFoEdge :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelFoId s t fn v sov uv -> ESUnifRelFoId s t fn v sov uv -> StateT (ESUnifVDGraph s t fn v sov uv) (ST s) [ESUnifDGOp s t fn v sov uv]
prop_addVFoEdge s t = do
	{
		let {result = []};

		-- First, check that the source and the target have elements. If they don't, don't do anything!
		mb_sfot <- mzoom lens_esunifdgraph_dgraph (getSTRelativeEqDGFoCoId s);
		mb_tfot <- mzoom lens_esunifdgraph_dgraph (getSTRelativeEqDGFoCoId t);

		if ((isNothing mb_sfot) || (isNothing mb_tfot)) then (return []) else do
		{
			-- This may create the source and target nodes!
			result2 <- ((return result) >>=++ (justprop_newEqDGFONode s));

			result3 <- ((return result2) >>=++ (justprop_newEqDGFONode t));

			exist <- checkVFoEdge s t;
			if exist then (return []) else (do
			{
				addVFoEdge s t;
				(return result3) >>=++ (justprop_addVFoEdge s t);
			})
		}
	}

prop_mergeEqDGFONodes :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelFoId s t fn v sov uv -> ESUnifRelFoId s t fn v sov uv -> StateT (ESUnifVDGraph s t fn v sov uv) (ST s) [ESUnifDGOp s t fn v sov uv]
prop_mergeEqDGFONodes n1 n2 = do
	{
		let {result = []};

		-- This may create the nodes!
		result2 <- ((return result) >>=++ (justprop_newEqDGFONode n1));

		result3 <- ((return result2) >>=++ (justprop_newEqDGFONode n2));

		equal <- mzoom lens_esunifdgraph_dgraph (eqSTRelativeEqDGFoIds n1 n2);
		if equal then (return result3) else (do
		{
			mzoom lens_esunifdgraph_dgraph (mergeEqDGFONodes n1 n2);
			(return result3) >>=++ (justprop_mergeEqDGFONodes n1 n2);
		})
	}

prop_mergeEqDGSONodes :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelSoId s t fn v sov uv -> ESUnifRelSoId s t fn v sov uv -> StateT (ESUnifVDGraph s t fn v sov uv) (ST s) [ESUnifDGOp s t fn v sov uv]
prop_mergeEqDGSONodes n1 n2 = do
	{		
		let {result = []};

		-- This may create the nodes!
		result2 <- ((return result) >>=++ (justprop_newEqDGSONode n1));
		
		result3 <- ((return result2) >>=++ (justprop_newEqDGSONode n2));
		
		equal <- mzoom lens_esunifdgraph_dgraph (eqSTRelativeEqDGSoIds n1 n2);
		if equal then (return result3) else (do
		{
			mzoom lens_esunifdgraph_dgraph (mergeEqDGSONodes n1 n2);
			(return result3) >>=++ (justprop_mergeEqDGSONodes n1 n2);			
		})
	}

prop_deleteEqDGSOEdge :: ESMGUConstraintsU t pd fn v sov uv => Int -> StateT (ESUnifVDGraph s t fn v sov uv) (ST s) [ESUnifDGOp s t fn v sov uv]
prop_deleteEqDGSOEdge soe = do
	{
		-- Check that the edge still exists!
		eex <- mzoom lens_esunifdgraph_dgraph (checkEqDGSOEdge soe);
		if (not eex) then (return []) else do
		{
			mzoom lens_esunifdgraph_dgraph (deleteEqDGSOEdge soe);
			justprop_deleteEqDGSOEdge soe
		}
	}

prop_deleteEqDGFOEdge :: ESMGUConstraintsU t pd fn v sov uv => Int -> StateT (ESUnifVDGraph s t fn v sov uv) (ST s) [ESUnifDGOp s t fn v sov uv]
prop_deleteEqDGFOEdge foe = do
	{
		-- Check that the edge still exists!
		eex <- mzoom lens_esunifdgraph_dgraph (checkEqDGFOEdge foe);
		if (not eex) then (return []) else do
		{
			mzoom lens_esunifdgraph_dgraph (deleteEqDGFOEdge foe);
			justprop_deleteEqDGFOEdge foe
		}
	}

prop_newAnonEqDGFOEdge :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelSoId s t fn v sov uv -> [ESUnifRelFoId s t fn v sov uv] -> StateT (ESUnifVDGraph s t fn v sov uv) (ST s) (ESUnifRelFoId s t fn v sov uv,[ESUnifDGOp s t fn v sov uv])
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

prop_newAnonEqDGSOEdge :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelSoId s t fn v sov uv -> [ESUnifRelSoId s t fn v sov uv] -> StateT (ESUnifVDGraph s t fn v sov uv) (ST s) (ESUnifRelSoId s t fn v sov uv,[ESUnifDGOp s t fn v sov uv])
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

justprop_deleteEqDGFOEdge :: ESMGUConstraintsU t pd fn v sov uv => Int -> StateT (ESUnifVDGraph s t fn v sov uv) (ST s) [ESUnifDGOp s t fn v sov uv]
justprop_deleteEqDGFOEdge soe = return []

justprop_deleteEqDGSOEdge :: ESMGUConstraintsU t pd fn v sov uv => Int -> StateT (ESUnifVDGraph s t fn v sov uv) (ST s) [ESUnifDGOp s t fn v sov uv]
justprop_deleteEqDGSOEdge soe = return []

justprop_mergeEqDGSONodes :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelSoId s t fn v sov uv -> ESUnifRelSoId s t fn v sov uv -> StateT (ESUnifVDGraph s t fn v sov uv) (ST s) [ESUnifDGOp s t fn v sov uv]
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

justprop_mergeEqDGFONodes :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelFoId s t fn v sov uv -> ESUnifRelFoId s t fn v sov uv -> StateT (ESUnifVDGraph s t fn v sov uv) (ST s) [ESUnifDGOp s t fn v sov uv]
justprop_mergeEqDGFONodes n1 n2 = do
	{
		-- We assume the nodes have already been merged (i.e. they are equivalent).
		-- For any outgoing vertical edges of the resulting merged node, create a vertical commute instance, just in case.
		ves <- outVFoEdges n1;
		let {result = Prelude.map ESUVCommuteFo ves};

		-- Similarly, any outgoing horizontal edge of the resulting merged node must be checked for zipping.
		hes <- mzoom lens_esunifdgraph_dgraph (st_searchOutEqDGFOEdges [] [] n1);
		let {result2 = result ++ (Prelude.map ESUFOZip hes)};

		return result2
	}

justprop_addVFoEdge :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelFoId s t fn v sov uv -> ESUnifRelFoId s t fn v sov uv -> StateT (ESUnifVDGraph s t fn v sov uv) (ST s) [ESUnifDGOp s t fn v sov uv]
justprop_addVFoEdge s t = return [ESUVCommuteFo (ESUnifVFoEdge s t)]

justprop_newEqDGFONode :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelFoId s t fn v sov uv -> StateT (ESUnifVDGraph s t fn v sov uv) (ST s) [ESUnifDGOp s t fn v sov uv]
justprop_newEqDGFONode foid = return [ESUVAlign foid]

justprop_newEqDGSONode :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelSoId s t fn v sov uv -> StateT (ESUnifVDGraph s t fn v sov uv) (ST s) [ESUnifDGOp s t fn v sov uv]
justprop_newEqDGSONode soid = return []

justprop_newEqDGFOEdge :: ESMGUConstraintsU t pd fn v sov uv => Int -> StateT (ESUnifVDGraph s t fn v sov uv) (ST s) [ESUnifDGOp s t fn v sov uv]
justprop_newEqDGFOEdge eid = do
	{
		-- For any outgoing vertical edges of the target of the edge, create a vertical commute instance.
		t <- mzoom lens_esunifdgraph_dgraph (eqDGFOEdge_target eid);
		ves <- outVFoEdges t;
		let {result = Prelude.map ESUVCommuteFo ves};

		-- Check for zipping of the edge.
		let {result2 = (ESUFOZip eid):result};

		-- Check for projection simplifying of the edge.
		let {result3 = (ESUFOSimpProj eid):result2};

		-- Check for dumping of the edge.
		let {result4 = (ESUFODump eid):result3};

		return result4
	}

justprop_newEqDGSOEdge :: ESMGUConstraintsU t pd fn v sov uv => Int -> StateT (ESUnifVDGraph s t fn v sov uv) (ST s) [ESUnifDGOp s t fn v sov uv]
justprop_newEqDGSOEdge eid = do
	{
		-- In the case of second-order edges, there's no need to do vertical commute, because that only happens on the first-order nodes.
		
		-- Check for zipping of the edge.
		let {result = [ESUSOZip eid]};

		-- Check for projection simplifying of the edge.
		let {result2 = (ESUSOSimpProj eid):result};

		-- Check for dumping of the edge.
		let {result3 = (ESUSODump eid):result2};

		return result3
	}

getStateTSTESUnifVDGraph :: (forall s. StateT (ESUnifVDGraph s t fn v sov uv) (ST s) a) -> RESUnifVDGraph t fn v sov uv -> a
getStateTSTESUnifVDGraph st resuvdg = runST (do {esuvdg <- fromRESUnifVDGraph resuvdg; fst <$> runStateT st esuvdg})

validate_occurs_check_fo :: ESMGUConstraintsU t pd fn v sov uv => RESUnifVDGraph t fn v sov uv -> AnswerSet (RESUnifVDGraph t fn v sov uv) (UnifSysSolution fn sov)
validate_occurs_check_fo resuvdg = if consistent then (ImplicitAS resuvdg) else (ExplicitAS EnumProc.Empty)
	where
		checked = occurs_check_fo;
		consistent = getStateTSTESUnifVDGraph checked resuvdg

occurs_check_fo :: ESMGUConstraintsU t pd fn v sov uv => StateT (ESUnifVDGraph s t fn v sov uv) (ST s) Bool
occurs_check_fo = do
	{
		leaves <- mzoom lens_esunifdgraph_dgraph find_eqdgraph_foleaves;
		esuvdg <- get;
		let {nodes = Prelude.map (DirectId . EqDGFoId . dgid . fromJust) (Prelude.filter isJust (esuvdg ^. (lens_esunifdgraph_dgraph . lens_eqdgraph . lens_fonodes)))};
		cycle_up <- traverse_collect mb_concat (check_cycle_up_fot []) leaves;
		let {j_cycle_up = fromJust cycle_up};
		
		if (isNothing cycle_up) then (return False) else (m_all (\x -> mzoom lens_esunifdgraph_dgraph (m_any (eqSTRelativeEqDGFoIds x) j_cycle_up)) nodes)
	}

check_cycle_up_fot :: ESMGUConstraintsU t pd fn v sov uv => [ESUnifRelFoId s t fn v sov uv] -> ESUnifRelFoId s t fn v sov uv -> StateT (ESUnifVDGraph s t fn v sov uv) (ST s) (Maybe [ESUnifRelFoId s t fn v sov uv])
check_cycle_up_fot downs fot = do
	{
		cycle <- mzoom lens_esunifdgraph_dgraph (m_any (eqSTRelativeEqDGFoIds fot) downs);
		if cycle then (return Nothing) else do
		{
			ines <- mzoom lens_esunifdgraph_dgraph (st_searchInEqDGFOEdges [] [] fot);
			ss <- mzoom lens_esunifdgraph_dgraph (m_concat eqDGFOEdge_sources ines);
			ups <- traverse_collect mb_concat (check_cycle_up_fot (fot:downs)) ss;
			return ((fot:) <$> ups)
		}
	}

validate_occurs_check_so :: ESMGUConstraintsU t pd fn v sov uv => RESUnifVDGraph t fn v sov uv -> AnswerSet (RESUnifVDGraph t fn v sov uv) (UnifSysSolution fn sov)
validate_occurs_check_so resuvdg = if consistent then (ImplicitAS resuvdg) else (ExplicitAS EnumProc.Empty)
	where
		checked = occurs_check_so;
		consistent = getStateTSTESUnifVDGraph checked resuvdg

occurs_check_so :: ESMGUConstraintsU t pd fn v sov uv => StateT (ESUnifVDGraph s t fn v sov uv) (ST s) Bool
occurs_check_so = do
	{
		leaves <- mzoom lens_esunifdgraph_dgraph find_eqdgraph_soleaves;
		esuvdg <- get;
		let {nodes = Prelude.map (DirectId . EqDGSoId . dgid . fromJust) (Prelude.filter isJust (esuvdg ^. (lens_esunifdgraph_dgraph . lens_eqdgraph . lens_sonodes)))};
		cycle_up <- traverse_collect mb_concat (check_cycle_up_sot []) leaves;
		let {j_cycle_up = fromJust cycle_up};
		
		if (isNothing cycle_up) then (return False) else (m_all (\x -> mzoom lens_esunifdgraph_dgraph (m_any (eqSTRelativeEqDGSoIds x) j_cycle_up)) nodes)
	}

check_cycle_up_sot :: ESMGUConstraintsU t pd fn v sov uv => [ESUnifRelSoId s t fn v sov uv] -> ESUnifRelSoId s t fn v sov uv -> StateT (ESUnifVDGraph s t fn v sov uv) (ST s) (Maybe [ESUnifRelSoId s t fn v sov uv])
check_cycle_up_sot downs sot = do
	{
		cycle <- mzoom lens_esunifdgraph_dgraph (m_any (eqSTRelativeEqDGSoIds sot) downs);
		if cycle then (return Nothing) else do
		{
			ines <- mzoom lens_esunifdgraph_dgraph (st_searchInEqDGSOEdges [] [] sot);
			ss <- mzoom lens_esunifdgraph_dgraph (m_concat eqDGSOEdge_sources ines);
			hs <- mzoom lens_esunifdgraph_dgraph (traverse eqDGSOEdge_head ines);
			ups <- traverse_collect mb_concat (check_cycle_up_sot (sot:downs)) (ss ++ hs);
			return ((sot:) <$> ups)
		}
	}

validate_target_arity_so :: ESMGUConstraintsU t pd fn v sov uv => RESUnifVDGraph t fn v sov uv -> AnswerSet (RESUnifVDGraph t fn v sov uv) (UnifSysSolution fn sov)
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

validate_target_arity_sot :: ESMGUConstraintsU t pd fn v sov uv => (forall s. ESUnifRelSoId s t fn v sov uv) -> RESUnifVDGraph t fn v sov uv -> AnswerSet (RESUnifVDGraph t fn v sov uv) (UnifSysSolution fn sov)
validate_target_arity_sot sot resuvdg = if consistent then (ImplicitAS resuvdg) else (ExplicitAS EnumProc.Empty) where consistent = getStateTSTESUnifVDGraph (check_target_arity_sot sot) resuvdg

check_target_arity_so :: ESMGUConstraintsU t pd fn v sov uv => StateT (ESUnifVDGraph s t fn v sov uv) (ST s) Bool
check_target_arity_so = (StateT (\esuvdg -> runStateT (all id <$> traverse check_target_arity_sot (Prelude.map (DirectId . EqDGSoId . dgid . fromJust) (Prelude.filter isJust ((eqdgraph (esunifdgraph esuvdg)) ^. lens_sonodes)))) esuvdg))

check_target_arity_sot :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelSoId s t fn v sov uv -> StateT (ESUnifVDGraph s t fn v sov uv) (ST s) Bool
check_target_arity_sot sot = mzoom lens_esunifdgraph_dgraph (do
	{
		sots <- getEquivDGSONodes sot;
		-- They must all be variables! If they are not, then they must not have incoming edges, and as long as that's true, it's correct.
		if (not (all isvar_sot sots)) then do
		{
			ines <- st_searchInEqDGSOEdges [] [] sot;
			return (Data.List.null ines)
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

validate_head_arity_fo :: ESMGUConstraintsU t pd fn v sov uv => RESUnifVDGraph t fn v sov uv -> AnswerSet (RESUnifVDGraph t fn v sov uv) (UnifSysSolution fn sov)
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

validate_head_arity_foe :: ESMGUConstraintsU t pd fn v sov uv => Int -> RESUnifVDGraph t fn v sov uv -> AnswerSet (RESUnifVDGraph t fn v sov uv) (UnifSysSolution fn sov)
validate_head_arity_foe foe resuvdg = if consistent then (ImplicitAS resuvdg) else (ExplicitAS EnumProc.Empty) where consistent = getStateTSTESUnifVDGraph (check_head_arity_foe foe) resuvdg

check_head_arity_fo :: ESMGUConstraintsU t pd fn v sov uv => StateT (ESUnifVDGraph s t fn v sov uv) (ST s) Bool
check_head_arity_fo = (StateT (\esuvdg -> runStateT (all id <$> traverse check_head_arity_foe (Prelude.map (dgid . fromJust) (Prelude.filter isJust ((eqdgraph (esunifdgraph esuvdg)) ^. lens_foedges)))) esuvdg))

check_head_arity_foe :: ESMGUConstraintsU t pd fn v sov uv => Int -> StateT (ESUnifVDGraph s t fn v sov uv) (ST s) Bool
check_head_arity_foe foe = do
	{
		h <- mzoom lens_esunifdgraph_dgraph (eqDGFOEdge_head foe);
		sots <- mzoom lens_esunifdgraph_dgraph (getEquivDGSONodes h);
		let {arities = Prelude.map sot_min_arity sots; arity = Prelude.foldr (\i -> \m -> max i m) 0 arities};
		ss <- mzoom lens_esunifdgraph_dgraph (eqDGFOEdge_sources foe);
		return ((length ss) >= arity)
	}

validate_head_arity_so :: ESMGUConstraintsU t pd fn v sov uv => RESUnifVDGraph t fn v sov uv -> AnswerSet (RESUnifVDGraph t fn v sov uv) (UnifSysSolution fn sov)
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

validate_head_arity_soe :: ESMGUConstraintsU t pd fn v sov uv => Int -> RESUnifVDGraph t fn v sov uv -> AnswerSet (RESUnifVDGraph t fn v sov uv) (UnifSysSolution fn sov)
validate_head_arity_soe soe resuvdg = if consistent then (ImplicitAS resuvdg) else (ExplicitAS EnumProc.Empty) where consistent = getStateTSTESUnifVDGraph (check_head_arity_soe soe) resuvdg

check_head_arity_so :: ESMGUConstraintsU t pd fn v sov uv => StateT (ESUnifVDGraph s t fn v sov uv) (ST s) Bool
check_head_arity_so = (StateT (\esuvdg -> runStateT (all id <$> traverse check_head_arity_soe (Prelude.map (dgid . fromJust) (Prelude.filter isJust ((eqdgraph (esunifdgraph esuvdg)) ^. lens_soedges)))) esuvdg))

check_head_arity_soe :: ESMGUConstraintsU t pd fn v sov uv => Int -> StateT (ESUnifVDGraph s t fn v sov uv) (ST s) Bool
check_head_arity_soe soe = do
	{
		h <- mzoom lens_esunifdgraph_dgraph (eqDGSOEdge_head soe);
		sots <- mzoom lens_esunifdgraph_dgraph (getEquivDGSONodes h);
		let {arities = Prelude.map sot_min_arity sots; arity = Prelude.foldr (\i -> \m -> max i m) 0 arities};
		ss <- mzoom lens_esunifdgraph_dgraph (eqDGSOEdge_sources soe);
		return ((length ss) >= arity)
	}

validate_sot_consistency :: ESMGUConstraintsU t pd fn v sov uv => RESUnifVDGraph t fn v sov uv -> AnswerSet (RESUnifVDGraph t fn v sov uv) (UnifSysSolution fn sov)
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

validate_sot_consistency_sot :: ESMGUConstraintsU t pd fn v sov uv => (forall s. ESUnifRelSoId s t fn v sov uv) -> RESUnifVDGraph t fn v sov uv -> AnswerSet (RESUnifVDGraph t fn v sov uv) (UnifSysSolution fn sov)
validate_sot_consistency_sot sot resuvdg = if consistent then (ImplicitAS resuvdg) else (ExplicitAS EnumProc.Empty) where consistent = getStateTSTESUnifVDGraph (check_sot_consistency_sot sot) resuvdg

check_sot_consistency :: ESMGUConstraintsU t pd fn v sov uv => StateT (ESUnifVDGraph s t fn v sov uv) (ST s) Bool
check_sot_consistency = (StateT (\esuvdg -> runStateT (all id <$> traverse check_sot_consistency_sot (Prelude.map (DirectId . EqDGSoId . dgid . fromJust) (Prelude.filter isJust ((eqdgraph (esunifdgraph esuvdg)) ^. lens_sonodes)))) esuvdg))

check_sot_consistency_sot :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelSoId s t fn v sov uv -> StateT (ESUnifVDGraph s t fn v sov uv) (ST s) Bool
check_sot_consistency_sot sot = do
	{
		sots <- mzoom lens_esunifdgraph_dgraph (getEquivDGSONodes sot);
		let {nvsots = Prelude.filter (not . isvar_sot) sots};
		return (allEq nvsots)
	}

validate_fot_consistency :: ESMGUConstraintsU t pd fn v sov uv => RESUnifVDGraph t fn v sov uv -> AnswerSet (RESUnifVDGraph t fn v sov uv) (UnifSysSolution fn sov)
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

validate_fot_consistency_fot :: ESMGUConstraintsU t pd fn v sov uv => (forall s. ESUnifRelFoId s t fn v sov uv) -> RESUnifVDGraph t fn v sov uv -> AnswerSet (RESUnifVDGraph t fn v sov uv) (UnifSysSolution fn sov)
validate_fot_consistency_fot fot resuvdg = if consistent then (ImplicitAS resuvdg) else (ExplicitAS EnumProc.Empty) where consistent = getStateTSTESUnifVDGraph (check_fot_consistency_fot fot) resuvdg

check_fot_consistency :: ESMGUConstraintsU t pd fn v sov uv => StateT (ESUnifVDGraph s t fn v sov uv) (ST s) Bool
check_fot_consistency = (StateT (\esuvdg -> runStateT (all id <$> traverse check_fot_consistency_fot (Prelude.map (DirectId . EqDGFoId . dgid . fromJust) (Prelude.filter isJust ((eqdgraph (esunifdgraph esuvdg)) ^. lens_fonodes)))) esuvdg))

check_fot_consistency_fot :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelFoId s t fn v sov uv -> StateT (ESUnifVDGraph s t fn v sov uv) (ST s) Bool
check_fot_consistency_fot fot = do
	{
		fots <- mzoom lens_esunifdgraph_dgraph (getEquivDGFONodes fot);
		let {nvfots = Prelude.filter (not . is_td_var) fots};
		return (allEq nvfots)
	}

-- TODO: First-order version of the consistency check for so. This applies because there can be constant terms. (!)

esu_fo_dump :: ESMGUConstraintsU t pd fn v sov uv => StateT (ESUnifVDGraph s t fn v sov uv) (ST s) ()
esu_fo_dump = (StateT (\esuvdg -> runStateT (runStateTOps (Prelude.map (ESUFODump . dgid . fromJust) (Prelude.filter isJust ((eqdgraph (esunifdgraph esuvdg)) ^. lens_foedges)))) esuvdg)) >> pass

esu_fo_dump_foe :: ESMGUConstraintsU t pd fn v sov uv => Int -> StateT (ESUnifVDGraph s t fn v sov uv) (ST s) [ESUnifDGOp s t fn v sov uv]
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

esu_so_dump :: ESMGUConstraintsU t pd fn v sov uv => StateT (ESUnifVDGraph s t fn v sov uv) (ST s) ()
esu_so_dump = (StateT (\esuvdg -> runStateT (runStateTOps (Prelude.map (ESUSODump . dgid . fromJust) (Prelude.filter isJust ((eqdgraph (esunifdgraph esuvdg)) ^. lens_soedges)))) esuvdg)) >> pass

esu_so_dump_soe :: ESMGUConstraintsU t pd fn v sov uv => Int -> StateT (ESUnifVDGraph s t fn v sov uv) (ST s) [ESUnifDGOp s t fn v sov uv]
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

esu_so_simplify_projections :: ESMGUConstraintsU t pd fn v sov uv => StateT (ESUnifVDGraph s t fn v sov uv) (ST s) ()
esu_so_simplify_projections = (StateT (\esuvdg -> runStateT (runStateTOps (Prelude.map (ESUSOSimpProj . dgid . fromJust) (Prelude.filter isJust ((eqdgraph (esunifdgraph esuvdg)) ^. lens_soedges)))) esuvdg)) >> pass

esu_so_simplify_proj_soe :: ESMGUConstraintsU t pd fn v sov uv => Int -> StateT (ESUnifVDGraph s t fn v sov uv) (ST s) [ESUnifDGOp s t fn v sov uv]
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
				if (length ss) <= idx then (trace ("Projection does not have enough inputs! Has: " ++ (show (length ss)) ++ ", but is looking for " ++ (show idx) ++ "th projection.") (return [])) else do
				{
					result1 <- prop_mergeEqDGSONodes (ss !! idx) t;
					result2 <- (return result1) >>=++ (prop_deleteEqDGSOEdge soe);

					return result2
				}
			}
			else (return [])
		}
	}

esu_fo_simplify_projections :: ESMGUConstraintsU t pd fn v sov uv => StateT (ESUnifVDGraph s t fn v sov uv) (ST s) ()
esu_fo_simplify_projections = (StateT (\esuvdg -> runStateT (runStateTOps (Prelude.map (ESUFOSimpProj . dgid . fromJust) (Prelude.filter isJust ((eqdgraph (esunifdgraph esuvdg)) ^. lens_foedges)))) esuvdg)) >> pass

esu_fo_simplify_proj_foe :: ESMGUConstraintsU t pd fn v sov uv => Int -> StateT (ESUnifVDGraph s t fn v sov uv) (ST s) [ESUnifDGOp s t fn v sov uv]
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
				if (length ss) <= idx then (trace ("Projection does not have enough inputs! Has: " ++ (show (length ss)) ++ ", but is looking for " ++ (show idx) ++ "th projection.") (return [])) else do
				{
					result1 <- prop_mergeEqDGFONodes (ss !! idx) t;
					result2 <- (return result1) >>=++ (prop_deleteEqDGFOEdge foe);

					return result2
				}
			}
			else (return [])
		}
	}

esu_vertical_commute :: ESMGUConstraintsU t pd fn v sov uv => StateT (ESUnifVDGraph s t fn v sov uv) (ST s) ()
esu_vertical_commute = (StateT (\esuvdg -> runStateT (runStateTOps (Prelude.map ESUVCommuteFo (esunifdgraph_vfoedges esuvdg))) esuvdg)) >> pass

esu_vertical_commute_fo_edge :: ESMGUConstraintsU t pd fn v sov uv => ESUnifVFoEdge s t fn v sov uv -> StateT (ESUnifVDGraph s t fn v sov uv) (ST s) [ESUnifDGOp s t fn v sov uv]
esu_vertical_commute_fo_edge e = do
	{
		let {s = esunifvfoedge_source e; t = esunifvfoedge_target e};
		sines <- mzoom lens_esunifdgraph_dgraph (st_searchInEqDGFOEdges [] [] s);
		soutes <- mzoom lens_esunifdgraph_dgraph (st_searchOutEqDGFOEdges [] [] s);
		result1 <- concat <$> (traverse (esu_vertical_commute_fo_edge_hedge e) sines);
		result2 <- (return result1) >>=++ (concat <$> (traverse (esu_vertical_commute_fo_edge_hedge e) soutes));

		return result2
	}

-- Check if a specific horizontal edge that has the source node of the vertical edge as a target/source has a corresponding one with the target of the vertical edge as a target/source, and if it does not, then create it.
-- Arguments: Vertical edge, identifier of the horizontal edge.
esu_vertical_commute_fo_edge_hedge :: ESMGUConstraintsU t pd fn v sov uv => ESUnifVFoEdge s t fn v sov uv -> Int -> StateT (ESUnifVDGraph s t fn v sov uv) (ST s) [ESUnifDGOp s t fn v sov uv]
esu_vertical_commute_fo_edge_hedge ve he = do
	{
		-- First verify that the horizontal edge still exists in the graph!
		eex <- mzoom lens_esunifdgraph_dgraph (checkEqDGFOEdge he);
		if (not eex) then (return []) else do
		{
			sss <- mzoom lens_esunifdgraph_dgraph (eqDGFOEdge_sources he);
			tss <- sequence (Prelude.map (divideOverVFoEdge ve) sss);
			h <- mzoom lens_esunifdgraph_dgraph (eqDGFOEdge_head he);		
			st <- mzoom lens_esunifdgraph_dgraph (eqDGFOEdge_target he);
			tt <- divideOverVFoEdge ve st;
			ex <- mzoom lens_esunifdgraph_dgraph (st_checkEqDGFOEdge h tss tt);
			if ex then (return [])
			else do
			{
				--mzoom lens_esunifdgraph_dgraph (newEqDGFOEdge h tss tt);
				result <- prop_newEqDGFOEdge h tss tt;
				let {zipped = zip sss tss};
				--traverse (uncurry addVFoEdge) zipped;
				--return (Prelude.map (ESUVCommuteFo . (uncurry ESUnifVFoEdge)) zipped)
				result2 <- (return result) >>=++ (concat <$> traverse (uncurry prop_addVFoEdge) zipped);

				result3 <- (return result2) >>=++ (prop_addVFoEdge st tt);

				return result3
			}
		}
	}

esu_vertical_align :: ESMGUConstraintsU t pd fn v sov uv => StateT (ESUnifVDGraph s t fn v sov uv) (ST s) ()
esu_vertical_align = (StateT (\esuvdg -> runStateT (runStateTOps (Prelude.map (ESUVAlign . directEqDGFoId . dgid . fromJust) (Prelude.filter isJust ((eqdgraph (esunifdgraph esuvdg)) ^. lens_fonodes)))) esuvdg)) >> pass

esu_vertical_align_fot :: ESMGUConstraintsU t pd fn v sov uv => ESUnifRelFoId s t fn v sov uv -> StateT (ESUnifVDGraph s t fn v sov uv) (ST s) [ESUnifDGOp s t fn v sov uv]
esu_vertical_align_fot fot = do
	{
		mb_rtd <- mzoom lens_esunifdgraph_dgraph (getSTRelativeEqDGFoCoId fot);
		if (isNothing mb_rtd) then (return []) else do
		{		
			let {rtd = fromJustErr "This should never happen. esu_vertical_align_fot" mb_rtd};
			if (not (is_tdunif rtd)) then (return []) else do
			{
				let {intd = from_tdunif rtd; intd_id = relbwEqDGFoId intd};
				exist <- checkVFoEdge intd_id fot;
				if exist then (return [])
				else do
				{
					--addVFoEdge intd_id fot;
					--return [ESUVAlign intd_id, ESUVCommuteFo (ESUnifVFoEdge intd_id fot)]
					prop_addVFoEdge intd_id fot
				}
			}	
		}
	}

esu_sozip :: ESMGUConstraintsU t pd fn v sov uv => StateT (ESUnifVDGraph s t fn v sov uv) (ST s) ()
esu_sozip = (StateT (\esuvdg -> runStateT (runStateTOps (Prelude.map (ESUSOZip . dgid . fromJust) (Prelude.filter isJust ((eqdgraph (esunifdgraph esuvdg)) ^. lens_soedges)))) esuvdg)) >> pass

esu_sozip_soe :: ESMGUConstraintsU t pd fn v sov uv => Int -> StateT (ESUnifVDGraph s t fn v sov uv) (ST s) [ESUnifDGOp s t fn v sov uv]
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
					sresult2 <- (return sresult1) >>=++ (prop_deleteEqDGSOEdge rpe);

					return sresult2
				}
			})};
			result <- concat <$> traverse te tomerges;
			return result
		}
	}

esu_fozip :: ESMGUConstraintsU t pd fn v sov uv => StateT (ESUnifVDGraph s t fn v sov uv) (ST s) ()
esu_fozip = (StateT (\esuvdg -> runStateT (runStateTOps (Prelude.map (ESUFOZip . dgid. fromJust) (Prelude.filter isJust ((eqdgraph (esunifdgraph esuvdg)) ^. lens_foedges)))) esuvdg)) >> pass

esu_fozip_foe :: ESMGUConstraintsU t pd fn v sov uv => Int -> StateT (ESUnifVDGraph s t fn v sov uv) (ST s) [ESUnifDGOp s t fn v sov uv]
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
					sresult2 <- (return sresult1) >>=++ (prop_deleteEqDGFOEdge rpe);

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


-- TODO: Be able to add an entire expression to a graph, creating all intermediate nodes. This would absolutely de-normalize the graph, though, gotta keep that in mind!

-- Case matching against an expression is done on an "exists" and a "first" basis: We look for some incoming edge that matches, not that all incoming edges match, and furthermore, if multiple edges match the head, we pick an arbitrary one of them, which may not match the remainder of the expression! Therefore, using this on non-factorized graphs should be done with care.
-- Of course, matching is direct matching, it does not consider what could "potentially unify with". It needs to be exactly that.

case_foexp :: ESMGUConstraintsU t pd fn v sov uv => FOTermDependantExp t fn v sov uv -> ESUnifRelFoId s t fn v sov uv -> StateT (ESUnifVDGraph s t fn v sov uv) (ST s) (Maybe [(FOTermDependantExp t fn v sov uv,ESUnifRelFoId s t fn v sov uv)])
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

match_foexp :: ESMGUConstraintsU t pd fn v sov uv => FOTermDependantExp t fn v sov uv -> ESUnifRelFoId s t fn v sov uv -> StateT (ESUnifVDGraph s t fn v sov uv) (ST s) Bool
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

case_soexp :: ESMGUConstraintsU t pd fn v sov uv => SOTermDependantExp fn sov -> ESUnifRelSoId s t fn v sov uv -> StateT (ESUnifVDGraph s t fn v sov uv) (ST s) (Maybe [(SOTermDependantExp fn sov,ESUnifRelSoId s t fn v sov uv)])
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

match_soexp :: ESMGUConstraintsU t pd fn v sov uv => SOTermDependantExp fn sov -> ESUnifRelSoId s t fn v sov uv -> StateT (ESUnifVDGraph s t fn v sov uv) (ST s) Bool
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


