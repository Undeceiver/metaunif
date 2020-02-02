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

-- Heuristics
esunif_search_heuristic :: Diagonalize
esunif_search_heuristic = Diagonalize False False 1 1 False


data TermDependant t fn v sov uv = TDDirect (SOMetawrap t fn v sov) | TDUnif uv (TermDependant t fn v sov uv) -- deriving (Eq, Ord)
data SOTermDependant fn sov uv = SOTDDirect (SOTerm fn sov) | SOTDUnif uv (SOTermDependant fn sov uv) -- deriving (Eq, Ord)

instance (Show (t (SOTerm fn sov) (UTerm (t (SOTerm fn sov)) v)), Show uv, Show v, Show fn, Show sov) => Show (TermDependant t fn v sov uv) where
	show (TDDirect somw) = show somw
	show (TDUnif uv td) = (show uv) ++ " " ++ (show td)

instance (Show uv, Show fn, Show sov) => Show (SOTermDependant fn sov uv) where
	show (SOTDDirect sot) = show sot
	show (SOTDUnif uv td) = (show uv) ++ " " ++ (show td)


data UnifEquation t fn v sov uv = TermUnif (TermDependant t fn v sov uv) (TermDependant t fn v sov uv) -- Pending adding atom unification here when we are ready.

type UnifSystem t fn v sov uv = [UnifEquation t fn v sov uv]

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

type UnifSysSolution t fn v sov uv = Map uv (UnifSolution t fn v sov)

-- A system of equations is a highly implicit solution to a system of unification equations
instance Implicit (UnifSystem t fn v sov uv) (UnifSysSolution t fn v sov uv) where
	checkImplicit = undefined
	enumImplicit = undefined




-- Single unifier solving: Here we do not explicitly talk about the unifier because it's only one.
-- That is: There are NO UNIFIER VARIABLES.
data SUnifEquation t fn v sov = STermUnif (SOMetawrap t fn v sov) (SOMetawrap t fn v sov)

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




type ESMGUConstraints t pd fn v sov = (Ord sov, SimpleTerm t, Eq fn, HasArity fn, HasArity sov, ChangeArity sov, Functor (t (SOTerm fn sov)), Functor (t fn), Bifunctor t, Traversable (t (GroundSOT fn)), Unifiable (t (SOTerm fn sov)), Variabilizable v, Variable v, Variabilizable sov, Variable sov, Ord v, Functor (t (GroundSOT fn)), Eq (t fn (Fix (t fn))), Show sov, Show fn, Show v, Show (t (SOTerm fn sov) (UTerm (t (SOTerm fn sov)) v)), Show (t (GroundSOT fn) (UTerm (t (GroundSOT fn)) v)))
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
	enumImplicit mgu = raw <$> (fromProvenanceT (nesmgu_enumImplicit mgu))

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



solve_single_unif_equation :: SUnifEquation t fn v sov -> AnswerSet (ESMGU t pd fn v sov) (UnifSolution t fn v sov)
solve_single_unif_equation = undefined




-- A dependency graph is another implicit solution to a system of unification equations (an intermediate one)
-- instance Implicit **DEPENDENCY GRAPH** (UnifSysSolution t fn v sov uv) where



