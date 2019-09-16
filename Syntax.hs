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
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE FlexibleContexts #-}
module Syntax where

import Control.Unification
import Control.Unification.IntVar
import HaskellPlus
import Data.Functor.Fixedpoint
import Data.Bifunctor
import Data.Either
import Data.Functor.Const
import Data.Functor.Fixedpoint
import Data.Functor.Identity
import Control.Monad.Error.Class
import Control.Monad.Trans.Identity
import Control.Monad.Except
import Control.Unification.Types
import Extensionality
import Data.List
import Data.Maybe

class Variabilizable t where
	from_var :: IntVar -> t
	get_var :: t -> IntVar

getVarID_gen :: Variabilizable v => v -> Int
getVarID_gen x = getVarID (get_var x)

read_arity :: String -> (Int,String)
read_arity ('[':xs) = (let r = (head (reads xs))
			in ((fst r),(tail (snd r))))

class HasArity t where
	arity :: t -> Int

-- A type providing base cases for a functor structure
class FunctorBase b where
	isBase :: (b f t) -> Bool
	fromBase :: (b f t) -> (b g t)
	fromRec :: Functor f => (b f t) -> f (b f t)

fromRecSafe :: (Functor f, FunctorBase b) => f (b f t) -> (b f t) -> f (b f t)
fromRecSafe def r = if (isBase r) then def else (fromRec r)

class SimpleTerm (t :: * -> * -> *) where
	build_term :: fn -> [a] -> t fn a
	unbuild_term :: t fn a -> (fn,[a])

read_term_list :: Read v => String -> ([v],String)
read_term_list = read_term_list_gen '(' ')' ','

read_soterm_list :: Read v => String -> ([v],String)
read_soterm_list = read_term_list_gen '{' '}' ','

read_term_list_gen :: Read v => Char -> Char -> Char -> String -> ([v],String)
read_term_list_gen o c s [] = ([],"")
read_term_list_gen o c s (x:xs) | x == o = read_term_list_gen o c s xs
read_term_list_gen o c s (x:xs) | x == c = ([],xs)
read_term_list_gen o c s (x:xs) | x == s = read_term_list_gen o c s xs
read_term_list_gen o c s (x:xs) | x == ' ' = read_term_list_gen o c s xs
read_term_list_gen o c s x = (let r = (head (reads x))
			in (let r2 = read_term_list_gen o c s (snd r)
				in ((fst r):(fst r2),(snd r2))))

data Predicabilize (a :: * -> *) f = Atom (a f) | Term f deriving (Eq, Ord, Functor, Foldable, Traversable)

instance (Show (a f), Show f) => Show (Predicabilize a f) where
	show (Atom x) = show x
	show (Term x) = show x

instance Unifiable a => Unifiable (Predicabilize a) where
	zipMatch (Atom a1) (Atom a2) = (zipMatch a1 a2) >>= (Just . Atom)
	zipMatch (Term t1) (Term t2) = Just (Term (Right (t1,t2)))

-- Like UTerm but with no recursive data type. Used to modify it before doing the fixed point, and there is a simple translation back and forth.
data FlatTerm t v f = Var v | FTerm (t f) deriving (Eq, Ord, Functor, Foldable, Traversable)

instance (Show v, Show (t f)) => Show (FlatTerm t v f) where
	show (Var v) = show v
	show (FTerm x) = show x

-- Note that in this instance variables are actually constants, as this is a lifting of variables into object-level elements.
instance (Unifiable t, Eq v) => Unifiable (FlatTerm t v) where
	zipMatch (Var v1) (Var v2) | v1 == v2 = Just (Var v1)
	zipMatch (FTerm t1) (FTerm t2) = (zipMatch t1 t2) >>= (Just . FTerm)
	zipMatch _ _ = Nothing

flat_to_uterm :: Functor t => Fix (FlatTerm t v) -> UTerm t v
flat_to_uterm (Fix (Var v)) = UVar v
flat_to_uterm (Fix (FTerm st)) = UTerm (fmap flat_to_uterm st)

uterm_to_flat :: Functor t => UTerm t v -> Fix (FlatTerm t v)
uterm_to_flat (UVar v) = Fix (Var v)
uterm_to_flat (UTerm st) = Fix (FTerm (fmap uterm_to_flat st))

type GroundT t fn = Fix (t fn)
type GroundA a t pd fn = a pd (GroundT t fn)

-------------------------------------------------------------------
-- Big design decision: Meta-variables as second-order variables.
-------------------------------------------------------------------

-- The following part is outdated, it deals with flat meta-variables (non second-order). But we keep it because it is likely we will need it at some point, even if just to translate from one to the other.

-- Wrapper that takes a syntactic element and a type of meta-variables and creates syntactic elements which may also contain meta-variables in places.
type Metawrapper t v mv f = FlatTerm (FlatTerm t v) mv f
type Metawrap t v mv = UTerm (FlatTerm t v) mv

mw :: Functor t => UTerm t v -> Metawrap t v mv
mw (UVar v) = UTerm (Var v)
mw (UTerm t) = UTerm (FTerm (fmap mw t))

mv :: mv -> Metawrap t v mv
mv x = UVar x

type VariablePredicabilize (a :: * -> *) amv f = Predicabilize (FlatTerm a amv) f

type PredicateMetawrap (a :: * -> *) (t :: * -> *) v tmv amv = VariablePredicabilize a amv (Metawrap t v tmv)

tmv :: tmv -> PredicateMetawrap a t v tmv amv
tmv = Term . mv

amv :: amv -> PredicateMetawrap a t v tmv amv
amv = Atom . Var

pmw :: (Functor a, Functor t) => Predicabilize a (UTerm t v) -> PredicateMetawrap a t v tmv amv
pmw (Atom x) = Atom (FTerm (fmap mw x))
pmw (Term x) = Term (mw x)

-- A predicate meta wrap can be one of five things: An object-level variable, a term meta-variable, an atom meta-variable, a term or an atom. The structure itself is not structured like this because it has a lot more structure to it and that's good. But sometimes, we just want to have a case for these five things. The following structure is used for that.

data PredicateMetawrapDecomp (a :: * -> *) (t :: * -> *) v tmv amv = ObjVar v | TermMVar tmv | AtomMVar amv | ObjTerm (t (Metawrap t v tmv)) | ObjAtom (a (Metawrap t v tmv))

instance (Show v, Show tmv, Show amv, Show (t (Metawrap t v tmv)), Show (a (Metawrap t v tmv))) => Show (PredicateMetawrapDecomp a t v tmv amv) where
	show (ObjVar v) = show v
	show (TermMVar tmv) = show tmv
	show (AtomMVar amv) = show amv
	show (ObjTerm x) = show x
	show (ObjAtom x) = show x

decomp_pmw :: PredicateMetawrap a t v tmv amv -> PredicateMetawrapDecomp a t v tmv amv
decomp_pmw (Atom (Var amv)) = AtomMVar amv
decomp_pmw (Atom (FTerm x)) = ObjAtom x
decomp_pmw (Term (UVar tmv)) = TermMVar tmv
decomp_pmw (Term (UTerm (Var v))) = ObjVar v
decomp_pmw (Term (UTerm (FTerm x))) = ObjTerm x

-- And when they are not meta-variables, we can put them back into term shape.
unmw :: Functor t => Metawrap t v tmv -> UTerm t v
unmw (UTerm (Var v)) = UVar v
unmw (UTerm (FTerm x)) = UTerm (fmap unmw x)

unpmw :: (Functor a, Functor t) => PredicateMetawrap a t v tmv amv -> Predicabilize a (UTerm t v)
unpmw x = case (decomp_pmw x) of
	{
		AtomMVar amv -> error "An atom meta-variable cannot be unwrapped.";
		ObjAtom x -> Atom (fmap unmw x);
		TermMVar tmv -> error "A term meta-variable cannot be unwrapped.";
		ObjTerm x -> Term (UTerm (fmap unmw x));
		ObjVar v -> Term (UVar v)
	}


-- End of flat meta-variables section.

-- Start of second-order meta-variables section.
-- This is a limited second-order variables, which means several things.
--	Semantically, they can only be replaced by elements of the second-order Herbrand universe. That is, they are only elements in the space generated by functions in the signature and composition.
--	Syntactically, they are never quantified over, and the only second-order functions are constants.
-- In other words, they are only variable functions and compositions with those, and with the semantic restriction that their interpretation are only elements in the second-order Herbrand universe.
-- Implementation detail: The simplest way to represent compositions of arities greater than 1 is to use lambda abstractions, but we do so using an extension of De Bruijn indices to multiple parameters. The main attractive of this is that we can compare and combine second-order terms without any need for context or without considering alpha-equivalence.

-- The first element in the list is the index from which to take the first argument to this argument.
-- For example, if the argument map is [1,0] in f o g, it means f(g(y,x)), whereas if it is [0,1] it means f(g(x,y)) and if it is [1,1] it means f(g(y,y)). We write this f(g[1,1])(x,y)
-- Compositions just pass down, so f(g(h[0,1],i[1,1])[1,0]) means that the first variable inside g corresponds to the second one inside f, and the second one in g to the first one in f, the first in h is the first one in g, which is the second one in f, and the second one in h is the second one in g, which is the first one in f. Same for i. All in all, f(g(h[0,1],i[1,1])[1,0])(x,y) = f(g(h(y,x),i(x,x))). Note here that the arity of f is 1 but the arity of the overall expression is 2.
type ArgumentMap = [Int]

instance HasArity ArgumentMap where
	arity [] = 0
	arity (x:xs) = max (x+1) (arity xs)

instance {-# OVERLAPPING #-} Read (SOTerm fn r) => Read (SOTerm fn r,ArgumentMap) where
	readsPrec _ xs = (let r = (head (reads xs)::(SOTerm fn r,String))
				in (let r2 = (head (reads (snd r))::(ArgumentMap,String))
					in [((fst r,fst r2),snd r2)]))

-- ConstF indicates a function corresponding to a constant SYMBOL of second order (but the function is not constant in any way).
-- CConstF indicates a function that is constant.
-- In order to define constant functions, we need to specify what type the functions return.
data SOTermF fn r f = ConstF fn | CompF fn [(f,ArgumentMap)] | CConstF Int r | Proj Int Int deriving (Functor, Foldable, Traversable)

instance (Show fn, Show f, Show r) => Show (SOTermF fn r f) where
	show (ConstF fn) = show fn
	show (CompF fn args) = (show fn) ++ "{" ++ (show_as_args (\(f,arg) -> (show f) ++ (show arg)) args) ++ "}"
	show (CConstF aty v) = "(\\x -> " ++ (show v) ++ ")[" ++ (show aty) ++ "]"
	show (Proj aty idx) = "pi" ++ (show idx) ++ "[" ++ (show aty) ++ "]"

instance HasArity [(f,ArgumentMap)] where
	arity args = foldr max 0 (map (\(f,arg) -> arity arg) args)

instance HasArity fn => HasArity (SOTermF fn r f) where
	arity (ConstF x) = arity x
	arity (CompF x args) = arity args
	arity (CConstF aty _) = aty
	arity (Proj aty _) = aty


type SOTerm fn r = Fix (SOTermF fn r)

instance HasArity fn => HasArity (SOTerm fn r) where
	arity (Fix x) = arity x

-- Need to indicate into what structure it gets translated. That is the first (function) argument.
apply_soterm :: HasArity fn => (fn -> [t] -> t) -> SOTerm fn t -> [t] -> t
apply_soterm c f args = apply_soterm_checkarity f args (apply_soterm_actual c f args)

apply_soterm_actual :: HasArity fn => (fn -> [t] -> t) -> SOTerm fn t -> [t] -> t
apply_soterm_actual c (Fix (ConstF f)) args = c f args
apply_soterm_actual c (Fix (CompF f sargs)) args = c f (map (\(s,argmap) -> apply_soterm c s (apply_argmap argmap args)) sargs)
apply_soterm_actual c (Fix (CConstF aty v)) args = v
apply_soterm_actual c (Fix (Proj aty idx)) args = if (idx >= (length args)) then (error ("Projection on the " ++ (show idx) ++ " argument being applied to only " ++ (show (length args)) ++ " arguments.")) else (args !! idx)

apply_soterm_checkarity :: HasArity fn => SOTerm fn t -> [t] -> a -> a
apply_soterm_checkarity f args r = if (arity f <= length args) then r else (error ("The arity of the function (" ++ (show (arity f)) ++ ") is larger than the number of arguments (" ++ (show (length args)) ++ ")."))

apply_argmap :: ArgumentMap -> [a] -> [a]
apply_argmap inds args = map (args !!) inds

-- Composition of second-order terms
compose_soterm :: HasArity fn => SOTerm fn t -> [(SOTerm fn t, ArgumentMap)] -> SOTerm fn t
compose_soterm f args = compose_soterm_checkarity f args (compose_soterm_actual f args)

compose_soterm_actual :: HasArity fn => SOTerm fn t -> [(SOTerm fn t, ArgumentMap)] -> SOTerm fn t
compose_soterm_actual (Fix (ConstF f)) args = Fix (CompF f args)
compose_soterm_actual (Fix (CompF f sargs)) args = Fix (CompF f (map (\(s,argmap) -> (compose_soterm s (apply_argmap argmap args),[0..(arity args - 1)])) sargs))
compose_soterm_actual (Fix (CConstF aty v)) args = Fix (CConstF (arity args) v)
compose_soterm_actual (Fix (Proj aty idx)) args = case (args !! idx) of {(Fix (Proj saty sidx),argmap) -> Fix (Proj resarity (argmap !! sidx)); (s,argmap) -> compose_soterm s (map (\i -> (Fix (Proj resarity i),[0..resarity - 1])) argmap)} where resarity = arity args

compose_soterm_checkarity :: HasArity fn => SOTerm fn t -> [(SOTerm fn t, ArgumentMap)] -> a -> a
compose_soterm_checkarity f args r = if (arity f <= length args) then r else (error ("The arity of the function (" ++ (show (arity f)) ++ ") is larger than the number of arguments (" ++ (show (length args)) ++ ")."))

(*.) :: HasArity fn => SOTerm fn t -> [(SOTerm fn t, ArgumentMap)] -> SOTerm fn t
(*.) = compose_soterm

-- We do not provide equality checking for the unfixed versions on purpose, to avoid confusion. On the fixed versions, equality could happen even when syntactically they are not the same if the argument maps "cancel" each other.
-- As a note, it turns out constant functions are redundant in the fixed point, as it turns out that you can just express them by having 0-ary compositions of the others. However, we do *not* check this equality here. This could potentially become a problem, but I doubt it.

-- Don't use this directly, please.
data GenericTermForSO fn r f = GTFSO fn [f] | GTFSOBase Int | GTFSOBaseR r deriving (Eq, Ord, Functor, Foldable, Traversable, Show)

fixGtfso :: fn -> [Fix (GenericTermForSO fn r)] -> Fix (GenericTermForSO fn r)
fixGtfso = build_functor_fix GTFSO

generic_soterm :: SOTerm fn r -> SOTerm fn (Fix (GenericTermForSO fn r))
generic_soterm (Fix (ConstF fn)) = Fix (ConstF fn)
generic_soterm (Fix (CompF fn args)) = Fix (CompF fn (map (\(s,argmap) -> (generic_soterm s,argmap)) args))
generic_soterm (Fix (CConstF aty v)) = Fix (CConstF aty (Fix . GTFSOBaseR $ v))
generic_soterm (Fix (Proj aty idx)) = Fix (Proj aty idx)

instance {-# OVERLAPPING #-} (Eq fn, Eq r, HasArity fn) => Eq (SOTerm fn r) where
	t1 == t2 = (apply_soterm fixGtfso (generic_soterm t1) (map (Fix . GTFSOBase) [1..(arity t1)])) == (apply_soterm fixGtfso (generic_soterm t2) (map (Fix . GTFSOBase) [1..(arity t2)]))

type SOAtom pd fn pr fr = SOTermF pd pr (SOTerm fn fr)

apply_soatom :: (HasArity fn, HasArity pd) => (pd -> [t] -> p) -> (fn -> [t] -> t) -> SOAtom pd fn p t -> [t] -> p
apply_soatom cp cf p args = apply_soatom_checkarity p args (apply_soatom_actual cp cf p args)

apply_soatom_actual :: (HasArity fn, HasArity pd) => (pd -> [t] -> p) -> (fn -> [t] -> t) -> SOAtom pd fn p t -> [t] -> p
apply_soatom_actual cp cf (ConstF p) args = cp p args
apply_soatom_actual cp cf (CompF p sargs) args = cp p (map (\(s,argmap) -> apply_soterm cf s (apply_argmap argmap args)) sargs)
apply_soatom_actual cp cf (CConstF aty v) args = v
apply_soatom_actual cp cf (Proj aty idx) args = error "Projections should not be present in predicates."

apply_soatom_checkarity :: HasArity pd => SOAtom pd fn p t -> [t] -> a -> a
apply_soatom_checkarity p args r = if (arity p <= length args) then r else (error ("The arity of the predicate (" ++ (show (arity p)) ++ ") is larger than the number of arguments (" ++ (show (length args)) ++ ")."))

compose_soatom :: (HasArity pd, HasArity fn) => SOAtom pd fn p t -> [(SOTerm fn t, ArgumentMap)] -> SOAtom pd fn p t
compose_soatom p args = compose_soatom_checkarity p args (compose_soatom_actual p args)

compose_soatom_actual :: (HasArity pd, HasArity fn) => SOAtom pd fn p t -> [(SOTerm fn t, ArgumentMap)] -> SOAtom pd fn p t
compose_soatom_actual (ConstF p) args = (CompF p args)
compose_soatom_actual (CompF p sargs) args = (CompF p (map (\(s,argmap) -> (compose_soterm s (apply_argmap argmap args),[0..(arity args - 1)])) sargs))
compose_soatom_actual (CConstF aty v) args = (CConstF (arity args) v)
compose_soatom_actual (Proj aty idx) args = error "Projections should not be present in predicates."

compose_soatom_checkarity :: (HasArity pd, HasArity fn) => SOAtom pd fn p t -> [(SOTerm fn t, ArgumentMap)] -> a -> a
compose_soatom_checkarity p args r = if (arity p <= length args) then r else (error ("The arity of the predicate (" ++ (show (arity p)) ++ ") is larger than the number of arguments (" ++ (show (length args)) ++ ")."))

(**.) :: (HasArity pd, HasArity fn) => SOAtom pd fn p t -> [(SOTerm fn t, ArgumentMap)] -> SOAtom pd fn p t
(**.) = compose_soatom


type GroundSOT t fn = SOTerm fn (GroundT t fn)
type GroundSOA a t pd fn = SOAtom pd fn (GroundA a t pd fn) (GroundT t fn)


generic_soatom :: SOAtom pd fn pr fr -> SOAtom pd fn (GenericTermForSO pd pr f) (Fix (GenericTermForSO fn fr))
generic_soatom (ConstF p) = ConstF p
generic_soatom (CompF p sargs) = CompF p (map (\(s,argmap) -> (generic_soterm s,argmap)) sargs)
generic_soatom (CConstF aty v) = CConstF aty (GTFSOBaseR v)
generic_soatom (Proj aty idx) = Proj aty idx

instance {-# OVERLAPPING #-} (Eq pd, Eq fn, Eq pr, Eq fr, HasArity pd, HasArity fn) => Eq (SOAtom pd fn pr fr) where
	p1 == p2 = (apply_soatom GTFSO fixGtfso (generic_soatom p1) (map (Fix . GTFSOBase) [1..(arity p1)])) == (apply_soatom GTFSO fixGtfso (generic_soatom p2) (map (Fix . GTFSOBase) [1..(arity p2)]))

data SOMetawrapperV fn mv = CFunc fn | SOMV mv deriving Eq
type SOMetawrapF t fn v mv = SOTerm (SOMetawrapperV fn mv) (SOMetawrap t fn v mv)
type SOMetawrapper (t :: * -> * -> *) fn v mv f = FlatTerm (t (SOMetawrapF t fn v mv)) v f

instance (Show fn, Show mv) => Show (SOMetawrapperV fn mv) where
	show (CFunc x) = show x
	show (SOMV x) = show x

instance (HasArity fn, HasArity mv) => HasArity (SOMetawrapperV fn mv) where
	arity (CFunc fn) = arity fn
	arity (SOMV mv) = arity mv

data SOMetawrap (t :: * -> * -> *) fn v mv = SOMetawrap (UTerm (t (SOMetawrapF t fn v mv)) v)
fromSOMetawrap :: SOMetawrap t fn v mv -> UTerm (t (SOMetawrapF t fn v mv)) v
fromSOMetawrap (SOMetawrap x) = x

instance (Show v, Show (t (SOMetawrapF t fn v mv) (UTerm (t (SOMetawrapF t fn v mv)) v))) => Show (SOMetawrap t fn v mv) where
	show (SOMetawrap x) = show x

data NormSOMetawrap (t :: * -> * -> *) fn v mv = NSOMetawrap (UTerm (t (SOMetawrapperV fn mv)) v)
fromNormSOMetawrap :: NormSOMetawrap t fn v mv -> UTerm (t (SOMetawrapperV fn mv)) v
fromNormSOMetawrap (NSOMetawrap x) = x

instance (Show v, Show (t (SOMetawrapperV fn mv) (UTerm (t (SOMetawrapperV fn mv)) v))) => Show (NormSOMetawrap t fn v mv) where
	show (NSOMetawrap x) = show x

instance Eq (UTerm (t (SOMetawrapperV fn mv)) v) => Eq (NormSOMetawrap t fn v mv) where
	(NSOMetawrap x1) == (NSOMetawrap x2) = x1 == x2

-- Remove all second-order structure and dump it into the first-order structure.
normalize_metawrap :: SimpleTerm t => SOMetawrap t fn v mv -> NormSOMetawrap t fn v mv
normalize_metawrap (SOMetawrap (UVar v)) = NSOMetawrap (UVar v)
normalize_metawrap (SOMetawrap (UTerm t)) = NSOMetawrap . fromFlippedBifunctor $ (normalize_metawrap_helper (Just h) (map FlippedBifunctor ts)) where (h,ts) = unbuild_term t

normalize_metawrap_helper :: SimpleTerm t => Maybe (SOMetawrapF t fn v mv) -> [FlippedBifunctor UTerm v (t (SOMetawrapF t fn v mv))] -> FlippedBifunctor UTerm v (t (SOMetawrapperV fn mv))
normalize_metawrap_helper Nothing [t] = normalize_metawrap_helper2 t
normalize_metawrap_helper Nothing _ = error "Trying to build a term with no head and multiple arguments. This is multiple terms!"
normalize_metawrap_helper (Just (Fix (ConstF f))) ts = normalize_metawrap_build_term (Just f,map normalize_metawrap_helper2 ts)
normalize_metawrap_helper (Just (Fix (CompF f sargs))) ts = normalize_metawrap_build_term (Just f, rsargs) where rsargs = map (\(g,argmap) -> normalize_metawrap_helper (Just g) (apply_argmap argmap ts)) sargs
normalize_metawrap_helper (Just (Fix (CConstF aty v))) ts = FlippedBifunctor . fromNormSOMetawrap $ (normalize_metawrap v)
normalize_metawrap_helper (Just (Fix (Proj aty idx))) ts = normalize_metawrap_helper Nothing [ts !! idx]

normalize_metawrap_helper2 :: SimpleTerm t => FlippedBifunctor UTerm v (t (SOMetawrapF t fn v mv)) -> FlippedBifunctor UTerm v (t (SOMetawrapperV fn mv))
normalize_metawrap_helper2 = FlippedBifunctor . fromNormSOMetawrap . normalize_metawrap . SOMetawrap . fromFlippedBifunctor

normalize_metawrap_build_term :: SimpleTerm t => (Maybe (SOMetawrapperV fn mv),[FlippedBifunctor UTerm v (t (SOMetawrapperV fn mv))]) -> FlippedBifunctor UTerm v (t (SOMetawrapperV fn mv))
normalize_metawrap_build_term (Nothing,[t]) = t
normalize_metawrap_build_term (Nothing,_) = error "Trying to build a term with no head and multiple arguments. This is multiple terms!"
normalize_metawrap_build_term (Just h,ts) = FlippedBifunctor (UTerm (build_term h (map fromFlippedBifunctor ts)))

-- This only really deals with constant functions that are not explicitly indicated as constants.
normalize_metawrapf :: (SimpleTerm t, HasArity fn, HasArity mv) => SOMetawrapF t fn v mv -> SOMetawrapF t fn v mv
normalize_metawrapf (Fix (CConstF aty idx)) = (Fix (CConstF aty idx))
normalize_metawrapf f | arity f == 0 = Fix (CConstF 0 (SOMetawrap (UTerm (build_term f []))))
normalize_metawrapf x = x

instance (SimpleTerm t, Functor (t (SOMetawrapF t fn v mv)), Functor (t (SOMetawrapperV fn mv)), Eq (UTerm (t (SOMetawrapperV fn mv)) v)) => Eq (SOMetawrap t fn v mv) where
	mw1 == mw2 = (normalize_metawrap mw1 == normalize_metawrap mw2)

type SOMetawrapP a t pd fn v pmv fmv = SOAtom (SOMetawrapperV pd pmv) (SOMetawrapperV fn fmv) (SOMetawrapA a t pd fn v pmv fmv) (SOMetawrap t fn v fmv)

data SOMetawrapA (a :: * -> * -> *) (t :: * -> * -> *) pd fn v pmv fmv = SOMetawrapA (Predicabilize (a (SOMetawrapP a t pd fn v pmv fmv)) (SOMetawrap t fn v fmv))
fromSOMetawrapA :: SOMetawrapA a t pd fn v pmv fmv -> Predicabilize (a (SOMetawrapP a t pd fn v pmv fmv)) (SOMetawrap t fn v fmv)
fromSOMetawrapA (SOMetawrapA x) = x

instance (Show v, Show (t (SOMetawrapF t fn v fmv) (UTerm (t (SOMetawrapF t fn v fmv)) v)), Show (a (SOMetawrapP a t pd fn v pmv fmv) (SOMetawrap t fn v fmv))) => Show (SOMetawrapA a t pd fn v pmv fmv) where
	show (SOMetawrapA x) = show x

instance Eq (Predicabilize (a (SOMetawrapP a t pd fn v pmv fmv)) (SOMetawrap t fn v fmv)) => Eq (SOMetawrapA a t pd fn v pmv fmv) where
	(SOMetawrapA mw1) == (SOMetawrapA mw2) = mw1 == mw2

somw :: Bifunctor t => UTerm (t fn) v -> SOMetawrap t fn v mv
somw (UVar v) = SOMetawrap (UVar v)
somw (UTerm x) = SOMetawrap (UTerm (bimap (Fix . ConstF . CFunc) (fromSOMetawrap . somw) x))

somv :: (Bifunctor t, Functor l, forall xfn. Functor (t xfn)) => (forall xfn a. xfn -> l a -> t xfn a) -> mv -> l (UTerm (t fn) v) -> SOMetawrap t fn v mv
somv build mv args = SOMetawrap (termbuild (Fix . ConstF . SOMV $ mv) (fmap (fromSOMetawrap . somw) args)) where termbuild = build_functor_fix_uterm build

-- Missing: Functions to go from and to metawrap from no meta-variables.


-- Enter unifiers.
type IntBinding t = IntBindingT t Identity

-- I don't get why IntBinding has to necessarily work with IntVars, to be honest, but we can work around it.
newtype IntBindingW t v a = IntBindingW (IntBinding t a) deriving Functor
fromIntBindingW :: IntBindingW t v a -> IntBinding t a
fromIntBindingW (IntBindingW x) = x

instance Applicative (IntBindingW t v) where
	pure x = IntBindingW (pure x)
	a <*> b = IntBindingW ((fromIntBindingW a) <*> (fromIntBindingW b))

instance Monad (IntBindingW t v) where
	a >>= f = IntBindingW ((fromIntBindingW a) >>= (fromIntBindingW . f))

instance (Unifiable t, Variabilizable v, Variable v) => BindingMonad t v (IntBindingW t v) where
	lookupVar x = IntBindingW . (fmap . fmap . fmap $ from_var) $ (lookupVar . get_var $ x)
	freeVar = IntBindingW . (fmap from_var) $ freeVar
	newVar x = IntBindingW . (fmap from_var) $ (newVar . (fmap get_var) $ x)
	bindVar v x = IntBindingW ((bindVar (get_var v)) . (fmap get_var) $ x)

(=:.=) :: (BindingMonad t v m, Functor m, Show v, Show (t (UTerm t v))) => UTerm t v -> UTerm t v -> m (UTerm t v)
t1 =:.= t2 = floatExceptT (unif_exceptt_helper t1 t2)
infix 4 =:.=

unif_exceptt_helper :: BindingMonad t v m => UTerm t v -> UTerm t v -> (ExceptT (UFailure t v) m) (UTerm t v)
unif_exceptt_helper t1 t2 = (t1 =:= t2)



type Unifier t v = IntBindingW t v ()
get_u_value :: (Unifiable t, Variabilizable v, Variable v, Show v, Show (t (UTerm t v))) => Unifier t v -> v -> UTerm t v
get_u_value u v = runIdentity . evalIntBindingT . fromIntBindingW . floatExceptT $ ((lift u) >> (get_u_value_helper v))

get_u_value_helper :: BindingMonad t v m => v -> (ExceptT (UFailure t v) m) (UTerm t v)
get_u_value_helper v = applyBindings (UVar v)

-- We use ExceptT directly because it is just simpler to write. We keep the error class open so that we can include other errors at the higher level of unification. But in principle this shouldn't change things very much.
type MaybeUnifier t v e = (ExceptT e (IntBindingW t v)) ()
(=::=) :: (Unifiable t, Variabilizable v, Variable v) => UTerm t v -> UTerm t v -> MaybeUnifier t v (UFailure t v)
t1 =::= t2 = clear_value (t1 =:= t2)

get_mu_value :: (Unifiable t, Variabilizable v, Variable v, Fallible t v e) => MaybeUnifier t v e -> v -> Maybe (UTerm t v)
get_mu_value u v = get_mu_tvalue u (UVar v)

get_mu_tvalue :: (Unifiable t, Variabilizable v, Variable v, Fallible t v e) => MaybeUnifier t v e -> UTerm t v -> Maybe (UTerm t v)
get_mu_tvalue u t = runIdentity . evalIntBindingT . fromIntBindingW . mb_from_exceptT $ (u >> (applyBindings t))

-- TypeClass indicating something is unifiable and results in a unifier of a certain term/variable type. That's why it has three type parameters
class (Unifiable t, Variabilizable v, Variable v) => DirectlyUnifiable t v s e | s -> t v e where	
	(=.=) :: s -> s -> MaybeUnifier t v e
	infix 4 =.=
	($=) :: MaybeUnifier t v e -> s -> Maybe s
	infix 4 $=

instance (Functor t, Traversable t, Unifiable t, Variabilizable v, Variable v) => DirectlyUnifiable t v (UTerm t v) (UFailure t v) where
	(=.=) = (=::=)
	u $= t = get_mu_tvalue u t

-- No occurs checks may happen at higher levels with this approach.
data DUFailure s e = LowFailure e | HighFailure s s

instance (Show e, Show s) => Show (DUFailure s e) where
	show (LowFailure e) = show e
	show (HighFailure s1 s2) = "Unification error. Could not unify " ++ (show s1) ++ " and " ++ (show s2) ++ "."

with_lowfailure :: Monad m => (ExceptT e m) a -> (ExceptT (DUFailure s e) m) a
with_lowfailure x = ExceptT (fmap (\y -> case y of {Left e -> Left (LowFailure e); Right v -> Right v}) (runExceptT x))

-- These two functions *necessarily* apply the bindings because it is the only way to bring the error outside. This is done, however, lazily of course, so it only happens if the result is pattern matched against.
-- This one returns maybe
reduce_from_highfailure :: (Unifiable t, Variabilizable v, Variable v, Fallible t v e) => MaybeUnifier t v (DUFailure s e) -> ((Maybe (MaybeUnifier t v e)) |: (UTerm t v))
reduce_from_highfailure u = rextensional (\t -> 
						case (runIdentity . evalIntBindingT . fromIntBindingW . mb_from_exceptT $ (u >> (with_lowfailure (applyBindings t)))) of
						{
							Nothing -> Nothing;
							Just v -> Just (withExceptT (\(LowFailure x) -> x) u)
						}
					)

-- This one throws the error
float_from_highfailure :: (Unifiable t, Variabilizable v, Variable v, Fallible t v e, Show e, Show s) => MaybeUnifier t v (DUFailure s e) -> ((MaybeUnifier t v e) |: (UTerm t v))
float_from_highfailure u = rextensional (\t -> 
						case (runIdentity . evalIntBindingT . fromIntBindingW . mb_from_exceptT $ (u >> (with_lowfailure (applyBindings t)))) of
						{
							Nothing -> ExceptT ((runExceptT (u >> (with_lowfailure (applyBindings t)))) >>= (\x -> case x of {Left e -> error (show e); Right y -> return (Right ())}));
							Just v -> (withExceptT (\(LowFailure x) -> x) u)
						}
					)

instance (Functor t, Functor a, Traversable t, Traversable a, Unifiable t, Unifiable a, Variabilizable v, Variable v, DirectlyUnifiable t v (UTerm t v) e, Fallible t v e) => DirectlyUnifiable t v (Predicabilize a (UTerm t v)) (DUFailure (Predicabilize a (UTerm t v)) e) where
	(Atom a1) =.= (Atom a2) = case (zipMatch a1 a2) of 
					{
						Nothing -> ExceptT (return (Left (HighFailure (Atom a1) (Atom a2))));
						Just m -> foldr (\x -> \p -> p >> (case x of
											{
												Left v -> return (); -- No unification needed
												Right (t1,t2) -> with_lowfailure (t1 =.= t2) 
											}
											)) (return ()) m
					}
	(Term t1) =.= (Term t2) = with_lowfailure (t1 =.= t2)
	s1 =.= s2 = ExceptT (return (Left (HighFailure s1 s2)))
	u $= (Atom a) = fmap Atom (traverse (\t -> collapse_mb ((fmap (\v -> v $= t)) $<> ((reduce_from_highfailure u) |: t))) a)
	u $= (Term t) = fmap Term (collapse_mb ((fmap (\v -> v $= t)) $<> ((reduce_from_highfailure u) |: t)))


-- A particular case for applying the unifier extracted from a Predicabilize to a basic term.
($$=) :: (Functor t, Functor a, Traversable t, Traversable a, Unifiable t, Unifiable a, Variabilizable v, Variable v, DirectlyUnifiable t v (UTerm t v) e, Fallible t v e) => MaybeUnifier t v (DUFailure (Predicabilize a (UTerm t v)) e) -> UTerm t v -> Maybe (UTerm t v)
u $$= t = collapse_mb ((fmap ($= t)) $<> ut) where ut = ((reduce_from_highfailure u) |: t)

-- With the following, we can apply term unifiers and atom unifiers indistinctively to terms.

class (Unifiable t, Variabilizable v, Variable v) => SimplyUnifiable t v u | u -> t v where 
	($:=) :: u -> UTerm t v -> Maybe (UTerm t v)

instance (Functor t, Traversable t, Unifiable t, Variabilizable v, Variable v) => SimplyUnifiable t v (MaybeUnifier t v (UFailure t v)) where
	u $:= t = u $= t

instance (Functor t, Traversable t, Unifiable t, Variabilizable v, Variable v, Unifiable a, Functor a) => SimplyUnifiable t v (MaybeUnifier t v (DUFailure (Predicabilize a (UTerm t v)) (UFailure t v))) where
	u $:= t = u $$= t

-- And now back, to apply it to atoms indistinctively.
($$:=) :: (Functor t, Traversable t, Unifiable t, Variabilizable v, Variable v, SimplyUnifiable t v u, Functor a, Traversable a, Unifiable a) => u -> Predicabilize a (UTerm t v) -> Maybe (Predicabilize a (UTerm t v))
u $$:= a = traverse (u $:=) a

-- First-order unifying second-order terms. This is used to merge solutions to second-order variables.
-- Note that constant functions are only unifiable if they are equal: that is why this is "first-order unifying" second-order terms.
instance (Eq fn, Eq r) => Unifiable (SOTermF fn r) where
	zipMatch (ConstF f1) (ConstF f2) | f1 == f2 = Just (ConstF f1)
	zipMatch (CConstF aty1 r1) (CConstF aty2 r2) | r1 == r2 = Just (CConstF (max aty1 aty2) r1)
	zipMatch (Proj aty1 idx1) (Proj aty2 idx2) | idx1 == idx2 = Just (Proj (max aty1 aty2) idx1)
	zipMatch (CompF f1 args1) (CompF f2 args2) | f1 == f2 = fmap (\rargs -> CompF f1 rargs) (traverse (\((f1,argmap1),(f2,argmap2)) -> if (argmap1 == argmap2) then Just (Right (f1,f2), argmap1) else Nothing) (zip args1 args2))








-- And with unifiers, we need to start considering the concept of a signature (variables that are being considered).
data Signature v = Signature {getVars :: [v]}

show_unif :: (Show v, Show (UTerm t v), Unifiable t, Variabilizable v, Variable v) => [v] -> MaybeUnifier t v _ -> String
show_unif vs u = "{" ++ (intercalate "," (map show (fromMaybe [] (traverse (\v -> u $= (UVar v)) vs)))) ++ "}"

doshow_unif :: (Show v, Show (UTerm t v), Unifiable t, Variabilizable v, Variable v) => [v] -> MaybeUnifier t v _ -> IO ()
doshow_unif vs u = putStr ((show_unif vs u) ++ "\n")
