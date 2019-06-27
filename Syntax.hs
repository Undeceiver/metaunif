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

read_term_list :: Read v => String -> ([v],String)
read_term_list = read_term_list_gen '(' ')' ','

read_soterm_list :: Read v => String -> ([v],String)
read_soterm_list = read_term_list_gen '{' '}' ','

read_term_list_gen :: Read v => Char -> Char -> Char -> String -> ([v],String)
read_term_list_gen o c s (x:xs) | x == o = read_term_list_gen o c s xs
read_term_list_gen o c s (x:xs) | x == c = ([],xs)
read_term_list_gen o c s (x:xs) | x == s = read_term_list_gen o c s xs
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

instance HasArity fn => HasArity (SOTermF fn r f) where
	arity (ConstF x) = arity x
	arity (CompF x args) = foldr max 0 (map (\(f,arg) -> arity arg) args)
	arity (CConstF aty _) = aty
	arity (Proj aty _) = aty

type SOTerm fn r = Fix (SOTermF fn r)

instance HasArity fn => HasArity (SOTerm fn r) where
	arity (Fix x) = arity x

-- Need to indicate into what structure it gets translated. That is the first (function) argument.
apply_soterm :: (fn -> [t] -> t) -> SOTerm fn t -> [t] -> t
apply_soterm c (Fix (ConstF f)) args = c f args
apply_soterm c (Fix (CompF f sargs)) args = c f (map (\(s,argmap) -> apply_soterm c s (apply_argmap argmap args)) sargs)
apply_soterm c (Fix (CConstF aty v)) args = v
apply_soterm c (Fix (Proj aty idx)) args = if (idx >= (length args)) then (error ("Projection on the " ++ (show idx) ++ " argument being applied to only " ++ (show (length args)) ++ " arguments.")) else (args !! idx)

apply_argmap :: ArgumentMap -> [a] -> [a]
apply_argmap inds args = map (args !!) inds

-- We do not provide equality checking for the unfixed versions on purpose, to avoid confusion. On the fixed versions, equality could happen even when syntactically they are not the same if the argument maps "cancel" each other.

-- Don't use this directly, please.
data GenericTermForSO fn r f = GTFSO fn [f] | GTFSOBase Int | GTFSOBaseR r deriving (Eq, Ord, Functor, Foldable, Traversable)

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

apply_soatom :: (pd -> [t] -> p) -> (fn -> [t] -> t) -> SOAtom pd fn p t -> [t] -> p
apply_soatom cp cf (ConstF p) args = cp p args
apply_soatom cp cf (CompF p sargs) args = cp p (map (\(s,argmap) -> apply_soterm cf s (apply_argmap argmap args)) sargs)
apply_soatom cp cf (CConstF aty v) args = v
apply_soatom cp cf (Proj aty idx) args = error "Projections should not be present in predicates."

generic_soatom :: SOAtom pd fn pr fr -> SOAtom pd fn (GenericTermForSO pd pr f) (Fix (GenericTermForSO fn fr))
generic_soatom (ConstF p) = ConstF p
generic_soatom (CompF p sargs) = CompF p (map (\(s,argmap) -> (generic_soterm s,argmap)) sargs)
generic_soatom (CConstF aty v) = CConstF aty (GTFSOBaseR v)
generic_soatom (Proj aty idx) = Proj aty idx

instance {-# OVERLAPPING #-} (Eq pd, Eq fn, Eq pr, Eq fr, HasArity pd, HasArity fn) => Eq (SOAtom pd fn pr fr) where
	p1 == p2 = (apply_soatom GTFSO fixGtfso (generic_soatom p1) (map (Fix . GTFSOBase) [1..(arity p1)])) == (apply_soatom GTFSO fixGtfso (generic_soatom p2) (map (Fix . GTFSOBase) [1..(arity p2)]))

data SOMetawrapperV fn mv = CFunc fn | SOMV mv
type SOMetawrapF t fn v mv = SOTerm (SOMetawrapperV fn mv) (SOMetawrap t fn v mv)
type SOMetawrapper (t :: * -> * -> *) fn v mv f = FlatTerm (t (SOMetawrapF t fn v mv)) v f

instance (Show fn, Show mv) => Show (SOMetawrapperV fn mv) where
	show (CFunc x) = show x
	show (SOMV x) = show x

data SOMetawrap (t :: * -> * -> *) fn v mv = SOMetawrap (UTerm (t (SOMetawrapF t fn v mv)) v)
fromSOMetawrap :: SOMetawrap t fn v mv -> UTerm (t (SOMetawrapF t fn v mv)) v
fromSOMetawrap (SOMetawrap x) = x

instance (Show v, Show (t (SOMetawrapF t fn v mv) (UTerm (t (SOMetawrapF t fn v mv)) v))) => Show (SOMetawrap t fn v mv) where
	show (SOMetawrap x) = show x

type SOMetawrapP a t pd fn v pmv fmv = SOAtom (SOMetawrapperV pd pmv) (SOMetawrapperV fn fmv) (SOMetawrapA a t pd fn v pmv fmv) (SOMetawrap t fn v fmv)

data SOMetawrapA (a :: * -> * -> *) (t :: * -> * -> *) pd fn v pmv fmv = SOMetawrapA (Predicabilize (a (SOMetawrapP a t pd fn v pmv fmv)) (SOMetawrap t fn v fmv))
fromSOMetawrapA :: SOMetawrapA a t pd fn v pmv fmv -> Predicabilize (a (SOMetawrapP a t pd fn v pmv fmv)) (SOMetawrap t fn v fmv)
fromSOMetawrapA (SOMetawrapA x) = x

instance (Show v, Show (t (SOMetawrapF t fn v fmv) (UTerm (t (SOMetawrapF t fn v fmv)) v)), Show (a (SOMetawrapP a t pd fn v pmv fmv) (SOMetawrap t fn v fmv))) => Show (SOMetawrapA a t pd fn v pmv fmv) where
	show (SOMetawrapA x) = show x

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

(=::=) :: (BindingMonad t v m, Functor m, Show v, Show (t (UTerm t v))) => UTerm t v -> UTerm t v -> m (UTerm t v)
t1 =::= t2 = floatExceptT (unif_exceptt_helper t1 t2)
infix 4 =::=

unif_exceptt_helper :: BindingMonad t v m => UTerm t v -> UTerm t v -> (ExceptT (UFailure t v) m) (UTerm t v)
unif_exceptt_helper t1 t2 = (t1 =:= t2)



type Unifier t v = IntBindingW t v ()
get_u_value :: (Unifiable t, Variabilizable v, Variable v, Show v, Show (t (UTerm t v))) => Unifier t v -> v -> UTerm t v
get_u_value u v = runIdentity . evalIntBindingT . fromIntBindingW . floatExceptT $ ((lift u) >> (get_u_value_helper v))

get_u_value_helper :: BindingMonad t v m => v -> (ExceptT (UFailure t v) m) (UTerm t v)
get_u_value_helper v = applyBindings (UVar v)

-- And with unifiers, we need to start considering the concept of a signature (variables that are being considered).
