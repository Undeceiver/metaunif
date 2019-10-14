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
{-# LANGUAGE StandaloneDeriving #-}
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

ordFromVar :: Variabilizable t => t -> t -> Bool
ordFromVar a b = (getVarID_gen a) <= (getVarID_gen b)

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
-- Also used for predicate variables
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
--	Syntactically, they are never quantified over, and there are no second-order functions.
-- In other words, they are only function symbols, variable functions and compositions with those, and with the semantic restriction that their interpretation are only elements in the second-order Herbrand universe.
-- Implementation detail: The simplest way to represent compositions of arities greater than 1 is to use lambda abstractions, but we do this by composing with projections whenever necessary The main attractive of this is that we can compare and combine second-order terms without any need for context or without considering alpha-equivalence.

-- ConstF indicates a function corresponding to a constant SYMBOL of second order (but the function is not constant in any way).
data SOTermPF fn p f = ConstF fn | Proj Int | CompF p [f] deriving Eq
newtype SOTermF fn f = SOF (SOTermPF fn f f) deriving Eq

instance Bifunctor (SOTermPF fn) where
	bimap f g (ConstF fn) = ConstF fn
	bimap f g (Proj idx) = Proj idx
	bimap f g (CompF p args) = CompF (f p) (map g args)

instance Functor (SOTermF fn) where
	fmap f (SOF x) = SOF (bimap f f x)

instance Foldable (SOTermF fn) where
	-- foldr :: (a -> b -> b) -> b -> t a -> b
	-- foldr :: (a -> b -> b) -> b -> SOTermF fn a -> b
	foldr _ x (SOF (ConstF _)) = x
	foldr _ x (SOF (Proj idx)) = x
	foldr f x (SOF (CompF g args)) = foldr f (f g x) args

instance Traversable (SOTermF fn) where
	traverse f (SOF (ConstF c)) = pure (SOF (ConstF c))
	traverse f (SOF (Proj idx)) = pure (SOF (Proj idx))
	-- f g :: f b
	-- map f sargs = [f b]
	-- CompF :: a -> ([a] -> SOTermPF fn p a)
	-- (\h -> \ts -> SOF (CompF h ts)) :: ([a] -> SOTermF fn a)	
	-- fmap (\h -> \ts -> SOF (CompF h ts)) (f g) :: f ([b] -> SOTermF fn b)
	-- traverse :: (aa -> ff bb) -> [aa] -> ff [bb]
	-- traverse :: (f b -> f b) -> [f b] -> f [b]
	-- ((fmap (\h -> \ts -> SOF (CompF h ts)) (f g)) <*>) :: f [b] -> f (SOTermF fn b)
	-- traverse id (map f sargs) :: f [b]
	-- (fmap (\h -> \ts -> SOF (CompF h ts)) (f g)) <*> (traverse id (map f sargs)) :: f (SOTermF fn b)
	traverse f (SOF (CompF g sargs)) = (fmap (\h -> \ts -> SOF (CompF h ts)) (f g)) <*> (traverse id (map f sargs))

instance (Show fn, Show p, Show f) => Show (SOTermPF fn p f) where
	show (ConstF fn) = show fn
	show (CompF fn args) = (show fn) ++ "{" ++ (show_as_args (map show args)) ++ "}"
	show (Proj idx) = "pi" ++ (show idx)

instance (Show fn, Show f) => Show (SOTermF fn f) where
	show (SOF x) = show x

instance HasArity x => HasArity [x] where
	arity = foldr (\i -> \m -> max (arity i) m) 0

instance (HasArity fn, HasArity p, HasArity f) => HasArity (SOTermPF fn p f) where
	arity (ConstF x) = arity x
	arity (CompF x args) = arity args
	arity (Proj idx) = (idx + 1)

instance (HasArity fn, HasArity f) => HasArity (SOTermF fn f) where
	arity (SOF x) = arity x

type GroundSOT fn = Fix (SOTermF fn)

instance HasArity fn => HasArity (GroundSOT fn) where
	arity (Fix x) = arity x

type SOTerm fn sov = UTerm (SOTermF fn) sov

instance (HasArity fn, HasArity sov) => HasArity (SOTerm fn sov) where
	arity (UVar v) = arity v
	arity (UTerm t) = arity t

instance (HasArity fn, HasArity sov) => HasArity (FlippedBifunctor UTerm sov (SOTermF fn)) where
	arity x = arity (fromFlippedBifunctor x)

inject_groundsot :: GroundSOT fn -> SOTerm fn sov
inject_groundsot (Fix x) = UTerm (fmap inject_groundsot x)

-- Need to indicate into what structure it gets translated. That is the first (function) argument.
-- Application can only be used on ground second-order terms. Composition can be used on any fixed point.
apply_soterm :: HasArity fn => (fn -> [t] -> t) -> GroundSOT fn -> [t] -> t
apply_soterm c f args = apply_soterm_checkarity ff args (apply_soterm_actual c ff args) where ff = normalize f

apply_soterm_actual :: HasArity fn => (fn -> [t] -> t) -> GroundSOT fn -> [t] -> t
apply_soterm_actual c (Fix (SOF (ConstF f))) args = c f args
-- It is normalized, so the head needs to be a constant function symbol.
apply_soterm_actual c (Fix (SOF (CompF (Fix (SOF (ConstF f))) sargs))) args = c f (map (\s -> apply_soterm c s args) sargs)
apply_soterm_actual c (Fix (SOF (Proj idx))) args = args !! idx

apply_soterm_checkarity :: HasArity fn => GroundSOT fn -> [t] -> a -> a
apply_soterm_checkarity f args r = if (arity f <= length args) then r else (error ("The arity of the function (" ++ (show (arity f)) ++ ") is larger than the number of arguments (" ++ (show (length args)) ++ ")."))

-- Composition of second-order terms
compose_soterm :: (Fixpoint fx, HasArity (fx (SOTermF fn))) => fx (SOTermF fn) -> [fx (SOTermF fn)] -> fx (SOTermF fn)
compose_soterm f args = compose_soterm_checkarity f args (compose_soterm_actual f args)

compose_soterm_actual :: (Fixpoint fx, HasArity (fx (SOTermF fn))) => fx (SOTermF fn) -> [fx (SOTermF fn)] -> fx (SOTermF fn)
compose_soterm_actual f args = fixp (SOF (CompF f args))

compose_soterm_checkarity :: (Fixpoint fx, HasArity (fx (SOTermF fn))) => fx (SOTermF fn) -> [fx (SOTermF fn)] -> a -> a
compose_soterm_checkarity f args r = if (arity f <= length args) then r else (error ("The arity of the function (" ++ (show (arity f)) ++ ") is larger than the number of arguments (" ++ (show (length args)) ++ ")."))

(*.) :: (Fixpoint fx, HasArity (fx (SOTermF fn))) => fx (SOTermF fn) -> [fx (SOTermF fn)] -> fx (SOTermF fn)
(*.) = compose_soterm

(*..) :: (HasArity fn, HasArity sov) => SOTerm fn sov -> [SOTerm fn sov] -> SOTerm fn sov
f *.. args = fromFlippedBifunctor ((FlippedBifunctor f) *. (map FlippedBifunctor args))

-- A ground second-order term is normal if:
--		- It is a constant function.
--		- It is a projection.
--		- It is a composition whose head is a constant function and all its sub-functions are normal.
-- Ideally I would have a separate type for normalized terms, but it's quite a big deal considering how these types are defined with a lot of type parameters.
instance HasArity fn => Normalizable (GroundSOT fn) (GroundSOT fn) where
	inject_normal = id
	normalize (Fix (SOF (ConstF f))) = Fix (SOF (ConstF f))
	normalize (Fix (SOF (Proj idx))) = Fix (SOF (Proj idx))
	normalize (Fix (SOF (CompF h args))) = case (normalize h) of
												{
													(Fix (SOF (ConstF f))) -> Fix (SOF (CompF (Fix (SOF (ConstF f))) (map normalize args)));
													(Fix (SOF (Proj idx))) | idx < length args -> normalize (args !! idx);
													(Fix (SOF (Proj idx))) -> error ("Projection on the " ++ (show idx) ++ "th argument, but only " ++ (show (length args)) ++ " arguments were provided.");
													-- If the normalized head is a composition, we can assume its head is a constant function, and so...
													(Fix (SOF (CompF f args1))) -> Fix (SOF (CompF f (map (normalize . (*. args)) args1)))
												}

instance (HasArity fn, HasArity sov) => Normalizable (SOTerm fn sov) (SOTerm fn sov) where
	inject_normal = id
	normalize (UVar v) = UVar v
	normalize (UTerm (SOF (ConstF f))) = UTerm (SOF (ConstF f))
	normalize (UTerm (SOF (Proj idx))) = UTerm (SOF (Proj idx))
	normalize (UTerm (SOF (CompF h args))) = case (normalize h) of
													{
														(UVar v) -> UTerm (SOF (CompF (UVar v) (map normalize args)));
														(UTerm (SOF (ConstF f))) -> UTerm (SOF (CompF (UTerm (SOF (ConstF f))) (map normalize args)));
														(UTerm (SOF (Proj idx))) | idx < length args -> normalize (args !! idx);
														(UTerm (SOF (Proj idx))) -> error ("Projection on the " ++ (show idx) ++ "th argument, but only " ++ (show (length args)) ++ " arguments were provided.");
														-- If the normalized head is a composition, we can assume its head is a constant function OR a variable, and so...
														(UTerm (SOF (CompF f args1))) -> UTerm (SOF (CompF f (map (normalize . (*.. args)) args1)))
													}



newtype SOTermP pd f p = SOP (SOTermPF pd p f) deriving Eq
type GroundSOA pd fn = Fix (SOTermP pd (GroundSOT fn))
type SOAtom pd fn soav sov = UTerm (SOTermP pd (SOTerm fn sov)) soav

instance Bifunctor (SOTermP pd) where
	bimap f g (SOP sotermpf) = SOP (bimap g f sotermpf)

instance (Show pd, Show f, Show p) => Show (SOTermP pd f p) where
	show (SOP x) = show x

instance (HasArity pd, HasArity p, HasArity f) => HasArity (SOTermP pd f p) where
	arity (SOP x) = arity x

instance (HasArity pd, HasArity fn) => HasArity (GroundSOA pd fn) where
	arity (Fix x) = arity x

instance (HasArity pd, HasArity fn, HasArity soav, HasArity sov) => HasArity (SOAtom pd fn soav sov) where
	arity (UVar v) = arity v
	arity (UTerm t) = arity t

instance (HasArity pd, HasArity fn, HasArity soav, HasArity sov) => HasArity (FlippedBifunctor UTerm soav (SOTermP pd (SOTerm fn sov))) where
	arity x = arity (fromFlippedBifunctor x)

inject_groundsoa :: GroundSOA pd fn -> SOAtom pd fn soav sov
inject_groundsoa (Fix x) = UTerm (bimap inject_groundsot inject_groundsoa x)

apply_soatom :: (HasArity fn, HasArity pd) => (pd -> [t] -> p) -> (fn -> [t] -> t) -> GroundSOA pd fn -> [t] -> p
apply_soatom cp cf p args = apply_soatom_checkarity pp args (apply_soatom_actual cp cf pp args) where pp = normalize p

apply_soatom_actual :: (HasArity fn, HasArity pd) => (pd -> [t] -> p) -> (fn -> [t] -> t) -> GroundSOA pd fn -> [t] -> p
apply_soatom_actual cp cf (Fix (SOP (ConstF p))) args = cp p args
apply_soatom_actual cp cf (Fix (SOP (CompF (Fix (SOP (ConstF p))) sargs))) args = cp p (map (\s -> apply_soterm cf s args) sargs)
apply_soatom_actual cp cf (Fix (SOP (Proj idx))) args = error "Projections should not be present in predicates."

apply_soatom_checkarity :: (HasArity fn, HasArity pd) => GroundSOA pd fn -> [t] -> a -> a
apply_soatom_checkarity p args r = if (arity p <= length args) then r else (error ("The arity of the predicate (" ++ (show (arity p)) ++ ") is larger than the number of arguments (" ++ (show (length args)) ++ ")."))

compose_soatom :: (HasArity pd, HasArity soav, HasArity fn, HasArity sov) => SOAtom pd fn soav sov -> [SOTerm fn sov] -> SOAtom pd fn soav sov
compose_soatom p args = compose_soatom_checkarity p args (compose_soatom_actual p args)

compose_soatom_actual :: (HasArity pd, HasArity soav, HasArity fn, HasArity sov) => SOAtom pd fn soav sov -> [SOTerm fn sov] -> SOAtom pd fn soav sov
compose_soatom_actual (UTerm (SOP (Proj idx))) args = error "Projections should not be present in predicates."
compose_soatom_actual h args = UTerm (SOP (CompF h args))

compose_soatom_checkarity :: (HasArity pd, HasArity soav, HasArity fn, HasArity sov) => SOAtom pd fn soav sov -> [SOTerm fn sov] -> a -> a
compose_soatom_checkarity p args r = if (arity p <= length args) then r else (error ("The arity of the predicate (" ++ (show (arity p)) ++ ") is larger than the number of arguments (" ++ (show (length args)) ++ ")."))

(**.) :: (HasArity pd, HasArity soav, HasArity fn, HasArity sov) => SOAtom pd fn soav sov -> [SOTerm fn sov] -> SOAtom pd fn soav sov
(**.) = compose_soatom


compose_gsoatom :: (HasArity pd, HasArity fn) => GroundSOA pd fn -> [GroundSOT fn] -> GroundSOA pd fn
compose_gsoatom p args = compose_gsoatom_checkarity p args (compose_gsoatom_actual p args)

compose_gsoatom_actual :: (HasArity pd, HasArity fn) => GroundSOA pd fn -> [GroundSOT fn] -> GroundSOA pd fn
compose_gsoatom_actual (Fix (SOP (Proj idx))) args = error "Projections should not be present in predicates."
compose_gsoatom_actual h args = Fix (SOP (CompF h args))

compose_gsoatom_checkarity :: (HasArity pd, HasArity fn) => GroundSOA pd fn -> [GroundSOT fn] -> a -> a
compose_gsoatom_checkarity p args r = if (arity p <= length args) then r else (error ("The arity of the predicate (" ++ (show (arity p)) ++ ") is larger than the number of arguments (" ++ (show (length args)) ++ ")."))


instance (HasArity pd, HasArity fn) => Normalizable (GroundSOA pd fn) (GroundSOA pd fn) where
	inject_normal = id
	normalize (Fix (SOP (ConstF p))) = Fix (SOP (ConstF p))
	normalize (Fix (SOP (Proj idx))) = error "Projections should not be present in predicates."
	normalize (Fix (SOP (CompF h args))) = case (normalize h) of
												{
													(Fix (SOP (ConstF p))) -> Fix (SOP (CompF (Fix (SOP (ConstF p))) (map normalize args)));													
													(Fix (SOP (Proj idx))) -> error "Projections should not be present in predicates.";
													-- If the normalized head is a composition, we can assume its head is a constant predicate, and so...
													(Fix (SOP (CompF p args1))) -> Fix (SOP (CompF p (map (normalize . (*. args)) args1)))
												}

instance (HasArity pd, HasArity soav, HasArity fn, HasArity sov) => Normalizable (SOAtom pd fn soav sov) (SOAtom pd fn soav sov) where
	inject_normal = id
	normalize (UVar v) = UVar v
	normalize (UTerm (SOP (ConstF p))) = UTerm (SOP (ConstF p))
	normalize (UTerm (SOP (Proj idx))) = error "Projections should not be present in predicates."
	normalize (UTerm (SOP (CompF h args))) = case (normalize h) of
													{
														(UVar v) -> UTerm (SOP (CompF (UVar v) (map normalize args)));
														(UTerm (SOP (ConstF p))) -> UTerm (SOP (CompF (UTerm (SOP (ConstF p))) (map normalize args)));
														(UTerm (SOP (Proj idx))) -> error "Projections should not be present in predicates.";
														-- If the normalized head is a composition, we can assume its head is a constant function OR a variable, and so...
														(UTerm (SOP (CompF p args1))) -> UTerm (SOP (CompF p (map (normalize . (*.. args)) args1)))
													}



newtype SOMetawrap (t :: * -> * -> *) fn v mv = SOMetawrap (UTerm (t (SOTerm fn mv)) v)
fromSOMetawrap :: SOMetawrap t fn v mv -> UTerm (t (SOTerm fn mv)) v
fromSOMetawrap (SOMetawrap x) = x

instance (Show v, Show (t (SOTerm fn mv) (UTerm (t (SOTerm fn mv)) v))) => Show (SOMetawrap t fn v mv) where
	show (SOMetawrap x) = show x

deriving instance Eq (UTerm (t (SOTerm fn mv)) v) => Eq (SOMetawrap t fn v mv)
	
-- Remove all second-order structure and dump it into the first-order structure.
instance (HasArity fn, HasArity mv, SimpleTerm t) => Normalizable (SOMetawrap t fn v mv) (SOMetawrap t fn v mv) where
	inject_normal = id
	normalize (SOMetawrap (UVar v)) = SOMetawrap (UVar v)
	normalize (SOMetawrap (UTerm t)) = SOMetawrap . fromFlippedBifunctor $ (normalize_metawrap_helper (Just nh) (map FlippedBifunctor ts)) where (h,ts) = unbuild_term t; nh = normalize h

normalize_metawrap_helper :: (HasArity fn, HasArity mv, SimpleTerm t) => Maybe (SOTerm fn mv) -> [FlippedBifunctor UTerm v (t (SOTerm fn mv))] -> FlippedBifunctor UTerm v (t (SOTerm fn mv))
normalize_metawrap_helper Nothing [t] = normalize_metawrap_helper2 t
normalize_metawrap_helper Nothing _ = error "Trying to build a term with no head and multiple arguments. This is multiple terms!"
normalize_metawrap_helper (Just (UVar sov)) ts = normalize_metawrap_build_term (Just (UVar sov), map normalize_metawrap_helper2 ts)
normalize_metawrap_helper (Just (UTerm (SOF (ConstF f)))) ts = normalize_metawrap_build_term (Just (UTerm (SOF (ConstF f))),map normalize_metawrap_helper2 ts)
normalize_metawrap_helper (Just (UTerm (SOF (Proj idx)))) ts | idx < length ts = normalize_metawrap_helper2 (ts !! idx)
normalize_metawrap_helper (Just (UTerm (SOF (Proj idx)))) ts = error ("Trying to project on the " ++ (show idx) ++ "th argument, but there are only " ++ (show (length ts)) ++ " arguments.")
normalize_metawrap_helper (Just (UTerm (SOF (CompF (UTerm (SOF (ConstF f))) sargs)))) ts = normalize_metawrap_build_term ((Just (UTerm (SOF (ConstF f)))),(map (\g -> normalize_metawrap_helper (Just g) ts) sargs))
normalize_metawrap_helper (Just (UTerm (SOF (CompF (UVar v) sargs)))) ts = normalize_metawrap_build_term ((Just (UVar v)),(map (\g -> normalize_metawrap_helper (Just g) ts) sargs))

normalize_metawrap_helper2 :: (HasArity fn, HasArity mv, SimpleTerm t) => FlippedBifunctor UTerm v (t (SOTerm fn mv)) -> FlippedBifunctor UTerm v (t (SOTerm fn mv))
normalize_metawrap_helper2 = FlippedBifunctor . fromSOMetawrap . normalize . SOMetawrap . fromFlippedBifunctor

normalize_metawrap_build_term :: (HasArity fn, HasArity mv, SimpleTerm t) => (Maybe (SOTerm fn mv),[FlippedBifunctor UTerm v (t (SOTerm fn mv))]) -> FlippedBifunctor UTerm v (t (SOTerm fn mv))
normalize_metawrap_build_term (Nothing,[t]) = t
normalize_metawrap_build_term (Nothing,_) = error "Trying to build a term with no head and multiple arguments. This is multiple terms!"
normalize_metawrap_build_term (Just h,ts) = FlippedBifunctor (UTerm (build_term h (map fromFlippedBifunctor (take (arity h) ts))))

-- With the metawrap, we can indeed apply variable functions.
apply_vsoterm :: (HasArity fn, HasArity mv, SimpleTerm t) => SOTerm fn mv -> [SOMetawrap t fn v mv] -> SOMetawrap t fn v mv
apply_vsoterm f args = apply_vsoterm_checkarity f args (apply_vsoterm_actual f args)

-- The hard work is done in the normalization. Here it is enough to just indicate the application. We do not normalize here yet, it should be done when needed.
apply_vsoterm_actual :: (HasArity fn, HasArity mv, SimpleTerm t) => SOTerm fn mv -> [SOMetawrap t fn v mv] -> SOMetawrap t fn v mv
apply_vsoterm_actual f args = SOMetawrap (UTerm (build_term f (map fromSOMetawrap args)))

apply_vsoterm_checkarity :: (HasArity fn, HasArity mv) => SOTerm fn mv -> [SOMetawrap t fn v mv] -> a -> a
apply_vsoterm_checkarity f args r = if (arity f <= length args) then r else (error ("The arity of the function (" ++ (show (arity f)) ++ ") is larger than the number of arguments (" ++ (show (length args)) ++ ")."))


newtype SOMetawrapA (a :: * -> * -> *) (t :: * -> * -> *) pd fn v pmv fmv = SOMetawrapA (a (SOAtom pd fn pmv fmv) (SOMetawrap t fn v fmv))
fromSOMetawrapA :: SOMetawrapA a t pd fn v pmv fmv -> a (SOAtom pd fn pmv fmv) (SOMetawrap t fn v fmv)
fromSOMetawrapA (SOMetawrapA x) = x

instance Show (a (SOAtom pd fn pmv fmv) (SOMetawrap t fn v fmv)) => Show (SOMetawrapA a t pd fn v pmv fmv) where
	show (SOMetawrapA x) = show x

deriving instance Eq (a (SOAtom pd fn pmv fmv) (SOMetawrap t fn v fmv)) => Eq (SOMetawrapA a t pd fn v pmv fmv)
	
instance (HasArity pd, HasArity fn, HasArity pmv, HasArity fmv, SimpleTerm a, SimpleTerm t) => Normalizable (SOMetawrapA a t pd fn v pmv fmv) (SOMetawrapA a t pd fn v pmv fmv) where
	inject_normal = id
	normalize (SOMetawrapA a) = SOMetawrapA (normalize_metawrapa_helper nh (map (FlippedBifunctor . fromSOMetawrap) ts)) where (h,ts) = unbuild_term a; nh = normalize h

normalize_metawrapa_helper :: (HasArity pd, HasArity fn, HasArity pmv, HasArity fmv, SimpleTerm a, SimpleTerm t) => SOAtom pd fn pmv fmv -> [FlippedBifunctor UTerm v (t (SOTerm fn fmv))] -> a (SOAtom pd fn pmv fmv) (SOMetawrap t fn v fmv)
normalize_metawrapa_helper (UVar soav) ts = normalize_metawrapa_build_atom (UVar soav, map normalize_metawrap_helper2 ts)
normalize_metawrapa_helper (UTerm (SOP (ConstF p))) ts = normalize_metawrapa_build_atom (UTerm (SOP (ConstF p)),map normalize_metawrap_helper2 ts)
normalize_metawrapa_helper (UTerm (SOP (Proj idx))) ts = error "Projections should not be present in predicates"
normalize_metawrapa_helper (UTerm (SOP (CompF (UTerm (SOP (ConstF p))) sargs))) ts = normalize_metawrapa_build_atom (UTerm (SOP (ConstF p)),(map (\g -> normalize_metawrap_helper (Just g) ts) sargs))
normalize_metawrapa_helper (UTerm (SOP (CompF (UVar v) sargs))) ts = normalize_metawrapa_build_atom (UVar v,(map (\g -> normalize_metawrap_helper (Just g) ts) sargs))

--normalize_metawrapa_helper2 :: (HasArity fn, HasArity mv, SimpleTerm t) => FlippedBifunctor UTerm v (t (SOTerm fn mv)) -> FlippedBifunctor UTerm v (t (SOTerm fn mv))

normalize_metawrapa_build_atom :: (HasArity pd, HasArity fn, HasArity pmv, HasArity fmv, SimpleTerm a) => (SOAtom pd fn pmv fmv,[FlippedBifunctor UTerm v (t (SOTerm fn fmv))]) -> a (SOAtom pd fn pmv fmv) (SOMetawrap t fn v fmv)
normalize_metawrapa_build_atom (h,ts) = build_term h (map (SOMetawrap . fromFlippedBifunctor) (take (arity h) ts))


apply_vsoatom :: (HasArity pd, HasArity fn, HasArity pmv, HasArity fmv, SimpleTerm a) => SOAtom pd fn pmv fmv -> [SOMetawrap t fn v fmv] -> SOMetawrapA a t pd fn v pmv fmv
apply_vsoatom p args = apply_vsoatom_checkarity p args (apply_vsoatom_actual p args)

-- The hard work is done in the normalization. Here it is enough to just indicate the application. We do not normalize here yet, it should be done when needed.
apply_vsoatom_actual :: (HasArity pd, HasArity fn, HasArity pmv, HasArity fmv, SimpleTerm a) => SOAtom pd fn pmv fmv -> [SOMetawrap t fn v fmv] -> SOMetawrapA a t pd fn v pmv fmv
apply_vsoatom_actual p args = SOMetawrapA (build_term p args)

apply_vsoatom_checkarity :: (HasArity pd, HasArity fn, HasArity pmv, HasArity fmv) => SOAtom pd fn pmv fmv -> [SOMetawrap t fn v fmv] -> a -> a
apply_vsoatom_checkarity p args r = if (arity p <= length args) then r else (error ("The arity of the predicate (" ++ (show (arity p)) ++ ") is larger than the number of arguments (" ++ (show (length args)) ++ ")."))

somw :: Bifunctor t => UTerm (t fn) v -> SOMetawrap t fn v mv
somw (UVar v) = SOMetawrap (UVar v)
somw (UTerm x) = SOMetawrap (UTerm (bimap (UTerm . SOF . ConstF) (fromSOMetawrap . somw) x))

somv :: (SimpleTerm t) => mv -> [SOMetawrap t fn v mv] -> SOMetawrap t fn v mv
somv mv ts = SOMetawrap (UTerm (build_term (UVar mv) (map fromSOMetawrap ts)))

-- Missing: Ground metawrap terms. If necessary.



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
-- This should only be applied after the second-order terms have been normalized!!! Otherwise it will fail.

instance (Eq fn) => Unifiable (SOTermF fn) where
	zipMatch (SOF (ConstF f1)) (SOF (ConstF f2)) | f1 == f2 = Just (SOF (ConstF f1))
	zipMatch (SOF (Proj idx1)) (SOF (Proj idx2)) | idx1 == idx2 = Just (SOF (Proj idx1))
	zipMatch (SOF (CompF f1 args1)) (SOF (CompF f2 args2)) = Just (SOF (CompF (Right (f1,f2)) (map Right (zip args1 args2))))
	zipMatch _ _ = Nothing







-- And with unifiers, we need to start considering the concept of a signature (variables that are being considered).
data Signature v = Signature {getVars :: [v]}

show_unif :: (Show v, Show (UTerm t v), Unifiable t, Variabilizable v, Variable v) => [v] -> MaybeUnifier t v _ -> String
show_unif vs u = "{" ++ (intercalate "," (map show (fromMaybe [] (traverse (\v -> u $= (UVar v)) vs)))) ++ "}"

doshow_unif :: (Show v, Show (UTerm t v), Unifiable t, Variabilizable v, Variable v) => [v] -> MaybeUnifier t v _ -> IO ()
doshow_unif vs u = putStr ((show_unif vs u) ++ "\n")




class Substitutable t v r where
	subst :: v -> r -> t -> t

-- This allows us to always provide a substitutable instance when there is nothing to substitute.
idsubst :: v -> r -> t -> t
idsubst _ _ = id


--instance (Functor f, Substitutable t v r) => Substitutable (f t) v r where
--	subst v r = fmap (subst v r)
subst_fmap :: (Functor f, Substitutable t v r) => v -> r -> f t -> f t
subst_fmap v r = fmap (subst v r)

