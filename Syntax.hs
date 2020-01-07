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
import Data.Map.Strict
import EnumProc
import qualified Control.Lens

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

class HasArity t => ChangeArity t where
	change_arity :: t -> Int -> t

-- An instance through functors
newtype FoldableArity f t = FoldableArity {fromFoldableArity :: f t}

instance (HasArity t, Foldable f, Functor f) => HasArity (FoldableArity f t) where
	arity = (Prelude.foldr max 0) . (fmap arity) . fromFoldableArity
	

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

-- Find all variables present in a term
find_vars :: (Foldable t, Eq v) => UTerm t v -> [v]
find_vars (UVar v) = [v]
find_vars (UTerm t) = nub (foldMap find_vars t)

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
inject_groundt :: Functor (t fn) => GroundT t fn -> UTerm (t fn) v
inject_groundt (Fix t) = UTerm (fmap inject_groundt t)

type GroundA a t pd fn = a pd (GroundT t fn)
inject_grounda :: (Functor (a pd), Functor (t fn)) => GroundA a t pd fn -> a pd (UTerm (t fn) v)
inject_grounda = fmap inject_groundt

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
-- Implementation detail: The simplest way to represent compositions of arities greater than 1 is to use lambda abstractions, but we do this by composing with projections whenever necessary. The main attractive of this is that we can compare and combine second-order terms without any need for context or without considering alpha-equivalence.

-- Traversal for the second-order elements of a UTerm
fntraverse :: (Applicative f, SimpleTerm t) => (fn -> f fnb) -> UTerm (t fn) v -> f (UTerm (t fnb) v)
fntraverse f (UVar v) = pure (UVar v)
fntraverse f (UTerm t) = UTerm <$> ((pure build_term) <*> frfn <*> rec) where (fn,sts) = unbuild_term t; frfn = f fn; rec = traverse (fntraverse f) sts

fntraversal :: SimpleTerm t => Control.Lens.Traversal (UTerm (t fn) v) (UTerm (t fnb) v) fn fnb
fntraversal = fntraverse

-- ConstF indicates a function corresponding to a constant SYMBOL of second order (but the function is not constant in any way).
data SOTermPF fn p f = ConstF fn | Proj Int | CompF p [f] deriving Eq
newtype SOTermF fn f = SOF (SOTermPF fn f f) deriving Eq

instance Bifunctor (SOTermPF fn) where
	bimap f g (ConstF fn) = ConstF fn
	bimap f g (Proj idx) = Proj idx
	bimap f g (CompF p args) = CompF (f p) (Prelude.map g args)

instance Functor (SOTermF fn) where
	fmap f (SOF x) = SOF (bimap f f x)

instance Foldable (SOTermF fn) where
	-- foldr :: (a -> b -> b) -> b -> t a -> b
	-- foldr :: (a -> b -> b) -> b -> SOTermF fn a -> b
	foldr _ x (SOF (ConstF _)) = x
	foldr _ x (SOF (Proj idx)) = x
	foldr f x (SOF (CompF g args)) = Prelude.foldr f (f g x) args

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
	traverse f (SOF (CompF g sargs)) = (fmap (\h -> \ts -> SOF (CompF h ts)) (f g)) <*> (traverse id (Prelude.map f sargs))

instance (Show fn, Show p, Show f) => Show (SOTermPF fn p f) where
	show (ConstF fn) = show fn
	show (CompF fn args) = (show fn) ++ "{" ++ (show_as_args (Prelude.map show args)) ++ "}"
	show (Proj idx) = "pi" ++ (show idx)

instance (Show fn, Show f) => Show (SOTermF fn f) where
	show (SOF x) = show x

instance HasArity x => HasArity [x] where
	arity = Prelude.foldr (\i -> \m -> max (arity i) m) 0

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

-- Dummy second-order variable type used when using inject_groundsot. Its entire purpose is that it can be an instance of any class, because its methods will never be used.
newtype DummySOV = DummySOV ()

instance HasArity DummySOV where
	arity = undefined


-- Need to indicate into what structure it gets translated. That is the first (function) argument.
-- Application can only be used on ground second-order terms. Composition can be used on any fixed point.
apply_soterm :: HasArity fn => (fn -> [t] -> t) -> GroundSOT fn -> [t] -> t
apply_soterm c f args = apply_soterm_checkarity ff args (apply_soterm_actual c ff args) where ff = normalize f

apply_soterm_actual :: HasArity fn => (fn -> [t] -> t) -> GroundSOT fn -> [t] -> t
apply_soterm_actual c (Fix (SOF (ConstF f))) args = c f args
-- It is normalized, so the head needs to be a constant function symbol.
apply_soterm_actual c (Fix (SOF (CompF (Fix (SOF (ConstF f))) sargs))) args = c f (Prelude.map (\s -> apply_soterm c s args) sargs)
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
f *.. args = fromFlippedBifunctor ((FlippedBifunctor f) *. (Prelude.map FlippedBifunctor args))

-- A ground second-order term is normal if:
--		- (REMOVED) It is a constant function: Constant functions are left as a composition of a function with projections. Making constant functions different from compositions with projections made for false inequalities between functions.
--		- It is a projection.
--		- It is a composition whose head is a constant function and all its sub-functions are normal.
-- Ideally I would have a separate type for normalized terms, but it's quite a big deal considering how these types are defined with a lot of type parameters.
instance HasArity fn => Normalizable (GroundSOT fn) (GroundSOT fn) where
	inject_normal = id
	normalize (Fix (SOF (ConstF f))) = Fix (SOF (CompF (Fix (SOF (ConstF f))) (fmap (Fix . SOF . Proj) [0..((arity f) - 1)])))
	normalize (Fix (SOF (Proj idx))) = Fix (SOF (Proj idx))
	normalize (Fix (SOF (CompF h args))) = case (normalize h) of
												{
													(Fix (SOF (ConstF f))) -> Fix (SOF (CompF (Fix (SOF (ConstF f))) (Prelude.map normalize args)));
													(Fix (SOF (Proj idx))) | idx < length args -> normalize (args !! idx);
													(Fix (SOF (Proj idx))) -> error ("Projection on the " ++ (show idx) ++ "th argument, but only " ++ (show (length args)) ++ " arguments were provided.");
													-- If the normalized head is a composition, we can assume its head is a constant function, and so...
													(Fix (SOF (CompF f args1))) -> Fix (SOF (CompF f (Prelude.map (normalize . (*. args)) args1)))
												}

instance (HasArity fn, HasArity sov) => Normalizable (SOTerm fn sov) (SOTerm fn sov) where
	inject_normal = id
	normalize (UVar v) = UVar v
	normalize (UTerm (SOF (ConstF f))) = UTerm (SOF (CompF (UTerm (SOF (ConstF f))) (fmap (UTerm . SOF . Proj) [0..((arity f) - 1)])))
	normalize (UTerm (SOF (Proj idx))) = UTerm (SOF (Proj idx))
	normalize (UTerm (SOF (CompF h args))) = case (normalize h) of
													{
														(UVar v) -> UTerm (SOF (CompF (UVar v) (Prelude.map normalize args)));
														(UTerm (SOF (ConstF f))) -> UTerm (SOF (CompF (UTerm (SOF (ConstF f))) (Prelude.map normalize args)));
														(UTerm (SOF (Proj idx))) | idx < length args -> normalize (args !! idx);
														(UTerm (SOF (Proj idx))) -> error ("Projection on the " ++ (show idx) ++ "th argument, but only " ++ (show (length args)) ++ " arguments were provided.");
														-- If the normalized head is a composition, we can assume its head is a constant function OR a variable, and so...
														(UTerm (SOF (CompF f args1))) -> UTerm (SOF (CompF f (Prelude.map (normalize . (*.. args)) args1)))
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
apply_soatom_actual cp cf (Fix (SOP (CompF (Fix (SOP (ConstF p))) sargs))) args = cp p (Prelude.map (\s -> apply_soterm cf s args) sargs)
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
													(Fix (SOP (ConstF p))) -> Fix (SOP (CompF (Fix (SOP (ConstF p))) (Prelude.map normalize args)));													
													(Fix (SOP (Proj idx))) -> error "Projections should not be present in predicates.";
													-- If the normalized head is a composition, we can assume its head is a constant predicate, and so...
													(Fix (SOP (CompF p args1))) -> Fix (SOP (CompF p (Prelude.map (normalize . (*. args)) args1)))
												}

instance (HasArity pd, HasArity soav, HasArity fn, HasArity sov) => Normalizable (SOAtom pd fn soav sov) (SOAtom pd fn soav sov) where
	inject_normal = id
	normalize (UVar v) = UVar v
	normalize (UTerm (SOP (ConstF p))) = UTerm (SOP (ConstF p))
	normalize (UTerm (SOP (Proj idx))) = error "Projections should not be present in predicates."
	normalize (UTerm (SOP (CompF h args))) = case (normalize h) of
													{
														(UVar v) -> UTerm (SOP (CompF (UVar v) (Prelude.map normalize args)));
														(UTerm (SOP (ConstF p))) -> UTerm (SOP (CompF (UTerm (SOP (ConstF p))) (Prelude.map normalize args)));
														(UTerm (SOP (Proj idx))) -> error "Projections should not be present in predicates.";
														-- If the normalized head is a composition, we can assume its head is a constant function OR a variable, and so...
														(UTerm (SOP (CompF p args1))) -> UTerm (SOP (CompF p (Prelude.map (normalize . (*.. args)) args1)))
													}



newtype SOMetawrap (t :: * -> * -> *) fn v mv = SOMetawrap {fromSOMetawrap :: UTerm (t (SOTerm fn mv)) v}

-- These following "tricks" are a consequence of being unable to produce the normalization algorithm for SOMetawrap for generic function and term types, which was a huge pain that we ended up giving up on.
-- This type is only briefly used for small things so we don't provide all that we provide for SOMetawrap.
newtype GSOMetawrap (t :: * -> * -> *) fn v = GSOMetawrap {fromGSOMetawrap :: UTerm (t (GroundSOT fn)) v}
gsomw :: (HasArity fn, SimpleTerm t) => UTerm (t fn) v -> GSOMetawrap t fn v
gsomw (UVar v) = GSOMetawrap (UVar v)
gsomw (UTerm t) = GSOMetawrap (UTerm (build_term (Fix (SOF (ConstF h))) (fromGSOMetawrap . gsomw <$> args))) where (h,args) = unbuild_term t

plain_gsomw :: (HasArity fn, SimpleTerm t) => GSOMetawrap t fn v -> UTerm (t fn) v
plain_gsomw x = plain_gsomw_norm . fromGSOMetawrap . normalize $ x

plain_gsomw_norm :: (HasArity fn, SimpleTerm t) => UTerm (t (GroundSOT fn)) v -> UTerm (t fn) v
plain_gsomw_norm (UVar v) = UVar v
plain_gsomw_norm (UTerm t) = (case h of {Fix (SOF (ConstF fn)) -> UTerm (build_term fn (plain_gsomw_norm <$> args))}) where (h,args) = unbuild_term t

-- Similar situation.
newtype GGSOMetawrap (t :: * -> * -> *) fn = GGSOMetawrap {fromGGSOMetawrap :: Fix (t (GroundSOT fn))}
ggsomw :: (HasArity fn, SimpleTerm t) => GroundT t fn -> GGSOMetawrap t fn
ggsomw (Fix t) = GGSOMetawrap (Fix (build_term (Fix (SOF (ConstF h))) (fromGGSOMetawrap . ggsomw <$> args))) where (h,args) = unbuild_term t

ggsomw_to_gsomw :: Functor (t (GroundSOT fn)) => GGSOMetawrap t fn -> GSOMetawrap t fn v
ggsomw_to_gsomw (GGSOMetawrap (Fix x)) = GSOMetawrap (UTerm (fromGSOMetawrap . ggsomw_to_gsomw . GGSOMetawrap <$> x))

gsomw_to_ggsomw :: Functor (t (GroundSOT fn)) => GSOMetawrap t fn v -> GGSOMetawrap t fn
gsomw_to_ggsomw (GSOMetawrap (UVar v)) = error "Variable in doubly ground metawrap!"
gsomw_to_ggsomw (GSOMetawrap (UTerm x)) = GGSOMetawrap (Fix (fromGGSOMetawrap . gsomw_to_ggsomw . GSOMetawrap <$> x))

groundt_to_ggsomw :: Bifunctor t => GroundT t fn -> GGSOMetawrap t fn
groundt_to_ggsomw (Fix t) = GGSOMetawrap (Fix (bimap (Fix . SOF . ConstF) (fromGGSOMetawrap . groundt_to_ggsomw) t))

ggsomw_to_groundt :: Bifunctor t => GGSOMetawrap t fn -> GroundT t fn
ggsomw_to_groundt (GGSOMetawrap (Fix t)) = Fix (bimap (\(Fix (SOF (ConstF fn))) -> fn) (ggsomw_to_groundt . GGSOMetawrap) t)

plain_ggsomw :: (HasArity fn, SimpleTerm t, Functor (t (GroundSOT fn))) => GGSOMetawrap t fn -> GroundT t fn
plain_ggsomw x = plain_ggsomw_norm . fromGGSOMetawrap . normalize $ x

plain_ggsomw_norm :: (HasArity fn, SimpleTerm t, Functor (t (GroundSOT fn))) => Fix (t (GroundSOT fn)) -> GroundT t fn
plain_ggsomw_norm (Fix t) = (case h of {Fix (SOF (ConstF fn)) -> Fix (build_term fn (plain_ggsomw_norm <$> args))}) where (h,args) = unbuild_term t

-- Tools doing something equivalent to the above but without the extra types.
absorb_groundsot_into_groundt :: forall t fn. (HasArity fn, SimpleTerm t, Bifunctor t, Functor (t fn)) => t (GroundSOT fn) (GroundT t fn) -> t fn (GroundT t fn)
absorb_groundsot_into_groundt t = absorb_groundsot_into_groundt_norm normalized where tosomw = SOMetawrap . UTerm $ (bimap (inject_groundsot :: GroundSOT fn -> SOTerm fn DummySOV) (fromSOMetawrap . somw . inject_groundt) t); normalized = normalize tosomw

absorb_groundsot_into_groundt_norm :: (HasArity fn, SimpleTerm t, Bifunctor t, Functor (t fn)) => SOMetawrap t fn v sov -> t fn (GroundT t fn)
-- We purposely do not include the variable case, because it may not appear if used through the above function!
absorb_groundsot_into_groundt_norm (SOMetawrap (UTerm t)) = build_term rh rargs	where (h,args) = unbuild_term t; rh = case h of {UTerm (SOF (ConstF fn)) -> fn}; rargs = fmap (Fix . absorb_groundsot_into_groundt_norm . SOMetawrap) args



instance (Show v, Show (t (SOTerm fn mv) (UTerm (t (SOTerm fn mv)) v))) => Show (SOMetawrap t fn v mv) where
	show (SOMetawrap x) = show x

deriving instance Eq (UTerm (t (SOTerm fn mv)) v) => Eq (SOMetawrap t fn v mv)
	
-- Remove all second-order structure and dump it into the first-order structure.
instance (HasArity fn, HasArity mv, SimpleTerm t) => Normalizable (SOMetawrap t fn v mv) (SOMetawrap t fn v mv) where
	inject_normal = id
	normalize (SOMetawrap (UVar v)) = SOMetawrap (UVar v)
	normalize (SOMetawrap (UTerm t)) = SOMetawrap . fromFlippedBifunctor $ (normalize_metawrap_helper (Just nh) (Prelude.map FlippedBifunctor ts)) where (h,ts) = unbuild_term t; nh = normalize h

normalize_metawrap_helper :: (HasArity fn, HasArity mv, SimpleTerm t) => Maybe (SOTerm fn mv) -> [FlippedBifunctor UTerm v (t (SOTerm fn mv))] -> FlippedBifunctor UTerm v (t (SOTerm fn mv))
normalize_metawrap_helper Nothing [t] = normalize_metawrap_helper2 t
normalize_metawrap_helper Nothing _ = error "Trying to build a term with no head and multiple arguments. This is multiple terms!"
normalize_metawrap_helper (Just (UVar sov)) ts = normalize_metawrap_build_term (Just (UVar sov), Prelude.map normalize_metawrap_helper2 ts)
normalize_metawrap_helper (Just (UTerm (SOF (ConstF f)))) ts = normalize_metawrap_build_term (Just (UTerm (SOF (ConstF f))),Prelude.map normalize_metawrap_helper2 ts)
normalize_metawrap_helper (Just (UTerm (SOF (Proj idx)))) ts | idx < length ts = normalize_metawrap_helper2 (ts !! idx)
normalize_metawrap_helper (Just (UTerm (SOF (Proj idx)))) ts = error ("Trying to project on the " ++ (show idx) ++ "th argument, but there are only " ++ (show (length ts)) ++ " arguments.")
normalize_metawrap_helper (Just (UTerm (SOF (CompF (UTerm (SOF (ConstF f))) sargs)))) ts = normalize_metawrap_build_term ((Just (UTerm (SOF (ConstF f)))),(Prelude.map (\g -> normalize_metawrap_helper (Just g) ts) sargs))
normalize_metawrap_helper (Just (UTerm (SOF (CompF (UVar v) sargs)))) ts = normalize_metawrap_build_term ((Just (UVar v)),(Prelude.map (\g -> normalize_metawrap_helper (Just g) ts) sargs))

normalize_metawrap_helper2 :: (HasArity fn, HasArity mv, SimpleTerm t) => FlippedBifunctor UTerm v (t (SOTerm fn mv)) -> FlippedBifunctor UTerm v (t (SOTerm fn mv))
normalize_metawrap_helper2 = FlippedBifunctor . fromSOMetawrap . normalize . SOMetawrap . fromFlippedBifunctor

normalize_metawrap_build_term :: (HasArity fn, HasArity mv, SimpleTerm t) => (Maybe (SOTerm fn mv),[FlippedBifunctor UTerm v (t (SOTerm fn mv))]) -> FlippedBifunctor UTerm v (t (SOTerm fn mv))
normalize_metawrap_build_term (Nothing,[t]) = t
normalize_metawrap_build_term (Nothing,_) = error "Trying to build a term with no head and multiple arguments. This is multiple terms!"
normalize_metawrap_build_term (Just h,ts) = FlippedBifunctor (UTerm (build_term h (Prelude.map fromFlippedBifunctor (Prelude.take (arity h) ts))))

-- Equivalent for GroundSOT-based elements. Ideally we would have done this generically for any fixed point operator, but that did not work out very well for various reasons.
instance (HasArity fn, SimpleTerm t) => Normalizable (GSOMetawrap t fn v) (GSOMetawrap t fn v) where
	inject_normal = id
	normalize (GSOMetawrap (UVar v)) = GSOMetawrap (UVar v)
	normalize (GSOMetawrap (UTerm t)) = GSOMetawrap . fromFlippedBifunctor $ (normalize_groundsotwrap_helper (Just nh) (Prelude.map FlippedBifunctor ts)) where (h,ts) = unbuild_term t; nh = normalize h

instance (HasArity fn, SimpleTerm t, Functor (t (GroundSOT fn))) => Normalizable (GGSOMetawrap t fn) (GGSOMetawrap t fn) where
	inject_normal = id
	normalize = gsomw_to_ggsomw . normalize . ggsomw_to_gsomw

-- We can use this to normalize ground terms, but the instance is too generic

normalize_groundt :: (HasArity fn, SimpleTerm t, Functor (t (GroundSOT fn)), Bifunctor t) => GroundT t fn -> GroundT t fn
normalize_groundt = ggsomw_to_groundt . normalize . groundt_to_ggsomw

normalize_groundsotwrap_helper :: (HasArity fn, SimpleTerm t) => Maybe (GroundSOT fn) -> [FlippedBifunctor UTerm v (t (GroundSOT fn))] -> FlippedBifunctor UTerm v (t (GroundSOT fn))
normalize_groundsotwrap_helper Nothing [t] = normalize_groundsotwrap_helper2 t
normalize_groundsotwrap_helper Nothing _ = error "Trying to build a term with no head and multiple arguments. This is multiple terms!"
normalize_groundsotwrap_helper (Just (Fix (SOF (ConstF f)))) ts = normalize_groundsotwrap_build_term (Just (Fix (SOF (ConstF f))),Prelude.map normalize_groundsotwrap_helper2 ts)
normalize_groundsotwrap_helper (Just (Fix (SOF (Proj idx)))) ts | idx < length ts = normalize_groundsotwrap_helper2 (ts !! idx)
normalize_groundsotwrap_helper (Just (Fix (SOF (Proj idx)))) ts = error ("Trying to project on the " ++ (show idx) ++ "th argument, but there are only " ++ (show (length ts)) ++ " arguments.")
normalize_groundsotwrap_helper (Just (Fix (SOF (CompF (Fix (SOF (ConstF f))) sargs)))) ts = normalize_groundsotwrap_build_term ((Just (Fix (SOF (ConstF f)))),(Prelude.map (\g -> normalize_groundsotwrap_helper (Just g) ts) sargs))

normalize_groundsotwrap_helper2 :: (HasArity fn, SimpleTerm t) => FlippedBifunctor UTerm v (t (GroundSOT fn)) -> FlippedBifunctor UTerm v (t (GroundSOT fn))
normalize_groundsotwrap_helper2 = FlippedBifunctor . fromGSOMetawrap . normalize . GSOMetawrap . fromFlippedBifunctor

normalize_groundsotwrap_build_term :: (HasArity fn, SimpleTerm t) => (Maybe (GroundSOT fn),[FlippedBifunctor UTerm v (t (GroundSOT fn))]) -> FlippedBifunctor UTerm v (t (GroundSOT fn))
normalize_groundsotwrap_build_term (Nothing,[t]) = t
normalize_groundsotwrap_build_term (Nothing,_) = error "Trying to build a term with no head and multgiple arguments. This is multiple terms!"
normalize_groundsotwrap_build_term (Just h,ts) = FlippedBifunctor (UTerm (build_term h (Prelude.map fromFlippedBifunctor (Prelude.take (arity h) ts))))


-- With the metawrap, we can indeed apply variable functions.
apply_vsoterm :: (HasArity fn, HasArity mv, SimpleTerm t) => SOTerm fn mv -> [SOMetawrap t fn v mv] -> SOMetawrap t fn v mv
apply_vsoterm f args = apply_vsoterm_checkarity f args (apply_vsoterm_actual f args)

-- The hard work is done in the normalization. Here it is enough to just indicate the application. We do not normalize here yet, it should be done when needed.
apply_vsoterm_actual :: (HasArity fn, HasArity mv, SimpleTerm t) => SOTerm fn mv -> [SOMetawrap t fn v mv] -> SOMetawrap t fn v mv
apply_vsoterm_actual f args = SOMetawrap (UTerm (build_term f (Prelude.map fromSOMetawrap args)))

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
	normalize (SOMetawrapA a) = SOMetawrapA (normalize_metawrapa_helper nh (Prelude.map (FlippedBifunctor . fromSOMetawrap) ts)) where (h,ts) = unbuild_term a; nh = normalize h

normalize_metawrapa_helper :: (HasArity pd, HasArity fn, HasArity pmv, HasArity fmv, SimpleTerm a, SimpleTerm t) => SOAtom pd fn pmv fmv -> [FlippedBifunctor UTerm v (t (SOTerm fn fmv))] -> a (SOAtom pd fn pmv fmv) (SOMetawrap t fn v fmv)
normalize_metawrapa_helper (UVar soav) ts = normalize_metawrapa_build_atom (UVar soav, Prelude.map normalize_metawrap_helper2 ts)
normalize_metawrapa_helper (UTerm (SOP (ConstF p))) ts = normalize_metawrapa_build_atom (UTerm (SOP (ConstF p)),Prelude.map normalize_metawrap_helper2 ts)
normalize_metawrapa_helper (UTerm (SOP (Proj idx))) ts = error "Projections should not be present in predicates"
normalize_metawrapa_helper (UTerm (SOP (CompF (UTerm (SOP (ConstF p))) sargs))) ts = normalize_metawrapa_build_atom (UTerm (SOP (ConstF p)),(Prelude.map (\g -> normalize_metawrap_helper (Just g) ts) sargs))
normalize_metawrapa_helper (UTerm (SOP (CompF (UVar v) sargs))) ts = normalize_metawrapa_build_atom (UVar v,(Prelude.map (\g -> normalize_metawrap_helper (Just g) ts) sargs))

--normalize_metawrapa_helper2 :: (HasArity fn, HasArity mv, SimpleTerm t) => FlippedBifunctor UTerm v (t (SOTerm fn mv)) -> FlippedBifunctor UTerm v (t (SOTerm fn mv))

normalize_metawrapa_build_atom :: (HasArity pd, HasArity fn, HasArity pmv, HasArity fmv, SimpleTerm a) => (SOAtom pd fn pmv fmv,[FlippedBifunctor UTerm v (t (SOTerm fn fmv))]) -> a (SOAtom pd fn pmv fmv) (SOMetawrap t fn v fmv)
normalize_metawrapa_build_atom (h,ts) = build_term h (Prelude.map (SOMetawrap . fromFlippedBifunctor) (Prelude.take (arity h) ts))


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
somv mv ts = SOMetawrap (UTerm (build_term (UVar mv) (Prelude.map fromSOMetawrap ts)))

-- First-order atoms in which the universe of discourse are second-order atoms.
-- We provide a very simple case, which is the one we need: Only second-order predicates (no functions) and only applied on object-level predicates (not functions, although the predicates could be composites containing functions).
-- We allow the inclusion of an additional inner layer in the first-second-order predicates. This will likely be a lambda-CNF structure, allowing to express properties of conjunctions, disjunctions, negations and the like. But we try to keep it parametric at this level for now. This is represented by the s type parameter.
newtype FirstSOAAtom (a :: * -> * -> *) (s :: * -> *) mpd pd fn pmv fmv = FirstSOAAtom {fromFirstSOAAtom :: a mpd (s (SOAtom pd fn pmv fmv))}

instance Show (a mpd (s (SOAtom pd fn pmv fmv))) => Show (FirstSOAAtom a s mpd pd fn pmv fmv) where
	show (FirstSOAAtom x) = show x

deriving instance Eq (a mpd (s (SOAtom pd fn pmv fmv))) => Eq (FirstSOAAtom a s mpd pd fn pmv fmv)

instance (HasArity pd, HasArity pmv, HasArity fn, HasArity fmv, Functor (a mpd), Functor s) => Normalizable (FirstSOAAtom a s mpd pd fn pmv fmv) (FirstSOAAtom a s mpd pd fn pmv fmv) where
	inject_normal = id
	normalize (FirstSOAAtom x) = FirstSOAAtom (fmap (fmap normalize) x)


data CombSOAtom (a :: * -> * -> *) (t :: * -> * -> *) (s :: * -> *) mpd pd fn v pmv fmv = NSOAtom (SOMetawrapA a t pd fn v pmv fmv) | FSOAtom (FirstSOAAtom a s mpd pd fn pmv fmv)

instance (Show (a mpd (s (SOAtom pd fn pmv fmv))), Show (a (SOAtom pd fn pmv fmv) (SOMetawrap t fn v fmv))) => Show (CombSOAtom a t s mpd pd fn v pmv fmv) where
	show (NSOAtom x) = show x
	show (FSOAtom x) = show x

deriving instance (Eq (a (SOAtom pd fn pmv fmv) (SOMetawrap t fn v fmv)), Eq (a mpd (s (SOAtom pd fn pmv fmv)))) => Eq (CombSOAtom a t s mpd pd fn v pmv fmv)

instance (HasArity pd, HasArity pmv, HasArity fn, HasArity fmv, Functor (a mpd), Functor s, SimpleTerm a, SimpleTerm t) => Normalizable (CombSOAtom a t s mpd pd fn v pmv fmv) (CombSOAtom a t s mpd pd fn v pmv fmv) where
	inject_normal = id
	normalize (NSOAtom x) = NSOAtom (normalize x)
	normalize (FSOAtom x) = FSOAtom (normalize x)


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

-- Type class indicating something is unifiable and results in a unifier of a certain term/variable type. That's why it has three type parameters
class (Unifiable t, Variabilizable v, Variable v) => DirectlyUnifiable t v s e | s -> t v e where	
	(=.=) :: s -> s -> MaybeUnifier t v e
	infix 4 =.=
	($=) :: MaybeUnifier t v e -> s -> Maybe s
	infix 4 $=

instance (Functor t, Traversable t, Unifiable t, Variabilizable v, Variable v) => DirectlyUnifiable t v (UTerm t v) (UFailure t v) where
	(=.=) = (=::=)
	u $= t = get_mu_tvalue u t

-- A utility function to force the occurs check on a unifier. Needs a set of variables to check.
force_occurs :: (Unifiable t, Variabilizable v, Variable v) => [v] -> MaybeUnifier t v (UFailure t v) -> MaybeUnifier t v (UFailure t v)
force_occurs vs u = clear_value (u >> (applyBindingsAll vts)) where vts = UVar <$> vs

-- And if we want to get a boolean result. Forcing occurs and then evaluating the variables may seem inefficient, but in fact it is more efficient, as we leverage the efficiency of applyBindingsAll to find the occurs check only once. In theory, verifying just one variable would be enough, but there's not a huge harm in evaluating all after we've already evalutated their bindings.
check_occurs :: (Unifiable t, Variabilizable v, Variable v) => [v] -> MaybeUnifier t v (UFailure t v) -> (MaybeUnifier t v (UFailure t v),Bool)
check_occurs vs u = (ru,all isJust ((ru $=) <$> vts)) where vts = UVar <$> vs; ru = force_occurs vs u

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
						Just m -> Prelude.foldr (\x -> \p -> p >> (case x of
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
	zipMatch (SOF (CompF f1 args1)) (SOF (CompF f2 args2)) = Just (SOF (CompF (Right (f1,f2)) (Prelude.map Right (zip args1 args2))))
	zipMatch _ _ = Nothing







show_unif :: (Show v, Show (UTerm t v), Unifiable t, Variabilizable v, Variable v) => [v] -> MaybeUnifier t v _ -> String
show_unif vs u = "{" ++ (intercalate "," (Prelude.map show (fromMaybe [] (traverse (\v -> u $= (UVar v)) vs)))) ++ "}"

doshow_unif :: (Show v, Show (UTerm t v), Unifiable t, Variabilizable v, Variable v) => [v] -> MaybeUnifier t v _ -> IO ()
doshow_unif vs u = putStr ((show_unif vs u) ++ "\n")




class Substitutable t v r where
	subst :: v -> r -> t -> t

subst_all :: Substitutable t v r => (v := r) -> t -> t
subst_all m x = Prelude.foldr (\(v,r) -> subst v r) x (assocs m)

-- This allows us to always provide a substitutable instance when there is nothing to substitute.
idsubst :: v -> r -> t -> t
idsubst _ _ = id


--instance (Functor f, Substitutable t v r) => Substitutable (f t) v r where
--	subst v r = fmap (subst v r)
subst_fmap :: (Functor f, Substitutable t v r) => v -> r -> f t -> f t
subst_fmap v r = fmap (subst v r)

subst_bimap :: (Bifunctor f, Substitutable t v r, Substitutable s v r) => v -> r -> f t s -> f t s
subst_bimap v r = bimap (subst v r) (subst v r)

instance (Eq v, Functor t) => Substitutable (UTerm t v) v (UTerm t v) where
	subst v rt (UVar w) | v == w = rt
	subst v rt (UVar w) = (UVar w)
	subst v rt (UTerm t) = UTerm ((subst v rt) <$> t)




-- We obtain predicates and functions as a function of their arity (really a list, but the index in the index in the list indicates the arity. imum arity of the signature, if it has one.
-- So, for example, ((preds sig) !! 3) are all predicates in the signature of arity 3.
-- Use econcat if you want all predicates or functions together.
-- We really should not need the variables in the signature, but because first-order unifiers for some (stupid) reason do not allow you to check which variables appear at all in the unifier, we need to keep track of that ourselves. vars will always be a superset of all the variables that may appear in any terms we have built while using this signature, and in many cases it will be a *proper* superset.
data Signature pd fn v = Signature {preds :: [EnumProc pd], funcs :: [EnumProc fn], vars :: EnumProc v}

-- Enumerate functions (including composites) of a certain arity (this includes lower arities, as they simply ignore the remaining arguments).
-- Concatenating this function with arbitrarily large arities is highly discouraged since this will include an exponential amount of redundancy.
-- Note that the values returned by this function are already normal!
enum_funcs :: HasArity fn => Int -> Signature pd fn v -> EnumProc (GroundSOT fn)
enum_funcs aty sig = enum_funcs_rec sig (enum_funcs_base aty sig)

enum_funcs_base :: HasArity fn => Int -> Signature pd fn v -> EnumProc (GroundSOT fn)
--enum_funcs_base aty sig = ((Fix . SOF . ConstF) <$> (econcat (Data.List.take (aty+1) (funcs sig)))) ..+ ((Fix . SOF . Proj) <$> (uns_enum_from_list [0..(aty-1)]))
-- Base functions really are just projections (choosing which variable)? 
-- Even when the arity is zero: then there are no base functions.
-- However, to avoid zero arity functions appearing multiple times, we consider those the base for arity zero.
enum_funcs_base aty sig = ((Fix . SOF . Proj) <$> (uns_enum_from_list [0..(aty-1)])) ..+ ((Fix . SOF . ConstF) <$> ((funcs sig) !! 0))

enum_funcs_rec :: HasArity fn => Signature pd fn v -> EnumProc (GroundSOT fn) -> EnumProc (GroundSOT fn)
enum_funcs_rec sig prev = prev ..+ (enum_funcs_rec sig next) where next = enum_funcs_next sig prev

-- We do not include arity zero functions here.
enum_funcs_next :: HasArity fn => Signature pd fn v -> EnumProc (GroundSOT fn) -> EnumProc (GroundSOT fn)
enum_funcs_next sig prev = all_funcs >>= (\fn -> Fix . SOF . (CompF (Fix . SOF . ConstF $ fn)) <$> (epick (arity fn) prev)) where all_funcs = econcat (tail (funcs sig))


-- Perhaps surprisingly, enumerating terms (of a simple term structure with a second-order structure on top) is as simple as enumerating 0-ary functions, converting into first-order simple elements by adding 0 arguments, and then normalizing to dump the second-order structure into first-order.
enum_terms :: (HasArity fn, SimpleTerm t, Functor (t (GroundSOT fn))) => Signature pd fn v -> EnumProc (GroundT t fn)
enum_terms sig = plain_ggsomw <$> ggsomws where fs = enum_funcs 0 sig; ggsomws = (\f -> GGSOMetawrap (Fix (build_term f []))) <$> fs

data SOSignature pd fn v sov = SOSignature {fosig :: Signature pd fn v, sovars :: EnumProc sov}
fopreds :: SOSignature pd fn v sov -> [EnumProc pd]
fopreds = preds . fosig

fofuncs :: SOSignature pd fn v sov -> [EnumProc fn]
fofuncs = funcs . fosig

fovars :: SOSignature pd fn v sov -> EnumProc v
fovars = vars. fosig 

enum_fofuncs :: HasArity fn => Int -> SOSignature pd fn v sov -> EnumProc (GroundSOT fn)
enum_fofuncs aty = (enum_funcs aty) . fosig

enum_foterms :: (HasArity fn, SimpleTerm t, Functor (t (GroundSOT fn))) => SOSignature pd fn v sov -> EnumProc (GroundT t fn)
enum_foterms = enum_terms . fosig


-- Functions to refresh second-order variables where necessary.
refresh_somv :: (Eq sov, ChangeArity sov) => SOSignature pd fn v sov -> sov -> sov
refresh_somv sig v = refresh_somv_vars (sovars sig) v

refresh_somv_vars :: (Eq sov, ChangeArity sov) => EnumProc sov -> sov -> sov
refresh_somv_vars Empty v = v
refresh_somv_vars Halt v = v
refresh_somv_vars (Error str) v = error str
refresh_somv_vars (Continue x) v = refresh_somv_vars x v
refresh_somv_vars (Produce v1 x) v2 | v1 == v2 = change_arity v2 (arity v1)
refresh_somv_vars (Produce _ x) v = refresh_somv_vars x v

refresh_somv_soterm :: (Eq fn, Eq sov, ChangeArity sov) => SOSignature pd fn v sov -> SOTerm fn sov -> SOTerm fn sov
refresh_somv_soterm sig t = (refresh_somv sig) <$> t

apply_somvunif :: (Eq fn, Eq sov, ChangeArity sov, Variabilizable sov, Variable sov) => SOSignature pd fn v sov -> MaybeUnifier (SOTermF fn) sov (UFailure (SOTermF fn) sov) -> SOTerm fn sov -> Maybe (SOTerm fn sov)
apply_somvunif sig u t = (refresh_somv_soterm sig) <$> ru where ru = u $= t
	
