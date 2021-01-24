{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
--{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
module ObjectLogic where

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
import Syntax
import Data.Functor.Fixedpoint
import Data.Bifunctor
import HaskellPlus

newtype OVariable = OVar Int deriving (Eq, Ord)

instance Show OVariable where
	show (OVar x) = "x" ++ (show x)
instance Read OVariable where
	readsPrec _ ('x':xs) = (let r = (head (reads xs))
				in [(OVar (fst r),(snd r))])
instance Variabilizable OVariable where 
	from_var (IntVar x) = OVar x
	get_var (OVar x) = IntVar x

instance Variable OVariable where
	getVarID = getVarID_gen

data OFunction = OFun Int Int deriving (Eq, Ord)

instance Show OFunction where
	show (OFun x y) = "f" ++ (show x) ++ "[" ++ (show y) ++ "]"

instance Read OFunction where 
	readsPrec _ ('f':xs) = (let r = (head (reads xs))
				in (let r2 = (read_arity (snd r))
					in [(OFun (fst r) (fst r2),(snd r2))]))

instance HasArity OFunction where
	arity (OFun _ x) = x									

data OPredicate = OPred Int Int deriving (Eq, Ord)

instance Show OPredicate where
	show (OPred x y) = "p" ++ (show x) ++ "[" ++ (show y) ++ "]"

instance Read OPredicate where
	readsPrec _ ('p':xs) = (let r = (head (reads xs))
				in (let r2 = (read_arity (snd r))
					in [(OPred (fst r) (fst r2),(snd r2))]))									

instance HasArity OPredicate where
	arity (OPred _ x) = x

data CTermF fn f = TFun fn [f] deriving (Eq, Ord, Functor, Foldable, Traversable)

fixTFun :: fn -> [Fix (CTermF fn)] -> Fix (CTermF fn)
fixTFun = build_functor_fix TFun

type CTermFn = CTermF OFunction
type CTerm = Fix CTermFn

instance (Show f, Show fn) => Show (CTermF fn f) where
	show (TFun x []) = (show x) ++ "()"
	show (TFun x (y:ys)) = (show x) ++ "(" ++ (foldl (\x -> \y -> x ++ "," ++ (show y)) (show y) ys) ++ ")"

instance Read f => Read (CTermFn f) where
	readsPrec _ ('f':xs) = (let r = (head (reads ('f':xs))::(OFunction,String))
				in (let r2 = read_term_list (snd r)
					in [(TFun (fst r) (fst r2),(snd r2))]))

instance Bifunctor CTermF where
	bimap f g (TFun fn ts) = TFun (f fn) (map g ts)

instance SimpleTerm CTermF where
	build_term = TFun
	unbuild_term (TFun f ts) = (f,ts)

-- The functions of a term can also be traversed
instance Foldable (FlippedBifunctor CTermF f) where
	foldMap g (FlippedBifunctor (TFun f ts)) = g f

instance Traversable (FlippedBifunctor CTermF f) where
	sequenceA (FlippedBifunctor (TFun f ts)) = (pure (\g -> FlippedBifunctor (TFun g ts))) <*> f

type GTerm = UTerm CTermFn
type Term = GTerm OVariable
type GroundTerm = GroundT CTermF OFunction

type TermUnifier = MaybeUnifier CTermFn OVariable (UFailure CTermFn OVariable)

instance Read Term where
	readsPrec _ ('x':xs) = (let r = (head (reads ('x':xs))::(OVariable,String))
				in [(UVar (fst r),(snd r))])
	readsPrec _ ('f':xs) = (let r = (head (reads ('f':xs))::(OFunction,String))
				in (let r2 = read_term_list (snd r)
					in [(UTerm (TFun (fst r) (fst r2)),(snd r2))]))


instance (Eq fn, Show fn) => Unifiable (CTermF fn) where
	zipMatch (TFun f t1s) (TFun g t2s) | (f == g) && ((length t1s) == (length t2s)) = Just (TFun f (map Right (zip t1s t2s)))
	zipMatch (TFun f t1s) (TFun g t2s) | (f == g) && ((length t1s) /= (length t2s)) = error ("Unifying function " ++ (show f) ++ " but arities don't match! Arities: " ++ (show (length t1s)) ++  " and " ++ (show (length t2s)))
	zipMatch (TFun f t1s) (TFun g t2s) = Nothing

data CAtomPF pd f = APred pd [f] deriving (Eq, Ord, Functor, Foldable, Traversable)

fixAPred :: pd -> [Fix (CAtomPF pd)] -> Fix (CAtomPF pd)
fixAPred = build_functor_fix APred

type CAtomPd = CAtomPF OPredicate

instance (Show f, Show pd) => Show (CAtomPF pd f) where
	show (APred p []) = (show p) ++ "()"
	show (APred p (y:ys)) = (show p) ++ "(" ++ (foldl (\x -> \y -> x ++ "," ++ (show y)) (show y) ys) ++ ")"

instance Read f => Read (CAtomPd f) where
	readsPrec _ ('p':xs) = (let r = (head (reads ('p':xs))::(OPredicate,String))
				in (let r2 = read_term_list (snd r)
					in [(APred (fst r) (fst r2),(snd r2))]))

instance Bifunctor CAtomPF where
	bimap f g (APred pd ts) = APred (f pd) (map g ts)

instance SimpleTerm CAtomPF where
	build_term = APred
	unbuild_term (APred p ts) = (p,ts)

instance Foldable (FlippedBifunctor CAtomPF f) where
	foldMap g (FlippedBifunctor (APred p ts)) = g p

instance Traversable (FlippedBifunctor CAtomPF f) where
	sequenceA (FlippedBifunctor (APred p ts)) = (pure (\q -> FlippedBifunctor (APred q ts))) <*> p


type GAtom = Predicabilize CAtomPd
type Atom = GAtom Term
type GroundAtom = GroundA CAtomPF CTermF OPredicate OFunction

type AtomUnifier = MaybeUnifier CTermFn OVariable (DUFailure (Predicabilize CAtomPd Term) (UFailure CTermFn OVariable))

instance Read Atom where
	readsPrec _ ('x':xs) = (let r = (head (reads ('x':xs))::(OVariable,String))
				in [(Term (UVar (fst r)),(snd r))])
	readsPrec _ ('f':xs) = (let r = (head (reads ('f':xs))::(OFunction,String))
				in (let r2 = read_term_list (snd r)
					in [(Term (UTerm (TFun (fst r) (fst r2))),(snd r2))]))
	readsPrec _ ('p':xs) = (let r = (head (reads ('p':xs))::(OPredicate,String))
				in (let r2 = read_term_list (snd r)
					in [(Atom (APred (fst r) (fst r2)),(snd r2))]))

instance (Eq pd, Show pd) => Unifiable (CAtomPF pd) where
	zipMatch (APred p t1s) (APred q t2s) | (p == q) && ((length t1s) == (length t2s)) = Just (APred p (map Right (zip t1s t2s)))
	zipMatch (APred p t1s) (APred q t2s) | (p == q) && ((length t1s) /= (length t2s)) = error ("Unifying predicate " ++ (show p) ++ " but arities don't match! Arities: " ++ (show (length t1s)) ++  " and " ++ (show (length t2s)))
	zipMatch (APred p t1s) (APred q t2s) = Nothing
