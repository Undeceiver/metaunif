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

newtype OVariable = OVar Int deriving (Eq, Ord)

instance Show OVariable where
	show (OVar x) = "x" ++ (show x)
instance Read OVariable where
	readsPrec _ ('x':xs) = (let r = (head (reads xs))
				in [(OVar (fst r),(snd r))])
instance Variabilizable OVariable where 
	get_var (OVar x) = IntVar x

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

data CTermF f = TFun OFunction [f] deriving (Eq, Ord, Functor, Foldable, Traversable)
type CTerm = Fix CTermF

instance Show f => Show (CTermF f) where
	show (TFun x []) = (show x) ++ "()"
	show (TFun x (y:ys)) = (show x) ++ "(" ++ (foldl (\x -> \y -> x ++ "," ++ (show y)) (show y) ys) ++ ")"

instance Read f => Read (CTermF f) where
	readsPrec _ ('f':xs) = (let r = (head (reads ('f':xs))::(OFunction,String))
				in (let r2 = read_term_list (snd r)
					in [(TFun (fst r) (fst r2),(snd r2))]))

type GTerm = UTerm CTermF
type Term = GTerm OVariable

read_term_list :: Read v => String -> ([v],String)
read_term_list ('(':xs) = read_term_list xs
read_term_list (')':xs) = ([],xs)
read_term_list (',':xs) = read_term_list xs
read_term_list x = (let r = (head (reads x))
			in (let r2 = read_term_list (snd r)
				in ((fst r):(fst r2),(snd r2))))

instance Read Term where
	readsPrec _ ('x':xs) = (let r = (head (reads ('x':xs))::(OVariable,String))
				in [(UVar (fst r),(snd r))])
	readsPrec _ ('f':xs) = (let r = (head (reads ('f':xs))::(OFunction,String))
				in (let r2 = read_term_list (snd r)
					in [(UTerm (TFun (fst r) (fst r2)),(snd r2))]))


instance Unifiable CTermF where
	zipMatch (TFun f t1s) (TFun g t2s) | (f == g) && ((length t1s) == (length t2s)) = Just (TFun f (map Right (zip t1s t2s)))
	zipMatch (TFun f t1s) (TFun g t2s) | (f == g) && ((length t1s) /= (length t2s)) = error ("Unifying function " ++ (show f) ++ " but arities don't match! Arities: " ++ (show (length t1s)) ++  " and " ++ (show (length t2s)))
	zipMatch (TFun f t1s) (TFun g t2s) = Nothing

data CAtomPF f = APred OPredicate [f] deriving (Eq, Ord, Functor, Foldable, Traversable)
type CAtomF = Predicabilize CAtomPF

instance Show f => Show (CAtomPF f) where
	show (APred p []) = (show p) ++ "()"
	show (APred p (y:ys)) = (show p) ++ "(" ++ (foldl (\x -> \y -> x ++ "," ++ (show y)) (show y) ys) ++ ")"

instance Read f => Read (CAtomPF f) where
	readsPrec _ ('p':xs) = (let r = (head (reads ('p':xs))::(OPredicate,String))
				in (let r2 = read_term_list (snd r)
					in [(APred (fst r) (fst r2),(snd r2))]))

type GAtom = Predicabilize CAtomPF
type Atom = GAtom Term

instance Unifiable CAtomPF where
	zipMatch (APred p t1s) (APred q t2s) | (p == q) && ((length t1s) == (length t2s)) = Just (APred p (map Right (zip t1s t2s)))
	zipMatch (APred p t1s) (APred q t2s) | (p == q) && ((length t1s) /= (length t2s)) = error ("Unifying predicate " ++ (show p) ++ " but arities don't match! Arities: " ++ (show (length t1s)) ++  " and " ++ (show (length t2s)))
	zipMatch (APred p t1s) (APred q t2s) = Nothing
