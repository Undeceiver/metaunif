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
module MetaLogic where

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
import ObjectLogic
import Data.Functor.Fixedpoint
import Data.List

-- We may use these so we leave them, but these are the old flat meta-variables approach. Check the new second-order approach instead.

newtype MVariable = MVar Int deriving (Eq, Ord)

instance Show MVariable where
	show (MVar x) = "X" ++ (show x)
instance Read MVariable where
	readsPrec _ ('X':xs) = (let r = (head (reads xs))
				in [(MVar (fst r),(snd r))])

instance Variabilizable MVariable where
	from_var (IntVar x) = MVar x
	get_var (MVar x) = IntVar x

newtype AMVariable = AMVar Int deriving (Eq, Ord)

instance Show AMVariable where
	show (AMVar x) = "Z" ++ (show x)
instance Read AMVariable where
	readsPrec _ ('Z':xs) = (let r = (head (reads xs))
				in [(AMVar (fst r),(snd r))])

instance Variabilizable AMVariable where 
	from_var (IntVar x) = AMVar x
	get_var (AMVar x) = IntVar x


-- This is NOT what I used to call a meta-term.
type Metaterm = Metawrap CTermFn OVariable MVariable
instance Read Metaterm where
	readsPrec _ ('x':xs) = (let r = (head (reads ('x':xs))::(OVariable,String))
				in [(mw (UVar (fst r)),(snd r))])
	readsPrec _ ('X':xs) = (let r = (head (reads ('X':xs))::(MVariable,String))
				in [(mv (fst r),(snd r))])
	readsPrec _ ('f':xs) = (let r = (head (reads ('f':xs))::(OFunction,String))
				in (let r2 = read_term_list (snd r)
					in [(UTerm (FTerm (TFun (fst r) (fst r2))),(snd r2))]))

type Metaatom = PredicateMetawrap CAtomPd CTermFn OVariable MVariable AMVariable

-- We use X for term meta-variables and Z for atom meta-variables
instance Read Metaatom where
	readsPrec _ ('x':xs) = (let r = (head (reads ('x':xs))::(OVariable,String))
				in [(pmw (Term (UVar (fst r))),(snd r))])
	readsPrec _ ('X':xs) = (let r = (head (reads ('X':xs))::(MVariable,String))
				in [(tmv (fst r),(snd r))])
	readsPrec _ ('f':xs) = (let r = (head (reads ('f':xs))::(OFunction,String))
				in (let r2 = read_term_list (snd r)
					in [(Term (UTerm (FTerm (TFun (fst r) (fst r2)))),(snd r2))]))
	readsPrec _ ('p':xs) = (let r = (head (reads ('p':xs))::(OPredicate,String))
				in (let r2 = read_term_list (snd r)
					in [(Atom (FTerm (APred (fst r) (fst r2))),(snd r2))]))
	readsPrec _ ('Z':xs) = (let r = (head (reads ('Z':xs))::(AMVariable,String))
				in [(amv (fst r),(snd r))])




-- Second-order approach to meta-variables
apply_soterm_term :: SOTerm OFunction Term -> [Term] -> Term
apply_soterm_term = apply_soterm (\f -> \args -> UTerm (TFun f args))

apply_soatom_atom :: SOAtom OPredicate OFunction Atom Term -> [Term] -> Atom
apply_soatom_atom = apply_soatom (\p -> \args -> Atom (APred p args)) (\f -> \args -> UTerm (TFun f args))


data SOMVariable = SOMVar Int Int deriving (Eq, Ord)

instance Show SOMVariable where
	show (SOMVar x a) = "F" ++ (show x) ++ "[" ++ (show a) ++ "]"
instance Read SOMVariable where 
	readsPrec _ ('F':xs) = (let r = (head (reads xs))
				in (let r2 = (read_arity (snd r))
					in [(SOMVar (fst r) (fst r2),(snd r2))]))

instance HasArity SOMVariable where
	arity (SOMVar _ a) = a

--instance Variabilizable SOMVariable where 
--	from_var (IntVar x) = SOMVar x ??
--	get_var (SOMVar x _) = IntVar x

instance {-# OVERLAPPING #-} Read (SOMetawrapperV OFunction SOMVariable) where
	readsPrec _ ('f':xs) = (let r = (head (reads ('f':xs))::(OFunction,String)) in [(CFunc (fst r),(snd r))])
	readsPrec _ ('F':xs) = (let r = (head (reads ('F':xs))::(SOMVariable,String)) in [(SOMV (fst r),(snd r))])

type SOMetatermF = SOMetawrapF CTermF OFunction OVariable SOMVariable
type SOMetaterm = SOMetawrap CTermF OFunction OVariable SOMVariable
type GroundSOMetaterm = GroundSOT CTermF OFunction

instance Read SOMetatermF where
	readsPrec _ xs = 
		case stripPrefix "f" xs of
		{
     			Just rest -> (let r = (head (reads ('f':rest))::(OFunction,String))
				in (case (snd r) of
					{
						('{':xs2) -> (let r2 = read_soterm_list ('{':xs2)
							in [(Fix (CompF (CFunc (fst r)) (fst r2)),(snd r2))]);
						_ -> [(Fix (ConstF (CFunc (fst r))),(snd r))]
					}
				));
			Nothing -> 
		case stripPrefix "F" xs of
		{
     			Just rest -> (let r = (head (reads ('F':rest))::(SOMVariable,String))
				in (case (snd r) of
					{
						('{':xs2) -> (let r2 = read_soterm_list ('{':xs2)
							in [(Fix (CompF (SOMV (fst r)) (fst r2)),(snd r2))]);
						_ -> [(Fix (ConstF (SOMV (fst r))),(snd r))]
					}
				));
			Nothing -> 
		case stripPrefix "(\\x -> " xs of
		{
			Just rest -> (let r = (head (reads rest)::(SOMetaterm,String))
				in (case (snd r) of {(')':xs2) -> (let r2 = read_arity xs2
					in [(Fix (CConstF (fst r2) (fst r)),(snd r2))])}));
			Nothing ->
		case stripPrefix "pi" xs of
		{
			Just rest -> (let r = (head (reads rest)::(Int,String))
				in (let r2 = read_arity (snd r)
					in [(Fix (Proj (fst r2) (fst r)),(snd r2))]));
			Nothing -> error ("Cannot read meta-term: " ++ xs)
		}}}}

instance Read (UTerm (CTermF SOMetatermF) OVariable) where
	readsPrec _ xs =
		case stripPrefix "x" xs of
		{
			Just rest -> (let r = (head (reads ('x':rest))::(OVariable,String))
				in [(UVar (fst r),(snd r))]);
			Nothing ->
		case stripPrefix "f" xs of
		{
			Just rest -> (let r = (head (reads ('f':rest))::(SOMetatermF,String))
				in (let r2 = read_term_list (snd r)
					in [(UTerm (TFun (fst r) (fst r2)),(snd r2))]));
			Nothing ->
		case stripPrefix "F" xs of
		{
			Just rest -> (let r = (head (reads ('F':rest))::(SOMetatermF,String))
				in (let r2 = read_term_list (snd r)
					in [(UTerm (TFun (fst r) (fst r2)),(snd r2))]));
			Nothing ->
		case stripPrefix "(\\x -> " xs of
		{
			Just rest -> (let r = (head (reads ("(\\x -> " ++ rest))::(SOMetatermF,String))
				in (let r2 = read_term_list (snd r)
					in [(UTerm (TFun (fst r) (fst r2)),(snd r2))]));
			Nothing ->
		case stripPrefix "pi" xs of
		{
			Just rest -> (let r = (head (reads ("pi" ++ rest))::(SOMetatermF,String))
				in (let r2 = read_term_list (snd r)
					in [(UTerm (TFun (fst r) (fst r2)),(snd r2))]));
			Nothing -> error ("Cannot read meta-term: " ++ xs)
		}}}}}

instance Read SOMetaterm where
	readsPrec i xs = case (readsPrec i xs) of ((r,xs):_) -> [(SOMetawrap r,xs)]

data SOAMVariable = SOAMVar Int Int deriving (Eq, Ord)

instance Show SOAMVariable where
	show (SOAMVar x a) = "P" ++ (show x) ++ "[" ++ (show a) ++ "]"
instance Read SOAMVariable where 
	readsPrec _ ('P':xs) = (let r = (head (reads xs))
				in (let r2 = (read_arity (snd r))
					in [(SOAMVar (fst r) (fst r2),(snd r2))]))

instance HasArity SOAMVariable where
	arity (SOAMVar _ a) = a

--instance Variabilizable SOAMVariable where 
--	get_var (SOAMVar x _) = IntVar x

instance {-# OVERLAPPING #-} Read (SOMetawrapperV OPredicate SOAMVariable) where
	readsPrec _ ('p':xs) = (let r = (head (reads ('p':xs))::(OPredicate,String)) in [(CFunc (fst r),(snd r))])
	readsPrec _ ('P':xs) = (let r = (head (reads ('P':xs))::(SOAMVariable,String)) in [(SOMV (fst r),(snd r))])

type SOMetaatomP = SOMetawrapP CAtomPF CTermF OPredicate OFunction OVariable SOAMVariable SOMVariable
type SOMetaatom = SOMetawrapA CAtomPF CTermF OPredicate OFunction OVariable SOAMVariable SOMVariable
type GroundSOMetaatom = GroundSOA CAtomPF CTermF OPredicate OFunction

instance Read SOMetaatomP where
	readsPrec _ xs = 
		case stripPrefix "p" xs of
		{
			Just rest -> (let r = (head (reads ('p':rest))::(OPredicate,String))
				in (case (snd r) of
					{
						('{':xs2) -> (let r2 = read_soterm_list ('{':xs2)
							in [(CompF (CFunc (fst r)) (fst r2),(snd r2))]);
						_ -> [(ConstF (CFunc (fst r)),(snd r))]
					}
				));
			Nothing ->
		case stripPrefix "P" xs of
		{
			Just rest -> (let r = (head (reads ('P':rest))::(SOAMVariable,String))
				in (case (snd r) of
					{
						('{':xs2) -> (let r2 = read_soterm_list ('{':xs2)
							in [(CompF (SOMV (fst r)) (fst r2),(snd r2))]);
						_ -> [(ConstF (SOMV (fst r)),(snd r))]
					}
				));
			Nothing ->
		case stripPrefix "(\\z -> " xs of
		{
			Just rest -> (let r = (head (reads rest)::(SOMetaatom,String))
				in (case (snd r) of {(')':xs2) -> (let r2 = read_arity xs2
					in [(CConstF (fst r2) (fst r),(snd r2))])}));
			Nothing -> error ("Cannot read meta-atom: " ++ xs)
		--case stripPrefix "zpi" xs of
		--{
		--	Just rest -> (let r = (head (reads rest)::(Int,String))
		--		in (let r2 = read_arity (snd r)
		--			in [(Proj (fst r2) (fst r),(snd r2))]));
		--	Nothing -> error ("Cannot read meta-atom: " ++ xs)
		}}}


instance Read (Predicabilize (CAtomPF SOMetaatomP) SOMetaterm) where
	readsPrec _ xs =
		case stripPrefix "x" xs of
		{
			Just rest -> (let r = (head (reads ('x':rest))::(OVariable,String))
				in [(Term (SOMetawrap (UVar (fst r))),(snd r))]);
			Nothing ->
		case stripPrefix "f" xs of
		{
			Just rest -> (let r = (head (reads ('f':rest))::(SOMetatermF,String))
				in (let r2 = read_term_list (snd r)
					in [(Term (SOMetawrap (UTerm (TFun (fst r) (fst r2)))),(snd r2))]));
			Nothing ->
		case stripPrefix "F" xs of
		{
			Just rest -> (let r = (head (reads ('F':rest))::(SOMetatermF,String))
				in (let r2 = read_term_list (snd r)
					in [(Term (SOMetawrap (UTerm (TFun (fst r) (fst r2)))),(snd r2))]));
			Nothing ->
		case stripPrefix "(\\x -> " xs of
		{
			Just rest -> (let r = (head (reads ("\\x -> " ++ rest))::(SOMetatermF,String))
				in (let r2 = read_term_list (snd r)
					in [(Term (SOMetawrap (UTerm (TFun (fst r) (fst r2)))),(snd r2))]));
			Nothing ->
		case stripPrefix "pi" xs of
		{
			Just rest -> (let r = (head (reads ("pi" ++ rest))::(SOMetatermF,String))
				in (let r2 = read_term_list (snd r)
					in [(Term (SOMetawrap (UTerm (TFun (fst r) (fst r2)))),(snd r2))]));
			Nothing ->
		case stripPrefix "p" xs of
		{
			Just rest -> (let r = (head (reads ('p':rest))::(SOMetaatomP,String))
				in (let r2 = read_term_list (snd r)
					in [(Atom (APred (fst r) (fst r2)),(snd r2))]));
			Nothing ->
		case stripPrefix "P" xs of
		{
			Just rest -> (let r = (head (reads ('P':rest))::(SOMetaatomP,String))
				in (let r2 = read_term_list (snd r)
					in [(Atom (APred (fst r) (fst r2)),(snd r2))]));
			Nothing ->
		case stripPrefix "(\\z -> " xs of
		{
			Just rest -> (let r = (head (reads ("\\z -> " ++ rest))::(SOMetaatomP,String))
				in (let r2 = read_term_list (snd r)
					in [(Atom (APred (fst r) (fst r2)),(snd r2))]));
			Nothing -> error ("Cannot read meta-atom: " ++ xs)
		--case stripPrefix "zpi" xs of
		--{
		--	Just rest -> (let r = (head (reads ("zpi" ++ rest))::(SOMetaatomP,String))
		--		in (let r2 = read_term_list (snd r)
		--			in [(Atom (APred (fst r) (fst r2)),(snd r2))]));
		--	Nothing -> error ("Cannot read meta-atom: " ++ xs)
		}}}}}}}}

instance Read SOMetaatom where
	readsPrec i xs = case (readsPrec i xs) of ((r,xs):_) -> [(SOMetawrapA r,xs)]

apply_soterm_termw :: SOMetatermF -> [SOMetaterm] -> SOMetaterm
apply_soterm_termw = apply_soterm (\f -> \args -> SOMetawrap (UTerm (TFun (Fix . ConstF $ f) (map fromSOMetawrap args))))

(*$) :: SOMetatermF -> [SOMetaterm] -> SOMetaterm
(*$) = apply_soterm_termw

infix 7 *$

apply_soatom_atomw :: SOMetaatomP -> [SOMetaterm] -> SOMetaatom
apply_soatom_atomw = apply_soatom (\p -> \args -> SOMetawrapA (Atom (APred (ConstF p) args))) (\f -> \args -> SOMetawrap (UTerm (TFun (Fix . ConstF $ f) (map fromSOMetawrap args))))

(**$) :: SOMetaatomP -> [SOMetaterm] -> SOMetaatom
(**$) = apply_soatom_atomw

infix 7 **$
