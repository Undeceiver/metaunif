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
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE StandaloneDeriving #-}
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
import QueryLogic
import CESQLogic

-- We may use these so we leave them, but these are the old flat meta-variables approach. Check the new second-order approach instead.

-- Second-order approach to meta-variables
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

type SOMetatermF = SOTerm OFunction SOMVariable
type SOMetaterm = SOMetawrap CTermF OFunction OVariable SOMVariable
type GroundSOMetatermF = GroundSOT OFunction
type GroundSOMetaterm = GroundT CTermF OFunction

apply_soterm_term :: SOMetatermF -> [SOMetaterm] -> SOMetaterm
apply_soterm_term = apply_vsoterm

instance Read SOMetatermF where
	readsPrec _ xs = 
		case stripPrefix "f" xs of
		{
     			Just rest -> (let r = (head (reads ('f':rest))::(OFunction,String))
				in (case (snd r) of
					{
						('{':xs2) -> (let r2 = read_soterm_list ('{':xs2)
							in [(UTerm (SOF (CompF (UTerm (SOF (ConstF (fst r)))) (fst r2))),(snd r2))]);
						_ -> [(UTerm (SOF (ConstF (fst r))),(snd r))]
					}
				));
			Nothing -> 
		case stripPrefix "F" xs of
		{
     			Just rest -> (let r = (head (reads ('F':rest))::(SOMVariable,String))
				in (case (snd r) of
					{
						('{':xs2) -> (let r2 = read_soterm_list ('{':xs2)
							in [(UTerm (SOF (CompF (UVar (fst r)) (fst r2))),(snd r2))]);
						_ -> [(UVar (fst r),(snd r))]
					}
				));
			Nothing -> 
		case stripPrefix "pi" xs of
		{
			Just rest -> (let r = (head (reads rest)::(Int,String))
				in [(UTerm (SOF (Proj (fst r))),(snd r))]);
			Nothing -> error ("Cannot read meta-term: " ++ xs)
		}}}

instance Read GroundSOMetatermF where
	readsPrec _ xs = 
		case stripPrefix "f" xs of
		{
     			Just rest -> (let r = (head (reads ('f':rest))::(OFunction,String))
				in (case (snd r) of
					{
						('{':xs2) -> (let r2 = read_soterm_list ('{':xs2)
							in [(Fix (SOF (CompF (Fix (SOF (ConstF (fst r)))) (fst r2))),(snd r2))]);
						_ -> [(Fix (SOF (ConstF (fst r))),(snd r))]
					}
				));
			Nothing ->
		case stripPrefix "pi" xs of
		{
			Just rest -> (let r = (head (reads rest)::(Int,String))
				in [(Fix (SOF (Proj (fst r))),(snd r))]);
			Nothing -> error ("Cannot read ground second-order term: " ++ xs)
		}}

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
		case stripPrefix "pi" xs of
		{
			Just rest -> (let r = (head (reads ("pi" ++ rest))::(SOMetatermF,String))
				in (let r2 = read_term_list (snd r)
					in [(UTerm (TFun (fst r) (fst r2)),(snd r2))]));
			Nothing -> error ("Cannot read meta-term: " ++ xs)
		}}}}

instance Read SOMetaterm where
	readsPrec a xs = case (readsPrec a xs) of ((t,r):_) -> [(SOMetawrap t, r)]

instance Read GroundSOMetaterm where
	readsPrec _ xs =
		case stripPrefix "f" xs of
		{
			Just rest -> (let r = (head (reads ('f':rest))::(OFunction,String))
				in (let r2 = read_term_list (snd r)
					in [(Fix (TFun (fst r) (fst r2)),(snd r2))]));
			Nothing -> error ("Cannot read ground term: " ++ xs)
		}

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

type SOMetaatomP = SOAtom OPredicate OFunction SOAMVariable SOMVariable
type SOMetaatom = SOMetawrapA CAtomPF CTermF OPredicate OFunction OVariable SOAMVariable SOMVariable
type GroundSOMetaatomP = GroundSOA OPredicate OFunction
type GroundSOMetaatom = GroundA CAtomPF CTermF OPredicate OFunction

apply_soatom_atom :: SOMetaatomP -> [SOMetaterm] -> SOMetaatom
apply_soatom_atom = apply_vsoatom

instance Read SOMetaatomP where
	readsPrec _ xs = 
		case stripPrefix "p" xs of
		{
			Just rest -> (let r = (head (reads ('p':rest))::(OPredicate,String))
				in (case (snd r) of
					{
						('{':xs2) -> (let r2 = read_soterm_list ('{':xs2)
							in [(UTerm (SOP (CompF (UTerm (SOP (ConstF (fst r)))) (fst r2))),(snd r2))]);
						_ -> [(UTerm (SOP (ConstF (fst r))),(snd r))]
					}
				));
			Nothing ->
		case stripPrefix "P" xs of
		{
			Just rest -> (let r = (head (reads ('P':rest))::(SOAMVariable,String))
				in (case (snd r) of
					{
						('{':xs2) -> (let r2 = read_soterm_list ('{':xs2)
							in [(UTerm (SOP (CompF (UVar (fst r)) (fst r2))),(snd r2))]);
						_ -> [(UVar (fst r),(snd r))]
					}
				));
			Nothing -> error ("Cannot read meta-atom: " ++ xs)
		}}

instance Read GroundSOMetaatomP where
	readsPrec _ xs = 
		case stripPrefix "p" xs of
		{
			Just rest -> (let r = (head (reads ('p':rest))::(OPredicate,String))
				in (case (snd r) of
					{
						('{':xs2) -> (let r2 = read_soterm_list ('{':xs2)
							in [(Fix (SOP (CompF (Fix (SOP (ConstF (fst r)))) (fst r2))),(snd r2))]);
						_ -> [(Fix (SOP (ConstF (fst r))),(snd r))]
					}
				));
			Nothing -> error ("Cannot read ground second-order predicate: " ++ xs)
		}

instance Read (CAtomPF SOMetaatomP SOMetaterm) where
	readsPrec _ xs =
		case stripPrefix "p" xs of
		{
			Just rest -> (let r = (head (reads ('p':rest))::(SOMetaatomP,String))
				in (let r2 = read_term_list (snd r)
					in [(APred (fst r) (fst r2),(snd r2))]));
			Nothing ->
		case stripPrefix "P" xs of
		{
			Just rest -> (let r = (head (reads ('P':rest))::(SOMetaatomP,String))
				in (let r2 = read_term_list (snd r)
					in [(APred (fst r) (fst r2),(snd r2))]));
			Nothing -> error ("Cannot read meta-atom: " ++ xs)
		}}

instance Read SOMetaatom where
	readsPrec i xs = case (readsPrec i xs) of ((r,xs):_) -> [(SOMetawrapA r,xs)]


(*$) :: SOMetatermF -> [SOMetaterm] -> SOMetaterm
(*$) = apply_soterm_term

infix 7 *$

(**$) :: SOMetaatomP -> [SOMetaterm] -> SOMetaatom
(**$) = apply_soatom_atom

infix 7 **$


-- Queries in this meta-logic.
type SOMetaliteral = VarLiteral CAtomPF CTermF OPredicate OFunction OVariable SOAMVariable SOMVariable -- = Literal SOMetaatom
type GroundSOMetaliteral = GroundLiteral CAtomPF CTermF OPredicate OFunction -- = Literal GroundSOMetaatom
type SOMetaclause = Clause CAtomPF CTermF OPredicate OFunction OVariable SOAMVariable SOMVariable -- = [SOMetaliteral]
type SOMetaCNF = CNF CAtomPF CTermF OPredicate OFunction OVariable SOAMVariable SOMVariable -- = [SOMetaclause]

type SOMetaQVar = CESQVar SOAMVariable SOMVariable
type SOMetaQSol = CESQSol OPredicate OFunction
type SOMetaBaseQ = BaseCESQuery CAtomPF CTermF OPredicate OFunction OVariable SOAMVariable SOMVariable -- = LogicQuery SOMetaCNF
type SOMetaQuery = CESQuery CAtomPF CTermF OPredicate OFunction OVariable SOAMVariable SOMVariable -- = Query SOMetaBaseQ SOMetaQVar SOMetaQSol

-- This should be doable this way, but it isn't now:
--deriving via (NormalizeLiteral SOMetaatom, NormalizeLiteral SOMetaatom) instance Normalizable SOMetaliteral SOMetaliteral
instance Normalizable SOMetaliteral SOMetaliteral where
	inject_normal = fromNormalizeLiteral . inject_normal . NormalizeLiteral
	normalize = fromNormalizeLiteral . normalize . NormalizeLiteral

instance Normalizable SOMetaclause SOMetaclause where
	inject_normal = fromNormalizedFunctor . inject_normal . NormalizedFunctor
	normalize = fromNormalizedFunctor . normalize . NormalizedFunctor

instance Normalizable SOMetaCNF SOMetaCNF where
	inject_normal = fromNormalizedFunctor . inject_normal . NormalizedFunctor
	normalize = fromNormalizedFunctor . normalize . NormalizedFunctor

instance Read SOMetaQVar where
	readsPrec _ xs =
		case stripPrefix "F" xs of
		{
			Just rest -> (let r = (head (reads ('F':rest))::(SOMVariable,String)) in
				[(CESQVar (Right (fst r)),(snd r))]);
			Nothing ->
		case stripPrefix "P" xs of
		{
			Just rest -> (let r = (head (reads ('P':rest))::(SOAMVariable,String)) in
				[(CESQVar (Left (fst r)),(snd r))]);
			Nothing -> error ("Cannot read CESQ variable: " ++ xs)
		}}

instance Read SOMetaQSol where
	readsPrec _ xs =
		case stripPrefix "f" xs of
		{
     			Just rest -> (let r = (head (reads ('f':rest))::(GroundSOMetatermF,String))
				in [(CESQSol (Right (fst r)), (snd r))]);
			Nothing ->
		case stripPrefix "pi" xs of
		{
			Just rest -> (let r = (head (reads ('p':'i':rest))::(GroundSOMetatermF,String))
				in [(CESQSol (Right (fst r)), (snd r))]);
			Nothing -> 
		case stripPrefix "p" xs of
		{
			Just rest -> (let r = (head (reads ('p':rest))::(GroundSOMetaatomP,String))
				in [(CESQSol (Left (fst r)), (snd r))]);
			Nothing ->
		case stripPrefix "P" xs of
		{
			Just rest -> (let r = (head (reads ('P':rest))::(GroundSOMetaatomP,String))
				in [(CESQSol (Left (fst r)), (snd r))]);
			Nothing -> error ("Cannot read ground term or atom: " ++ xs)
		}}}}
