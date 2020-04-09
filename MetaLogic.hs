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
import ESUnification
import EnumProc
import Control.Monad.ST
import Control.Monad.State
import AnswerSet

-- We may use these so we leave them, but these are the old flat meta-variables approach. Check the new second-order approach instead.

-- Second-order approach to meta-variables
data SOMVariable = SOMVar Int Int deriving (Ord)

-- Equality does not check arity, just in case we use the Variabilizable instance in the wrong way.
instance Eq SOMVariable where
	(SOMVar i _) == (SOMVar j _) = i == j

instance Show SOMVariable where
	show (SOMVar x a) = "F" ++ (show x) ++ "[" ++ (show a) ++ "]"
instance Read SOMVariable where 
	readsPrec _ ('F':xs) = (let r = (head (reads xs))
				in (let r2 = (read_arity (snd r))
					in [(SOMVar (fst r) (fst r2),(snd r2))]))

instance HasArity SOMVariable where
	arity (SOMVar _ a) = a

instance ChangeArity SOMVariable where
	change_arity (SOMVar idx a) b = SOMVar idx b

-- This instance is potentially problematic due to the arity issue. But we need it because the Unification library for some reason requires variable
-- Just remember that whenever a second-order variable is extracted from a unifier, we need to re-adjust the arity with respect to the signature.
instance Variabilizable SOMVariable where 
	from_var (IntVar x) = SOMVar x 0
	get_var (SOMVar x _) = IntVar x

instance Variable SOMVariable where
	getVarID = getVarID_gen


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



-- Second-order atoms.
data SOPredicate = SOPred Int Int deriving (Eq, Ord)

instance Show SOPredicate where
	show (SOPred x y) = "k" ++ (show x) ++ "[" ++ (show y) ++ "]"

instance Read SOPredicate where 
	readsPrec _ ('k':xs) = (let r = (head (reads xs))
				in (let r2 = (read_arity (snd r))
					in [(SOPred (fst r) (fst r2),(snd r2))]))

instance HasArity SOPredicate where
	arity (SOPred _ x) = x									

type FirstSOMetaAAtom = FirstSOAAtom CAtomPF LambdaCNF SOPredicate OPredicate OFunction SOAMVariable SOMVariable

instance Read FirstSOMetaAAtom where
	readsPrec _ xs =
		case stripPrefix "k" xs of
		{
			Just rest -> (let r = (head (reads ('k':rest))::(SOPredicate,String))
				in (let r2 = read_term_list (snd r)
					in [(FirstSOAAtom (APred (fst r) (fst r2)),(snd r2))]));
		}

type CombSOMetaatom = CombSOAtom CAtomPF CTermF LambdaCNF SOPredicate OPredicate OFunction OVariable SOAMVariable SOMVariable

instance Read CombSOMetaatom where
	readsPrec _ xs =
		case stripPrefix "k" xs of
		{
			Just rest -> (let r = (head (reads ('k':rest))::(FirstSOMetaAAtom,String))
				in [(FSOAtom (fst r),(snd r))]);
			Nothing ->
		case stripPrefix "p" xs of
		{
			Just rest -> (let r = (head (reads ('p':rest))::(SOMetaatom,String))
				in [(NSOAtom (fst r),(snd r))]);
			Nothing ->
		case stripPrefix "P" xs of
		{
			Just rest -> (let r = (head (reads ('P':rest))::(SOMetaatom,String))
				in [(NSOAtom (fst r),(snd r))]);
			Nothing -> error ("Cannot read meta-atom: " ++ xs)
		}}}


-- Dependency graphs in this meta-logic.
data UnifVariable = UnifVar Int deriving (Ord)

-- Equality does not check arity, just in case we use the Variabilizable instance in the wrong way.
instance Eq UnifVariable where
	(UnifVar i) == (UnifVar j) = i == j

instance Show UnifVariable where
	show (UnifVar x) = "u" ++ (show x)
instance Read UnifVariable where 
	readsPrec _ ('u':xs) = (let r = (head (reads xs))
				in [(UnifVar (fst r),(snd r))])

instance Variabilizable UnifVariable where 
	from_var (IntVar x) = UnifVar x
	get_var (UnifVar x) = IntVar x

instance Variable UnifVariable where
	getVarID = getVarID_gen


type SOMetaTermDependant = TermDependant CTermF OFunction OVariable SOMVariable UnifVariable
instance Read SOMetaTermDependant where
	readsPrec _ xs = 
		case stripPrefix "u" xs of
		{
			Just rest -> (let r = (head (reads ('u':rest))::(UnifVariable,String))
				-- We expect exactly one space between the unifier and the inner dependant.
				in (let r2 = (head (reads (tail (snd r)))::(SOMetaTermDependant,String))
					in [(TDUnif (fst r) (fst r2),(snd r2))]));
			Nothing -> (let r = (head (reads xs))::(SOMetaterm,String) in
				[(TDDirect (fst r),(snd r))])
		}

type SOMetaUnifDGraph s = ESUnifVDGraph s CTermF OFunction OVariable SOMVariable UnifVariable
type SOMetaUnifRelFoId s = ESUnifRelFoId s CTermF OFunction OVariable SOMVariable UnifVariable
type SOMetaUnifRelSoId s = ESUnifRelSoId s CTermF OFunction OVariable SOMVariable UnifVariable
type RSOMetaUnifDGraph = RESUnifVDGraph CTermF OFunction OVariable SOMVariable UnifVariable
type SOMetaUnifSysSolution = UnifSysSolution OFunction SOMVariable

metaunif_vertical_commute :: StateT (SOMetaUnifDGraph s) (ST s) ()
metaunif_vertical_commute = esu_vertical_commute

metaunif_vertical_align :: StateT (SOMetaUnifDGraph s) (ST s) ()
metaunif_vertical_align = esu_vertical_align

metaunif_sozip :: StateT (SOMetaUnifDGraph s) (ST s) ()
metaunif_sozip = esu_sozip

metaunif_fozip :: StateT (SOMetaUnifDGraph s) (ST s) ()
metaunif_fozip = esu_fozip

metaunif_so_simplify_projections :: StateT (SOMetaUnifDGraph s) (ST s) ()
metaunif_so_simplify_projections = esu_so_simplify_projections

metaunif_fo_simplify_projections :: StateT (SOMetaUnifDGraph s) (ST s) ()
metaunif_fo_simplify_projections = esu_fo_simplify_projections

metaunif_fo_dump :: StateT (SOMetaUnifDGraph s) (ST s) ()
metaunif_fo_dump = esu_fo_dump

metaunif_so_dump :: StateT (SOMetaUnifDGraph s) (ST s) ()
metaunif_so_dump = esu_so_dump

metaunif_check_all_consistency :: StateT (SOMetaUnifDGraph s) (ST s) Bool
metaunif_check_all_consistency = metaunif_check_sot_consistency >>=& metaunif_check_head_arity_so >>=& metaunif_check_head_arity_fo >>=& metaunif_check_target_arity_so >>=& metaunif_occurs_check_so >>=& metaunif_occurs_check_fo

metaunif_check_sot_consistency :: StateT (SOMetaUnifDGraph s) (ST s) Bool
metaunif_check_sot_consistency = check_sot_consistency

metaunif_check_fot_consistency :: StateT (SOMetaUnifDGraph s) (ST s) Bool
metaunif_check_fot_consistency = check_fot_consistency

metaunif_check_head_arity_so :: StateT (SOMetaUnifDGraph s) (ST s) Bool
metaunif_check_head_arity_so = check_head_arity_so

metaunif_check_head_arity_fo :: StateT (SOMetaUnifDGraph s) (ST s) Bool
metaunif_check_head_arity_fo = check_head_arity_fo

metaunif_check_target_arity_so :: StateT (SOMetaUnifDGraph s) (ST s) Bool
metaunif_check_target_arity_so = check_target_arity_so

metaunif_occurs_check_so :: StateT (SOMetaUnifDGraph s) (ST s) Bool
metaunif_occurs_check_so = occurs_check_so

metaunif_occurs_check_fo :: StateT (SOMetaUnifDGraph s) (ST s) Bool
metaunif_occurs_check_fo = occurs_check_fo

metaunif_validate_all_consistency :: RSOMetaUnifDGraph -> AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
metaunif_validate_all_consistency resuvdg = (ImplicitAS resuvdg) ?>>= SOTConsistency ?>>= HeadAritySO ?>>= HeadArityFO ?>>= OccursCheckSO ?>>= OccursCheckFO

metaunif_validate_sot_consistency :: RSOMetaUnifDGraph -> AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
metaunif_validate_sot_consistency = validate_sot_consistency

metaunif_validate_fot_consistency :: RSOMetaUnifDGraph -> AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
metaunif_validate_fot_consistency = validate_fot_consistency

metaunif_validate_head_arity_so :: RSOMetaUnifDGraph -> AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
metaunif_validate_head_arity_so = validate_head_arity_so

metaunif_validate_head_arity_fo :: RSOMetaUnifDGraph -> AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
metaunif_validate_head_arity_fo = validate_head_arity_fo

metaunif_validate_target_arity_so :: RSOMetaUnifDGraph -> AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
metaunif_validate_target_arity_so = validate_target_arity_so

metaunif_validate_occurs_check_so :: RSOMetaUnifDGraph -> AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
metaunif_validate_occurs_check_so = validate_occurs_check_so

metaunif_validate_occurs_check_fo :: RSOMetaUnifDGraph -> AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
metaunif_validate_occurs_check_fo = validate_occurs_check_fo


type SOMetaUnifFOExp = FOTermDependantExp CTermF OFunction OVariable SOMVariable UnifVariable
type SOMetaUnifSOExp = SOTermDependantExp OFunction SOMVariable

instance Read SOMetaUnifFOExp where
	readsPrec _ xs = 
		case stripPrefix "u" xs of
		{
			Just _ -> (let r = (head (reads xs)::(SOMetaTermDependant,String))
					in [(FOTDExp (fst r),(snd r))]);
			Nothing -> (let r = (head (reads xs)::(SOMetatermF,String))
					in (let r2 = read_term_list (snd r)
						in [(FOEdgeExp (fst r) (fst r2),(snd r2))]))
		}

instance Read SOMetaUnifSOExp where
	readsPrec _ xs = 
		let r = (head (reads xs)::(SOMetatermF,String))
			in [(separate_sot_dependant_exp (normalize (fst r)),(snd r))]


-- Queries in this meta-logic.
type SOMetaliteral = VarLiteral CAtomPF CTermF SOPredicate OPredicate OFunction OVariable SOAMVariable SOMVariable -- = Literal CombSOMetaatom
type GroundSOMetaliteral = GroundLiteral CAtomPF CTermF OPredicate OFunction -- = Literal GroundSOMetaatom
type SOMetaclause = Clause CAtomPF CTermF SOPredicate OPredicate OFunction OVariable SOAMVariable SOMVariable -- = [SOMetaliteral]
type SOMetaCNF = CNF CAtomPF CTermF SOPredicate OPredicate OFunction OVariable SOAMVariable SOMVariable -- = [SOMetaclause]
type SOMetaSignature = SOSignature OPredicate OFunction OVariable SOMVariable

type SOMetaMGU = ESMGU CTermF OPredicate OFunction OVariable SOMVariable
type SOMetaNMGU = NESMGU CTermF OPredicate OFunction OVariable SOMVariable

type SOMetaQVar = CESQVar SOAMVariable SOMVariable
type SOMetaQSol = CESQSol OPredicate OFunction
type SOMetaQParcSol = ParcCESQSol OPredicate OFunction SOAMVariable SOMVariable
type SOMetaQFullSol = SOMetaQVar := SOMetaQSol
type SOMetaBaseQ = BaseCESQuery CAtomPF CTermF SOPredicate OPredicate OFunction OVariable SOAMVariable SOMVariable -- = LogicQuery SOMetaCNF SOMetaterm
type SOMetaQuery = CESQuery CAtomPF CTermF SOPredicate OPredicate OFunction OVariable SOAMVariable SOMVariable -- = Query SOMetaBaseQ SOMetaQVar SOMetaQSol

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
		case stripPrefix "[" xs of
		{
			Just rest -> (let r = (head (reads ('[':rest))::(LambdaCNF GroundSOMetaatomP,String))
				in [(CESQSol (Left (fst r)), (snd r))]);			
			Nothing -> error ("Cannot read ground term or atom: " ++ xs)
		}}}

instance Read SOMetaQParcSol where
	readsPrec _ xs =
		case stripPrefix "f" xs of
		{
     			Just rest -> (let r = (head (reads ('f':rest))::(SOMetatermF,String))
				in [(ParcCESQSol (Right (fst r)), (snd r))]);
			Nothing ->
		case stripPrefix "pi" xs of
		{
			Just rest -> (let r = (head (reads ('p':'i':rest))::(SOMetatermF,String))
				in [(ParcCESQSol (Right (fst r)), (snd r))]);
			Nothing -> 
		case stripPrefix "F" xs of
		{
			Just rest -> (let r = (head (reads ('p':'i':rest))::(SOMetatermF,String))
				in [(ParcCESQSol (Right (fst r)), (snd r))]);
			Nothing ->
		case stripPrefix "[" xs of
		{
			Just rest -> (let r = (head (reads ('[':rest))::(LambdaCNF SOMetaatomP,String))
				in [(ParcCESQSol (Left (fst r)), (snd r))]);			
			Nothing -> error ("Cannot read ground term or atom: " ++ xs)
		}}}}
