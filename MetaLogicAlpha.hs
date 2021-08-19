{-# LANGUAGE DeriveGeneric #-}
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
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE StandaloneDeriving #-}
-- Alpha equivalence of sets of equations.
module MetaLogicAlpha where

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
import Data.Maybe
import QueryLogic
import CESQLogic
import ESUnification
import EnumProc
import Control.Monad.ST
import Control.Monad.State
import AnswerSet
import Resolution
import SOResolution
import Algorithm
import Heuristics
import MetaLogic
import GHC.Base (liftA2)
import Similarity
import Equiv
import GHC.Generics (Generic)
import Data.Hashable

-- The entire purpose of all of this is to make the structures a single-parameter functor with the variables being what it depends on.
data SomeVariable v fmv pmv uv = SomeOVariable {unsomeovariable :: v} | SomeFVariable {unsomefvariable :: fmv} | SomePVariable {unsomepvariable :: pmv} | SomeUVariable {unsomeuvariable :: uv} deriving (Eq, Ord, Generic)

instance (Hashable v, Hashable fmv, Hashable pmv, Hashable uv) => Hashable (SomeVariable v fmv pmv uv)

someov :: v -> SomeVariable v fmv pmv uv
someov = SomeOVariable

somefmv :: fmv -> SomeVariable v fmv pmv uv
somefmv = SomeFVariable

somepmv :: pmv -> SomeVariable v fmv pmv uv
somepmv = SomePVariable

someuv :: uv -> SomeVariable v fmv pmv uv
someuv = SomeUVariable

instance (Show v, Show fmv, Show pmv, Show uv) => Show (SomeVariable v fmv pmv uv) where
	show (SomeOVariable v) = show v
	show (SomeFVariable fmv) = show fmv
	show (SomePVariable pmv) = show pmv
	show (SomeUVariable uv) = show uv

instance (HasArity v, HasArity fmv, HasArity pmv, HasArity uv) => HasArity (SomeVariable v fmv pmv uv) where
	arity (SomeOVariable v) = error "Trying to calculate the arity of an object variable!"
	arity (SomeFVariable fmv) = arity fmv
	arity (SomePVariable pmv) = arity pmv
	arity (SomeUVariable uv) = error "Trying to calculate the arity of a unifier variable!"

type SomeMetaVariable = SomeVariable OVariable SOMVariable SOAMVariable UnifVariable

-- Do note that for normalizable types (like functions and predicates), we assume normalization BEFORE applying similarity. Applying it during is too complex type-wise, and it can really be done before.



{-|
newtype SomeSOMetaCNFV sv = SomeSOMetaCNF {fromSomeSOMetaCNF :: CNF CAtomPF CTermF SOPredicate OPredicate OFunction sv sv sv}
type SomeSOMetaCNF = SomeSOMetaCNFV SomeMetaVariable
some_sometacnf :: SOMetaCNF -> SomeSOMetaCNF
some_sometacnf cnf = SomeSOMetaCNF (fmap (fromSomeSOMetaclause . some_sometaclause) cnf)

unsome_sometacnf :: SomeSOMetaCNF -> SOMetaCNF
unsome_sometacnf cnf = fmap (unsome_sometaclause . SomeSOMetaclause) (fromSomeSOMetaCNF cnf)

newtype SomeSOMetaclauseV sv = SomeSOMetaclause {fromSomeSOMetaclause :: Clause CAtomPF CTermF SOPredicate OPredicate OFunction sv sv sv}
type SomeSOMetaclause = SomeSOMetaclauseV SomeMetaVariable
some_sometaclause :: SOMetaclause -> SomeSOMetaclause
some_sometaclause cl = SomeSOMetaclause (fmap (fromSomeSOMetaliteral . some_sometaliteral) cl)

unsome_sometaclause :: SomeSOMetaclause -> SOMetaclause
unsome_sometaclause cl = undefined

newtype SomeSOMetaliteralV sv = SomeSOMetaliteral {fromSomeSOMetaliteral :: VarLiteral CAtomPF CTermF SOPredicate OPredicate OFunction sv sv sv}
type SomeSOMetaliteral = SomeSOMetaliteralV SomeMetaVariable
some_sometaliteral :: SOMetaliteral -> SomeSOMetaliteral
some_sometaliteral lit = SomeSOMetaliteral (fmap (fromSomeCombSOMetaatom . some_combsometaatom) lit)

|-}

-- The grand finale: I can consider if two systems of equations are alpha-equivalent!
sometaunifsystem_alpha_eq :: [SOMetaUnifEquation] -> [SOMetaUnifEquation] -> Bool
sometaunifsystem_alpha_eq sys1 sys2 = alpha_eq_wsim some_sometaunifsystem_similarities (some_sometaunifsystem sys1) (some_sometaunifsystem sys2)

newtype SomeSOMetaUnifSystemV sv = SomeSOMetaUnifSystem {fromSomeSOMetaUnifSystem :: [UnifEquation CAtomPF CTermF LambdaCNF SOPredicate OPredicate OFunction sv sv sv sv]}
type SomeSOMetaUnifSystem = SomeSOMetaUnifSystemV SomeMetaVariable
some_sometaunifsystem :: [SOMetaUnifEquation] -> SomeSOMetaUnifSystem
some_sometaunifsystem eqs = SomeSOMetaUnifSystem (fromSomeSOMetaUnifEquation . some_sometaunifequation <$> eqs)

unsome_sometaunifsystem :: SomeSOMetaUnifSystem -> [SOMetaUnifEquation]
unsome_sometaunifsystem (SomeSOMetaUnifSystem eqs) = unsome_sometaunifequation . SomeSOMetaUnifEquation <$> eqs

instance Functor SomeSOMetaUnifSystemV where
	fmap g (SomeSOMetaUnifSystem eqs) = SomeSOMetaUnifSystem (fmap (fromSomeSOMetaUnifEquation . (fmap g) . SomeSOMetaUnifEquation) eqs)

instance Foldable SomeSOMetaUnifSystemV where
	foldr g z (SomeSOMetaUnifSystem eqs) = homofoldr2 g (SomeSOMetaUnifEquation <$> eqs) z

instance Traversable SomeSOMetaUnifSystemV where
	traverse g (SomeSOMetaUnifSystem eqs) = SomeSOMetaUnifSystem <$> (fmap2 fromSomeSOMetaUnifEquation (traverse2 g (SomeSOMetaUnifEquation <$> eqs)))

-- Here we go. 
-- Unfortunately, we cannot produce an actual Similarity instance because that requires assuming Ord on the variables.
-- But we can produce the function that does what we want, and this shall suffice for now.
-- s sv == (wrapped) Either (SomeSOMetaTermDependantV sv) (SomeSOMetaAtomDependantV sv)
-- t ssv == EquivClasses sv
-- t (s sv) = EquivClasses (Either (SomeSOMetaTermDependantV sv) (SomeSOMetaAtomDependantV sv)) ~~ Equiv (Either (SomeSOMetaTermDependantV sv) (SomeSOMetaAtomDependantV sv))
some_sometaunifsystem_similarities :: (Hashable sv1, Ord sv1, Hashable sv2, Ord sv2) => SomeSOMetaUnifSystemV sv1 -> SomeSOMetaUnifSystemV sv2 -> Computation (Equiv (Either sv1 sv2))
some_sometaunifsystem_similarities (SomeSOMetaUnifSystem leqs) (SomeSOMetaUnifSystem reqs) = composite_similarities lequivcst requivcst
	where
		lequiv = produce_equivs_somesometaunifsystem (SomeSOMetaUnifEquation <$> leqs);
		requiv = produce_equivs_somesometaunifsystem (SomeSOMetaUnifEquation <$> reqs);
		lequivcs = equivclasses lequiv;
		requivcs = equivclasses requiv;
		lequivcst = SomeSOMetaSomeDependant <$> lequivcs;
		requivcst = SomeSOMetaSomeDependant <$> requivcs;


newtype SomeSOMetaSomeDependantV sv = SomeSOMetaSomeDependant {fromSomeSOMetaSomeDependant :: Either (SomeSOMetaTermDependantV sv) (SomeSOMetaAtomDependantV sv)} deriving (Eq, Ord, Show, Generic)

instance Hashable sv => Hashable (SomeSOMetaSomeDependantV sv)

instance Functor SomeSOMetaSomeDependantV where
	fmap g (SomeSOMetaSomeDependant (Left somt)) = (SomeSOMetaSomeDependant (Left (fmap g somt)))
	fmap g (SomeSOMetaSomeDependant (Right soma)) = (SomeSOMetaSomeDependant (Right (fmap g soma)))

instance Foldable SomeSOMetaSomeDependantV where
	foldr g z (SomeSOMetaSomeDependant (Left somt)) = homofoldr g somt z
	foldr g z (SomeSOMetaSomeDependant (Right soma)) = homofoldr g soma z

instance Traversable SomeSOMetaSomeDependantV where
	traverse g (SomeSOMetaSomeDependant (Left somt)) = (SomeSOMetaSomeDependant . Left) <$> (traverse g somt)
	traverse g (SomeSOMetaSomeDependant (Right soma)) = (SomeSOMetaSomeDependant . Right) <$> (traverse g soma)

instance Similarity SomeSOMetaSomeDependantV where
	similarities (SomeSOMetaSomeDependant (Left somt1)) (SomeSOMetaSomeDependant (Left somt2)) = similarities somt1 somt2
	similarities (SomeSOMetaSomeDependant (Right soma1)) (SomeSOMetaSomeDependant (Right soma2)) = similarities soma1 soma2
	similarities _ _ = emptycomp


produce_equivs_somesometaunifsystem :: (Hashable sv, Ord sv) => [SomeSOMetaUnifEquationV sv] -> Equiv (Either (SomeSOMetaTermDependantV sv) (SomeSOMetaAtomDependantV sv))
produce_equivs_somesometaunifsystem [] = empty_equiv
produce_equivs_somesometaunifsystem ((SomeSOMetaUnifEquation (TermUnif ltd rtd)):eqs) = (Left (SomeSOMetaTermDependant ltd)) =:~ (Left (SomeSOMetaTermDependant rtd)) $ (produce_equivs_somesometaunifsystem eqs)
produce_equivs_somesometaunifsystem ((SomeSOMetaUnifEquation (AtomUnif lad rad)):eqs) = (Right (SomeSOMetaAtomDependant lad)) =:~ (Right (SomeSOMetaAtomDependant rad)) $ (produce_equivs_somesometaunifsystem eqs)

newtype SomeSOMetaUnifEquationV sv = SomeSOMetaUnifEquation {fromSomeSOMetaUnifEquation :: UnifEquation CAtomPF CTermF LambdaCNF SOPredicate OPredicate OFunction sv sv sv sv} deriving (Show)
type SomeSOMetaUnifEquation = SomeSOMetaUnifEquationV SomeMetaVariable
some_sometaunifequation :: SOMetaUnifEquation -> SomeSOMetaUnifEquation
some_sometaunifequation (TermUnif ltd rtd) = SomeSOMetaUnifEquation (TermUnif ((fromSomeSOMetaTermDependant . some_sometatermdependant) ltd) ((fromSomeSOMetaTermDependant . some_sometatermdependant) rtd))
some_sometaunifequation (AtomUnif lad rad) = SomeSOMetaUnifEquation (AtomUnif ((fromSomeSOMetaAtomDependant . some_sometaatomdependant) lad) ((fromSomeSOMetaAtomDependant . some_sometaatomdependant) rad))

unsome_sometaunifequation :: SomeSOMetaUnifEquation -> SOMetaUnifEquation
unsome_sometaunifequation (SomeSOMetaUnifEquation (TermUnif ltd rtd)) = TermUnif ((unsome_sometatermdependant . SomeSOMetaTermDependant) ltd) ((unsome_sometatermdependant . SomeSOMetaTermDependant) rtd)
unsome_sometaunifequation (SomeSOMetaUnifEquation (AtomUnif lad rad)) = AtomUnif ((unsome_sometaatomdependant . SomeSOMetaAtomDependant) lad) ((unsome_sometaatomdependant . SomeSOMetaAtomDependant) rad)

instance Functor SomeSOMetaUnifEquationV where
	fmap g (SomeSOMetaUnifEquation (TermUnif ltd rtd)) = SomeSOMetaUnifEquation (TermUnif (fromSomeSOMetaTermDependant (fmap g (SomeSOMetaTermDependant ltd))) (fromSomeSOMetaTermDependant (fmap g (SomeSOMetaTermDependant rtd))))
	fmap g (SomeSOMetaUnifEquation (AtomUnif lad rad)) = SomeSOMetaUnifEquation (AtomUnif (fromSomeSOMetaAtomDependant (fmap g (SomeSOMetaAtomDependant lad))) (fromSomeSOMetaAtomDependant (fmap g (SomeSOMetaAtomDependant rad))))

instance Foldable SomeSOMetaUnifEquationV where
	foldr g z (SomeSOMetaUnifEquation (TermUnif ltd rtd)) = homofoldr g (SomeSOMetaTermDependant ltd) $ homofoldr g (SomeSOMetaTermDependant rtd) $ z
	foldr g z (SomeSOMetaUnifEquation (AtomUnif lad rad)) = homofoldr g (SomeSOMetaAtomDependant lad) $ homofoldr g (SomeSOMetaAtomDependant rad) $ z

instance Traversable SomeSOMetaUnifEquationV where
	traverse g (SomeSOMetaUnifEquation (TermUnif ltd rtd)) = SomeSOMetaUnifEquation <$> (liftA2 (\rltd -> \rrtd -> TermUnif (fromSomeSOMetaTermDependant rltd) (fromSomeSOMetaTermDependant rrtd)) (traverse g (SomeSOMetaTermDependant ltd)) (traverse g (SomeSOMetaTermDependant rtd)))
	traverse g (SomeSOMetaUnifEquation (AtomUnif lad rad)) = SomeSOMetaUnifEquation <$> (liftA2 (\rlad -> \rrad -> AtomUnif (fromSomeSOMetaAtomDependant rlad) (fromSomeSOMetaAtomDependant rrad)) (traverse g (SomeSOMetaAtomDependant lad)) (traverse g (SomeSOMetaAtomDependant rad)))

newtype SomeSOMetaTermDependantV sv = SomeSOMetaTermDependant {fromSomeSOMetaTermDependant :: TermDependant CTermF OFunction sv sv sv} deriving (Eq, Ord, Show, Generic)

instance Hashable sv => Hashable (SomeSOMetaTermDependantV sv)

type SomeSOMetaTermDependant = SomeSOMetaTermDependantV SomeMetaVariable
some_sometatermdependant :: SOMetaTermDependant -> SomeSOMetaTermDependant
some_sometatermdependant (TDUnif uv std) = SomeSOMetaTermDependant (TDUnif (SomeUVariable uv) (fromSomeSOMetaTermDependant (some_sometatermdependant std)))
some_sometatermdependant (TDDirect somt) = SomeSOMetaTermDependant (TDDirect (fromSomeSOMetaterm (some_sometaterm somt)))

unsome_sometatermdependant :: SomeSOMetaTermDependant -> SOMetaTermDependant
unsome_sometatermdependant (SomeSOMetaTermDependant (TDUnif uv std)) = TDUnif (unsomeuvariable uv) (unsome_sometatermdependant (SomeSOMetaTermDependant std))
unsome_sometatermdependant (SomeSOMetaTermDependant (TDDirect somt)) = TDDirect (unsome_sometaterm (SomeSOMetaterm somt))

instance Functor SomeSOMetaTermDependantV where
	fmap g (SomeSOMetaTermDependant (TDUnif uv td)) = SomeSOMetaTermDependant (TDUnif (g uv) (fromSomeSOMetaTermDependant (fmap g (SomeSOMetaTermDependant td))))
	fmap g (SomeSOMetaTermDependant (TDDirect somt)) = SomeSOMetaTermDependant (TDDirect (fromSomeSOMetaterm (fmap g (SomeSOMetaterm somt))))

instance Foldable SomeSOMetaTermDependantV where
	foldr g z (SomeSOMetaTermDependant (TDUnif uv td)) = g uv $ homofoldr g (SomeSOMetaTermDependant td) $ z
	foldr g z (SomeSOMetaTermDependant (TDDirect somt)) = homofoldr g (SomeSOMetaterm somt) z

instance Traversable SomeSOMetaTermDependantV where
	traverse g (SomeSOMetaTermDependant (TDUnif uv td)) = SomeSOMetaTermDependant <$> (liftA2 (\ruv -> \rtd -> TDUnif ruv (fromSomeSOMetaTermDependant rtd)) (g uv) (traverse g (SomeSOMetaTermDependant td)))
	traverse g (SomeSOMetaTermDependant (TDDirect somt)) = (SomeSOMetaTermDependant . TDDirect . fromSomeSOMetaterm) <$> (traverse g (SomeSOMetaterm somt))

instance Similarity SomeSOMetaTermDependantV where
	similarities (SomeSOMetaTermDependant (TDUnif uv1 td1)) (SomeSOMetaTermDependant (TDUnif uv2 td2)) = (alg ((Left uv1) =:~ (Right uv2) $)) ... (similarities (SomeSOMetaTermDependant td1) (SomeSOMetaTermDependant td2))
	similarities (SomeSOMetaTermDependant (TDDirect somt1)) (SomeSOMetaTermDependant (TDDirect somt2)) = similarities (SomeSOMetaterm somt1) (SomeSOMetaterm somt2)
	similarities _ _ = emptycomp

newtype SomeSOMetaAtomDependantV sv = SomeSOMetaAtomDependant {fromSomeSOMetaAtomDependant :: AtomDependant CAtomPF CTermF LambdaCNF SOPredicate OPredicate OFunction sv sv sv sv} deriving (Eq, Ord, Show, Generic)

instance Hashable sv => Hashable (SomeSOMetaAtomDependantV sv)

type SomeSOMetaAtomDependant = SomeSOMetaAtomDependantV SomeMetaVariable
some_sometaatomdependant :: SOMetaAtomDependant -> SomeSOMetaAtomDependant
some_sometaatomdependant (ADUnif uv atd) = SomeSOMetaAtomDependant (ADUnif (SomeUVariable uv) (fromSomeSOMetaAtomDependant (some_sometaatomdependant atd)))
some_sometaatomdependant (ADDirect csoa) = SomeSOMetaAtomDependant (ADDirect (fromSomeCombSOMetaatom (some_combsometaatom csoa)))

unsome_sometaatomdependant :: SomeSOMetaAtomDependant -> SOMetaAtomDependant
unsome_sometaatomdependant (SomeSOMetaAtomDependant (ADUnif uv atd)) = ADUnif (unsomeuvariable uv) (unsome_sometaatomdependant (SomeSOMetaAtomDependant atd))
unsome_sometaatomdependant (SomeSOMetaAtomDependant (ADDirect csoa)) = ADDirect (unsome_combsometaatom (SomeCombSOMetaatom csoa))


instance Functor SomeSOMetaAtomDependantV where
	fmap g (SomeSOMetaAtomDependant (ADUnif uv atd)) = SomeSOMetaAtomDependant (ADUnif (g uv) (fromSomeSOMetaAtomDependant (fmap g (SomeSOMetaAtomDependant atd))))
	fmap g (SomeSOMetaAtomDependant (ADDirect csoa)) = SomeSOMetaAtomDependant (ADDirect (fromSomeCombSOMetaatom (fmap g (SomeCombSOMetaatom csoa))))

instance Foldable SomeSOMetaAtomDependantV where
	foldr g z (SomeSOMetaAtomDependant (ADUnif uv atd)) = g uv $ homofoldr g (SomeSOMetaAtomDependant atd) $ z
	foldr g z (SomeSOMetaAtomDependant (ADDirect csoa)) = homofoldr g (SomeCombSOMetaatom csoa) z

instance Traversable SomeSOMetaAtomDependantV where
	traverse g (SomeSOMetaAtomDependant (ADUnif uv atd)) = SomeSOMetaAtomDependant <$> (liftA2 (\ruv -> \ratd -> ADUnif ruv (fromSomeSOMetaAtomDependant ratd)) (g uv) (traverse g (SomeSOMetaAtomDependant atd)))
	traverse g (SomeSOMetaAtomDependant (ADDirect csoa)) = (SomeSOMetaAtomDependant . ADDirect . fromSomeCombSOMetaatom) <$> (traverse g (SomeCombSOMetaatom csoa))

instance Similarity SomeSOMetaAtomDependantV where
	similarities (SomeSOMetaAtomDependant (ADUnif uv1 atd1)) (SomeSOMetaAtomDependant (ADUnif uv2 atd2)) = (alg ((Left uv1) =:~ (Right uv2) $)) ... (similarities (SomeSOMetaAtomDependant atd1) (SomeSOMetaAtomDependant atd2))
	similarities (SomeSOMetaAtomDependant (ADDirect csoa1)) (SomeSOMetaAtomDependant (ADDirect csoa2)) = similarities (SomeCombSOMetaatom csoa1) (SomeCombSOMetaatom csoa2)
	similarities _ _ = emptycomp

newtype SomeSOMetatermV sv = SomeSOMetaterm {fromSomeSOMetaterm :: SOMetawrap CTermF OFunction sv sv} deriving (Eq, Ord, Show, Generic)

instance Hashable sv => Hashable (SomeSOMetatermV sv)

type SomeSOMetaterm = SomeSOMetatermV SomeMetaVariable
some_sometaterm :: SOMetaterm -> SomeSOMetaterm
some_sometaterm (SOMetawrap (UVar v)) = SomeSOMetaterm (SOMetawrap (UVar (SomeOVariable v)))
some_sometaterm (SOMetawrap (UTerm t)) = SomeSOMetaterm (SOMetawrap (UTerm (build_term (fromSomeSOMetatermF (some_sometatermf h)) (fmap (fromSOMetawrap . fromSomeSOMetaterm . some_sometaterm . SOMetawrap) sts)))) where (h,sts) = unbuild_term t

unsome_sometaterm :: SomeSOMetaterm -> SOMetaterm
unsome_sometaterm (SomeSOMetaterm (SOMetawrap (UVar v))) = SOMetawrap (UVar (unsomeovariable v))
unsome_sometaterm (SomeSOMetaterm (SOMetawrap (UTerm t))) = SOMetawrap (UTerm (build_term (unsome_sometatermf (SomeSOMetatermF h)) (fmap (fromSOMetawrap . unsome_sometaterm . SomeSOMetaterm . SOMetawrap) sts))) where (h,sts) = unbuild_term t

instance Functor SomeSOMetatermV where
	fmap g (SomeSOMetaterm (SOMetawrap (UVar v))) = SomeSOMetaterm (SOMetawrap (UVar (g v)))
	fmap g (SomeSOMetaterm (SOMetawrap (UTerm t))) = SomeSOMetaterm (SOMetawrap (UTerm (build_term (fromSomeSOMetatermF (fmap g (SomeSOMetatermF h))) (fmap (fromSOMetawrap . fromSomeSOMetaterm . (fmap g) . SomeSOMetaterm . SOMetawrap) sts)))) where (h,sts) = unbuild_term t

instance Foldable SomeSOMetatermV where
	foldr g z (SomeSOMetaterm (SOMetawrap (UVar v))) = g v z
	foldr g z (SomeSOMetaterm (SOMetawrap (UTerm t))) = homofoldr g (SomeSOMetatermF h) $ homofoldr2 g ((SomeSOMetaterm . SOMetawrap) <$> sts) $ z where (h,sts) = unbuild_term t

instance Traversable SomeSOMetatermV where
	traverse g (SomeSOMetaterm (SOMetawrap (UVar v))) = (SomeSOMetaterm . SOMetawrap . UVar) <$> (g v)
	traverse g (SomeSOMetaterm (SOMetawrap (UTerm t))) = (SomeSOMetaterm . SOMetawrap . UTerm) <$> (liftA2 (\rh -> \rsts -> build_term (fromSomeSOMetatermF rh) ((fromSOMetawrap . fromSomeSOMetaterm) <$> rsts)) (traverse g (SomeSOMetatermF h)) (traverse2 g ((SomeSOMetaterm . SOMetawrap) <$> sts))) where (h,sts) = unbuild_term t

instance Similarity SomeSOMetatermV where
	similarities (SomeSOMetaterm (SOMetawrap (UVar v1))) (SomeSOMetaterm (SOMetawrap (UVar v2))) = comp ((Left v1) =:~ (Right v2) $ empty_equiv)
	similarities (SomeSOMetaterm (SOMetawrap (UTerm t1))) (SomeSOMetaterm (SOMetawrap (UTerm t2))) = do {hsim <- similarities (SomeSOMetatermF h1) (SomeSOMetatermF h2); ssim <- composite_similarities (PosSimilarList ((SomeSOMetaterm . SOMetawrap) <$> sts1)) (PosSimilarList ((SomeSOMetaterm . SOMetawrap) <$> sts2)); return (hsim <> ssim)} where (h1,sts1) = unbuild_term t1; (h2,sts2) = unbuild_term t2
	similarities _ _ = emptycomp

newtype SomeCombSOMetaatomV sv = SomeCombSOMetaatom {fromSomeCombSOMetaatom :: CombSOAtom CAtomPF CTermF LambdaCNF SOPredicate OPredicate OFunction sv sv sv}
type SomeCombSOMetaatom = SomeCombSOMetaatomV SomeMetaVariable
some_combsometaatom :: CombSOMetaatom -> SomeCombSOMetaatom
some_combsometaatom (NSOAtom soma) = SomeCombSOMetaatom (NSOAtom (fromSomeSOMetaatom (some_sometaatom soma)))
some_combsometaatom (FSOAtom fsomaa) = SomeCombSOMetaatom (FSOAtom (fromSomeFirstSOMetaAAtom (some_firstsometaaatom fsomaa)))

unsome_combsometaatom :: SomeCombSOMetaatom -> CombSOMetaatom
unsome_combsometaatom (SomeCombSOMetaatom (NSOAtom soma)) = NSOAtom (unsome_sometaatom (SomeSOMetaatom soma))
unsome_combsometaatom (SomeCombSOMetaatom (FSOAtom fsomaa)) = FSOAtom (unsome_firstsometaaatom (SomeFirstSOMetaAAtom fsomaa))

instance Functor SomeCombSOMetaatomV where
	fmap g (SomeCombSOMetaatom (NSOAtom soma)) = SomeCombSOMetaatom (NSOAtom (fromSomeSOMetaatom (fmap g (SomeSOMetaatom soma))))
	fmap g (SomeCombSOMetaatom (FSOAtom fsomaa)) = SomeCombSOMetaatom (FSOAtom (fromSomeFirstSOMetaAAtom (fmap g (SomeFirstSOMetaAAtom fsomaa))))

instance Foldable SomeCombSOMetaatomV where
	foldr g z (SomeCombSOMetaatom (NSOAtom soma)) = homofoldr g (SomeSOMetaatom soma) z
	foldr g z (SomeCombSOMetaatom (FSOAtom fsomaa)) = homofoldr g (SomeFirstSOMetaAAtom fsomaa) z

instance Traversable SomeCombSOMetaatomV where
	traverse g (SomeCombSOMetaatom (NSOAtom soma)) = (SomeCombSOMetaatom . NSOAtom . fromSomeSOMetaatom) <$> (traverse g (SomeSOMetaatom soma))
	traverse g (SomeCombSOMetaatom (FSOAtom fsomaa)) = (SomeCombSOMetaatom . FSOAtom . fromSomeFirstSOMetaAAtom) <$> (traverse g (SomeFirstSOMetaAAtom fsomaa))

instance Similarity SomeCombSOMetaatomV where
	similarities (SomeCombSOMetaatom (NSOAtom soma1)) (SomeCombSOMetaatom (NSOAtom soma2)) = similarities (SomeSOMetaatom soma1) (SomeSOMetaatom soma2)
	similarities (SomeCombSOMetaatom (FSOAtom fsomaa1)) (SomeCombSOMetaatom (FSOAtom fsomaa2)) = similarities (SomeFirstSOMetaAAtom fsomaa1) (SomeFirstSOMetaAAtom fsomaa2)
	similarities _ _ = emptycomp

newtype SomeSOMetatermFV sv = SomeSOMetatermF {fromSomeSOMetatermF :: SOTerm OFunction sv} deriving (Eq, Ord, Generic)

instance Hashable sv => Hashable (SomeSOMetatermFV sv)

type SomeSOMetatermF = SomeSOMetatermFV SomeMetaVariable
some_sometatermf :: SOMetatermF -> SomeSOMetatermF
some_sometatermf (UVar fmv) = SomeSOMetatermF (UVar (SomeFVariable fmv))
some_sometatermf (UTerm (SOF (ConstF f))) = SomeSOMetatermF (UTerm (SOF (ConstF f)))
some_sometatermf (UTerm (SOF (Proj idx))) = SomeSOMetatermF (UTerm (SOF (Proj idx)))
some_sometatermf (UTerm (SOF (CompF f sfs))) = SomeSOMetatermF (UTerm (SOF (CompF (fromSomeSOMetatermF (some_sometatermf f)) (fmap (fromSomeSOMetatermF . some_sometatermf) sfs))))

unsome_sometatermf :: SomeSOMetatermF -> SOMetatermF
unsome_sometatermf (SomeSOMetatermF (UVar fmv)) = UVar (unsomefvariable fmv)
unsome_sometatermf (SomeSOMetatermF (UTerm (SOF (ConstF f)))) = UTerm (SOF (ConstF f))
unsome_sometatermf (SomeSOMetatermF (UTerm (SOF (Proj idx)))) = UTerm (SOF (Proj idx))
unsome_sometatermf (SomeSOMetatermF (UTerm (SOF (CompF f sfs)))) = UTerm (SOF (CompF (unsome_sometatermf (SomeSOMetatermF f)) (fmap (unsome_sometatermf . SomeSOMetatermF) sfs)))

instance Functor SomeSOMetatermFV where
	fmap g (SomeSOMetatermF (UVar fmv)) = SomeSOMetatermF (UVar (g fmv))
	fmap g (SomeSOMetatermF (UTerm (SOF (ConstF f)))) = SomeSOMetatermF (UTerm (SOF (ConstF f)))
	fmap g (SomeSOMetatermF (UTerm (SOF (Proj idx)))) = SomeSOMetatermF (UTerm (SOF (Proj idx)))
	fmap g (SomeSOMetatermF (UTerm (SOF (CompF f sfs)))) = SomeSOMetatermF (UTerm (SOF (CompF (fromSomeSOMetatermF (fmap g (SomeSOMetatermF f))) (fmap (fromSomeSOMetatermF . (fmap g) . SomeSOMetatermF) sfs))))

instance Foldable SomeSOMetatermFV where
	foldr g z (SomeSOMetatermF (UVar fmv)) = g fmv z
	foldr g z (SomeSOMetatermF (UTerm (SOF (ConstF f)))) = z
	foldr g z (SomeSOMetatermF (UTerm (SOF (Proj idx)))) = z
	foldr g z (SomeSOMetatermF (UTerm (SOF (CompF f sfs)))) = homofoldr g (SomeSOMetatermF f) $ homofoldr2 g (SomeSOMetatermF <$> sfs) $ z

instance Traversable SomeSOMetatermFV where
	traverse g (SomeSOMetatermF (UVar fmv)) = SomeSOMetatermF . UVar <$> g fmv
	traverse g (SomeSOMetatermF (UTerm (SOF (ConstF f)))) = pure (SomeSOMetatermF (UTerm (SOF (ConstF f))))
	traverse g (SomeSOMetatermF (UTerm (SOF (Proj idx)))) = pure (SomeSOMetatermF (UTerm (SOF (Proj idx))))
	traverse g (SomeSOMetatermF (UTerm (SOF (CompF f sfs)))) = liftA2 (\rf -> \rsfs -> SomeSOMetatermF (UTerm (SOF (CompF (fromSomeSOMetatermF rf) (fromSomeSOMetatermF <$> rsfs))))) (traverse g (SomeSOMetatermF f)) (traverse2 g (SomeSOMetatermF <$> sfs))

instance Similarity SomeSOMetatermFV where
	similarities (SomeSOMetatermF (UVar fmv1)) (SomeSOMetatermF (UVar fmv2)) = comp ((Left fmv1) =:~ (Right fmv2) $ empty_equiv)
	similarities (SomeSOMetatermF (UTerm (SOF (ConstF f1)))) (SomeSOMetatermF (UTerm (SOF (ConstF f2)))) | f1 == f2 = comp empty_equiv
	similarities (SomeSOMetatermF (UTerm (SOF (Proj idx1)))) (SomeSOMetatermF (UTerm (SOF (Proj idx2)))) | idx1 == idx2 = comp empty_equiv
	similarities (SomeSOMetatermF (UTerm (SOF (CompF h1 sfs1)))) (SomeSOMetatermF (UTerm (SOF (CompF h2 sfs2)))) = do {hsim <- similarities (SomeSOMetatermF h1) (SomeSOMetatermF h2); ssim <- composite_similarities (PosSimilarList (SomeSOMetatermF <$> sfs1)) (PosSimilarList (SomeSOMetatermF <$> sfs2)); return (hsim <> ssim)}
	similarities _ _ = emptycomp

newtype SomeSOMetaatomV sv = SomeSOMetaatom {fromSomeSOMetaatom :: SOMetawrapA CAtomPF CTermF OPredicate OFunction sv sv sv}
type SomeSOMetaatom = SomeSOMetaatomV SomeMetaVariable
some_sometaatom :: SOMetaatom -> SomeSOMetaatom
some_sometaatom (SOMetawrapA a) = SomeSOMetaatom (SOMetawrapA (build_term (fromSomeSOMetaatomP (some_sometaatomp p)) (fmap (fromSomeSOMetaterm . some_sometaterm) ts))) where (p,ts) = unbuild_term a

unsome_sometaatom :: SomeSOMetaatom -> SOMetaatom
unsome_sometaatom (SomeSOMetaatom (SOMetawrapA a)) = SOMetawrapA (build_term (unsome_sometaatomp (SomeSOMetaatomP p)) (fmap (unsome_sometaterm . SomeSOMetaterm) ts)) where (p,ts) = unbuild_term a

instance Functor SomeSOMetaatomV where
	fmap g (SomeSOMetaatom (SOMetawrapA a)) = (SomeSOMetaatom (SOMetawrapA (build_term (fromSomeSOMetaatomP (fmap g (SomeSOMetaatomP h))) (fmap (fromSomeSOMetaterm . (fmap g) . SomeSOMetaterm) sts)))) where (h,sts) = unbuild_term a

instance Foldable SomeSOMetaatomV where
	foldr g z (SomeSOMetaatom (SOMetawrapA a)) = homofoldr g (SomeSOMetaatomP h) $ homofoldr2 g (SomeSOMetaterm <$> sts) $ z where (h,sts) = unbuild_term a

instance Traversable SomeSOMetaatomV where
	traverse g (SomeSOMetaatom (SOMetawrapA a)) = (SomeSOMetaatom . SOMetawrapA) <$> (liftA2 (\rh -> \rsts -> build_term (fromSomeSOMetaatomP rh) (fromSomeSOMetaterm <$> rsts)) (traverse g (SomeSOMetaatomP h)) (traverse2 g (SomeSOMetaterm <$> sts))) where (h,sts) = unbuild_term a

instance Similarity SomeSOMetaatomV where
	similarities (SomeSOMetaatom (SOMetawrapA a1)) (SomeSOMetaatom (SOMetawrapA a2)) = do {hsim <- similarities (SomeSOMetaatomP h1) (SomeSOMetaatomP h2); ssim <- composite_similarities (PosSimilarList (SomeSOMetaterm <$> sts1)) (PosSimilarList (SomeSOMetaterm <$> sts2)); return (hsim <> ssim)} where (h1,sts1) = unbuild_term a1; (h2,sts2) = unbuild_term a2
	similarities _ _ = emptycomp

newtype SomeFirstSOMetaAAtomV sv = SomeFirstSOMetaAAtom {fromSomeFirstSOMetaAAtom :: FirstSOAAtom CAtomPF LambdaCNF SOPredicate OPredicate OFunction sv sv}
type SomeFirstSOMetaAAtom = SomeFirstSOMetaAAtomV SomeMetaVariable
some_firstsometaaatom :: FirstSOMetaAAtom -> SomeFirstSOMetaAAtom
some_firstsometaaatom (FirstSOAAtom a) = SomeFirstSOMetaAAtom (FirstSOAAtom (build_term mp (fmap (fmap (fromSomeSOMetaatomP . some_sometaatomp)) ssoas))) where (mp,ssoas) = unbuild_term a

unsome_firstsometaaatom :: SomeFirstSOMetaAAtom -> FirstSOMetaAAtom
unsome_firstsometaaatom (SomeFirstSOMetaAAtom (FirstSOAAtom a)) = FirstSOAAtom (build_term mp (fmap (fmap (unsome_sometaatomp . SomeSOMetaatomP)) ssoas)) where (mp,ssoas) = unbuild_term a

instance Functor SomeFirstSOMetaAAtomV where
	fmap g (SomeFirstSOMetaAAtom (FirstSOAAtom a)) = SomeFirstSOMetaAAtom (FirstSOAAtom (build_term mp (fmap (fmap (fromSomeSOMetaatomP . (fmap g) . SomeSOMetaatomP)) ssoas))) where (mp,ssoas) = unbuild_term a

instance Foldable SomeFirstSOMetaAAtomV where
	foldr g z (SomeFirstSOMetaAAtom (FirstSOAAtom a)) = homofoldr3 g ((fmap SomeSOMetaatomP) <$> ssoas) $ z where (mp,ssoas) = unbuild_term a

instance Traversable SomeFirstSOMetaAAtomV where
	traverse g (SomeFirstSOMetaAAtom (FirstSOAAtom a)) = SomeFirstSOMetaAAtom . FirstSOAAtom <$> (fmap (build_term mp) (fmap3 fromSomeSOMetaatomP (traverse3 g (fmap2 SomeSOMetaatomP ssoas)))) where (mp,ssoas) = unbuild_term a

newtype ListLambdaCNF t = ListLambdaCNF [LambdaCNF t] deriving (Eq, Ord, Generic)

instance Hashable t => Hashable (ListLambdaCNF t)

instance Functor ListLambdaCNF where
	fmap g (ListLambdaCNF l) = ListLambdaCNF (fmap2 g l)

instance Foldable ListLambdaCNF where
	foldr g z (ListLambdaCNF l) = homofoldr2 g l z

instance Traversable ListLambdaCNF where
	traverse g (ListLambdaCNF l) = ListLambdaCNF <$> (traverse2 g l)

instance Similarity ListLambdaCNF where
	similarities (ListLambdaCNF l1) (ListLambdaCNF l2) = composite_similarities (SetSimilarList l1) (SetSimilarList l2)

instance Similarity SomeFirstSOMetaAAtomV where
	similarities (SomeFirstSOMetaAAtom (FirstSOAAtom a1)) (SomeFirstSOMetaAAtom (FirstSOAAtom a2)) | mp1 == mp2 = composite_similarities (SomeSOMetaatomP <$> xssoas1) (SomeSOMetaatomP <$> xssoas2) where (mp1,ssoas1) = unbuild_term a1; (mp2,ssoas2) = unbuild_term a2; xssoas1 = ListLambdaCNF ssoas1; xssoas2 = ListLambdaCNF ssoas2
	similarities _ _ = emptycomp

newtype SomeSOMetaatomPV sv = SomeSOMetaatomP {fromSomeSOMetaatomP :: SOAtom OPredicate OFunction sv sv} deriving (Eq, Ord, Generic)

instance Hashable sv => Hashable (SomeSOMetaatomPV sv)

type SomeSOMetaatomP = SomeSOMetaatomPV SomeMetaVariable
some_sometaatomp :: SOMetaatomP -> SomeSOMetaatomP
some_sometaatomp (UVar pmv) = SomeSOMetaatomP (UVar (SomePVariable pmv))
some_sometaatomp (UTerm (SOP (ConstF p))) = SomeSOMetaatomP (UTerm (SOP (ConstF p)))
-- No projections
some_sometaatomp (UTerm (SOP (CompF p sfs))) = SomeSOMetaatomP (UTerm (SOP (CompF (fromSomeSOMetaatomP (some_sometaatomp p)) (fmap (fromSomeSOMetatermF . some_sometatermf) sfs))))

unsome_sometaatomp :: SomeSOMetaatomP -> SOMetaatomP
unsome_sometaatomp (SomeSOMetaatomP (UVar pmv)) = UVar (unsomepvariable pmv)
unsome_sometaatomp (SomeSOMetaatomP (UTerm (SOP (ConstF p)))) = UTerm (SOP (ConstF p))
unsome_sometaatomp (SomeSOMetaatomP (UTerm (SOP (CompF p sfs)))) = UTerm (SOP (CompF (unsome_sometaatomp (SomeSOMetaatomP p)) (fmap (unsome_sometatermf . SomeSOMetatermF) sfs)))

instance Functor SomeSOMetaatomPV where
	fmap g (SomeSOMetaatomP (UVar pmv)) = SomeSOMetaatomP (UVar (g pmv))
	fmap g (SomeSOMetaatomP (UTerm (SOP (ConstF p)))) = SomeSOMetaatomP (UTerm (SOP (ConstF p)))
	fmap g (SomeSOMetaatomP (UTerm (SOP (CompF p sfs)))) = SomeSOMetaatomP (UTerm (SOP (CompF (fromSomeSOMetaatomP (fmap g (SomeSOMetaatomP p))) (fmap (fromSomeSOMetatermF . (fmap g) . SomeSOMetatermF) sfs))))

instance Foldable SomeSOMetaatomPV where
	foldr g z (SomeSOMetaatomP (UVar pmv)) = g pmv z
	foldr g z (SomeSOMetaatomP (UTerm (SOP (ConstF p)))) = z
	foldr g z (SomeSOMetaatomP (UTerm (SOP (CompF p sfs)))) = homofoldr g (SomeSOMetaatomP p) $ homofoldr2 g (SomeSOMetatermF <$> sfs) $ z

instance Traversable SomeSOMetaatomPV where
	traverse g (SomeSOMetaatomP (UVar pmv)) = SomeSOMetaatomP . UVar <$> g pmv
	traverse g (SomeSOMetaatomP (UTerm (SOP (ConstF p)))) = pure (SomeSOMetaatomP (UTerm (SOP (ConstF p))))
	traverse g (SomeSOMetaatomP (UTerm (SOP (CompF p sfs)))) = liftA2 (\rp -> \rsfs -> SomeSOMetaatomP (UTerm (SOP (CompF (fromSomeSOMetaatomP rp) (fromSomeSOMetatermF <$> rsfs))))) (traverse g (SomeSOMetaatomP p)) (traverse2 g (SomeSOMetatermF <$> sfs))

instance Similarity SomeSOMetaatomPV where
	similarities (SomeSOMetaatomP (UVar pmv1)) (SomeSOMetaatomP (UVar pmv2)) = comp ((Left pmv1) =:~ (Right pmv2) $ empty_equiv)
	similarities (SomeSOMetaatomP (UTerm (SOP (ConstF p1)))) (SomeSOMetaatomP (UTerm (SOP (ConstF p2)))) | p1 == p2 = comp empty_equiv
	similarities (SomeSOMetaatomP (UTerm (SOP (CompF h1 sfs1)))) (SomeSOMetaatomP (UTerm (SOP (CompF h2 sfs2)))) = do {hsim <- similarities (SomeSOMetaatomP h1) (SomeSOMetaatomP h2); ssim <- composite_similarities (PosSimilarList (SomeSOMetatermF <$> sfs1)) (PosSimilarList (SomeSOMetatermF <$> sfs2)); return (hsim <> ssim)}
	similarities _ _ = emptycomp

