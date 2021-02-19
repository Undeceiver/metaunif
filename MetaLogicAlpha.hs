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

-- The entire purpose of all of this is to make the structures a single-parameter functor with the variables being what it depends on.
data SomeVariable v fmv pmv uv = SomeOVariable v | SomeFVariable fmv | SomePVariable pmv | SomeUVariable uv deriving (Eq, Ord)

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

type SomeMetaVariable = SomeVariable OVariable SOMVariable SOAMVariable UnifVariable

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

newtype SomeCombSOMetaatomV sv = SomeCombSOMetaatom {fromSomeCombSOMetaatom :: CombSOAtom CAtomPF CTermF LambdaCNF SOPredicate OPredicate OFunction sv sv sv}
type SomeCombSOMetaatom = SomeCombSOMetaatomV SomeMetaVariable
some_combsometaatom :: CombSOMetaatom -> SomeCombSOMetaatom
some_combsometaatom csoa = undefined
|-}

newtype SomeSOMetaUnifEquationV sv = SomeSOMetaUnifEquation {fromSomeSOMetaUnifEquation :: UnifEquation CAtomPF CTermF LambdaCNF SOPredicate OPredicate OFunction sv sv sv sv} deriving (Show)
type SomeSOMetaUnifEquation = SomeSOMetaUnifEquationV SomeMetaVariable
some_sometaunifequation :: SOMetaUnifEquation -> SomeSOMetaUnifEquation
some_sometaunifequation (TermUnif ltd rtd) = SomeSOMetaUnifEquation (TermUnif ((fromSomeSOMetaTermDependant . some_sometatermdependant) ltd) ((fromSomeSOMetaTermDependant . some_sometatermdependant) rtd))
some_sometaunifequation (AtomUnif lad rad) = SomeSOMetaUnifEquation (AtomUnif ((fromSomeSOMetaAtomDependant . some_sometaatomdependant) lad) ((fromSomeSOMetaAtomDependant . some_sometaatomdependant) rad))

unsome_sometaunifequation :: SomeSOMetaUnifEquation -> SOMetaUnifEquation
unsome_sometaunifequation (SomeSOMetaUnifEquation (TermUnif ltd rtd)) = TermUnif ((unsome_sometatermdependant . SomeSOMetaTermDependant) ltd) ((unsome_sometatermdependant . SomeSOMetaTermDependant) rtd)
unsome_sometaunifequation (SomeSOMetaUnifEquation (AtomUnif lad rad)) = AtomUnif ((unsome_sometaatomdependant . SomeSOMetaAtomDependant) lad) ((unsome_sometaatomdependant . SomeSOMetaAtomDependant) rad)

newtype SomeSOMetaTermDependantV sv = SomeSOMetaTermDependant {fromSomeSOMetaTermDependant :: TermDependant CTermF OFunction sv sv sv} deriving (Eq, Show)
type SomeSOMetaTermDependant = SomeSOMetaTermDependantV SomeMetaVariable
some_sometatermdependant :: SOMetaTermDependant -> SomeSOMetaTermDependant
some_sometatermdependant = undefined

unsome_sometatermdependant :: SomeSOMetaTermDependant -> SOMetaTermDependant
unsome_sometatermdependant = undefined

newtype SomeSOMetaAtomDependantV sv = SomeSOMetaAtomDependant {fromSomeSOMetaAtomDependant :: AtomDependant CAtomPF CTermF LambdaCNF SOPredicate OPredicate OFunction sv sv sv sv} deriving (Eq, Show)
type SomeSOMetaAtomDependant = SomeSOMetaAtomDependantV SomeMetaVariable
some_sometaatomdependant :: SOMetaAtomDependant -> SomeSOMetaAtomDependant
some_sometaatomdependant = undefined

unsome_sometaatomdependant :: SomeSOMetaAtomDependant -> SOMetaAtomDependant
unsome_sometaatomdependant = undefined
