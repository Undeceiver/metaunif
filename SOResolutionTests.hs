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
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
module SOResolutionTests where

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
import Data.Functor.Fixedpoint
import Data.List
import Data.Map.Strict
import AnswerSet
import EnumProc
import Data.Maybe
import Data.Graph
import Data.Bifunctor
import Control.Lens
import Control.Monad.State
import Control.Monad.Morph
import Algorithm
import Provenance
import CESQResolutionProvenance
import DependencyGraph
import Identifier
import Control.Monad.ST
import Operable
import Data.Tuple
import Debug.Trace
import Safe (maximumMay, minimumMay)
import GlobalTrace
import ESUnification
import Heuristics
import Resolution
import SOResolution
import MetaLogic
import AutoTests
import Similarity



rslv_to_eqs_sig_1 :: SOMetaSignature
rslv_to_eqs_sig_1 = SOSignature (Signature [read "p1[0]" --> EnumProc.Empty] [] (EnumProc.Empty)) (EnumProc.Empty) EnumProc.Empty EnumProc.Empty

rslv_to_eqs_cnf_1 :: SOMetaCNF
rslv_to_eqs_cnf_1 = read "[[+p1[0]()],[-p1[0]()]]"

rslv_to_eqs_eqs_1 :: EnumProc [SOMetaUnifEquation]
rslv_to_eqs_eqs_1 = resolve_to_constraints_metacnf_enum rslv_to_eqs_sig_1 rslv_to_eqs_cnf_1

rslv_to_eqs_1_t1 :: AutomatedTest
rslv_to_eqs_1_t1 = check_exactly_enum "Checking there is exactly one proof for [[+p1[0]()],[-p1[0]()]]" 1 rslv_to_eqs_eqs_1

rslv_to_eqs_1_t2 :: AutomatedTest
rslv_to_eqs_1_t2 = undefined

rslv_to_eqs_sig_2 :: SOMetaSignature
rslv_to_eqs_sig_2 = SOSignature (Signature [read "p1[0]" --> EnumProc.Empty] [] (EnumProc.Empty)) (EnumProc.Empty) EnumProc.Empty EnumProc.Empty

rslv_to_eqs_cnf_2 :: SOMetaCNF
rslv_to_eqs_cnf_2 = read "[[+p1[0]()],[+p1[0]()]]"

rslv_to_eqs_eqs_2 :: EnumProc [SOMetaUnifEquation]
rslv_to_eqs_eqs_2 = resolve_to_constraints_metacnf_enum rslv_to_eqs_sig_2 rslv_to_eqs_cnf_2

rslv_to_eqs_sig_3 :: SOMetaSignature
rslv_to_eqs_sig_3 = SOSignature (Signature [read "p1[0]" --> read "p2[0]" --> EnumProc.Empty] [] (EnumProc.Empty)) (EnumProc.Empty) EnumProc.Empty EnumProc.Empty

rslv_to_eqs_cnf_3 :: SOMetaCNF
rslv_to_eqs_cnf_3 = read "[[+p1[0]()],[-p2[0]()]]"

rslv_to_eqs_eqs_3 :: EnumProc [SOMetaUnifEquation]
rslv_to_eqs_eqs_3 = resolve_to_constraints_metacnf_enum rslv_to_eqs_sig_3 rslv_to_eqs_cnf_3
