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
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
-- Existential second-order unification (with instantiation set results, performing batch unification (multiple unifiers and equations at once))
module ESUnificationExtraTests where

import Control.Exception
import HaskellPlus
import Syntax
import Data.Functor.Fixedpoint
import Data.List
import Data.Map.Strict
import AnswerSet
import EnumProc
import Data.Maybe
import Data.Bifunctor
import Control.Lens
import Control.Monad.State
import ESUnification
import AutoTests
import MetaLogic
import ObjectLogic
import Provenance
import CESQResolutionProvenance
import Control.Monad.ST
import DependencyGraph
import Identifier
import Algorithm

sig :: SOMetaSignature
sig = SOSignature (Signature [] [EnumProc.Empty, read "f0[1]" --> read "f1[1]" --> read "f2[1]" --> read "f3[1]" --> EnumProc.Empty] (read "x0" --> EnumProc.Empty)) (read "F0[1]" --> read "F1[1]" --> EnumProc.Empty) EnumProc.Empty EnumProc.Empty

ueq1_1 :: SOMetaUnifEquation
ueq1_1 = read "u0 F0[1](x0) = u0 f0[1](f2[1](x0))"

ueq1_2 :: SOMetaUnifEquation
ueq1_2 = read "u1 F1[1](x0) = u1 f1[1](x0)"

usys1 :: SOMetaUnifSystem
usys1 = USys sig [ueq1_1, ueq1_2]

ueq2_1 :: SOMetaUnifEquation
ueq2_1 = read "u0 F1[1](x0) = u0 f1[1](f3[1](x0))"

ueq2_2 :: SOMetaUnifEquation
ueq2_2 = read "u1 F0[1](x0) = u1 f0[1](x0)"

usys2 :: SOMetaUnifSystem
usys2 = USys sig [ueq2_1, ueq2_2]

resuvdg1 :: RSOMetaUnifDGraph
resuvdg1 = doRESUnifVDGraph sig (dgraph_from_usys sig (us_eqs usys1))

rresuvdg1 :: RSOMetaUnifDGraph
rresuvdg1 = uns_produce_next (implicitOnly (metaunif_quasinormalize (ImplicitAS resuvdg1)) \$ ())

resuvdg2 :: RSOMetaUnifDGraph
resuvdg2 = doRESUnifVDGraph sig (dgraph_from_usys sig (us_eqs usys2))

rresuvdg2 :: RSOMetaUnifDGraph
rresuvdg2 = uns_produce_next (implicitOnly (metaunif_quasinormalize (ImplicitAS resuvdg2)) \$ ())

mergeresuvdg :: RSOMetaUnifDGraph
mergeresuvdg = mergeRESUnifVDGraph sig rresuvdg1 rresuvdg2

