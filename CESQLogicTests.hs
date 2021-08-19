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
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
module CESQLogicTests where

import Control.Unification
import Control.Unification.IntVar
import HaskellPlus
import Data.Either
import Control.Unification.Types
import Data.List
import Data.Maybe
import Data.HashMap
import Syntax
import AnswerSet
import QueryLogic
import Equiv
import Similarity
import Algorithm
import ESUnification
import EnumProc
import Resolution
import SOResolution
import Control.Monad.State
import Control.Monad.ST
import Data.Functor.Fixedpoint
import Data.Bifunctor
import DependencyGraph
import CESQLogic
import MetaLogic
import SimplePerformance

cesqlogic1_sig :: SOMetaSignature
cesqlogic1_sig = SOSignature (Signature [read "p1[0]" --> EnumProc.Empty] [] EnumProc.Empty) EnumProc.Empty (read "P1[0]" --> EnumProc.Empty) EnumProc.Empty

cesqlogic1_t :: SOMetaCNF
cesqlogic1_t = read "[[+p1[0]()]]"

cesqlogic1_q :: SOMetaQuery
cesqlogic1_q = BaseQ (read "[?P1[0]]") (FLogicQuery cesqlogic1_sig (read "|= [[-P1[0]()]]"))

cesqlogic1_as :: AnswerSet SOMetaImplicitInstantiation (SOMetaQVar =<- SOMetaQSol)
cesqlogic1_as = runQuery cesqlogic1_t cesqlogic1_q

cesqlogic2_sig :: SOMetaSignature
cesqlogic2_sig = SOSignature (Signature [read "p1[0]" --> read "p2[0]" --> EnumProc.Empty] [] EnumProc.Empty) EnumProc.Empty (read "P1[0]" --> EnumProc.Empty) EnumProc.Empty

cesqlogic2_t :: SOMetaCNF
cesqlogic2_t = read "[[+p1[0]()],[+p2[0]()]]"

cesqlogic2_q :: SOMetaQuery
cesqlogic2_q = BaseQ (read "[?P1[0]]") (FLogicQuery cesqlogic2_sig (read "|= [[-P1[0]()]]"))

cesqlogic2_as :: AnswerSet SOMetaImplicitInstantiation (SOMetaQVar =<- SOMetaQSol)
cesqlogic2_as = runQuery cesqlogic2_t cesqlogic2_q

cesqlogic3_sig :: SOMetaSignature
cesqlogic3_sig = SOSignature (Signature [read "p1[0]" --> read "p2[0]" --> EnumProc.Empty] [] EnumProc.Empty) EnumProc.Empty (read "P1[0]" --> EnumProc.Empty) EnumProc.Empty

cesqlogic3_t :: SOMetaCNF
cesqlogic3_t = read "[[+p1[0]()],[-p2[0]()]]"

cesqlogic3_q :: SOMetaQuery
cesqlogic3_q = BaseQ (read "[?P1[0]]") (FLogicQuery cesqlogic3_sig (read "|= [[+P1[0]()]]"))

cesqlogic3_as :: AnswerSet SOMetaImplicitInstantiation (SOMetaQVar =<- SOMetaQSol)
cesqlogic3_as = runQuery cesqlogic3_t cesqlogic3_q

cesqlogic4_sig :: SOMetaSignature
cesqlogic4_sig = SOSignature (Signature [read "p1[0]" --> read "p2[0]" --> EnumProc.Empty] [] EnumProc.Empty) EnumProc.Empty (read "P1[0]" --> EnumProc.Empty) EnumProc.Empty

cesqlogic4_t :: SOMetaCNF
cesqlogic4_t = read "[[+p1[0]()],[-p2[0]()]]"

cesqlogic4_q :: SOMetaQuery
cesqlogic4_q = BaseQ (read "[?P1[0]]") (FLogicQuery cesqlogic4_sig (read "|= [[+P1[0](),-p1[0]()]]"))

cesqlogic4_as :: AnswerSet SOMetaImplicitInstantiation (SOMetaQVar =<- SOMetaQSol)
cesqlogic4_as = runQuery cesqlogic4_t cesqlogic4_q

cesqlogic5_sig :: SOMetaSignature
cesqlogic5_sig = SOSignature (Signature [read "p1[0]" --> read "p2[0]" --> EnumProc.Empty] [] EnumProc.Empty) EnumProc.Empty (read "P1[0]" --> EnumProc.Empty) EnumProc.Empty

cesqlogic5_t :: SOMetaCNF
cesqlogic5_t = read "[[-p1[0]()],[-p2[0]()]]"

cesqlogic5_q :: SOMetaQuery
cesqlogic5_q = BaseQ (read "[?P1[0]]") (FLogicQuery cesqlogic5_sig (read "|= [[+P1[0](),+P1[0]()]]"))

cesqlogic5_as :: AnswerSet SOMetaImplicitInstantiation (SOMetaQVar =<- SOMetaQSol)
cesqlogic5_as = runQuery cesqlogic5_t cesqlogic5_q

cesqlogic6_sig :: SOMetaSignature
cesqlogic6_sig = SOSignature (Signature [EnumProc.Empty,read "p1[1]" --> read "p2[1]" --> EnumProc.Empty] [EnumProc.Empty, read "f1[1]" --> EnumProc.Empty] (read "x0" --> read "x1" --> EnumProc.Empty)) EnumProc.Empty (read "P1[1]" --> EnumProc.Empty) EnumProc.Empty

cesqlogic6_t :: SOMetaCNF
cesqlogic6_t = read "[[-p1[1](f1[1](x0))],[-p2[1](x0)]]"
	
cesqlogic6_q :: SOMetaQuery
cesqlogic6_q = BaseQ (read "[?P1[1]]") (FLogicQuery cesqlogic6_sig (read "|= [[+P1[1](x1)]]"))

cesqlogic6_as :: AnswerSet SOMetaImplicitInstantiation (SOMetaQVar =<- SOMetaQSol)
cesqlogic6_as = runQuery cesqlogic6_t cesqlogic6_q

cesqlogic7_sig :: SOMetaSignature
cesqlogic7_sig = SOSignature (Signature [EnumProc.Empty,read "p1[1]" --> read "p2[1]" --> EnumProc.Empty] [EnumProc.Empty, read "f1[1]" --> EnumProc.Empty] (read "x0" --> read "x1" --> EnumProc.Empty)) EnumProc.Empty (read "P1[1]" --> EnumProc.Empty) EnumProc.Empty

cesqlogic7_t :: SOMetaCNF
cesqlogic7_t = read "[[-p1[1](f1[1](x0))],[-p2[1](x0)]]"

cesqlogic7_q :: SOMetaQuery
cesqlogic7_q = BaseQ (read "[?P1[1]]") (FLogicQuery cesqlogic7_sig (read "*|= [[-P1[1](x1)]] || [[+P1[1](x1)]]"))

cesqlogic7_as :: AnswerSet SOMetaImplicitInstantiation (SOMetaQVar =<- SOMetaQSol)
cesqlogic7_as = runQuery cesqlogic7_t cesqlogic7_q

cesqlogic8_sig :: SOMetaSignature
cesqlogic8_sig = SOSignature (Signature [EnumProc.Empty,read "p1[1]" --> read "p2[1]" --> EnumProc.Empty] [EnumProc.Empty, read "f1[1]" --> EnumProc.Empty] (read "x0" --> read "x1" --> EnumProc.Empty)) EnumProc.Empty (read "P1[1]" --> EnumProc.Empty) EnumProc.Empty

cesqlogic8_t :: SOMetaCNF
cesqlogic8_t = read "[[-p1[1](f1[1](x0))],[-p2[1](x0)]]"

cesqlogic8_q :: SOMetaQuery
cesqlogic8_q = BaseQ (read "[?P1[1]]") (FLogicQuery cesqlogic8_sig (read "*|= [[+P1[1](x1)]] || [[-P1[1](x1)]]"))

cesqlogic8_as :: AnswerSet SOMetaImplicitInstantiation (SOMetaQVar =<- SOMetaQSol)
cesqlogic8_as = runQuery cesqlogic8_t cesqlogic8_q

cesqlogic9_sig :: SOMetaSignature
cesqlogic9_sig = SOSignature (Signature [EnumProc.Empty,read "p1[1]" --> read "p2[1]" --> EnumProc.Empty] [EnumProc.Empty, read "f1[1]" --> EnumProc.Empty] (read "x0" --> read "x1" --> EnumProc.Empty)) EnumProc.Empty (read "P1[1]" --> EnumProc.Empty) EnumProc.Empty

-- The theory should not matter in syntactic checks.
cesqlogic9_t :: SOMetaCNF
cesqlogic9_t = undefined

cesqlogic9_q :: SOMetaQuery
cesqlogic9_q = BaseQ (read "[?P1[1]]") (FLogicQuery cesqlogic9_sig (read "P1[1](x0) ~ p1[1](x0)"))

cesqlogic9_as :: AnswerSet SOMetaImplicitInstantiation (SOMetaQVar =<- SOMetaQSol)
cesqlogic9_as = runQuery cesqlogic9_t cesqlogic9_q

cesqlogic10_sig :: SOMetaSignature
cesqlogic10_sig = SOSignature (Signature [EnumProc.Empty,read "p1[1]" --> read "p2[1]" --> EnumProc.Empty] [EnumProc.Empty, read "f1[1]" --> EnumProc.Empty] (read "x0" --> read "x1" --> EnumProc.Empty)) EnumProc.Empty (read "P1[1]" --> EnumProc.Empty) EnumProc.Empty

-- The theory should not matter in syntactic checks.
cesqlogic10_t :: SOMetaCNF
cesqlogic10_t = undefined

cesqlogic10_q :: SOMetaQuery
cesqlogic10_q = BaseQ (read "[?P1[1]]") (FLogicQuery cesqlogic10_sig (read "p1[1](x0) ~ P1[1](x0)"))

cesqlogic10_as :: AnswerSet SOMetaImplicitInstantiation (SOMetaQVar =<- SOMetaQSol)
cesqlogic10_as = runQuery cesqlogic10_t cesqlogic10_q

cesqlogic11_sig :: SOMetaSignature
cesqlogic11_sig = SOSignature (Signature [EnumProc.Empty,read "p1[1]" --> read "p2[1]" --> EnumProc.Empty] [EnumProc.Empty, read "f1[1]" --> EnumProc.Empty] (read "x0" --> read "x1" --> EnumProc.Empty)) EnumProc.Empty (read "P1[1]" --> EnumProc.Empty) EnumProc.Empty

-- The theory should not matter in syntactic checks.
cesqlogic11_t :: SOMetaCNF
cesqlogic11_t = undefined

cesqlogic11_q :: SOMetaQuery
cesqlogic11_q = BaseQ (read "[?P1[1]]") (FLogicQuery cesqlogic11_sig (read "p1[1](f1[1](x0)) ~ P1[1](x0)"))

cesqlogic11_as :: AnswerSet SOMetaImplicitInstantiation (SOMetaQVar =<- SOMetaQSol)
cesqlogic11_as = runQuery cesqlogic11_t cesqlogic11_q

-- This one does not work when enumerating due to the approximation for negations, but it should work when checking.
cesqlogic12_sig :: SOMetaSignature
cesqlogic12_sig = SOSignature (Signature [EnumProc.Empty,read "p1[1]" --> read "p2[1]" --> EnumProc.Empty] [EnumProc.Empty, read "f1[1]" --> EnumProc.Empty] (read "x0" --> read "x1" --> EnumProc.Empty)) EnumProc.Empty (read "P1[1]" --> EnumProc.Empty) EnumProc.Empty

-- The theory should not matter in syntactic checks.
cesqlogic12_t :: SOMetaCNF
cesqlogic12_t = undefined

cesqlogic12_q :: SOMetaQuery
cesqlogic12_q = BaseQ (read "[?P1[1]]") (FLogicQuery cesqlogic12_sig (read "p1[1](f1[1](x0)) # P1[1](x0)"))

cesqlogic12_as :: AnswerSet SOMetaImplicitInstantiation (SOMetaQVar =<- SOMetaQSol)
cesqlogic12_as = runQuery cesqlogic12_t cesqlogic12_q

cesqlogic13_sig :: SOMetaSignature
cesqlogic13_sig = SOSignature (Signature [EnumProc.Empty,read "p1[1]" --> read "p2[1]" --> EnumProc.Empty] [EnumProc.Empty, read "f1[1]" --> read "f2[1]" --> EnumProc.Empty] (read "x0" --> read "x1" --> EnumProc.Empty)) EnumProc.Empty (read "P1[1]" --> EnumProc.Empty) EnumProc.Empty

cesqlogic13_t :: SOMetaCNF
cesqlogic13_t = read "[[-p1[1](f1[1](x0))],[-p1[1](f2[1](x0))],[-p2[1](f2[1](x0))]]"

cesqlogic13_q :: SOMetaQuery
cesqlogic13_q = (BaseQ (read "[?P1[1]]") (FLogicQuery cesqlogic13_sig (read "|= [[+P1[1](f1[1](x1))]]"))) $<- (BaseQ (read "[?P1[1]]") (FLogicQuery cesqlogic13_sig (read "|= [[+P1[1](f2[1](x1))]]"))) $ (read "[P1[1] := P1[1]]")

cesqlogic13_as :: AnswerSet SOMetaImplicitInstantiation (SOMetaQVar =<- SOMetaQSol)
cesqlogic13_as = runQuery cesqlogic13_t cesqlogic13_q

cesqlogic14_sig :: SOMetaSignature
cesqlogic14_sig = SOSignature (Signature [EnumProc.Empty,read "p1[1]" --> read "p2[1]" --> EnumProc.Empty] [EnumProc.Empty, read "f1[1]" --> read "f2[1]" --> EnumProc.Empty] (read "x0" --> read "x1" --> EnumProc.Empty)) EnumProc.Empty (read "P1[1]" --> read "P2[1]" --> EnumProc.Empty) EnumProc.Empty

cesqlogic14_t :: SOMetaCNF
cesqlogic14_t = read "[[-p1[1](f1[1](x0))],[-p1[1](f2[1](x0))],[-p2[1](f2[1](x0))]]"

cesqlogic14_q :: SOMetaQuery
cesqlogic14_q = (BaseQ (read "[?P2[1]]") (FLogicQuery cesqlogic14_sig (read "|= [[+P2[1](f1[1](x1))]]"))) $<- (BaseQ (read "[?P1[1]]") (FLogicQuery cesqlogic14_sig (read "|= [[+P1[1](f2[1](x1))]]"))) $ (read "[P2[1] := P1[1]]")

cesqlogic14_as :: AnswerSet SOMetaImplicitInstantiation (SOMetaQVar =<- SOMetaQSol)
cesqlogic14_as = runQuery cesqlogic14_t cesqlogic14_q

cesqlogic15_sig :: SOMetaSignature
cesqlogic15_sig = SOSignature (Signature [EnumProc.Empty,read "p1[1]" --> read "p2[1]" --> EnumProc.Empty] [EnumProc.Empty, read "f1[1]" --> read "f2[1]" --> EnumProc.Empty] (read "x0" --> read "x1" --> EnumProc.Empty)) EnumProc.Empty (read "P1[1]" --> read "P2[1]" --> EnumProc.Empty) EnumProc.Empty

cesqlogic15_t :: SOMetaCNF
cesqlogic15_t = read "[[-p1[1](f1[1](x0))],[-p1[1](f2[1](x0))],[-p2[1](f2[1](x0))]]"

cesqlogic15_q :: SOMetaQuery
cesqlogic15_q = (BaseQ (read "[?P2[1],?P1[1]]") (FLogicQuery cesqlogic15_sig (read "|= [[+P2[1](f1[1](x1)),+P1[1](f1[1](x1))]]"))) $<- (BaseQ (read "[?P1[1]]") (FLogicQuery cesqlogic15_sig (read "|= [[+P1[1](f2[1](x1))]]"))) $ (read "[P2[1] := P1[1]]")

cesqlogic15_as :: AnswerSet SOMetaImplicitInstantiation (SOMetaQVar =<- SOMetaQSol)
cesqlogic15_as = runQuery cesqlogic15_t cesqlogic15_q

cesqlogic16_sig :: SOMetaSignature
cesqlogic16_sig = SOSignature (Signature [EnumProc.Empty,read "p1[1]" --> read "p2[1]" --> EnumProc.Empty] [EnumProc.Empty, read "f1[1]" --> read "f2[1]" --> EnumProc.Empty] (read "x0" --> read "x1" --> EnumProc.Empty)) EnumProc.Empty (read "P1[1]" --> EnumProc.Empty) EnumProc.Empty

cesqlogic16_t :: SOMetaCNF
cesqlogic16_t = read "[[-p1[1](f1[1](x0))],[-p1[1](f2[1](x0))],[-p2[1](f2[1](x0))]]"

cesqlogic16_q :: SOMetaQuery
cesqlogic16_q = (BaseQ (read "[?P1[1]]") (FLogicQuery cesqlogic16_sig (read "|= [[+P1[1](f1[1](x1))]]"))) $<= (BaseQ (read "[?P1[1]]") (FLogicQuery cesqlogic16_sig (read "|= [[+P1[1](f2[1](x1))]]"))) $ (read "[P1[1] := P1[1]]")

cesqlogic16_as :: AnswerSet SOMetaImplicitInstantiation (SOMetaQVar =<- SOMetaQSol)
cesqlogic16_as = runQuery cesqlogic16_t cesqlogic16_q

cesqlogic17_sig :: SOMetaSignature
cesqlogic17_sig = SOSignature (Signature [EnumProc.Empty,read "p1[1]" --> read "p2[1]" --> EnumProc.Empty] [EnumProc.Empty, read "f1[1]" --> read "f2[1]" --> EnumProc.Empty] (read "x0" --> read "x1" --> EnumProc.Empty)) EnumProc.Empty (read "P1[1]" --> read "P2[1]" --> EnumProc.Empty) EnumProc.Empty

cesqlogic17_t :: SOMetaCNF
cesqlogic17_t = read "[[-p1[1](f1[1](x0))],[-p1[1](f2[1](x0))],[-p2[1](f2[1](x0))]]"

cesqlogic17_q :: SOMetaQuery
cesqlogic17_q = (BaseQ (read "[?P2[1]]") (FLogicQuery cesqlogic17_sig (read "|= [[+P2[1](f1[1](x1))]]"))) $<= (BaseQ (read "[?P1[1]]") (FLogicQuery cesqlogic17_sig (read "|= [[+P1[1](f2[1](x1))]]"))) $ (read "[P2[1] := P1[1]]")

cesqlogic17_as :: AnswerSet SOMetaImplicitInstantiation (SOMetaQVar =<- SOMetaQSol)
cesqlogic17_as = runQuery cesqlogic17_t cesqlogic17_q

cesqlogic18_sig :: SOMetaSignature
cesqlogic18_sig = SOSignature (Signature [EnumProc.Empty,read "p1[1]" --> read "p2[1]" --> EnumProc.Empty] [EnumProc.Empty, read "f1[1]" --> read "f2[1]" --> EnumProc.Empty] (read "x0" --> read "x1" --> EnumProc.Empty)) EnumProc.Empty (read "P1[1]" --> read "P2[1]" --> EnumProc.Empty) EnumProc.Empty

cesqlogic18_t :: SOMetaCNF
cesqlogic18_t = read "[[-p1[1](f1[1](x0))],[-p1[1](f2[1](x0))],[-p2[1](f2[1](x0))]]"

cesqlogic18_q :: SOMetaQuery
cesqlogic18_q = (BaseQ (read "[?P2[1],?P1[1]]") (FLogicQuery cesqlogic18_sig (read "|= [[+P2[1](f1[1](x1)),+P1[1](f1[1](x1))]]"))) $<= (BaseQ (read "[?P1[1]]") (FLogicQuery cesqlogic18_sig (read "|= [[+P1[1](f2[1](x1))]]"))) $ (read "[P2[1] := P1[1]]")

cesqlogic18_as :: AnswerSet SOMetaImplicitInstantiation (SOMetaQVar =<- SOMetaQSol)
cesqlogic18_as = runQuery cesqlogic18_t cesqlogic18_q

cesqlogic19_sig :: SOMetaSignature
cesqlogic19_sig = SOSignature (Signature [EnumProc.Empty,read "p1[1]" --> read "p2[1]" --> EnumProc.Empty] [EnumProc.Empty, read "f1[1]" --> read "f2[1]" --> EnumProc.Empty] (read "x0" --> read "x1" --> EnumProc.Empty)) (read "F1[1]" --> EnumProc.Empty) EnumProc.Empty EnumProc.Empty

cesqlogic19_t :: SOMetaCNF
cesqlogic19_t = read "[[-p1[1](f1[1](x0))],[-p1[1](f2[1](x0))],[-p2[1](f2[1](x0))]]"

cesqlogic19_q :: SOMetaQuery
cesqlogic19_q = (BaseQ (read "[?F1[1]]") (FLogicQuery cesqlogic19_sig (read "|= [[+p1[1](F1[1](x1))]]"))) $<- (BaseQ (read "[?F1[1]]") (FLogicQuery cesqlogic19_sig (read "|= [[+p2[1](F1[1](x1))]]"))) $ (read "[F1[1] := F1[1]]")

cesqlogic19_as :: AnswerSet SOMetaImplicitInstantiation (SOMetaQVar =<- SOMetaQSol)
cesqlogic19_as = runQuery cesqlogic19_t cesqlogic19_q

cesqlogic20_sig :: SOMetaSignature
cesqlogic20_sig = SOSignature (Signature [EnumProc.Empty,read "p1[1]" --> read "p2[1]" --> EnumProc.Empty] [EnumProc.Empty, read "f1[1]" --> read "f2[1]" --> EnumProc.Empty] (read "x0" --> read "x1" --> EnumProc.Empty)) (read "F1[1]" --> EnumProc.Empty) EnumProc.Empty EnumProc.Empty

cesqlogic20_t :: SOMetaCNF
cesqlogic20_t = read "[[-p1[1](f1[1](x0))],[-p1[1](f2[1](x0))],[-p2[1](f2[1](x0))]]"

cesqlogic20_q :: SOMetaQuery
cesqlogic20_q = (BaseQ (read "[?F1[1]]") (FLogicQuery cesqlogic19_sig (read "|= [[+p1[1](F1[1](x1))]]"))) $<= (BaseQ (read "[?F1[1]]") (FLogicQuery cesqlogic19_sig (read "|= [[+p2[1](F1[1](x1))]]"))) $ (read "[F1[1] := F1[1]]")

cesqlogic20_as :: AnswerSet SOMetaImplicitInstantiation (SOMetaQVar =<- SOMetaQSol)
cesqlogic20_as = runQuery cesqlogic20_t cesqlogic20_q

cesqlogic21_sig :: SOMetaSignature
cesqlogic21_sig = SOSignature (Signature [EnumProc.Empty,read "p1[1]" --> read "p2[1]" --> EnumProc.Empty] [read "f3[0]" --> EnumProc.Empty, read "f1[1]" --> read "f2[1]" --> EnumProc.Empty] (read "x0" --> read "x1" --> EnumProc.Empty)) EnumProc.Empty (read "P1[1]" --> EnumProc.Empty) EnumProc.Empty

cesqlogic21_t :: SOMetaCNF
cesqlogic21_t = read "[[+p1[1](f3[0]())],[-p2[1](f2[1](x0))]]"

cesqlogic21_q :: SOMetaQuery
cesqlogic21_q = (BaseQ (read "[?P1[1]]") (FLogicQuery cesqlogic21_sig (read "*|= [[-P1[1](f3[0]())]] || [[+P1[1](f3[0]())]]"))) $<- (BaseQ (read "[?P1[1]]") (FLogicQuery cesqlogic21_sig (read "|= [[+P1[1](x1)]]"))) $ (read "[P1[1] := P1[1]]")

cesqlogic21_as :: AnswerSet SOMetaImplicitInstantiation (SOMetaQVar =<- SOMetaQSol)
cesqlogic21_as = runQuery cesqlogic21_t cesqlogic21_q

cesqlogic22_sig :: SOMetaSignature
cesqlogic22_sig = SOSignature (Signature [EnumProc.Empty,read "p1[1]" --> read "p2[1]" --> EnumProc.Empty] [read "f3[0]" --> EnumProc.Empty, read "f1[1]" --> read "f2[1]" --> EnumProc.Empty] (read "x0" --> read "x1" --> EnumProc.Empty)) EnumProc.Empty (read "P1[1]" --> EnumProc.Empty) EnumProc.Empty

cesqlogic22_t :: SOMetaCNF
cesqlogic22_t = read "[[+p1[1](f3[0]())],[-p2[1](f2[1](x0))]]"

cesqlogic22_q :: SOMetaQuery
cesqlogic22_q = (BaseQ (read "[?P1[1]]") (FLogicQuery cesqlogic22_sig (read "*|= [[-P1[1](f3[0]())]] || [[+P1[1](f3[0]())]]"))) $<= (BaseQ (read "[?P1[1]]") (FLogicQuery cesqlogic22_sig (read "|= [[+P1[1](x1)]]"))) $ (read "[P1[1] := P1[1]]")

cesqlogic22_as :: AnswerSet SOMetaImplicitInstantiation (SOMetaQVar =<- SOMetaQSol)
cesqlogic22_as = runQuery cesqlogic22_t cesqlogic22_q

cesqlogic23_sig :: SOMetaSignature
cesqlogic23_sig = SOSignature (Signature [EnumProc.Empty,read "p1[1]" --> read "p2[1]" --> EnumProc.Empty] [read "f3[0]" --> EnumProc.Empty, read "f1[1]" --> read "f2[1]" --> EnumProc.Empty] (read "x0" --> read "x1" --> EnumProc.Empty)) EnumProc.Empty (read "P1[1]" --> EnumProc.Empty) EnumProc.Empty

cesqlogic23_t :: SOMetaCNF
cesqlogic23_t = read "[[-p1[1](x0)],[+p2[1](x0)]]"

cesqlogic23_q :: SOMetaQuery
cesqlogic23_q = (BaseQ (read "[?P1[1]]") (FLogicQuery cesqlogic23_sig (read "P1[1](x0) ~ p1[1](x0)"))) $<- (BaseQ (read "[?P1[1]]") (FLogicQuery cesqlogic23_sig (read "|= [[+P1[1](x1)]]"))) $ (read "[P1[1] := P1[1]]")

cesqlogic23_as :: AnswerSet SOMetaImplicitInstantiation (SOMetaQVar =<- SOMetaQSol)
cesqlogic23_as = runQuery cesqlogic23_t cesqlogic23_q

cesqlogic24_sig :: SOMetaSignature
cesqlogic24_sig = SOSignature (Signature [EnumProc.Empty,read "p1[1]" --> read "p2[1]" --> EnumProc.Empty] [read "f3[0]" --> EnumProc.Empty, read "f1[1]" --> read "f2[1]" --> EnumProc.Empty] (read "x0" --> read "x1" --> EnumProc.Empty)) EnumProc.Empty (read "P1[1]" --> EnumProc.Empty) EnumProc.Empty

cesqlogic24_t :: SOMetaCNF
cesqlogic24_t = read "[[-p1[1](x0)],[+p2[1](x0)]]"

cesqlogic24_q :: SOMetaQuery
cesqlogic24_q = (BaseQ (read "[?P1[1]]") (FLogicQuery cesqlogic24_sig (read "P1[1](x0) ~ p2[1](x0)"))) $<- (BaseQ (read "[?P1[1]]") (FLogicQuery cesqlogic24_sig (read "|= [[+P1[1](x1)]]"))) $ (read "[P1[1] := P1[1]]")

cesqlogic24_as :: AnswerSet SOMetaImplicitInstantiation (SOMetaQVar =<- SOMetaQSol)
cesqlogic24_as = runQuery cesqlogic24_t cesqlogic24_q

cesqlogic25_sig :: SOMetaSignature
cesqlogic25_sig = SOSignature (Signature [EnumProc.Empty,read "p1[1]" --> read "p2[1]" --> EnumProc.Empty] [read "f3[0]" --> EnumProc.Empty, read "f1[1]" --> read "f2[1]" --> EnumProc.Empty] (read "x0" --> read "x1" --> EnumProc.Empty)) EnumProc.Empty (read "P1[1]" --> EnumProc.Empty) EnumProc.Empty

cesqlogic25_t :: SOMetaCNF
cesqlogic25_t = read "[[-p1[1](x0)],[+p2[1](x0)]]"

cesqlogic25_q :: SOMetaQuery
cesqlogic25_q = (BaseQ (read "[?P1[1]]") (FLogicQuery cesqlogic25_sig (read "P1[1](x0) ~ p1[1](x0)"))) $<= (BaseQ (read "[?P1[1]]") (FLogicQuery cesqlogic25_sig (read "|= [[+P1[1](x1)]]"))) $ (read "[P1[1] := P1[1]]")

cesqlogic25_as :: AnswerSet SOMetaImplicitInstantiation (SOMetaQVar =<- SOMetaQSol)
cesqlogic25_as = runQuery cesqlogic25_t cesqlogic25_q

cesqlogic26_sig :: SOMetaSignature
cesqlogic26_sig = SOSignature (Signature [EnumProc.Empty,read "p1[1]" --> read "p2[1]" --> EnumProc.Empty] [read "f3[0]" --> EnumProc.Empty, read "f1[1]" --> read "f2[1]" --> EnumProc.Empty] (read "x0" --> read "x1" --> EnumProc.Empty)) EnumProc.Empty (read "P1[1]" --> EnumProc.Empty) EnumProc.Empty

cesqlogic26_t :: SOMetaCNF
cesqlogic26_t = read "[[-p1[1](x0)],[+p2[1](x0)]]"

cesqlogic26_q :: SOMetaQuery
cesqlogic26_q = (BaseQ (read "[?P1[1]]") (FLogicQuery cesqlogic26_sig (read "P1[1](x0) # p1[1](x0)"))) $<- (BaseQ (read "[?P1[1]]") (FLogicQuery cesqlogic26_sig (read "|= [[+P1[1](x1)]]"))) $ (read "[P1[1] := P1[1]]")

cesqlogic26_as :: AnswerSet SOMetaImplicitInstantiation (SOMetaQVar =<- SOMetaQSol)
cesqlogic26_as = runQuery cesqlogic26_t cesqlogic26_q

cesqlogic27_sig :: SOMetaSignature
cesqlogic27_sig = SOSignature (Signature [read "p1[0]" --> read "p2[0]" --> EnumProc.Empty] [] EnumProc.Empty) EnumProc.Empty (read "P1[0]" --> EnumProc.Empty) EnumProc.Empty

cesqlogic27_t :: SOMetaCNF
cesqlogic27_t = read "[[+p1[0]()],[-p2[0]()]]"

cesqlogic27_q :: SOMetaQuery
cesqlogic27_q = ProductQ (BaseQ (read "[?P1[0]]") (FLogicQuery cesqlogic27_sig (read "|= [[-P1[0]()]]"))) (BaseQ (read "[?P1[0]]") (FLogicQuery cesqlogic27_sig (read "|= [[+P1[0]()]]")))

cesqlogic27_as :: AnswerSet SOMetaImplicitInstantiation (SOMetaQVar =<- SOMetaQSol)
cesqlogic27_as = runQuery cesqlogic27_t cesqlogic27_q

cesqlogic28_sig :: SOMetaSignature
cesqlogic28_sig = SOSignature (Signature [read "p1[0]" --> read "p2[0]" --> EnumProc.Empty] [] EnumProc.Empty) EnumProc.Empty (read "P1[0]" --> read "P2[0]" --> EnumProc.Empty) EnumProc.Empty

cesqlogic28_t :: SOMetaCNF
cesqlogic28_t = read "[[+p1[0]()],[-p2[0]()]]"

cesqlogic28_q :: SOMetaQuery
cesqlogic28_q = ProductQ (BaseQ (read "[?P1[0]]") (FLogicQuery cesqlogic28_sig (read "|= [[-P1[0]()]]"))) (BaseQ (read "[?P2[0]]") (FLogicQuery cesqlogic28_sig (read "|= [[+P2[0]()]]")))

cesqlogic28_as :: AnswerSet SOMetaImplicitInstantiation (SOMetaQVar =<- SOMetaQSol)
cesqlogic28_as = runQuery cesqlogic28_t cesqlogic28_q

cesqlogic29_sig :: SOMetaSignature
cesqlogic29_sig = SOSignature (Signature [EnumProc.Empty, read "p1[1]" --> read "p2[1]" --> read "p3[1]" --> EnumProc.Empty] [read "f3[0]" --> read "f4[0]" --> EnumProc.Empty, read "f1[1]" --> read "f2[1]" --> EnumProc.Empty] EnumProc.Empty) (read "F1[0]" --> EnumProc.Empty) (read "P1[1]" --> read "P2[1]" --> EnumProc.Empty) EnumProc.Empty

cesqlogic29_t :: SOMetaCNF
cesqlogic29_t = read "[[+p1[1](f3[0]())],[+p2[1](f3[0]())],[+p3[1](f3[0]())],[-p1[1](f3[0]())],[-p1[1](f4[0]())],[-p2[1](f3[0]())],[-p3[1](f3[0]())],[-p3[1](f4[0]())]]"

cesqlogic29_q :: SOMetaQuery
cesqlogic29_q = (BaseQ (read "[?F1[0]]") (FLogicQuery cesqlogic29_sig (read "|= [[+P1[1](F1[0]())]]"))) $<=| (BaseQ (read "[?P2[1]]") (FLogicQuery cesqlogic29_sig (read "|= [[-P2[1](f3[0]())]]"))) $ (read "[P1[1] := P2[1]]")

cesqlogic29_as :: AnswerSet SOMetaImplicitInstantiation (SOMetaQVar =<- SOMetaQSol)
cesqlogic29_as = runQuery cesqlogic29_t cesqlogic29_q


