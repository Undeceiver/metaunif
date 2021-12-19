{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}

module IssuesExploration where

import ObjectLogic
import MetaLogic
import AutoTests
import Control.Unification
import Data.Functor.Fixedpoint
import Syntax
import Data.Maybe
import HaskellPlus
import QueryLogic 
import CESQLogic
import Data.HashMap
import AnswerSet
import SimplePerformance
import EnumProc
import Algorithm

cesqtest :: Double -> String -> AnswerSet SOMetaImplicitInstantiation (SOMetaQVar =<- SOMetaQSol) -> IO ()
cesqtest maxsecs filename as = stdout_to_file filename >> n_timeout_secs maxsecs (t_measure_enum_csv "\t" (enumAS as \$ ()))

cesqsig20 :: SOMetaSignature
cesqsig20 = SOSignature (Signature [EnumProc.Empty, read "p1[1]" --> read "p2[1]" --> EnumProc.Empty] [] (read "x0" --> EnumProc.Empty)) EnumProc.Empty (read "P1[1]" --> read "P2[1]" --> EnumProc.Empty) (read "k1[1]" --> read "k2[2]" --> EnumProc.Empty)

cesqtheory20 :: SOMetaCNF
cesqtheory20 = read "[[-p1[1](x0),+p2[1](x0)],[-p2[1](x0),+p1[1](x0)],[+k1[1]([[+p1[1]]])],[+k1[1]([[+p2[1]]])],[+k2[2]([[+p1[1]]],[[+p2[1]]])]]"

cesqsigstd20 :: SOMetaSignature
cesqtheorystd20 :: SOMetaCNF
(cesqsigstd20,cesqtheorystd20) = standardize_apart_cesqclause cesqsig20 cesqtheory20

cesqquery20_1 :: SOMetaBaseQ
cesqquery20_1 = FLogicQuery cesqsigstd20 (read "|= [[-k1[1]([[+P1[1]]]),-k1[1]([[+P2[1]]])]]")

cesqquery20_2 :: SOMetaBaseQ
cesqquery20_2 = FLogicQuery cesqsigstd20 (read "|= [[-k2[2]([[+P1[1]]],[[+P2[1]]])]]")

cesqquery20 :: SOMetaQuery
cesqquery20 = (BaseQ (read "[?P1[1],?P2[1]]") cesqquery20_1) $<- (BaseQ (read "[?P1[1],?P2[1]]") cesqquery20_2) $ (read "[P1[1] := P1[1],P2[1] := P2[1]]")

cesqas20 :: AnswerSet SOMetaImplicitInstantiation (SOMetaQVar =<- SOMetaQSol)
cesqas20 = runQuery cesqtheorystd20 cesqquery20

exploresig1 :: SOMetaSignature
exploresig1 = SOSignature (Signature [EnumProc.Empty, read "p1[1]" --> read "p2[1]" --> EnumProc.Empty, read "p3[2]" --> EnumProc.Empty] [EnumProc.Empty, read "f1[1]" --> EnumProc.Empty] (read "x0" --> read "x1" --> EnumProc.Empty)) EnumProc.Empty (read "P1[1]" --> read "P2[1]" --> read "P3[2]" --> EnumProc.Empty) (read "k1[1]" --> read "k2[2]" --> EnumProc.Empty)

exploretheory1 :: SOMetaCNF
exploretheory1 = read "[[+p1[1](x0)]]"

exploresigstd1 :: SOMetaSignature
exploretheorystd1 :: SOMetaCNF
(exploresigstd1,exploretheorystd1) = standardize_apart_cesqclause exploresig1 exploretheory1

explorequery1_1 :: SOMetaBaseQ
explorequery1_1 = FLogicQuery exploresigstd1 (read "|= [[-P1[1](x0)]]")

explorequery1 :: SOMetaQuery
explorequery1 = BaseQ (read "[?P1[1]]") explorequery1_1

exploreas1 :: AnswerSet SOMetaImplicitInstantiation (SOMetaQVar =<- SOMetaQSol)
exploreas1 = runQuery exploretheorystd1 explorequery1


cesqsig4 :: SOMetaSignature
cesqsig4 = SOSignature (Signature [EnumProc.Empty, read "p2[1]" --> read "p3[1]" --> read "p4[1]" --> read "p5[1]" --> read "p6[1]" --> read "p7[1]" --> EnumProc.Empty, read "p1[2]" --> EnumProc.Empty] [read "f5[0]" --> EnumProc.Empty, read "f1[0]" --> read "f2[0]" --> read "f3[0]" --> read "f4[0]" --> EnumProc.Empty] (read "x0" --> read "x1" --> EnumProc.Empty)) EnumProc.Empty (read "P1[1]" --> EnumProc.Empty) (read "k1[1]" --> EnumProc.Empty)

cesqtheory4 :: SOMetaCNF
cesqtheory4 = read "[[-p1[2](x0,x1),-p2[1](x1),-p1[2](x0,x1),-p3[1](x1)],[-p7[1](x0),-p6[1](x0)],[-p7[1](x0),+p1[2](x0,f1[1](x0))],[-p7[1](x0),+p3[1](f1[1](x0))],[-p7[1](x0),+p1[2](x0,f2[1](x0))],[-p7[1](x0),+p2[1](f2[1](x0))],[-p7[1](x0),+p1[2](x0,f3[1](x0))],[-p7[1](x0),+p4[1](f3[1](x0))],[-p7[1](x0),+p1[2](x0,f4[1](x0))],[-p7[1](x0),+p5[1](f4[1](x0))],[+k1[1]([[+p2[1]]])],[+k1[1]([[+p3[1]]])],[+k1[1]([[+p4[1]]])],[+k1[1]([[+p5[1]]])]]"

cesqsigstd4 :: SOMetaSignature
cesqtheorystd4 :: SOMetaCNF
(cesqsigstd4,cesqtheorystd4) = standardize_apart_cesqclause cesqsig4 cesqtheory4

cesqquery4_1 :: SOMetaBaseQ
cesqquery4_1 = FLogicQuery cesqsigstd4 (read "|= [[+P1[1](f5[0]())]]")

cesqquery4_2 :: SOMetaBaseQ
cesqquery4_2 = FLogicQuery cesqsigstd4 (read "|= [[-k1[1]([[+P1[1]]])]]")

cesqquery4 :: SOMetaQuery
cesqquery4 = (BaseQ (read "[?P1[1]]") cesqquery4_1) $<- (BaseQ (read "[?P1[1]]") cesqquery4_2) $ (read "[P1[1] := P1[1]]")

cesqas4 :: AnswerSet SOMetaImplicitInstantiation (SOMetaQVar =<- SOMetaQSol)
cesqas4 = runQuery cesqtheorystd4 cesqquery4


cesqsig8 :: SOMetaSignature
cesqsig8 = SOSignature (Signature [EnumProc.Empty, read "p1[1]" --> read "p2[1]" --> read "p4[1]" --> read "p5[1]" --> EnumProc.Empty, read "p3[2]" --> EnumProc.Empty] [read "f3[0]" --> read "f4[0]" --> EnumProc.Empty, read "f1[1]" --> read "f2[1]" --> EnumProc.Empty] (read "x0" --> read "x1" --> EnumProc.Empty)) EnumProc.Empty (read "P1[1]" --> read "P2[1]" --> read "P3[2]" --> read "P4[1]" --> EnumProc.Empty) (read "k1[3]" --> EnumProc.Empty)

cesqtheory8 :: SOMetaCNF
cesqtheory8 = read "[[-p1[1](x0),+p2[1](x0)],[-p1[1](x0),-p3[2](x0,x1),+p4[1](x1)],[-p2[1](x0),+p1[1](x0),+p3[2](x0,f1[1](x0))],[-p2[1](x0),+p1[1](x0),-p4[1](f1[1](x0))],[-p5[1](x0),+p2[1](x0)],[-p5[1](x0),-p3[2](x0,x1)],[-p2[1](x0),+p5[1](x0),+p3[2](x0,f2[1](x0))],[+k1[3]([[+p1[1]]],[[+p3[2]]],[[+p4[1]]])]]"

cesqsigstd8 :: SOMetaSignature
cesqtheorystd8 :: SOMetaCNF
(cesqsigstd8,cesqtheorystd8) = standardize_apart_cesqclause cesqsig8 cesqtheory8

cesqquery8_1 :: SOMetaBaseQ
cesqquery8_1 = FLogicQuery cesqsigstd8 (read "|= [[+P1[1](f3[0]())],[-P2[1](f3[0]()),+P3[2](f3[0](),f4[0]())]]")

cesqquery8_2 :: SOMetaBaseQ
cesqquery8_2 = FLogicQuery cesqsigstd8 (read "|= [[-k1[3]([[+P2[1]]],[[+P3[2]]],[[+P4[1]]])]]")

cesqquery8 :: SOMetaQuery
cesqquery8 = (BaseQ (read "[?P1[1],?P2[1],?P3[2]]") cesqquery8_1) $<- (BaseQ (read "[?P2[1],?P3[2]]") cesqquery8_2) $ (read "[P2[1] := P2[1],P3[2] := P3[2]]")

cesqas8 :: AnswerSet SOMetaImplicitInstantiation (SOMetaQVar =<- SOMetaQSol)
cesqas8 = runQuery cesqtheorystd8 cesqquery8
