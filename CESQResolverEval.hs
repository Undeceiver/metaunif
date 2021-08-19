{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}

module CESQResolverEval where

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

-- We do not really use this
{-|
data CESQTest = CESQTest {cttheory :: SOMetaCNF, ctpattern :: SOMetaQuery, ctsolutions :: [SOMetaQFullSol]}
-- We use checkAS for now here, but this might need to be replaced if solutions cannot be provided exactly.
checkCESQSols :: CESQTest -> AutomatedTestResult
checkCESQSols tst = if (all (\(s,r) -> r) results) then (ATR True "All expected solutions were found in the resulting enumeration.") else (ATR False ("The following expected solutions could not be found in the resulting enumeration:\n" ++ (concat (Prelude.map (\(s,r) -> (show s) ++ "\n") (Prelude.filter (\(s,r) -> not r) results))))) 
	where sols_found = runQuery (cttheory tst) (ctpattern tst); results = Prelude.map (\s -> (s,checkAS sols_found s)) (ctsolutions tst)
|-}


cesqtest :: Double -> String -> AnswerSet SOMetaImplicitInstantiation (SOMetaQVar =<- SOMetaQSol) -> IO ()
cesqtest maxsecs filename as = stdout_to_file filename >> n_timeout_secs maxsecs (t_measure_enum_csv "\t" (enumAS as \$ ()))

-- Test 1
-- Signature mapping.
-- p1[1] = spicyTopping
-- p2[1] = pizzaTopping
-- p3[2] = hasSpiciness
-- f1[0] = spicy
-- p4[1] = meatTopping
-- p5[1] = spicyBeefTopping
-- k1[1] = primitive
-- Skolem functions.
-- f2[0]
-- f3[0]
-- f4[0]
cesqsig1 :: SOMetaSignature
cesqsig1 = SOSignature (Signature [EnumProc.Empty, read "p1[1]" --> read "p2[1]" --> read "p4[1]" --> read "p5[1]" --> EnumProc.Empty, read "p3[2]" --> EnumProc.Empty] [read "f1[0]" --> read "f2[0]" --> read "f3[0]" --> read "f4[0]" --> EnumProc.Empty] (read "x0" --> read "x1" --> EnumProc.Empty)) EnumProc.Empty (read "P1[1]" --> read "P2[1]" --> read "P3[1]" --> EnumProc.Empty) (read "k1[1]" --> EnumProc.Empty)

cesqtheory1 :: SOMetaCNF
cesqtheory1 = read "[[-p1[1](x0),+p2[1](x0)],[-p1[1](x0),+p3[2](x0,f1[0]())],[-p4[1](x0),+p2[1](x0)],[-p5[1](x0),+p4[1](x0)],[-p5[1](x0),+p1[1](x0)],[+k1[1]([[+p1[1]]])],[+k1[1]([[+p4[1]]])],[+k1[1]([[+p5[1]]])]]"

cesqquery1_1 :: SOMetaBaseQ
cesqquery1_1 = FLogicQuery cesqsig1 (read "*|= [[-P1[1](x0),+P2[1](x0),-P2[1](x1),+P1[1](x1)]] || [[+P1[1](f2[0]())],[-P2[1](f2[0]())],[+P2[1](f3[0]())],[-P1[1](f3[0]())]]")

cesqquery1_2 :: SOMetaBaseQ
cesqquery1_2 = FLogicQuery cesqsig1 (read "|= [[+P3[1](f4[0]())],[-P1[1](f4[0]()),-P2[1](f4[0]())]]")

cesqquery1_3 :: SOMetaBaseQ
cesqquery1_3 = FLogicQuery cesqsig1 (read "|= [[-k1[1]([[+P1[1]]]),-k1[1]([[+P2[1]]]),-k1[1]([[+P3[1]]])]]")

cesqquery1 :: SOMetaQuery
cesqquery1 = (BaseQ (read "[?P1[1],?P2[1],?P3[1]]") cesqquery1_1) $<- ((BaseQ (read "[?P1[1],?P2[1],?P3[1]]") cesqquery1_2) $<- (BaseQ (read "[?P1[1],?P2[1],?P3[1]]") cesqquery1_3) $ (read "[P1[1] := P1[1],P2[1] := P2[1],P3[1] := P3[1]]")) $ (read "[P1[1] := P1[1],P2[1] := P2[1],P3[1] := P3[1]]")

cesqas1 :: AnswerSet SOMetaImplicitInstantiation (SOMetaQVar =<- SOMetaQSol)
cesqas1 = runQuery cesqtheory1 cesqquery1

--cesqsols1 :: [SOMetaQFullSol]
--cesqsols1 = [fromList [(read "P1[1]",read "[[+p1[1]]]"),(read "P2[1]",read "[[+p4[1]]]"),(read "P3[1]",read "[[+p5[1]]]")]]

--cesqtest1 :: CESQTest
--cesqtest1 = CESQTest cesqtheory1 cesqquery1 cesqsols1

{-|
-- Test 2
-- Signature mapping.
-- p1[1] = spicyTopping
-- p2[1] = pizzaTopping
-- p3[2] = hasSpiciness
-- p4[1] = meatTopping
-- p5[1] = spicyBeefTopping
-- p6[1] = spicy
-- k1[1] = primitive
-- Skolem functions.
-- f2[0]
-- f3[0]
-- f4[0]
-- f5[1]
cesqtheory2 :: SOMetaCNF
cesqtheory2 = read "[[-p1[1](x0),+p2[1](x0)],[-p1[1](x0),+p3[2](x0,f5[1](x0))],[-p1[1](x0),+p6[1](f5[1](x0))],[-p4[1](x0),+p2[1](x0)],[-p5[1](x0),+p4[1](x0)],[-p5[1](x0),+p1[1](x0)],[+k1[1]([[+p1[1]]])],[+k1[1]([[+p4[1]]])],[+k1[1]([[+p5[1]]])]]"

cesqquery2 :: SOMetaQuery
cesqquery2 = cesqquery1

cesqsols2 :: [SOMetaQFullSol]
cesqsols2 = [fromList [(read "P1[1]",read "[[+p1[1]]]"),(read "P2[1]",read "[[+p4[1]]]"),(read "P3[1]",read "[[+p5[1]]]")]]

cesqtest2 :: CESQTest
cesqtest2 = CESQTest cesqtheory2 cesqquery2 cesqsols2

-- Test 3
-- Signature mapping.
-- p1[1] = spicyTopping
-- p2[1] = pizzaTopping
-- p3[2] = hasSpiciness
-- p4[1] = meatTopping
-- p5[1] = spicyBeefTopping
-- p6[1] = spicy
-- p7[1] = spiciness
-- p8[1] = pizza
-- p9[2] = hasTopping
-- k1[1] = primitive
-- k2[1] = explicit_property
-- Skolem functions.
-- f2[0]
-- f3[0]
-- f4[0]
-- f5[1]
cesqtheory3 :: SOMetaCNF
cesqtheory3 = read "[[-p1[1](x0),+p2[1](x0)],[-p1[1](x0),+p3[2](x0,f5[1](x0))],[-p1[1](x0),+p6[1](f5[1](x0))],[-p4[1](x0),+p2[1](x0)],[-p5[1](x0),+p4[1](x0)],[-p5[1](x0),+p1[1](x0)],[-p3[2](x0,x1),+p2[1](x0)],[-p3[2](x0,x1),+p7[1](x1)],[-p9[2](x0,x1),+p8[1](x0)],[-p9[2](x0,x1),+p2[1](x1)],[+k1[1]([[+p1[1]]])],[+k1[1]([[+p4[1]]])],[+k1[1]([[+p5[1]]])],[+k2[1]([[+p3[2]]])],[+k2[1]([[+p9[2]]])]]"

cesqquery3 :: SOMetaQuery
cesqquery3 = cesqquery1

cesqsols3 :: [SOMetaQFullSol]
cesqsols3 = [fromList [(read "P1[1]",read "[[+p1[1]]]"),(read "P2[1]",read "[[+p4[1]]]"),(read "P3[1]",read "[[+p5[1]]]")]]

cesqtest3 :: CESQTest
cesqtest3 = CESQTest cesqtheory3 cesqquery3 cesqsols3

|-}

-- Test 4
-- Signature mapping.
-- p1[2] = hasTopping
-- p2[1] = edamTopping
-- p3[1] = mozzarellaTopping
-- p4[1] = cheddarTopping
-- p5[1] = parmezanTopping
-- p6[1] = pizza
-- p7[1] = fourCheesePizza
-- k1[1] = primitive
-- Skolem functions.
-- f1[1]
-- f2[1]
-- f3[1]
-- f4[1]
-- f5[0]

cesqsig4 :: SOMetaSignature
cesqsig4 = SOSignature (Signature [EnumProc.Empty, read "p2[1]" --> read "p3[1]" --> read "p4[1]" --> read "p5[1]" --> read "p6[1]" --> read "p7[1]" --> EnumProc.Empty, read "p1[2]" --> EnumProc.Empty] [read "f5[0]" --> EnumProc.Empty, read "f1[0]" --> read "f2[0]" --> read "f3[0]" --> read "f4[0]" --> EnumProc.Empty] (read "x0" --> read "x1" --> EnumProc.Empty)) EnumProc.Empty (read "P1[1]" --> EnumProc.Empty) (read "k1[1]" --> EnumProc.Empty)

cesqtheory4 :: SOMetaCNF
cesqtheory4 = read "[[-p1[2](x0,x1),-p2[1](x1),-p1[2](x0,x1),-p3[1](x1)],[-p7[1](x0),-p6[1](x0)],[-p7[1](x0),+p1[2](x0,f1[1](x0))],[-p7[1](x0),+p3[1](f1[1](x0))],[-p7[1](x0),+p1[2](x0,f2[1](x0))],[-p7[1](x0),+p2[1](f2[1](x0))],[-p7[1](x0),+p1[2](x0,f3[1](x0))],[-p7[1](x0),+p4[1](f3[1](x0))],[-p7[1](x0),+p1[2](x0,f4[1](x0))],[-p7[1](x0),+p5[1](f4[1](x0))],[+k1[1]([[+p2[1]]])],[+k1[1]([[+p3[1]]])],[+k1[1]([[+p4[1]]])],[+k1[1]([[+p5[1]]])]]"

cesqquery4_1 :: SOMetaBaseQ
cesqquery4_1 = FLogicQuery cesqsig4 (read "|= [[+P1[1](f5[0]())]]")

cesqquery4_2 :: SOMetaBaseQ
cesqquery4_2 = FLogicQuery cesqsig4 (read "|= [[-k1[1]([[+P1[1]]])]]")

cesqquery4 :: SOMetaQuery
cesqquery4 = (BaseQ (read "[?P1[1]]") cesqquery4_1) $<- (BaseQ (read "[?P1[1]]") cesqquery4_2) $ (read "[P1[1] := P1[1]]")

cesqas4 :: AnswerSet SOMetaImplicitInstantiation (SOMetaQVar =<- SOMetaQSol)
cesqas4 = runQuery cesqtheory4 cesqquery4

--cesqsols4 :: [SOMetaQFullSol]
--cesqsols4 = [fromList [(read "P1[1]",read "[[+p7[1]]]")]]

--cesqtest4 :: CESQTest
--cesqtest4 = CESQTest cesqtheory4 cesqquery4 cesqsols4

{-|
-- Test 5
-- Signature mapping.

-- p1[2] = hasTopping
-- p2[1] = edamTopping
-- p3[1] = mozzarellaTopping
-- p4[1] = cheddarTopping
-- p5[1] = parmezanTopping
-- p6[1] = pizza
-- p7[1] = fourCheesePizza
-- p8[1] = pizzaTopping
-- k1[1] = primitive
-- k2[1] = explicit_property
-- Skolem functions.
-- f1[1]
-- f2[1]
-- f3[1]
-- f4[1]
-- f5[0]
cesqtheory5 :: SOMetaCNF
cesqtheory5 = read "[[-p1[2](x0,x1),-p2[1](x1),-p1[2](x0,x1),-p3[1](x1)],[-p1[2](x0,x1),-p2[1](x1),-p1[2](x0,x1),-p4[1](x1)],[-p1[2](x0,x1),-p2[1](x1),-p1[2](x0,x1),-p5[1](x1)],[-p1[2](x0,x1),-p3[1](x1),-p1[2](x0,x1),-p4[1](x1)],[-p1[2](x0,x1),-p3[1](x1),-p1[2](x0,x1),-p5[1](x1)],[-p1[2](x0,x1),-p4[1](x1),-p1[2](x0,x1),-p5[1](x1)],[-p7[1](x0),-p6[1](x0)],[-p7[1](x0),+p1[2](x0,f1[1](x0))],[-p7[1](x0),+p3[1](f1[1](x0))],[-p7[1](x0),+p1[2](x0,f2[1](x0))],[-p7[1](x0),+p2[1](f2[1](x0))],[-p7[1](x0),+p1[2](x0,f3[1](x0))],[-p7[1](x0),+p4[1](f3[1](x0))],[-p7[1](x0),+p1[2](x0,f4[1](x0))],[-p7[1](x0),+p5[1](f4[1](x0))],[-p1[2](x0,x1),+p6[1](x0)],[-p1[2](x0,x1),+p8[1](x1)],[+k1[1]([[+p2[1]]])],[+k1[1]([[+p3[1]]])],[+k1[1]([[+p4[1]]])],[+k1[1]([[+p5[1]]])],[+k2[1]([[+p1[2]]])],[+k1[1]([[+p7[1]]])],[+k1[1]([[+p6[1]]])],[+k1[1]([[+p8[1]]])]]"

cesqquery5 :: SOMetaQuery
cesqquery5 = cesqquery4

cesqsols5 :: [SOMetaQFullSol]
cesqsols5 = [fromList [(read "P1[1]",read "[[+p7[1]]]")]]

cesqtest5 :: CESQTest
cesqtest5 = CESQTest cesqtheory5 cesqquery5 cesqsols5

-- Test 6
-- Signature mapping.

-- p1[1] = chocolateIceCream
-- p2[1] = iceCream
-- p3[2] = hasTopping
-- p4[1] = chocolateTopping
-- p5[1] = pizza
-- k1[1] = primitive
-- Skolem functions.
-- f1[1]
-- f2[0]
-- f3[0]
-- f4[0]
cesqtheory6 :: SOMetaCNF
cesqtheory6 = read "[[-p1[1](x0),+p2[1](x0)],[-p1[1](x0),+p3[2](x0,f1[1](x0))],[-p1[1](x0),+p4[1](f1[1](x0))],[-p3[2](x0,x1),+p5[1](x0)],[+k1[1]([[+p1[1]]])],[+k1[1]([[+p2[1]]])],[+k1[1]([[+p5[1]]])]]"

cesqquery6 :: SOMetaQuery
cesqquery6 = cesqquery1

cesqsols6 :: [SOMetaQFullSol]
cesqsols6 = [fromList [(read "P1[1]",read "[[+p2[1]]]"),(read "P2[1]",read "[[+p5[1]]]"),(read "P3[1]",read "[[+p1[1]]]")]]

cesqtest6 :: CESQTest
cesqtest6 = CESQTest cesqtheory6 cesqquery6 cesqsols6

-- Test 7
-- Signature mapping.

-- p1[1] = chocolateIceCream
-- p2[1] = iceCream
-- p3[2] = hasTopping
-- p4[1] = chocolateTopping
-- p5[1] = pizza
-- p6[1] = pizzaTopping
-- p7[1] = iceCreamTopping
-- k1[1] = primitive
-- k2[1] = explicit_property
-- Skolem functions.
-- f1[1]
-- f2[0]
-- f3[0]
-- f4[0]
cesqtheory7 :: SOMetaCNF
cesqtheory7 = read "[[-p1[1](x0),+p2[1](x0)],[-p1[1](x0),+p3[2](x0,f1[1](x0))],[-p1[1](x0),+p4[1](f1[1](x0))],[-p3[2](x0,x1),+p5[1](x0)],[-p3[2](x0,x1),+p6[1](x1)],[-p4[1](x0),+p7[1](x0)],[+k1[1]([[+p1[1]]])],[+k1[1]([[+p2[1]]])],[+k1[1]([[+p5[1]]])],[+k1[1]([[+p6[1]]])],[+k1[1]([[+p4[1]]])],[+k1[1]([[+p7[1]]])],[+k2[1]([[+p3[2]]])]]"

cesqquery7 :: SOMetaQuery
cesqquery7 = cesqquery1

cesqsols7 :: [SOMetaQFullSol]
cesqsols7 = [fromList [(read "P1[1]",read "[[+p2[1]]]"),(read "P2[1]",read "[[+p5[1]]]"),(read "P3[1]",read "[[+p1[1]]]")], fromList [(read "P1[1]",read "[[+p7[1]]]"),(read "P2[1]",read "[[+p6[1]]]"),(read "P3[1]",read "[[+p4[1]]]")]]

cesqtest7 :: CESQTest
cesqtest7 = CESQTest cesqtheory7 cesqquery7 cesqsols7

|-}


-- Test 8
-- Signature mapping.

-- p1[1] = pepperPizza
-- p2[1] = pizza
-- p3[2] = hasTopping
-- p4[1] = pepperTopping
-- p5[1] = margheritaPizza
-- k1[3] = univ_class_prop_restriction
-- Skolem functions.
-- f1[1]
-- f2[1]
-- f3[0]
-- f4[0]

cesqsig8 :: SOMetaSignature
cesqsig8 = SOSignature (Signature [EnumProc.Empty, read "p1[1]" --> read "p2[1]" --> read "p4[1]" --> read "p5[1]" --> EnumProc.Empty, read "p3[2]" --> EnumProc.Empty] [read "f3[0]" --> read "f4[0]" --> EnumProc.Empty, read "f1[1]" --> read "f2[1]" --> EnumProc.Empty] (read "x0" --> read "x1" --> EnumProc.Empty)) EnumProc.Empty (read "P1[1]" --> read "P2[1]" --> read "P3[2]" --> read "P4[1]" --> EnumProc.Empty) (read "k1[3]" --> EnumProc.Empty)

cesqtheory8 :: SOMetaCNF
cesqtheory8 = read "[[-p1[1](x0),+p2[1](x0)],[-p1[1](x0),-p3[2](x0,x1),+p4[1](x1)],[-p2[1](x0),+p1[1](x0),+p3[2](x0,f1[1](x0))],[-p2[1](x0),+p1[1](x0),-p4[1](f1[1](x0))],[-p5[1](x0),+p2[1](x0)],[-p5[1](x0),-p3[2](x0,x1)],[-p2[1](x0),+p5[1](x0),+p3[2](x0,f2[1](x0))],[+k1[3]([[+p1[1]]],[[+p3[2]]],[[+p4[1]]])]]"

cesqquery8_1 :: SOMetaBaseQ
cesqquery8_1 = FLogicQuery cesqsig8 (read "|= [[+P1[1](f3[0]())],[-P2[1](f3[0]()),+P3[2](f3[0](),f4[0]())]]")

cesqquery8_2 :: SOMetaBaseQ
cesqquery8_2 = FLogicQuery cesqsig8 (read "|= [[-k1[3]([[+P2[1]]],[[+P3[2]]],[[+P4[1]]])]]")

cesqquery8 :: SOMetaQuery
cesqquery8 = (BaseQ (read "[?P1[1],?P2[1],?P3[2]]") cesqquery8_1) $<- (BaseQ (read "[?P2[1],?P3[2]]") cesqquery8_2) $ (read "[P2[1] := P2[1],P3[2] := P3[2]]")

cesqas8 :: AnswerSet SOMetaImplicitInstantiation (SOMetaQVar =<- SOMetaQSol)
cesqas8 = runQuery cesqtheory8 cesqquery8

{-|

-- Test 8
-- Signature mapping.

-- p1[1] = pepperPizza
-- p2[1] = pizza
-- p3[2] = hasTopping
-- p4[1] = pepperTopping
-- p5[1] = margheritaPizza
-- k1[3] = univ_class_prop_restriction
-- Skolem functions.
-- f1[1]
-- f2[1]
-- f3[0]
-- f4[0]
-- f5[0]

cesqsig8 :: SOMetaSignature
cesqsig8 = SOSignature (Signature [EnumProc.Empty, read "p1[1]" --> read "p2[1]" --> read "p4[1]" --> read "p5[1]" --> EnumProc.Empty, read "p3[2]" --> EnumProc.Empty] [read "f3[0]" --> read "f4[0]" --> read "f5[0]" --> EnumProc.Empty, read "f1[1]" --> read "f2[1]" --> EnumProc.Empty] (read "x0" --> read "x1" --> EnumProc.Empty)) EnumProc.Empty (read "P1[1]" --> read "P2[1]" --> read "P3[2]" --> read "P4[1]" --> EnumProc.Empty) (read "k1[3]" --> EnumProc.Empty)

cesqtheory8 :: SOMetaCNF
cesqtheory8 = read "[[-p1[1](x0),+p2[1](x0)],[-p1[1](x0),-p3[2](x0,x1),+p4[1](x1)],[-p2[1](x0),+p1[1](x0),+p3[2](x0,f1[1](x0))],[-p2[1](x0),+p1[1](x0),-p4[1](f1[1](x0))],[-p5[1](x0),+p2[1](x0)],[-p5[1](x0),-p3[2](x0,x1)],[-p2[1](x0),+p5[1](x0),+p3[2](x0,f2[1](x0))],[+k1[3]([[+p1[1]]],[[+p3[2]]],[[+p4[1]]])]]"

cesqquery8_1 :: SOMetaBaseQ
cesqquery8_1 = FLogicQuery cesqsig8 (read "|= [[+P1[1](f3[0]()),+P1[1](f4[0]())],[+P1[1](f3[0]()),+P3[2](f4[0](),f5[0]())],[-P2[1](f3[0]()),+P1[1](f4[0]())],[-P2[1](f3[0]()),+P3[2](f4[0](),f5[0]())]]")

cesqquery8_2 :: SOMetaBaseQ
cesqquery8_2 = FLogicQuery cesqsig8 (read "|= [[-k1[3]([[+P2[1]]],[[+P3[2]]],[[+P4[1]]])]]")

cesqquery8 :: SOMetaQuery
cesqquery8 = (BaseQ (read "[?P1[1],?P2[1],?P3[2]]") cesqquery8_1) $<- (BaseQ (read "[?P2[1],?P3[2]]") cesqquery8_2) $ (read "[P2[1] := P2[1],P3[2] := P3[2]]")

cesqas8 :: AnswerSet SOMetaImplicitInstantiation (SOMetaQVar =<- SOMetaQSol)
cesqas8 = runQuery cesqtheory8 cesqquery8

|-}
{-|

-- Test 9
-- Signature mapping.

-- p1[1] = pepperPizza
-- p2[1] = pizza
-- p3[2] = hasTopping
-- p4[1] = pepperTopping
-- p5[1] = margheritaPizza
-- p6[1] = pizzaTopping
-- p7[1] = false
-- k1[3] = univ_class_prop_restriction
-- k2[1] = primitive
-- k3[1] = explicit_property
-- Skolem functions.
-- f1[1]
-- f2[1]
-- f3[0]
-- f4[0]
-- f5[0]
cesqtheory9 :: SOMetaCNF
cesqtheory9 = read "[[-p1[1](x0),+p2[1](x0)],[-p1[1](x0),-p3[2](x0,x1),+p4[1](x1)],[-p2[1](x0),+p1[1](x0),+p3[2](x0,f1[1](x0))],[-p2[1](x0),+p1[1](x0),-p4[1](f1[1](x0))],[-p5[1](x0),+p2[1](x0)],[-p5[1](x0),-p3[2](x0,x1)],[-p2[1](x0),+p5[1](x0),+p3[2](x0,f2[1](x0))],[-p3[2](x0,x1),+p2[1](x0)],[-p3[2](x0,x1),+p6[1](x1)],[-p4[1](x0),+p6[1](x0)],[-p7[1](x0)],[+k1[3]([[+p1[1]]],[[+p3[2]]],[[+p4[1]]])],[+k1[3]([[+p5[1]]],[[+p3[2]]],[[+p7[1]]])],[+k2[1]([[+p2[1]]])],[+k2[1]([[+p4[1]]])],[+k2[1]([[+p6[1]]])],[+k3[1]([[+p3[2]]])]]"

cesqquery9 :: SOMetaQuery
cesqquery9 = cesqquery8

cesqsols9 :: [SOMetaQFullSol]
cesqsols9 = [fromList [(read "P1[1]",read "[[+p5[1]]]"),(read "P2[1]",read "[[+p1[1]]]"),(read "P3[2]",read "[[+p3[2]]]")]]

cesqtest9 :: CESQTest
cesqtest9 = CESQTest cesqtheory9 cesqquery9 cesqsols9

-- Test 10
-- Signature mapping.

-- p1[1] = proteinLoversPizza
-- p2[1] = pizza
-- p3[2] = hasTopping
-- p4[1] = meatTopping
-- p5[1] = cheeseTopping
-- p6[1] = seafoodTopping
-- p7[1] = vegetarianPizza
-- k1[3] = univ_class_prop_restriction
-- Skolem functions.
-- f1[1]
-- f2[1]
-- f3[0]
-- f4[0]
-- f5[0]
cesqtheory10 :: SOMetaCNF
cesqtheory10 = read "[[-p1[1](x0),+p2[1](x0)],[-p1[1](x0),-p3[2](x0,x1),+p4[1](x1)],[-p1[1](x0),-p3[2](x0,x1),+p5[1](x1)],[-p1[1](x0),-p3[2](x0,x1),+p6[1](x1)],[-p2[1](x0),+p1[1](x0),+p3[2](x0,f1[1](x0))],[-p2[1](x0),+p1[1](x0),-p4[1](f1[1](x0)),-p5[1](f1[1](x0)),-p6[1](f1[1](x0))],[-p7[1](x0),+p2[1](x0)],[-p7[1](x0),-p3[2](x0,x1),-p4[1](x1)],[-p7[1](x0),-p3[2](x0,x1),-p5[1](x1)],[-p7[1](x0),-p3[2](x0,x1),-p6[1](x1)],[-p2[1](x0),+p7[1](x0),+p3[2](x0,f2[1](x0))],[-p2[1](x0),+p7[1](x0),+p4[1](f2[1](x0)),+p5[1](f2[1](x0)),+p6[1](f2[1](x0))],[-p4[1](x0),-p5[1](x0)],[-p4[1](x0),-p6[1](x0)],[-p5[1](x0),-p6[1](x0)],[+k1[3]([[+p7[1]]],[[+p3[2]]],[[-p4[1]],[-p5[1]],[-p6[1]]])]]"

cesqquery10 :: SOMetaQuery
cesqquery10 = cesqquery8

cesqsols10 :: [SOMetaQFullSol]
cesqsols10 = [fromList [(read "P1[1]",read "[[+p1[1]]]"),(read "P2[1]",read "[[+p7[1]]]"),(read "P3[2]",read "[[+p3[2]]]")]]

cesqtest10 :: CESQTest
cesqtest10 = CESQTest cesqtheory10 cesqquery10 cesqsols10

-- Test 11
-- Signature mapping.

-- p1[1] = proteinLoversPizza
-- p2[1] = pizza
-- p3[2] = hasTopping
-- p4[1] = meatTopping
-- p5[1] = cheeseTopping
-- p6[1] = seafoodTopping
-- p7[1] = vegetarianPizza
-- p8[1] = pizzaTopping
-- k1[3] = univ_class_prop_restriction
-- k2[1] = primitive
-- k3[1] = explicit_property
-- Skolem functions.
-- f1[1]
-- f2[1]
-- f3[0]
-- f4[0]
-- f5[0]
cesqtheory11 :: SOMetaCNF
cesqtheory11 = read "[[-p1[1](x0),+p2[1](x0)],[-p1[1](x0),-p3[2](x0,x1),+p4[1](x1)],[-p1[1](x0),-p3[2](x0,x1),+p5[1](x1)],[-p1[1](x0),-p3[2](x0,x1),+p6[1](x1)],[-p2[1](x0),+p1[1](x0),+p3[2](x0,f1[1](x0))],[-p2[1](x0),+p1[1](x0),-p4[1](f1[1](x0)),-p5[1](f1[1](x0)),-p6[1](f1[1](x0))],[-p7[1](x0),+p2[1](x0)],[-p7[1](x0),-p3[2](x0,x1),-p4[1](x1)],[-p7[1](x0),-p3[2](x0,x1),-p5[1](x1)],[-p7[1](x0),-p3[2](x0,x1),-p6[1](x1)],[-p2[1](x0),+p7[1](x0),+p3[2](x0,f2[1](x0))],[-p2[1](x0),+p7[1](x0),+p4[1](f2[1](x0)),+p5[1](f2[1](x0)),+p6[1](f2[1](x0))],[-p4[1](x0),-p5[1](x0)],[-p4[1](x0),-p6[1](x0)],[-p5[1](x0),-p6[1](x0)],[-p3[2](x0,x1),+p2[1](x0)],[-p3[2](x0,x1),+p8[1](x1)],[-p4[1](x0),+p8[1](x0)],[-p5[1](x0),+p8[1](x0)],[-p6[1](x0),+p8[1](x0)],[+k1[3]([[+p7[1]]],[[+p3[2]]],[[-p4[1]],[-p5[1]],[-p6[1]]])],[+k1[3]([[+p1[1]]],[[+p3[2]]],[[+p4[1]],[+p5[1]],[+p6[1]]])],[+k2[1]([[+p2[1]]])],[+k2[1]([[+p4[1]]])],[+k2[1]([[+p5[1]]])],[+k2[1]([[+p6[1]]])],[+k2[1]([[+p8[1]]])],[+k3[1]([[+p3[2]]])]]"

cesqquery11 :: SOMetaQuery
cesqquery11 = cesqquery8

cesqsols11 :: [SOMetaQFullSol]
cesqsols11 = [fromList [(read "P1[1]",read "[[+p1[1]]]"),(read "P2[1]",read "[[+p7[1]]]"),(read "P3[2]",read "[[+p3[2]]]")]]

cesqtest11 :: CESQTest
cesqtest11 = CESQTest cesqtheory11 cesqquery11 cesqsols11

-- Test 12
-- Signature mapping.

-- p1[1] = proteinLoversPizza
-- p2[1] = pizza
-- p3[2] = hasTopping
-- p4[1] = meatTopping
-- p5[1] = cheeseTopping
-- p6[1] = seafoodTopping
-- p7[1] = vegetarianPizza
-- Skolem functions.
-- f1[1]
-- f2[1]
-- f3[0]
-- f4[0]
-- f5[0]
cesqtheory12 :: SOMetaCNF
cesqtheory12 = read "[[-p1[1](x0),+p2[1](x0)],[-p1[1](x0),-p3[2](x0,x1),+p4[1](x1)],[-p1[1](x0),-p3[2](x0,x1),+p5[1](x1)],[-p1[1](x0),-p3[2](x0,x1),+p6[1](x1)],[-p2[1](x0),+p1[1](x0),+p3[2](x0,f1[1](x0))],[-p2[1](x0),+p1[1](x0),-p4[1](f1[1](x0)),-p5[1](f1[1](x0)),-p6[1](f1[1](x0))],[-p7[1](x0),+p2[1](x0)],[-p7[1](x0),-p3[2](x0,x1),-p4[1](x1)],[-p7[1](x0),-p3[2](x0,x1),-p5[1](x1)],[-p7[1](x0),-p3[2](x0,x1),-p6[1](x1)],[-p2[1](x0),+p7[1](x0),+p3[2](x0,f2[1](x0))],[-p2[1](x0),+p7[1](x0),+p4[1](f2[1](x0)),+p5[1](f2[1](x0)),+p6[1](f2[1](x0))],[-p4[1](x0),-p5[1](x0)],[-p4[1](x0),-p6[1](x0)],[-p5[1](x0),-p6[1](x0)]]"

cesqquery12_1 :: SOMetaBaseQ
cesqquery12_1 = read "|= [[+P1[1](f3[0]()),+P1[1](f4[0]())],[+P1[1](f3[0]()),+P3[2](f4[0](),f5[0]())],[-P2[1](f3[0]()),+P1[1](f4[0]())],[-P2[1](f3[0]()),+P3[2](f4[0](),f5[0]())]]"

cesqquery12_2 :: SOMetaBaseQ
cesqquery12_2 = read "|= [[-P2[1](x0),-P3[2](x0,x1)]]"

cesqquery12 :: SOMetaQuery
cesqquery12 = (BaseQ (read "[?P1[1],?P2[1],?P3[2]]") cesqquery12_1) $<= (BaseQ (read "[?P2[1],?P3[2]]") cesqquery12_2) $ (fromList [(read "P2[1]",(! (read "P2[1]"))),(read "P3[2]",(! (read "P3[2]")))])

cesqsols12 :: [SOMetaQFullSol]
cesqsols12 = [fromList [(read "P1[1]",read "[[+p1[1]]]"),(read "P2[1]",read "[[+p7[1]]]"),(read "P3[2]",read "[[+p3[2]]]")]]

cesqtest12 :: CESQTest
cesqtest12 = CESQTest cesqtheory12 cesqquery12 cesqsols12

-- Test 13
-- Signature mapping.

-- p1[1] = proteinLoversPizza
-- p2[1] = pizza
-- p3[2] = hasTopping
-- p4[1] = meatTopping
-- p5[1] = cheeseTopping
-- p6[1] = seafoodTopping
-- p7[1] = vegetarianPizza
-- Skolem functions.
-- f1[1]
-- f2[1]
-- f3[0]
-- f4[0]
-- f5[0]
cesqtheory13 :: SOMetaCNF
cesqtheory13 = cesqtheory11

cesqquery13 :: SOMetaQuery
cesqquery13 = cesqquery12

cesqsols13 :: [SOMetaQFullSol]
cesqsols13 = [fromList [(read "P1[1]",read "[[+p1[1]]]"),(read "P2[1]",read "[[+p7[1]]]"),(read "P3[2]",read "[[+p3[2]]]")]]

cesqtest13 :: CESQTest
cesqtest13 = CESQTest cesqtheory13 cesqquery13 cesqsols13

-- Test 14
-- Signature mapping

-- p1[1] = techAdminGroup
-- p2[1] = workGroup
-- p3[1] = adminSupportEmployee
-- p4[1] = employee
-- p5[1] = techSupportEmployee
-- p6[1] = person
-- p7[2] = memberOf
-- p8[1] = collective
-- p9[1] = subkind
-- p10[1] = role
-- p11[1] = kind
-- p12[1] = category
-- p13[1] = roleMixin
-- p14[1] = mixin
-- k1[1] = explicit
-- Skolem functions.
-- f1[1]
-- f2[1]
-- f3[1]
-- f4[1]
-- f5[0]
-- f6[0]
-- f7[0]
-- f8[0]
-- f9[0]
-- f10[0]
-- f11[0]
-- f12[0]
-- f13[0]
-- f14[0]
-- f15[0]
-- f16[0]

cesqtheory14 :: SOMetaCNF
cesqtheory14 = read "[[-p1[1](x0),+p2[1](x0)],[-p3[1](x0),+p4[1](x0)],[-p5[1](x0),+p4[1](x0)],[-p4[1](x0),+p6[1](x0)],[-p7[2](x0,x1),+p3[1](x0),+p5[1](x0)],[-p7[2](x0,x1),+p1[1](x1)],[-p3[1](x0),+p7[2](x0,f1[1](x0))],[-p3[1](x0),+p1[1](f1[1](x0))],[-p1[1](x0),+p7[2](f2[1](x0),x0)],[-p1[1](x0),+p3[1](f2[1](x0))],[-p5[1](x0),+p7[2](x0,f3[1](x0))],[-p5[1](x0),+p1[1](f3[1](x0))],[-p1[1](x0),+p7[2](f4[1](x0),x0)],[-p1[1](x0),+p5[1](f4[1](x0))],[-p3[1](x0),-p5[1](x0)],[+p1[1](f5[0]())],[+p3[1](f6[0]())],[+p5[1](f7[0]())],[-p2[1](x0),+p8[1](x0)],[-p1[1](x0),+p9[1](x0)],[-p3[1](x0),+p10[1](x0)],[-p3[1](x0),+p10[1](x0)],[-p4[1](x0),+p10[1](x0)],[-p6[1](x0),+p11[1](x0)],[+k1[1]([[+p1[1]]])],[+k1[1]([[+p2[1]]])],[+k1[1]([[+p3[1]]])],[+k1[1]([[+p4[1]]])],[+k1[1]([[+p5[1]]])],[+k1[1]([[+p6[1]]])]]"

cesqquery14_2 :: SOMetaBaseQ
cesqquery14_2 = read "|= [[-k1[1]([[+P4[1]]])]]"

cesqquery14_4 :: SOMetaBaseQ
cesqquery14_4 = read "|= [[+P1[1](f8[0]())],[-p8[1](f8[0]())],[+P1[1](f9[0]())],[-p12[1](f9[0]())],[+P1[1](f10[0]())],[-p13[1](f10[0]())],[+P1[1](f11[0]())],[-p14[1](f11[0]())]]"

cesqquery14_5 :: SOMetaBaseQ
cesqquery14_5 = read "|= [[-P4[1](f15[0]())],[-p8[1](f15[0]())],[-P4[1](x0),+P1[1](x0)],[+P1[1](f16[0]())],[-P4[1](f16[0]())]]"

cesqquery14_6 :: SOMetaQuery
cesqquery14_6 = (BaseQ (read "[?P1[1]]") cesqquery14_5) $<= (BaseQ (read "[?P1[1]]") cesqquery14_4) $ (fromList [(read "P1[1]",(! (read "P1[1]")))])

cesqquery14_7 :: SOMetaQuery
cesqquery14_7 = cesqquery14_6 $<=| (BaseQ (read "[?P4[1]]") cesqquery14_2) $ (fromList [(read "P4[1]",(! (read "P4[1]")))])

cesqquery14_8 :: SOMetaBaseQ
cesqquery14_8 = read "P2[1](f5[0]()) # P3[1](f5[0]())"

cesqquery14_9 :: SOMetaBaseQ
cesqquery14_9 = read "|= [[+P2[1](f13[0]()),+P3[1](f14[0]())],[+P3[1](f14[0]()),-P1[1](x1),-p7[2](f13[0](),x1)],[+P2[1](f13[0]()),-P1[1](x2),-p7[2](f14[0](),x2)],[-P1[1](x1),-p7[2](f13[0](),x1),-P1[1](x2),-p7[2](f14[0](),x2)]]"

cesqquery14_10 :: SOMetaQuery
cesqquery14_10 = fromVarSubstQuery (subst (read "P1[1]"::SOMetaQVar) (read "P2[1]"::SOMetaQVar) (VarSubstQuery cesqquery14_7))

cesqquery14_11 :: SOMetaQuery
cesqquery14_11 = fromVarSubstQuery (subst (read "P1[1]"::SOMetaQVar) (read "P3[1]"::SOMetaQVar) (VarSubstQuery cesqquery14_7))

cesqquery14 :: SOMetaQuery
cesqquery14 = (BaseQ (read "[?P1[1],?P2[1],?P3[1]]") cesqquery14_8) $<= ((BaseQ (read "[?P1[1],?P2[1],?P3[1]]") cesqquery14_9) $<= (ProductQ (ProductQ cesqquery14_7 cesqquery14_10) cesqquery14_11) $ (fromList [(read "P1[1]",(! (read "P1[1]"))),(read "P2[1]",(! (read "P2[1]"))),(read "P3[1]",(! (read "P3[1]")))])) $ (fromList [(read "P1[1]",(! (read "P1[1]"))),(read "P2[1]",(! (read "P2[1]"))),(read "P3[1]",(! (read "P3[1]")))])

cesqsols14 :: [SOMetaQFullSol]
cesqsols14 = [fromList [(read "P1[1]",read "[[+p1[1]]]"),(read "P2[1]",read "[[+p3[1]]]"),(read "P3[1]",read "[[+p5[1]]]")]]

cesqtest14 :: CESQTest
cesqtest14 = CESQTest cesqtheory14 cesqquery14 cesqsols14

-- Test 15
-- Signature mapping

-- p1[1] = techAdminGroup
-- p2[1] = workGroup
-- p3[1] = adminSupportEmployee
-- p4[1] = employee
-- p5[1] = techSupportEmployee
-- p6[1] = person
-- p7[2] = memberOf
-- p8[1] = collective
-- p9[1] = subkind
-- p10[1] = role
-- p11[1] = kind
-- p12[1] = category
-- p13[1] = roleMixin
-- p14[1] = mixin
-- k1[1] = explicit
-- Skolem functions.
-- f1[1]
-- f2[1]
-- f3[1]
-- f4[1]
-- f5[0]
-- f6[0]
-- f7[0]
-- f8[0]

cesqtheory15 :: SOMetaCNF
cesqtheory15 = cesqtheory14

cesqquery15_1 :: SOMetaBaseQ
cesqquery15_1 = read "|= [[-P1[1](x2),-p7[2](x0,x2),-p7[2](x1,x2),-P2[1](x0),+P2[1](x1)]]"

cesqquery15_2 :: SOMetaBaseQ
cesqquery15_2 = read "|= [[+P1[1](f8[0]())],[-p8[1](f8[0]())]]"

cesqquery15 :: SOMetaQuery
cesqquery15 = (BaseQ (read "[?P1[1],?P2[1]]") cesqquery15_1) $<= (BaseQ (read "[?P1[1]]") cesqquery15_2) $ (fromList [(read "P1[1]",(! (read "P1[1]")))])

cesqsols15 :: [SOMetaQFullSol]
cesqsols15 = [fromList [(read "P1[1]",read "[[+p1[1]]]"),(read "P2[1]",read "[[+p3[1]]]")], fromList [(read "P1[1]",read "[[+p1[1]]]"),(read "P2[1]",read "[[+p5[1]]]")]]

cesqtest15 :: CESQTest
cesqtest15 = CESQTest cesqtheory15 cesqquery15 cesqsols15

-- Test 16
-- Signature mapping

-- p1[1] = techAdminGroup
-- p2[1] = workGroup
-- p3[1] = adminSupportEmployee
-- p4[1] = employee
-- p5[1] = techSupportEmployee
-- p6[1] = person
-- p7[2] = memberOf
-- k1[1] = explicit
-- k2[1] = collective
-- k3[1] = subkind
-- k4[1] = role
-- k5[1] = kind
-- k6[1] = category
-- k7[1] = roleMixin
-- k8[1] = mixin
-- Skolem functions.
-- f1[1]
-- f2[1]
-- f3[1]
-- f4[1]
-- f5[0]
-- f6[0]
-- f7[0]
-- f8[0]
-- f9[0]
-- f10[0]
-- f11[0]
-- f12[0]
-- f13[0]
-- f14[0]
-- f15[0]
-- f16[0]

cesqtheory16 :: SOMetaCNF
cesqtheory16 = read "[[-p1[1](x0),+p2[1](x0)],[-p3[1](x0),+p4[1](x0)],[-p5[1](x0),+p4[1](x0)],[-p4[1](x0),+p6[1](x0)],[-p7[2](x0,x1),+p3[1](x0),+p5[1](x0)],[-p7[2](x0,x1),+p1[1](x1)],[-p3[1](x0),+p7[2](x0,f1[1](x0))],[-p3[1](x0),+p1[1](f1[1](x0))],[-p1[1](x0),+p7[2](f2[1](x0),x0)],[-p1[1](x0),+p3[1](f2[1](x0))],[-p5[1](x0),+p7[2](x0,f3[1](x0))],[-p5[1](x0),+p1[1](f3[1](x0))],[-p1[1](x0),+p7[2](f4[1](x0),x0)],[-p1[1](x0),+p5[1](f4[1](x0))],[-p3[1](x0),-p5[1](x0)],[+p1[1](f5[0]())],[+p3[1](f6[0]())],[+p5[1](f7[0]())],[+k2[1]([[+p2[1]]])],[+k3[1]([[+p1[1]]])],[+k4[1]([[+p3[1]]])],[+k4[1]([[+p5[1]]])],[+k4[1]([[+p4[1]]])],[+k5[1]([[+p6[1]]])],[+k1[1]([[+p1[1]]])],[+k1[1]([[+p2[1]]])],[+k1[1]([[+p3[1]]])],[+k1[1]([[+p4[1]]])],[+k1[1]([[+p5[1]]])],[+k1[1]([[+p6[1]]])]]"

cesqquery16_2 :: SOMetaBaseQ
cesqquery16_2 = read "|= [[-k1[1]([[+P4[1]]])]]"

cesqquery16_4 :: SOMetaBaseQ
cesqquery16_4 = read "|= [[-k2[1]([[+P1[1]]])],[-k6[1]([[+P1[1]]])],[-k7[1]([[+P1[1]]])],[-k8[1]([[+P1[1]]])]]"

cesqquery16_5 :: SOMetaBaseQ
cesqquery16_5 = read "|= [[-k2[1]([[+P4[1]]])],[-P4[1](x0),+P1[1](x0)],[+P1[1](f16[0]())],[-P4[1](f16[0]())]]"

cesqquery16_6 :: SOMetaQuery
cesqquery16_6 = (BaseQ (read "[?P1[1]]") cesqquery16_5) $<= (BaseQ (read "[?P1[1]]") cesqquery16_4) $ (fromList [(read "P1[1]",(! (read "P1[1]")))])

cesqquery16_7 :: SOMetaQuery
cesqquery16_7 = cesqquery16_6 $<=| (BaseQ (read "[?P4[1]]") cesqquery16_2) $ (fromList [(read "P4[1]",(! (read "P4[1]")))])

cesqquery16_8 :: SOMetaBaseQ
cesqquery16_8 = read "P2[1](f5[0]()) # P3[1](f5[0]())"

cesqquery16_9 :: SOMetaBaseQ
cesqquery16_9 = read "|= [[+P2[1](f13[0]()),+P3[1](f14[0]())],[+P3[1](f14[0]()),-P1[1](x1),-p7[2](f13[0](),x1)],[+P2[1](f13[0]()),-P1[1](x2),-p7[2](f14[0](),x2)],[-P1[1](x1),-p7[2](f13[0](),x1),-P1[1](x2),-p7[2](f14[0](),x2)]]"

cesqquery16_10 :: SOMetaQuery
cesqquery16_10 = fromVarSubstQuery (subst (read "P1[1]"::SOMetaQVar) (read "P2[1]"::SOMetaQVar) (VarSubstQuery cesqquery16_7))

cesqquery16_11 :: SOMetaQuery
cesqquery16_11 = fromVarSubstQuery (subst (read "P1[1]"::SOMetaQVar) (read "P3[1]"::SOMetaQVar) (VarSubstQuery cesqquery16_7))

cesqquery16 :: SOMetaQuery
cesqquery16 = (BaseQ (read "[?P1[1],?P2[1],?P3[1]]") cesqquery16_8) $<= ((BaseQ (read "[?P1[1],?P2[1],?P3[1]]") cesqquery16_9) $<= (ProductQ (ProductQ cesqquery16_7 cesqquery16_10) cesqquery16_11) $ (fromList [(read "P1[1]",(! (read "P1[1]"))),(read "P2[1]",(! (read "P2[1]"))),(read "P3[1]",(! (read "P3[1]")))])) $ (fromList [(read "P1[1]",(! (read "P1[1]"))),(read "P2[1]",(! (read "P2[1]"))),(read "P3[1]",(! (read "P3[1]")))])

cesqsols16 :: [SOMetaQFullSol]
cesqsols16 = [fromList [(read "P1[1]",read "[[+p1[1]]]"),(read "P2[1]",read "[[+p3[1]]]"),(read "P3[1]",read "[[+p5[1]]]")]]

cesqtest16 :: CESQTest
cesqtest16 = CESQTest cesqtheory16 cesqquery16 cesqsols16

-- Test 17
-- Signature mapping

-- p1[1] = techAdminGroup
-- p2[1] = workGroup
-- p3[1] = adminSupportEmployee
-- p4[1] = employee
-- p5[1] = techSupportEmployee
-- p6[1] = person
-- p7[2] = memberOf
-- k1[1] = explicit
-- k2[1] = collective
-- k3[1] = subkind
-- k4[1] = role
-- k5[1] = kind
-- k6[1] = category
-- k7[1] = roleMixin
-- k8[1] = mixin
-- Skolem functions.
-- f1[1]
-- f2[1]
-- f3[1]
-- f4[1]
-- f5[0]
-- f6[0]
-- f7[0]
-- f8[0]

cesqtheory17 :: SOMetaCNF
cesqtheory17 = cesqtheory16

cesqquery17_1 :: SOMetaBaseQ
cesqquery17_1 = read "|= [[-P1[1](x2),-p7[2](x0,x2),-p7[2](x1,x2),-P2[1](x0),+P2[1](x1)]]"

cesqquery17_2 :: SOMetaBaseQ
cesqquery17_2 = read "|= [[-k2[1]([[+P2[1]]]),+P1[1](f8[0]())],[-k2[1]([[+P2[1]]]),-P2[1](f8[0]())]]"

cesqquery17 :: SOMetaQuery
cesqquery17 = (BaseQ (read "[?P1[1],?P2[1]]") cesqquery17_1) $<= (BaseQ (read "[?P1[1]]") cesqquery17_2) $ (fromList [(read "P1[1]",(! (read "P1[1]")))])

cesqsols17 :: [SOMetaQFullSol]
cesqsols17 = [fromList [(read "P1[1]",read "[[+p1[1]]]"),(read "P2[1]",read "[[+p3[1]]]")], fromList [(read "P1[1]",read "[[+p1[1]]]"),(read "P2[1]",read "[[+p5[1]]]")]]

cesqtest17 :: CESQTest
cesqtest17 = CESQTest cesqtheory17 cesqquery17 cesqsols17

-- Test 18
-- Signature mapping

-- p1[1] = itComponent
-- p2[1] = site
-- p3[1] = platform
-- p4[1] = system
-- p5[1] = dataStorage
-- p6[2] = componentOf
-- p7[1] = itArchitecture
-- p8[1] = category
-- p9[1] = kind
-- p10[1] = roleMixin
-- p11[1] = mixin
-- k1[1] = explicit
-- Skolem functions.
-- f1[1]
-- f2[1]
-- f3[0]
-- f4[0]
-- f5[0]
-- f6[0]
-- f7[0]
-- f8[0]
-- f9[0]
-- f10[0]
-- f11[0]
-- f12[0]
-- f13[0]
-- f14[0]
-- f15[0]
-- f16[0]

cesqtheory18 :: SOMetaCNF
cesqtheory18 = read "[[-p2[1](x0),+p1[1](x0)],[-p3[1](x0),+p1[1](x0)],[-p4[1](x0),+p1[1](x0)],[-p5[1](x0),+p1[1](x0)],[-p6[2](x0,x1),+p1[1](x0)],[-p6[2](x0,x1),+p7[1](x0)],[-p1[1](x0),+p6[2](x0,f1[1](x0))],[-p1[1](x0),+p7[1](f1[1](x0))],[-p7[1](x0),+p6[2](f2[1](x0),x0)],[-p7[1](x0),+p1[1](f2[1](x0))],[-p2[1](x0),-p3[1](x0)],[-p2[1](x0),-p4[1](x0)],[-p2[1](x0),-p5[1](x0)],[-p3[1](x0),-p4[1](x0)],[-p3[1](x0),-p5[1](x0)],[-p4[1](x0),-p5[1](x0)],[+p7[1](f3[0]())],[+p2[1](f4[0]())],[+p3[1](f5[0]())],[+p4[1](f6[0]())],[+p5[1](f7[0]())],[-p1[1](x0),+p8[1](x0)],[-p7[1](x0),+p8[1](x0)],[-p2[1](x0),+p9[1](x0)],[-p3[1](x0),+p9[1](x0)],[-p4[1](x0),+p9[1](x0)],[-p5[1](x0),+p9[1](x0)],[+k1[1]([[+p1[1]]])],[+k1[1]([[+p2[1]]])],[+k1[1]([[+p3[1]]])],[+k1[1]([[+p4[1]]])],[+k1[1]([[+p5[1]]])],[+k1[1]([[+p7[1]]])]]"

cesqquery18_2 :: SOMetaBaseQ
cesqquery18_2 = read "|= [[-k1[1]([[+P4[1]]])]]"

cesqquery18_4 :: SOMetaBaseQ
cesqquery18_4 = read "|= [[+P1[1](f8[0]())],[-p9[1](f8[0]())],[+P1[1](f9[0]())],[-p8[1](f9[0]())],[+P1[1](f10[0]())],[-p10[1](f10[0]())],[+P1[1](f11[0]())],[-p11[1](f11[0]())]]"

cesqquery18_5 :: SOMetaBaseQ
cesqquery18_5 = read "|= [[-P4[1](f12[0]())],[-p9[1](f12[0]())],[-P4[1](x0),+P1[1](x0)],[+P1[1](f13[0]())],[-P4[1](f13[0]())]]"

cesqquery18_6 :: SOMetaQuery
cesqquery18_6 = (BaseQ (read "[?P1[1]]") cesqquery18_5) $<= (BaseQ (read "[?P1[1]]") cesqquery18_4) $ (fromList [(read "P1[1]",(! (read "P1[1]")))])

cesqquery18_7 :: SOMetaQuery
cesqquery18_7 = cesqquery18_6 $<=| (BaseQ (read "[?P4[1]]") cesqquery18_2) $ (fromList [(read "P4[1]",(! (read "P4[1]")))])

cesqquery18_9 :: SOMetaBaseQ
cesqquery18_9 = read "|= [[+P1[1](f14[0]()),+P2[1](f16[0]())],[+P1[1](f14[0]()),-P1[1](x0),-p6[2](x0,f16[0]())],[+p6[2](f14[0](),f15[0]()),+P2[1](f16[0]())],[+p6[2](f14[0](),f15[0]()),-P1[1](x0),-p6[2](x0,f16[0]())],[-P2[1](f14[0]()),+P2[1](f16[0]())],[-P2[1](f14[0]()),-P1[1](x0),-p6[2](x0,f16[0]())]]"

cesqquery18_10 :: SOMetaQuery
cesqquery18_10 = fromVarSubstQuery (subst (read "P1[1]"::SOMetaQVar) (read "P2[1]"::SOMetaQVar) (VarSubstQuery cesqquery18_7))

cesqquery18 :: SOMetaQuery
cesqquery18 = (BaseQ (read "[?P1[1],?P2[1]]") cesqquery18_9) $<= (ProductQ cesqquery18_7 cesqquery18_10) $ (fromList [(read "P1[1]",(! (read "P1[1]"))),(read "P2[1]",(! (read "P2[1]")))])

cesqsols18 :: [SOMetaQFullSol]
cesqsols18 = [fromList [(read "P1[1]",read "[[+p7[1]]]"),(read "P2[1]",read "[[+p1[1]]]")]]

cesqtest18 :: CESQTest
cesqtest18 = CESQTest cesqtheory18 cesqquery18 cesqsols18

-- Test 19
-- Signature mapping

-- p1[1] = itComponent
-- p2[1] = site
-- p3[1] = platform
-- p4[1] = system
-- p5[1] = dataStorage
-- p6[2] = componentOf
-- p7[1] = itArchitecture
-- k1[1] = explicit
-- k2[1] = category
-- k3[1] = kind
-- k4[1] = roleMixin
-- k5[1] = mixin
-- Skolem functions.
-- f1[1]
-- f2[1]
-- f3[0]
-- f4[0]
-- f5[0]
-- f6[0]
-- f7[0]
-- f8[0]
-- f9[0]
-- f10[0]
-- f11[0]
-- f12[0]
-- f13[0]
-- f14[0]
-- f15[0]
-- f16[0]

cesqtheory19 :: SOMetaCNF
cesqtheory19 = read "[[-p2[1](x0),+p1[1](x0)],[-p3[1](x0),+p1[1](x0)],[-p4[1](x0),+p1[1](x0)],[-p5[1](x0),+p1[1](x0)],[-p6[2](x0,x1),+p1[1](x0)],[-p6[2](x0,x1),+p7[1](x0)],[-p1[1](x0),+p6[2](x0,f1[1](x0))],[-p1[1](x0),+p7[1](f1[1](x0))],[-p7[1](x0),+p6[2](f2[1](x0),x0)],[-p7[1](x0),+p1[1](f2[1](x0))],[-p2[1](x0),-p3[1](x0)],[-p2[1](x0),-p4[1](x0)],[-p2[1](x0),-p5[1](x0)],[-p3[1](x0),-p4[1](x0)],[-p3[1](x0),-p5[1](x0)],[-p4[1](x0),-p5[1](x0)],[+p7[1](f3[0]())],[+p2[1](f4[0]())],[+p3[1](f5[0]())],[+p4[1](f6[0]())],[+p5[1](f7[0]())],[+k2[1]([[+p1[1]]])],[+k2[1]([[+p7[1]]])],[+k3[1]([[+p2[1]]])],[+k3[1]([[+p3[1]]])],[+k3[1]([[+p4[1]]])],[+k3[1]([[+p5[1]]])],[+k1[1]([[+p1[1]]])],[+k1[1]([[+p2[1]]])],[+k1[1]([[+p3[1]]])],[+k1[1]([[+p4[1]]])],[+k1[1]([[+p5[1]]])],[+k1[1]([[+p7[1]]])]]"

cesqquery19_2 :: SOMetaBaseQ
cesqquery19_2 = read "|= [[-k1[1]([[+P4[1]]])]]"

cesqquery19_4 :: SOMetaBaseQ
cesqquery19_4 = read "|= [[-k3[1]([[+P1[1]]])],[-k2[1]([[+P1[1]]])],[-k4[1]([[+P1[1]]])],[-k5[1]([[+P1[1]]])]]"

cesqquery19_5 :: SOMetaBaseQ
cesqquery19_5 = read "|= [[-k3[1]([[+P4[1]]])],[-P4[1](x0),+P1[1](x0)],[+P1[1](f13[0]())],[-P4[1](f13[0]())]]"

cesqquery19_6 :: SOMetaQuery
cesqquery19_6 = (BaseQ (read "[?P1[1]]") cesqquery18_5) $<= (BaseQ (read "[?P1[1]]") cesqquery18_4) $ (fromList [(read "P1[1]",(! (read "P1[1]")))])

cesqquery19_7 :: SOMetaQuery
cesqquery19_7 = cesqquery18_6 $<=| (BaseQ (read "[?P4[1]]") cesqquery18_2) $ (fromList [(read "P4[1]",(! (read "P4[1]")))])

cesqquery19_9 :: SOMetaBaseQ
cesqquery19_9 = read "|= [[+P1[1](f14[0]()),+P2[1](f16[0]())],[+P1[1](f14[0]()),-P1[1](x0),-p6[2](x0,f16[0]())],[+p6[2](f14[0](),f15[0]()),+P2[1](f16[0]())],[+p6[2](f14[0](),f15[0]()),-P1[1](x0),-p6[2](x0,f16[0]())],[-P2[1](f14[0]()),+P2[1](f16[0]())],[-P2[1](f14[0]()),-P1[1](x0),-p6[2](x0,f16[0]())]]"

cesqquery19_10 :: SOMetaQuery
cesqquery19_10 = fromVarSubstQuery (subst (read "P1[1]"::SOMetaQVar) (read "P2[1]"::SOMetaQVar) (VarSubstQuery cesqquery18_7))

cesqquery19 :: SOMetaQuery
cesqquery19 = (BaseQ (read "[?P1[1],?P2[1]]") cesqquery19_9) $<= (ProductQ cesqquery19_7 cesqquery19_10) $ (fromList [(read "P1[1]",(! (read "P1[1]"))),(read "P2[1]",(! (read "P2[1]")))])

cesqsols19 :: [SOMetaQFullSol]
cesqsols19 = [fromList [(read "P1[1]",read "[[+p7[1]]]"),(read "P2[1]",read "[[+p1[1]]]")]]

cesqtest19 :: CESQTest
cesqtest19 = CESQTest cesqtheory19 cesqquery19 cesqsols19

|-}

-- Test 20
-- Signature mapping

-- p1[1] = falls
-- p2[1] = waterfall
-- k1[1] = primitive
-- k2[2] = equivalent_classes

cesqsig20 :: SOMetaSignature
cesqsig20 = SOSignature (Signature [EnumProc.Empty, read "p1[1]" --> read "p2[1]" --> EnumProc.Empty] [] (read "x0" --> EnumProc.Empty)) EnumProc.Empty (read "P1[1]" --> read "P2[1]" --> EnumProc.Empty) (read "k1[1]" --> read "k2[2]" --> EnumProc.Empty)

cesqtheory20 :: SOMetaCNF
cesqtheory20 = read "[[-p1[1](x0),+p2[1](x0)],[-p2[1](x0),+p1[1](x0)],[+k1[1]([[+p1[1]]])],[+k1[1]([[+p2[1]]])],[+k2[2]([[+p1[1]]],[[+p2[1]]])]]"

cesqquery20_1 :: SOMetaBaseQ
cesqquery20_1 = FLogicQuery cesqsig20 (read "|= [[-k1[1]([[+P1[1]]]),-k1[1]([[+P2[1]]])]]")

cesqquery20_2 :: SOMetaBaseQ
cesqquery20_2 = FLogicQuery cesqsig20 (read "|= [[-k2[2]([[+P1[1]]],[[+P2[1]]])]]")

cesqquery20 :: SOMetaQuery
cesqquery20 = (BaseQ (read "[?P1[1],?P2[1]]") cesqquery20_1) $<- (BaseQ (read "[?P1[1],?P2[1]]") cesqquery20_2) $ (read "[P1[1] := P1[1],P2[1] := P2[1]]")

cesqas20 :: AnswerSet SOMetaImplicitInstantiation (SOMetaQVar =<- SOMetaQSol)
cesqas20 = runQuery cesqtheory20 cesqquery20

{-|

-- Test 21
-- Signature mapping

-- p1[1] = professor
-- p2[1] = person
-- p3[1] = individual
-- k1[1] = primitive
-- Skolem functions
-- f1[0]
-- f2[0]

cesqtheory21 :: SOMetaCNF
cesqtheory21 = read "[[-p1[1](x0),+p2[1](x0)],[-p2[1](x0),+p3[1](x0)],[-p3[1](x0),+p1[1](x0)],[+k1[1]([[+p1[1]]])],[+k1[1]([[+p2[1]]])],[+k1[1]([[+p3[1]]])]]"

cesqquery21_1 :: SOMetaBaseQ
cesqquery21_1 = read "|= [[+P1[1](f1[0]()),+P2[1](f1[0]())],[-P1[1](f1[0]()),-P2[1](f1[0]())]]"

cesqquery21_2 :: SOMetaBaseQ
cesqquery21_2 = read "P1[1](f2[0]()) # P2[1](f2[0]())"

cesqquery21_3 :: SOMetaBaseQ
cesqquery21_3 = read "|= [[-k1[1]([[+P1[1]]]),-k1[1]([[+P2[1]]])]]"

cesqquery21 :: SOMetaQuery
cesqquery21 = (BaseQ (read "[?P1[1],?P2[1]]") cesqquery21_1) $<= ((BaseQ (read "[?P1[1],?P2[1]]") cesqquery21_2) $<= (BaseQ (read "[?P1[1],?P2[1]]") cesqquery21_3) $ (fromList [(read "P1[1]",(! (read "P1[1]"))),(read "P2[1]",(! (read "P2[1]")))])) $ (fromList [(read "P1[1]",(! (read "P1[1]"))),(read "P2[1]",(! (read "P2[1]")))])

cesqsols21 :: [SOMetaQFullSol]
cesqsols21 = [fromList [(read "P1[1]",read "[[+p1[1]]]"),(read "P2[1]",read "[[+p2[1]]]")]]

cesqtest21 :: CESQTest
cesqtest21 = CESQTest cesqtheory21 cesqquery21 cesqsols21

-- Test 22
-- Signature mappinng

-- p1[1] = writer
-- p2[1] = literaryWork
-- p3[2] = writesLiteraryWork
-- k1[1] = primitive
-- k2[1] = explicit_property
-- Skolem functions.
-- f1[0]

cesqsig22 :: SOMetaSignature
cesqsig22 = SOSignature (Signature [EnumProc.Empty, read "p1[1]" --> read "p2[1]" --> EnumProc.Empty, read "p3[2]" --> EnumProc.Empty] [] (read "x0" --> EnumProc.Empty)) EnumProc.Empty (read "P1[1]" --> read "P2[1]" --> EnumProc.Empty) (read "k1[1]" --> read "k2[2]" --> EnumProc.Empty)

cesqtheory22 :: SOMetaCNF
cesqtheory22 = read "[[+k1[1]([[+p1[1]]])],[+k1[1]([[+p2[1]]])],[+k2[1]([[+p3[2]]])]]"

cesqquery22_1 :: SOMetaBaseQ
cesqquery22_1 = read "|= [[-P1[2](f1[0](),x1)]]"

cesqquery22_2 :: SOMetaBaseQ
cesqquery22_2 = read "|= [[-k2[1]([[+P1[2]]])]]"

cesqquery22_3 :: SOMetaBaseQ
cesqquery22_3 = read "|= [[-P1[2](x1,f1[0]())]]"

cesqquery22 :: SOMetaQuery
cesqquery22 = (BaseQ (read "[?P1[2]]") cesqquery22_1) $<= (BaseQ (read "[?P1[2]]") cesqquery22_2) $ (fromList [(read "P1[2]",(! (read "P1[2]")))])

cesqquery22bis :: SOMetaQuery
cesqquery22bis = (BaseQ (read "[?P1[2]]") cesqquery22_3) $<= (BaseQ (read "[?P1[2]]") cesqquery22_2) $ (fromList [(read "P1[2]",(! (read "P1[2]")))])

cesqsols22 :: [SOMetaQFullSol]
cesqsols22 = [fromList [(read "P1[2]",read "[[+p3[2]]]")]]

cesqtest22 :: CESQTest
cesqtest22 = CESQTest cesqtheory22 cesqquery22 cesqsols22

cesqtest22bis :: CESQTest
cesqtest22bis = CESQTest cesqtheory22 cesqquery22bis cesqsols22

-- Test 23
-- Signature mapping

-- p1[2] = hasOfficialLanguage
-- p2[1] = administrativeArea
-- p3[1] = language
-- p4[2] = isOfficialLanguage
-- k1[1] = primitive
-- k2[1] = explicit_property
-- Skolem functions.
-- f1[0]
-- f2[0]
-- f3[0]
-- f4[0]
-- f5[0]
-- f6[0]

cesqtheory23 :: SOMetaCNF
cesqtheory23 = read "[[-p1[2](x0,x1),+p2[1](x0)],[-p1[2](x0,x1),+p3[1](x1)],[-p4[2](x0,x1),+p3[1](x0)],[-p4[2](x0,x1),+p2[1](x1)],[+k1[1]([[+p2[1]]])],[+k1[1]([[+p3[1]]])],[+k2[1]([[+p1[2]]])],[+k2[1]([[+p4[2]]])]]"

cesqquery23_1 :: SOMetaBaseQ
cesqquery23_1 = read "|= [[+P1[2](f1[0](),f2[0]())],[-P3[1](f1[0]()),-P4[1](f2[0]())]]"

cesqquery23_2 :: SOMetaBaseQ
cesqquery23_2 = read "|= [[-k2[1]([[+P1[2]]])]]"

cesqquery23_3 :: SOMetaBaseQ
cesqquery23_3 = read "|= [[+P2[2](f3[0](),f4[0]())],[-P4[1](f3[0]()),-P3[1](f4[0]())]]"

cesqquery23_4 :: SOMetaBaseQ
cesqquery23_4 = read "|= [[-k2[1]([[+P2[2]]])]]"

cesqquery23_5 :: SOMetaBaseQ
cesqquery23_5 = read "*|= [[-P1[2](x0,x1),+P2[2](x1,x0)],[-P2[2](x1,x0),+P1[2](x0,x1)]] || [[+P1[2](f5[0](),f6[0]()),+P2[2](f6[0](),f5[0]())],[-P1[2](f5[0](),f6[0]()),+P2[2](f6[0](),f5[0]())]]"

cesqquery23_6 :: SOMetaQuery
cesqquery23_6 = (BaseQ (read "[?P1[2],?P3[1],?P4[1]]") cesqquery23_1) $<= (BaseQ (read "[?P1[2]]") cesqquery23_2) $ (fromList [(read "P1[2]",(! (read "P1[2]")))])

cesqquery23_7 :: SOMetaQuery
cesqquery23_7 = (BaseQ (read "[?P2[2],?P1[2],?P3[1],?P4[1]]") cesqquery23_3) $<= (ProductQ (BaseQ (read "[?P2[2]]") cesqquery23_4) cesqquery23_6) $ (fromList [(read "P1[2]",(! (read "P1[2]"))),(read "P2[2]",(! (read "P2[2]"))),(read "P3[1]",(! (read "P3[1]"))),(read "P4[1]",(! (read "P4[1]")))])

cesqquery23 :: SOMetaQuery
cesqquery23 = (BaseQ (read "[?P2[2],?P1[2],?P3[1],?P4[1]]") cesqquery23_5) $<= cesqquery23_7 $ (fromList [(read "P1[2]",(! (read "P1[2]"))),(read "P2[2]",(! (read "P2[2]"))),(read "P3[1]",(! (read "P3[1]"))),(read "P4[1]",(! (read "P4[1]")))])

cesqsols23 :: [SOMetaQFullSol]
cesqsols23 = [fromList [(read "P1[2]",read "[[+p1[2]]]"),(read "P2[2]",read "[[+p4[2]]]"),(read "P3[1]",read "[[+p2[1]]]"),(read "P4[1]",read "[[+p3[1]]]")]]

cesqtest23 :: CESQTest
cesqtest23 = CESQTest cesqtheory23 cesqquery23 cesqsols23

-- Test 24
-- Signature mapping

-- p1[1] = book
-- p2[2] = producedBy
-- p3[1] = writer
-- p4[2] = uses
-- p5[1] = paper
-- k1[1] = primitive
-- k2[1] = explicit_property
-- Skolem functions.
-- f1[0]
-- f2[0]
-- f3[1]
-- f4[1]
-- f5[1]
-- f6[0]

cesqtheory24 :: SOMetaCNF
cesqtheory24 = read "[[+p1[1](x0),-p2[2](x0,x1),-p3[1](x1),+p4[2](x0,f3[1](x0))],[+p1[1](x0),-p2[2](x0,x1),-p3[1](x1),-p5[1](f3[1](x0))],[-p1[1](x0),+p2[2](x0,f4[1](x0))],[-p1[1](x0),+p3[1](f4[1](x0))],[-p1[1](x0),-p4[2](x0,x1),+p5[1](x1)],[+k1[1]([[+p1[1]]])],[+k1[1]([[+p3[1]]])],[+k1[1]([[+p5[1]]])],[+k2[1]([[+p2[2]]])],[+k2[1]([[+p4[2]]])]]"

cesqquery24_1 :: SOMetaBaseQ
cesqquery24_1 = read "*|= [[-P1[1](x0),+P3[2](x0,f5[1](x0))],[-P1[1](x0),+P2[1](f5[1](x0))]] || [[+P1[1](f1[0]())],[-P3[2](f1[0](),x1),-P2[1](x1)]]"

cesqquery24_2 :: SOMetaBaseQ
cesqquery24_2 = read "|= [[+P1[1](f2[0]())],[+P3[2](f2[0](),f6[0]())],[-P2[1](f6[0]())]]"

cesqquery24_3 :: SOMetaBaseQ
cesqquery24_3 = read "|= [[-k1[1]([[+P1[1]]])]]"

cesqquery24_4 :: SOMetaBaseQ
cesqquery24_4 = read "|= [[-k2[1]([[+P3[2]]])]]"

cesqquery24 :: SOMetaQuery
cesqquery24 = (BaseQ (read "[?P1[1],?P2[1],?P3[2]]") cesqquery24_1) $<= ((BaseQ (read "[?P1[1],?P2[1],?P3[2]]") cesqquery24_2) $<= (ProductQ (BaseQ (read "[?P1[1]]") cesqquery24_3) (BaseQ (read "[?P3[2]]") cesqquery24_4)) $ (fromList [(read "P1[1]",(! (read "P1[1]"))),(read "P3[2]",(! (read "P3[2]")))])) $ (fromList [(read "P1[1]",(! (read "P1[1]"))),(read "P2[1]",(! (read "P2[1]"))),(read "P3[2]",(! (read "P3[2]")))])

cesqsols24 :: [SOMetaQFullSol]
cesqsols24 = [fromList [(read "P1[1]",read "[[+p1[1]]]"),(read "P2[1]",read "[[+p5[1]]]"),(read "P3[2]",read "[[+p4[2]]]")]]

cesqtest24 :: CESQTest
cesqtest24 = CESQTest cesqtheory24 cesqquery24 cesqsols24

-- Test 25
-- Signature mapping

-- p1[1] = vegetarianPizza
-- p2[2] = hasTopping
-- p3[1] = meatTopping
-- k1[1] = explicit
-- k2[1] = defined
-- k3[1] = primitive
-- k4[1] = explicit_property
-- k5[3] = exist_class_prop_restriction
-- Skolem functions.
-- f1[1]

cesqtheory25 :: SOMetaCNF
cesqtheory25 = read "[[-p1[1](x0),+p2[2](x0,f1[1](x0))],[-p1[1](x0),-p3[1](f1[1](x0))],[+p1[1](x0),-p2[2](x0,x1),+p3[1](x1)],[+k1[1]([[+p1[1]]])],[+k1[1]([[+p3[1]]])],[+k2[1]([[+p1[1]]])],[+k3[1]([[+p3[1]]])],[+k4[1]([[+p2[2]]])],[+k5[3]([[+p1[1]]],[[+p2[2]]],[[-p3[1]]])]]"

cesqquery25_1 :: SOMetaBaseQ
cesqquery25_1 = read "|= [[-k5[3]([[+P1[1]]],[[+P3[2]]],[[-P2[1]]])]]"

cesqquery25_2 :: SOMetaBaseQ
cesqquery25_2 = read "|= [[-k2[1]([[+P1[1]]])]]"

cesqquery25_3 :: SOMetaBaseQ
cesqquery25_3 = read "|= [[-k1[1]([[+P2[1]]])]]"

cesqquery25_4 :: SOMetaBaseQ
cesqquery25_4 = read "|= [[-k4[1]([[+P3[2]]])]]"

cesqquery25 :: SOMetaQuery
cesqquery25 = (BaseQ (read "[?P1[1],?P2[1],?P3[2]]") cesqquery25_1) $<= (ProductQ (ProductQ (BaseQ (read "[?P1[1]]") cesqquery25_2) (BaseQ (read "[?P2[1]]") cesqquery25_3)) (BaseQ (read "[?P3[2]]") cesqquery25_4)) $ (fromList [(read "P1[1]",(! (read "P1[1]"))),(read "P2[1]",(! (read "P2[1]"))),(read "P3[2]",(! (read "P3[2]")))])

cesqsols25 :: [SOMetaQFullSol]
cesqsols25 = [fromList [(read "P1[1]",read "[[+p1[1]]]"),(read "P2[1]",read "[[+p3[1]]]"),(read "P3[2]",read "[[+p2[2]]]")]]

cesqtest25 :: CESQTest
cesqtest25 = CESQTest cesqtheory25 cesqquery25 cesqsols25

-- Test 26
-- Signature mapping

-- p1[2] = takesPlaceIn
-- p2[1] = event
-- p3[1] = city
-- p4[1] = nation
-- k1[1] = primitive
-- k2[1] = explicit_property
-- Skolem functions.
-- f1[0]
-- f2[0]

cesqtheory26 :: SOMetaCNF
cesqtheory26 = read "[[-p1[2](x0,x1),+p2[1](x0)],[-p1[2](x0,x1),+p3[1](x1)],[-p1[2](x0,x1),+p4[1](x1)],[-p3[1](x0),-p4[1](x0)],[+k1[1]([[+p2[1]]])],[+k1[1]([[+p3[1]]])],[+k1[1]([[+p4[1]]])],[+k2[1]([[+p1[2]]])]]"

cesqquery26_1 :: SOMetaBaseQ
cesqquery26_1 = read "|= [[+P1[2](f1[0](),f2[0]())]]"

cesqquery26_2 :: SOMetaBaseQ
cesqquery26_2 = read "|= [[-k2[1]([[+P1[2]]])]]"

cesqquery26 :: SOMetaQuery
cesqquery26 = (BaseQ (read "[?P1[2]]") cesqquery26_1) $<= (BaseQ (read "[?P1[2]]") cesqquery26_2) $ (fromList [(read "P1[2]",(! (read "P1[2]")))])

cesqsols26 :: [SOMetaQFullSol]
cesqsols26 = [fromList [(read "P1[2]",read "[[+p1[2]]]")]]

cesqtest26 :: CESQTest
cesqtest26 = CESQTest cesqtheory26 cesqquery26 cesqsols26
|-}




main = show_enumproc_run (enumAS cesqas8 \$ ())
