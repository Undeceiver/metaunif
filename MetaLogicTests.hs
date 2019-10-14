{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE FlexibleContexts #-}

module MetaLogicTests where

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

-- Parsing tests
-- First, parse second-order terms.
-- Note that lambda abstractions are exclusively used to write down constant functions. Other functions that would have a lambda abstraction, need to be written down with composition and projections.
-- In the future, we will likely implement alternate read and print for this syntax.
parse_soterm_str1 :: String
parse_soterm_str1 = "f1[0]"

parse_soterm_soterm1 :: SOMetatermF
parse_soterm_soterm1 = read parse_soterm_str1

parse_soterm1 :: AutomatedTest
parse_soterm1 = AT "Parsing 'f1[0]'" (ATR correct (if correct then "Parsing correct." else ("Parsing incorrect. Expected " ++ (show expected) ++ " but was " ++ (show parse_soterm_soterm1) ++ " instead."))) where correct = parse_soterm_soterm1 == expected; expected = UTerm (SOF (ConstF (OFun 1 0))) :: SOMetatermF

parse_soterm_str2 :: String
parse_soterm_str2 = "f2[1]{f1[0]}"

parse_soterm_soterm2 :: SOMetatermF
parse_soterm_soterm2 = read parse_soterm_str2

parse_soterm2 :: AutomatedTest
parse_soterm2 = AT "Parsing 'f2[1]{f1[0]}'" (ATR correct (if correct then "Parsing correct." else ("Parsing incorrect. Expected " ++ (show expected) ++ " but was " ++ (show parse_soterm_soterm2) ++ " instead."))) where correct = parse_soterm_soterm2 == expected; expected = UTerm (SOF (CompF (UTerm (SOF (ConstF (OFun 2 1)))) [UTerm (SOF (ConstF (OFun 1 0)))])) :: SOMetatermF

parse_soterm_str3 :: String
parse_soterm_str3 = "f2[2]{f1[0],f2[2]}"

parse_soterm_soterm3 :: SOMetatermF
parse_soterm_soterm3 = read parse_soterm_str3

parse_soterm3_1 :: AutomatedTest
parse_soterm3_1 = AT "Parsing 'f2[2]{f1[0],f2[2]}'" (ATR correct (if correct then "Parsing correct." else ("Parsing incorrect. Expected " ++ (show expected) ++ " but was " ++ (show parse_soterm_soterm3) ++ " instead."))) where correct = parse_soterm_soterm3 == expected; expected = UTerm (SOF (CompF (UTerm (SOF (ConstF (OFun 2 2)))) [UTerm (SOF (ConstF (OFun 1 0))),UTerm (SOF (ConstF (OFun 2 2)))])) :: SOMetatermF

parse_soterm3_2 :: AutomatedTest
parse_soterm3_2 = AT "Checking arity for 'f2[2]{f1[0],f2[2]}'" (ATR correct (if correct then "Arity correct." else ("Arity incorrect. Expected 2 but was " ++ (show (arity parse_soterm_soterm3)) ++ " instead."))) where correct = (arity parse_soterm_soterm3) == 2

parse_soterm_str4 :: String
parse_soterm_str4 = "f2[2]{f1[0],f3[1]}"

parse_soterm_soterm4 :: SOMetatermF
parse_soterm_soterm4 = read parse_soterm_str4

parse_soterm4_1 :: AutomatedTest
parse_soterm4_1 = AT "Parsing 'f2[2]{f1[0],f3[1]}'" (ATR correct (if correct then "Parsing correct." else ("Parsing incorrect. Expected " ++ (show expected) ++ " but was " ++ (show parse_soterm_soterm4) ++ " instead."))) where correct = parse_soterm_soterm4 == expected; expected = UTerm (SOF (CompF (UTerm (SOF (ConstF (OFun 2 2)))) [UTerm (SOF (ConstF (OFun 1 0))),UTerm (SOF (ConstF (OFun 3 1)))])) :: SOMetatermF

parse_soterm4_2 :: AutomatedTest
parse_soterm4_2 = AT "Checking arity for 'f2[2]{f1[0],f3[1]}'" (ATR correct (if correct then "Arity correct." else ("Arity incorrect. Expected 1 but was " ++ (show (arity parse_soterm_soterm4)) ++ " instead."))) where correct = (arity parse_soterm_soterm4) == 1

parse_soterm_str5 :: String
parse_soterm_str5 = "f2[2]{f1[0],f2[2]{f3[1],f3[1]}}"

parse_soterm_soterm5 :: SOMetatermF
parse_soterm_soterm5 = read parse_soterm_str5

parse_soterm5_1 :: AutomatedTest
parse_soterm5_1 = AT "Parsing 'f2[2]{f1[0],f2[2]{f3[1],f3[1]}}'" (ATR correct (if correct then "Parsing correct." else ("Parsing incorrect. Expected " ++ (show expected) ++ " but was " ++ (show parse_soterm_soterm5) ++ " instead."))) where correct = parse_soterm_soterm5 == expected; expected = UTerm (SOF (CompF (UTerm (SOF (ConstF (OFun 2 2)))) [UTerm (SOF (ConstF (OFun 1 0))),UTerm (SOF (CompF (UTerm (SOF (ConstF (OFun 2 2)))) [UTerm (SOF (ConstF (OFun 3 1))),UTerm (SOF (ConstF (OFun 3 1)))]))])) :: SOMetatermF

parse_soterm5_2 :: AutomatedTest
parse_soterm5_2 = AT "Checking arity for 'f2[2]{f1[0],f2[2]{f3[1],f3[1]}}'" (ATR correct (if correct then "Arity correct." else ("Arity incorrect. Expected 1 but was " ++ (show (arity parse_soterm_soterm5)) ++ " instead."))) where correct = (arity parse_soterm_soterm5) == 1

parse_soterm_str6 :: String
parse_soterm_str6 = "f2[2]{f1[0],f2[2]{f3[1]{f3[1]},f3[1]}}"

parse_soterm_soterm6 :: SOMetatermF
parse_soterm_soterm6 = read parse_soterm_str6

parse_soterm6_1 :: AutomatedTest
parse_soterm6_1 = AT "Parsing 'f2[2]{f1[0],f2[2]{f3[1]{f3[1]},f3[1]}}'" (ATR correct (if correct then "Parsing correct." else ("Parsing incorrect. Expected " ++ (show expected) ++ " but was " ++ (show parse_soterm_soterm5) ++ " instead."))) where correct = parse_soterm_soterm6 == expected; expected = UTerm (SOF (CompF (UTerm (SOF (ConstF (OFun 2 2)))) [UTerm (SOF (ConstF (OFun 1 0))),UTerm (SOF (CompF (UTerm (SOF (ConstF (OFun 2 2)))) [UTerm (SOF (CompF (UTerm (SOF (ConstF (OFun 3 1)))) [UTerm (SOF (ConstF (OFun 3 1)))])),UTerm (SOF (ConstF (OFun 3 1)))]))])) :: SOMetatermF

parse_soterm6_2 :: AutomatedTest
parse_soterm6_2 = AT "Checking arity for 'f2[2]{f1[0],f2[2]{f3[1]{f3[1]},f3[1]}}'" (ATR correct (if correct then "Arity correct." else ("Arity incorrect. Expected 1 but was " ++ (show (arity parse_soterm_soterm6)) ++ " instead."))) where correct = (arity parse_soterm_soterm6) == 1

parse_soterm_str7 :: String
parse_soterm_str7 = "pi0"

parse_soterm_soterm7 :: SOMetatermF
parse_soterm_soterm7 = read parse_soterm_str7

parse_soterm7 :: AutomatedTest
parse_soterm7 = AT "Parsing 'pi0'" (ATR correct (if correct then "Parsing correct." else ("Parsing incorrect. Expected " ++ (show expected) ++ " but was " ++ (show parse_soterm_soterm7) ++ " instead."))) where correct = parse_soterm_soterm7 == expected; expected = UTerm (SOF (Proj 0)) :: SOMetatermF

parse_soterm_str8 :: String
parse_soterm_str8 = "f2[2]{pi0,pi1}"

parse_soterm_soterm8 :: SOMetatermF
parse_soterm_soterm8 = read parse_soterm_str8

parse_soterm8_1 :: AutomatedTest
parse_soterm8_1 = AT "Parsing 'f2[2]{pi0,pi1}'" (ATR correct (if correct then "Parsing correct." else ("Parsing incorrect. Expected " ++ (show expected) ++ " but was " ++ (show parse_soterm_soterm8) ++ " instead."))) where correct = parse_soterm_soterm8 == expected; expected = UTerm (SOF (CompF (UTerm (SOF (ConstF (OFun 2 2)))) [UTerm (SOF (Proj 0)),UTerm (SOF (Proj 1))])) :: SOMetatermF

parse_soterm8_2 :: AutomatedTest
parse_soterm8_2 = AT "Checking arity for 'f2[2]{pi0,pi1}'" (ATR correct (if correct then "Arity correct." else ("Arity incorrect. Expected 2 but was " ++ (show (arity parse_soterm_soterm8)) ++ " instead."))) where correct = (arity parse_soterm_soterm8 == 2)

-- Tests 9, 10 and 11 have been removed.

parse_soterm_str12 :: String
parse_soterm_str12 = "F1[0]"

parse_soterm_soterm12 :: SOMetatermF
parse_soterm_soterm12 = read parse_soterm_str12

parse_soterm12_1 :: AutomatedTest
parse_soterm12_1 = AT "Parsing 'F1[0]'" (ATR correct (if correct then "Parsing correct." else ("Parsing incorrect. Expected " ++ (show expected) ++ " but was " ++ (show parse_soterm_soterm12) ++ " instead."))) where correct = parse_soterm_soterm12 == expected; expected = UVar (SOMVar 1 0) :: SOMetatermF

parse_soterm12_2 :: AutomatedTest
parse_soterm12_2 = AT "Checking arity for 'F1[0]'" (ATR correct (if correct then "Arity correct." else ("Arity incorrect. Expected 0 but was " ++ (show (arity parse_soterm_soterm12)) ++ " instead."))) where correct = (arity parse_soterm_soterm12 == 0)

parse_soterm_str13 :: String
parse_soterm_str13 = "F1[2]"

parse_soterm_soterm13 :: SOMetatermF
parse_soterm_soterm13 = read parse_soterm_str13

parse_soterm13_1 :: AutomatedTest
parse_soterm13_1 = AT "Parsing 'F1[2]'" (ATR correct (if correct then "Parsing correct." else ("Parsing incorrect. Expected " ++ (show expected) ++ " but was " ++ (show parse_soterm_soterm13) ++ " instead."))) where correct = parse_soterm_soterm13 == expected; expected = UVar (SOMVar 1 2) :: SOMetatermF

parse_soterm13_2 :: AutomatedTest
parse_soterm13_2 = AT "Checking arity for 'F1[2]'" (ATR correct (if correct then "Arity correct." else ("Arity incorrect. Expected 2 but was " ++ (show (arity parse_soterm_soterm13)) ++ " instead."))) where correct = (arity parse_soterm_soterm13 == 2)

parse_soterm_str14 :: String
parse_soterm_str14 = "F1[2]{f1[1],F2[3]}"

parse_soterm_soterm14 :: SOMetatermF
parse_soterm_soterm14 = read parse_soterm_str14

parse_soterm14_1 :: AutomatedTest
parse_soterm14_1 = AT "Parsing 'F1[2]{f1[1],F2[3]}" (ATR correct (if correct then "Parsing correct." else ("Parsing incorrect. Expected " ++ (show expected) ++ " but was " ++ (show parse_soterm_soterm14) ++ " instead."))) where correct = parse_soterm_soterm14 == expected; expected = UTerm (SOF (CompF (UVar (SOMVar 1 2)) [UTerm (SOF (ConstF (OFun 1 1))),UVar (SOMVar 2 3)])) :: SOMetatermF

parse_soterm14_2 :: AutomatedTest
parse_soterm14_2 = AT "Checking arity for 'F1[2]{f1[1],F2[3]}" (ATR correct (if correct then "Arity correct." else ("Arity incorrect. Expected 3 but was " ++ (show (arity parse_soterm_soterm14)) ++ " instead."))) where correct = (arity parse_soterm_soterm14 == 3)

parse_soterm_str15 :: String
parse_soterm_str15 = "f1[2]{F1[0],F2[0]}"

parse_soterm_soterm15 :: SOMetatermF
parse_soterm_soterm15 = read parse_soterm_str15

parse_soterm15_1 :: AutomatedTest
parse_soterm15_1 = AT "Parsing 'f1[2]{F1[0],F2[0]}'" (ATR correct (if correct then "Parsing correct." else ("Parsing incorrect. Expected " ++ (show expected) ++ " but was " ++ (show parse_soterm_soterm15) ++ " instead."))) where correct = parse_soterm_soterm15 == expected; expected = UTerm (SOF (CompF (UTerm (SOF (ConstF (OFun 1 2)))) [UVar (SOMVar 1 0),UVar (SOMVar 2 0)])) :: SOMetatermF

parse_soterm15_2 :: AutomatedTest
parse_soterm15_2 = AT "Checking arity for 'f1[2]{F1[0],F2[0]}'" (ATR correct (if correct then "Arity correct." else ("Arity incorrect. Expected 0 but was " ++ (show (arity parse_soterm_soterm15)) ++ " instead."))) where correct = (arity parse_soterm_soterm15 == 0)

parse_soterm_str16 :: String
parse_soterm_str16 = "p1[0]"

parse_soterm_soterm16 :: SOMetaatomP
parse_soterm_soterm16 = read parse_soterm_str16

parse_soterm16_1 :: AutomatedTest
parse_soterm16_1 = AT "Parsing 'p1[0]'" (ATR correct (if correct then "Parsing correct." else ("Parsing incorrect. Expected " ++ (show expected) ++ " but was " ++ (show parse_soterm_soterm16) ++ " instead."))) where correct = parse_soterm_soterm16 == expected; expected = UTerm (SOP (ConstF (OPred 1 0))) :: SOMetaatomP

parse_soterm16_2 :: AutomatedTest
parse_soterm16_2 = AT "Checking arity for 'p1[0]'" (ATR correct (if correct then "Arity correct." else ("Arity incorrect. Expected 0 but was " ++ (show (arity parse_soterm_soterm16)) ++ " instead."))) where correct = (arity parse_soterm_soterm16 == 0)

parse_soterm_str17 :: String
parse_soterm_str17 = "p1[2]"

parse_soterm_soterm17 :: SOMetaatomP
parse_soterm_soterm17 = read parse_soterm_str17

parse_soterm17_1 :: AutomatedTest
parse_soterm17_1 = AT "Parsing 'p1[2]'" (ATR correct (if correct then "Parsing correct." else ("Parsing incorrect. Expected " ++ (show expected) ++ " but was " ++ (show parse_soterm_soterm17) ++ " instead."))) where correct = parse_soterm_soterm17 == expected; expected = UTerm (SOP (ConstF (OPred 1 2))) :: SOMetaatomP

parse_soterm17_2 :: AutomatedTest
parse_soterm17_2 = AT "Checking arity for 'p1[2]'" (ATR correct (if correct then "Arity correct." else ("Arity incorrect. Expected 2 but was " ++ (show (arity parse_soterm_soterm17)) ++ " instead."))) where correct = (arity parse_soterm_soterm17 == 2)

-- Test 18 removed.
parse_soterm_str19 :: String
parse_soterm_str19 = "P1[1]"

parse_soterm_soterm19 :: SOMetaatomP
parse_soterm_soterm19 = read parse_soterm_str19

parse_soterm19 :: AutomatedTest
parse_soterm19 = AT "Parsing 'P1[1]'" (ATR correct (if correct then "Parsing correct." else ("Parsing incorrect. Expected " ++ (show expected) ++ " but was " ++ (show parse_soterm_soterm19) ++ " instead."))) where correct = parse_soterm_soterm19 == expected; expected = UVar (SOAMVar 1 1) :: SOMetaatomP

parse_soterm_str20 :: String
parse_soterm_str20 = "P1[2]{f1[1]{f2[0]},F2[0]}"

parse_soterm_soterm20 :: SOMetaatomP
parse_soterm_soterm20 = read parse_soterm_str20

parse_soterm20_1 :: AutomatedTest
parse_soterm20_1 = AT "Parsing 'P1[2]{f1[1]{f2[0]},F2[0]}'" (ATR correct (if correct then "Parsing correct." else ("Parsing incorrect. Expected " ++ (show expected) ++ " but was " ++ (show parse_soterm_soterm20) ++ " instead."))) where correct = parse_soterm_soterm20 == expected; expected = UTerm (SOP (CompF (UVar (SOAMVar 1 2)) [UTerm (SOF (CompF (UTerm (SOF (ConstF (OFun 1 1)))) [UTerm (SOF (ConstF (OFun 2 0)))])), UVar (SOMVar 2 0)])) :: SOMetaatomP

parse_soterm20_2 :: AutomatedTest
parse_soterm20_2 = AT "Checking arity for 'P1[2]{f1[1]{f2[0]},F2[0]}'" (ATR correct (if correct then "Arity correct." else ("Arity incorrect. Expected 0 but was " ++ (show (arity parse_soterm_soterm20)) ++ " instead."))) where correct = (arity parse_soterm_soterm20 == 0)

parse_soterm_str21 :: String
parse_soterm_str21 = "P1[3]{pi1,f1[1]{f2[0]},F2[1]{F3[2]}}(x0,f3[3]{f1[1],f2[0],F2[1]{F2[1]}}(f1[1](f2[0]())))"

parse_soterm_soterm21 :: SOMetaatom
parse_soterm_soterm21 = read parse_soterm_str21

parse_soterm21 :: AutomatedTest
parse_soterm21 = AT "Parsing 'P1[3]{pi1,f1[1]{f2[0]},F2[1]{F3[2]}}(x0,f3[3]{f1[1],f2[0],F2[1]{F2[1]}}(f1[1](f2[0]())))'" (ATR correct (if correct then "Parsing correct." else ("Parsing incorrect. Expected " ++ (show expected) ++ " but was " ++ (show parse_soterm_soterm21) ++ " instead."))) where correct = parse_soterm_soterm21 == expected; expected = SOMetawrapA (APred (UTerm (SOP (CompF (UVar (SOAMVar 1 3)) [UTerm (SOF (Proj 1)),UTerm (SOF (CompF (UTerm (SOF (ConstF (OFun 1 1)))) [UTerm (SOF (ConstF (OFun 2 0)))])),UTerm (SOF (CompF (UVar (SOMVar 2 1)) [UVar (SOMVar 3 2)]))]))) [SOMetawrap (UVar (OVar 0)),SOMetawrap (UTerm (TFun (UTerm (SOF (CompF (UTerm (SOF (ConstF (OFun 3 3)))) [UTerm (SOF (ConstF (OFun 1 1))), UTerm (SOF (ConstF (OFun 2 0))), UTerm (SOF (CompF (UVar (SOMVar 2 1)) [UVar (SOMVar 2 1)]))]))) [UTerm (TFun (UTerm (SOF (ConstF (OFun 1 1)))) [UTerm (TFun (UTerm (SOF (ConstF (OFun 2 0)))) [])])]))])  :: SOMetaatom





parse_soterm_tests :: [AutomatedTest]
parse_soterm_tests = [parse_soterm1, parse_soterm2, parse_soterm3_1, parse_soterm3_2, parse_soterm4_1, parse_soterm4_2, parse_soterm5_1, parse_soterm5_2, parse_soterm6_1, parse_soterm6_2, parse_soterm7, parse_soterm8_1, parse_soterm8_2, parse_soterm12_1, parse_soterm12_2, parse_soterm13_1, parse_soterm13_2, parse_soterm14_1, parse_soterm14_2, parse_soterm15_1, parse_soterm15_2, parse_soterm16_1, parse_soterm16_2, parse_soterm17_1, parse_soterm17_2, parse_soterm19, parse_soterm20_1, parse_soterm20_2, parse_soterm21]

parse_soterm_test :: IO ()
parse_soterm_test = putStr (combine_test_results parse_soterm_tests)


-- Application and composition tests

apply_soterm_f1 :: SOMetatermF
apply_soterm_f1 = read "f1[1]"

apply_soterm_t1 :: SOMetaterm
apply_soterm_t1 = read "x0"

apply_soterm_r1 :: SOMetaterm
apply_soterm_r1 = apply_soterm_f1 *$ [apply_soterm_t1]

apply_soterm1 :: AutomatedTest
apply_soterm1 = AT ("Applying s.o. term " ++ (show apply_soterm_f1) ++ " to term " ++ (show apply_soterm_t1) ++ ".") (ATR correct (if correct then "Result correct." else "Result incorrect. Expected " ++ (show expected) ++ " but obtained " ++ (show apply_soterm_r1) ++ " instead.")) where correct = apply_soterm_r1 ~~ expected; expected = read "f1[1](x0)"::SOMetaterm

apply_soterm_f2 :: SOMetatermF
apply_soterm_f2 = read "F1[2]{f1[2]{pi0,pi0},f2[1]}"

apply_soterm_t2 :: SOMetaterm
apply_soterm_t2 = read "f2[1](f3[0]())"

apply_soterm_r2 :: SOMetaterm
apply_soterm_r2 = apply_soterm_f2 *$ [apply_soterm_t2]

apply_soterm2 :: AutomatedTest
apply_soterm2 = AT ("Applying s.o. term " ++ (show apply_soterm_f2) ++ " to term " ++ (show apply_soterm_t2) ++ ".") (ATR correct (if correct then "Result correct." else "Result incorrect. Expected " ++ (show expected) ++ " but obtained " ++ (show apply_soterm_r2) ++ " instead.")) where correct = apply_soterm_r2 ~~ expected; expected = read "F1[2](f1[2](f2[1](f3[0]()),f2[1](f3[0]())),f2[1](f2[1](f3[0]())))" :: SOMetaterm

apply_soterm_f3 :: SOMetatermF
apply_soterm_f3 = read "pi1"

apply_soterm_t3_1 :: SOMetaterm
apply_soterm_t3_1 = read "x0"

apply_soterm_t3_2 :: SOMetaterm
apply_soterm_t3_2 = read "x1"

apply_soterm_t3_3 :: SOMetaterm
apply_soterm_t3_3 = read "x2"

apply_soterm_r3 :: SOMetaterm
apply_soterm_r3 = apply_soterm_f3 *$ [apply_soterm_t3_1, apply_soterm_t3_2, apply_soterm_t3_3]

apply_soterm3 :: AutomatedTest
apply_soterm3 = AT ("Applying s.o. term " ++ (show apply_soterm_f3) ++ " to terms " ++ (show [apply_soterm_t3_1, apply_soterm_t3_2, apply_soterm_t3_3]) ++ ".") (ATR correct (if correct then "Result correct." else ("Result incorrect. Expected " ++ (show expected) ++ " but obtained " ++ (show apply_soterm_r3) ++ " instead."))) where correct = apply_soterm_r3 ~~ expected; expected = read "x1" :: SOMetaterm

-- Tests 4 and 5 removed

apply_soterm_f6 :: SOMetaatomP
apply_soterm_f6 = read "P1[3]{pi1,f1[1]{f2[0]},F2[1]{F3[2]{pi1,pi0}}}"

apply_soterm_t6_1 :: SOMetaterm
apply_soterm_t6_1 = read "x0"

apply_soterm_t6_2 :: SOMetaterm
apply_soterm_t6_2 = read "f3[3]{f1[1],f2[0],F2[1]{F2[1]}}(f1[1](f2[0]()))"

apply_soterm_r6 :: SOMetaatom
apply_soterm_r6 = apply_soterm_f6 **$ [apply_soterm_t6_1, apply_soterm_t6_2]

apply_soterm6 :: AutomatedTest
apply_soterm6 = AT ("Applying s.o. term " ++ (show apply_soterm_f6) ++ " to terms " ++ (show [apply_soterm_t6_1, apply_soterm_t6_2]) ++ ".") (ATR correct (if correct then "Result correct." else ("Result incorrect. Expected " ++ (show expected) ++ " but obtained " ++ (show apply_soterm_r6) ++ " instead."))) where correct = apply_soterm_r6 ~~ expected; expected = read "P1[3](f3[3](f1[1](f1[1](f2[0]())),f2[0](),F2[1](F2[1](f1[1](f2[0]())))),f1[1](f2[0]()),F2[1](F3[2](f3[3](f1[1](f1[1](f2[0]())),f2[0](),F2[1](F2[1](f1[1](f2[0]())))),x0)))" :: SOMetaatom

apply_soterm_f7 :: SOMetatermF
apply_soterm_f7 = read "f1[2]"

apply_soterm_s7_1 :: SOMetatermF
apply_soterm_s7_1 = read "f2[1]"

apply_soterm_s7_2 :: SOMetatermF
apply_soterm_s7_2 = read "f2[1]"

apply_soterm_r7 :: SOMetatermF
apply_soterm_r7 = apply_soterm_f7 *.. [apply_soterm_s7_1, apply_soterm_s7_2]

apply_soterm7 :: AutomatedTest
apply_soterm7 = AT ("Composing s.o. term " ++ (show apply_soterm_f7) ++ " with s.o. terms " ++ (show [apply_soterm_s7_1, apply_soterm_s7_2]) ++ ".") (ATR correct (if correct then "Result correct." else ("Result incorrect. Expected " ++  (show expected) ++ " but obtained " ++ (show apply_soterm_r7) ++ " instead."))) where correct = apply_soterm_r7 ~~ expected; expected = read "f1[2]{f2[1],f2[1]}" :: SOMetatermF

apply_soterm_f8 :: SOMetatermF
apply_soterm_f8 = read "f1[2]"

apply_soterm_s8_1 :: SOMetatermF
apply_soterm_s8_1 = read "f2[1]{f2[1]}"

apply_soterm_s8_2 :: SOMetatermF
apply_soterm_s8_2 = read "f3[1]{f3[1]}"

apply_soterm_r8 :: SOMetatermF
apply_soterm_r8 = apply_soterm_f8 *.. [apply_soterm_s8_1, apply_soterm_s8_2]

apply_soterm8 :: AutomatedTest
apply_soterm8 = AT ("Composing s.o. term " ++ (show apply_soterm_f8) ++ " with s.o. terms " ++ (show [apply_soterm_s8_1, apply_soterm_s8_2]) ++ ".") (ATR correct (if correct then "Result correct." else ("Result incorrect. Expected " ++ (show expected) ++ " but obtained " ++ (show apply_soterm_r8) ++ " instead."))) where correct = apply_soterm_r8 ~~ expected; expected = read "f1[2]{f2[1]{f2[1]},f3[1]{f3[1]}}" :: SOMetatermF

apply_soterm_f9 :: SOMetatermF
apply_soterm_f9 = read "f2[1]{f1[3]{pi0,pi1,pi0}}"

apply_soterm_s9_1 :: SOMetatermF
apply_soterm_s9_1 = read "f2[1]"

apply_soterm_s9_2 :: SOMetatermF
apply_soterm_s9_2 = read "f1[3]"

apply_soterm_r9 :: SOMetatermF
apply_soterm_r9 = apply_soterm_f9 *.. [apply_soterm_s9_1, apply_soterm_s9_2]

apply_soterm9 :: AutomatedTest
apply_soterm9 = AT ("Composing s.o. term " ++ (show apply_soterm_f9) ++ " with s.o. terms " ++ (show [apply_soterm_s9_1, apply_soterm_s9_2]) ++ ".") (ATR correct (if correct then "Result correct." else ("Result incorrect. Expected " ++ (show expected) ++ " but obtained " ++ (show apply_soterm_r9) ++ " instead."))) where correct = apply_soterm_r9 ~~ expected; expected = read "f2[1]{f1[3]{f2[1],f1[3],f2[1]}}" :: SOMetatermF

apply_soterm_f10 :: SOMetatermF
apply_soterm_f10 = read "f2[1]{f1[3]{pi1,pi0,pi1}}"

apply_soterm_s10_1 :: SOMetatermF
apply_soterm_s10_1 = read "f2[1]{f2[1]}"

apply_soterm_s10_2 :: SOMetatermF
apply_soterm_s10_2 = read "f2[1]{f1[3]}"

apply_soterm_r10 :: SOMetatermF
apply_soterm_r10 = apply_soterm_f10 *.. [apply_soterm_s10_1, apply_soterm_s10_2]

apply_soterm10 :: AutomatedTest
apply_soterm10 = AT ("Composing s.o. term " ++ (show apply_soterm_f10) ++ " with s.o. terms " ++ (show [apply_soterm_s10_1, apply_soterm_s10_2]) ++ ".") (ATR correct (if correct then "Result correct." else ("Result incorrect. Expected " ++ (show expected) ++ " but obtained " ++ (show apply_soterm_r10) ++ " instead."))) where correct = apply_soterm_r10 ~~ expected; expected = read "f2[1]{f1[3]{f2[1]{f1[3]},f2[1]{f2[1]},f2[1]{f1[3]}}}" :: SOMetatermF

-- Tests 11 and 12 removed

apply_soterm_f13 :: SOMetatermF
apply_soterm_f13 = read "f1[2]"

apply_soterm_s13_1 :: SOMetatermF
apply_soterm_s13_1 = read "pi2"

apply_soterm_s13_2 :: SOMetatermF
apply_soterm_s13_2 = read "pi0"

apply_soterm_r13 :: SOMetatermF
apply_soterm_r13 = apply_soterm_f13 *.. [apply_soterm_s13_1, apply_soterm_s13_2]

apply_soterm13 :: AutomatedTest
apply_soterm13 = AT ("Composing s.o. term " ++ (show apply_soterm_f13) ++ " with s.o. terms " ++ (show [apply_soterm_s13_1, apply_soterm_s13_2]) ++ ".") (ATR correct (if correct then "Result correct." else ("Result incorrect. Expected " ++ (show expected) ++ " but obtained " ++ (show apply_soterm_r13) ++ " instead."))) where correct = apply_soterm_r13 ~~ expected; expected = read "f1[2]{pi2,pi0}"

apply_soterm_f14 :: SOMetatermF
apply_soterm_f14 = read "pi1"

apply_soterm_s14_1 :: SOMetatermF
apply_soterm_s14_1 = read "f1[0]"

apply_soterm_s14_2 :: SOMetatermF
apply_soterm_s14_2 = read "f2[1]{f2[1]}"

apply_soterm_s14_3 :: SOMetatermF
apply_soterm_s14_3 = read "pi3"

apply_soterm_r14 :: SOMetatermF
apply_soterm_r14 = apply_soterm_f14 *.. [apply_soterm_s14_1, apply_soterm_s14_2, apply_soterm_s14_3]

apply_soterm14 :: AutomatedTest
apply_soterm14 = AT ("Composing s.o. term " ++ (show apply_soterm_f14) ++ " with s.o. terms " ++ (show [apply_soterm_s14_1, apply_soterm_s14_2, apply_soterm_s14_3]) ++ ".") (ATR correct (if correct then "Result correct." else ("Result incorrect. Expected " ++ (show expected) ++ " but obtained " ++ (show apply_soterm_r14) ++  " instead."))) where correct = apply_soterm_r14 ~~ expected; expected = read "f2[1]{f2[1]}"

apply_soterm_f15 :: SOMetatermF
apply_soterm_f15 = read "pi1"

apply_soterm_s15_1 :: SOMetatermF
apply_soterm_s15_1 = read "f1[1]"

apply_soterm_s15_2 :: SOMetatermF
apply_soterm_s15_2 = read "pi4"

apply_soterm_r15 :: SOMetatermF
apply_soterm_r15 = apply_soterm_f15 *.. [apply_soterm_s15_1, apply_soterm_s15_2]

apply_soterm15 :: AutomatedTest
apply_soterm15 = AT ("Composing s.o. term " ++ (show apply_soterm_f15) ++ " with s.o. terms " ++ (show [apply_soterm_s15_1, apply_soterm_s15_2]) ++ ".") (ATR correct (if correct then "Result correct." else ("Result incorrect. Expected " ++ (show expected) ++ " but obtained " ++ (show apply_soterm_r15) ++ " instead."))) where correct = apply_soterm_r15 ~~ expected; expected = read "pi4"

apply_soterm_f16 :: SOMetatermF
apply_soterm_f16 = read "pi0"

apply_soterm_s16_1 :: SOMetatermF
apply_soterm_s16_1 = read "f1[1]{pi1}"

apply_soterm_r16 :: SOMetatermF
apply_soterm_r16 = apply_soterm_f16 *.. [apply_soterm_s16_1]

apply_soterm16 :: AutomatedTest
apply_soterm16 = AT ("Composing s.o. term " ++ (show apply_soterm_f16) ++ " with s.o. terms " ++ (show [apply_soterm_s16_1]) ++ ".") (ATR correct (if correct then "Result correct." else ("Result incorrect. Expected " ++ (show expected) ++ " but obtained " ++ (show apply_soterm_r16) ++ " instead."))) where correct = apply_soterm_r16 ~~ expected; expected = read "f1[1]{pi1}"

apply_soterm_f17 :: SOMetaatomP
apply_soterm_f17 = read "p1[2]{f1[1]{pi2},pi0}"

apply_soterm_s17_1 :: SOMetatermF
apply_soterm_s17_1 = read "f1[1]{f2[0]}"

apply_soterm_s17_2 :: SOMetatermF
apply_soterm_s17_2 = read "f134[2]"

apply_soterm_s17_3 :: SOMetatermF
apply_soterm_s17_3 = read "f1[1]{f1[1]}"

apply_soterm_r17 :: SOMetaatomP
apply_soterm_r17 = apply_soterm_f17 **. [apply_soterm_s17_1, apply_soterm_s17_2, apply_soterm_s17_3]

apply_soterm17 :: AutomatedTest
apply_soterm17 = AT ("Composing s.o. term " ++ (show apply_soterm_f17) ++ " with s.o. terms " ++ (show [apply_soterm_s17_1, apply_soterm_s17_2, apply_soterm_s17_3]) ++ ".") (ATR correct (if correct then "Result correct." else ("Result incorrect. Expected " ++ (show expected) ++ " but obtained " ++ (show apply_soterm_r17) ++ " instead."))) where correct = apply_soterm_r17 ~~ expected; expected = read "p1[2]{f1[1]{f1[1]{f1[1]}},f1[1]{f2[0]}}"





apply_soterm_tests :: [AutomatedTest]
apply_soterm_tests = [apply_soterm1, apply_soterm2, apply_soterm3, apply_soterm6, apply_soterm7, apply_soterm8, apply_soterm9, apply_soterm10, apply_soterm13, apply_soterm14, apply_soterm15, apply_soterm16, apply_soterm17]

apply_soterm_test :: IO ()
apply_soterm_test = putStr (combine_test_results apply_soterm_tests)

-- Pending: First-order unification of second-order terms.


all_test :: IO ()
all_test = (putStr "\n\nSECOND-ORDER TERM PARSING TESTS\n\n") >> parse_soterm_test >>
		(putStr "\n\nSECOND-ORDER TERM APPLICATION AND COMPOSITION TESTS\n\n") >> apply_soterm_test

