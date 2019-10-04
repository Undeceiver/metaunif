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

-- Parsing tests
-- First, parse second-order terms.
-- Note that lambda abstractions are exclusively used to write down constant functions. Other functions that would have a lambda abstraction, need to be written down with composition and projections.
-- In the future, we will likely implement alternate read and print for this syntax.
parse_soterm_str1 :: String
parse_soterm_str1 = "f1[0]"

parse_soterm_soterm1 :: SOMetatermF
parse_soterm_soterm1 = read parse_soterm_str1

parse_soterm1 :: AutomatedTest
parse_soterm1 = AT "Parsing 'f1[0]'" (ATR correct (if correct then "Parsing correct." else ("Parsing incorrect. Expected " ++ (show expected) ++ " but was " ++ (show parse_soterm_soterm1) ++ " instead."))) where correct = parse_soterm_soterm1 == expected; expected = Fix (ConstF (CFunc (OFun 1 0))) :: SOMetatermF

parse_soterm_str2 :: String
parse_soterm_str2 = "f2[1]{f1[0][]}"

parse_soterm_soterm2 :: SOMetatermF
parse_soterm_soterm2 = read parse_soterm_str2

parse_soterm2 :: AutomatedTest
parse_soterm2 = AT "Parsing 'f2[1]{f1[0][]}'" (ATR correct (if correct then "Parsing correct." else ("Parsing incorrect. Expected " ++ (show expected) ++ " but was " ++ (show parse_soterm_soterm2) ++ " instead."))) where correct = parse_soterm_soterm2 == expected; expected = Fix (CompF (CFunc (OFun 2 1)) [(Fix (ConstF (CFunc (OFun 1 0))),[])]) :: SOMetatermF

parse_soterm_str3 :: String
parse_soterm_str3 = "f2[2]{f1[0][],f2[2][0,1]}"

parse_soterm_soterm3 :: SOMetatermF
parse_soterm_soterm3 = read parse_soterm_str3

parse_soterm3_1 :: AutomatedTest
parse_soterm3_1 = AT "Parsing 'f2[2]{f1[0][],f2[2][0,1]}'" (ATR correct (if correct then "Parsing correct." else ("Parsing incorrect. Expected " ++ (show expected) ++ " but was " ++ (show parse_soterm_soterm3) ++ " instead."))) where correct = parse_soterm_soterm3 == expected; expected = Fix (CompF (CFunc (OFun 2 2)) [(Fix (ConstF (CFunc (OFun 1 0))),[]),(Fix (ConstF (CFunc (OFun 2 2))),[0,1])]) :: SOMetatermF

parse_soterm3_2 :: AutomatedTest
parse_soterm3_2 = AT "Checking arity for 'f2[2]{f1[0][],f2[2][0,1]}'" (ATR correct (if correct then "Arity correct." else ("Arity incorrect. Expected 2 but was " ++ (show (arity parse_soterm_soterm3)) ++ " instead."))) where correct = (arity parse_soterm_soterm3) == 2

parse_soterm_str4 :: String
parse_soterm_str4 = "f2[2]{f1[0][],f2[2][0,0]}"

parse_soterm_soterm4 :: SOMetatermF
parse_soterm_soterm4 = read parse_soterm_str4

parse_soterm4_1 :: AutomatedTest
parse_soterm4_1 = AT "Parsing 'f2[2]{f1[0][],f2[2][0,0]}'" (ATR correct (if correct then "Parsing correct." else ("Parsing incorrect. Expected " ++ (show expected) ++ " but was " ++ (show parse_soterm_soterm4) ++ " instead."))) where correct = parse_soterm_soterm4 == expected; expected = Fix (CompF (CFunc (OFun 2 2)) [(Fix (ConstF (CFunc (OFun 1 0))),[]),(Fix (ConstF (CFunc (OFun 2 2))),[0,0])]) :: SOMetatermF

parse_soterm4_2 :: AutomatedTest
parse_soterm4_2 = AT "Checking arity for 'f2[2]{f1[0][],f2[2][0,0]}'" (ATR correct (if correct then "Arity correct." else ("Arity incorrect. Expected 1 but was " ++ (show (arity parse_soterm_soterm4)) ++ " instead."))) where correct = (arity parse_soterm_soterm4) == 1

parse_soterm_str5 :: String
parse_soterm_str5 = "f2[2]{f1[0][],f2[2]{f3[1][2],f3[1][0]}[0,1,1]}"

parse_soterm_soterm5 :: SOMetatermF
parse_soterm_soterm5 = read parse_soterm_str5

parse_soterm5_1 :: AutomatedTest
parse_soterm5_1 = AT "Parsing 'f2[2]{f1[0][],f2[2]{f3[1][2],f3[1][0]}[0,1,1]}'" (ATR correct (if correct then "Parsing correct." else ("Parsing incorrect. Expected " ++ (show expected) ++ " but was " ++ (show parse_soterm_soterm5) ++ " instead."))) where correct = parse_soterm_soterm5 == expected; expected = Fix (CompF (CFunc (OFun 2 2)) [(Fix (ConstF (CFunc (OFun 1 0))),[]),(Fix (CompF (CFunc (OFun 2 2)) [(Fix (ConstF (CFunc (OFun 3 1))),[2]),(Fix (ConstF (CFunc (OFun 3 1))),[0])]),[0,1,1])]) :: SOMetatermF

parse_soterm5_2 :: AutomatedTest
parse_soterm5_2 = AT "Checking arity for 'f2[2]{f1[0][],f2[2]{f3[1][2],f3[1][0]}[0,1,1]}'" (ATR correct (if correct then "Arity correct." else ("Arity incorrect. Expected 2 but was " ++ (show (arity parse_soterm_soterm5)) ++ " instead."))) where correct = (arity parse_soterm_soterm5) == 2

parse_soterm_str6 :: String
parse_soterm_str6 = "f2[2]{f1[0][],f2[2]{f3[1][2],f3[1][0]}[0,1,2]}"

parse_soterm_soterm6 :: SOMetatermF
parse_soterm_soterm6 = read parse_soterm_str6

parse_soterm6_1 :: AutomatedTest
parse_soterm6_1 = AT "Parsing 'f2[2]{f1[0][],f2[2]{f3[1][2],f3[1][0]}[0,1,2]}'" (ATR correct (if correct then "Parsing correct." else ("Parsing incorrect. Expected " ++ (show expected) ++ " but was " ++ (show parse_soterm_soterm5) ++ " instead."))) where correct = parse_soterm_soterm6 == expected; expected = Fix (CompF (CFunc (OFun 2 2)) [(Fix (ConstF (CFunc (OFun 1 0))),[]),(Fix (CompF (CFunc (OFun 2 2)) [(Fix (ConstF (CFunc (OFun 3 1))),[2]),(Fix (ConstF (CFunc (OFun 3 1))),[0])]),[0,1,2])]) :: SOMetatermF

parse_soterm6_2 :: AutomatedTest
parse_soterm6_2 = AT "Checking arity for 'f2[2]{f1[0][],f2[2]{f3[1][2],f3[1][0]}[0,1,2]}'" (ATR correct (if correct then "Arity correct." else ("Arity incorrect. Expected 3 but was " ++ (show (arity parse_soterm_soterm6)) ++ " instead."))) where correct = (arity parse_soterm_soterm6) == 3

parse_soterm_str7 :: String
parse_soterm_str7 = "pi1[2]"

parse_soterm_soterm7 :: SOMetatermF
parse_soterm_soterm7 = read parse_soterm_str7

parse_soterm7 :: AutomatedTest
parse_soterm7 = AT "Parsing 'pi1[2]'" (ATR correct (if correct then "Parsing correct." else ("Parsing incorrect. Expected " ++ (show expected) ++ " but was " ++ (show parse_soterm_soterm7) ++ " instead."))) where correct = parse_soterm_soterm7 == expected; expected = Fix (Proj 2 1) :: SOMetatermF

parse_soterm_str8 :: String
parse_soterm_str8 = "f2[2]{pi1[2][0,1],pi2[3][0,1,2]}"

parse_soterm_soterm8 :: SOMetatermF
parse_soterm_soterm8 = read parse_soterm_str8

parse_soterm8_1 :: AutomatedTest
parse_soterm8_1 = AT "Parsing 'f2[2]{pi1[2][0,1],pi2[3][2,0,2]}'" (ATR correct (if correct then "Parsing correct." else ("Parsing incorrect. Expected " ++ (show expected) ++ " but was " ++ (show parse_soterm_soterm8) ++ " instead."))) where correct = parse_soterm_soterm8 == expected; expected = Fix (CompF (CFunc (OFun 2 2)) [(Fix (Proj 2 1),[0,1]),(Fix (Proj 3 2),[2,0,2])]) :: SOMetatermF

parse_soterm8_2 :: AutomatedTest
parse_soterm8_2 = AT "Checking arity for 'f2[2]{pi1[2][0,1],pi2[3][2,0,2]}'" (ATR correct (if correct then "Arity correct." else ("Arity incorrect. Expected 3 but was " ++ (show (arity parse_soterm_soterm8)) ++ " instead."))) where correct = (arity parse_soterm_soterm8 == 3)

parse_soterm_str9 :: String
parse_soterm_str9 = "(\\x -> f1[0]())[0]"

parse_soterm_soterm9 :: SOMetatermF
parse_soterm_soterm9 = read parse_soterm_str9

parse_soterm9_1 :: AutomatedTest
parse_soterm9_1 = AT "Parsing '(\\x -> f1[0]())[0]'" (ATR correct (if correct then "Parsing correct." else ("Parsing incorrect. Expected " ++ (show expected) ++ " but was " ++ (show parse_soterm_soterm9) ++ " instead."))) where correct = parse_soterm_soterm9 == expected; expected = Fix (CConstF 0 (SOMetawrap (UTerm (TFun (Fix (ConstF (CFunc (OFun 1 0)))) [])))) :: SOMetatermF

parse_soterm9_2 :: AutomatedTest
parse_soterm9_2 = AT "Checking arity for '(\\x -> f1[0]())[0]'" (ATR correct (if correct then "Arity correct." else ("Arity incorrect. Expected 0 but was " ++ (show (arity parse_soterm_soterm9)) ++ " instead."))) where correct = (arity parse_soterm_soterm9 == 0)

parse_soterm_str10 :: String
parse_soterm_str10 = "(\\x -> f1[0]())[2]"

parse_soterm_soterm10 :: SOMetatermF
parse_soterm_soterm10 = read parse_soterm_str10

parse_soterm10_1 :: AutomatedTest
parse_soterm10_1 = AT "Parsing '(\\x -> f1[0]())[2]'" (ATR correct (if correct then "Parsing correct." else ("Parsing incorrect. Expected " ++ (show expected) ++ " but was " ++ (show parse_soterm_soterm10) ++ " instead."))) where correct = parse_soterm_soterm10 == expected; expected = Fix (CConstF 2 (SOMetawrap (UTerm (TFun (Fix (ConstF (CFunc (OFun 1 0)))) [])))) :: SOMetatermF

parse_soterm10_2 :: AutomatedTest
parse_soterm10_2 = AT "Checking arity for '(\\x -> f1[0]())[2]'" (ATR correct (if correct then "Arity correct." else ("Arity incorrect. Expected 2 but was " ++ (show (arity parse_soterm_soterm10)) ++ " instead."))) where correct = (arity parse_soterm_soterm10 == 2)

parse_soterm_str11 :: String
parse_soterm_str11 = "(\\x -> pi0[1](f1[0]()))[0]"

parse_soterm_soterm11 :: SOMetatermF
parse_soterm_soterm11 = read parse_soterm_str11

parse_soterm11 :: AutomatedTest
parse_soterm11 = AT "Parsing '(\\x -> pi0[1](f1[0]()))[0]'" (ATR correct (if correct then "Parsing correct." else ("Parsing incorrect. Expected " ++ (show expected) ++ " but was " ++ (show parse_soterm_soterm11) ++ " instead."))) where correct = parse_soterm_soterm11 == expected; expected = Fix (CConstF 0 (SOMetawrap (UTerm (TFun (Fix (Proj 1 0)) [UTerm (TFun (Fix (ConstF (CFunc (OFun 1 0)))) [])])))) :: SOMetatermF

parse_soterm_str12 :: String
parse_soterm_str12 = "F1[0]"

parse_soterm_soterm12 :: SOMetatermF
parse_soterm_soterm12 = read parse_soterm_str12

parse_soterm12_1 :: AutomatedTest
parse_soterm12_1 = AT "Parsing 'F1[0]'" (ATR correct (if correct then "Parsing correct." else ("Parsing incorrect. Expected " ++ (show expected) ++ " but was " ++ (show parse_soterm_soterm12) ++ " instead."))) where correct = parse_soterm_soterm12 == expected; expected = Fix (ConstF (SOMV (SOMVar 1 0))) :: SOMetatermF

parse_soterm12_2 :: AutomatedTest
parse_soterm12_2 = AT "Checking arity for 'F1[0]'" (ATR correct (if correct then "Arity correct." else ("Arity incorrect. Expected 0 but was " ++ (show (arity parse_soterm_soterm12)) ++ " instead."))) where correct = (arity parse_soterm_soterm12 == 0)

parse_soterm_str13 :: String
parse_soterm_str13 = "F1[2]"

parse_soterm_soterm13 :: SOMetatermF
parse_soterm_soterm13 = read parse_soterm_str13

parse_soterm13_1 :: AutomatedTest
parse_soterm13_1 = AT "Parsing 'F1[2]'" (ATR correct (if correct then "Parsing correct." else ("Parsing incorrect. Expected " ++ (show expected) ++ " but was " ++ (show parse_soterm_soterm13) ++ " instead."))) where correct = parse_soterm_soterm13 == expected; expected = Fix (ConstF (SOMV (SOMVar 1 2))) :: SOMetatermF

parse_soterm13_2 :: AutomatedTest
parse_soterm13_2 = AT "Checking arity for 'F1[2]'" (ATR correct (if correct then "Arity correct." else ("Arity incorrect. Expected 2 but was " ++ (show (arity parse_soterm_soterm13)) ++ " instead."))) where correct = (arity parse_soterm_soterm13 == 2)

parse_soterm_str14 :: String
parse_soterm_str14 = "F1[2]{f1[1][0],F2[3][0,0,0]}"

parse_soterm_soterm14 :: SOMetatermF
parse_soterm_soterm14 = read parse_soterm_str14

parse_soterm14_1 :: AutomatedTest
parse_soterm14_1 = AT "Parsing 'F1[2]{f1[1][0],F2[3][0,0,0]}" (ATR correct (if correct then "Parsing correct." else ("Parsing incorrect. Expected " ++ (show expected) ++ " but was " ++ (show parse_soterm_soterm14) ++ " instead."))) where correct = parse_soterm_soterm14 == expected; expected = Fix (CompF (SOMV (SOMVar 1 2)) [(Fix (ConstF (CFunc (OFun 1 1))),[0]),(Fix (ConstF (SOMV (SOMVar 2 3))),[0,0,0])]) :: SOMetatermF

parse_soterm14_2 :: AutomatedTest
parse_soterm14_2 = AT "Checking arity for 'F1[2]{f1[1][0],F2[3][0,0,0]}" (ATR correct (if correct then "Arity correct." else ("Arity incorrect. Expected 1 but was " ++ (show (arity parse_soterm_soterm14)) ++ " instead."))) where correct = (arity parse_soterm_soterm14 == 1)

parse_soterm_str15 :: String
parse_soterm_str15 = "f1[2]{F1[0][],F2[0][]}"

parse_soterm_soterm15 :: SOMetatermF
parse_soterm_soterm15 = read parse_soterm_str15

parse_soterm15_1 :: AutomatedTest
parse_soterm15_1 = AT "Parsing 'f1[2]{F1[0][],F2[0][]}'" (ATR correct (if correct then "Parsing correct." else ("Parsing incorrect. Expected " ++ (show expected) ++ " but was " ++ (show parse_soterm_soterm15) ++ " instead."))) where correct = parse_soterm_soterm15 == expected; expected = Fix (CompF (CFunc (OFun 1 2)) [(Fix (ConstF (SOMV (SOMVar 1 0))),[]),(Fix (ConstF (SOMV (SOMVar 2 0))),[])]) :: SOMetatermF

parse_soterm15_2 :: AutomatedTest
parse_soterm15_2 = AT "Checking arity for 'f1[2]{F1[0][],F2[0][]}'" (ATR correct (if correct then "Arity correct." else ("Arity incorrect. Expected 0 but was " ++ (show (arity parse_soterm_soterm15)) ++ " instead."))) where correct = (arity parse_soterm_soterm15 == 0)

parse_soterm_str16 :: String
parse_soterm_str16 = "p1[0]"

parse_soterm_soterm16 :: SOMetaatomP
parse_soterm_soterm16 = read parse_soterm_str16

parse_soterm16_1 :: AutomatedTest
parse_soterm16_1 = AT "Parsing 'p1[0]'" (ATR correct (if correct then "Parsing correct." else ("Parsing incorrect. Expected " ++ (show expected) ++ " but was " ++ (show parse_soterm_soterm16) ++ " instead."))) where correct = parse_soterm_soterm16 == expected; expected = ConstF (CFunc (OPred 1 0)) :: SOMetaatomP

parse_soterm16_2 :: AutomatedTest
parse_soterm16_2 = AT "Checking arity for 'p1[0]'" (ATR correct (if correct then "Arity correct." else ("Arity incorrect. Expected 0 but was " ++ (show (arity parse_soterm_soterm16)) ++ " instead."))) where correct = (arity parse_soterm_soterm16 == 0)

parse_soterm_str17 :: String
parse_soterm_str17 = "p1[2]"

parse_soterm_soterm17 :: SOMetaatomP
parse_soterm_soterm17 = read parse_soterm_str17

parse_soterm17_1 :: AutomatedTest
parse_soterm17_1 = AT "Parsing 'p1[2]'" (ATR correct (if correct then "Parsing correct." else ("Parsing incorrect. Expected " ++ (show expected) ++ " but was " ++ (show parse_soterm_soterm17) ++ " instead."))) where correct = parse_soterm_soterm17 == expected; expected = ConstF (CFunc (OPred 1 2)) :: SOMetaatomP

parse_soterm17_2 :: AutomatedTest
parse_soterm17_2 = AT "Checking arity for 'p1[2]'" (ATR correct (if correct then "Arity correct." else ("Arity incorrect. Expected 2 but was " ++ (show (arity parse_soterm_soterm17)) ++ " instead."))) where correct = (arity parse_soterm_soterm17 == 2)

parse_soterm_str18 :: String
parse_soterm_str18 = "(\\z -> p1[2](f1[0](),f2[1](f1[0]())))[7]"

parse_soterm_soterm18 :: SOMetaatomP
parse_soterm_soterm18 = read parse_soterm_str18

parse_soterm18_1 :: AutomatedTest
parse_soterm18_1 = AT "Parsing '(\\z -> p1[2](f1[0](),f2[1](f1[0]())))[7]'" (ATR correct (if correct then "Parsing correct." else ("Parsing incorrect. Expected " ++ (show expected) ++ " but was " ++ (show parse_soterm_soterm18) ++ " instead."))) where correct = parse_soterm_soterm18 == expected; expected = CConstF 7 (SOMetawrapA (Atom (APred (ConstF (CFunc (OPred 1 2))) [SOMetawrap (UTerm (TFun (Fix (ConstF (CFunc (OFun 1 0)))) [])), SOMetawrap (UTerm (TFun (Fix (ConstF (CFunc (OFun 2 1)))) [UTerm (TFun (Fix (ConstF (CFunc (OFun 1 0)))) [])]))]))) :: SOMetaatomP

parse_soterm18_2 :: AutomatedTest
parse_soterm18_2 = AT "Checking arity for '(\\z -> p1[2](f1[0](),f2[1](f1[0]())))[7]'" (ATR correct (if correct then "Arity correct." else ("Arity incorrect. Expected 7 but was " ++ (show (arity parse_soterm_soterm18)) ++ " instead."))) where correct = (arity parse_soterm_soterm18 == 7)

parse_soterm_str19 :: String
parse_soterm_str19 = "P1[1]"

parse_soterm_soterm19 :: SOMetaatomP
parse_soterm_soterm19 = read parse_soterm_str19

parse_soterm19 :: AutomatedTest
parse_soterm19 = AT "Parsing 'P1[1]'" (ATR correct (if correct then "Parsing correct." else ("Parsing incorrect. Expected " ++ (show expected) ++ " but was " ++ (show parse_soterm_soterm19) ++ " instead."))) where correct = parse_soterm_soterm19 == expected; expected = ConstF (SOMV (SOAMVar 1 1)) :: SOMetaatomP

parse_soterm_str20 :: String
parse_soterm_str20 = "P1[2]{f1[1]{(\\x -> f2[0]())[1][1]}[2,2],F2[0][]}"

parse_soterm_soterm20 :: SOMetaatomP
parse_soterm_soterm20 = read parse_soterm_str20

parse_soterm20_1 :: AutomatedTest
parse_soterm20_1 = AT "Parsing 'P1[2]{f1[1]{(\\x -> f2[0]())[1][1]}[2,2],F2[0][]}'" (ATR correct (if correct then "Parsing correct." else ("Parsing incorrect. Expected " ++ (show expected) ++ " but was " ++ (show parse_soterm_soterm20) ++ " instead."))) where correct = parse_soterm_soterm20 == expected; expected = CompF (SOMV (SOAMVar 1 2)) [(Fix (CompF (CFunc (OFun 1 1)) [(Fix (CConstF 1 (SOMetawrap (UTerm (TFun (Fix (ConstF (CFunc (OFun 2 0)))) [])))),[1])]),[2,2]),(Fix (ConstF (SOMV (SOMVar 2 0))),[])] :: SOMetaatomP

parse_soterm20_2 :: AutomatedTest
parse_soterm20_2 = AT "Checking arity for 'P1[2]{f1[1]{(\\x -> f2[0]())[1][1]}[2,2],F2[0][]}'" (ATR correct (if correct then "Arity correct." else ("Arity incorrect. Expected 3 but was " ++ (show (arity parse_soterm_soterm20)) ++ " instead."))) where correct = (arity parse_soterm_soterm20 == 3)

parse_soterm_str21 :: String
parse_soterm_str21 = "P1[3]{pi1[2][1,1],f1[1]{(\\x -> f2[0]())[2][1,0]}[1,0],F2[1]{F3[2][0,1]}[1,0]}(x0,f3[3]{f1[1][0],f2[0][],F2[1]{F2[1][0]}[0]}(f1[1](f2[0]())))"

parse_soterm_soterm21 :: SOMetaatom
parse_soterm_soterm21 = read parse_soterm_str21

parse_soterm21 :: AutomatedTest
parse_soterm21 = AT "Parsing 'P1[3]{pi1[2][1,1],f1[1]{(\\x -> f2[0]())[2][1,0]}[1,0],F2[1]{F3[2][0,1]}[1,0]}(x0,f3[3]{f1[1][0],f2[0][],F2[1]{F2[1][0]}[0]}(f1[1](f2[0]())))'" (ATR correct (if correct then "Parsing correct." else ("Parsing incorrect. Expected " ++ (show expected) ++ " but was " ++ (show parse_soterm_soterm21) ++ " instead."))) where correct = parse_soterm_soterm21 == expected; expected = SOMetawrapA (Atom (APred (CompF (SOMV (SOAMVar 1 3)) [(Fix (Proj 2 1),[1,1]),(Fix (CompF (CFunc (OFun 1 1)) [(Fix (CConstF 2 (SOMetawrap (UTerm (TFun (Fix (ConstF (CFunc (OFun 2 0)))) [])))),[1,0])]),[1,0]),(Fix (CompF (SOMV (SOMVar 2 1)) [(Fix (ConstF (SOMV (SOMVar 3 2))),[0,1])]),[1,0])]) [SOMetawrap (UVar (OVar 0)),SOMetawrap (UTerm (TFun (Fix (CompF (CFunc (OFun 3 3)) [(Fix (ConstF (CFunc (OFun 1 1))),[0]),(Fix (ConstF (CFunc (OFun 2 0))),[]),(Fix (CompF (SOMV (SOMVar 2 1)) [(Fix (ConstF (SOMV (SOMVar 2 1))),[0])]),[0])])) [UTerm (TFun (Fix (ConstF (CFunc (OFun 1 1)))) [UTerm (TFun (Fix (ConstF (CFunc (OFun 2 0)))) [])])]))])) :: SOMetaatom





parse_soterm_tests :: [AutomatedTest]
parse_soterm_tests = [parse_soterm1, parse_soterm2, parse_soterm3_1, parse_soterm3_2, parse_soterm4_1, parse_soterm4_2, parse_soterm5_1, parse_soterm5_2, parse_soterm6_1, parse_soterm6_2, parse_soterm7, parse_soterm8_1, parse_soterm8_2, parse_soterm9_1, parse_soterm9_2, parse_soterm10_1, parse_soterm10_2, parse_soterm11, parse_soterm12_1, parse_soterm12_2, parse_soterm13_1, parse_soterm13_2, parse_soterm14_1, parse_soterm14_2, parse_soterm15_1, parse_soterm15_2, parse_soterm16_1, parse_soterm16_2, parse_soterm17_1, parse_soterm17_2, parse_soterm18_1, parse_soterm18_2, parse_soterm19, parse_soterm20_1, parse_soterm20_2, parse_soterm21]

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
apply_soterm1 = AT ("Applying s.o. term " ++ (show apply_soterm_f1) ++ " to term " ++ (show apply_soterm_t1) ++ ".") (ATR correct (if correct then "Result correct." else "Result incorrect. Expected " ++ (show expected) ++ " but obtained " ++ (show apply_soterm_r1) ++ " instead.")) where correct = apply_soterm_r1 == expected; expected = read "f1[1](x0)"::SOMetaterm

apply_soterm_f2 :: SOMetatermF
apply_soterm_f2 = read "F1[2]{f1[2][0,0],f2[1][0]}"

apply_soterm_t2 :: SOMetaterm
apply_soterm_t2 = read "f2[1](f3[0]())"

apply_soterm_r2 :: SOMetaterm
apply_soterm_r2 = apply_soterm_f2 *$ [apply_soterm_t2]

apply_soterm2 :: AutomatedTest
apply_soterm2 = AT ("Applying s.o. term " ++ (show apply_soterm_f2) ++ " to term " ++ (show apply_soterm_t2) ++ ".") (ATR correct (if correct then "Result correct." else "Result incorrect. Expected " ++ (show expected) ++ " but obtained " ++ (show apply_soterm_r2) ++ " instead.")) where correct = apply_soterm_r2 == expected; expected = read "F1[2](f1[2](f2[1](f3[0]()),f2[1](f3[0]())),f2[1](f2[1](f3[0]())))" :: SOMetaterm

apply_soterm_f3 :: SOMetatermF
apply_soterm_f3 = read "pi1[3]"

apply_soterm_t3_1 :: SOMetaterm
apply_soterm_t3_1 = read "x0"

apply_soterm_t3_2 :: SOMetaterm
apply_soterm_t3_2 = read "x1"

apply_soterm_t3_3 :: SOMetaterm
apply_soterm_t3_3 = read "x2"

apply_soterm_r3 :: SOMetaterm
apply_soterm_r3 = apply_soterm_f3 *$ [apply_soterm_t3_1, apply_soterm_t3_2, apply_soterm_t3_3]

apply_soterm3 :: AutomatedTest
apply_soterm3 = AT ("Applying s.o. term " ++ (show apply_soterm_f3) ++ " to terms " ++ (show [apply_soterm_t3_1, apply_soterm_t3_2, apply_soterm_t3_3]) ++ ".") (ATR correct (if correct then "Result correct." else ("Result incorrect. Expected " ++ (show expected) ++ " but obtained " ++ (show apply_soterm_r3) ++ " instead."))) where correct = apply_soterm_r3 == expected; expected = read "x1" :: SOMetaterm

apply_soterm_f4 :: SOMetatermF
apply_soterm_f4 = read "(\\x -> f1[1](f2[0]()))[1]"

apply_soterm_t4 :: SOMetaterm
apply_soterm_t4 = read "f5[2](x0,x1)"

apply_soterm_r4 :: SOMetaterm
apply_soterm_r4 = apply_soterm_f4 *$ [apply_soterm_t4]

apply_soterm4 :: AutomatedTest
apply_soterm4 = AT ("Applying s.o. term " ++ (show apply_soterm_f4) ++ " to term " ++ (show apply_soterm_t4) ++ ".") (ATR correct (if correct then "Result correct." else ("Result incorrect. Expected " ++ (show expected) ++ " but obtained " ++ (show apply_soterm_r4) ++ " instead."))) where correct = apply_soterm_r4 == expected; expected = read "f1[1](f2[0]())" :: SOMetaterm

apply_soterm_f5 :: SOMetaatomP
apply_soterm_f5 = read "(\\z -> p1[0]())[2]"

apply_soterm_t5 :: SOMetaterm
apply_soterm_t5 = read "f5[2](x0,x1)"

apply_soterm_r5 :: SOMetaatom
apply_soterm_r5 = apply_soterm_f5 **$ [apply_soterm_t5, apply_soterm_t5]

apply_soterm5 :: AutomatedTest
apply_soterm5 = AT ("Applying s.o. term " ++ (show apply_soterm_f5) ++ " to terms " ++ (show [apply_soterm_t5, apply_soterm_t5]) ++ ".") (ATR correct (if correct then "Result correct." else ("Result incorrect. Expected " ++ (show expected) ++ " but obtained " ++ (show apply_soterm_r5) ++ " instead."))) where correct = apply_soterm_r5 == expected; expected = read "p1[0]()" :: SOMetaatom

apply_soterm_f6 :: SOMetaatomP
apply_soterm_f6 = read "P1[3]{pi1[2][1,1],f1[1]{(\\x -> f2[0]())[2][1,0]}[1,0],F2[1]{F3[2][0,1]}[1,0]}"

apply_soterm_t6_1 :: SOMetaterm
apply_soterm_t6_1 = read "x0"

apply_soterm_t6_2 :: SOMetaterm
apply_soterm_t6_2 = read "f3[3]{f1[1][0],f2[0][],F2[1]{F2[1][0]}[0]}(f1[1](f2[0]()))"

apply_soterm_r6 :: SOMetaatom
apply_soterm_r6 = apply_soterm_f6 **$ [apply_soterm_t6_1, apply_soterm_t6_2]

apply_soterm6 :: AutomatedTest
apply_soterm6 = AT ("Applying s.o. term " ++ (show apply_soterm_f6) ++ " to terms " ++ (show [apply_soterm_t6_1, apply_soterm_t6_2]) ++ ".") (ATR correct (if correct then "Result correct." else ("Result incorrect. Expected " ++ (show expected) ++ " but obtained " ++ (show apply_soterm_r6) ++ " instead."))) where correct = apply_soterm_r6 == expected; expected = read "P1[3](f3[3](f1[1](f1[1](f2[0]())),f2[0](),F2[1](F2[1](f1[1](f2[0]())))),f1[1](f2[0]()),F2[1](F3[2](f3[3](f1[1](f1[1](f2[0]())),f2[0](),F2[1](F2[1](f1[1](f2[0]())))),x0)))" :: SOMetaatom

apply_soterm_f7 :: SOMetatermF
apply_soterm_f7 = read "f1[2]"

apply_soterm_s7_1 :: SOMetatermF
apply_soterm_s7_1 = read "f2[1]"

apply_soterm_am7_1 :: ArgumentMap
apply_soterm_am7_1 = [0]

apply_soterm_s7_2 :: SOMetatermF
apply_soterm_s7_2 = read "f2[1]"

apply_soterm_am7_2 :: ArgumentMap
apply_soterm_am7_2 = [1]

apply_soterm_r7 :: SOMetatermF
apply_soterm_r7 = apply_soterm_f7 *. [(apply_soterm_s7_1, apply_soterm_am7_1), (apply_soterm_s7_2, apply_soterm_am7_2)]

apply_soterm7 :: AutomatedTest
apply_soterm7 = AT ("Composing s.o. term " ++ (show apply_soterm_f7) ++ " with s.o. terms " ++ (show [(apply_soterm_s7_1, apply_soterm_am7_1), (apply_soterm_s7_2, apply_soterm_am7_2)]) ++ ".") (ATR correct (if correct then "Result correct." else ("Result incorrect. Expected " ++  (show expected) ++ " but obtained " ++ (show apply_soterm_r7) ++ " instead."))) where correct = apply_soterm_r7 == expected; expected = read "f1[2]{f2[1][0],f2[1][1]}" :: SOMetatermF

apply_soterm_f8 :: SOMetatermF
apply_soterm_f8 = read "f1[2]"

apply_soterm_s8_1 :: SOMetatermF
apply_soterm_s8_1 = read "f2[1]{f2[1][0]}"

apply_soterm_am8_1 :: ArgumentMap
apply_soterm_am8_1 = [0]

apply_soterm_s8_2 :: SOMetatermF
apply_soterm_s8_2 = read "f3[1]{f3[1][0]}"

apply_soterm_am8_2 :: ArgumentMap
apply_soterm_am8_2 = [1]

apply_soterm_r8 :: SOMetatermF
apply_soterm_r8 = apply_soterm_f8 *. [(apply_soterm_s8_1, apply_soterm_am8_1), (apply_soterm_s8_2, apply_soterm_am8_2)]

apply_soterm8 :: AutomatedTest
apply_soterm8 = AT ("Composing s.o. term " ++ (show apply_soterm_f8) ++ " with s.o. terms " ++ (show [(apply_soterm_s8_1, apply_soterm_am8_1), (apply_soterm_s8_2, apply_soterm_am8_2)]) ++ ".") (ATR correct (if correct then "Result correct." else ("Result incorrect. Expected " ++ (show expected) ++ " but obtained " ++ (show apply_soterm_r8) ++ " instead."))) where correct = apply_soterm_r8 == expected; expected = read "f1[2]{f2[1]{f2[1][0]}[0],f3[1]{f3[1][0]}[1]}" :: SOMetatermF

apply_soterm_f9 :: SOMetatermF
apply_soterm_f9 = read "f2[1]{f1[3][0,1,1]}"

apply_soterm_s9_1 :: SOMetatermF
apply_soterm_s9_1 = read "f2[1]"

apply_soterm_am9_1 :: ArgumentMap
apply_soterm_am9_1 = [4]

apply_soterm_s9_2 :: SOMetatermF
apply_soterm_s9_2 = read "f2[1]"

apply_soterm_am9_2 :: ArgumentMap
apply_soterm_am9_2 = [0]

apply_soterm_r9 :: SOMetatermF
apply_soterm_r9 = apply_soterm_f9 *. [(apply_soterm_s9_1, apply_soterm_am9_1), (apply_soterm_s9_2, apply_soterm_am9_2)]

apply_soterm9 :: AutomatedTest
apply_soterm9 = AT ("Composing s.o. term " ++ (show apply_soterm_f9) ++ " with s.o. terms " ++ (show [(apply_soterm_s9_1, apply_soterm_am9_1), (apply_soterm_s9_2, apply_soterm_am9_2)]) ++ ".") (ATR correct (if correct then "Result correct." else ("Result incorrect. Expected " ++ (show expected) ++ " but obtained " ++ (show apply_soterm_r9) ++ " instead."))) where correct = apply_soterm_r9 == expected; expected = read "f2[1]{f1[3]{f2[1][4],f2[1][0],f2[1][0]}[0,1,2,3,4]}" :: SOMetatermF

apply_soterm_f10 :: SOMetatermF
apply_soterm_f10 = read "f2[1]{f1[3][0,1,1]}"

apply_soterm_s10_1 :: SOMetatermF
apply_soterm_s10_1 = read "f2[1]{f2[1][0]}"

apply_soterm_am10_1 :: ArgumentMap
apply_soterm_am10_1 = [1]

apply_soterm_s10_2 :: SOMetatermF
apply_soterm_s10_2 = read "f2[1]{f2[1][2]}"

apply_soterm_am10_2 :: ArgumentMap
apply_soterm_am10_2 = [0,0,0]

apply_soterm_r10 :: SOMetatermF
apply_soterm_r10 = apply_soterm_f10 *. [(apply_soterm_s10_1, apply_soterm_am10_1), (apply_soterm_s10_2, apply_soterm_am10_2)]

apply_soterm10 :: AutomatedTest
apply_soterm10 = AT ("Composing s.o. term " ++ (show apply_soterm_f10) ++ " with s.o. terms " ++ (show [(apply_soterm_s10_1, apply_soterm_am10_1), (apply_soterm_s10_2, apply_soterm_am10_2)]) ++ ".") (ATR correct (if correct then "Result correct." else ("Result incorrect. Expected " ++ (show expected) ++ " but obtained " ++ (show apply_soterm_r10) ++ " instead."))) where correct = apply_soterm_r10 == expected; expected = read "f2[1]{f1[3]{f2[1]{f2[1][0]}[1],f2[1]{f2[1][2]}[0,0,0],f2[1]{f2[1][2]}[0,0,0]}[0,1]}" :: SOMetatermF

apply_soterm_f11 :: SOMetatermF
apply_soterm_f11 = read "f1[1]{f2[1][1]}"

apply_soterm_s11_1 :: SOMetatermF
apply_soterm_s11_1 = read "f1[1]"

apply_soterm_am11_1 :: ArgumentMap
apply_soterm_am11_1 = [4]

apply_soterm_s11_2 :: SOMetatermF
apply_soterm_s11_2 = read "(\\x -> f3[2](f4[0](),f1[1](f4[0]())))[3]"

apply_soterm_am11_2 :: ArgumentMap
apply_soterm_am11_2 = [0,3,2]

apply_soterm_r11 :: SOMetatermF
apply_soterm_r11 = apply_soterm_f11 *. [(apply_soterm_s11_1, apply_soterm_am11_1), (apply_soterm_s11_2, apply_soterm_am11_2)]

apply_soterm11 :: AutomatedTest
apply_soterm11 = AT ("Composing s.o. term " ++ (show apply_soterm_f11) ++ " with s.o. terms " ++ (show [(apply_soterm_s11_1, apply_soterm_am11_1), (apply_soterm_s11_2, apply_soterm_am11_2)]) ++ ".") (ATR correct (if correct then "Result correct." else ("Result incorrect. Expected " ++ (show expected) ++ " but obtained " ++ (show apply_soterm_r11) ++ " instead."))) where correct = apply_soterm_r11 == expected; expected = read "f1[1]{f2[1]{(\\x -> f3[2](f4[0](),f1[1](f4[0]())))[3][0,3,2]}[0,1,2,3,4]}" :: SOMetatermF

apply_soterm_f12 :: SOMetatermF
apply_soterm_f12 = read "(\\x -> f1[2](f2[0](),f3[1](f2[0]())))[1]"

apply_soterm_s12_1 :: SOMetatermF
apply_soterm_s12_1 = read "f1[2]"

apply_soterm_am12_1 :: ArgumentMap
apply_soterm_am12_1 = [3,1]

apply_soterm_s12_2 :: SOMetatermF
apply_soterm_s12_2 = read "(\\x -> f2[0]())[2]"

apply_soterm_am12_2 :: ArgumentMap
apply_soterm_am12_2 = [0,0]

apply_soterm_r12 :: SOMetatermF
apply_soterm_r12 = apply_soterm_f12 *. [(apply_soterm_s12_1, apply_soterm_am12_1), (apply_soterm_s12_2, apply_soterm_am12_2)]

apply_soterm12 :: AutomatedTest
apply_soterm12 = AT ("Composing s.o. term " ++ (show apply_soterm_f12) ++ " with s.o. terms " ++ (show [(apply_soterm_s12_1, apply_soterm_am12_1), (apply_soterm_s12_2, apply_soterm_am12_2)]) ++ ".") (ATR correct (if correct then "Result correct." else ("Result incorrect. Expected " ++ (show expected) ++ " but obtained " ++ (show apply_soterm_r12) ++ " instead."))) where correct = apply_soterm_r12 == expected; expected = read "(\\x -> f1[2](f2[0](),f3[1](f2[0]())))[4]"

apply_soterm_f13 :: SOMetatermF
apply_soterm_f13 = read "f1[2]"

apply_soterm_s13_1 :: SOMetatermF
apply_soterm_s13_1 = read "pi2[3]"

apply_soterm_am13_1 :: ArgumentMap
apply_soterm_am13_1 = [1,3,5]

apply_soterm_s13_2 :: SOMetatermF
apply_soterm_s13_2 = read "pi0[2]"

apply_soterm_am13_2 :: ArgumentMap
apply_soterm_am13_2 = [1,0]

apply_soterm_r13 :: SOMetatermF
apply_soterm_r13 = apply_soterm_f13 *. [(apply_soterm_s13_1, apply_soterm_am13_1), (apply_soterm_s13_2, apply_soterm_am13_2)]

apply_soterm13 :: AutomatedTest
apply_soterm13 = AT ("Composing s.o. term " ++ (show apply_soterm_f13) ++ " with s.o. terms " ++ (show [(apply_soterm_s13_1, apply_soterm_am13_1), (apply_soterm_s13_2, apply_soterm_am13_2)]) ++ ".") (ATR correct (if correct then "Result correct." else ("Result incorrect. Expected " ++ (show expected) ++ " but obtained " ++ (show apply_soterm_r13) ++ " instead."))) where correct = apply_soterm_r13 == expected; expected = read "f1[2]{pi2[3][1,3,5],pi0[2][1,0]}"

apply_soterm_f14 :: SOMetatermF
apply_soterm_f14 = read "pi1[3]"

apply_soterm_s14_1 :: SOMetatermF
apply_soterm_s14_1 = read "f1[0]"

apply_soterm_am14_1 :: ArgumentMap
apply_soterm_am14_1 = []

apply_soterm_s14_2 :: SOMetatermF
apply_soterm_s14_2 = read "f2[1]{f2[1][1]}"

apply_soterm_am14_2 :: ArgumentMap
apply_soterm_am14_2 = [1,2]

apply_soterm_s14_3 :: SOMetatermF
apply_soterm_s14_3 = read "pi3[7]"

apply_soterm_am14_3 :: ArgumentMap
apply_soterm_am14_3 = [0,1,2,3,4,5,6]

apply_soterm_r14 :: SOMetatermF
apply_soterm_r14 = apply_soterm_f14 *. [(apply_soterm_s14_1, apply_soterm_am14_1), (apply_soterm_s14_2, apply_soterm_am14_2), (apply_soterm_s14_3, apply_soterm_am14_3)]

apply_soterm14 :: AutomatedTest
apply_soterm14 = AT ("Composing s.o. term " ++ (show apply_soterm_f14) ++ " with s.o. terms " ++ (show [(apply_soterm_s14_1, apply_soterm_am14_1), (apply_soterm_s14_2, apply_soterm_am14_2), (apply_soterm_s14_3, apply_soterm_am14_3)]) ++ ".") (ATR correct (if correct then "Result correct." else ("Result incorrect. Expected " ++ (show expected) ++ " but obtained " ++ (show apply_soterm_r14) ++  " instead."))) where correct = apply_soterm_r14 == expected; expected = read "f2[1]{f2[1][2]}"

apply_soterm_f15 :: SOMetatermF
apply_soterm_f15 = read "pi1[2]"

apply_soterm_s15_1 :: SOMetatermF
apply_soterm_s15_1 = read "f1[1]"

apply_soterm_am15_1 :: ArgumentMap
apply_soterm_am15_1 = [156]

apply_soterm_s15_2 :: SOMetatermF
apply_soterm_s15_2 = read "pi4[5]"

apply_soterm_am15_2 :: ArgumentMap
apply_soterm_am15_2 = [0,2,1,0,1]

apply_soterm_r15 :: SOMetatermF
apply_soterm_r15 = apply_soterm_f15 *. [(apply_soterm_s15_1, apply_soterm_am15_1), (apply_soterm_s15_2, apply_soterm_am15_2)]

apply_soterm15 :: AutomatedTest
apply_soterm15 = AT ("Composing s.o. term " ++ (show apply_soterm_f15) ++ " with s.o. terms " ++ (show [(apply_soterm_s15_1, apply_soterm_am15_1), (apply_soterm_s15_2, apply_soterm_am15_2)]) ++ ".") (ATR correct (if correct then "Result correct." else ("Result incorrect. Expected " ++ (show expected) ++ " but obtained " ++ (show apply_soterm_r15) ++ " instead."))) where correct = apply_soterm_r15 == expected; expected = read "pi1[157]"

apply_soterm_f16 :: SOMetatermF
apply_soterm_f16 = read "pi0[1]"

apply_soterm_s16_1 :: SOMetatermF
apply_soterm_s16_1 = read "f1[1]{pi1[2][0,1]}"

apply_soterm_am16_1 :: ArgumentMap
apply_soterm_am16_1 = [4,3]

apply_soterm_r16 :: SOMetatermF
apply_soterm_r16 = apply_soterm_f16 *. [(apply_soterm_s16_1, apply_soterm_am16_1)]

apply_soterm16 :: AutomatedTest
apply_soterm16 = AT ("Composing s.o. term " ++ (show apply_soterm_f16) ++ " with s.o. terms " ++ (show [(apply_soterm_s16_1, apply_soterm_am16_1)]) ++ ".") (ATR correct (if correct then "Result correct." else ("Result incorrect. Expected " ++ (show expected) ++ " but obtained " ++ (show apply_soterm_r16) ++ " instead."))) where correct = apply_soterm_r16 == expected; expected = read "f1[1]{pi3[5][0,1,2,3,4]}"

apply_soterm_f17 :: SOMetaatomP
apply_soterm_f17 = read "p1[2]{f1[1][2],pi0[3][0,1,2]}"

apply_soterm_s17_1 :: SOMetatermF
apply_soterm_s17_1 = read "f1[1]{f2[0][]}"

apply_soterm_am17_1 :: ArgumentMap
apply_soterm_am17_1 = []

apply_soterm_s17_2 :: SOMetatermF
apply_soterm_s17_2 = read "f134[2]"

apply_soterm_am17_2 :: ArgumentMap
apply_soterm_am17_2 = [4,1]

apply_soterm_s17_3 :: SOMetatermF
apply_soterm_s17_3 = read "f1[1]{f1[1][0]}"

apply_soterm_am17_3 :: ArgumentMap
apply_soterm_am17_3 = [1]

apply_soterm_r17 :: SOMetaatomP
apply_soterm_r17 = apply_soterm_f17 **. [(apply_soterm_s17_1, apply_soterm_am17_1), (apply_soterm_s17_2, apply_soterm_am17_2), (apply_soterm_s17_3, apply_soterm_am17_3)]

apply_soterm17 :: AutomatedTest
apply_soterm17 = AT ("Composing s.o. term " ++ (show apply_soterm_f17) ++ " with s.o. terms " ++ (show [(apply_soterm_s17_1, apply_soterm_am17_1)]) ++ ".") (ATR correct (if correct then "Result correct." else ("Result incorrect. Expected " ++ (show expected) ++ " but obtained " ++ (show apply_soterm_r17) ++ " instead."))) where correct = apply_soterm_r17 == expected; expected = read "p1[2]{f1[1]{f1[1]{f1[1][0]}[1]}[0,1,2,3,4],f1[1]{f2[0][]}[0,1,2,3,4]}"





apply_soterm_tests :: [AutomatedTest]
apply_soterm_tests = [apply_soterm1, apply_soterm2, apply_soterm3, apply_soterm4, apply_soterm5, apply_soterm6, apply_soterm7, apply_soterm8, apply_soterm9, apply_soterm10, apply_soterm11, apply_soterm12, apply_soterm13, apply_soterm14, apply_soterm15, apply_soterm16, apply_soterm17]

apply_soterm_test :: IO ()
apply_soterm_test = putStr (combine_test_results apply_soterm_tests)



all_test :: IO ()
all_test = (putStr "\n\nSECOND-ORDER TERM PARSING TESTS\n\n") >> parse_soterm_test >>
		(putStr "\n\nSECOND-ORDER TERM APPLICATION AND COMPOSITION TESTS\n\n") >> apply_soterm_test

