{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE FlexibleContexts #-}

module ObjectLogicTests where

import ObjectLogic
import AutoTests
import Control.Unification
import Syntax
import Data.Maybe

-- Testing parsing of terms
parse_term_str1 :: String
parse_term_str1 = "x0"

parse_term_term1 :: Term
parse_term_term1 = read parse_term_str1

parse_term1 :: AutomatedTest
parse_term1 = AT "Parsing 'x0'" (ATR correct (if correct then "Parsing correct." else ("Parsing incorrect. Expected 'x0' but was '" ++ (show parse_term1) ++ "' instead."))) where correct = (parse_term_term1 == UVar (OVar 0))

parse_term_str2 :: String
parse_term_str2 = "f1[0]()"

parse_term_term2 :: Term
parse_term_term2 = read parse_term_str2

parse_term2 :: AutomatedTest
parse_term2 = AT "Parsing 'f1[0]()'" (ATR correct (if correct then "Parsing correct." else ("Parsing incorrect. Expected 'f1[0]()' but was '" ++ (show parse_term2) ++ "' instead."))) where correct = (parse_term_term2 == UTerm (TFun (OFun 1 0) []))

parse_term_str3 :: String
parse_term_str3 = "f2[2](x0,x1)"

parse_term_term3 :: Term
parse_term_term3 = read parse_term_str3

parse_term3 :: AutomatedTest
parse_term3 = AT "Parsing 'f2[2](x0,x1)'" (ATR correct (if correct then "Parsing correct." else ("Parsing incorrect. Expected 'f2[2](x0,x1)' but was '" ++ (show parse_term3) ++ "' instead."))) where correct = (parse_term_term3 == UTerm (TFun (OFun 2 2) [UVar (OVar 0), UVar (OVar 1)]))

parse_term_str4 :: String
parse_term_str4 = "f2[2](f3[1](x0),f2[2](x1,f3[1](f1[0]())))"

parse_term_term4 :: Term
parse_term_term4 = read parse_term_str4

parse_term4 :: AutomatedTest
parse_term4 = AT "Parsing 'f2[2](f3[1](x0),f2[2](x1,f3[1](f1[0]())))'" (ATR correct (if correct then "Parsing correct." else ("Parsing incorrect. Expected 'f2[2](f3[1](x0),f2[2](x1,f3[1](f1[0]())))' but was '" ++ (show parse_term4) ++ "' instead."))) where correct = (parse_term_term4 == UTerm (TFun (OFun 2 2) [UTerm (TFun (OFun 3 1) [UVar (OVar 0)]),UTerm (TFun (OFun 2 2) [UVar (OVar 1),UTerm (TFun (OFun 3 1) [UTerm (TFun (OFun 1 0) [])])])]))

parse_term_tests :: [AutomatedTest]
parse_term_tests = [parse_term1,parse_term2,parse_term3,parse_term4]

parse_term_test :: IO ()
parse_term_test = putStr (combine_test_results parse_term_tests)

parse_atom_str1 :: String
parse_atom_str1 = "x0"

parse_atom_atom1 :: Atom
parse_atom_atom1 = read parse_atom_str1

parse_atom1 :: AutomatedTest
parse_atom1 = AT "Parsing 'x0'" (ATR correct (if correct then "Parsing correct." else ("Parsing incorrect. Expected 'x0' but was '" ++ (show parse_atom1) ++ "' instead."))) where correct = (parse_atom_atom1 == Term (UVar (OVar 0)))

parse_atom_str2 :: String
parse_atom_str2 = "f2[2](f3[1](x0),f2[2](x1,f3[1](f1[0]())))"

parse_atom_atom2 :: Atom
parse_atom_atom2 = read parse_atom_str2

parse_atom2 :: AutomatedTest
parse_atom2 = AT "Parsing 'f2[2](f3[1](x0),f2[2](x1,f3[1](f1[0]())))'" (ATR correct (if correct then "Parsing correct." else ("Parsing incorrect. Expected 'f2[2](f3[1](x0),f2[2](x1,f3[1](f1[0]())))' but was '" ++ (show parse_atom2) ++ "' instead."))) where correct = (parse_atom_atom2 == Term (UTerm (TFun (OFun 2 2) [UTerm (TFun (OFun 3 1) [UVar (OVar 0)]),UTerm (TFun (OFun 2 2) [UVar (OVar 1),UTerm (TFun (OFun 3 1) [UTerm (TFun (OFun 1 0) [])])])])))

parse_atom_str3 :: String
parse_atom_str3 = "p1[0]()"

parse_atom_atom3 :: Atom
parse_atom_atom3 = read parse_atom_str3

parse_atom3 :: AutomatedTest
parse_atom3 = AT "Parsing 'p1[0]()'" (ATR correct (if correct then "Parsing correct." else ("Parsing incorrect. Expected 'p1[0]()' but was '" ++ (show parse_atom3) ++ "' instead."))) where correct = (parse_atom_atom3 == Atom (APred (OPred 1 0) []))

parse_atom_str4 :: String
parse_atom_str4 = "p2[2](x0,f1[1](x1))"

parse_atom_atom4 :: Atom
parse_atom_atom4 = read parse_atom_str4

parse_atom4 :: AutomatedTest
parse_atom4 = AT "Parsing 'p2[2](x0,f1[1](x1))'" (ATR correct (if correct then "Parsing correct." else ("Parsing incorrect. Expected 'p2[2](x0,f1[1](x1))' but was '" ++ (show parse_atom4) ++ "' instead."))) where correct = (parse_atom_atom4 == Atom (APred (OPred 2 2) [UVar (OVar 0),UTerm (TFun (OFun 1 1) [UVar (OVar 1)])]))

parse_atom_tests :: [AutomatedTest]
parse_atom_tests = [parse_atom1,parse_atom2,parse_atom3,parse_atom4]

parse_atom_test :: IO ()
parse_atom_test = putStr (combine_test_results parse_atom_tests)


-- Unification tests
unif_x0 :: OVariable
unif_x0 = OVar 0

unif_x1 :: OVariable
unif_x1 = OVar 1

unif_x2 :: OVariable
unif_x2 = OVar 2

unif_x3 :: OVariable
unif_x3 = OVar 3

unif_tx0 :: Term
unif_tx0 = UVar (unif_x0)

unif_tx1 :: Term
unif_tx1 = UVar (unif_x1)

unif_tx2 :: Term
unif_tx2 = UVar (unif_x2)

unif_tx3 :: Term
unif_tx3 = UVar (unif_x3)


-- Check that the unification was successful, and that it unifies or does not unify two particular terms.
unif_test_term :: (SimplyUnifiable CTermFn OVariable u) => u -> Term -> Term -> Bool -> AutomatedTestResult
unif_test_term u t1 t2 r = if successful then
				(if r then 
					(if equals then (ATR True "The terms correctly unify.")
					else (ATR False ("The terms " ++ (show t1) ++ " and " ++ (show t2) ++  " should unify under this unifier, but when applied, it yields " ++ (show (fromJust result1)) ++ " and " ++ (show (fromJust result2)) ++ " respectively.")))
				else
					(if equals then (ATR False ("The terms " ++ (show t1) ++ " and " ++ (show t2) ++ " should not unify under this unifier, but they do."))
					else (ATR True "The terms do not unify, as expected.")))
			else (ATR False "The unification was not successful.")
		where result1 = u $:= t1; result2 = u $:= t2; successful = (isJust result1) && (isJust result2); equals = (fromJust result1) == (fromJust result2)

unif_test_term_fail :: (SimplyUnifiable CTermFn OVariable u) => u -> Term -> Term -> AutomatedTestResult
unif_test_term_fail u t1 t2 = if (s1 || s2) then
				(ATR False ("The unification seems to succeed. When applied to " ++ (show t1) ++ " it yields " ++ (show (u $:= t1)) ++ ", and when applied to " ++ (show t2) ++ " it yields " ++ (show (u $:= t2))))
				else (ATR True "The unification failed, as expected.")
	where s1 = isJust (u $:= t1); s2 = isJust (u $:= t2)




unif_term1_t1 :: Term
unif_term1_t1 = read "f1[0]()"

unif_term1_t2 :: Term
unif_term1_t2 = read "f1[0]()"

unif_unif1 :: TermUnifier
unif_unif1 = unif_term1_t1 =.= unif_term1_t2

unif1_1 :: AutomatedTest
unif1_1 = AT "Unifying f1[0]() with f1[0]()" (unif_test_term unif_unif1 unif_tx0 unif_tx1 False)

unif1_2 :: AutomatedTest
unif1_2 = AT "Unifying f1[0]() with f1[0]()" (unif_test_term unif_unif1 unif_tx0 unif_tx0 True)


unif_term2_t1 :: Term
unif_term2_t1 = read "f1[1](x0)"

unif_term2_t2 :: Term
unif_term2_t2 = read "f1[1](x0)"

unif_unif2 :: TermUnifier
unif_unif2 = unif_term2_t1 =.= unif_term2_t2

unif2_1 :: AutomatedTest
unif2_1 = AT "Unifying f1[1](x0) with f1[1](x0)" (unif_test_term unif_unif2 unif_tx0 unif_tx1 False)

unif2_2 :: AutomatedTest
unif2_2 = AT "Unifying f1[1](x0) with f1[1](x0)" (unif_test_term unif_unif2 unif_tx0 unif_tx0 True)


unif_term3_t1 :: Term
unif_term3_t1 = read "f1[1](x0)"

unif_term3_t2 :: Term
unif_term3_t2 = read "f1[1](x1)"

unif_unif3 :: TermUnifier
unif_unif3 = unif_term3_t1 =.= unif_term3_t2

unif3_1 :: AutomatedTest
unif3_1 = AT "Unifying f1[1](x0) with f1[1](x1)" (unif_test_term unif_unif3 unif_tx0 unif_tx1 True)

unif3_2 :: AutomatedTest
unif3_2 = AT "Unifying f1[1](x0) with f1[1](x1)" (unif_test_term unif_unif3 unif_tx0 unif_tx0 True)

unif3_3 :: AutomatedTest
unif3_3 = AT "Unifying f1[1](x0) with f1[1](x1)" (unif_test_term unif_unif3 unif_tx0 unif_tx2 False)


unif_term4_t1 :: Term
unif_term4_t1 = read "f1[2](x0,x1)"

unif_term4_t2 :: Term
unif_term4_t2 = read "f1[2](x0,x1)"

unif_unif4 :: TermUnifier
unif_unif4 = unif_term4_t1 =.= unif_term4_t2

unif4_1 :: AutomatedTest
unif4_1 = AT "Unifying f1[2](x0,x1) with f1[2](x0,x1)" (unif_test_term unif_unif4 unif_tx0 unif_tx1 False)

unif4_2 :: AutomatedTest
unif4_2 = AT "Unifying f1[2](x0,x1) with f1[2](x0,x1)" (unif_test_term unif_unif4 unif_tx0 unif_tx0 True)


unif_term5_t1 :: Term
unif_term5_t1 = read "f1[2](x0,x1)"

unif_term5_t2 :: Term
unif_term5_t2 = read "f1[2](x1,x0)"

unif_unif5 :: TermUnifier
unif_unif5 = unif_term5_t1 =.= unif_term5_t2

unif5_1 :: AutomatedTest
unif5_1 = AT "Unifying f1[2](x0,x1) with f1[2](x1,x0)" (unif_test_term unif_unif5 unif_tx0 unif_tx1 True)

unif5_2 :: AutomatedTest
unif5_2 = AT "Unifying f1[2](x0,x1) with f1[2](x1,x0)" (unif_test_term unif_unif5 unif_tx0 unif_tx0 True)

unif5_3 :: AutomatedTest
unif5_3 = AT "Unifying f1[2](x0,x1) with f1[2](x1,x0)" (unif_test_term unif_unif5 unif_tx0 unif_tx2 False) 


unif_term6_t1 :: Term
unif_term6_t1 = read "f1[0]()"

unif_term6_t2 :: Term
unif_term6_t2 = read "f2[0]()"

unif_unif6 :: TermUnifier
unif_unif6 = unif_term6_t1 =.= unif_term6_t2

unif6_1 :: AutomatedTest
unif6_1 = AT "Unifying f1[0]() with f2[0]()" (unif_test_term_fail unif_unif6 unif_term6_t1 unif_term6_t2)


unif_term7_t1 :: Term
unif_term7_t1 = read "f1[1](f2[0]())"

unif_term7_t2 :: Term
unif_term7_t2 = read "f1[1](x0)"

unif_unif7 :: TermUnifier
unif_unif7 = unif_term7_t1 =.= unif_term7_t2

unif7_1 :: AutomatedTest
unif7_1 = AT "Unifying f1[1](f2[0]()) with f1[1](x0)" (unif_test_term unif_unif7 unif_tx0 (read "f2[0]()") True)

unif7_2 :: AutomatedTest
unif7_2 = AT "Unifying f1[1](f2[0]()) with f1[1](x0)" (unif_test_term unif_unif7 unif_tx0 unif_tx1 False)

unif7_3 :: AutomatedTest
unif7_3 = AT "Unifying f1[1](f2[0]()) with f1[1](x0)" (unif_test_term unif_unif7 unif_tx0 unif_tx0 True)


unif_term8_t1 :: Term
unif_term8_t1 = read "f1[2](x0,x1)"

unif_term8_t2 :: Term
unif_term8_t2 = read "f1[2](x1,x2)"

unif_unif8 :: TermUnifier
unif_unif8 = unif_term8_t1 =.= unif_term8_t2

unif8_1 :: AutomatedTest
unif8_1 = AT "Unifying f1[2](x0,x1) with f1[2](x1,x2)" (unif_test_term unif_unif8 unif_tx0 unif_tx1 True)

unif8_2 :: AutomatedTest
unif8_2 = AT "Unifying f1[2](x0,x1) with f1[2](x1,x2)" (unif_test_term unif_unif8 unif_tx1 unif_tx2 True)

unif8_3 :: AutomatedTest
unif8_3 = AT "Unifying f1[2](x0,x1) with f1[2](x1,x2)" (unif_test_term unif_unif8 unif_tx2 unif_tx0 True)

unif8_4 :: AutomatedTest
unif8_4 = AT "Unifying f1[2](x0,x1) with f1[2](x1,x2)" (unif_test_term unif_unif8 unif_tx0 unif_tx0 True)


unif_term9_t1 :: Term
unif_term9_t1 = read "f1[2](x0,x1)"

unif_term9_t2 :: Term
unif_term9_t2 = read "f1[2](x1,f2[0]())"

unif_unif9 :: TermUnifier
unif_unif9 = unif_term9_t1 =.= unif_term9_t2

unif9_1 :: AutomatedTest
unif9_1 = AT "Unifying f1[2](x0,x1) with f1[2](x1,f2[0]())" (unif_test_term unif_unif9 unif_tx0 unif_tx1 True)

unif9_2 :: AutomatedTest
unif9_2 = AT "Unifying f1[2](x0,x1) with f1[2](x1,f2[0]())" (unif_test_term unif_unif9 unif_tx1 (read "f2[0]()") True)

unif9_3 :: AutomatedTest
unif9_3 = AT "Unifying f1[2](x0,x1) with f1[2](x1,f2[0]())" (unif_test_term unif_unif9 unif_tx0 (read "f2[0]()") True)

unif9_4 :: AutomatedTest
unif9_4 = AT "Unifying f1[2](x0,x1) with f1[2](x1,f2[0]())" (unif_test_term unif_unif9 unif_tx0 unif_tx2 False)


unif_term10_t1 :: Term
unif_term10_t1 = read "f1[2](x0,x0)"

unif_term10_t2 :: Term
unif_term10_t2 = read "f1[2](f2[0](),f3[0]())"

unif_unif10 :: TermUnifier
unif_unif10 = unif_term10_t1 =.= unif_term10_t2

unif10_1 :: AutomatedTest
unif10_1 = AT "Unifying f1[2](x0,x0) with f1[2](f2[0](),f3[0]())" (unif_test_term_fail unif_unif10 unif_term10_t1 unif_term10_t2)


unif_term11_t1 :: Term
unif_term11_t1 = read "f1[2](x0,f2[1](x0))"

unif_term11_t2 :: Term
unif_term11_t2 = read "f1[2](f2[1](x1),x1)"

unif_unif11 :: TermUnifier
unif_unif11 = unif_term11_t1 =.= unif_term11_t2

unif11_1 :: AutomatedTest
unif11_1 = AT "Unifying f1[2](x0,f2[1](x0)) with f1[2](f2[1](x1),x1)" (unif_test_term_fail unif_unif11 unif_term11_t1 unif_term11_t2)


unif_term12_t1 :: Term
unif_term12_t1 = read "x0"

unif_term12_t2 :: Term
unif_term12_t2 = read "x1"

unif_term12_t3 :: Term
unif_term12_t3 = read "f1[1](x2)"

unif_term12_t4 :: Term
unif_term12_t4 = read "f1[1](x1)"

unif_unif12 :: TermUnifier
unif_unif12 = (unif_term12_t1 =.= unif_term12_t2) >> (unif_term12_t3 =.= unif_term12_t4)

unif12_1 :: AutomatedTest
unif12_1 = AT "Unifying x0 with x1 and f1[1](x2) with f1[1](x1)" (unif_test_term unif_unif12 unif_tx1 unif_tx0 True)

unif12_2 :: AutomatedTest
unif12_2 = AT "Unifying x0 with x1 and f1[1](x2) with f1[1](x1)" (unif_test_term unif_unif12 unif_tx2 unif_tx1 True)

unif12_3 :: AutomatedTest
unif12_3 = AT "Unifying x0 with x1 and f1[1](x2) with f1[1](x1)" (unif_test_term unif_unif12 unif_tx2 unif_tx0 True)

unif12_4 :: AutomatedTest
unif12_4 = AT "Unifying x0 with x1 and f1[1](x2) with f1[1](x1)" (unif_test_term unif_unif12 unif_tx0 unif_tx0 True)

unif12_5 :: AutomatedTest
unif12_5 = AT "Unifying x0 with x1 and f1[1](x2) with f1[1](x1)" (unif_test_term unif_unif12 unif_tx0 unif_tx3 False)


unif_term13_t1 :: Term
unif_term13_t1 = read "f1[2](x0,x1)"

unif_term13_t2 :: Term
unif_term13_t2 = read "f1[2](f2[0](),x2)"

unif_term13_t3 :: Term
unif_term13_t3 = read "f3[2](x2,f4[0]())"

unif_term13_t4 :: Term
unif_term13_t4 = read "f3[2](x0,x1)"

unif_unif13 :: TermUnifier
unif_unif13 = (unif_term13_t1 =.= unif_term13_t2) >> (unif_term13_t3 =.= unif_term13_t4)

unif13_1 :: AutomatedTest
unif13_1 = AT "Unifying f1[2](x0,x1) with f1[2](f2[0](),x2) and f3[2](x2,f4[0]()) with f3[2](x0,x1)" (unif_test_term_fail unif_unif13 unif_term13_t1 unif_term13_t4)


unif_term14_t1 :: Term
unif_term14_t1 = read "f1[2](x0,x1)"

unif_term14_t2 :: Term
unif_term14_t2 = read "f1[2](f2[0](),x2)"

unif_term14_t3 :: Term
unif_term14_t3 = read "f3[2](x2,f4[0]())"

unif_term14_t4 :: Term
unif_term14_t4 = read "f3[2](x0,f4[0]())"

unif_unif14 :: TermUnifier
unif_unif14 = (unif_term14_t1 =.= unif_term14_t2) >> (unif_term14_t3 =.= unif_term14_t4)

unif14_1 :: AutomatedTest
unif14_1 = AT "Unifying f1[2](x0,x1) with f1[2](f2[0](),x2) and f3[2](x2,f4[0]()) with f3[2](x0,f4[0]())" (unif_test_term unif_unif14 unif_tx0 unif_tx1 True)

unif14_2 :: AutomatedTest
unif14_2 = AT "Unifying f1[2](x0,x1) with f1[2](f2[0](),x2) and f3[2](x2,f4[0]()) with f3[2](x0,f4[0]())" (unif_test_term unif_unif14 unif_tx2 unif_tx1 True)

unif14_3 :: AutomatedTest
unif14_3 = AT "Unifying f1[2](x0,x1) with f1[2](f2[0](),x2) and f3[2](x2,f4[0]()) with f3[2](x0,f4[0]())" (unif_test_term unif_unif14 unif_tx2 unif_tx0 True)

unif14_4 :: AutomatedTest
unif14_4 = AT "Unifying f1[2](x0,x1) with f1[2](f2[0](),x2) and f3[2](x2,f4[0]()) with f3[2](x0,f4[0]())" (unif_test_term unif_unif14 unif_tx2 (read "f2[0]()") True)

unif14_5 :: AutomatedTest
unif14_5 = AT "Unifying f1[2](x0,x1) with f1[2](f2[0](),x2) and f3[2](x2,f4[0]()) with f3[2](x0,f4[0]())" (unif_test_term unif_unif14 (read "f2[0]()") unif_tx1 True)

unif14_6 :: AutomatedTest
unif14_6 = AT "Unifying f1[2](x0,x1) with f1[2](f2[0](),x2) and f3[2](x2,f4[0]()) with f3[2](x0,f4[0]())" (unif_test_term unif_unif14 (read "f4[0]()") unif_tx0 False)

unif14_7 :: AutomatedTest
unif14_7 = AT "Unifying f1[2](x0,x1) with f1[2](f2[0](),x2) and f3[2](x2,f4[0]()) with f3[2](x0,f4[0]())" (unif_test_term unif_unif14 (read "f4[0]()") unif_tx1 False)


unif_term15_t1 :: Term
unif_term15_t1 = read "x0"

unif_term15_t2 :: Term
unif_term15_t2 = read "f1[1](x1)"

unif_term15_t3 :: Term
unif_term15_t3 = read "f1[1](x0)"

unif_term15_t4 :: Term
unif_term15_t4 = read "x1"

unif_unif15_1 :: TermUnifier
unif_unif15_1 = unif_term15_t1 =.= unif_term15_t2

unif_unif15_2 :: TermUnifier
unif_unif15_2 = unif_term15_t3 =.= unif_term15_t4

unif_unif15_3 :: TermUnifier
unif_unif15_3 = unif_unif15_1 >> unif_unif15_2

unif15_1 :: AutomatedTest
unif15_1 = AT "Unifying x0 with f1[1](x1)" (unif_test_term unif_unif15_1 unif_tx0 (read "f1[1](x1)") True)

unif15_2 :: AutomatedTest
unif15_2 = AT "Unifying f1[1](x0) with x1" (unif_test_term unif_unif15_2 (read "f1[1](x0)") unif_tx1 True)

unif15_3 :: AutomatedTest
unif15_3 = AT "Unifying x0 with f1[1](x1) and f1[1](x0) with x1" (unif_test_term_fail unif_unif15_3 unif_term15_t1 unif_term15_t4)


unif_term16_t1 :: Term
unif_term16_t1 = read "x0"

unif_term16_t2 :: Term
unif_term16_t2 = read "f1[1](x1)"

unif_term16_t3 :: Term
unif_term16_t3 = read "f1[1](x0)"

unif_term16_t4 :: Term
unif_term16_t4 = read "x2"

unif_unif16_1 :: TermUnifier
unif_unif16_1 = unif_term16_t1 =.= unif_term16_t2

unif_unif16_2 :: TermUnifier
unif_unif16_2 = unif_term16_t3 =.= unif_term16_t4

unif_unif16_3 :: TermUnifier
unif_unif16_3 = unif_unif16_1 >> unif_unif16_2

unif16_1 :: AutomatedTest
unif16_1 = AT "Unifying x0 with f1[1](x1)" (unif_test_term unif_unif16_1 unif_tx0 (read "f1[1](x1)") True)

unif16_2 :: AutomatedTest
unif16_2 = AT "Unifying x0 with f1[1](x1)" (unif_test_term unif_unif16_1 (read "f1[1](x0)") (read "f1[1](f1[1](x1))") True)

unif16_3 :: AutomatedTest
unif16_3 = AT "Unifying x0 with f1[1](x1)" (unif_test_term unif_unif16_1 (read "x2") (read "f1[1](f1[1](x1))") False)

unif16_4 :: AutomatedTest
unif16_4 = AT "Unifying f1[1](x0) with x2" (unif_test_term unif_unif16_2 unif_tx2 (read "f1[1](x0)") True)

unif16_5 :: AutomatedTest
unif16_5 = AT "Unifying f1[1](x0) with x2" (unif_test_term unif_unif16_2 (read "f1[1](x1)") unif_tx0 False)

unif16_6 :: AutomatedTest
unif16_6 = AT "Unifying f1[1](x0) with x2" (unif_test_term unif_unif16_2 (read "x2") (read "f1[1](f1[1](x1))") False)

unif16_7 :: AutomatedTest
unif16_7 = AT "Unifying x0 with f1[1](x1) and f1[1](x0) with x2" (unif_test_term unif_unif16_3 unif_tx0 (read "f1[1](x1)") True)

unif16_8 :: AutomatedTest
unif16_8 = AT "Unifying x0 with f1[1](x1) and f1[1](x0) with x2" (unif_test_term unif_unif16_3 (read "f1[1](x0)") (read "f1[1](f1[1](x1))") True)

unif16_9 :: AutomatedTest
unif16_9 = AT "Unifying x0 with f1[1](x1) and f1[1](x0) with x2" (unif_test_term unif_unif16_3 unif_tx2 (read "f1[1](x0)") True)

unif16_10 :: AutomatedTest
unif16_10 = AT "Unifying x0 with f1[1](x1) and f1[1](x0) with x2" (unif_test_term unif_unif16_3 unif_tx2 (read "f1[1](f1[1](x1))") True)

unif16_11 :: AutomatedTest
unif16_11 = AT "Unifying x0 with f1[1](x1) and f1[1](x0) with x2" (unif_test_term unif_unif16_3 unif_tx0 unif_tx1 False)

unif16_12 :: AutomatedTest
unif16_12 = AT "Unifying x0 with f1[1](x1) and f1[1](x0) with x2" (unif_test_term unif_unif16_3 unif_tx2 unif_tx1 False)

unif16_13 :: AutomatedTest
unif16_13 = AT "Unifying x0 with f1[1](x1) and f1[1](x0) with x2" (unif_test_term unif_unif16_3 unif_tx2 unif_tx0 False)


-- And now atoms. Just do the basic: One without variables, one variable to variable, one variable to term, one with multiple recursive, one with occurs check, one with incompatible terms, one with multiple iterative. (Maybe some of these are more than one to account for particularities)

unif_term17_a1 :: Atom
unif_term17_a1 = read "p1[0]()"

unif_term17_a2 :: Atom
unif_term17_a2 = read "p1[0]()"

unif_unif17 :: AtomUnifier
unif_unif17 = unif_term17_a1 =.= unif_term17_a2

unif17_1 :: AutomatedTest
unif17_1 = AT "Unifying p1[0]() with p1[0]()" (unif_test_term unif_unif17 unif_tx0 unif_tx1 False)

unif17_2 :: AutomatedTest
unif17_2 = AT "Unifying p1[0]() with p1[0]()" (unif_test_term unif_unif17 unif_tx0 unif_tx0 True)


unif_term18_a1 :: Atom
unif_term18_a1 = read "p1[0]()"

unif_term18_a2 :: Atom
unif_term18_a2 = read "p2[0]()"

unif_unif18 :: AtomUnifier
unif_unif18 = unif_term18_a1 =.= unif_term18_a2

unif18_1 :: AutomatedTest
unif18_1 = AT "Unifying p1[0]() with p2[0]()" (unif_test_term_fail unif_unif18 unif_tx0 unif_tx1)


unif_term19_a1 :: Atom
unif_term19_a1 = read "p1[1](x0)"

unif_term19_a2 :: Atom
unif_term19_a2 = read "p1[1](x1)"

unif_unif19 :: AtomUnifier
unif_unif19 = unif_term19_a1 =.= unif_term19_a2

unif19_1 :: AutomatedTest
unif19_1 = AT "Unifying p1[1](x0) with p1[1](x1)" (unif_test_term unif_unif19 unif_tx0 unif_tx1 True)

unif19_2 :: AutomatedTest
unif19_2 = AT "Unifying p1[1](x0) with p1[1](x1)" (unif_test_term unif_unif19 unif_tx0 unif_tx2 False)

unif19_3 :: AutomatedTest
unif19_3 = AT "Unifying p1[1](x0) with p1[1](x1)" (unif_test_term unif_unif19 unif_tx0 unif_tx0 True)


unif_term20_a1 :: Atom
unif_term20_a1 = read "p1[1](x0)"

unif_term20_a2 :: Atom
unif_term20_a2 = read "p1[1](f1[0]())"

unif_unif20 :: AtomUnifier
unif_unif20 = unif_term20_a1 =.= unif_term20_a2

unif20_1 :: AutomatedTest
unif20_1 = AT "Unifying p1[1](x0) with p1[1](f1[0]())" (unif_test_term unif_unif20 unif_tx0 (read "f1[0]()") True)

unif20_2 :: AutomatedTest
unif20_2 = AT "Unifying p1[1](x0) with p1[1](f1[0]())" (unif_test_term unif_unif20 unif_tx0 unif_tx1 False)

unif20_3 :: AutomatedTest
unif20_3 = AT "Unifying p1[1](x0) with p1[1](f1[0]())" (unif_test_term unif_unif20 unif_tx0 unif_tx0 True)


unif_term21_a1 :: Atom
unif_term21_a1 = read "p1[2](x0,x1)"

unif_term21_a2 :: Atom
unif_term21_a2 = read "p1[2](x1,x2)"

unif_unif21 :: AtomUnifier
unif_unif21 = unif_term21_a1 =.= unif_term21_a2

unif21_1 :: AutomatedTest
unif21_1 = AT "Unifying p1[2](x0,x1) with p1[2](x1,x2)" (unif_test_term unif_unif21 unif_tx0 unif_tx1 True)

unif21_2 :: AutomatedTest
unif21_2 = AT "Unifying p1[2](x0,x1) with p1[2](x1,x2)" (unif_test_term unif_unif21 unif_tx2 unif_tx1 True)

unif21_3 :: AutomatedTest
unif21_3 = AT "Unifying p1[2](x0,x1) with p1[2](x1,x2)" (unif_test_term unif_unif21 unif_tx2 unif_tx0 True)

unif21_4 :: AutomatedTest
unif21_4 = AT "Unifying p1[2](x0,x1) with p1[2](x1,x2)" (unif_test_term unif_unif21 unif_tx1 unif_tx1 True)


unif_term22_a1 :: Atom
unif_term22_a1 = read "p1[2](x0,x1)"

unif_term22_a2 :: Atom
unif_term22_a2 = read "p1[2](f1[1](x1),f1[1](x0))"

unif_unif22 :: AtomUnifier
unif_unif22 = unif_term22_a1 =.= unif_term22_a2

unif22_1 :: AutomatedTest
unif22_1 = AT "Unifying p1[2](x0,x1) with p1[2](f1[1](x1),f1[1](x0))" (unif_test_term_fail unif_unif22 unif_tx0 unif_tx1)


unif_term23_a1 :: Atom
unif_term23_a1 = read "p1[2](x0,f1[0]())"

unif_term23_a2 :: Atom
unif_term23_a2 = read "p1[2](f1[0](),x0)"

unif_unif23 :: AtomUnifier
unif_unif23 = unif_term23_a1 =.= unif_term23_a2

unif23_1 :: AutomatedTest
unif23_1 = AT "Unifying p1[2](x0,f1[0]()) with p1[2](f1[0](),x0)" (unif_test_term unif_unif23 unif_tx0 (read "f1[0]()") True)

unif23_2 :: AutomatedTest
unif23_2 = AT "Unifying p1[2](x0,f1[0]()) with p1[2](f1[0](),x0)" (unif_test_term unif_unif23 unif_tx0 unif_tx1 False)


unif_term24_a1 :: Atom
unif_term24_a1 = read "p1[2](x0,f1[0]())"

unif_term24_a2 :: Atom
unif_term24_a2 = read "p1[2](f2[0](),x0)"

unif_unif24 :: AtomUnifier
unif_unif24 = unif_term24_a1 =.= unif_term24_a2

unif24_1 :: AutomatedTest
unif24_1 = AT "Unifying p1[2](x0,f1[0]()) with p1[2](f2[0](),x0)" (unif_test_term_fail unif_unif24 unif_tx0 unif_tx1)


unif_term25_a1 :: Atom
unif_term25_a1 = read "p1[1](f1[1](x0))"

unif_term25_a2 :: Atom
unif_term25_a2 = read "p1[1](f1[1](x1))"

unif_term25_a3 :: Atom
unif_term25_a3 = read "p2[1](x2)"

unif_term25_a4 :: Atom
unif_term25_a4 = read "p2[1](f2[1](x0))"

unif_unif25 :: AtomUnifier
unif_unif25 = (unif_term25_a1 =.= unif_term25_a2) >> (unif_term25_a3 =.= unif_term25_a4)

unif25_1 :: AutomatedTest
unif25_1 = AT "Unifying p1[1](f1[1](x0)) with p1[1](f1[1](x1)) and p2[1](x2) with p2[1](f2[1](x0))" (unif_test_term unif_unif25 unif_tx0 unif_tx1 True)

unif25_2 :: AutomatedTest
unif25_2 = AT "Unifying p1[1](f1[1](x0)) with p1[1](f1[1](x1)) and p2[1](x2) with p2[1](f2[1](x0))" (unif_test_term unif_unif25 unif_tx0 unif_tx2 False)

unif25_3 :: AutomatedTest
unif25_3 = AT "Unifying p1[1](f1[1](x0)) with p1[1](f1[1](x1)) and p2[1](x2) with p2[1](f2[1](x0))" (unif_test_term unif_unif25 unif_tx2 unif_tx1 False)

unif25_4 :: AutomatedTest
unif25_4 = AT "Unifying p1[1](f1[1](x0)) with p1[1](f1[1](x1)) and p2[1](x2) with p2[1](f2[1](x0))" (unif_test_term unif_unif25 unif_tx2 (read "f2[1](x0)") True)

unif25_5 :: AutomatedTest
unif25_5 = AT "Unifying p1[1](f1[1](x0)) with p1[1](f1[1](x1)) and p2[1](x2) with p2[1](f2[1](x0))" (unif_test_term unif_unif25 unif_tx2 (read "f2[1](x1)") True)

unif25_6 :: AutomatedTest
unif25_6 = AT "Unifying p1[1](f1[1](x0)) with p1[1](f1[1](x1)) and p2[1](x2) with p2[1](f2[1](x0))" (unif_test_term unif_unif25 unif_tx2 (read "f1[1](x0)") False)



unif_tests :: [AutomatedTest]
unif_tests = [unif1_1, unif1_2, unif2_1, unif2_2, unif3_1, unif3_2, unif3_3, unif4_1, unif4_2, unif5_1, unif5_2, unif5_3, unif6_1, unif7_1, unif7_2, unif7_3, unif8_1, unif8_2, unif8_3, unif8_4, unif9_1, unif9_2, unif9_3, unif9_4, unif10_1, unif11_1, unif12_1, unif12_2, unif12_3, unif12_4, unif12_5, unif13_1, unif14_1, unif14_2, unif14_3, unif14_4, unif14_5, unif14_6, unif14_7, unif15_1, unif15_2, unif15_3, unif16_1, unif16_2, unif16_3, unif16_4, unif16_5, unif16_6, unif16_7, unif16_8, unif16_9, unif16_9, unif16_10, unif16_11, unif16_12, unif16_13, unif17_1, unif17_2, unif18_1, unif19_1, unif19_2, unif19_3, unif20_1, unif20_2, unif20_3, unif21_1, unif21_2, unif21_3, unif21_4, unif22_1, unif23_1, unif23_2, unif24_1, unif25_1, unif25_2, unif25_3, unif25_4, unif25_5, unif25_6]

unif_test :: IO ()
unif_test = putStr (combine_test_results unif_tests)





all_test :: IO ()
all_test = (putStr "\n\nTERM PARSING TESTS\n\n") >> parse_term_test >>
		(putStr "\n\nATOM PARSING TESTS\n\n") >> parse_atom_test >>
		(putStr "\n\nFIRST ORDER UNIFICATION TESTS\n\n") >> unif_test
