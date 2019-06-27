
module ObjectLogicTests where

import ObjectLogic
import AutoTests
import Control.Unification
import Syntax

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
