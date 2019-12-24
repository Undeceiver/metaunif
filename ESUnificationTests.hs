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
-- Existential second-order unification (with instantiation set results, performing batch unification (multiple unifiers and equations at once))
module ESUnificationTests where

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


-- Implicit solution handling tests.
-- We define implicit solutions using the (>:=) and (>::=) operators and then check that they work properly.

check_sol_implicit :: String -> SOMetaUnifSol -> SOMetaNMGU -> AutomatedTest
check_sol_implicit title usol mgu = AT title (if res then (ATR True "The solution is correctly implicitly represented.") else (ATR False "The implicit unifier does not include the provided solution.")) where res = checkImplicit mgu usol

check_not_sol_implicit :: String -> SOMetaUnifSol -> SOMetaNMGU -> AutomatedTest
check_not_sol_implicit title usol mgu = AT title (if res then (ATR False "The solution should not be implicitly represented, but it is.") else (ATR True "The implicit unifier correctly does not include the provided solution.")) where res = checkImplicit mgu usol

explicit_unif_compare :: SOMetaUnifSol -> SOMetaUnifSol -> Bool
explicit_unif_compare usols usoll = (isSubmapOf (fosol usols) (fosol usoll)) && (isSubmapOf (sosol usols) (sosol usoll))

check_sol_explicit :: String -> SOMetaUnifSol -> SOMetaNMGU -> Int -> AutomatedTest
check_sol_explicit title usol mgu n = AT title (if (isNothing res) then (ATR False ("Could not find the given solution in the first " ++ (show n) ++ " elements of the enumeration of the implicit solution.")) else (ATR True ("Found the given solution within the first " ++ (show n) ++ " elements of the enumeration of the implicit solution."))) where res = uns_produce_next (efind (explicit_unif_compare usol) (etake n (enumImplicit mgu)))

check_not_sol_explicit :: String -> SOMetaUnifSol -> SOMetaNMGU -> Int -> AutomatedTest
check_not_sol_explicit title usol mgu n = AT title (if (isNothing res) then (ATR True ("Verified the solution is not within the first " ++ (show n) ++ " elements of the enumeration of the implicit solution.")) else (ATR False ("Incorrectly found the given solution within the first " ++ (show n) ++ " elements of the enumeration of the implicit solution."))) where res = uns_produce_next (efind (explicit_unif_compare usol) (etake n (enumImplicit mgu)))

check_all_sol :: String -> SOMetaUnifSol -> SOMetaNMGU -> Int -> AutomatedTest
check_all_sol title usol mgu n = AT title (if res then (ATR True ("Verified that all of the first " ++ (show n) ++ " elements of the enumeration of the implicit solution contain the given subsolution.")) else (ATR False ("Found elements within the first " ++ (show n) ++ " elements of the enumeration of the implicit solution that do not contain the given subsolution."))) where res = uns_produce_next (eall (return . (explicit_unif_compare usol)) (etake n (enumImplicit mgu)))

check_not_all_sol :: String -> SOMetaUnifSol -> SOMetaNMGU -> Int -> AutomatedTest
check_not_all_sol title usol mgu n = AT title (if res then (ATR False ("Incorrectly, all of the first " ++ (show n) ++ " elements of the enumeration of the implicit solution contain the given subsolution.")) else (ATR True ("Verified that there exist elements within the first " ++ (show n) ++ " elements of the enumeration that do not contain the given subsolution."))) where res = uns_produce_next (eall (return . (explicit_unif_compare usol)) (etake n (enumImplicit mgu)))


implicit_sig1 :: SOMetaSignature
implicit_sig1 = SOSignature (Signature [read "p1[0]" --> EnumProc.Empty, read "p2[1]" --> EnumProc.Empty, read "p3[2]" --> EnumProc.Empty, read "p4[3]" --> EnumProc.Empty] [read "f1[0]" --> EnumProc.Empty, read "f2[1]" --> EnumProc.Empty, read "f3[2]" --> EnumProc.Empty, read "f4[3]" --> EnumProc.Empty] (read "x0" --> read "x1" --> read "x2" --> read "x3" --> read "x4" --> EnumProc.Empty)) (read "F1[0]" --> read "F2[1]" --> read "F3[2]" --> read "F4[3]" --> EnumProc.Empty)

implicit_scale1 :: Int
implicit_scale1 = 100


implicit_eq1_1 :: JState SOMetaMGU
implicit_eq1_1 = (read "x0") >:= (read "f1[0]()")

implicit_mgu1 :: SOMetaMGU
implicit_mgu1 = runESMGU implicit_sig1 (implicit_eq1_1)

implicit_nmgu1 :: SOMetaNMGU
implicit_nmgu1 = fromJust (normalize_esmgu implicit_mgu1)

implicit1_t1 :: AutomatedTest
implicit1_t1 = check_sol_implicit "Verifying the implicit representation of {x0 -> f1[0]()}"
		(UnifSolution (fromList [(read "x0",read "f1[0]()")]) (fromList []))
		implicit_nmgu1

implicit1_t2 :: AutomatedTest
implicit1_t2 = check_sol_explicit "Verifying the explicit presence of {x0 -> f1[0]()}"
		(UnifSolution (fromList [(read "x0",read "f1[0]()")]) (fromList []))
		implicit_nmgu1
		implicit_scale1

implicit1_t3 :: AutomatedTest
implicit1_t3 = check_all_sol "Verifying that all solutions have {x0 -> f1[0]()}"
		(UnifSolution (fromList [(read "x0",read "f1[0]()")]) (fromList []))
		implicit_nmgu1
		implicit_scale1

implicit1_t4 :: AutomatedTest
implicit1_t4 = check_not_sol_implicit "Verifying the implicit non-representation of {x0 -> f2[1](f1[0]())}"
		(UnifSolution (fromList [(read "x0",read "f2[1](f1[0]())")]) (fromList []))
		implicit_nmgu1

implicit1_t5 :: AutomatedTest
implicit1_t5 = check_not_sol_explicit "Verifying the explicit non-presence of {x0 -> f2[1](f1[0]())}"
		(UnifSolution (fromList [(read "x0",read "f2[1](f1[0]())")]) (fromList []))
		implicit_nmgu1
		implicit_scale1

implicit1_t6 :: AutomatedTest
implicit1_t6 = check_sol_implicit "Verifying the implicit representation of {x1 -> f2[1](f1[0]())}"
		(UnifSolution (fromList [(read "x1",read "f2[1](f1[0]())")]) (fromList []))
		implicit_nmgu1
		
implicit1_t7 :: AutomatedTest
implicit1_t7 = check_sol_explicit "Verifying the explicit presence of {x1 -> f2[1](f1[0]())"
		(UnifSolution (fromList [(read "x1",read "f2[1](f1[0]())")]) (fromList []))
		implicit_nmgu1
		implicit_scale1

implicit1_t8 :: AutomatedTest
implicit1_t8 = check_not_all_sol "Verifying that not all solutions have {x1 -> f2[1](f1[0]())"
		(UnifSolution (fromList [(read "x1",read "f2[1](f1[0]())")]) (fromList []))
		implicit_nmgu1
		implicit_scale1

implicit_tests1 :: String
implicit_tests1 = combine_test_results [implicit1_t1,implicit1_t2,implicit1_t3,implicit1_t4,implicit1_t5,implicit1_t6,implicit1_t7,implicit1_t8]


implicit_eq2_1 :: JState SOMetaMGU
implicit_eq2_1 = (read "x0") >:= (read "f1[0]()")

implicit_eq2_2 :: JState SOMetaMGU
implicit_eq2_2 = (read "x1") >:= (read "f2[1](f1[0]())")

implicit_mgu2 :: SOMetaMGU
implicit_mgu2 = runESMGU implicit_sig1 (implicit_eq1_1 >> implicit_eq2_2)

implicit_nmgu2 :: SOMetaNMGU
implicit_nmgu2 = fromJust (normalize_esmgu implicit_mgu2)

implicit2_t1 :: AutomatedTest
implicit2_t1 = check_sol_implicit "Verifying the implicit representation of {x0 -> f1[0]()}"
		(UnifSolution (fromList [(read "x0",read "f1[0]()")]) (fromList []))
		implicit_nmgu2

implicit2_t2 :: AutomatedTest
implicit2_t2 = check_sol_explicit "Verifying the explicit presence of {x0 -> f1[0]()}"
		(UnifSolution (fromList [(read "x0",read "f1[0]()")]) (fromList []))
		implicit_nmgu2
		implicit_scale1

implicit2_t3 :: AutomatedTest
implicit2_t3 = check_all_sol "Verifying that all solutions have {x0 -> f1[0]()}"
		(UnifSolution (fromList [(read "x0",read "f1[0]()")]) (fromList []))
		implicit_nmgu2
		implicit_scale1

implicit2_t4 :: AutomatedTest
implicit2_t4 = check_not_sol_implicit "Verifying the implicit non-representation of {x0 -> f2[1](f1[0]())}"
		(UnifSolution (fromList [(read "x0",read "f2[1](f1[0]())")]) (fromList []))
		implicit_nmgu2

implicit2_t5 :: AutomatedTest
implicit2_t5 = check_not_sol_explicit "Verifying the explicit non-presence of {x0 -> f2[1](f1[0]())}"
		(UnifSolution (fromList [(read "x0",read "f2[1](f1[0]())")]) (fromList []))
		implicit_nmgu2
		implicit_scale1

implicit2_t6 :: AutomatedTest
implicit2_t6 = check_sol_implicit "Verifying the implicit representation of {x1 -> f2[1](f1[0]())}"
		(UnifSolution (fromList [(read "x1",read "f2[1](f1[0]())")]) (fromList []))
		implicit_nmgu2
		
implicit2_t7 :: AutomatedTest
implicit2_t7 = check_sol_explicit "Verifying the explicit presence of {x1 -> f2[1](f1[0]())"
		(UnifSolution (fromList [(read "x1",read "f2[1](f1[0]())")]) (fromList []))
		implicit_nmgu2
		implicit_scale1

implicit2_t8 :: AutomatedTest
implicit2_t8 = check_all_sol "Verifying that all solutions have {x1 -> f2[1](f1[0]())"
		(UnifSolution (fromList [(read "x1",read "f2[1](f1[0]())")]) (fromList []))
		implicit_nmgu2
		implicit_scale1

implicit2_t9 :: AutomatedTest
implicit2_t9 = check_not_sol_implicit "Verifying the implicit non-representation of {x1 -> f1[0]()}"
		(UnifSolution (fromList [(read "x1",read "f1[0]()")]) (fromList []))
		implicit_nmgu2

implicit2_t10 :: AutomatedTest
implicit2_t10 = check_not_sol_explicit "Verifying the explicit non-presence of {x1 -> f1[0]()}"
		(UnifSolution (fromList [(read "x1",read "f1[0]()")]) (fromList []))
		implicit_nmgu2
		implicit_scale1

implicit_tests2 :: String
implicit_tests2 = combine_test_results [implicit2_t1,implicit2_t2,implicit2_t3,implicit2_t4,implicit2_t5,implicit2_t6,implicit2_t7,implicit2_t8,implicit2_t9,implicit2_t10]


implicit_eq3_1 :: JState SOMetaMGU
implicit_eq3_1 = (read "F1[0]") >::= (read "f1[0]")

implicit_mgu3 :: SOMetaMGU
implicit_mgu3 = runESMGU implicit_sig1 (implicit_eq3_1)

implicit_nmgu3 :: SOMetaNMGU
implicit_nmgu3 = fromJust (normalize_esmgu implicit_mgu3)

implicit3_t1 :: AutomatedTest
implicit3_t1 = check_sol_implicit "Verifying the implicit representation of {F1[0] -> f1[0]}"
		(UnifSolution (fromList []) (fromList [(read "F1[0]",read "f1[0]")]))
		implicit_nmgu3

implicit3_t2 :: AutomatedTest
implicit3_t2 = check_sol_explicit "Verifying the explicit presence of {F1[0] -> f1[0]}"
		(UnifSolution (fromList []) (fromList [(read "F1[0]",read "f1[0]")]))
		implicit_nmgu3
		implicit_scale1

implicit3_t3 :: AutomatedTest
implicit3_t3 = check_all_sol "Verifying that all solutions have {F1[0] -> f1[0]}"
		(UnifSolution (fromList []) (fromList [(read "F1[0]",read "f1[0]")]))
		implicit_nmgu3
		implicit_scale1

implicit3_t4 :: AutomatedTest
implicit3_t4 = check_not_sol_implicit "Verifying the implicit non-representation of {F1[0] -> f2[1]{f1[0]}}"
		(UnifSolution (fromList []) (fromList [(read "F1[0]",read "f2[1]{f1[0]}")]))
		implicit_nmgu3

implicit3_t5 :: AutomatedTest
implicit3_t5 = check_not_sol_explicit "Verifying the explicit non-presence of {F1[0] -> f2[1]{f1[0]}}"
		(UnifSolution (fromList []) (fromList [(read "F1[0]",read "f2[1]{f1[0]}")]))
		implicit_nmgu3
		implicit_scale1

implicit3_t6 :: AutomatedTest
implicit3_t6 = check_sol_implicit "Verifying the implicit representation of {F2[1] -> f2[1]{f1[0]}}"
		(UnifSolution (fromList []) (fromList [(read "F2[1]",read "f2[1]{f1[0]}")]))
		implicit_nmgu3
		
implicit3_t7 :: AutomatedTest
implicit3_t7 = check_sol_explicit "Verifying the explicit presence of {F2[1] -> f2[1]{f1[0]}}"
		(UnifSolution (fromList []) (fromList [(read "F2[1]",read "f2[1]{f1[0]}")]))
		implicit_nmgu3
		implicit_scale1

implicit3_t8 :: AutomatedTest
implicit3_t8 = check_not_all_sol "Verifying that not all solutions have {F2[1] -> f2[1]{f1[0]}}"
		(UnifSolution (fromList []) (fromList [(read "F2[1]",read "f2[1]{f1[0]}")]))
		implicit_nmgu3
		implicit_scale1

implicit_tests3 :: String
implicit_tests3 = combine_test_results [implicit3_t1,implicit3_t2,implicit3_t3,implicit3_t4,implicit3_t5,implicit3_t6,implicit3_t7,implicit3_t8]





implicit_test :: IO ()
implicit_test = putStr "EXAMPLE 1\n\n" >> putStr implicit_tests1 >>
		putStr "EXAMPLE 2\n\n" >> putStr implicit_tests2 >>
		putStr "EXAMPLE 3\n\n" >> putStr implicit_tests3
