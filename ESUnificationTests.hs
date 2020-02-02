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
import Provenance
import CESQResolutionProvenance


-- Implicit solution handling tests.
-- We define implicit solutions using the (>:=) and (>::=) operators and then check that they work properly.

check_sol_implicit :: String -> SOMetaUnifSol -> SOMetaNMGU -> AutomatedTest
check_sol_implicit title usol mgu = AT title (if res then (ATR True "The solution is correctly implicitly represented.") else (ATR False "The implicit unifier does not include the provided solution.")) where res = checkImplicit mgu usol

check_not_sol_implicit :: String -> SOMetaUnifSol -> SOMetaNMGU -> AutomatedTest
check_not_sol_implicit title usol mgu = AT title (if res then (ATR False "The solution should not be implicitly represented, but it is.") else (ATR True "The implicit unifier correctly does not include the provided solution.")) where res = checkImplicit mgu usol

explicit_unif_compare :: SOMetaUnifSol -> SOMetaUnifSol -> Bool
explicit_unif_compare usols usoll = (isSubmapOfBy (\a -> \b -> ((normalize_groundt a)::GroundSOMetaterm) == (normalize_groundt b)) (fosol usols) (fosol usoll)) && (isSubmapOfBy (\a -> \b -> ((normalize a)::GroundSOMetatermF) == (normalize b)) (sosol usols) (sosol usoll))

check_sol_explicit :: String -> SOMetaUnifSol -> SOMetaNMGU -> Int -> AutomatedTest
check_sol_explicit title usol mgu n = AT title (if (isNothing res) then (ATR False ("Could not find the given solution in the first " ++ (show n) ++ " elements of the enumeration of the implicit solution.")) else (ATR True ("Found the given solution within the first " ++ (show n) ++ " elements of the enumeration of the implicit solution."))) where res = uns_produce_next (efind (explicit_unif_compare usol) (etake n (enumImplicit mgu)))

check_not_sol_explicit :: String -> SOMetaUnifSol -> SOMetaNMGU -> Int -> AutomatedTest
check_not_sol_explicit title usol mgu n = AT title (if (isNothing res) then (ATR True ("Verified the solution is not within the first " ++ (show n) ++ " elements of the enumeration of the implicit solution.")) else (ATR False ("Incorrectly found the given solution within the first " ++ (show n) ++ " elements of the enumeration of the implicit solution."))) where res = uns_produce_next (efind (explicit_unif_compare usol) (etake n (enumImplicit mgu)))

check_all_sol :: String -> SOMetaUnifSol -> SOMetaNMGU -> Int -> AutomatedTest
check_all_sol title usol mgu n = AT title (if res then (ATR True ("Verified that all of the first " ++ (show n) ++ " elements of the enumeration of the implicit solution contain the given subsolution.")) else (ATR False ("Found elements within the first " ++ (show n) ++ " elements of the enumeration of the implicit solution that do not contain the given subsolution."))) where res = uns_produce_next (eall (return . (explicit_unif_compare usol)) (etake n (enumImplicit mgu)))

check_not_all_sol :: String -> SOMetaUnifSol -> SOMetaNMGU -> Int -> AutomatedTest
check_not_all_sol title usol mgu n = AT title (if res then (ATR False ("Incorrectly, all of the first " ++ (show n) ++ " elements of the enumeration of the implicit solution contain the given subsolution.")) else (ATR True ("Verified that there exist elements within the first " ++ (show n) ++ " elements of the enumeration that do not contain the given subsolution."))) where res = uns_produce_next (eall (return . (explicit_unif_compare usol)) (etake n (enumImplicit mgu)))

-- Detail to make testing more reliable and efficient: We reverse the lists of predicates, functions and variables, as the first one to be enumerated is the last one in the list (recursion happens from the end).

implicit_preds1 :: [EnumProc OPredicate]
implicit_preds1 = (uns_ecollapse . uns_ereverse) <$> [read "p1[0]" --> EnumProc.Empty, read "p2[1]" --> EnumProc.Empty, read "p3[2]" --> EnumProc.Empty, read "p4[3]" --> EnumProc.Empty]

implicit_funcs1 :: [EnumProc OFunction]
implicit_funcs1 = (uns_ecollapse . uns_ereverse) <$> [read "f1[0]" --> EnumProc.Empty, read "f2[1]" --> EnumProc.Empty, read "f3[2]" --> EnumProc.Empty, read "f4[3]" --> EnumProc.Empty]

implicit_vars1 :: EnumProc OVariable
implicit_vars1 = uns_ecollapse . uns_ereverse $ (read "x0" --> read "x1" --> read "x2" --> read "x3" --> read "x4" --> EnumProc.Empty)

implicit_sovars1 :: EnumProc SOMVariable
implicit_sovars1 = uns_ecollapse . uns_ereverse $ (read "F1[0]" --> read "F2[1]" --> read "F3[2]" --> read "F4[3]" --> EnumProc.Empty)

implicit_sig1 :: SOMetaSignature
implicit_sig1 = SOSignature (Signature implicit_preds1 implicit_funcs1 implicit_vars1) implicit_sovars1

implicit_scale1 :: Int
implicit_scale1 = 100


implicit_eq1_1 :: JState SOMetaMGU
implicit_eq1_1 = (read "x0") >:= (read "f1[0]()")

implicit_mgu1 :: SOMetaMGU
implicit_mgu1 = runESMGU implicit_sig1 (implicit_eq1_1)

implicit_nmgu1 :: SOMetaNMGU
implicit_nmgu1 = fromJust (normalize_esmgu implicit_mgu1)

implicit_sols1 :: EnumProc (SOMetaUnifSol :- CQRP)
implicit_sols1 = fromProvenanceT (nesmgu_enumImplicit implicit_nmgu1)

implicit_lsols1 :: EnumProc (SOMetaUnifSol :- CQRP)
implicit_lsols1 = etake implicit_scale1 implicit_sols1

implicit_rsols1 :: EnumProc SOMetaUnifSol
implicit_rsols1 = raw <$> implicit_lsols1

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

implicit_sols2 :: EnumProc (SOMetaUnifSol :- CQRP)
implicit_sols2 = fromProvenanceT (nesmgu_enumImplicit implicit_nmgu2)

implicit_lsols2 :: EnumProc (SOMetaUnifSol :- CQRP)
implicit_lsols2 = etake implicit_scale1 implicit_sols2

implicit_rsols2 :: EnumProc SOMetaUnifSol
implicit_rsols2 = raw <$> implicit_lsols2


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


implicit_scale2 :: Int
implicit_scale2 = 1000

implicit_eq3_1 :: JState SOMetaMGU
implicit_eq3_1 = (read "F1[0]") >::= (read "f1[0]")

implicit_mgu3 :: SOMetaMGU
implicit_mgu3 = runESMGU implicit_sig1 (implicit_eq3_1)

implicit_nmgu3 :: SOMetaNMGU
implicit_nmgu3 = fromJust (normalize_esmgu implicit_mgu3)

implicit_sols3 :: EnumProc (SOMetaUnifSol :- CQRP)
implicit_sols3 = fromProvenanceT (nesmgu_enumImplicit implicit_nmgu3)

implicit_lsols3 :: EnumProc (SOMetaUnifSol :- CQRP)
implicit_lsols3 = etake implicit_scale2 implicit_sols3

implicit_rsols3 :: EnumProc SOMetaUnifSol
implicit_rsols3 = raw <$> implicit_lsols3


implicit3_t1 :: AutomatedTest
implicit3_t1 = check_sol_implicit "Verifying the implicit representation of {F1[0] -> f1[0]}"
		(UnifSolution (fromList []) (fromList [(read "F1[0]",read "f1[0]")]))
		implicit_nmgu3

implicit3_t2 :: AutomatedTest
implicit3_t2 = check_sol_explicit "Verifying the explicit presence of {F1[0] -> f1[0]}"
		(UnifSolution (fromList []) (fromList [(read "F1[0]",read "f1[0]")]))
		implicit_nmgu3
		implicit_scale2

implicit3_t3 :: AutomatedTest
implicit3_t3 = check_all_sol "Verifying that all solutions have {F1[0] -> f1[0]}"
		(UnifSolution (fromList []) (fromList [(read "F1[0]",read "f1[0]")]))
		implicit_nmgu3
		implicit_scale2

implicit3_t4 :: AutomatedTest
implicit3_t4 = check_not_sol_implicit "Verifying the implicit non-representation of {F1[0] -> f2[1]{f1[0]}}"
		(UnifSolution (fromList []) (fromList [(read "F1[0]",read "f2[1]{f1[0]}")]))
		implicit_nmgu3

implicit3_t5 :: AutomatedTest
implicit3_t5 = check_not_sol_explicit "Verifying the explicit non-presence of {F1[0] -> f2[1]{f1[0]}}"
		(UnifSolution (fromList []) (fromList [(read "F1[0]",read "f2[1]{f1[0]}")]))
		implicit_nmgu3
		implicit_scale2

implicit3_t6 :: AutomatedTest
implicit3_t6 = check_sol_implicit "Verifying the implicit representation of {F2[1] -> f2[1]{f1[0]}}"
		(UnifSolution (fromList []) (fromList [(read "F2[1]",read "f2[1]{f1[0]}")]))
		implicit_nmgu3
		
implicit3_t7 :: AutomatedTest
implicit3_t7 = check_sol_explicit "Verifying the explicit presence of {F2[1] -> f2[1]{f1[0]}}"
		(UnifSolution (fromList []) (fromList [(read "F2[1]",read "f2[1]{f1[0]}")]))
		implicit_nmgu3
		implicit_scale2

implicit3_t8 :: AutomatedTest
implicit3_t8 = check_not_all_sol "Verifying that not all solutions have {F2[1] -> f2[1]{f1[0]}}"
		(UnifSolution (fromList []) (fromList [(read "F2[1]",read "f2[1]{f1[0]}")]))
		implicit_nmgu3
		implicit_scale2

implicit_tests3 :: String
implicit_tests3 = combine_test_results [implicit3_t1,implicit3_t2,implicit3_t3,implicit3_t4,implicit3_t5,implicit3_t6,implicit3_t7,implicit3_t8]


implicit_eq4_1 :: JState SOMetaMGU
implicit_eq4_1 = (read "F1[0]") >::= (read "f1[0]")

implicit_eq4_2 :: JState SOMetaMGU
implicit_eq4_2 = (read "x0") >:= (read "F1[0]()")

implicit_mgu4 :: SOMetaMGU
implicit_mgu4 = runESMGU implicit_sig1 (implicit_eq4_1 >> implicit_eq4_2)

implicit_nmgu4 :: SOMetaNMGU
implicit_nmgu4 = fromJust (normalize_esmgu implicit_mgu4)

implicit_sols4 :: EnumProc (SOMetaUnifSol :- CQRP)
implicit_sols4 = fromProvenanceT (nesmgu_enumImplicit implicit_nmgu4)

implicit_lsols4 :: EnumProc (SOMetaUnifSol :- CQRP)
implicit_lsols4 = etake implicit_scale2 implicit_sols4

implicit_rsols4 :: EnumProc SOMetaUnifSol
implicit_rsols4 = raw <$> implicit_lsols4

implicit4_t1 :: AutomatedTest
implicit4_t1 = check_sol_implicit "Verifying the implicit representation of {x0 -> f1[0]()}"
		(UnifSolution (fromList [(read "x0",read "f1[0]()")]) (fromList []))
		implicit_nmgu4

implicit4_t2 :: AutomatedTest
implicit4_t2 = check_sol_explicit "Verifying the explicit presence of {x0 -> f1[0]()}"
		(UnifSolution (fromList [(read "x0",read "f1[0]()")]) (fromList []))
		implicit_nmgu4
		implicit_scale2

implicit4_t3 :: AutomatedTest
implicit4_t3 = check_all_sol "Verifying that all solutions have {x0 -> f1[0]()}"
		(UnifSolution (fromList [(read "x0",read "f1[0]()")]) (fromList []))
		implicit_nmgu4
		implicit_scale2

implicit4_t4 :: AutomatedTest
implicit4_t4 = check_not_sol_implicit "Verifying the implicit non-representation of {x0 -> f2[1](f1[0]())}"
		(UnifSolution (fromList [(read "x0",read "f2[1](f1[0]())")]) (fromList []))
		implicit_nmgu4

implicit4_t5 :: AutomatedTest
implicit4_t5 = check_not_sol_explicit "Verifying the explicit non-presence of {x0 -> f2[1](f1[0]())}"
		(UnifSolution (fromList [(read "x0",read "f2[1](f1[0]())")]) (fromList []))
		implicit_nmgu4
		implicit_scale2

implicit_tests4 :: String
implicit_tests4 = combine_test_results [implicit4_t1,implicit4_t2,implicit4_t3,implicit4_t4,implicit4_t5]


implicit_eq5_1 :: JState SOMetaMGU
implicit_eq5_1 = (read "x0") >:= (read "F1[0]()")

implicit_eq5_2 :: JState SOMetaMGU
implicit_eq5_2 = (read "x1") >:= (read "F1[0]()")

implicit_mgu5 :: SOMetaMGU
implicit_mgu5 = runESMGU implicit_sig1 (implicit_eq5_1 >> implicit_eq5_2)

implicit_nmgu5 :: SOMetaNMGU
implicit_nmgu5 = fromJust (normalize_esmgu implicit_mgu5)

implicit_sols5 :: EnumProc (SOMetaUnifSol :- CQRP)
implicit_sols5 = fromProvenanceT (nesmgu_enumImplicit implicit_nmgu5)

implicit_lsols5 :: EnumProc (SOMetaUnifSol :- CQRP)
implicit_lsols5 = etake implicit_scale2 implicit_sols5

implicit_rsols5 :: EnumProc SOMetaUnifSol
implicit_rsols5 = raw <$> implicit_lsols5

implicit5_t1 :: AutomatedTest
implicit5_t1 = check_sol_implicit "Verifying the implicit representation of {x0 -> f1[0](), x1 -> f1[0](), F1[0] -> f1[0]}"
		(UnifSolution (fromList [(read "x0",read "f1[0]()"),(read "x1",read "f1[0]()")]) (fromList [(read "F1[0]",read "f1[0]")]))
		implicit_nmgu5

implicit5_t2 :: AutomatedTest
implicit5_t2 = check_sol_explicit "Verifying the explicit presence of {x0 -> f1[0](), x1 -> f1[0](), F1[0] -> f1[0]}"
		(UnifSolution (fromList [(read "x0",read "f1[0]()"),(read "x1",read "f1[0]()")]) (fromList [(read "F1[0]",read "f1[0]")]))
		implicit_nmgu5
		implicit_scale2

implicit5_t3 :: AutomatedTest
implicit5_t3 = check_not_all_sol "Verifying that not all solutions have {x0 -> f1[0](), x1 -> f1[0](), F1[0] -> f1[0]}"
		(UnifSolution (fromList [(read "x0",read "f1[0]()"),(read "x1",read "f1[0]()")]) (fromList [(read "F1[0]",read "f1[0]")]))
		implicit_nmgu5
		implicit_scale2

implicit5_t4 :: AutomatedTest
implicit5_t4 = check_sol_implicit "Verifying the implicit representation of {x0 -> f2[1](f1[0]()), x1 -> f2[1](f1[0]()), F1[0] -> f2[1]{f1[0]}}"
		(UnifSolution (fromList [(read "x0",read "f2[1](f1[0]())"),(read "x1",read "f2[1](f1[0]())")]) (fromList [(read "F1[0]",read "f2[1]{f1[0]}")]))
		implicit_nmgu5

implicit5_t5 :: AutomatedTest
implicit5_t5 = check_sol_explicit "Verifying the explicit presence of {x0 -> f2[1](f1[0]()), x1 -> f2[1](f1[0]()), F1[0] -> f2[1]{f1[0]}}"
		(UnifSolution (fromList [(read "x0",read "f2[1](f1[0]())"),(read "x1",read "f2[1](f1[0]())")]) (fromList [(read "F1[0]",read "f2[1]{f1[0]}")]))
		implicit_nmgu5
		implicit_scale2

implicit5_t6 :: AutomatedTest
implicit5_t6 = check_not_all_sol "Verifying that not all solutions have {x0 -> f2[1](f1[0]()), x1 -> f2[1](f1[0]()), F1[0] -> f2[1]{f1[0]}}"
		(UnifSolution (fromList [(read "x0",read "f2[1](f1[0]())"),(read "x1",read "f2[1](f1[0]())")]) (fromList [(read "F1[0]",read "f2[1]{f1[0]}")]))
		implicit_nmgu5
		implicit_scale2

implicit5_t7 :: AutomatedTest
implicit5_t7 = check_not_sol_implicit "Verifying the implicit non-representation of {x0 -> f1[0](), x1 -> f2[1](f1[0]())}"
		(UnifSolution (fromList [(read "x0",read "f1[0]()"),(read "x1",read "f2[1](f1[0]())")]) (fromList []))
		implicit_nmgu5

implicit5_t8 :: AutomatedTest
implicit5_t8 = check_not_sol_explicit "Verifying the explicit non-presence of {x0 -> f1[0](), x1 -> f2[1](f1[0]())}"
		(UnifSolution (fromList [(read "x0",read "f1[0]()"),(read "x1",read "f2[1](f1[0]())")]) (fromList []))
		implicit_nmgu5
		implicit_scale2

implicit5_t9 :: AutomatedTest
implicit5_t9 = check_not_sol_implicit "Verifying the implicit non-representation of {x0 -> f2[1](f1[0]()), x1 -> f1[0]()}"
		(UnifSolution (fromList [(read "x0",read "f2[1](f1[0]())"),(read "x1",read "f1[0]()")]) (fromList []))
		implicit_nmgu5

implicit5_t10 :: AutomatedTest
implicit5_t10 = check_not_sol_explicit "Verifying the explicit non-presence of {x0 -> f2[1](f1[0]()), x1 -> f1[0]()}"
		(UnifSolution (fromList [(read "x0",read "f2[1](f1[0]())"),(read "x1",read "f1[0]()")]) (fromList []))
		implicit_nmgu5
		implicit_scale2

implicit_tests5 :: String
implicit_tests5 = combine_test_results [implicit5_t1,implicit5_t2,implicit5_t3,implicit5_t4,implicit5_t5,implicit5_t6,implicit5_t7,implicit5_t8,implicit5_t9,implicit5_t10]


implicit_scale3 :: Int
implicit_scale3 = 3000

implicit_eq6_1 :: JState SOMetaMGU
implicit_eq6_1 = (read "x0") >:= (read "f3[2]{F2[1],pi0}(f1[0](),f1[0]())")

implicit_eq6_2 :: JState SOMetaMGU
implicit_eq6_2 = (read "x1") >:= (read "f2[1]{F2[1]}(f1[0]())")

implicit_mgu6 :: SOMetaMGU
implicit_mgu6 = runESMGU implicit_sig1 (implicit_eq6_1 >> implicit_eq6_2)

implicit_nmgu6 :: SOMetaNMGU
implicit_nmgu6 = fromJust (normalize_esmgu implicit_mgu6)

implicit_sols6 :: EnumProc (SOMetaUnifSol :- CQRP)
implicit_sols6 = fromProvenanceT (nesmgu_enumImplicit implicit_nmgu6)

implicit_lsols6 :: EnumProc (SOMetaUnifSol :- CQRP)
implicit_lsols6 = etake implicit_scale3 implicit_sols6

implicit_rsols6 :: EnumProc SOMetaUnifSol
implicit_rsols6 = raw <$> implicit_lsols6

-- Unfortunately, we choose not to do explicit checks for this case because the solution space is too big to get a representative subset in a reasonable time using any reasonable search order.

implicit6_t1 :: AutomatedTest
implicit6_t1 = check_sol_implicit "Verifying the implicit representation of {x0 -> f3[2](f1[0](),f1[0]()), x1 -> f2[1](f1[0]()), F2[1] -> pi0}"
		(UnifSolution (fromList [(read "x0",read "f3[2](f1[0](),f1[0]())"),(read "x1",read "f2[1](f1[0]())")]) (fromList [(read "F2[1]",read "pi0")]))
		implicit_nmgu6

implicit6_t2 :: AutomatedTest
implicit6_t2 = check_sol_explicit "Verifying the explicit presence of {x0 -> f3[2](f1[0](),f1[0]()), x1 -> f2[1](f1[0]()), F2[1] -> pi0}"
		(UnifSolution (fromList [(read "x0",read "f3[2](f1[0](),f1[0]())"),(read "x1",read "f2[1](f1[0]())")]) (fromList [(read "F2[1]",read "pi0")]))
		implicit_nmgu6
		implicit_scale3

implicit6_t3 :: AutomatedTest
implicit6_t3 = check_not_all_sol "Verifying that not all solutions have {x0 -> f3[2](f1[0](),f1[0]()), x1 -> f2[1](f1[0]()), F2[1] -> pi0}"
		(UnifSolution (fromList [(read "x0",read "f3[2](f1[0](),f1[0]())"),(read "x1",read "f2[1](f1[0]())")]) (fromList [(read "F2[1]",read "pi0")]))
		implicit_nmgu6
		implicit_scale3

implicit6_t4 :: AutomatedTest
implicit6_t4 = check_sol_implicit "Verifying the implicit representation of {x0 -> f3[2](f1[0](),f1[0]()), x1 -> f2[1](f1[0]()), F2[1] -> f1[0]}"
		(UnifSolution (fromList [(read "x0",read "f3[2](f1[0](),f1[0]())"),(read "x1",read "f2[1](f1[0]())")]) (fromList [(read "F2[1]",read "f1[0]")]))
		implicit_nmgu6

implicit6_t5 :: AutomatedTest
implicit6_t5 = check_sol_explicit "Verifying the explicit presence of {x0 -> f3[2](f1[0](),f1[0]()), x1 -> f2[1](f1[0]()), F2[1] -> f1[0]}"
		(UnifSolution (fromList [(read "x0",read "f3[2](f1[0](),f1[0]())"),(read "x1",read "f2[1](f1[0]())")]) (fromList [(read "F2[1]",read "f1[0]")]))
		implicit_nmgu6
		implicit_scale3

implicit6_t6 :: AutomatedTest
implicit6_t6 = check_not_all_sol "Verifying that not all solutions have {x0 -> f3[2](f1[0](),f1[0]()), x1 -> f2[1](f1[0]()), F2[1] -> f1[0]}"
		(UnifSolution (fromList [(read "x0",read "f3[2](f1[0](),f1[0]())"),(read "x1",read "f2[1](f1[0]())")]) (fromList [(read "F2[1]",read "f1[0]")]))
		implicit_nmgu6
		implicit_scale3

implicit6_t7 :: AutomatedTest
implicit6_t7 = check_sol_implicit "Verifying the implicit representation of {x0 -> f3[2](f2[1](f1[0]()),f1[0]()), x1 -> f2[1](f2[1](f1[0]())), F2[1] -> f2[1]{f1[0]}}"
		(UnifSolution (fromList [(read "x0",read "f3[2](f2[1](f1[0]()),f1[0]())"),(read "x1",read "f2[1](f2[1](f1[0]()))")]) (fromList [(read "F2[1]",read "f2[1]{f1[0]}")]))
		implicit_nmgu6

implicit6_t8 :: AutomatedTest
implicit6_t8 = check_sol_explicit "Verifying the explicit presence of {x0 -> f3[2](f2[1](f1[0]()),f1[0]()), x1 -> f2[1](f2[1](f1[0]())), F2[1] -> f2[1]{f1[0]}}"
		(UnifSolution (fromList [(read "x0",read "f3[2](f2[1](f1[0]()),f1[0]())"),(read "x1",read "f2[1](f2[1](f1[0]()))")]) (fromList [(read "F2[1]",read "f2[1]{f1[0]}")]))
		implicit_nmgu6
		implicit_scale3

implicit6_t9 :: AutomatedTest
implicit6_t9 = check_not_all_sol "Verifying that not all solutions have {x0 -> f3[2](f2[1](f1[0]()),f1[0]()), x1 -> f2[1](f2[1](f1[0]())), F2[1] -> f2[1]{f1[0]}}"
		(UnifSolution (fromList [(read "x0",read "f3[2](f2[1](f1[0]()),f1[0]())"),(read "x1",read "f2[1](f2[1](f1[0]()))")]) (fromList [(read "F2[1]",read "f2[1]{f1[0]}")]))
		implicit_nmgu6
		implicit_scale3

implicit6_t10 :: AutomatedTest
implicit6_t10 = check_not_sol_implicit "Verifying the implicit non-representation of {x0 -> f3[2](f2[1](f1[0]()),f1[0]()), x1 -> f2[1](f1[0]())}"
		(UnifSolution (fromList [(read "x0",read "f3[2](f2[1](f1[0]()),f1[0]())"),(read "x1",read "f2[1](f1[0]())")]) (fromList []))
		implicit_nmgu6

implicit6_t11 :: AutomatedTest
implicit6_t11 = check_not_sol_explicit "Verifying the explicit non-presence of {x0 -> f3[2](f2[1](f1[0]()),f1[0]()), x1 -> f2[1](f1[0]())}"
		(UnifSolution (fromList [(read "x0",read "f3[2](f2[1](f1[0]()),f1[0]())"),(read "x1",read "f2[1](f1[0]())")]) (fromList []))
		implicit_nmgu6
		implicit_scale3


implicit_tests6 :: String
--implicit_tests6 = combine_test_results [implicit6_t1,implicit6_t2,implicit6_t3,implicit6_t4,implicit6_t5,implicit6_t6,implicit6_t7,implicit6_t8,implicit6_t9,implicit6_t10,implicit6_t11]
implicit_tests6 = combine_test_results [implicit6_t1,implicit6_t2,implicit6_t3,implicit6_t4,implicit6_t5,implicit6_t6,implicit6_t7,implicit6_t9,implicit6_t10,implicit6_t11]
--implicit_tests6 = combine_test_results [implicit6_t1,implicit6_t4,implicit6_t7,implicit6_t10]


implicit_scale4 :: Int
implicit_scale4 = 100


implicit_eq7_1 :: JState SOMetaMGU
implicit_eq7_1 = (read "x0") >:= (read "F2[1](x1)")

implicit_eq7_2 :: JState SOMetaMGU
implicit_eq7_2 = (read "x1") >:= (read "F3[2](f1[0](),f2[1](f1[0]()))")

implicit_eq7_3 :: JState SOMetaMGU
implicit_eq7_3 = (read "F3[2]") >::= (read "f3[2]{F2[1],f1[0]}")

implicit_mgu7 :: SOMetaMGU
implicit_mgu7 = runESMGU implicit_sig1 (implicit_eq7_1 >> implicit_eq7_2 >> implicit_eq7_3)


implicit_nmgu7 :: SOMetaNMGU
implicit_nmgu7 = fromJust (normalize_esmgu implicit_mgu7)

implicit_sols7 :: EnumProc (SOMetaUnifSol :- CQRP)
implicit_sols7 = fromProvenanceT (nesmgu_enumImplicit implicit_nmgu7)

implicit_lsols7 :: EnumProc (SOMetaUnifSol :- CQRP)
implicit_lsols7 = etake implicit_scale4 implicit_sols7

implicit_rsols7 :: EnumProc SOMetaUnifSol
implicit_rsols7 = raw <$> implicit_lsols7

implicit7_t1 :: AutomatedTest
implicit7_t1 = check_sol_implicit "Verifying the implicit representation of {x0 -> f1[0](), x1 -> f3[2](f1[0](),f1[0]()), F3[2] -> f3[2]{f1[0],f1[0]}, F2[1] -> f1[0]}"
		(UnifSolution (fromList [(read "x0",read "f1[0]()"),(read "x1",read "f3[2](f1[0](),f1[0]())")]) (fromList [(read "F3[2]",read "f3[2]{f1[0],f1[0]}"),(read "F2[1]",read "f1[0]")]))
		implicit_nmgu7

implicit7_t2 :: AutomatedTest
implicit7_t2 = check_sol_explicit "Verifying the explicit presence of {x0 -> f1[0](), x1 -> f3[2](f1[0](),f1[0]()), F3[2] -> f3[2]{f1[0],f1[0]}, F2[1] -> f1[0]}"
		(UnifSolution (fromList [(read "x0",read "f1[0]()"),(read "x1",read "f3[2](f1[0](),f1[0]())")]) (fromList [(read "F3[2]",read "f3[2]{f1[0],f1[0]}"),(read "F2[1]",read "f1[0]")]))
		implicit_nmgu7
		implicit_scale4

implicit7_t3 :: AutomatedTest
implicit7_t3 = check_not_all_sol "Verifying that not all solutions have {x0 -> f1[0](), x1 -> f3[2](f1[0](),f1[0]()), F3[2] -> f3[2]{f1[0],f1[0]}, F2[1] -> f1[0]}"
		(UnifSolution (fromList [(read "x0",read "f1[0]()"),(read "x1",read "f3[2](f1[0](),f1[0]())")]) (fromList [(read "F3[2]",read "f3[2]{f1[0],f1[0]}"),(read "F2[1]",read "f1[0]")]))
		implicit_nmgu7
		implicit_scale4

implicit7_t4 :: AutomatedTest
implicit7_t4 = check_sol_implicit "Verifying the implicit representation of {x0 -> f3[2](f1[0](),f1[0]()), x1 -> f3[2](f1[0](),f1[0]()), F3[2] -> f3[2]{pi0,f1[0]}, F2[1] -> pi0}"
		(UnifSolution (fromList [(read "x0",read "f3[2](f1[0](),f1[0]())"),(read "x1",read "f3[2](f1[0](),f1[0]())")]) (fromList [(read "F3[2]",read "f3[2]{pi0,f1[0]}"),(read "F2[1]",read "pi0")]))
		implicit_nmgu7

implicit7_t5 :: AutomatedTest
implicit7_t5 = check_sol_explicit "Verifying the explicit presence of {x0 -> f3[2](f1[0](),f1[0]()), x1 -> f3[2](f1[0](),f1[0]()), F3[2] -> f3[2]{pi0,f1[0]}, F2[1] -> pi0}"
		(UnifSolution (fromList [(read "x0",read "f3[2](f1[0](),f1[0]())"),(read "x1",read "f3[2](f1[0](),f1[0]())")]) (fromList [(read "F3[2]",read "f3[2]{pi0,f1[0]}"),(read "F2[1]",read "pi0")]))
		implicit_nmgu7
		implicit_scale4

implicit7_t6 :: AutomatedTest
implicit7_t6 = check_not_all_sol "Verifying that not all solutions have {x0 -> f3[2](f1[0](),f1[0]()), x1 -> f3[2](f1[0](),f1[0]()), F3[2] -> f3[2]{pi0,f1[0]}, F2[1] -> pi0}"
		(UnifSolution (fromList [(read "x0",read "f3[2](f1[0](),f1[0]())"),(read "x1",read "f3[2](f1[0](),f1[0]())")]) (fromList [(read "F3[2]",read "f3[2]{pi0,f1[0]}"),(read "F2[1]",read "pi0")]))
		implicit_nmgu7
		implicit_scale4

implicit7_t7 :: AutomatedTest
implicit7_t7 = check_not_sol_implicit "Verifying the implicit non-representation of {x0 -> f1[0](), x1 -> f3[2](f2[1](f1[0]()),f1[0]())}"
		(UnifSolution (fromList [(read "x0",read "f1[0]()"),(read "x1",read "f3[2](f2[1](f1[0]()),f1[0]())")]) (fromList []))
		implicit_nmgu7

implicit7_t8 :: AutomatedTest
implicit7_t8 = check_not_sol_explicit "Verifying the explicit non-presence of {x0 -> f1[0](), x1 -> f3[2](f2[1](f1[0]()),f1[0]())}"
		(UnifSolution (fromList [(read "x0",read "f1[0]()"),(read "x1",read "f3[2](f2[1](f1[0]()),f1[0]())")]) (fromList []))
		implicit_nmgu7
		implicit_scale4

implicit7_t9 :: AutomatedTest
implicit7_t9 = check_not_sol_implicit "Verifying the implicit non-representation of {x0 -> f1[0](), F3[2] -> f3[2]{pi0,f1[0]}}"
		(UnifSolution (fromList [(read "x0",read "f1[0]()")]) (fromList [(read "F3[2]",read "f3[2]{pi0,f1[0]}")]))
		implicit_nmgu7

implicit7_t10 :: AutomatedTest
implicit7_t10 = check_not_sol_explicit "Verifying the explicit non-presence of {x0 -> f1[0](), F3[2] -> f3[2]{pi0,f1[0]}}"
		(UnifSolution (fromList [(read "x0",read "f1[0]()")]) (fromList [(read "F3[2]",read "f3[2]{pi0,f1[0]}")]))
		implicit_nmgu7
		implicit_scale4

implicit7_t11 :: AutomatedTest
implicit7_t11 = check_not_sol_implicit "Verifying the implicit non-representation of {x0 -> f1[0](), F2[1] -> pi0}"
		(UnifSolution (fromList [(read "x0",read "f1[0]()")]) (fromList [(read "F2[1]",read "pi0")]))
		implicit_nmgu7

implicit7_t12 :: AutomatedTest
implicit7_t12 = check_not_sol_explicit "Verifying the explicit non-presence of {x0 -> f1[0](), F2[1] -> pi0}"
		(UnifSolution (fromList [(read "x0",read "f1[0]()")]) (fromList [(read "F2[1]",read "pi0")]))
		implicit_nmgu7
		implicit_scale4

-- These are actually compatible, because x1 has the same value in the first two cases.
--implicit7_t13 :: AutomatedTest
--implicit7_t13 = check_not_sol_implicit "Verifying the implicit non-representation of {x1 -> f3[2](f1[0](),f1[0]()), F3[2] -> f3[2]{pi0,f1[0]}}"
--		(UnifSolution (fromList [(read "x1",read "f3[2](f1[0](),f1[0]())")]) (fromList [(read "F3[2]",read "f3[2]{pi0,f1[0]}")]))
--		implicit_nmgu7

--implicit7_t14 :: AutomatedTest
--implicit7_t14 = check_not_sol_explicit "Verifying the explicit non-presence of {x1 -> f3[2](f1[0](),f1[0]()), F3[2] -> f3[2]{pi0,f1[0]}}"
--		(UnifSolution (fromList [(read "x1",read "f3[2](f1[0](),f1[0]())")]) (fromList [(read "F3[2]",read "f3[2]{pi0,f1[0]}")]))
--		implicit_nmgu7
--		implicit_scale4

--implicit7_t15 :: AutomatedTest
--implicit7_t15 = check_not_sol_implicit "Verifying the implicit non-representation of {x1 -> f3[2](f1[0](),f1[0]()), F2[1] -> pi0}"
--		(UnifSolution (fromList [(read "x1",read "f3[2](f1[0](),f1[0]())")]) (fromList [(read "F2[1]",read "pi0")]))
--		implicit_nmgu7

--implicit7_t16 :: AutomatedTest
--implicit7_t16 = check_not_sol_explicit "Verifying the explicit non-presence of {x1 -> f3[2](f1[0](),f1[0]()), F2[1] -> pi0}"
--		(UnifSolution (fromList [(read "x1",read "f3[2](f1[0](),f1[0]())")]) (fromList [(read "F2[1]",read "pi0")]))
--		implicit_nmgu7
--		implicit_scale4

implicit7_t17 :: AutomatedTest
implicit7_t17 = check_not_sol_implicit "Verifying the implicit non-representation of {F3[2] -> f3[2]{f1[0],f1[0]}, F2[1] -> pi0}"
		(UnifSolution (fromList []) (fromList [(read "F3[2]",read "f3[2]{f1[0],f1[0]}"),(read "F2[1]",read "pi0")]))
		implicit_nmgu7

implicit7_t18 :: AutomatedTest
implicit7_t18 = check_not_sol_explicit "Verifying the explicit non-presence of {F3[2] -> f3[2]{f1[0],f1[0]}, F2[1] -> pi0}"
		(UnifSolution (fromList []) (fromList [(read "F3[2]",read "f3[2]{f1[0],f1[0]}"),(read "F2[1]",read "pi0")]))
		implicit_nmgu7
		implicit_scale4

implicit_tests7 :: String
implicit_tests7 = combine_test_results [implicit7_t1,implicit7_t2,implicit7_t3,implicit7_t4,implicit7_t5,implicit7_t6,implicit7_t7,implicit7_t8,implicit7_t9,implicit7_t10,implicit7_t11,implicit7_t12,implicit7_t17,implicit7_t18]


implicit_eq8_1 :: JState SOMetaMGU
implicit_eq8_1 = (read "x0") >:= (read "F2[1](f1[0]())")

implicit_mgu8 :: SOMetaMGU
implicit_mgu8 = runESMGU implicit_sig1 (implicit_eq8_1)

implicit_nmgu8 :: SOMetaNMGU
implicit_nmgu8 = fromJust (normalize_esmgu implicit_mgu8)

implicit_sols8 :: EnumProc (SOMetaUnifSol :- CQRP)
implicit_sols8 = fromProvenanceT (nesmgu_enumImplicit implicit_nmgu8)

implicit_lsols8 :: EnumProc (SOMetaUnifSol :- CQRP)
implicit_lsols8 = etake implicit_scale3 implicit_sols8

implicit_rsols8 :: EnumProc SOMetaUnifSol
implicit_rsols8 = raw <$> implicit_lsols8

-- We only check implicitly for this one, as it is quite complex instantiations that explicitly would take long to appear.
implicit8_t1 :: AutomatedTest
implicit8_t1 = check_sol_implicit "Verifying the implicit representation of {x0 -> f3[2](f1[0](),f1[0]()), F2[1] -> f3[2]{pi0,pi0}}"
		(UnifSolution (fromList [(read "x0",read "f3[2](f1[0](),f1[0]())")]) (fromList [(read "F2[1]",read "f3[2]{pi0,pi0}")]))
		implicit_nmgu8

implicit8_t2 :: AutomatedTest
implicit8_t2 = check_sol_implicit "Verifying the implicit representation of {x0 -> f3[2](f1[0](),f1[0]()), F2[1] -> f3[2]{pi0,f1[0]}}"
		(UnifSolution (fromList [(read "x0",read "f3[2](f1[0](),f1[0]())")]) (fromList [(read "F2[1]",read "f3[2]{pi0,f1[0]}")]))
		implicit_nmgu8

implicit8_t3 :: AutomatedTest
implicit8_t3 = check_sol_implicit "Verifying the implicit representation of {x0 -> f3[2](f2[1](f1[0]()),f2[1](f1[0]())), F2[1] -> f3[2]{f2[1]{pi0},f2[1]{pi0}}}"
		(UnifSolution (fromList [(read "x0",read "f3[2](f2[1](f1[0]()),f2[1](f1[0]()))")]) (fromList [(read "F2[1]",read "f3[2]{f2[1]{pi0},f2[1]{pi0}}")]))
		implicit_nmgu8

implicit8_t4 :: AutomatedTest
implicit8_t4 = check_sol_implicit "Verifying the implicit representation of {x0 -> f3[2](f2[1](f1[0]()),f1[0]()), F2[1] -> f3[2]{f2[1]{f1[0]},pi0}}"
		(UnifSolution (fromList [(read "x0",read "f3[2](f2[1](f1[0]()),f1[0]())")]) (fromList [(read "F2[1]",read "f3[2]{f2[1]{f1[0]},pi0}")]))
		implicit_nmgu8

implicit8_t5 :: AutomatedTest
implicit8_t5 = check_not_sol_implicit "Verifying the implicit non-representation of {x0 -> f3[2](f2[1](f1[0]()),f1[0]()), F2[1] -> f3[2]{pi0,pi0}}"
		(UnifSolution (fromList [(read "x0",read "f3[2](f2[1](f1[0]()),f1[0]())")]) (fromList [(read "F2[1]",read "f3[2]{pi0,pi0}")]))
		implicit_nmgu8

-- What if we don't give it the hint of what the second-order instantiation might look like, so that it needs to infer composite instantiations for them. This will fail in not-so-naive implementations.
implicit8_t6 :: AutomatedTest
implicit8_t6 = check_sol_implicit "Verifying the implicit representation of {x0 -> f3[2](f1[0](),f1[0]())}"
		(UnifSolution (fromList [(read "x0",read "f3[2](f1[0](),f1[0]())")]) (fromList []))
		implicit_nmgu8

implicit8_t7 :: AutomatedTest
implicit8_t7 = check_sol_implicit "Verifying the implicit representation of {x0 -> f3[2](f2[1](f1[0]()),f1[0]())}"
		(UnifSolution (fromList [(read "x0",read "f3[2](f2[1](f1[0]()),f1[0]())")]) (fromList []))
		implicit_nmgu8



implicit_tests8 :: String
implicit_tests8 = combine_test_results [implicit8_t1,implicit8_t2,implicit8_t3,implicit8_t4,implicit8_t5,implicit8_t6,implicit8_t7]




implicit_test :: IO ()
implicit_test = putStr "EXAMPLE 1\n\n" >> putStr implicit_tests1 >>
		putStr "EXAMPLE 2\n\n" >> putStr implicit_tests2 >>
		putStr "EXAMPLE 3\n\n" >> putStr implicit_tests3 >>
		putStr "EXAMPLE 4\n\n" >> putStr implicit_tests4 >>
		putStr "EXAMPLE 5\n\n" >> putStr implicit_tests5 >>
		putStr "EXAMPLE 6\n\n" >> putStr implicit_tests6 >>
		putStr "EXAMPLE 7\n\n" >> putStr implicit_tests7 >>
		putStr "EXAMPLE 8\n\n" >> putStr implicit_tests8
