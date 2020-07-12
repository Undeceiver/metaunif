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
{-# LANGUAGE TupleSections #-}
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
import Control.Monad.ST
import DependencyGraph
import Identifier
import Algorithm


-- Implicit solution handling tests.
-- We define implicit solutions using the (>:=) and (>::=) operators and then check that they work properly.

{-|
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

|-}




-- Dependency graph operation tests
-- Note that on the tests we always assume that we start from an empty graph, to build the StateT.
newtype RTestSOMetaUnifDGraph s = RTestSOMetaUnifDGraph {fromMudg :: SOMetaUnifDGraph s}

lens_RTestSOMetaUnifDGraph :: Lens' (RTestSOMetaUnifDGraph s) (SOMetaUnifDGraph s)
lens_RTestSOMetaUnifDGraph f rrmudg = fmap (\rmudg -> RTestSOMetaUnifDGraph rmudg) (f (fromMudg rrmudg))

emptyRMUDG :: SOMetaSignature -> RTestSOMetaUnifDGraph s
emptyRMUDG sig = RTestSOMetaUnifDGraph (emptyVDGraph sig)

on_vdgraph :: StateT (ESUnifVDGraph s CTermF OPredicate OFunction OVariable SOMVariable UnifVariable) (ST s) a -> StateT (RTestSOMetaUnifDGraph s) (ST s) a
on_vdgraph = mzoom lens_RTestSOMetaUnifDGraph

on_dgraph :: StateT (ESUnifDGraph s CTermF OFunction OVariable SOMVariable UnifVariable) (ST s) a -> StateT (RTestSOMetaUnifDGraph s) (ST s) a
on_dgraph = mzoom (lens_RTestSOMetaUnifDGraph . lens_esunifdgraph_dgraph)

show_mudg :: SOMetaSignature -> (forall s. StateT (RTestSOMetaUnifDGraph s) (ST s) a) -> IO ()
--show_mudg s = putStr (runST ((show_eqdgraph . esunifdgraph . fromESUnifNDGraph . fromMudg . snd) <$> (runStateT s emptyRMUDG)))
show_mudg sig s = putStr (runST (fst <$> (runStateT (s >> (mzoom lens_RTestSOMetaUnifDGraph show_esuvdg)) (emptyRMUDG sig))))

-- Check that horizontal edge exists / does not exist
check_hfoedge :: SOMetaSignature -> String -> (forall s. StateT (RTestSOMetaUnifDGraph s) (ST s) a) -> SOMetatermF -> [SOMetaTermDependant] -> SOMetaTermDependant -> AutomatedTest
check_hfoedge sig title stmudg h ss t = AT title (if result then (ATR True "The horizontal edge was correctly found.") else (ATR False "Could not find the expected horizontal edge.")) where hid = relbwEqDGSoId h; sids = Prelude.map relbwEqDGFoId ss; tid = relbwEqDGFoId t; checked = do {stmudg; on_dgraph (st_checkEqDGFOEdge hid sids tid)}; result = getStateTSTValue checked (emptyRMUDG sig)

check_hsoedge :: SOMetaSignature -> String -> (forall s. StateT (RTestSOMetaUnifDGraph s) (ST s) a) -> SOMetatermF -> [SOMetatermF] -> SOMetatermF -> AutomatedTest
check_hsoedge sig title stmudg h ss t = AT title (if result then (ATR True "The horizontal edge was correctly found.") else (ATR False "Could not find the expected horizontal edge.")) where hid = relbwEqDGSoId h; sids = Prelude.map relbwEqDGSoId ss; tid = relbwEqDGSoId t; checked = do {stmudg; on_dgraph (st_checkEqDGSOEdge hid sids tid)}; result = getStateTSTValue checked (emptyRMUDG sig)

check_not_hfoedge :: SOMetaSignature -> String -> (forall s. StateT (RTestSOMetaUnifDGraph s) (ST s) a) -> SOMetatermF -> [SOMetaTermDependant] -> SOMetaTermDependant -> AutomatedTest
check_not_hfoedge sig title stmudg h ss t = AT title (if result then (ATR True "The horizontal edge was correctly not found.") else (ATR False "Found the horizontal edge, but we should not have done so.")) where hid = relbwEqDGSoId h; sids = Prelude.map relbwEqDGFoId ss; tid = relbwEqDGFoId t; checked = do {stmudg; on_dgraph (st_checkEqDGFOEdge hid sids tid)}; result = not (getStateTSTValue checked (emptyRMUDG sig))

check_not_hsoedge :: SOMetaSignature -> String -> (forall s. StateT (RTestSOMetaUnifDGraph s) (ST s) a) -> SOMetatermF -> [SOMetatermF] -> SOMetatermF -> AutomatedTest
check_not_hsoedge sig title stmudg h ss t = AT title (if result then (ATR True "The horizontal edge was correctly not found.") else (ATR False "Found the horizontal edge, but we should not have done so.")) where hid = relbwEqDGSoId h; sids = Prelude.map relbwEqDGSoId ss; tid = relbwEqDGSoId t; checked = do {stmudg; on_dgraph (st_checkEqDGSOEdge hid sids tid)}; result = not (getStateTSTValue checked (emptyRMUDG sig))


-- Check that vertical edge exists / does not exist
check_vedge :: SOMetaSignature -> String -> (forall s. StateT (RTestSOMetaUnifDGraph s) (ST s) a) -> SOMetaTermDependant -> SOMetaTermDependant -> AutomatedTest
check_vedge sig title stmudg s t = AT title (if result then (ATR True "The vertical edge was correctly found.") else (ATR False "Could not find the expected vertical edge.")) where sid = relbwEqDGFoId s; tid = relbwEqDGFoId t; checked = do {stmudg; on_vdgraph (checkVFoEdge sid tid)}; result = getStateTSTValue checked (emptyRMUDG sig)

check_not_vedge :: SOMetaSignature -> String -> (forall s. StateT (RTestSOMetaUnifDGraph s) (ST s) a) -> SOMetaTermDependant -> SOMetaTermDependant -> AutomatedTest
check_not_vedge sig title stmudg s t = AT title (if result then (ATR True "The vertical edge was correctly not found.") else (ATR False "Found the vertical edge, but we should not have done so.")) where sid = relbwEqDGFoId s; tid = relbwEqDGFoId t; checked = do {stmudg; on_vdgraph (checkVFoEdge sid tid)}; result = not (getStateTSTValue checked (emptyRMUDG sig))

-- Check that two elements are equivalent / not equivalent
check_foequiv :: SOMetaSignature -> String -> (forall s. StateT (RTestSOMetaUnifDGraph s) (ST s) a) -> SOMetaTermDependant -> SOMetaTermDependant -> AutomatedTest
check_foequiv sig title stmudg a b = AT title (if result then (ATR True "The two elements were indeed found to be equivalent.") else (ATR False "The two elements were not equivalent, but they should be.")) where aid = relbwEqDGFoId a; bid = relbwEqDGFoId b; checked = do {stmudg; on_dgraph (eqSTRelativeIds aid bid)}; result = getStateTSTValue checked (emptyRMUDG sig)

check_soequiv :: SOMetaSignature -> String -> (forall s. StateT (RTestSOMetaUnifDGraph s) (ST s) a) -> SOMetatermF -> SOMetatermF -> AutomatedTest
check_soequiv sig title stmudg a b = AT title (if result then (ATR True "The two elements were indeed found to be equivalent.") else (ATR False "The two elements were not equivalent, but they should be.")) where aid = relbwEqDGSoId a; bid = relbwEqDGSoId b; checked = do {stmudg; on_dgraph (eqSTRelativeIds aid bid)}; result = getStateTSTValue checked (emptyRMUDG sig)

check_not_foequiv :: SOMetaSignature -> String -> (forall s. StateT (RTestSOMetaUnifDGraph s) (ST s) a) -> SOMetaTermDependant -> SOMetaTermDependant -> AutomatedTest
check_not_foequiv sig title stmudg a b = AT title (if result then (ATR True "The two elements were indeed found to be not equivalent.") else (ATR False "The two elements were equivalent, but they should not be.")) where aid = relbwEqDGFoId a; bid = relbwEqDGFoId b; checked = do {stmudg; on_dgraph (eqSTRelativeIds aid bid)}; result = not (getStateTSTValue checked (emptyRMUDG sig))

check_not_soequiv :: SOMetaSignature -> String -> (forall s. StateT (RTestSOMetaUnifDGraph s) (ST s) a) -> SOMetatermF -> SOMetatermF -> AutomatedTest
check_not_soequiv sig title stmudg a b = AT title (if result then (ATR True "The two elements were indeed found to be not equivalent.") else (ATR False "The two elements were equivalent, but they should not be.")) where aid = relbwEqDGSoId a; bid = relbwEqDGSoId b; checked = do {stmudg; on_dgraph (eqSTRelativeIds aid bid)}; result = not (getStateTSTValue checked (emptyRMUDG sig))


-- Checking with expressions
check_foexp :: SOMetaSignature -> String -> (forall s. StateT (RTestSOMetaUnifDGraph s) (ST s) a) -> SOMetaUnifFOExp -> SOMetaTermDependant -> AutomatedTest
check_foexp sig title stmudg exp t = AT title (if result then (ATR True "The dependant matches the expression in the graph.") else (ATR False "The dependant does not match the expression in the graph, but it should.")) where checked = do {stmudg; on_vdgraph (match_foexp exp (relbwEqDGFoId t))}; result = getStateTSTValue checked (emptyRMUDG sig)

check_not_foexp :: SOMetaSignature -> String -> (forall s. StateT (RTestSOMetaUnifDGraph s) (ST s) a) -> SOMetaUnifFOExp -> SOMetaTermDependant -> AutomatedTest
check_not_foexp sig title stmudg exp t = AT title (if result then (ATR True "The dependant does not match the expression in the graph.") else (ATR False "The dependant matches the expression in the graph, but it should not.")) where checked = do {stmudg; on_vdgraph (match_foexp exp (relbwEqDGFoId t))}; result = not (getStateTSTValue checked (emptyRMUDG sig))

check_soexp :: SOMetaSignature -> String -> (forall s. StateT (RTestSOMetaUnifDGraph s) (ST s) a) -> SOMetaUnifSOExp -> SOMetatermF -> AutomatedTest
check_soexp sig title stmudg exp t = AT title (if result then (ATR True "The dependant matches the expression in the graph.") else (ATR False "The dependant does not match the expression in the graph, but it should.")) where checked = do {stmudg; on_vdgraph (match_soexp exp (relbwEqDGSoId t))}; result = getStateTSTValue checked (emptyRMUDG sig)

check_not_soexp :: SOMetaSignature -> String -> (forall s. StateT (RTestSOMetaUnifDGraph s) (ST s) a) -> SOMetaUnifSOExp -> SOMetatermF -> AutomatedTest
check_not_soexp sig title stmudg exp t = AT title (if result then (ATR True "The dependant does not match the expression in the graph.") else (ATR False "The dependant matches the expression in the graph, but it should not.")) where checked = do {stmudg; on_vdgraph (match_soexp exp (relbwEqDGSoId t))}; result = not (getStateTSTValue checked (emptyRMUDG sig))


-- For answer sets
check_min_as :: String -> Int -> AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution -> AutomatedTest
check_min_as title n as = if l < n then (AT title (ATR False ("Expected at least " ++ (show n) ++ " results, but could only find " ++ (show l) ++ "."))) else (AT title (ATR True ("Correctly found at least " ++ (show n) ++ " results."))) where l = uns_produce_next (elength (etake n ((implicitOnly as) \$ ())))

check_max_as :: String -> Int -> AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution -> AutomatedTest
check_max_as title n as = if l > n then (AT title (ATR False ("Expected at most " ++ (show n) ++ " results, but found " ++ (show l) ++ "."))) else (AT title (ATR True ("Correctly found less than " ++ (show n) ++ " results."))) where l = uns_produce_next (elength (etake (n+1) ((implicitOnly as) \$ ())))

check_exactly_as :: String -> Int -> AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution -> AutomatedTest
check_exactly_as title n as = if l /= n then (AT title (ATR False ("Expected exactly " ++ (show n) ++ " results, but found " ++ (show l) ++ " instead."))) else (AT title (ATR True ("Correctly found exactly " ++ (show n) ++ " results."))) where l = uns_produce_next (elength (etake (n+1) ((implicitOnly as) \$ ())))


check_any_resuvdg :: Int -> String -> (forall a. String -> (forall s. StateT (RTestSOMetaUnifDGraph s) (ST s) a) -> AutomatedTest) -> AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution -> AutomatedTest
check_any_resuvdg maxen title ftest as = case filtered of {EnumProc.Empty -> AT title (ATR False ("None of the first " ++ (show maxen) ++ " results produced passed the check.")); Produce at _ -> at} where imp = etake maxen ((implicitOnly as) \$ ()); impat = (\resuvdg -> ftest title (StateT (\rtest -> (((),) . RTestSOMetaUnifDGraph) <$> (fromRESUnifVDGraph resuvdg)))) <$> imp; filtered = uns_ecollapse (efilter (\(AT title (ATR res str)) -> res) impat)

check_all_resuvdg :: Int -> String -> (forall a. String -> (forall s. StateT (RTestSOMetaUnifDGraph s) (ST s) a) -> AutomatedTest) -> AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution -> AutomatedTest
check_all_resuvdg maxen title ftest as = case filtered of {EnumProc.Empty -> AT title (ATR True ("All of the first " ++ (show maxen) ++ " results produced passed the check.")); Produce at _ -> AT title (ATR False ("Found a result amongst the first " ++ (show maxen) ++ " produced that did not pass the check."))} where imp = etake maxen ((implicitOnly as) \$ ()); impat = (\resuvdg -> ftest title (StateT (\rtest -> (((),) . RTestSOMetaUnifDGraph) <$> (fromRESUnifVDGraph resuvdg)))) <$> imp; filtered = uns_ecollapse (efilter (\(AT title (ATR res str)) -> not res) impat)


-- Vertical commute tests


-- Test 1
vcommute1_term1 :: SOMetaTermDependant
vcommute1_term1 = read "u0 x0"

vcommute1_tid1 :: SOMetaUnifRelFoId s
vcommute1_tid1 = relbwEqDGFoId vcommute1_term1

vcommute1_term2 :: SOMetaTermDependant
vcommute1_term2 = read "u0 x1"

vcommute1_tid2 :: SOMetaUnifRelFoId s
vcommute1_tid2 = relbwEqDGFoId vcommute1_term2

vcommute1_term3 :: SOMetaTermDependant
vcommute1_term3 = read "u1 u0 x1"

vcommute1_tid3 :: SOMetaUnifRelFoId s
vcommute1_tid3 = relbwEqDGFoId vcommute1_term3

vcommute1_term4 :: SOMetaTermDependant
vcommute1_term4 = read "u1 u0 x0"

vcommute1_tid4 :: SOMetaUnifRelFoId s
vcommute1_tid4 = relbwEqDGFoId vcommute1_term4

vcommute1_soterm1 :: SOMetatermF
vcommute1_soterm1 = read "f1[1]"

vcommute1_sotid1 :: SOMetaUnifRelSoId s
vcommute1_sotid1 = relbwEqDGSoId vcommute1_soterm1

vcommute1_sig :: SOMetaSignature
vcommute1_sig = SOSignature (Signature [] [EnumProc.Empty,read "f1[1]" --> EnumProc.Empty] (read "x0" --> read "x1" --> EnumProc.Empty)) EnumProc.Empty

vcommute1_mudg1 :: StateT (RTestSOMetaUnifDGraph s) (ST s) _
vcommute1_mudg1 = do {on_dgraph (newEqDGFOEdge vcommute1_sotid1 [vcommute1_tid1] vcommute1_tid2); on_vdgraph (addVFoEdge vcommute1_tid2 vcommute1_tid3)}

vcommute1_mudg2 :: StateT (RTestSOMetaUnifDGraph s) (ST s) _
vcommute1_mudg2 = do {vcommute1_mudg1; on_vdgraph metaunif_vertical_commute}

vcommute1_t1 :: AutomatedTest
vcommute1_t1 = check_hfoedge vcommute1_sig "Checking the source horizontal edge is there before" vcommute1_mudg1 vcommute1_soterm1 [vcommute1_term1] vcommute1_term2

vcommute1_t2 :: AutomatedTest
vcommute1_t2 = check_vedge vcommute1_sig "Checking the source vertical edge is there before" vcommute1_mudg1 vcommute1_term2 vcommute1_term3

vcommute1_t3 :: AutomatedTest
vcommute1_t3 = check_not_hfoedge vcommute1_sig "Checking the commuted horizontal edge is not there before" vcommute1_mudg1 vcommute1_soterm1 [vcommute1_term4] vcommute1_term3

vcommute1_t4 :: AutomatedTest
vcommute1_t4 = check_not_vedge vcommute1_sig "Checking the commuted vertical edge is not there before" vcommute1_mudg1 vcommute1_term1 vcommute1_term4

vcommute1_t5 :: AutomatedTest
vcommute1_t5 = check_hfoedge vcommute1_sig "Checking the source horizontal edge is there after" vcommute1_mudg2 vcommute1_soterm1 [vcommute1_term1] vcommute1_term2

vcommute1_t6 :: AutomatedTest
vcommute1_t6 = check_vedge vcommute1_sig "Checking the source vertical edge is there after" vcommute1_mudg2 vcommute1_term2 vcommute1_term3

vcommute1_t7 :: AutomatedTest
vcommute1_t7 = check_hfoedge vcommute1_sig "Checking the commuted horizontal edge is there after" vcommute1_mudg2 vcommute1_soterm1 [vcommute1_term4] vcommute1_term3

vcommute1_t8 :: AutomatedTest
vcommute1_t8 = check_vedge vcommute1_sig "Checking the commuted vertical edge is there after" vcommute1_mudg2 vcommute1_term1 vcommute1_term4

vcommute_tests1 :: String
vcommute_tests1 = combine_test_results [vcommute1_t1,vcommute1_t2,vcommute1_t3,vcommute1_t4,vcommute1_t5,vcommute1_t6,vcommute1_t7,vcommute1_t8]


-- Test 2
vcommute2_term1 :: SOMetaTermDependant
vcommute2_term1 = read "u0 x0"

vcommute2_tid1 :: SOMetaUnifRelFoId s
vcommute2_tid1 = relbwEqDGFoId vcommute2_term1

vcommute2_term2 :: SOMetaTermDependant
vcommute2_term2 = read "u0 x1"

vcommute2_tid2 :: SOMetaUnifRelFoId s
vcommute2_tid2 = relbwEqDGFoId vcommute2_term2

vcommute2_term3 :: SOMetaTermDependant
vcommute2_term3 = read "u0 x2"

vcommute2_tid3 :: SOMetaUnifRelFoId s
vcommute2_tid3 = relbwEqDGFoId vcommute2_term3

vcommute2_term4 :: SOMetaTermDependant
vcommute2_term4 = read "u1 u0 x2"

vcommute2_tid4 :: SOMetaUnifRelFoId s
vcommute2_tid4 = relbwEqDGFoId vcommute2_term4

vcommute2_term5 :: SOMetaTermDependant
vcommute2_term5 = read "u1 u0 x0"

vcommute2_tid5 :: SOMetaUnifRelFoId s
vcommute2_tid5 = relbwEqDGFoId vcommute2_term5

vcommute2_term6 :: SOMetaTermDependant
vcommute2_term6 = read "u1 u0 x1"

vcommute2_tid6 :: SOMetaUnifRelFoId s
vcommute2_tid6 = relbwEqDGFoId vcommute2_term6

vcommute2_soterm1 :: SOMetatermF
vcommute2_soterm1 = read "f1[2]"

vcommute2_sotid1 :: SOMetaUnifRelSoId s
vcommute2_sotid1 = relbwEqDGSoId vcommute2_soterm1

vcommute2_sig :: SOMetaSignature
vcommute2_sig = SOSignature (Signature [] [EnumProc.Empty,EnumProc.Empty,read "f1[2]" --> EnumProc.Empty] (read "x0" --> read "x1" --> read "x2" --> EnumProc.Empty)) EnumProc.Empty

vcommute2_mudg1 :: StateT (RTestSOMetaUnifDGraph s) (ST s) _
vcommute2_mudg1 = do {on_dgraph (newEqDGFOEdge vcommute2_sotid1 [vcommute2_tid1,vcommute2_tid2] vcommute2_tid3); on_vdgraph (addVFoEdge vcommute2_tid3 vcommute2_tid4)}

vcommute2_mudg2 :: StateT (RTestSOMetaUnifDGraph s) (ST s) _
vcommute2_mudg2 = do {vcommute2_mudg1; on_vdgraph metaunif_vertical_commute}

vcommute2_t1 :: AutomatedTest
vcommute2_t1 = check_hfoedge vcommute2_sig "Checking the source horizontal edge is there before" vcommute2_mudg1 vcommute2_soterm1 [vcommute2_term1,vcommute2_term2] vcommute2_term3

vcommute2_t2 :: AutomatedTest
vcommute2_t2 = check_vedge vcommute2_sig "Checking the source vertical edge is there before" vcommute2_mudg1 vcommute2_term3 vcommute2_term4

vcommute2_t3 :: AutomatedTest
vcommute2_t3 = check_not_hfoedge vcommute2_sig "Checking the commuted horizontal edge is not there before" vcommute2_mudg1 vcommute2_soterm1 [vcommute2_term5,vcommute2_term6] vcommute2_term4

vcommute2_t4 :: AutomatedTest
vcommute2_t4 = check_not_vedge vcommute2_sig "Checking the commuted vertical edge is not there before" vcommute2_mudg1 vcommute2_term1 vcommute2_term5

vcommute2_t5 :: AutomatedTest
vcommute2_t5 = check_not_vedge vcommute2_sig "Checking the commuted vertical edge is not there before" vcommute2_mudg1 vcommute2_term2 vcommute2_term6

vcommute2_t6 :: AutomatedTest
vcommute2_t6 = check_hfoedge vcommute2_sig "Checking the source horizontal edge is there after" vcommute2_mudg2 vcommute2_soterm1 [vcommute2_term1,vcommute2_term2] vcommute2_term3

vcommute2_t7 :: AutomatedTest
vcommute2_t7 = check_vedge vcommute2_sig "Checking the source vertical edge is there after" vcommute2_mudg2 vcommute2_term3 vcommute2_term4

vcommute2_t8 :: AutomatedTest
vcommute2_t8 = check_hfoedge vcommute2_sig "Checking the commuted horizontal edge is there after" vcommute2_mudg2 vcommute2_soterm1 [vcommute2_term5,vcommute2_term6] vcommute2_term4

vcommute2_t9 :: AutomatedTest
vcommute2_t9 = check_vedge vcommute2_sig "Checking the commuted vertical edge is there after" vcommute2_mudg2 vcommute2_term1 vcommute2_term5

vcommute2_t10 :: AutomatedTest
vcommute2_t10 = check_vedge vcommute2_sig "Checking the commuted vertical edge is there after" vcommute2_mudg2 vcommute2_term2 vcommute2_term6

-- Additional tests, verifying no weird crossings have happened.
vcommute2_t11 :: AutomatedTest
vcommute2_t11 = check_not_hfoedge vcommute2_sig "Checking no crossed horizontal edge is there after" vcommute2_mudg2 vcommute2_soterm1 [vcommute2_term6,vcommute2_term5] vcommute2_term4

vcommute2_t12 :: AutomatedTest
vcommute2_t12 = check_not_vedge vcommute2_sig "Checking no crossed vertical edge is there after" vcommute2_mudg2 vcommute2_term1 vcommute2_term6

vcommute2_t13 :: AutomatedTest
vcommute2_t13 = check_not_vedge vcommute2_sig "Checking no crossed vertical edge is there after" vcommute2_mudg2 vcommute2_term2 vcommute2_term5

vcommute_tests2 :: String
vcommute_tests2 = combine_test_results [vcommute2_t1,vcommute2_t2,vcommute2_t3,vcommute2_t4,vcommute2_t5,vcommute2_t6,vcommute2_t7,vcommute2_t8,vcommute2_t9,vcommute2_t10,vcommute2_t11,vcommute2_t12,vcommute2_t13]



-- Test 3
vcommute3_term1 :: SOMetaTermDependant
vcommute3_term1 = read "u0 x0"

vcommute3_tid1 :: SOMetaUnifRelFoId s
vcommute3_tid1 = relbwEqDGFoId vcommute3_term1

vcommute3_term2 :: SOMetaTermDependant
vcommute3_term2 = read "u0 x1"

vcommute3_tid2 :: SOMetaUnifRelFoId s
vcommute3_tid2 = relbwEqDGFoId vcommute3_term2

vcommute3_term3 :: SOMetaTermDependant
vcommute3_term3 = read "u1 u0 x1"

vcommute3_tid3 :: SOMetaUnifRelFoId s
vcommute3_tid3 = relbwEqDGFoId vcommute3_term3

vcommute3_term4 :: SOMetaTermDependant
vcommute3_term4 = read "u1 u0 x0"

vcommute3_tid4 :: SOMetaUnifRelFoId s
vcommute3_tid4 = relbwEqDGFoId vcommute3_term4

vcommute3_term5 :: SOMetaTermDependant
vcommute3_term5 = read "u0 x2"

vcommute3_tid5 :: SOMetaUnifRelFoId s
vcommute3_tid5 = relbwEqDGFoId vcommute3_term5

vcommute3_term6 :: SOMetaTermDependant
vcommute3_term6 = read "u1 u0 x2"

vcommute3_tid6 :: SOMetaUnifRelFoId s
vcommute3_tid6 = relbwEqDGFoId vcommute3_term6

vcommute3_soterm1 :: SOMetatermF
vcommute3_soterm1 = read "f1[1]"

vcommute3_sotid1 :: SOMetaUnifRelSoId s
vcommute3_sotid1 = relbwEqDGSoId vcommute3_soterm1

vcommute3_soterm2 :: SOMetatermF
vcommute3_soterm2 = read "f2[1]"

vcommute3_sotid2 :: SOMetaUnifRelSoId s
vcommute3_sotid2 = relbwEqDGSoId vcommute3_soterm2

vcommute3_sig :: SOMetaSignature
vcommute3_sig = SOSignature (Signature [] [EnumProc.Empty,read "f1[1]" --> read "f2[1]" --> EnumProc.Empty] (read "x0" --> read "x1" --> read "x2" --> EnumProc.Empty)) EnumProc.Empty

vcommute3_mudg1 :: StateT (RTestSOMetaUnifDGraph s) (ST s) _
vcommute3_mudg1 = do {on_dgraph (newEqDGFOEdge vcommute3_sotid1 [vcommute3_tid1] vcommute3_tid2); on_dgraph (newEqDGFOEdge vcommute3_sotid2 [vcommute3_tid5] vcommute3_tid1); on_vdgraph (addVFoEdge vcommute3_tid2 vcommute3_tid3)}

vcommute3_mudg2 :: StateT (RTestSOMetaUnifDGraph s) (ST s) _
vcommute3_mudg2 = do {vcommute3_mudg1; on_vdgraph metaunif_vertical_commute}

vcommute3_t1 :: AutomatedTest
vcommute3_t1 = check_hfoedge vcommute3_sig "Checking the source horizontal edge is there before" vcommute3_mudg1 vcommute3_soterm1 [vcommute3_term1] vcommute3_term2

vcommute3_t2 :: AutomatedTest
vcommute3_t2 = check_hfoedge vcommute3_sig "Checking the source horizontal edge is there before" vcommute3_mudg1 vcommute3_soterm2 [vcommute3_term5] vcommute3_term1

vcommute3_t3 :: AutomatedTest
vcommute3_t3 = check_not_hfoedge vcommute3_sig "Checking that the target horizontal edge is not there before" vcommute3_mudg1 vcommute3_soterm1 [vcommute3_term4] vcommute3_term3

vcommute3_t4 :: AutomatedTest
vcommute3_t4 = check_not_hfoedge vcommute3_sig "Checking that the target horizontal edge is not there before" vcommute3_mudg1 vcommute3_soterm2 [vcommute3_term6] vcommute3_term4

vcommute3_t5 :: AutomatedTest
vcommute3_t5 = check_vedge vcommute3_sig "Checking that the source vertical edge is there before" vcommute3_mudg1 vcommute3_term2 vcommute3_term3

vcommute3_t6 :: AutomatedTest
vcommute3_t6 = check_not_vedge vcommute3_sig "Checking that the target vertical edge is not there before" vcommute3_mudg1 vcommute3_term1 vcommute3_term4

vcommute3_t7 :: AutomatedTest
vcommute3_t7 = check_not_vedge vcommute3_sig "Checking that the target vertical edge is not there before" vcommute3_mudg1 vcommute3_term5 vcommute3_term6

vcommute3_t8 :: AutomatedTest
vcommute3_t8 = check_hfoedge vcommute3_sig "Checking that the target horizontal edge is there after" vcommute3_mudg2 vcommute3_soterm1 [vcommute3_term4] vcommute3_term3

vcommute3_t9 :: AutomatedTest
vcommute3_t9 = check_hfoedge vcommute3_sig "Checking that the target horizontal edge is there after" vcommute3_mudg2 vcommute3_soterm2 [vcommute3_term6] vcommute3_term4

vcommute3_t10 :: AutomatedTest
vcommute3_t10 = check_vedge vcommute3_sig "Checking that the target vertical edge is there after" vcommute3_mudg2 vcommute3_term1 vcommute3_term4

vcommute3_t11 :: AutomatedTest
vcommute3_t11 = check_vedge vcommute3_sig "Checking that the target vertical edge is there after" vcommute3_mudg2 vcommute3_term5 vcommute3_term6

vcommute_tests3 :: String
vcommute_tests3 = combine_test_results [vcommute3_t1,vcommute3_t2,vcommute3_t3,vcommute3_t4,vcommute3_t5,vcommute3_t6,vcommute3_t7,vcommute3_t8,vcommute3_t9,vcommute3_t10,vcommute3_t11]



vcommute4_term1 :: SOMetaTermDependant
vcommute4_term1 = read "u0 x0"

vcommute4_tid1 :: SOMetaUnifRelFoId s
vcommute4_tid1 = relbwEqDGFoId vcommute4_term1

vcommute4_term2 :: SOMetaTermDependant
vcommute4_term2 = read "u0 x1"

vcommute4_tid2 :: SOMetaUnifRelFoId s
vcommute4_tid2 = relbwEqDGFoId vcommute4_term2

vcommute4_term3 :: SOMetaTermDependant
vcommute4_term3 = read "u1 u0 x1"

vcommute4_tid3 :: SOMetaUnifRelFoId s
vcommute4_tid3 = relbwEqDGFoId vcommute4_term3

vcommute4_term4 :: SOMetaTermDependant
vcommute4_term4 = read "u1 u0 x0"

vcommute4_tid4 :: SOMetaUnifRelFoId s
vcommute4_tid4 = relbwEqDGFoId vcommute4_term4

vcommute4_soterm1 :: SOMetatermF
vcommute4_soterm1 = read "f1[1]"

vcommute4_sotid1 :: SOMetaUnifRelSoId s
vcommute4_sotid1 = relbwEqDGSoId vcommute4_soterm1

vcommute4_sig :: SOMetaSignature
vcommute4_sig = SOSignature (Signature [] [EnumProc.Empty,read "f1[1]" --> EnumProc.Empty] (read "x0" --> read "x1" --> EnumProc.Empty)) EnumProc.Empty

vcommute4_mudg1 :: StateT (RTestSOMetaUnifDGraph s) (ST s) _
vcommute4_mudg1 = do {on_dgraph (newEqDGFOEdge vcommute4_sotid1 [vcommute4_tid1] vcommute4_tid2); on_vdgraph (addVFoEdge vcommute4_tid1 vcommute4_tid4)}

vcommute4_mudg2 :: StateT (RTestSOMetaUnifDGraph s) (ST s) _
vcommute4_mudg2 = do {vcommute4_mudg1; on_vdgraph metaunif_vertical_commute}

vcommute4_t1 :: AutomatedTest
vcommute4_t1 = check_hfoedge vcommute4_sig "Checking the source horizontal edge is there before" vcommute4_mudg1 vcommute4_soterm1 [vcommute4_term1] vcommute4_term2

vcommute4_t2 :: AutomatedTest
vcommute4_t2 = check_vedge vcommute4_sig "Checking the source vertical edge is there before" vcommute4_mudg1 vcommute4_term1 vcommute4_term4

vcommute4_t3 :: AutomatedTest
vcommute4_t3 = check_not_hfoedge vcommute4_sig "Checking the resulting horizontal edge is not there before" vcommute4_mudg1 vcommute4_soterm1 [vcommute4_term4] vcommute4_term3

vcommute4_t4 :: AutomatedTest
vcommute4_t4 = check_not_vedge vcommute4_sig "Checking the resulting vertical edge is not there before" vcommute4_mudg1 vcommute4_term2 vcommute4_term3

vcommute4_t5 :: AutomatedTest
vcommute4_t5 = check_hfoedge vcommute4_sig "Checking the source horizontal edge is there after" vcommute4_mudg2 vcommute4_soterm1 [vcommute4_term1] vcommute4_term2

vcommute4_t6 :: AutomatedTest
vcommute4_t6 = check_vedge vcommute4_sig "Checking the source vertical edge is there after" vcommute4_mudg2 vcommute4_term1 vcommute4_term4

vcommute4_t7 :: AutomatedTest
vcommute4_t7 = check_hfoedge vcommute4_sig "Checking the resulting horizontal edge is there after" vcommute4_mudg2 vcommute4_soterm1 [vcommute4_term4] vcommute4_term3

vcommute4_t8 :: AutomatedTest
vcommute4_t8 = check_vedge vcommute4_sig "Checking the resulting vertical edge is there before" vcommute4_mudg2 vcommute4_term2 vcommute4_term3

vcommute_tests4 :: String
vcommute_tests4 = combine_test_results [vcommute4_t1,vcommute4_t2,vcommute4_t3,vcommute4_t4,vcommute4_t5,vcommute4_t6,vcommute4_t7,vcommute4_t8]





vcommute_test :: IO ()
vcommute_test = putStr "EXAMPLE 1\n\n" >> putStr vcommute_tests1 >>
		putStr "EXAMPLE 2\n\n" >> putStr vcommute_tests2 >>
		putStr "EXAMPLE 3\n\n" >> putStr vcommute_tests3 >>
		putStr "EXAMPLE 4\n\n" >> putStr vcommute_tests4


-- Vertical align tests
valign1_term1 :: SOMetaTermDependant
valign1_term1 = read "u1 u0 x0"

valign1_tid1 :: SOMetaUnifRelFoId s
valign1_tid1 = relbwEqDGFoId valign1_term1

valign1_term2 :: SOMetaTermDependant
valign1_term2 = read "u2 u0 x1"

valign1_tid2 :: SOMetaUnifRelFoId s
valign1_tid2 = relbwEqDGFoId valign1_term2

valign1_term3 :: SOMetaTermDependant
valign1_term3 = read "u0 x0"

valign1_tid3 :: SOMetaUnifRelFoId s
valign1_tid3 = relbwEqDGFoId valign1_term3

valign1_term4 :: SOMetaTermDependant
valign1_term4 = read "x0"

valign1_tid4 :: SOMetaUnifRelFoId s
valign1_tid4 = relbwEqDGFoId valign1_term4

valign1_term5 :: SOMetaTermDependant
valign1_term5 = read "u0 x1"

valign1_tid5 :: SOMetaUnifRelFoId s
valign1_tid5 = relbwEqDGFoId valign1_term5

valign1_term6 :: SOMetaTermDependant
valign1_term6 = read "x1"

valign1_tid6 :: SOMetaUnifRelFoId s
valign1_tid6 = relbwEqDGFoId valign1_term6

valign1_sig :: SOMetaSignature
valign1_sig = SOSignature (Signature [] [] (read "x0" --> read "x1" --> EnumProc.Empty)) EnumProc.Empty

valign1_mudg1 :: StateT (RTestSOMetaUnifDGraph s) (ST s) _
valign1_mudg1 = do {on_vdgraph (addVFoEdge valign1_tid3 valign1_tid1); on_dgraph (newEqDGFONode valign1_term6); on_dgraph (newEqDGFONode valign1_term2); return ()}

valign1_mudg2 :: StateT (RTestSOMetaUnifDGraph s) (ST s) _
valign1_mudg2 = do {valign1_mudg1; on_vdgraph metaunif_vertical_align; return ()}

valign1_t1 :: AutomatedTest
valign1_t1 = check_vedge valign1_sig "Checking that the preexisting vertical edge exists before" valign1_mudg1 valign1_term3 valign1_term1

valign1_t2 :: AutomatedTest
valign1_t2 = check_not_vedge valign1_sig "Checking that the produced vertical edge does not exist before" valign1_mudg1 valign1_term4 valign1_term3

valign1_t3 :: AutomatedTest
valign1_t3 = check_not_vedge valign1_sig "Checking that the produced vertical edge does not exist before" valign1_mudg1 valign1_term5 valign1_term2

valign1_t4 :: AutomatedTest
valign1_t4 = check_not_vedge valign1_sig "Checking that the produced vertical edge does not exist before" valign1_mudg1 valign1_term6 valign1_term5

valign1_t5 :: AutomatedTest
valign1_t5 = check_not_vedge valign1_sig "Checking that a transitive vertical edge does not exist before" valign1_mudg1 valign1_term6 valign1_term2

valign1_t6 :: AutomatedTest
valign1_t6 = check_not_vedge valign1_sig "Checking that a transitive vertical edge does not exist before" valign1_mudg1 valign1_term4 valign1_term1

valign1_t7 :: AutomatedTest
valign1_t7 = check_vedge valign1_sig "Checking that the preexisting vertical edge exists after" valign1_mudg2 valign1_term3 valign1_term1

valign1_t8 :: AutomatedTest
valign1_t8 = check_vedge valign1_sig "Checking that the produced vertical edge exists after" valign1_mudg2 valign1_term4 valign1_term3

valign1_t9 :: AutomatedTest
valign1_t9 = check_vedge valign1_sig "Checking that the produced vertical edge exists after" valign1_mudg2 valign1_term5 valign1_term2

valign1_t10 :: AutomatedTest
valign1_t10 = check_vedge valign1_sig "Checking that the produced vertical edge exists after" valign1_mudg2 valign1_term6 valign1_term5

valign1_t11 :: AutomatedTest
valign1_t11 = check_not_vedge valign1_sig "Checking that a transitive vertical edge does not exist after" valign1_mudg2 valign1_term6 valign1_term2

valign1_t12 :: AutomatedTest
valign1_t12 = check_not_vedge valign1_sig "Checking that a transitive vertical edge does not exist after" valign1_mudg2 valign1_term4 valign1_term1

valign_tests1 :: String
valign_tests1 = combine_test_results [valign1_t1,valign1_t2,valign1_t3,valign1_t4,valign1_t5,valign1_t6,valign1_t7,valign1_t8,valign1_t9,valign1_t10,valign1_t11,valign1_t12]


valign_test :: IO ()
valign_test = putStr "EXAMPLE 1\n\n" >> putStr valign_tests1



-- Zip tests
zip1_soterm1 :: SOMetatermF
zip1_soterm1 = read "f1[2]"

zip1_sotid1 :: SOMetaUnifRelSoId s
zip1_sotid1 = relbwEqDGSoId zip1_soterm1

zip1_soterm2 :: SOMetatermF
zip1_soterm2 = read "f2[2]"

zip1_sotid2 :: SOMetaUnifRelSoId s
zip1_sotid2 = relbwEqDGSoId zip1_soterm2

zip1_soterm3 :: SOMetatermF
zip1_soterm3 = read "F0[1]"

zip1_sotid3 :: SOMetaUnifRelSoId s
zip1_sotid3 = relbwEqDGSoId zip1_soterm3

zip1_soterm4 :: SOMetatermF
zip1_soterm4 = read "F1[1]"

zip1_sotid4 :: SOMetaUnifRelSoId s
zip1_sotid4 = relbwEqDGSoId zip1_soterm4

zip1_soterm5 :: SOMetatermF
zip1_soterm5 = read "F2[1]"

zip1_sotid5 :: SOMetaUnifRelSoId s
zip1_sotid5 = relbwEqDGSoId zip1_soterm5

zip1_soterm6 :: SOMetatermF
zip1_soterm6 = read "F3[1]"

zip1_sotid6 :: SOMetaUnifRelSoId s
zip1_sotid6 = relbwEqDGSoId zip1_soterm6

zip1_soterm7 :: SOMetatermF
zip1_soterm7 = read "F4[1]"

zip1_sotid7 :: SOMetaUnifRelSoId s
zip1_sotid7 = relbwEqDGSoId zip1_soterm7

zip1_soterm8 :: SOMetatermF
zip1_soterm8 = read "F5[1]"

zip1_sotid8 :: SOMetaUnifRelSoId s
zip1_sotid8 = relbwEqDGSoId zip1_soterm8

zip1_soterm9 :: SOMetatermF
zip1_soterm9 = read "F6[1]"

zip1_sotid9 :: SOMetaUnifRelSoId s
zip1_sotid9 = relbwEqDGSoId zip1_soterm9

zip1_soterm10 :: SOMetatermF
zip1_soterm10 = read "F7[1]"

zip1_sotid10 :: SOMetaUnifRelSoId s
zip1_sotid10 = relbwEqDGSoId zip1_soterm10

zip1_sig :: SOMetaSignature
zip1_sig = SOSignature (Signature [] [EnumProc.Empty,EnumProc.Empty,read "f1[2]" --> read "f2[2]" --> EnumProc.Empty] EnumProc.Empty) (read "F0[1]" --> read "F1[1]" --> read "F2[1]" --> read "F3[1]" --> read "F4[1]" --> read "F5[1]" --> read "F6[1]" --> read "F7[1]" --> EnumProc.Empty)

zip1_mudg1 :: StateT (RTestSOMetaUnifDGraph s) (ST s) _
zip1_mudg1 = do
	{
		on_dgraph (newEqDGSONode zip1_soterm1);
		on_dgraph (newEqDGSONode zip1_soterm2);
		on_dgraph (newEqDGSONode zip1_soterm3);
		on_dgraph (newEqDGSONode zip1_soterm4);
		on_dgraph (newEqDGSONode zip1_soterm5);
		on_dgraph (newEqDGSONode zip1_soterm6);
		on_dgraph (newEqDGSONode zip1_soterm7);
		on_dgraph (newEqDGSONode zip1_soterm8);
		on_dgraph (newEqDGSONode zip1_soterm9);
		on_dgraph (newEqDGSONode zip1_soterm10);
		on_dgraph (newEqDGSOEdge zip1_sotid1 [zip1_sotid3, zip1_sotid4] zip1_sotid6);
		on_dgraph (newEqDGSOEdge zip1_sotid1 [zip1_sotid3, zip1_sotid4] zip1_sotid7);
		on_dgraph (newEqDGSOEdge zip1_sotid2 [zip1_sotid3, zip1_sotid4] zip1_sotid8);
		on_dgraph (newEqDGSOEdge zip1_sotid1 [zip1_sotid3, zip1_sotid5] zip1_sotid9);
		on_dgraph (newEqDGSOEdge zip1_sotid1 [zip1_sotid4, zip1_sotid3] zip1_sotid10)
	}

zip1_mudg2 :: StateT (RTestSOMetaUnifDGraph s) (ST s) _
zip1_mudg2 = do {zip1_mudg1; on_vdgraph metaunif_sozip}

zip1_t1 :: AutomatedTest
zip1_t1 = check_not_soequiv zip1_sig "Checking that F3 and F4 are not equivalent before" zip1_mudg1 zip1_soterm6 zip1_soterm7

zip1_t2 :: AutomatedTest
zip1_t2 = check_not_soequiv zip1_sig "Checking that F3 and F5 are not equivalent before" zip1_mudg1 zip1_soterm6 zip1_soterm8

zip1_t3 :: AutomatedTest
zip1_t3 = check_not_soequiv zip1_sig "Checking that F3 and F6 are not equivalent before" zip1_mudg1 zip1_soterm6 zip1_soterm9

zip1_t4 :: AutomatedTest
zip1_t4 = check_not_soequiv zip1_sig "Checking that F3 and F7 are not equivalent before" zip1_mudg1 zip1_soterm6 zip1_soterm10

zip1_t5 :: AutomatedTest
zip1_t5 = check_not_soequiv zip1_sig "Checking that F4 and F5 are not equivalent before" zip1_mudg1 zip1_soterm7 zip1_soterm8

zip1_t6 :: AutomatedTest
zip1_t6 = check_not_soequiv zip1_sig "Checking that F4 and F6 are not equivalent before" zip1_mudg1 zip1_soterm7 zip1_soterm9

zip1_t7 :: AutomatedTest
zip1_t7 = check_not_soequiv zip1_sig "Checking that F4 and F7 are not equivalent before" zip1_mudg1 zip1_soterm7 zip1_soterm10

zip1_t8 :: AutomatedTest
zip1_t8 = check_not_soequiv zip1_sig "Checking that F5 and F6 are not equivalent before" zip1_mudg1 zip1_soterm8 zip1_soterm9

zip1_t9 :: AutomatedTest
zip1_t9 = check_not_soequiv zip1_sig "Checking that F5 and F7 are not equivalent before" zip1_mudg1 zip1_soterm8 zip1_soterm10

zip1_t10 :: AutomatedTest
zip1_t10 = check_not_soequiv zip1_sig "Checking that F6 and F7 are not equivalent before" zip1_mudg1 zip1_soterm9 zip1_soterm10

zip1_t11 :: AutomatedTest
zip1_t11 = check_soequiv zip1_sig "Checking that F3 and F4 are equivalent after" zip1_mudg2 zip1_soterm6 zip1_soterm7

zip1_t12 :: AutomatedTest
zip1_t12 = check_not_soequiv zip1_sig "Checking that F3 and F5 are not equivalent after" zip1_mudg2 zip1_soterm6 zip1_soterm8

zip1_t13 :: AutomatedTest
zip1_t13 = check_not_soequiv zip1_sig "Checking that F3 and F6 are not equivalent after" zip1_mudg2 zip1_soterm6 zip1_soterm9

zip1_t14 :: AutomatedTest
zip1_t14 = check_not_soequiv zip1_sig "Checking that F3 and F7 are not equivalent after" zip1_mudg2 zip1_soterm6 zip1_soterm10

zip1_t15 :: AutomatedTest
zip1_t15 = check_not_soequiv zip1_sig "Checking that F4 and F5 are not equivalent after" zip1_mudg2 zip1_soterm7 zip1_soterm8

zip1_t16 :: AutomatedTest
zip1_t16 = check_not_soequiv zip1_sig "Checking that F4 and F6 are not equivalent after" zip1_mudg2 zip1_soterm7 zip1_soterm9

zip1_t17 :: AutomatedTest
zip1_t17 = check_not_soequiv zip1_sig "Checking that F4 and F7 are not equivalent after" zip1_mudg2 zip1_soterm7 zip1_soterm10

zip1_t18 :: AutomatedTest
zip1_t18 = check_not_soequiv zip1_sig "Checking that F5 and F6 are not equivalent after" zip1_mudg2 zip1_soterm8 zip1_soterm9

zip1_t19 :: AutomatedTest
zip1_t19 = check_not_soequiv zip1_sig "Checking that F5 and F7 are not equivalent after" zip1_mudg2 zip1_soterm8 zip1_soterm10

zip1_t20 :: AutomatedTest
zip1_t20 = check_not_soequiv zip1_sig "Checking that F6 and F7 are not equivalent after" zip1_mudg2 zip1_soterm9 zip1_soterm10

zip_tests1 :: String
zip_tests1 = combine_test_results [zip1_t1,zip1_t2,zip1_t3,zip1_t4,zip1_t5,zip1_t6,zip1_t7,zip1_t8,zip1_t9,zip1_t10,zip1_t11,zip1_t12,zip1_t13,zip1_t14,zip1_t15,zip1_t16,zip1_t17,zip1_t18,zip1_t19,zip1_t20]



zip2_soterm1 :: SOMetatermF
zip2_soterm1 = read "F0[1]"

zip2_sotid1 :: SOMetaUnifRelSoId s
zip2_sotid1 = relbwEqDGSoId zip2_soterm1

zip2_soterm2 :: SOMetatermF
zip2_soterm2 = read "F1[1]"

zip2_sotid2 :: SOMetaUnifRelSoId s
zip2_sotid2 = relbwEqDGSoId zip2_soterm2

zip2_soterm3 :: SOMetatermF
zip2_soterm3 = read "F2[1]"

zip2_sotid3 :: SOMetaUnifRelSoId s
zip2_sotid3 = relbwEqDGSoId zip2_soterm3

zip2_soterm4 :: SOMetatermF
zip2_soterm4 = read "F3[1]"

zip2_sotid4 :: SOMetaUnifRelSoId s
zip2_sotid4 = relbwEqDGSoId zip2_soterm4

zip2_soterm5 :: SOMetatermF
zip2_soterm5 = read "F4[1]"

zip2_sotid5 :: SOMetaUnifRelSoId s
zip2_sotid5 = relbwEqDGSoId zip2_soterm5

zip2_soterm6 :: SOMetatermF
zip2_soterm6 = read "f0[1]"

zip2_sotid6 :: SOMetaUnifRelSoId s
zip2_sotid6 = relbwEqDGSoId zip2_soterm6

zip2_soterm7 :: SOMetatermF
zip2_soterm7 = read "f1[1]"

zip2_sotid7 :: SOMetaUnifRelSoId s
zip2_sotid7 = relbwEqDGSoId zip2_soterm7

zip2_sig :: SOMetaSignature
zip2_sig = SOSignature (Signature [] [EnumProc.Empty,read "f0[1]" --> read "f1[1]" --> EnumProc.Empty] EnumProc.Empty) (read "F0[1]" --> read "F1[1]" --> read "F2[1]" --> read "F3[1]" --> read "F4[1]" --> EnumProc.Empty)

zip2_mudg1 :: StateT (RTestSOMetaUnifDGraph s) (ST s) _
zip2_mudg1 = do
	{
		on_dgraph (newEqDGSONode zip2_soterm1);
		on_dgraph (newEqDGSONode zip2_soterm2);
		on_dgraph (newEqDGSONode zip2_soterm3);
		on_dgraph (newEqDGSONode zip2_soterm4);
		on_dgraph (newEqDGSONode zip2_soterm5);
		on_dgraph (newEqDGSONode zip2_soterm6);
		on_dgraph (newEqDGSONode zip2_soterm7);
		on_dgraph (newEqDGSOEdge zip2_sotid6 [zip2_sotid1] zip2_sotid2);
		on_dgraph (newEqDGSOEdge zip2_sotid6 [zip2_sotid1] zip2_sotid3);
		on_dgraph (newEqDGSOEdge zip2_sotid7 [zip2_sotid2] zip2_sotid4);
		on_dgraph (newEqDGSOEdge zip2_sotid7 [zip2_sotid3] zip2_sotid5)
	}

zip2_mudg2 :: StateT (RTestSOMetaUnifDGraph s) (ST s) _
zip2_mudg2 = do {zip2_mudg1; on_vdgraph metaunif_sozip}

zip2_t1 :: AutomatedTest
zip2_t1 = check_not_soequiv zip2_sig "Checking that F1 and F2 are not equivalent before" zip2_mudg1 zip2_soterm2 zip2_soterm3

zip2_t2 :: AutomatedTest
zip2_t2 = check_not_soequiv zip2_sig "Checking that F3 and F4 are not equivalent before" zip2_mudg1 zip2_soterm4 zip2_soterm5

zip2_t3 :: AutomatedTest
zip2_t3 = check_not_soequiv zip2_sig "Checking that F1 and F3 are not equivalent before" zip2_mudg1 zip2_soterm2 zip2_soterm4

zip2_t4 :: AutomatedTest
zip2_t4 = check_soequiv zip2_sig "Checking that F1 and F2 are equivalent after" zip2_mudg2 zip2_soterm2 zip2_soterm3

zip2_t5 :: AutomatedTest
zip2_t5 = check_soequiv zip2_sig "Checking that F3 and F4 are equivalent after" zip2_mudg2 zip2_soterm4 zip2_soterm5

zip2_t6 :: AutomatedTest
zip2_t6 = check_not_soequiv zip2_sig "Checking that F1 and F3 are not equivalent after" zip2_mudg2 zip2_soterm2 zip2_soterm4

zip_tests2 :: String
zip_tests2 = combine_test_results [zip2_t1,zip2_t2,zip2_t3,zip2_t4,zip2_t5,zip2_t6]



zip3_term1 :: SOMetaTermDependant
zip3_term1 = read "u0 x0"

zip3_tid1 :: SOMetaUnifRelFoId s
zip3_tid1 = relbwEqDGFoId zip3_term1

zip3_term2 :: SOMetaTermDependant
zip3_term2 = read "u0 x1"

zip3_tid2 :: SOMetaUnifRelFoId s
zip3_tid2 = relbwEqDGFoId zip3_term2

zip3_term3 :: SOMetaTermDependant
zip3_term3 = read "u0 x2"

zip3_tid3 :: SOMetaUnifRelFoId s
zip3_tid3 = relbwEqDGFoId zip3_term3

zip3_term4 :: SOMetaTermDependant
zip3_term4 = read "u0 x3"

zip3_tid4 :: SOMetaUnifRelFoId s
zip3_tid4 = relbwEqDGFoId zip3_term4

zip3_term5 :: SOMetaTermDependant
zip3_term5 = read "u0 x4"

zip3_tid5 :: SOMetaUnifRelFoId s
zip3_tid5 = relbwEqDGFoId zip3_term5

zip3_soterm6 :: SOMetatermF
zip3_soterm6 = read "f0[1]"

zip3_sotid6 :: SOMetaUnifRelSoId s
zip3_sotid6 = relbwEqDGSoId zip3_soterm6

zip3_soterm7 :: SOMetatermF
zip3_soterm7 = read "f1[1]"

zip3_sotid7 :: SOMetaUnifRelSoId s
zip3_sotid7 = relbwEqDGSoId zip3_soterm7

zip3_sig :: SOMetaSignature
zip3_sig = SOSignature (Signature [] [EnumProc.Empty,read "f0[1]" --> read "f1[1]" --> EnumProc.Empty] (read "x0" --> read "x1" --> read "x2" --> read "x3" --> read "x4" --> EnumProc.Empty)) EnumProc.Empty

zip3_mudg1 :: StateT (RTestSOMetaUnifDGraph s) (ST s) _
zip3_mudg1 = do
	{
		on_dgraph (newEqDGFONode zip3_term1);
		on_dgraph (newEqDGFONode zip3_term2);
		on_dgraph (newEqDGFONode zip3_term3);
		on_dgraph (newEqDGFONode zip3_term4);
		on_dgraph (newEqDGFONode zip3_term5);
		on_dgraph (newEqDGSONode zip3_soterm6);
		on_dgraph (newEqDGSONode zip3_soterm7);
		on_dgraph (newEqDGFOEdge zip3_sotid6 [zip3_tid1] zip3_tid2);
		on_dgraph (newEqDGFOEdge zip3_sotid6 [zip3_tid1] zip3_tid3);
		on_dgraph (newEqDGFOEdge zip3_sotid7 [zip3_tid2] zip3_tid4);
		on_dgraph (newEqDGFOEdge zip3_sotid7 [zip3_tid3] zip3_tid5)
	}

zip3_mudg2 :: StateT (RTestSOMetaUnifDGraph s) (ST s) _
zip3_mudg2 = do {zip3_mudg1; on_vdgraph metaunif_fozip}

zip3_t1 :: AutomatedTest
zip3_t1 = check_not_foequiv zip3_sig "Checking that u0 x1 and u0 x2 are not equivalent before" zip3_mudg1 zip3_term2 zip3_term3

zip3_t2 :: AutomatedTest
zip3_t2 = check_not_foequiv zip3_sig "Checking that u0 x3 and u0 x4 are not equivalent before" zip3_mudg1 zip3_term4 zip3_term5

zip3_t3 :: AutomatedTest
zip3_t3 = check_not_foequiv zip3_sig "Checking that u0 x1 and u0 x3 are not equivalent before" zip3_mudg1 zip3_term2 zip3_term4

zip3_t4 :: AutomatedTest
zip3_t4 = check_foequiv zip3_sig "Checking that u0 x1 and u0 x2 are equivalent after" zip3_mudg2 zip3_term2 zip3_term3

zip3_t5 :: AutomatedTest
zip3_t5 = check_foequiv zip3_sig "Checking that u0 x3 and u0 x4 are equivalent after" zip3_mudg2 zip3_term4 zip3_term5

zip3_t6 :: AutomatedTest
zip3_t6 = check_not_foequiv zip3_sig "Checking that u0 x1 and u0 x3 are not equivalent after" zip3_mudg2 zip3_term2 zip3_term4

zip_tests3 :: String
zip_tests3 = combine_test_results [zip3_t1,zip3_t2,zip3_t3,zip3_t4,zip3_t5,zip3_t6]


zip4_term1 :: SOMetaTermDependant
zip4_term1 = read "u0 x0"

zip4_tid1 :: SOMetaUnifRelFoId s
zip4_tid1 = relbwEqDGFoId zip4_term1

zip4_term2 :: SOMetaTermDependant
zip4_term2 = read "u0 x1"

zip4_tid2 :: SOMetaUnifRelFoId s
zip4_tid2 = relbwEqDGFoId zip4_term2

zip4_term3 :: SOMetaTermDependant
zip4_term3 = read "u0 x2"

zip4_tid3 :: SOMetaUnifRelFoId s
zip4_tid3 = relbwEqDGFoId zip4_term3

zip4_term4 :: SOMetaTermDependant
zip4_term4 = read "u0 x3"

zip4_tid4 :: SOMetaUnifRelFoId s
zip4_tid4 = relbwEqDGFoId zip4_term4

zip4_term5 :: SOMetaTermDependant
zip4_term5 = read "u1 x1"

zip4_tid5 :: SOMetaUnifRelFoId s
zip4_tid5 = relbwEqDGFoId zip4_term5

zip4_term6 :: SOMetaTermDependant
zip4_term6 = read "u1 u0 x1"

zip4_tid6 :: SOMetaUnifRelFoId s
zip4_tid6 = relbwEqDGFoId zip4_term6

zip4_term7 :: SOMetaTermDependant
zip4_term7 = read "u1 u0 x3"

zip4_tid7 :: SOMetaUnifRelFoId s
zip4_tid7 = relbwEqDGFoId zip4_term7

zip4_term8 :: SOMetaTermDependant
zip4_term8 = read "u1 x3"

zip4_tid8 :: SOMetaUnifRelFoId s
zip4_tid8 = relbwEqDGFoId zip4_term8

zip4_term9 :: SOMetaTermDependant
zip4_term9 = read "u2 u1 x3"

zip4_tid9 :: SOMetaUnifRelFoId s
zip4_tid9 = relbwEqDGFoId zip4_term9

zip4_term10 :: SOMetaTermDependant
zip4_term10 = read "u2 u1 x1"

zip4_tid10 :: SOMetaUnifRelFoId s
zip4_tid10 = relbwEqDGFoId zip4_term10

zip4_soterm1 :: SOMetatermF
zip4_soterm1 = read "f1[1]"

zip4_sotid1 :: SOMetaUnifRelSoId s
zip4_sotid1 = relbwEqDGSoId zip4_soterm1

zip4_soterm2 :: SOMetatermF
zip4_soterm2 = read "f2[1]"

zip4_sotid2 :: SOMetaUnifRelSoId s
zip4_sotid2 = relbwEqDGSoId zip4_soterm2

zip4_soterm3 :: SOMetatermF
zip4_soterm3 = read "f3[1]"

zip4_sotid3 :: SOMetaUnifRelSoId s
zip4_sotid3 = relbwEqDGSoId zip4_soterm3

zip4_sig :: SOMetaSignature
zip4_sig = SOSignature (Signature [] [EnumProc.Empty,read "f1[1]" --> read "f2[1]" --> read "f3[1]" --> EnumProc.Empty] (read "x0" --> read "x1" --> read "x2" --> read "x3" --> EnumProc.Empty)) EnumProc.Empty

zip4_mudg1 :: StateT (RTestSOMetaUnifDGraph s) (ST s) _
zip4_mudg1 = do
	{
		on_dgraph (newEqDGFONode zip4_term1);
		on_dgraph (newEqDGFONode zip4_term2);
		on_dgraph (newEqDGFONode zip4_term3);
		on_dgraph (newEqDGFONode zip4_term4);
		on_dgraph (newEqDGFONode zip4_term5);
		on_dgraph (newEqDGFONode zip4_term6);
		on_dgraph (newEqDGFONode zip4_term7);
		on_dgraph (newEqDGFONode zip4_term8);
		on_dgraph (newEqDGFONode zip4_term9);
		-- term 10 is purposely not added to the graph beforehand. It should be generated by the operations.
		on_dgraph (newEqDGSONode zip4_soterm1);
		on_dgraph (newEqDGSONode zip4_soterm2);
		on_dgraph (newEqDGSONode zip4_soterm3);
		on_dgraph (newEqDGFOEdge zip4_sotid1 [zip4_tid1] zip4_tid2);
		on_dgraph (newEqDGFOEdge zip4_sotid1 [zip4_tid1] zip4_tid3);
		on_dgraph (newEqDGFOEdge zip4_sotid2 [zip4_tid4] zip4_tid3);
		on_dgraph (newEqDGFOEdge zip4_sotid2 [zip4_tid7] zip4_tid8);
		on_dgraph (newEqDGFOEdge zip4_sotid3 [zip4_tid5] zip4_tid6)
	}

zip4_mudg2 :: StateT (RTestSOMetaUnifDGraph s) (ST s) _
zip4_mudg2 = do {zip4_mudg1; on_vdgraph metaunif_vertical_align; on_vdgraph metaunif_vertical_commute; pass}

zip4_mudg3 :: StateT (RTestSOMetaUnifDGraph s) (ST s) _
zip4_mudg3 = do {zip4_mudg2; on_vdgraph metaunif_fozip; pass}

zip4_t1 :: AutomatedTest
zip4_t1 = check_not_foequiv zip4_sig "Checking that u0 x1 and u0 x2 are not equivalent before" zip4_mudg1 zip4_term2 zip4_term3

zip4_t2 :: AutomatedTest
zip4_t2 = check_not_hfoedge zip4_sig "Checking there is no g horizontal edge between u0 x3 and u0 x1 before" zip4_mudg1 zip4_soterm2 [zip4_term4] zip4_term2

zip4_t3 :: AutomatedTest
zip4_t3 = check_not_foequiv zip4_sig "Checking that u1 u0 x1 and u1 x3 are not equivalent before" zip4_mudg1 zip4_term6 zip4_term8

zip4_t4 :: AutomatedTest
zip4_t4 = check_not_hfoedge zip4_sig "Checking there is no g horizontal edge between u1 u0 x3 and u1 u0 x1 before" zip4_mudg1 zip4_soterm2 [zip4_term7] zip4_term6

zip4_t5 :: AutomatedTest
zip4_t5 = check_not_hfoedge zip4_sig "Checking there is no h horizontal edge between u1 x1 and u1 x3 before" zip4_mudg1 zip4_soterm3 [zip4_term5] zip4_term8

zip4_t6 :: AutomatedTest
zip4_t6 = check_not_hfoedge zip4_sig "Checking there is no h horizontal edge between u2 u1 x1 and u2 u1 x3 before" zip4_mudg1 zip4_soterm3 [zip4_term10] zip4_term9

zip4_t7 :: AutomatedTest
zip4_t7 = check_not_vedge zip4_sig "Checking there is no vertical edge between u0 x3 and u1 u0 x3 before" zip4_mudg1 zip4_term4 zip4_term7

zip4_t8 :: AutomatedTest
zip4_t8 = check_not_vedge zip4_sig "Checking there is no vertical edge between u0 x1 and u1 u0 x1 before" zip4_mudg1 zip4_term2 zip4_term6

zip4_t9 :: AutomatedTest
zip4_t9 = check_not_vedge zip4_sig "Checking there is no vertical edge between u1 x1 and u2 u1 x1 before" zip4_mudg1 zip4_term5 zip4_term10

zip4_t10 :: AutomatedTest
zip4_t10 = check_not_vedge zip4_sig "Checking there is no vertical edge between u1 x3 and u2 u1 x3 before" zip4_mudg1 zip4_term8 zip4_term9

-- We remove the inbetween tests because we underestimated how good propagation actually is!
{-|
zip4_t11 :: AutomatedTest
zip4_t11 = check_not_foequiv "Checking that u0 x1 and u0 x2 are not equivalent inbetween" zip4_mudg2 zip4_term2 zip4_term3

zip4_t12 :: AutomatedTest
zip4_t12 = check_not_hfoedge "Checking there is no g horizontal edge between u0 x3 and u0 x1 inbetween" zip4_mudg2 zip4_soterm2 [zip4_term4] zip4_term2

zip4_t13 :: AutomatedTest
zip4_t13 = check_not_foequiv "Checking that u1 u0 x1 and u1 x3 are not equivalent inbetween" zip4_mudg2 zip4_term6 zip4_term8

zip4_t14 :: AutomatedTest
zip4_t14 = check_not_hfoedge "Checking there is no g horizontal edge between u1 u0 x3 and u1 u0 x1 inbetween" zip4_mudg2 zip4_soterm2 [zip4_term7] zip4_term6

zip4_t15 :: AutomatedTest
zip4_t15 = check_not_hfoedge "Checking there is no h horizontal edge between u1 x1 and u1 x3 inbetween" zip4_mudg2 zip4_soterm3 [zip4_term5] zip4_term8

zip4_t16 :: AutomatedTest
zip4_t16 = check_not_hfoedge "Checking there is no h horizontal edge between u2 u1 x1 and u2 u1 x3 inbetween" zip4_mudg2 zip4_soterm3 [zip4_term10] zip4_term9

zip4_t17 :: AutomatedTest
zip4_t17 = check_vedge "Checking there is a vertical edge between u0 x3 and u1 u0 x3 inbetween" zip4_mudg2 zip4_term4 zip4_term7

zip4_t18 :: AutomatedTest
zip4_t18 = check_vedge "Checking there is a vertical edge between u0 x1 and u1 u0 x1 inbetween" zip4_mudg2 zip4_term2 zip4_term6

zip4_t19 :: AutomatedTest
zip4_t19 = check_not_vedge "Checking there is no vertical edge between u1 x1 and u2 u1 x1 inbetween" zip4_mudg2 zip4_term5 zip4_term10

zip4_t20 :: AutomatedTest
zip4_t20 = check_not_vedge "Checking there is no vertical edge between u1 x3 and u2 u1 x3 inbetween" zip4_mudg2 zip4_term8 zip4_term9
|-}

zip4_t21 :: AutomatedTest
zip4_t21 = check_foequiv zip4_sig "Checking that u0 x1 and u0 x2 are equivalent after" zip4_mudg3 zip4_term2 zip4_term3

zip4_t22 :: AutomatedTest
zip4_t22 = check_hfoedge zip4_sig "Checking there is a g horizontal edge between u0 x3 and u0 x1 after" zip4_mudg3 zip4_soterm2 [zip4_term4] zip4_term2

zip4_t23 :: AutomatedTest
zip4_t23 = check_foequiv zip4_sig "Checking that u1 u0 x1 and u1 x3 are equivalent after" zip4_mudg3 zip4_term6 zip4_term8

zip4_t24 :: AutomatedTest
zip4_t24 = check_hfoedge zip4_sig "Checking there is a g horizontal edge between u1 u0 x3 and u1 u0 x1 after" zip4_mudg3 zip4_soterm2 [zip4_term7] zip4_term6

zip4_t25 :: AutomatedTest
zip4_t25 = check_hfoedge zip4_sig "Checking there is a h horizontal edge between u1 x1 and u1 x3 after" zip4_mudg3 zip4_soterm3 [zip4_term5] zip4_term8

zip4_t26 :: AutomatedTest
zip4_t26 = check_hfoedge zip4_sig "Checking there is a h horizontal edge between u2 u1 x1 and u2 u1 x3 after" zip4_mudg3 zip4_soterm3 [zip4_term10] zip4_term9

zip4_t27 :: AutomatedTest
zip4_t27 = check_vedge zip4_sig "Checking there is a vertical edge between u0 x3 and u1 u0 x3 after" zip4_mudg3 zip4_term4 zip4_term7

zip4_t28 :: AutomatedTest
zip4_t28 = check_vedge zip4_sig "Checking there is a vertical edge between u0 x1 and u1 u0 x1 after" zip4_mudg3 zip4_term2 zip4_term6

zip4_t29 :: AutomatedTest
zip4_t29 = check_vedge zip4_sig "Checking there is a vertical edge between u1 x1 and u2 u1 x1 after" zip4_mudg3 zip4_term5 zip4_term10

zip4_t30 :: AutomatedTest
zip4_t30 = check_vedge zip4_sig "Checking there is a vertical edge between u1 x3 and u2 u1 x3 after" zip4_mudg3 zip4_term8 zip4_term9

zip_tests4 :: String
--zip_tests4 = combine_test_results [zip4_t1,zip4_t2,zip4_t3,zip4_t4,zip4_t5,zip4_t6,zip4_t7,zip4_t8,zip4_t9,zip4_t10,zip4_t11,zip4_t12,zip4_t13,zip4_t14,zip4_t15,zip4_t16,zip4_t17,zip4_t18,zip4_t19,zip4_t20,zip4_t21,zip4_t22,zip4_t23,zip4_t24,zip4_t25,zip4_t26,zip4_t27,zip4_t28,zip4_t29,zip4_t30]
zip_tests4 = combine_test_results [zip4_t1,zip4_t2,zip4_t3,zip4_t4,zip4_t5,zip4_t6,zip4_t7,zip4_t8,zip4_t9,zip4_t10,zip4_t21,zip4_t22,zip4_t23,zip4_t24,zip4_t25,zip4_t26,zip4_t27,zip4_t28,zip4_t29,zip4_t30]




zip_test :: IO ()
zip_test = putStr "EXAMPLE 1\n\n" >> putStr zip_tests1 >>
	putStr "EXAMPLE 2\n\n" >> putStr zip_tests2 >>
	putStr "EXAMPLE 3\n\n" >> putStr zip_tests3 >>
	putStr "EXAMPLE 4\n\n" >> putStr zip_tests4


simpproj1_term1 :: SOMetatermF
simpproj1_term1 = read "f1[0]"

simpproj1_tid1 :: SOMetaUnifRelSoId s
simpproj1_tid1 = relbwEqDGSoId simpproj1_term1

simpproj1_term2 :: SOMetatermF
simpproj1_term2 = read "f2[0]"

simpproj1_tid2 :: SOMetaUnifRelSoId s
simpproj1_tid2 = relbwEqDGSoId simpproj1_term2

simpproj1_term3 :: SOMetatermF
simpproj1_term3 = read "f3[0]"

simpproj1_tid3 :: SOMetaUnifRelSoId s
simpproj1_tid3 = relbwEqDGSoId simpproj1_term3

simpproj1_term4 :: SOMetatermF
simpproj1_term4 = read "f4[0]"

simpproj1_tid4 :: SOMetaUnifRelSoId s
simpproj1_tid4 = relbwEqDGSoId simpproj1_term4

simpproj1_term5 :: SOMetatermF
simpproj1_term5 = read "f5[3]"

simpproj1_tid5 :: SOMetaUnifRelSoId s
simpproj1_tid5 = relbwEqDGSoId simpproj1_term5

simpproj1_term6 :: SOMetatermF
simpproj1_term6 = read "pi1"

simpproj1_tid6 :: SOMetaUnifRelSoId s
simpproj1_tid6 = relbwEqDGSoId simpproj1_term6

simpproj1_sig :: SOMetaSignature
simpproj1_sig = SOSignature (Signature [] [read "f1[0]" --> read "f2[0]" --> read "f3[0]" --> read "f4[0]" --> EnumProc.Empty,EnumProc.Empty,EnumProc.Empty,read "f5[3]" --> EnumProc.Empty] EnumProc.Empty) EnumProc.Empty

simpproj1_mudg1 :: StateT (RTestSOMetaUnifDGraph s) (ST s) _
simpproj1_mudg1 = do
	{
		on_dgraph (newEqDGSONode simpproj1_term1);
		on_dgraph (newEqDGSONode simpproj1_term2);
		on_dgraph (newEqDGSONode simpproj1_term3);
		on_dgraph (newEqDGSONode simpproj1_term4);
		on_dgraph (newEqDGSONode simpproj1_term5);
		on_dgraph (newEqDGSONode simpproj1_term6);
		on_dgraph (newEqDGSOEdge simpproj1_tid5 [simpproj1_tid1,simpproj1_tid2,simpproj1_tid3] simpproj1_tid4);
		on_dgraph (mergeEqDGSONodes simpproj1_tid5 simpproj1_tid6);
		pass
	}

simpproj1_mudg2 :: StateT (RTestSOMetaUnifDGraph s) (ST s) _
simpproj1_mudg2 = do {simpproj1_mudg1; on_vdgraph metaunif_so_simplify_projections; pass}

simpproj1_t1 :: AutomatedTest
simpproj1_t1 = check_hsoedge simpproj1_sig "Checking that the edge is there before" simpproj1_mudg1 simpproj1_term5 [simpproj1_term1,simpproj1_term2,simpproj1_term3] simpproj1_term4

simpproj1_t2 :: AutomatedTest
simpproj1_t2 = check_not_soequiv simpproj1_sig "Checking that f1 and f2 are not equivalent before" simpproj1_mudg1 simpproj1_term1 simpproj1_term2

simpproj1_t3 :: AutomatedTest
simpproj1_t3 = check_not_soequiv simpproj1_sig "Checking that f1 and f3 are not equivalent before" simpproj1_mudg1 simpproj1_term1 simpproj1_term3

simpproj1_t4 :: AutomatedTest
simpproj1_t4 = check_not_soequiv simpproj1_sig "Checking that f1 and f4 are not equivalent before" simpproj1_mudg1 simpproj1_term1 simpproj1_term4

simpproj1_t5 :: AutomatedTest
simpproj1_t5 = check_not_soequiv simpproj1_sig "Checking that f2 and f3 are not equivalent before" simpproj1_mudg1 simpproj1_term2 simpproj1_term3

simpproj1_t6 :: AutomatedTest
simpproj1_t6 = check_not_soequiv simpproj1_sig "Checking that f2 and f4 are not equivalent before" simpproj1_mudg1 simpproj1_term2 simpproj1_term4

simpproj1_t7 :: AutomatedTest
simpproj1_t7 = check_not_soequiv simpproj1_sig "Checking that f3 and f4 are not equivalent before" simpproj1_mudg1 simpproj1_term3 simpproj1_term4

simpproj1_t8 :: AutomatedTest
simpproj1_t8 = check_soequiv simpproj1_sig "Checking that f5 and pi1 are equivalent before" simpproj1_mudg1 simpproj1_term5 simpproj1_term6

simpproj1_t9 :: AutomatedTest
simpproj1_t9 = check_not_hsoedge simpproj1_sig "Checking that the edge is not there after" simpproj1_mudg2 simpproj1_term5 [simpproj1_term1,simpproj1_term2,simpproj1_term3] simpproj1_term4

simpproj1_t10 :: AutomatedTest
simpproj1_t10 = check_not_soequiv simpproj1_sig "Checking that f1 and f2 are not equivalent after" simpproj1_mudg2 simpproj1_term1 simpproj1_term2

simpproj1_t11 :: AutomatedTest
simpproj1_t11 = check_not_soequiv simpproj1_sig "Checking that f1 and f3 are not equivalent after" simpproj1_mudg2 simpproj1_term1 simpproj1_term3

simpproj1_t12 :: AutomatedTest
simpproj1_t12 = check_not_soequiv simpproj1_sig "Checking that f1 and f4 are not equivalent after" simpproj1_mudg2 simpproj1_term1 simpproj1_term4

simpproj1_t13 :: AutomatedTest
simpproj1_t13 = check_not_soequiv simpproj1_sig "Checking that f2 and f3 are not equivalent after" simpproj1_mudg2 simpproj1_term2 simpproj1_term3

simpproj1_t14 :: AutomatedTest
simpproj1_t14 = check_soequiv simpproj1_sig "Checking that f2 and f4 are equivalent after" simpproj1_mudg2 simpproj1_term2 simpproj1_term4

simpproj1_t15 :: AutomatedTest
simpproj1_t15 = check_not_soequiv simpproj1_sig "Checking that f3 and f4 are not equivalent after" simpproj1_mudg2 simpproj1_term3 simpproj1_term4

simpproj1_t16 :: AutomatedTest
simpproj1_t16 = check_soequiv simpproj1_sig "Checking that f5 and pi1 are equivalent after" simpproj1_mudg2 simpproj1_term5 simpproj1_term6

simpproj_tests1 :: String
simpproj_tests1 = combine_test_results [simpproj1_t1,simpproj1_t2,simpproj1_t3,simpproj1_t4,simpproj1_t5,simpproj1_t6,simpproj1_t7,simpproj1_t8,simpproj1_t9,simpproj1_t10,simpproj1_t11,simpproj1_t12,simpproj1_t13,simpproj1_t14,simpproj1_t15,simpproj1_t16]



simpproj2_term1 :: SOMetaTermDependant
simpproj2_term1 = read "f1[0]()"

simpproj2_tid1 :: SOMetaUnifRelFoId s
simpproj2_tid1 = relbwEqDGFoId simpproj2_term1

simpproj2_term2 :: SOMetaTermDependant
simpproj2_term2 = read "f2[0]()"

simpproj2_tid2 :: SOMetaUnifRelFoId s
simpproj2_tid2 = relbwEqDGFoId simpproj2_term2

simpproj2_term3 :: SOMetaTermDependant
simpproj2_term3 = read "f3[0]()"

simpproj2_tid3 :: SOMetaUnifRelFoId s
simpproj2_tid3 = relbwEqDGFoId simpproj2_term3

simpproj2_term4 :: SOMetaTermDependant
simpproj2_term4 = read "f4[0]()"

simpproj2_tid4 :: SOMetaUnifRelFoId s
simpproj2_tid4 = relbwEqDGFoId simpproj2_term4

simpproj2_term5 :: SOMetatermF
simpproj2_term5 = read "f5[3]"

simpproj2_tid5 :: SOMetaUnifRelSoId s
simpproj2_tid5 = relbwEqDGSoId simpproj2_term5

simpproj2_term6 :: SOMetatermF
simpproj2_term6 = read "pi1"

simpproj2_tid6 :: SOMetaUnifRelSoId s
simpproj2_tid6 = relbwEqDGSoId simpproj2_term6

simpproj2_sig :: SOMetaSignature
simpproj2_sig = SOSignature (Signature [] [read "f1[0]" --> read "f2[0]" --> read "f3[0]" --> read "f4[0]" --> EnumProc.Empty,EnumProc.Empty,EnumProc.Empty,read "f5[3]" --> EnumProc.Empty] EnumProc.Empty) EnumProc.Empty

simpproj2_mudg1 :: StateT (RTestSOMetaUnifDGraph s) (ST s) _
simpproj2_mudg1 = do
	{
		on_dgraph (newEqDGFONode simpproj2_term1);
		on_dgraph (newEqDGFONode simpproj2_term2);
		on_dgraph (newEqDGFONode simpproj2_term3);
		on_dgraph (newEqDGFONode simpproj2_term4);
		on_dgraph (newEqDGSONode simpproj2_term5);
		on_dgraph (newEqDGSONode simpproj2_term6);
		on_dgraph (newEqDGFOEdge simpproj2_tid5 [simpproj2_tid1,simpproj2_tid2,simpproj2_tid3] simpproj2_tid4);
		on_dgraph (mergeEqDGSONodes simpproj2_tid5 simpproj2_tid6);
		pass
	}

simpproj2_mudg2 :: StateT (RTestSOMetaUnifDGraph s) (ST s) _
simpproj2_mudg2 = do {simpproj2_mudg1; on_vdgraph metaunif_fo_simplify_projections; pass}

simpproj2_t1 :: AutomatedTest
simpproj2_t1 = check_hfoedge simpproj2_sig "Checking that the edge is there before" simpproj2_mudg1 simpproj2_term5 [simpproj2_term1,simpproj2_term2,simpproj2_term3] simpproj2_term4

simpproj2_t2 :: AutomatedTest
simpproj2_t2 = check_not_foequiv simpproj2_sig "Checking that f1 and f2 are not equivalent before" simpproj2_mudg1 simpproj2_term1 simpproj2_term2

simpproj2_t3 :: AutomatedTest
simpproj2_t3 = check_not_foequiv simpproj2_sig "Checking that f1 and f3 are not equivalent before" simpproj2_mudg1 simpproj2_term1 simpproj2_term3

simpproj2_t4 :: AutomatedTest
simpproj2_t4 = check_not_foequiv simpproj2_sig "Checking that f1 and f4 are not equivalent before" simpproj2_mudg1 simpproj2_term1 simpproj2_term4

simpproj2_t5 :: AutomatedTest
simpproj2_t5 = check_not_foequiv simpproj2_sig "Checking that f2 and f3 are not equivalent before" simpproj2_mudg1 simpproj2_term2 simpproj2_term3

simpproj2_t6 :: AutomatedTest
simpproj2_t6 = check_not_foequiv simpproj2_sig "Checking that f2 and f4 are not equivalent before" simpproj2_mudg1 simpproj2_term2 simpproj2_term4

simpproj2_t7 :: AutomatedTest
simpproj2_t7 = check_not_foequiv simpproj2_sig "Checking that f3 and f4 are not equivalent before" simpproj2_mudg1 simpproj2_term3 simpproj2_term4

simpproj2_t8 :: AutomatedTest
simpproj2_t8 = check_soequiv simpproj2_sig "Checking that f5 and pi1 are equivalent before" simpproj2_mudg1 simpproj2_term5 simpproj2_term6

simpproj2_t9 :: AutomatedTest
simpproj2_t9 = check_not_hfoedge simpproj2_sig "Checking that the edge is not there after" simpproj2_mudg2 simpproj2_term5 [simpproj2_term1,simpproj2_term2,simpproj2_term3] simpproj2_term4

simpproj2_t10 :: AutomatedTest
simpproj2_t10 = check_not_foequiv simpproj2_sig "Checking that f1 and f2 are not equivalent after" simpproj2_mudg2 simpproj2_term1 simpproj2_term2

simpproj2_t11 :: AutomatedTest
simpproj2_t11 = check_not_foequiv simpproj2_sig "Checking that f1 and f3 are not equivalent after" simpproj2_mudg2 simpproj2_term1 simpproj2_term3

simpproj2_t12 :: AutomatedTest
simpproj2_t12 = check_not_foequiv simpproj2_sig "Checking that f1 and f4 are not equivalent after" simpproj2_mudg2 simpproj2_term1 simpproj2_term4

simpproj2_t13 :: AutomatedTest
simpproj2_t13 = check_not_foequiv simpproj2_sig "Checking that f2 and f3 are not equivalent after" simpproj2_mudg2 simpproj2_term2 simpproj2_term3

simpproj2_t14 :: AutomatedTest
simpproj2_t14 = check_foequiv simpproj2_sig "Checking that f2 and f4 are equivalent after" simpproj2_mudg2 simpproj2_term2 simpproj2_term4

simpproj2_t15 :: AutomatedTest
simpproj2_t15 = check_not_foequiv simpproj2_sig "Checking that f3 and f4 are not equivalent after" simpproj2_mudg2 simpproj2_term3 simpproj2_term4

simpproj2_t16 :: AutomatedTest
simpproj2_t16 = check_soequiv simpproj2_sig "Checking that f5 and pi1 are equivalent after" simpproj2_mudg2 simpproj2_term5 simpproj2_term6

simpproj_tests2 :: String
simpproj_tests2 = combine_test_results [simpproj2_t1,simpproj2_t2,simpproj2_t3,simpproj2_t4,simpproj2_t5,simpproj2_t6,simpproj2_t7,simpproj2_t8,simpproj2_t9,simpproj2_t10,simpproj2_t11,simpproj2_t12,simpproj2_t13,simpproj2_t14,simpproj2_t15,simpproj2_t16]




simpproj_test :: IO ()
simpproj_test = putStr "EXAMPLE 1\n\n" >> putStr simpproj_tests1 >>
		putStr "EXAMPLE 2\n\n" >> putStr simpproj_tests2



dump1_term1 :: SOMetaTermDependant
dump1_term1 = read "F0[0]()"

dump1_tid1 :: SOMetaUnifRelFoId s
dump1_tid1 = relbwEqDGFoId dump1_term1

dump1_term2 :: SOMetaTermDependant
dump1_term2 = read "F1[0]()"

dump1_tid2 :: SOMetaUnifRelFoId s
dump1_tid2 = relbwEqDGFoId dump1_term2

dump1_term3 :: SOMetaTermDependant
dump1_term3 = read "F2[0]()"

dump1_tid3 :: SOMetaUnifRelFoId s
dump1_tid3 = relbwEqDGFoId dump1_term3

dump1_soterm1 :: SOMetatermF
dump1_soterm1 = read "F3[2]"

dump1_sotid1 :: SOMetaUnifRelSoId s
dump1_sotid1 = relbwEqDGSoId dump1_soterm1

dump1_soterm2 :: SOMetatermF
dump1_soterm2 = read "F4[2]"

dump1_sotid2 :: SOMetaUnifRelSoId s
dump1_sotid2 = relbwEqDGSoId dump1_soterm2

dump1_soterm3 :: SOMetatermF
dump1_soterm3 = read "F5[2]"

dump1_sotid3 :: SOMetaUnifRelSoId s
dump1_sotid3 = relbwEqDGSoId dump1_soterm3

dump1_soterm4 :: SOMetatermF
dump1_soterm4 = read "F6[2]"

dump1_sotid4 :: SOMetaUnifRelSoId s
dump1_sotid4 = relbwEqDGSoId dump1_soterm4

dump1_exp1 :: SOMetaUnifFOExp
dump1_exp1 = read "F6[2](F4[2](F0[0](),F1[0]()),F5[2](F0[0](),F1[0]()))"

dump1_sig :: SOMetaSignature
dump1_sig = SOSignature (Signature [] [] EnumProc.Empty) (read "F0[0]" --> read "F1[0]" --> read "F2[0]" --> read "F3[2]" --> read "F4[2]" --> read "F5[2]" --> read "F6[2]" --> EnumProc.Empty)

dump1_mudg1 :: StateT (RTestSOMetaUnifDGraph s) (ST s) _
dump1_mudg1 = do
	{
		on_dgraph (newEqDGFONode dump1_term1);
		on_dgraph (newEqDGFONode dump1_term2);
		on_dgraph (newEqDGFONode dump1_term3);
		on_dgraph (newEqDGSONode dump1_soterm1);
		on_dgraph (newEqDGSONode dump1_soterm2);
		on_dgraph (newEqDGSONode dump1_soterm3);
		on_dgraph (newEqDGSONode dump1_soterm4);
		on_dgraph (newEqDGFOEdge dump1_sotid1 [dump1_tid1,dump1_tid2] dump1_tid3);
		on_dgraph (newEqDGSOEdge dump1_sotid4 [dump1_sotid2,dump1_sotid3] dump1_sotid1);
		pass
	}

dump1_mudg2 :: StateT (RTestSOMetaUnifDGraph s) (ST s) _
dump1_mudg2 = do {dump1_mudg1; on_vdgraph metaunif_fo_dump}

dump1_t1 :: AutomatedTest
dump1_t1 = check_hsoedge dump1_sig "Checking that the s.o. edge is there before" dump1_mudg1 dump1_soterm4 [dump1_soterm2,dump1_soterm3] dump1_soterm1

dump1_t2 :: AutomatedTest
dump1_t2 = check_hfoedge dump1_sig "Checking that the original f.o. edge is there before" dump1_mudg1 dump1_soterm1 [dump1_term1,dump1_term2] dump1_term3

dump1_t3 :: AutomatedTest
dump1_t3 = check_not_foexp dump1_sig "Checking that the f.o. node does not match the resulting expression before" dump1_mudg1 dump1_exp1 dump1_term3

dump1_t4 :: AutomatedTest
dump1_t4 = check_hsoedge dump1_sig "Checking that the s.o. edge is there after" dump1_mudg2 dump1_soterm4 [dump1_soterm2,dump1_soterm3] dump1_soterm1

dump1_t5 :: AutomatedTest
dump1_t5 = check_not_hfoedge dump1_sig "Checking that the original f.o. edge is not there after" dump1_mudg2 dump1_soterm1 [dump1_term1,dump1_term2] dump1_term3

dump1_t6 :: AutomatedTest
dump1_t6 = check_foexp dump1_sig "Checking that the f.o. node matches the resulting expression after" dump1_mudg2 dump1_exp1 dump1_term3

dump1_tests :: String
dump1_tests = combine_test_results [dump1_t1,dump1_t2,dump1_t3,dump1_t4,dump1_t5,dump1_t6]


dump2_term1 :: SOMetatermF
dump2_term1 = read "F0[0]"

dump2_tid1 :: SOMetaUnifRelSoId s
dump2_tid1 = relbwEqDGSoId dump2_term1

dump2_term2 :: SOMetatermF
dump2_term2 = read "F1[0]"

dump2_tid2 :: SOMetaUnifRelSoId s
dump2_tid2 = relbwEqDGSoId dump2_term2

dump2_term3 :: SOMetatermF
dump2_term3 = read "F2[0]"

dump2_tid3 :: SOMetaUnifRelSoId s
dump2_tid3 = relbwEqDGSoId dump2_term3

dump2_soterm1 :: SOMetatermF
dump2_soterm1 = read "F3[2]"

dump2_sotid1 :: SOMetaUnifRelSoId s
dump2_sotid1 = relbwEqDGSoId dump2_soterm1

dump2_soterm2 :: SOMetatermF
dump2_soterm2 = read "F4[2]"

dump2_sotid2 :: SOMetaUnifRelSoId s
dump2_sotid2 = relbwEqDGSoId dump2_soterm2

dump2_soterm3 :: SOMetatermF
dump2_soterm3 = read "F5[2]"

dump2_sotid3 :: SOMetaUnifRelSoId s
dump2_sotid3 = relbwEqDGSoId dump2_soterm3

dump2_soterm4 :: SOMetatermF
dump2_soterm4 = read "F6[2]"

dump2_sotid4 :: SOMetaUnifRelSoId s
dump2_sotid4 = relbwEqDGSoId dump2_soterm4

dump2_exp1 :: SOMetaUnifSOExp
dump2_exp1 = read "F6[2]{F4[2]{F0[0],F1[0]},F5[2]{F0[0],F1[0]}}"

dump2_sig :: SOMetaSignature
dump2_sig = SOSignature (Signature [] [] EnumProc.Empty) (read "F0[0]" --> read "F1[0]" --> read "F2[0]" --> read "F3[2]" --> read "F4[2]" --> read "F5[2]" --> read "F6[2]" --> EnumProc.Empty)

dump2_mudg1 :: StateT (RTestSOMetaUnifDGraph s) (ST s) _
dump2_mudg1 = do
	{
		on_dgraph (newEqDGSONode dump2_term1);
		on_dgraph (newEqDGSONode dump2_term2);
		on_dgraph (newEqDGSONode dump2_term3);
		on_dgraph (newEqDGSONode dump2_soterm1);
		on_dgraph (newEqDGSONode dump2_soterm2);
		on_dgraph (newEqDGSONode dump2_soterm3);
		on_dgraph (newEqDGSONode dump2_soterm4);
		on_dgraph (newEqDGSOEdge dump2_sotid1 [dump2_tid1,dump2_tid2] dump2_tid3);
		on_dgraph (newEqDGSOEdge dump2_sotid4 [dump2_sotid2,dump2_sotid3] dump2_sotid1);
		pass
	}

dump2_mudg2 :: StateT (RTestSOMetaUnifDGraph s) (ST s) _
dump2_mudg2 = do {dump2_mudg1; on_vdgraph metaunif_so_dump}

dump2_t1 :: AutomatedTest
dump2_t1 = check_hsoedge dump2_sig "Checking that the higher s.o. edge is there before" dump2_mudg1 dump2_soterm4 [dump2_soterm2,dump2_soterm3] dump2_soterm1

dump2_t2 :: AutomatedTest
dump2_t2 = check_hsoedge dump2_sig "Checking that the original lower s.o. edge is there before" dump2_mudg1 dump2_soterm1 [dump2_term1,dump2_term2] dump2_term3

dump2_t3 :: AutomatedTest
dump2_t3 = check_not_soexp dump2_sig "Checking that the lower s.o. node does not match the resulting expression before" dump2_mudg1 dump2_exp1 dump2_term3

dump2_t4 :: AutomatedTest
dump2_t4 = check_hsoedge dump2_sig "Checking that the higher s.o. edge is there after" dump2_mudg2 dump2_soterm4 [dump2_soterm2,dump2_soterm3] dump2_soterm1

dump2_t5 :: AutomatedTest
dump2_t5 = check_not_hsoedge dump2_sig "Checking that the original lower s.o. edge is not there after" dump2_mudg2 dump2_soterm1 [dump2_term1,dump2_term2] dump2_term3

dump2_t6 :: AutomatedTest
dump2_t6 = check_soexp dump2_sig "Checking that the s.o. node matches the resulting expression after" dump2_mudg2 dump2_exp1 dump2_term3

dump2_tests :: String
dump2_tests = combine_test_results [dump2_t1,dump2_t2,dump2_t3,dump2_t4,dump2_t5,dump2_t6]




dump_test :: IO ()
dump_test = putStr "EXAMPLE 1\n\n" >> putStr dump1_tests >>
		putStr "EXAMPLE 2\n\n" >> putStr dump2_tests


sotconsistency1_term1 :: SOMetatermF
sotconsistency1_term1 = read "f1[1]"

sotconsistency1_tid1 :: SOMetaUnifRelSoId s
sotconsistency1_tid1 = relbwEqDGSoId sotconsistency1_term1

sotconsistency1_term2 :: SOMetatermF
sotconsistency1_term2 = read "f2[1]"

sotconsistency1_tid2 :: SOMetaUnifRelSoId s
sotconsistency1_tid2 = relbwEqDGSoId sotconsistency1_term2

sotconsistency1_sig :: SOMetaSignature
sotconsistency1_sig = SOSignature (Signature [] [EnumProc.Empty,read "f1[1]" --> read "f2[1]" --> EnumProc.Empty] EnumProc.Empty) EnumProc.Empty

sotconsistency1_mudg1 :: StateT (RTestSOMetaUnifDGraph s) (ST s) Bool
sotconsistency1_mudg1 = do
	{
		on_dgraph (newEqDGSONode sotconsistency1_term1);
		on_dgraph (newEqDGSONode sotconsistency1_term2);
		on_vdgraph metaunif_check_sot_consistency;
	}

sotconsistency1_mudg1_consistent :: Bool
sotconsistency1_mudg1_consistent = getStateTSTValue sotconsistency1_mudg1 (emptyRMUDG sotconsistency1_sig)

sotconsistency1_mudg2 :: StateT (RTestSOMetaUnifDGraph s) (ST s) Bool
sotconsistency1_mudg2 = do {sotconsistency1_mudg1; on_dgraph (mergeEqDGSONodes sotconsistency1_tid1 sotconsistency1_tid2); on_vdgraph metaunif_check_sot_consistency}

sotconsistency1_mudg2_consistent :: Bool
sotconsistency1_mudg2_consistent = getStateTSTValue sotconsistency1_mudg2 (emptyRMUDG sotconsistency1_sig)

sotconsistency1_t1 :: AutomatedTest
sotconsistency1_t1 = AT "Checking the graph is consistent before." (if sotconsistency1_mudg1_consistent then (ATR True "The graph is indeed consistent.") else (ATR False "The graph is inconsistent, but it should not be."))

sotconsistency1_t2 :: AutomatedTest
sotconsistency1_t2 = AT "Checking the graph is inconsistent after." (if sotconsistency1_mudg2_consistent then (ATR False "The graph is consistent, but it should not be.") else (ATR True "The graph is indeed inconsistent."))

sotconsistency1_tests :: String
sotconsistency1_tests = combine_test_results [sotconsistency1_t1,sotconsistency1_t2]


sotconsistency2_term1 :: SOMetatermF
sotconsistency2_term1 = read "f1[1]"

sotconsistency2_tid1 :: SOMetaUnifRelSoId s
sotconsistency2_tid1 = relbwEqDGSoId sotconsistency2_term1

sotconsistency2_term2 :: SOMetatermF
sotconsistency2_term2 = read "F2[1]"

sotconsistency2_tid2 :: SOMetaUnifRelSoId s
sotconsistency2_tid2 = relbwEqDGSoId sotconsistency2_term2

sotconsistency2_sig :: SOMetaSignature
sotconsistency2_sig = SOSignature (Signature [] [EnumProc.Empty,read "f1[1]" --> EnumProc.Empty] EnumProc.Empty) (read "F2[1]" --> EnumProc.Empty)

sotconsistency2_mudg1 :: StateT (RTestSOMetaUnifDGraph s) (ST s) Bool
sotconsistency2_mudg1 = do
	{
		on_dgraph (newEqDGSONode sotconsistency2_term1);
		on_dgraph (newEqDGSONode sotconsistency2_term2);
		on_vdgraph metaunif_check_sot_consistency;
	}

sotconsistency2_mudg1_consistent :: Bool
sotconsistency2_mudg1_consistent = getStateTSTValue sotconsistency2_mudg1 (emptyRMUDG sotconsistency2_sig)

sotconsistency2_mudg2 :: StateT (RTestSOMetaUnifDGraph s) (ST s) Bool
sotconsistency2_mudg2 = do {sotconsistency2_mudg1; on_dgraph (mergeEqDGSONodes sotconsistency2_tid1 sotconsistency2_tid2); on_vdgraph metaunif_check_sot_consistency}

sotconsistency2_mudg2_consistent :: Bool
sotconsistency2_mudg2_consistent = getStateTSTValue sotconsistency2_mudg2 (emptyRMUDG sotconsistency2_sig)

sotconsistency2_t1 :: AutomatedTest
sotconsistency2_t1 = AT "Checking the graph is consistent before." (if sotconsistency2_mudg1_consistent then (ATR True "The graph is indeed consistent.") else (ATR False "The graph is inconsistent, but it should not be."))

sotconsistency2_t2 :: AutomatedTest
sotconsistency2_t2 = AT "Checking the graph is consistent after." (if sotconsistency2_mudg2_consistent then (ATR True "The graph is indeed consistent.") else (ATR False "The graph is inconsistent, but it should not be."))

sotconsistency2_tests :: String
sotconsistency2_tests = combine_test_results [sotconsistency2_t1,sotconsistency2_t2]




sotconsistency_test :: IO ()
sotconsistency_test = putStr "EXAMPLE 1\n\n" >> putStr sotconsistency1_tests >>
			putStr "EXAMPLE 2\n\n" >> putStr sotconsistency2_tests






head_arity1_term1 :: SOMetatermF
head_arity1_term1 = read "f1[1]"

head_arity1_tid1 :: SOMetaUnifRelSoId s
head_arity1_tid1 = relbwEqDGSoId head_arity1_term1

head_arity1_term2 :: SOMetatermF
head_arity1_term2 = read "f2[1]"

head_arity1_tid2 :: SOMetaUnifRelSoId s
head_arity1_tid2 = relbwEqDGSoId head_arity1_term2

head_arity1_term3 :: SOMetatermF
head_arity1_term3 = read "F3[4]"

head_arity1_tid3 :: SOMetaUnifRelSoId s
head_arity1_tid3 = relbwEqDGSoId head_arity1_term3

head_arity1_term4 :: SOMetatermF
head_arity1_term4 = read "f4[3]"

head_arity1_tid4 :: SOMetaUnifRelSoId s
head_arity1_tid4 = relbwEqDGSoId head_arity1_term4

head_arity1_term5 :: SOMetatermF
head_arity1_term5 = read "f5[1]"

head_arity1_tid5 :: SOMetaUnifRelSoId s
head_arity1_tid5 = relbwEqDGSoId head_arity1_term5

head_arity1_sig :: SOMetaSignature
head_arity1_sig = SOSignature (Signature [] [EnumProc.Empty,read "f1[1]" --> read "f2[1]" --> read "f5[1]" --> EnumProc.Empty, EnumProc.Empty, read "f4[3]" --> EnumProc.Empty] EnumProc.Empty) (read "F3[4]" --> EnumProc.Empty)

head_arity1_mudg1 :: StateT (RTestSOMetaUnifDGraph s) (ST s) Bool
head_arity1_mudg1 = do
	{
		on_dgraph (newEqDGSONode head_arity1_term1);
		on_dgraph (newEqDGSONode head_arity1_term2);
		on_dgraph (newEqDGSONode head_arity1_term3);
		on_dgraph (newEqDGSONode head_arity1_term4);
		on_dgraph (newEqDGSONode head_arity1_term5);
		on_dgraph (newEqDGSOEdge head_arity1_tid3 [head_arity1_tid1,head_arity1_tid2] head_arity1_tid5);
		on_vdgraph metaunif_check_head_arity_so
	}

head_arity1_mudg1_consistent :: Bool
head_arity1_mudg1_consistent = getStateTSTValue head_arity1_mudg1 (emptyRMUDG head_arity1_sig)

head_arity1_mudg2 :: StateT (RTestSOMetaUnifDGraph s) (ST s) Bool
head_arity1_mudg2 = do
	{
		head_arity1_mudg1;
		on_dgraph (mergeEqDGSONodes head_arity1_tid3 head_arity1_tid4);
		on_vdgraph metaunif_check_head_arity_so
	}

head_arity1_mudg2_consistent :: Bool
head_arity1_mudg2_consistent = getStateTSTValue head_arity1_mudg2 (emptyRMUDG head_arity1_sig)

head_arity1_t1 :: AutomatedTest
head_arity1_t1 = AT "Checking the graph is consistent before." (if head_arity1_mudg1_consistent then (ATR True "The graph is indeed consistent.") else (ATR False "The graph is inconsistent, but it should not be."))

head_arity1_t2 :: AutomatedTest
head_arity1_t2 = AT "Checking the graph is inconsistent after." (if head_arity1_mudg2_consistent then (ATR False "The graph is consistent, but it should not be.") else (ATR True "The graph is indeed inconsistent."))

head_arity1_tests :: String
head_arity1_tests = combine_test_results [head_arity1_t1,head_arity1_t2]



head_arity_test :: IO ()
head_arity_test = putStr "EXAMPLE 1\n\n" >> putStr head_arity1_tests



target_arity1_term1 :: SOMetatermF
target_arity1_term1 = read "f1[2]"

target_arity1_tid1 :: SOMetaUnifRelSoId s
target_arity1_tid1 = relbwEqDGSoId target_arity1_term1

target_arity1_term2 :: SOMetatermF
target_arity1_term2 = read "f2[1]"

target_arity1_tid2 :: SOMetaUnifRelSoId s
target_arity1_tid2 = relbwEqDGSoId target_arity1_term2

target_arity1_term3 :: SOMetatermF
target_arity1_term3 = read "f3[2]"

target_arity1_tid3 :: SOMetaUnifRelSoId s
target_arity1_tid3 = relbwEqDGSoId target_arity1_term3

target_arity1_sig :: SOMetaSignature
target_arity1_sig = SOSignature (Signature [] [EnumProc.Empty,read "f1[1]" --> read "f2[1]" --> EnumProc.Empty, read "f3[2]" --> EnumProc.Empty] EnumProc.Empty) EnumProc.Empty

target_arity1_mudg1 :: StateT (RTestSOMetaUnifDGraph s) (ST s) Bool
target_arity1_mudg1 = do
	{
		on_dgraph (newEqDGSONode target_arity1_term1);
		on_dgraph (newEqDGSONode target_arity1_term2);
		on_dgraph (newEqDGSONode target_arity1_term3);
		on_vdgraph metaunif_check_target_arity_so
	}

target_arity1_mudg1_consistent :: Bool
target_arity1_mudg1_consistent = getStateTSTValue target_arity1_mudg1 (emptyRMUDG target_arity1_sig)

target_arity1_mudg2 :: StateT (RTestSOMetaUnifDGraph s) (ST s) Bool
target_arity1_mudg2 = do
	{
		target_arity1_mudg1;
		on_dgraph (newEqDGSOEdge target_arity1_tid2 [target_arity1_tid1] target_arity1_tid3);
		on_vdgraph metaunif_check_target_arity_so
	}

target_arity1_mudg2_consistent :: Bool
target_arity1_mudg2_consistent = getStateTSTValue target_arity1_mudg2 (emptyRMUDG target_arity1_sig)

target_arity1_t1 :: AutomatedTest
target_arity1_t1 = AT "Checking the graph is consistent before." (if target_arity1_mudg1_consistent then (ATR True "The graph is indeed consistent.") else (ATR False "The graph is inconsistent, but it should not be."))

target_arity1_t2 :: AutomatedTest
target_arity1_t2 = AT "Checking the graph is inconsistent after." (if target_arity1_mudg2_consistent then (ATR False "The graph is consistent, but it should not be.") else (ATR True "The graph is indeed inconsistent."))

target_arity1_tests :: String
target_arity1_tests = combine_test_results [target_arity1_t1,target_arity1_t2]

target_arity2_term1 :: SOMetatermF
target_arity2_term1 = read "f1[2]"

target_arity2_tid1 :: SOMetaUnifRelSoId s
target_arity2_tid1 = relbwEqDGSoId target_arity2_term1

target_arity2_term2 :: SOMetatermF
target_arity2_term2 = read "f2[1]"

target_arity2_tid2 :: SOMetaUnifRelSoId s
target_arity2_tid2 = relbwEqDGSoId target_arity2_term2

target_arity2_term3 :: SOMetatermF
target_arity2_term3 = read "F3[1]"

target_arity2_tid3 :: SOMetaUnifRelSoId s
target_arity2_tid3 = relbwEqDGSoId target_arity2_term3

target_arity2_sig :: SOMetaSignature
target_arity2_sig = SOSignature (Signature [] [EnumProc.Empty,read "f2[1]" --> EnumProc.Empty, read "f1[2]" --> EnumProc.Empty] EnumProc.Empty) (read "F3[1]" --> EnumProc.Empty)

target_arity2_mudg1 :: StateT (RTestSOMetaUnifDGraph s) (ST s) Bool
target_arity2_mudg1 = do
	{
		on_dgraph (newEqDGSONode target_arity2_term1);
		on_dgraph (newEqDGSONode target_arity2_term2);
		on_dgraph (newEqDGSONode target_arity2_term3);
		on_vdgraph metaunif_check_target_arity_so
	}

target_arity2_mudg1_consistent :: Bool
target_arity2_mudg1_consistent = getStateTSTValue target_arity2_mudg1 (emptyRMUDG target_arity2_sig)

target_arity2_mudg2 :: StateT (RTestSOMetaUnifDGraph s) (ST s) Bool
target_arity2_mudg2 = do
	{
		target_arity2_mudg1;
		on_dgraph (newEqDGSOEdge target_arity2_tid2 [target_arity2_tid1] target_arity2_tid3);
		on_vdgraph metaunif_check_target_arity_so
	}

target_arity2_mudg2_consistent :: Bool
target_arity2_mudg2_consistent = getStateTSTValue target_arity2_mudg2 (emptyRMUDG target_arity2_sig)

target_arity2_t1 :: AutomatedTest
target_arity2_t1 = AT "Checking the graph is consistent before." (if target_arity2_mudg1_consistent then (ATR True "The graph is indeed consistent.") else (ATR False "The graph is inconsistent, but it should not be."))

target_arity2_t2 :: AutomatedTest
target_arity2_t2 = AT "Checking the graph is inconsistent after." (if target_arity2_mudg2_consistent then (ATR False "The graph is consistent, but it should not be.") else (ATR True "The graph is indeed inconsistent."))

target_arity2_tests :: String
target_arity2_tests = combine_test_results [target_arity2_t1,target_arity2_t2]

target_arity3_term1 :: SOMetatermF
target_arity3_term1 = read "f1[2]"

target_arity3_tid1 :: SOMetaUnifRelSoId s
target_arity3_tid1 = relbwEqDGSoId target_arity3_term1

target_arity3_term2 :: SOMetatermF
target_arity3_term2 = read "f2[1]"

target_arity3_tid2 :: SOMetaUnifRelSoId s
target_arity3_tid2 = relbwEqDGSoId target_arity3_term2

target_arity3_term3 :: SOMetatermF
target_arity3_term3 = read "F3[2]"

target_arity3_tid3 :: SOMetaUnifRelSoId s
target_arity3_tid3 = relbwEqDGSoId target_arity3_term3

target_arity3_sig :: SOMetaSignature
target_arity3_sig = SOSignature (Signature [] [EnumProc.Empty,read "f2[1]" --> EnumProc.Empty, read "f1[2]" --> EnumProc.Empty] EnumProc.Empty) (read "F3[2]" --> EnumProc.Empty)

target_arity3_mudg1 :: StateT (RTestSOMetaUnifDGraph s) (ST s) Bool
target_arity3_mudg1 = do
	{
		on_dgraph (newEqDGSONode target_arity3_term1);
		on_dgraph (newEqDGSONode target_arity3_term2);
		on_dgraph (newEqDGSONode target_arity3_term3);
		on_vdgraph metaunif_check_target_arity_so
	}

target_arity3_mudg1_consistent :: Bool
target_arity3_mudg1_consistent = getStateTSTValue target_arity3_mudg1 (emptyRMUDG target_arity3_sig)

target_arity3_mudg2 :: StateT (RTestSOMetaUnifDGraph s) (ST s) Bool
target_arity3_mudg2 = do
	{
		target_arity3_mudg1;
		on_dgraph (newEqDGSOEdge target_arity3_tid2 [target_arity3_tid1] target_arity3_tid3);
		on_vdgraph metaunif_check_target_arity_so
	}

target_arity3_mudg2_consistent :: Bool
target_arity3_mudg2_consistent = getStateTSTValue target_arity3_mudg2 (emptyRMUDG target_arity3_sig)

target_arity3_t1 :: AutomatedTest
target_arity3_t1 = AT "Checking the graph is consistent before." (if target_arity3_mudg1_consistent then (ATR True "The graph is indeed consistent.") else (ATR False "The graph is inconsistent, but it should not be."))

target_arity3_t2 :: AutomatedTest
target_arity3_t2 = AT "Checking the graph is consistent after." (if target_arity3_mudg2_consistent then (ATR True "The graph is indeed consistent.") else (ATR False "The graph is inconsistent, but it should not be."))

target_arity3_tests :: String
target_arity3_tests = combine_test_results [target_arity3_t1,target_arity3_t2]

target_arity4_term1 :: SOMetatermF
target_arity4_term1 = read "f1[1]"

target_arity4_tid1 :: SOMetaUnifRelSoId s
target_arity4_tid1 = relbwEqDGSoId target_arity4_term1

target_arity4_term2 :: SOMetatermF
target_arity4_term2 = read "f2[1]"

target_arity4_tid2 :: SOMetaUnifRelSoId s
target_arity4_tid2 = relbwEqDGSoId target_arity4_term2

target_arity4_term3 :: SOMetatermF
target_arity4_term3 = read "f3[2]"

target_arity4_tid3 :: SOMetaUnifRelSoId s
target_arity4_tid3 = relbwEqDGSoId target_arity4_term3

target_arity4_term4 :: SOMetatermF
target_arity4_term4 = read "F4[3]"

target_arity4_tid4 :: SOMetaUnifRelSoId s
target_arity4_tid4 = relbwEqDGSoId target_arity4_term4

target_arity4_term5 :: SOMetatermF
target_arity4_term5 = read "f5[1]"

target_arity4_tid5 :: SOMetaUnifRelSoId s
target_arity4_tid5 = relbwEqDGSoId target_arity4_term5

target_arity4_term6 :: SOMetatermF
target_arity4_term6 = read "F6[1]"

target_arity4_tid6 :: SOMetaUnifRelSoId s
target_arity4_tid6 = relbwEqDGSoId target_arity4_term6

target_arity4_sig :: SOMetaSignature
target_arity4_sig = SOSignature (Signature [] [EnumProc.Empty,read "f1[1]" --> read "f2[1]" --> read "f5[1]" --> EnumProc.Empty, read "f3[2]" --> EnumProc.Empty] EnumProc.Empty) (read "F4[3]" --> read "F6[1]" --> EnumProc.Empty)

target_arity4_mudg1 :: StateT (RTestSOMetaUnifDGraph s) (ST s) Bool
target_arity4_mudg1 = do
	{
		on_dgraph (newEqDGSONode target_arity4_term1);
		on_dgraph (newEqDGSONode target_arity4_term2);
		on_dgraph (newEqDGSONode target_arity4_term3);
		on_dgraph (newEqDGSONode target_arity4_term4);
		on_dgraph (newEqDGSONode target_arity4_term5);
		on_dgraph (newEqDGSONode target_arity4_term6);
		on_vdgraph metaunif_check_target_arity_so
	}

target_arity4_mudg1_consistent :: Bool
target_arity4_mudg1_consistent = getStateTSTValue target_arity4_mudg1 (emptyRMUDG target_arity4_sig)

target_arity4_mudg2 :: StateT (RTestSOMetaUnifDGraph s) (ST s) Bool
target_arity4_mudg2 = do
	{
		target_arity4_mudg1;
		on_dgraph (newEqDGSOEdge target_arity4_tid3 [target_arity4_tid1,target_arity4_tid2] target_arity4_tid4);
		on_dgraph (newEqDGSOEdge target_arity4_tid5 [target_arity4_tid4] target_arity4_tid6);
		on_vdgraph metaunif_check_target_arity_so
	}

target_arity4_mudg2_consistent :: Bool
target_arity4_mudg2_consistent = getStateTSTValue target_arity4_mudg2 (emptyRMUDG target_arity4_sig)

target_arity4_t1 :: AutomatedTest
target_arity4_t1 = AT "Checking the graph is consistent before." (if target_arity4_mudg1_consistent then (ATR True "The graph is indeed consistent.") else (ATR False "The graph is inconsistent, but it should not be."))

target_arity4_t2 :: AutomatedTest
target_arity4_t2 = AT "Checking the graph is consistent after." (if target_arity4_mudg2_consistent then (ATR True "The graph is indeed consistent.") else (ATR False "The graph is inconsistent, but it should not be."))

target_arity4_tests :: String
target_arity4_tests = combine_test_results [target_arity4_t1,target_arity4_t2]



target_arity_test :: IO ()
target_arity_test = putStr "EXAMPLE 1\n\n" >> putStr target_arity1_tests >>
			putStr "EXAMPLE 2\n\n" >> putStr target_arity2_tests >>
			putStr "EXAMPLE 3\n\n" >> putStr target_arity3_tests >>
			putStr "EXAMPLE 4\n\n" >> putStr target_arity4_tests



occurs_check1_term1 :: SOMetatermF
occurs_check1_term1 = read "F1[1]"

occurs_check1_tid1 :: SOMetaUnifRelSoId s
occurs_check1_tid1 = relbwEqDGSoId occurs_check1_term1

occurs_check1_term2 :: SOMetatermF
occurs_check1_term2 = read "F2[1]"

occurs_check1_tid2 :: SOMetaUnifRelSoId s
occurs_check1_tid2 = relbwEqDGSoId occurs_check1_term2

occurs_check1_term3 :: SOMetatermF
occurs_check1_term3 = read "F3[1]"

occurs_check1_tid3 :: SOMetaUnifRelSoId s
occurs_check1_tid3 = relbwEqDGSoId occurs_check1_term3

occurs_check1_term4 :: SOMetatermF
occurs_check1_term4 = read "F4[1]"

occurs_check1_tid4 :: SOMetaUnifRelSoId s
occurs_check1_tid4 = relbwEqDGSoId occurs_check1_term4

occurs_check1_term5 :: SOMetatermF
occurs_check1_term5 = read "F5[1]"

occurs_check1_tid5 :: SOMetaUnifRelSoId s
occurs_check1_tid5 = relbwEqDGSoId occurs_check1_term5

occurs_check1_term6 :: SOMetatermF
occurs_check1_term6 = read "F6[1]"

occurs_check1_tid6 :: SOMetaUnifRelSoId s
occurs_check1_tid6 = relbwEqDGSoId occurs_check1_term6

occurs_check1_sig :: SOMetaSignature
occurs_check1_sig = SOSignature (Signature [] [] EnumProc.Empty) (read "F1[1]" --> read "F2[1]" --> read "F3[1]" --> read "F4[1]" --> read "F5[1]" --> read "F6[1]" --> EnumProc.Empty)

occurs_check1_mudg1 :: StateT (RTestSOMetaUnifDGraph s) (ST s) Bool
occurs_check1_mudg1 = do
	{
		on_dgraph (newEqDGSONode occurs_check1_term1);
		on_dgraph (newEqDGSONode occurs_check1_term2);
		on_dgraph (newEqDGSONode occurs_check1_term3);
		on_dgraph (newEqDGSONode occurs_check1_term4);
		on_dgraph (newEqDGSONode occurs_check1_term5);
		on_dgraph (newEqDGSOEdge occurs_check1_tid6 [occurs_check1_tid1] occurs_check1_tid2); 
		on_dgraph (newEqDGSOEdge occurs_check1_tid6 [occurs_check1_tid2] occurs_check1_tid3);
		on_dgraph (newEqDGSOEdge occurs_check1_tid6 [occurs_check1_tid3] occurs_check1_tid4);
		on_dgraph (newEqDGSOEdge occurs_check1_tid6 [occurs_check1_tid4] occurs_check1_tid5);
		on_vdgraph metaunif_occurs_check_so
	}

occurs_check1_mudg1_consistent :: Bool
occurs_check1_mudg1_consistent = getStateTSTValue occurs_check1_mudg1 (emptyRMUDG occurs_check1_sig)

occurs_check1_mudg2 :: StateT (RTestSOMetaUnifDGraph s) (ST s) Bool
occurs_check1_mudg2 = do
	{
		occurs_check1_mudg1;
		on_dgraph (newEqDGSOEdge occurs_check1_tid6 [occurs_check1_tid5] occurs_check1_tid1);
		on_vdgraph metaunif_occurs_check_so
	}

occurs_check1_mudg2_consistent :: Bool
occurs_check1_mudg2_consistent = getStateTSTValue occurs_check1_mudg2 (emptyRMUDG occurs_check1_sig)

occurs_check1_mudg3 :: StateT (RTestSOMetaUnifDGraph s) (ST s) Bool
occurs_check1_mudg3 = do
	{
		occurs_check1_mudg1;
		on_dgraph (newEqDGSOEdge occurs_check1_tid6 [occurs_check1_tid4] occurs_check1_tid2);
		on_vdgraph metaunif_occurs_check_so
	}

occurs_check1_mudg3_consistent :: Bool
occurs_check1_mudg3_consistent = getStateTSTValue occurs_check1_mudg3 (emptyRMUDG occurs_check1_sig)

occurs_check1_mudg4 :: StateT (RTestSOMetaUnifDGraph s) (ST s) Bool
occurs_check1_mudg4 = do
	{
		occurs_check1_mudg1;
		on_dgraph (newEqDGSOEdge occurs_check1_tid6 [occurs_check1_tid3] occurs_check1_tid3);
		on_vdgraph metaunif_occurs_check_so
	}

occurs_check1_mudg4_consistent :: Bool
occurs_check1_mudg4_consistent = getStateTSTValue occurs_check1_mudg4 (emptyRMUDG occurs_check1_sig)

occurs_check1_mudg5 :: StateT (RTestSOMetaUnifDGraph s) (ST s) Bool
occurs_check1_mudg5 = do
	{
		occurs_check1_mudg1;
		on_dgraph (newEqDGSOEdge occurs_check1_tid6 [occurs_check1_tid6] occurs_check1_tid1);
		on_vdgraph metaunif_occurs_check_so
	}

occurs_check1_mudg5_consistent :: Bool
occurs_check1_mudg5_consistent = getStateTSTValue occurs_check1_mudg5 (emptyRMUDG occurs_check1_sig)

occurs_check1_mudg6 :: StateT (RTestSOMetaUnifDGraph s) (ST s) Bool
occurs_check1_mudg6 = do
	{
		occurs_check1_mudg1;
		on_dgraph (newEqDGSOEdge occurs_check1_tid5 [occurs_check1_tid6] occurs_check1_tid1);
		on_vdgraph metaunif_occurs_check_so
	}

occurs_check1_mudg6_consistent :: Bool
occurs_check1_mudg6_consistent = getStateTSTValue occurs_check1_mudg6 (emptyRMUDG occurs_check1_sig)

occurs_check1_mudg7 :: StateT (RTestSOMetaUnifDGraph s) (ST s) Bool
occurs_check1_mudg7 = do
	{
		occurs_check1_mudg1;
		on_dgraph (newEqDGSOEdge occurs_check1_tid1 [occurs_check1_tid2] occurs_check1_tid6);
		on_vdgraph metaunif_occurs_check_so
	}

occurs_check1_mudg7_consistent :: Bool
occurs_check1_mudg7_consistent = getStateTSTValue occurs_check1_mudg7 (emptyRMUDG occurs_check1_sig)

occurs_check1_mudg8 :: StateT (RTestSOMetaUnifDGraph s) (ST s) Bool
occurs_check1_mudg8 = do
	{
		occurs_check1_mudg1;
		on_dgraph (newEqDGSOEdge occurs_check1_tid2 [occurs_check1_tid1] occurs_check1_tid6);
		on_vdgraph metaunif_occurs_check_so
	}

occurs_check1_mudg8_consistent :: Bool
occurs_check1_mudg8_consistent = getStateTSTValue occurs_check1_mudg8 (emptyRMUDG occurs_check1_sig)

occurs_check1_mudg9 :: StateT (RTestSOMetaUnifDGraph s) (ST s) Bool
occurs_check1_mudg9 = do
	{
		occurs_check1_mudg1;
		on_dgraph (newEqDGSOEdge occurs_check1_tid1 [occurs_check1_tid1] occurs_check1_tid6);
		on_vdgraph metaunif_occurs_check_so
	}

occurs_check1_mudg9_consistent :: Bool
occurs_check1_mudg9_consistent = getStateTSTValue occurs_check1_mudg9 (emptyRMUDG occurs_check1_sig)

occurs_check1_t1 :: AutomatedTest
occurs_check1_t1 = AT "Checking the graph is consistent before." (if occurs_check1_mudg1_consistent then (ATR True "The graph is indeed consistent.") else (ATR False "The graph is inconsistent, but it should not be."))

occurs_check1_t2 :: AutomatedTest
occurs_check1_t2 = AT "Checking the graph is inconsistent after (1)." (if occurs_check1_mudg2_consistent then (ATR False "The graph is consistent, but it should not be.") else (ATR True "The graph is indeed inconsistent."))

occurs_check1_t3 :: AutomatedTest
occurs_check1_t3 = AT "Checking the graph is inconsistent after (2)." (if occurs_check1_mudg3_consistent then (ATR False "The graph is consistent, but it should not be.") else (ATR True "The graph is indeed inconsistent."))

occurs_check1_t4 :: AutomatedTest
occurs_check1_t4 = AT "Checking the graph is inconsistent after (3)." (if occurs_check1_mudg4_consistent then (ATR False "The graph is consistent, but it should not be.") else (ATR True "The graph is indeed inconsistent."))

occurs_check1_t5 :: AutomatedTest
occurs_check1_t5 = AT "Checking the graph is consistent after (4)." (if occurs_check1_mudg5_consistent then (ATR True "The graph is indeed consistent.") else (ATR False "The graph is inconsistent, but it should not be."))

occurs_check1_t6 :: AutomatedTest
occurs_check1_t6 = AT "Checking the graph is inconsistent after (5)." (if occurs_check1_mudg6_consistent then (ATR False "The graph is consistent, but it should not be.") else (ATR True "The graph is indeed inconsistent."))

occurs_check1_t7 :: AutomatedTest
occurs_check1_t7 = AT "Checking the graph is inconsistent after (6)." (if occurs_check1_mudg7_consistent then (ATR False "The graph is consistent, but it should not be.") else (ATR True "The graph is indeed inconsistent."))

occurs_check1_t8 :: AutomatedTest
occurs_check1_t8 = AT "Checking the graph is inconsistent after (7)." (if occurs_check1_mudg8_consistent then (ATR False "The graph is consistent, but it should not be.") else (ATR True "The graph is indeed inconsistent."))

occurs_check1_t9 :: AutomatedTest
occurs_check1_t9 = AT "Checking the graph is consistent after (8)." (if occurs_check1_mudg9_consistent then (ATR True "The graph is indeed consistent.") else (ATR False "The graph is inconsistent, but it should not be."))

occurs_check1_tests :: String
occurs_check1_tests = combine_test_results [occurs_check1_t1,occurs_check1_t2,occurs_check1_t3,occurs_check1_t4,occurs_check1_t5,occurs_check1_t6,occurs_check1_t7,occurs_check1_t8,occurs_check1_t9]



occurs_check_test :: IO ()
occurs_check_test = putStr "EXAMPLE 1\n\n" >> putStr occurs_check1_tests


factorize_tests_n :: Int
factorize_tests_n = 200

factorize1_term1 :: SOMetaTermDependant
factorize1_term1 = read "u0 x0"

factorize1_tid1 :: SOMetaUnifRelFoId s
factorize1_tid1 = relbwEqDGFoId factorize1_term1

factorize1_term2 :: SOMetaTermDependant
factorize1_term2 = read "u0 x1"

factorize1_tid2 :: SOMetaUnifRelFoId s
factorize1_tid2 = relbwEqDGFoId factorize1_term2

factorize1_term3 :: SOMetaTermDependant
factorize1_term3 = read "u0 x2"

factorize1_tid3 :: SOMetaUnifRelFoId s
factorize1_tid3 = relbwEqDGFoId factorize1_term3

factorize1_soterm1 :: SOMetatermF
factorize1_soterm1 = read "f1[1]"

factorize1_sotid1 :: SOMetaUnifRelSoId s
factorize1_sotid1 = relbwEqDGSoId factorize1_soterm1

factorize1_sig :: SOMetaSignature
factorize1_sig = SOSignature (Signature [] [EnumProc.Empty, read "f1[1]" --> EnumProc.Empty] (read "x0" --> read "x1" --> read "x2" --> EnumProc.Empty)) EnumProc.Empty

factorize1_mudg1 :: RSOMetaUnifDGraph
factorize1_mudg1 = RESUnifVDGraph (snd <$> runStateT (mzoom lens_esunifdgraph_dgraph (do
	{
		newEqDGFOEdge factorize1_sotid1 [factorize1_tid1] factorize1_tid3;
		newEqDGFOEdge factorize1_sotid1 [factorize1_tid2] factorize1_tid3
	})) (emptyVDGraph factorize1_sig))

factorize1_as1 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize1_as1 = ImplicitAS factorize1_mudg1

factorize1_as2 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize1_as2 = metaunif_prenormalize factorize1_as1

factorize1_as3 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize1_as3 = metaunif_seminormalize factorize1_as1

factorize1_t1 :: AutomatedTest
factorize1_t1 = check_all_resuvdg factorize_tests_n "Checking that the sources are not equivalent before" (\title -> \st -> check_not_foequiv factorize1_sig title st factorize1_term1 factorize1_term2) factorize1_as1

factorize1_t2 :: AutomatedTest
factorize1_t2 = check_all_resuvdg factorize_tests_n "Checking that the sources are not equivalent after prenormalization" (\title -> \st -> check_not_foequiv factorize1_sig title st factorize1_term1 factorize1_term2) factorize1_as2

factorize1_t3 :: AutomatedTest	
factorize1_t3 = check_all_resuvdg factorize_tests_n "Checking that the sources are equivalent after seminormalization" (\title -> \st -> check_foequiv factorize1_sig title st factorize1_term1 factorize1_term2) factorize1_as3

factorize1_t4 :: AutomatedTest
factorize1_t4 = check_exactly_as "Checking that there is exactly one result" 1 factorize1_as3

factorize1_tests :: String
factorize1_tests = combine_test_results [factorize1_t1, factorize1_t2, factorize1_t3, factorize1_t4]

factorize2_term1 :: SOMetatermF
factorize2_term1 = read "F0[1]"

factorize2_tid1 :: SOMetaUnifRelSoId s
factorize2_tid1 = relbwEqDGSoId factorize2_term1

factorize2_term2 :: SOMetatermF
factorize2_term2 = read "F1[1]"

factorize2_tid2 :: SOMetaUnifRelSoId s
factorize2_tid2 = relbwEqDGSoId factorize2_term2

factorize2_term3 :: SOMetatermF
factorize2_term3 = read "F2[1]"

factorize2_tid3 :: SOMetaUnifRelSoId s
factorize2_tid3 = relbwEqDGSoId factorize2_term3

factorize2_soterm1 :: SOMetatermF
factorize2_soterm1 = read "f1[1]"

factorize2_sotid1 :: SOMetaUnifRelSoId s
factorize2_sotid1 = relbwEqDGSoId factorize2_soterm1

factorize2_sig :: SOMetaSignature
factorize2_sig = SOSignature (Signature [] [EnumProc.Empty, read "f1[1]" --> EnumProc.Empty] EnumProc.Empty) (read "F0[1]" --> read "F1[1]" --> read "F2[1]" --> EnumProc.Empty)

factorize2_mudg1 :: RSOMetaUnifDGraph
factorize2_mudg1 = RESUnifVDGraph (snd <$> runStateT (mzoom lens_esunifdgraph_dgraph (do
	{
		newEqDGSOEdge factorize2_sotid1 [factorize2_tid1] factorize2_tid3;
		newEqDGSOEdge factorize2_sotid1 [factorize2_tid2] factorize2_tid3
	})) (emptyVDGraph factorize2_sig))

factorize2_as1 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize2_as1 = ImplicitAS factorize2_mudg1

factorize2_as2 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize2_as2 = metaunif_prenormalize factorize2_as1

factorize2_as3 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize2_as3 = metaunif_seminormalize factorize2_as1

factorize2_t1 :: AutomatedTest
factorize2_t1 = check_all_resuvdg factorize_tests_n "Checking that the sources are not equivalent before" (\title -> \st -> check_not_soequiv factorize2_sig title st factorize2_term1 factorize2_term2) factorize2_as1

factorize2_t2 :: AutomatedTest
factorize2_t2 = check_all_resuvdg factorize_tests_n "Checking that the sources are not equivalent after prenormalization" (\title -> \st -> check_not_soequiv factorize2_sig title st factorize2_term1 factorize2_term2) factorize2_as2

factorize2_t3 :: AutomatedTest	
factorize2_t3 = check_all_resuvdg factorize_tests_n "Checking that the sources are equivalent after seminormalization" (\title -> \st -> check_soequiv factorize2_sig title st factorize2_term1 factorize2_term2) factorize2_as3

factorize2_t4 :: AutomatedTest
factorize2_t4 = check_exactly_as "Checking that there is exactly one result" 1 factorize1_as3

factorize2_tests :: String
factorize2_tests = combine_test_results [factorize2_t1, factorize2_t2, factorize2_t3, factorize2_t4]

factorize3_term1 :: SOMetaTermDependant
factorize3_term1 = read "u0 x0"

factorize3_tid1 :: SOMetaUnifRelFoId s
factorize3_tid1 = relbwEqDGFoId factorize3_term1

factorize3_term2 :: SOMetaTermDependant
factorize3_term2 = read "u0 x1"

factorize3_tid2 :: SOMetaUnifRelFoId s
factorize3_tid2 = relbwEqDGFoId factorize3_term2

factorize3_term3 :: SOMetaTermDependant
factorize3_term3 = read "u0 x2"

factorize3_tid3 :: SOMetaUnifRelFoId s
factorize3_tid3 = relbwEqDGFoId factorize3_term3

factorize3_soterm1 :: SOMetatermF
factorize3_soterm1 = read "f1[1]"

factorize3_sotid1 :: SOMetaUnifRelSoId s
factorize3_sotid1 = relbwEqDGSoId factorize3_soterm1

factorize3_soterm2 :: SOMetatermF
factorize3_soterm2 = read "f2[1]"

factorize3_sotid2 :: SOMetaUnifRelSoId s
factorize3_sotid2 = relbwEqDGSoId factorize3_soterm2

factorize3_sig :: SOMetaSignature
factorize3_sig = SOSignature (Signature [] [EnumProc.Empty, read "f1[1]" --> read "f2[1]" --> EnumProc.Empty] (read "x0" --> read "x1" --> read "x2" --> EnumProc.Empty)) EnumProc.Empty

factorize3_mudg1 :: RSOMetaUnifDGraph
factorize3_mudg1 = RESUnifVDGraph (snd <$> runStateT (mzoom lens_esunifdgraph_dgraph (do
	{
		newEqDGFOEdge factorize3_sotid1 [factorize3_tid1] factorize3_tid3;
		newEqDGFOEdge factorize3_sotid2 [factorize3_tid2] factorize3_tid3
	})) (emptyVDGraph factorize3_sig))

factorize3_as1 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize3_as1 = ImplicitAS factorize3_mudg1

factorize3_as2 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize3_as2 = metaunif_prenormalize factorize3_as1

factorize3_as3 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize3_as3 = metaunif_seminormalize factorize3_as1

factorize3_t1 :: AutomatedTest
factorize3_t1 = check_exactly_as "Checking that there is exactly one solution before" 1 factorize3_as1

factorize3_t2 :: AutomatedTest
factorize3_t2 = check_exactly_as "Checking that there is exactly one solution after prenormalization" 1 factorize3_as2

factorize3_t3 :: AutomatedTest
factorize3_t3 = check_exactly_as "Checking that there are no solutions after seminormalization" 0 factorize3_as3

factorize3_tests :: String
factorize3_tests = combine_test_results [factorize3_t1, factorize3_t2, factorize3_t3]

factorize4_term1 :: SOMetatermF
factorize4_term1 = read "F0[1]"

factorize4_tid1 :: SOMetaUnifRelSoId s
factorize4_tid1 = relbwEqDGSoId factorize4_term1

factorize4_term2 :: SOMetatermF
factorize4_term2 = read "F1[1]"

factorize4_tid2 :: SOMetaUnifRelSoId s
factorize4_tid2 = relbwEqDGSoId factorize4_term2

factorize4_term3 :: SOMetatermF
factorize4_term3 = read "F2[1]"

factorize4_tid3 :: SOMetaUnifRelSoId s
factorize4_tid3 = relbwEqDGSoId factorize4_term3

factorize4_soterm1 :: SOMetatermF
factorize4_soterm1 = read "f1[1]"

factorize4_sotid1 :: SOMetaUnifRelSoId s
factorize4_sotid1 = relbwEqDGSoId factorize4_soterm1

factorize4_soterm2 :: SOMetatermF
factorize4_soterm2 = read "f2[1]"

factorize4_sotid2 :: SOMetaUnifRelSoId s
factorize4_sotid2 = relbwEqDGSoId factorize4_soterm2

factorize4_sig :: SOMetaSignature
factorize4_sig = SOSignature (Signature [] [EnumProc.Empty, read "f1[1]" --> read "f2[1]" --> EnumProc.Empty] EnumProc.Empty) (read "F0[1]" --> read "F1[1]" --> read "F2[1]" --> EnumProc.Empty)

factorize4_mudg1 :: RSOMetaUnifDGraph
factorize4_mudg1 = RESUnifVDGraph (snd <$> runStateT (mzoom lens_esunifdgraph_dgraph (do
	{
		newEqDGSOEdge factorize4_sotid1 [factorize4_tid1] factorize4_tid3;
		newEqDGSOEdge factorize4_sotid2 [factorize4_tid2] factorize4_tid3
	})) (emptyVDGraph factorize4_sig))

factorize4_as1 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize4_as1 = ImplicitAS factorize4_mudg1

factorize4_as2 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize4_as2 = metaunif_prenormalize factorize4_as1

factorize4_as3 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize4_as3 = metaunif_seminormalize factorize4_as1

factorize4_t1 :: AutomatedTest
factorize4_t1 = check_exactly_as "Checking that there is exactly one solution before" 1 factorize4_as1

factorize4_t2 :: AutomatedTest
factorize4_t2 = check_exactly_as "Checking that there is exactly one solution after prenormalization" 1 factorize4_as2

factorize4_t3 :: AutomatedTest
factorize4_t3 = check_exactly_as "Checking that there are no solutions after seminormalization" 0 factorize4_as3

factorize4_tests :: String
factorize4_tests = combine_test_results [factorize4_t1, factorize4_t2, factorize4_t3]

factorize5_term1 :: SOMetaTermDependant
factorize5_term1 = read "u0 x0"

factorize5_tid1 :: SOMetaUnifRelFoId s
factorize5_tid1 = relbwEqDGFoId factorize5_term1

factorize5_term2 :: SOMetaTermDependant
factorize5_term2 = read "u0 x1"

factorize5_tid2 :: SOMetaUnifRelFoId s
factorize5_tid2 = relbwEqDGFoId factorize5_term2

factorize5_term3 :: SOMetaTermDependant
factorize5_term3 = read "u0 x2"

factorize5_tid3 :: SOMetaUnifRelFoId s
factorize5_tid3 = relbwEqDGFoId factorize5_term3

factorize5_term4 :: SOMetaTermDependant
factorize5_term4 = read "u0 x3"

factorize5_tid4 :: SOMetaUnifRelFoId s
factorize5_tid4 = relbwEqDGFoId factorize5_term4

factorize5_term5 :: SOMetaTermDependant
factorize5_term5 = read "u0 x4"

factorize5_tid5 :: SOMetaUnifRelFoId s
factorize5_tid5 = relbwEqDGFoId factorize5_term5

factorize5_term6 :: SOMetaTermDependant
factorize5_term6 = read "u0 x5"

factorize5_tid6 :: SOMetaUnifRelFoId s
factorize5_tid6 = relbwEqDGFoId factorize5_term6

factorize5_term7 :: SOMetaTermDependant
factorize5_term7 = read "u0 x6"

factorize5_tid7 :: SOMetaUnifRelFoId s
factorize5_tid7 = relbwEqDGFoId factorize5_term7

factorize5_term8 :: SOMetaTermDependant
factorize5_term8 = read "u0 x7"

factorize5_tid8 :: SOMetaUnifRelFoId s
factorize5_tid8 = relbwEqDGFoId factorize5_term8

factorize5_term9 :: SOMetaTermDependant
factorize5_term9 = read "u0 x8"

factorize5_tid9 :: SOMetaUnifRelFoId s
factorize5_tid9 = relbwEqDGFoId factorize5_term9

factorize5_soterm1 :: SOMetatermF
factorize5_soterm1 = read "f1[2]"

factorize5_sotid1 :: SOMetaUnifRelSoId s
factorize5_sotid1 = relbwEqDGSoId factorize5_soterm1

factorize5_soterm2 :: SOMetatermF
factorize5_soterm2 = read "f2[1]"

factorize5_sotid2 :: SOMetaUnifRelSoId s
factorize5_sotid2 = relbwEqDGSoId factorize5_soterm2

factorize5_sig :: SOMetaSignature
factorize5_sig = SOSignature (Signature [] [EnumProc.Empty, read "f1[1]" --> read "f2[1]" --> EnumProc.Empty] (read "x0" --> read "x1" --> read "x2" --> read "x3" --> read "x4" --> read "x5" --> read "x6" --> read "x7" --> read "x8" --> EnumProc.Empty)) EnumProc.Empty

factorize5_mudg1 :: RSOMetaUnifDGraph
factorize5_mudg1 = RESUnifVDGraph (snd <$> runStateT (mzoom lens_esunifdgraph_dgraph (do
	{
		newEqDGFOEdge factorize5_sotid1 [factorize5_tid1,factorize5_tid2] factorize5_tid3;
		newEqDGFOEdge factorize5_sotid1 [factorize5_tid6,factorize5_tid7] factorize5_tid5;
		newEqDGFOEdge factorize5_sotid1 [factorize5_tid8,factorize5_tid9] factorize5_tid5;
		newEqDGFOEdge factorize5_sotid2 [factorize5_tid3] factorize5_tid4;
		newEqDGFOEdge factorize5_sotid2 [factorize5_tid5] factorize5_tid4
	})) (emptyVDGraph factorize5_sig))

factorize5_as1 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize5_as1 = ImplicitAS factorize5_mudg1

factorize5_as2 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize5_as2 = metaunif_prenormalize factorize5_as1

factorize5_as3 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize5_as3 = metaunif_seminormalize factorize5_as1

factorize5_t1 :: AutomatedTest
factorize5_t1 = check_exactly_as "Checking there is exactly one solution" 1 factorize5_as3

factorize5_t2 :: AutomatedTest
factorize5_t2 = check_all_resuvdg factorize_tests_n "Checking that u0 x0 and u0 x1 are not equivalent before" (\title -> \st -> check_not_foequiv factorize5_sig title st factorize5_term1 factorize5_term2) factorize5_as1

factorize5_t3 :: AutomatedTest
factorize5_t3 = check_all_resuvdg factorize_tests_n "Checking that u0 x0 and u0 x5 are not equivalent before" (\title -> \st -> check_not_foequiv factorize5_sig title st factorize5_term1 factorize5_term6) factorize5_as1

factorize5_t4 :: AutomatedTest
factorize5_t4 = check_all_resuvdg factorize_tests_n "Checking that u0 x1 and u0 x8 are not equivalent before" (\title -> \st -> check_not_foequiv factorize5_sig title st factorize5_term2 factorize5_term9) factorize5_as1

factorize5_t5 :: AutomatedTest
factorize5_t5 = check_all_resuvdg factorize_tests_n "Checking that u0 x2 and u0 x4 are not equivalent before" (\title -> \st -> check_not_foequiv factorize5_sig title st factorize5_term3 factorize5_term5) factorize5_as1

factorize5_t6 :: AutomatedTest
factorize5_t6 = check_all_resuvdg factorize_tests_n "Checking that u0 x0 and u0 x2 are not equivalent before" (\title -> \st -> check_not_foequiv factorize5_sig title st factorize5_term1 factorize5_term3) factorize5_as1

factorize5_t7 :: AutomatedTest
factorize5_t7 = check_all_resuvdg factorize_tests_n "Checking that u0 x2 and u0 x3 are not equivalent before" (\title -> \st -> check_not_foequiv factorize5_sig title st factorize5_term3 factorize5_term4) factorize5_as1

factorize5_t8 :: AutomatedTest
factorize5_t8 = check_all_resuvdg factorize_tests_n "Checking that u0 x0 and u0 x1 are not equivalent after prenormalizing" (\title -> \st -> check_not_foequiv factorize5_sig title st factorize5_term1 factorize5_term2) factorize5_as2

factorize5_t9 :: AutomatedTest
factorize5_t9 = check_all_resuvdg factorize_tests_n "Checking that u0 x0 and u0 x5 are not equivalent after prenormalizing" (\title -> \st -> check_not_foequiv factorize5_sig title st factorize5_term1 factorize5_term6) factorize5_as2

factorize5_t10 :: AutomatedTest
factorize5_t10 = check_all_resuvdg factorize_tests_n "Checking that u0 x1 and u0 x8 are not equivalent after prenormalizing" (\title -> \st -> check_not_foequiv factorize5_sig title st factorize5_term2 factorize5_term9) factorize5_as2

factorize5_t11 :: AutomatedTest
factorize5_t11 = check_all_resuvdg factorize_tests_n "Checking that u0 x2 and u0 x4 are not equivalent after prenormalizing" (\title -> \st -> check_not_foequiv factorize5_sig title st factorize5_term3 factorize5_term5) factorize5_as2

factorize5_t12 :: AutomatedTest
factorize5_t12 = check_all_resuvdg factorize_tests_n "Checking that u0 x0 and u0 x2 are not equivalent after prenormalizing" (\title -> \st -> check_not_foequiv factorize5_sig title st factorize5_term1 factorize5_term3) factorize5_as2

factorize5_t13 :: AutomatedTest
factorize5_t13 = check_all_resuvdg factorize_tests_n "Checking that u0 x2 and u0 x3 are not equivalent after prenormalizing" (\title -> \st -> check_not_foequiv factorize5_sig title st factorize5_term3 factorize5_term4) factorize5_as2

factorize5_t14 :: AutomatedTest
factorize5_t14 = check_all_resuvdg factorize_tests_n "Checking that u0 x0 and u0 x1 are not equivalent after seminormalizing" (\title -> \st -> check_not_foequiv factorize5_sig title st factorize5_term1 factorize5_term2) factorize5_as3

factorize5_t15 :: AutomatedTest
factorize5_t15 = check_all_resuvdg factorize_tests_n "Checking that u0 x0 and u0 x5 are equivalent after seminormalizing" (\title -> \st -> check_foequiv factorize5_sig title st factorize5_term1 factorize5_term6) factorize5_as3

factorize5_t16 :: AutomatedTest
factorize5_t16 = check_all_resuvdg factorize_tests_n "Checking that u0 x1 and u0 x8 are equivalent after seminormalizing" (\title -> \st -> check_foequiv factorize5_sig title st factorize5_term2 factorize5_term9) factorize5_as3

factorize5_t17 :: AutomatedTest
factorize5_t17 = check_all_resuvdg factorize_tests_n "Checking that u0 x2 and u0 x4 are equivalent after seminormalizing" (\title -> \st -> check_foequiv factorize5_sig title st factorize5_term3 factorize5_term5) factorize5_as3

factorize5_t18 :: AutomatedTest
factorize5_t18 = check_all_resuvdg factorize_tests_n "Checking that u0 x0 and u0 x2 are not equivalent after seminormalizing" (\title -> \st -> check_not_foequiv factorize5_sig title st factorize5_term1 factorize5_term3) factorize5_as3

factorize5_t19 :: AutomatedTest
factorize5_t19 = check_all_resuvdg factorize_tests_n "Checking that u0 x2 and u0 x3 are not equivalent after seminormalizing" (\title -> \st -> check_not_foequiv factorize5_sig title st factorize5_term3 factorize5_term4) factorize5_as3

factorize5_tests :: String
factorize5_tests = combine_test_results [factorize5_t1,factorize5_t2,factorize5_t3,factorize5_t4,factorize5_t5,factorize5_t6,factorize5_t7,factorize5_t8,factorize5_t9,factorize5_t10,factorize5_t11,factorize5_t12,factorize5_t13,factorize5_t14,factorize5_t15,factorize5_t16,factorize5_t17,factorize5_t18,factorize5_t19]

factorize6_term1 :: SOMetaTermDependant
factorize6_term1 = read "u0 x0"

factorize6_tid1 :: SOMetaUnifRelFoId s
factorize6_tid1 = relbwEqDGFoId factorize6_term1

factorize6_term2 :: SOMetaTermDependant
factorize6_term2 = read "u0 x1"

factorize6_tid2 :: SOMetaUnifRelFoId s
factorize6_tid2 = relbwEqDGFoId factorize6_term2

factorize6_term3 :: SOMetaTermDependant
factorize6_term3 = read "u0 x2"

factorize6_tid3 :: SOMetaUnifRelFoId s
factorize6_tid3 = relbwEqDGFoId factorize6_term3

factorize6_term4 :: SOMetaTermDependant
factorize6_term4 = read "u0 x3"

factorize6_tid4 :: SOMetaUnifRelFoId s
factorize6_tid4 = relbwEqDGFoId factorize6_term4

factorize6_soterm1 :: SOMetatermF
factorize6_soterm1 = read "f1[1]"

factorize6_sotid1 :: SOMetaUnifRelSoId s
factorize6_sotid1 = relbwEqDGSoId factorize6_soterm1

factorize6_soterm2 :: SOMetatermF
factorize6_soterm2 = read "F0[2]"

factorize6_sotid2 :: SOMetaUnifRelSoId s
factorize6_sotid2 = relbwEqDGSoId factorize6_soterm2

factorize6_soterm3 :: SOMetatermF
factorize6_soterm3 = read "f1[1]{pi1}"

factorize6_soterm4 :: SOMetatermF
factorize6_soterm4 = read "F1[2]"

factorize6_exp1 :: SOMetaUnifSOExp
factorize6_exp1 = read "f1[1]{F1[2]}"

factorize6_exp2 :: SOMetaUnifFOExp
factorize6_exp2 = read "F1[2](u0 x1, u0 x2)"

factorize6_sig :: SOMetaSignature
factorize6_sig = SOSignature (Signature [] [EnumProc.Empty, read "f1[1]" --> EnumProc.Empty] (read "x0" --> read "x1" --> read "x2" --> read "x3" --> EnumProc.Empty)) (read "F0[2]" --> EnumProc.Empty)

factorize6_mudg1 :: RSOMetaUnifDGraph
factorize6_mudg1 = RESUnifVDGraph (snd <$> runStateT (mzoom lens_esunifdgraph_dgraph (do
	{
		newEqDGFOEdge factorize6_sotid1 [factorize6_tid1] factorize6_tid4;
		newEqDGFOEdge factorize6_sotid2 [factorize6_tid2,factorize6_tid3] factorize6_tid4
	})) (emptyVDGraph factorize6_sig))

factorize6_as1 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize6_as1 = ImplicitAS factorize6_mudg1

factorize6_as2 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize6_as2 = metaunif_prenormalize factorize6_as1

factorize6_as3 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize6_as3 = metaunif_seminormalize factorize6_as1

factorize6_as4 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize6_as4 = metaunif_quasinormalize factorize6_as1

factorize6_t1 :: AutomatedTest
factorize6_t1 = check_exactly_as "Checking there is exactly one solution before" 1 factorize6_as1

factorize6_t2 :: AutomatedTest
factorize6_t2 = check_exactly_as "Checking there is exactly one solution after prenormalizing" 1 factorize6_as2

factorize6_t3 :: AutomatedTest
factorize6_t3 = check_exactly_as "Checking there is exactly one solution after seminormalizing" 1 factorize6_as3

factorize6_t4 :: AutomatedTest
factorize6_t4 = check_min_as "Checking there is at least two solutions after quasinormalizing" 2 factorize6_as4

factorize6_t5 :: AutomatedTest
factorize6_t5 = check_max_as "Checking there is a finite (no more than 1000) solutions after quasinormalizing" 1000 factorize6_as4

-- Note that on these tests we make assumptions about the newly created second-order variable. This may bite our asses depending on how things evolve.
factorize6_t6 :: AutomatedTest
factorize6_t6 = check_all_resuvdg factorize_tests_n "Checking that F0 is never equivalent to f{F1[2]} after seminormalizing" (\title -> \st -> check_not_soexp factorize6_sig title st factorize6_exp1 factorize6_soterm2) factorize6_as3

--factorize6_t7 :: AutomatedTest
--factorize6_t7 = check_all_resuvdg factorize_tests_n "Checking that F0 is never equivalent to f{pi1} after seminormalizing" (\title -> \st -> check_not_soequiv factorize6_sig title st -factorize6_soterm2 factorize6_soterm3) factorize6_as3

factorize6_t8 :: AutomatedTest
factorize6_t8 = check_all_resuvdg factorize_tests_n "Checking that u0 x0 is never equivalent to F1[2](u0 x1,u0 x2) after seminormalizing" (\title -> \st -> check_not_foexp factorize6_sig title st factorize6_exp2 factorize6_term1) factorize6_as3

--factorize6_t9 :: AutomatedTest
--factorize6_t9 = check_all_resuvdg factorize_tests_n "Checking that u0 x0 is never equivalent to u0 x2 after seminormalizing" (\title -> \st -> check_not_foequiv factorize6_sig title st factorize6_term1 factorize6_term3) factorize6_as3

factorize6_t10 :: AutomatedTest
factorize6_t10 = check_any_resuvdg factorize_tests_n "Checking that F0 is sometimes equivalent to f{F1[2]} after quasinormalizing" (\title -> \st -> check_soexp factorize6_sig title st factorize6_exp1 factorize6_soterm2) factorize6_as4

factorize6_t11 :: AutomatedTest
factorize6_t11 = check_any_resuvdg factorize_tests_n "Checking that F0 is sometimes not equivalent to f{F1[2]} after quasinormalizing" (\title -> \st -> check_not_soexp factorize6_sig title st factorize6_exp1 factorize6_soterm2) factorize6_as4

--factorize6_t12 :: AutomatedTest
--factorize6_t12 = check_any_resuvdg factorize_tests_n "Checking that F0 is sometimes equivalent to f{pi1} after quasinormalizing" (\title -> \st -> check_soequiv factorize6_sig title st factorize6_soterm2 factorize6_soterm3) factorize6_as4

--factorize6_t13 :: AutomatedTest
--factorize6_t13 = check_any_resuvdg factorize_tests_n "Checking that F0 is sometimes not equivalent to f{pi1} after quasinormalizing" (\title -> \st -> check_not_soequiv factorize6_sig title st factorize6_soterm2 factorize6_soterm3) factorize6_as4

factorize6_t14 :: AutomatedTest
factorize6_t14 = check_any_resuvdg factorize_tests_n "Checking that u0 x0 is sometimes equivalent to F1[2](u0 x1,u0 x2) after quasinormalizing" (\title -> \st -> check_foexp factorize6_sig title st factorize6_exp2 factorize6_term1) factorize6_as4

factorize6_t15 :: AutomatedTest
factorize6_t15 = check_any_resuvdg factorize_tests_n "Checking that u0 x0 is sometimes not equivalent to F1[2](u0 x1,u0 x2) after quasinormalizing" (\title -> \st -> check_not_foexp factorize6_sig title st factorize6_exp2 factorize6_term1) factorize6_as4

--factorize6_t16 :: AutomatedTest
--factorize6_t16 = check_any_resuvdg factorize_tests_n "Checking that u0 x0 is sometimes equivalent to u0 x2 after quasinormalizing" (\title -> \st -> check_foequiv factorize6_sig title st factorize6_term1 factorize6_term3) factorize6_as4

--factorize6_t17 :: AutomatedTest
--factorize6_t17 = check_any_resuvdg factorize_tests_n "Checking that u0 x0 is sometimes not equivalent to u0 x2 after quasinormalizing" (\title -> \st -> check_not_foequiv factorize6_sig title st factorize6_term1 factorize6_term3) factorize6_as4

factorize6_tests :: String
factorize6_tests = combine_test_results [factorize6_t1,factorize6_t2,factorize6_t3,factorize6_t4,factorize6_t5,factorize6_t6,factorize6_t8,factorize6_t10,factorize6_t11,factorize6_t14,factorize6_t15]

factorize7_term1 :: SOMetaTermDependant
factorize7_term1 = read "u0 x0"

factorize7_tid1 :: SOMetaUnifRelFoId s
factorize7_tid1 = relbwEqDGFoId factorize7_term1

factorize7_term2 :: SOMetaTermDependant
factorize7_term2 = read "u0 x1"

factorize7_tid2 :: SOMetaUnifRelFoId s
factorize7_tid2 = relbwEqDGFoId factorize7_term2

factorize7_term3 :: SOMetaTermDependant
factorize7_term3 = read "u0 x2"

factorize7_tid3 :: SOMetaUnifRelFoId s
factorize7_tid3 = relbwEqDGFoId factorize7_term3

factorize7_term4 :: SOMetaTermDependant
factorize7_term4 = read "u0 x3"

factorize7_tid4 :: SOMetaUnifRelFoId s
factorize7_tid4 = relbwEqDGFoId factorize7_term4

factorize7_soterm1 :: SOMetatermF
factorize7_soterm1 = read "f1[2]"

factorize7_sotid1 :: SOMetaUnifRelSoId s
factorize7_sotid1 = relbwEqDGSoId factorize7_soterm1

factorize7_soterm2 :: SOMetatermF
factorize7_soterm2 = read "F0[1]"

factorize7_sotid2 :: SOMetaUnifRelSoId s
factorize7_sotid2 = relbwEqDGSoId factorize7_soterm2

factorize7_soterm3 :: SOMetatermF
factorize7_soterm3 = read "F1[1]"

factorize7_soterm4 :: SOMetatermF
factorize7_soterm4 = read "F2[1]"

factorize7_exp1 :: SOMetaUnifSOExp
factorize7_exp1 = read "f1[2]{F1[1],F2[1]}"

factorize7_exp2 :: SOMetaUnifFOExp
factorize7_exp2 = read "F1[1](u0 x2)"

factorize7_exp3 :: SOMetaUnifFOExp
factorize7_exp3 = read "F2[1](u0 x2)"

factorize7_sig :: SOMetaSignature
factorize7_sig = SOSignature (Signature [] [EnumProc.Empty, read "f1[2]" --> EnumProc.Empty] (read "x0" --> read "x1" --> read "x2" --> read "x3" --> EnumProc.Empty)) (read "F0[1]" --> EnumProc.Empty)

factorize7_mudg1 :: RSOMetaUnifDGraph
factorize7_mudg1 = RESUnifVDGraph (snd <$> runStateT (mzoom lens_esunifdgraph_dgraph (do
	{
		newEqDGFOEdge factorize7_sotid1 [factorize7_tid1, factorize7_tid2] factorize7_tid4;
		newEqDGFOEdge factorize7_sotid2 [factorize7_tid3] factorize7_tid4
	})) (emptyVDGraph factorize7_sig))

factorize7_as1 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize7_as1 = ImplicitAS factorize7_mudg1

factorize7_as2 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize7_as2 = metaunif_prenormalize factorize7_as1

factorize7_as3 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize7_as3 = metaunif_seminormalize factorize7_as1

factorize7_as4 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize7_as4 = metaunif_quasinormalize factorize7_as1

factorize7_t1 :: AutomatedTest
factorize7_t1 = check_exactly_as "Checking there is exactly one solution before" 1 factorize7_as1

factorize7_t2 :: AutomatedTest
factorize7_t2 = check_exactly_as "Checking there is exactly one solution after prenormalizing" 1 factorize7_as2

factorize7_t3 :: AutomatedTest
factorize7_t3 = check_exactly_as "Checking there is exactly one solution after seminormalizing" 1 factorize7_as3

factorize7_t4 :: AutomatedTest
factorize7_t4 = check_min_as "Checking there is at least two solutions after quasinormalizing" 2 factorize7_as4

factorize7_t5 :: AutomatedTest
factorize7_t5 = check_max_as "Checking there is a finite (no more than 1000) solutions after quasinormalizing" 1000 factorize7_as4

-- Note that on these tests we make assumptions about the newly created second-order variable. This may bite our asses depending on how things evolve.
factorize7_t6 :: AutomatedTest
factorize7_t6 = check_all_resuvdg factorize_tests_n "Checking that F0 is never equivalent to f{F1[1],F2[1]} after seminormalizing" (\title -> \st -> check_not_soexp factorize7_sig title st factorize7_exp1 factorize7_soterm2) factorize7_as3

factorize7_t7 :: AutomatedTest
factorize7_t7 = check_all_resuvdg factorize_tests_n "Checking that u0 x0 is never equivalent to F1[1](u0 x2) after seminormalizing" (\title -> \st -> check_not_foexp factorize7_sig title st factorize7_exp2 factorize7_term1) factorize7_as3

factorize7_t8 :: AutomatedTest
factorize7_t8 = check_all_resuvdg factorize_tests_n "Checking that u0 x1 is never equivalent to F2[1](u0 x2) after seminormalizing" (\title -> \st -> check_not_foexp factorize7_sig title st factorize7_exp3 factorize7_term2) factorize7_as3

factorize7_t9 :: AutomatedTest
factorize7_t9 = check_all_resuvdg factorize_tests_n "Checking that u0 x3 is never equivalent to u0 x2 after seminormalizing" (\title -> \st -> check_not_foequiv factorize7_sig title st factorize7_term4 factorize7_term3) factorize7_as3

factorize7_t10 :: AutomatedTest
factorize7_t10 = check_any_resuvdg factorize_tests_n "Checking that F0 is sometimes equivalent to f{F1[1],F2[1]} after quasinormalizing" (\title -> \st -> check_soexp factorize7_sig title st factorize7_exp1 factorize7_soterm2) factorize7_as4

factorize7_t11 :: AutomatedTest
factorize7_t11 = check_any_resuvdg factorize_tests_n "Checking that F0 is sometimes not equivalent to f{F1[1],F2[1]} after quasinormalizing" (\title -> \st -> check_not_soexp factorize7_sig title st factorize7_exp1 factorize7_soterm2) factorize7_as4

factorize7_t12 :: AutomatedTest
factorize7_t12 = check_any_resuvdg factorize_tests_n "Checking that u0 x0 is sometimes equivalent to F1[1](u0 x2) after quasinormalizing" (\title -> \st -> check_foexp factorize7_sig title st factorize7_exp2 factorize7_term1) factorize7_as4

factorize7_t13 :: AutomatedTest
factorize7_t13 = check_any_resuvdg factorize_tests_n "Checking that u0 x0 is sometimes not equivalent to F1[1](u0 x2) after quasinormalizing" (\title -> \st -> check_not_foexp factorize7_sig title st factorize7_exp2 factorize7_term1) factorize7_as4

factorize7_t14 :: AutomatedTest
factorize7_t14 = check_any_resuvdg factorize_tests_n "Checking that u0 x1 is sometimes equivalent to F2[1](u0 x2) after quasinormalizing" (\title -> \st -> check_foexp factorize7_sig title st factorize7_exp3 factorize7_term2) factorize7_as4

factorize7_t15 :: AutomatedTest
factorize7_t15 = check_any_resuvdg factorize_tests_n "Checking that u0 x1 is sometimes not equivalent to F2[1](u0 x2) after quasinormalizing" (\title -> \st -> check_not_foexp factorize7_sig title st factorize7_exp3 factorize7_term2) factorize7_as4

factorize7_t16 :: AutomatedTest
factorize7_t16 = check_any_resuvdg factorize_tests_n "Checking that u0 x3 is sometimes equivalent to u0 x2 after quasinormalizing" (\title -> \st -> check_foequiv factorize7_sig title st factorize7_term4 factorize7_term3) factorize7_as4

factorize7_t17 :: AutomatedTest
factorize7_t17 = check_any_resuvdg factorize_tests_n "Checking that u0 x3 is sometimes not equivalent to u0 x2 after quasinormalizing" (\title -> \st -> check_not_foequiv factorize7_sig title st factorize7_term4 factorize7_term3) factorize7_as4

factorize7_tests :: String
factorize7_tests = combine_test_results [factorize7_t1,factorize7_t2,factorize7_t3,factorize7_t4,factorize7_t5,factorize7_t6,factorize7_t7,factorize7_t8,factorize7_t9,factorize7_t10,factorize7_t11,factorize7_t12,factorize7_t13,factorize7_t14,factorize7_t15,factorize7_t16,factorize7_t17]

factorize8_term1 :: SOMetaTermDependant
factorize8_term1 = read "u0 x0"

factorize8_tid1 :: SOMetaUnifRelFoId s
factorize8_tid1 = relbwEqDGFoId factorize8_term1

factorize8_term2 :: SOMetaTermDependant
factorize8_term2 = read "u0 x1"

factorize8_tid2 :: SOMetaUnifRelFoId s
factorize8_tid2 = relbwEqDGFoId factorize8_term2

factorize8_term3 :: SOMetaTermDependant
factorize8_term3 = read "u0 x2"

factorize8_tid3 :: SOMetaUnifRelFoId s
factorize8_tid3 = relbwEqDGFoId factorize8_term3

factorize8_term4 :: SOMetaTermDependant
factorize8_term4 = read "u0 x3"

factorize8_tid4 :: SOMetaUnifRelFoId s
factorize8_tid4 = relbwEqDGFoId factorize8_term4

factorize8_soterm1 :: SOMetatermF
factorize8_soterm1 = read "f1[2]"

factorize8_sotid1 :: SOMetaUnifRelSoId s
factorize8_sotid1 = relbwEqDGSoId factorize8_soterm1

factorize8_soterm2 :: SOMetatermF
factorize8_soterm2 = read "F0[15]"

factorize8_sotid2 :: SOMetaUnifRelSoId s
factorize8_sotid2 = relbwEqDGSoId factorize8_soterm2

factorize8_soterm3 :: SOMetatermF
factorize8_soterm3 = read "F1[15]"

factorize8_soterm4 :: SOMetatermF
factorize8_soterm4 = read "F2[15]"

factorize8_exp1 :: SOMetaUnifSOExp
factorize8_exp1 = read "f1[2]{F1[15],F2[15]}"

factorize8_exp2 :: SOMetaUnifFOExp
factorize8_exp2 = read "F1[15](u0 x2)"

factorize8_exp3 :: SOMetaUnifFOExp
factorize8_exp3 = read "F2[15](u0 x2)"

factorize8_sig :: SOMetaSignature
factorize8_sig = SOSignature (Signature [] [EnumProc.Empty, read "f1[2]" --> EnumProc.Empty] (read "x0" --> read "x1" --> read "x2" --> read "x3" --> EnumProc.Empty)) (read "F0[15]" --> EnumProc.Empty)

factorize8_mudg1 :: RSOMetaUnifDGraph
factorize8_mudg1 = RESUnifVDGraph (snd <$> runStateT (mzoom lens_esunifdgraph_dgraph (do
	{
		newEqDGFOEdge factorize8_sotid1 [factorize8_tid1, factorize8_tid2] factorize8_tid4;
		newEqDGFOEdge factorize8_sotid2 [factorize8_tid3] factorize8_tid4
	})) (emptyVDGraph factorize8_sig))

factorize8_as1 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize8_as1 = ImplicitAS factorize8_mudg1

factorize8_as2 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize8_as2 = metaunif_prenormalize factorize8_as1

factorize8_as3 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize8_as3 = metaunif_seminormalize factorize8_as1

factorize8_as4 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize8_as4 = metaunif_quasinormalize factorize8_as1

factorize8_t1 :: AutomatedTest
factorize8_t1 = check_exactly_as "Checking there is exactly one solution before" 1 factorize8_as1

factorize8_t2 :: AutomatedTest
factorize8_t2 = check_exactly_as "Checking there is exactly one solution after prenormalizing" 1 factorize8_as2

factorize8_t3 :: AutomatedTest
factorize8_t3 = check_exactly_as "Checking there is exactly one solution after seminormalizing" 1 factorize8_as3

factorize8_t4 :: AutomatedTest
factorize8_t4 = check_exactly_as "Checking there is exactly two solutions after quasinormalizing" 2 factorize8_as4

factorize8_t5 :: AutomatedTest
factorize8_t5 = check_max_as "Checking there is a finite (no more than 1000) solutions after quasinormalizing" 1000 factorize8_as4

-- Note that on these tests we make assumptions about the newly created second-order variable. This may bite our asses depending on how things evolve.
factorize8_t6 :: AutomatedTest
factorize8_t6 = check_all_resuvdg factorize_tests_n "Checking that F0 is never equivalent to f{F1[15],F2[15]} after seminormalizing" (\title -> \st -> check_not_soexp factorize8_sig title st factorize8_exp1 factorize8_soterm2) factorize8_as3

factorize8_t7 :: AutomatedTest
factorize8_t7 = check_all_resuvdg factorize_tests_n "Checking that u0 x0 is never equivalent to F1[15](u0 x2) after seminormalizing" (\title -> \st -> check_not_foexp factorize8_sig title st factorize8_exp2 factorize8_term1) factorize8_as3

factorize8_t8 :: AutomatedTest
factorize8_t8 = check_all_resuvdg factorize_tests_n "Checking that u0 x1 is never equivalent to F2[15](u0 x2) after seminormalizing" (\title -> \st -> check_not_foexp factorize8_sig title st factorize8_exp3 factorize8_term2) factorize8_as3

factorize8_t9 :: AutomatedTest
factorize8_t9 = check_all_resuvdg factorize_tests_n "Checking that u0 x3 is never equivalent to u0 x2 after seminormalizing" (\title -> \st -> check_not_foequiv factorize8_sig title st factorize8_term4 factorize8_term3) factorize8_as3

factorize8_t10 :: AutomatedTest
factorize8_t10 = check_any_resuvdg factorize_tests_n "Checking that F0 is sometimes equivalent to f{F1[15],F2[15]} after quasinormalizing" (\title -> \st -> check_soexp factorize8_sig title st factorize8_exp1 factorize8_soterm2) factorize8_as4

factorize8_t11 :: AutomatedTest
factorize8_t11 = check_any_resuvdg factorize_tests_n "Checking that F0 is sometimes not equivalent to f{F1[15],F2[15]} after quasinormalizing" (\title -> \st -> check_not_soexp factorize8_sig title st factorize8_exp1 factorize8_soterm2) factorize8_as4

factorize8_t12 :: AutomatedTest
factorize8_t12 = check_any_resuvdg factorize_tests_n "Checking that u0 x0 is sometimes equivalent to F1[15](u0 x2) after quasinormalizing" (\title -> \st -> check_foexp factorize8_sig title st factorize8_exp2 factorize8_term1) factorize8_as4

factorize8_t13 :: AutomatedTest
factorize8_t13 = check_any_resuvdg factorize_tests_n "Checking that u0 x0 is sometimes not equivalent to F1[15](u0 x2) after quasinormalizing" (\title -> \st -> check_not_foexp factorize8_sig title st factorize8_exp2 factorize8_term1) factorize8_as4

factorize8_t14 :: AutomatedTest
factorize8_t14 = check_any_resuvdg factorize_tests_n "Checking that u0 x1 is sometimes equivalent to F2[15](u0 x2) after quasinormalizing" (\title -> \st -> check_foexp factorize8_sig title st factorize8_exp3 factorize8_term2) factorize8_as4

factorize8_t15 :: AutomatedTest
factorize8_t15 = check_any_resuvdg factorize_tests_n "Checking that u0 x1 is sometimes not equivalent to F2[15](u0 x2) after quasinormalizing" (\title -> \st -> check_not_foexp factorize8_sig title st factorize8_exp3 factorize8_term2) factorize8_as4

factorize8_t16 :: AutomatedTest
factorize8_t16 = check_any_resuvdg factorize_tests_n "Checking that u0 x3 is sometimes equivalent to u0 x2 after quasinormalizing" (\title -> \st -> check_foequiv factorize8_sig title st factorize8_term4 factorize8_term3) factorize8_as4

factorize8_t17 :: AutomatedTest
factorize8_t17 = check_any_resuvdg factorize_tests_n "Checking that u0 x3 is sometimes not equivalent to u0 x2 after quasinormalizing" (\title -> \st -> check_not_foequiv factorize8_sig title st factorize8_term4 factorize8_term3) factorize8_as4

factorize8_tests :: String
factorize8_tests = combine_test_results [factorize8_t1,factorize8_t2,factorize8_t3,factorize8_t4,factorize8_t5,factorize8_t6,factorize8_t7,factorize8_t8,factorize8_t9,factorize8_t10,factorize8_t11,factorize8_t12,factorize8_t13,factorize8_t14,factorize8_t15,factorize8_t16,factorize8_t17]

factorize9_term1 :: SOMetaTermDependant
factorize9_term1 = read "u0 x0"

factorize9_tid1 :: SOMetaUnifRelFoId s
factorize9_tid1 = relbwEqDGFoId factorize9_term1

factorize9_term2 :: SOMetaTermDependant
factorize9_term2 = read "u0 x1"

factorize9_tid2 :: SOMetaUnifRelFoId s
factorize9_tid2 = relbwEqDGFoId factorize9_term2

factorize9_term3 :: SOMetaTermDependant
factorize9_term3 = read "u0 x2"

factorize9_tid3 :: SOMetaUnifRelFoId s
factorize9_tid3 = relbwEqDGFoId factorize9_term3

factorize9_soterm1 :: SOMetatermF
factorize9_soterm1 = read "f1[1]"

factorize9_sotid1 :: SOMetaUnifRelSoId s
factorize9_sotid1 = relbwEqDGSoId factorize9_soterm1

factorize9_soterm2 :: SOMetatermF
factorize9_soterm2 = read "f2[2]"

factorize9_sotid2 :: SOMetaUnifRelSoId s
factorize9_sotid2 = relbwEqDGSoId factorize9_soterm2

factorize9_soterm3 :: SOMetatermF
factorize9_soterm3 = read "F0[2]"

factorize9_sotid3 :: SOMetaUnifRelSoId s
factorize9_sotid3 = relbwEqDGSoId factorize9_soterm3

factorize9_soterm4 :: SOMetatermF
factorize9_soterm4 = read "F1[1]"

factorize9_sotid4 :: SOMetaUnifRelSoId s
factorize9_sotid4 = relbwEqDGSoId factorize9_soterm4

factorize9_sig :: SOMetaSignature
factorize9_sig = SOSignature (Signature [] [EnumProc.Empty, read "f1[1]" --> EnumProc.Empty, read "f2[2]" --> EnumProc.Empty] (read "x0" --> read "x1" --> read "x2" --> EnumProc.Empty)) (read "F0[2]" --> read "F1[1]" --> EnumProc.Empty)

factorize9_mudg1 :: RSOMetaUnifDGraph
factorize9_mudg1 = RESUnifVDGraph (snd <$> runStateT (mzoom lens_esunifdgraph_dgraph (do
	{
		newEqDGFOEdge factorize9_sotid3 [factorize9_tid1] factorize9_tid3;
		newEqDGFOEdge factorize9_sotid4 [factorize9_tid2] factorize8_tid3
	})) (emptyVDGraph factorize9_sig))

factorize9_as1 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize9_as1 = ImplicitAS factorize9_mudg1

factorize9_as2 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize9_as2 = metaunif_prenormalize factorize9_as1

factorize9_as3 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize9_as3 = metaunif_seminormalize factorize9_as1

factorize9_as4 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize9_as4 = metaunif_quasinormalize factorize9_as1

factorize9_as5 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize9_as5 = metaunif_normalize factorize9_as1

factorize9_t1 :: AutomatedTest
factorize9_t1 = check_exactly_as "Checking there is exactly one solution before" 1 factorize9_as1

factorize9_t2 :: AutomatedTest
factorize9_t2 = check_exactly_as "Checking there is exactly one solution after prenormalizing" 1 factorize9_as2

factorize9_t3 :: AutomatedTest
factorize9_t3 = check_exactly_as "Checking there is exactly one solution after seminormalizing" 1 factorize9_as3

factorize9_t4 :: AutomatedTest
factorize9_t4 = check_exactly_as "Checking there is exactly one solution after quasinormalizing" 1 factorize9_as4

factorize9_t5 :: AutomatedTest
factorize9_t5 = check_min_as "Checking there are more than 100 solutions after normalizing" 100 factorize9_as5

factorize9_tests :: String
factorize9_tests = combine_test_results [factorize9_t1,factorize9_t2,factorize9_t3,factorize9_t4,factorize9_t5]


factorize_test :: IO ()
factorize_test = putStr "EXAMPLE 1\n\n" >> putStr factorize1_tests >>
		putStr "EXAMPLE 2\n\n" >> putStr factorize2_tests >>
		putStr "EXAMPLE 3\n\n" >> putStr factorize3_tests >>
		putStr "EXAMPLE 4\n\n" >> putStr factorize4_tests >>
		putStr "EXAMPLE 5\n\n" >> putStr factorize5_tests >>
		putStr "EXAMPLE 6\n\n" >> putStr factorize6_tests >>
		putStr "EXAMPLE 7\n\n" >> putStr factorize7_tests >>
		putStr "EXAMPLE 8\n\n" >> putStr factorize8_tests -- >>
--		putStr "EXAMPLE 9\n\n" >> putStr factorize9_tests



dgraphop_test :: IO ()
dgraphop_test = putStr "VERTICAL COMMUTE TESTS\n\n" >> vcommute_test >>
		putStr "VERTICAL ALIGN TESTS\n\n" >> valign_test >>
		putStr "ZIP TESTS\n\n" >> zip_test >>
		putStr "SIMPLIFY PROJECTION TESTS\n\n" >> simpproj_test >>
		putStr "DUMP TESTS\n\n" >> dump_test >>
		putStr "SOT CONSISTENCY TESTS\n\n" >> sotconsistency_test >>
		putStr "HEAD ARITY TESTS\n\n" >> head_arity_test >>
		putStr "TARGET ARITY TESTS\n\n" >> target_arity_test >>
		putStr "OCCURS CHECK TESTS\n\n" >> occurs_check_test >>
		putStr "FACTORIZATION TESTS\n\n" >> factorize_test
