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
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
module SOResolutionTests where

import Control.Exception
import Data.Functor.Compose
import Data.Functor.Identity
import Control.Unification
import Control.Unification.IntVar
import Control.Unification.Types
import Control.Monad.Trans
import Control.Monad.Trans.Class
import Control.Monad.Trans.Identity
import Control.Monad.Error.Class
import HaskellPlus
import Syntax
import Data.Functor.Fixedpoint
import Data.List
import Data.HashMap
import AnswerSet
import EnumProc
import Data.Maybe
import Data.Graph
import Data.Bifunctor
import Control.Lens
import Control.Monad.State
import Control.Monad.Morph
import Algorithm
import Provenance
import CESQResolutionProvenance
import DependencyGraph
import Identifier
import Control.Monad.ST
import Operable
import Data.Tuple
import Debug.Trace
import Safe (maximumMay, minimumMay)
import GlobalTrace
import ESUnification
import Heuristics
import Resolution
import SOResolution
import MetaLogic
import MetaLogicAlpha
import AutoTests
import Similarity

check_eqs_alpha_eq :: [SOMetaUnifEquation] -> String -> [SOMetaUnifEquation] -> AutomatedTest
check_eqs_alpha_eq reqs str eqs = AT str (if (sometaunifsystem_alpha_eq reqs eqs) then (ATR True "The system matches (through alpha-equivalence) with the expected one.") else (ATR False ("The system does not match (including alpha-equivalence) with the expected one.\n   Expected: " ++ (show reqs) ++ "\n   Result: " ++ (show eqs))))

check_proof_length_min :: Int -> String -> ([SOMetaUnifEquation],[SOMetaResProofStep]) -> AutomatedTest
check_proof_length_min l str (_,proof) = AT str (if ((length proof) >= l) then (ATR True ("The proof is correctly less than " ++ (show l) ++ " steps long.")) else (ATR False ("The proof was meant to be at most " ++ (show l) ++ " steps long, but it actually is " ++ (show (length proof)) ++ " steps long.")))

check_proof_length_max :: Int -> String -> ([SOMetaUnifEquation],[SOMetaResProofStep]) -> AutomatedTest
check_proof_length_max l str (_,proof) = AT str (if ((length proof) <= l) then (ATR True ("The proof is correctly more than " ++ (show l) ++ " steps long.")) else (ATR False ("The proof was meant to be at least " ++ (show l) ++ " steps long, but it actually is only " ++ (show (length proof)) ++ " steps long.")))

check_proof_length_exact :: Int -> String -> ([SOMetaUnifEquation],[SOMetaResProofStep]) -> AutomatedTest
check_proof_length_exact l str (_,proof) = AT str (if ((length proof) == l) then (ATR True ("The proof is correctly exactly " ++ (show l) ++ " steps long.")) else (ATR False ("The proof was meant to be exactly " ++ (show l) ++ " steps long, but it is " ++ (show (length proof)) ++ " steps long instead.")))



show_wproof :: ([SOMetaUnifEquation],[SOMetaResProofStep]) -> String
show_wproof (eqs,proof) = (show_resproof proof) ++ "\n\nResulting constraints: " ++ (show eqs) ++ "\n\n\n"

show_enum_wproof :: EnumProc ([SOMetaUnifEquation],[SOMetaResProofStep]) -> String
show_enum_wproof EnumProc.Empty = ""
show_enum_wproof Halt = ""
show_enum_wproof (Error str) = error str
show_enum_wproof (Continue x) = "...\n" ++ (show_enum_wproof x)
show_enum_wproof (Produce v x) = (show_wproof v) ++ (show_enum_wproof x)

rslv_to_eqs_n_1 :: Int
rslv_to_eqs_n_1 = 1000

rslv_to_eqs_sig_1 :: SOMetaSignature
rslv_to_eqs_sig_1 = SOSignature (Signature [read "p1[0]" --> EnumProc.Empty] [] (EnumProc.Empty)) (EnumProc.Empty) EnumProc.Empty EnumProc.Empty

rslv_to_eqs_cnf_1 :: SOMetaCNF
rslv_to_eqs_cnf_1 = read "[[+p1[0]()],[-p1[0]()]]"

rslv_to_eqs_wproof_1 :: EnumProc ([SOMetaUnifEquation],[SOMetaResProofStep])
rslv_to_eqs_wproof_1 = resolve_to_constraints_metacnf_enum rslv_to_eqs_sig_1 rslv_to_eqs_cnf_1

rslv_to_eqs_eqs_1 :: EnumProc [SOMetaUnifEquation]
rslv_to_eqs_eqs_1 = fst <$> rslv_to_eqs_wproof_1

rslv_to_eqs_d_eqs_1 :: [SOMetaUnifEquation]
rslv_to_eqs_d_eqs_1 = [read "u0 p1[0]() ~ u0 p1[0]()"]

rslv_to_eqs_1_t1 :: AutomatedTest
rslv_to_eqs_1_t1 = check_exactly_enum "Checking there is exactly one proof for [[+p1[0]()],[-p1[0]()]]" 1 rslv_to_eqs_eqs_1

rslv_to_eqs_1_t2 :: AutomatedTest
rslv_to_eqs_1_t2 = check_all_enum rslv_to_eqs_n_1 "Checking that every proof results in u0 p1[0]() ~ u0 p1[0]()" (check_eqs_alpha_eq rslv_to_eqs_d_eqs_1) rslv_to_eqs_eqs_1

rslv_to_eqs_1_ts :: String
rslv_to_eqs_1_ts = combine_test_results [rslv_to_eqs_1_t1, rslv_to_eqs_1_t2]

rslv_to_eqs_sig_2 :: SOMetaSignature
rslv_to_eqs_sig_2 = SOSignature (Signature [read "p1[0]" --> EnumProc.Empty] [] (EnumProc.Empty)) (EnumProc.Empty) EnumProc.Empty EnumProc.Empty

rslv_to_eqs_cnf_2 :: SOMetaCNF
rslv_to_eqs_cnf_2 = read "[[+p1[0]()],[+p1[0]()]]"

rslv_to_eqs_wproof_2 :: EnumProc ([SOMetaUnifEquation],[SOMetaResProofStep])
rslv_to_eqs_wproof_2 = resolve_to_constraints_metacnf_enum rslv_to_eqs_sig_2 rslv_to_eqs_cnf_2

rslv_to_eqs_eqs_2 :: EnumProc [SOMetaUnifEquation]
rslv_to_eqs_eqs_2 = fst <$> rslv_to_eqs_wproof_2

rslv_to_eqs_2_t1 :: AutomatedTest
rslv_to_eqs_2_t1 = check_exactly_enum "Checking there are no proofs for [[+p1[0]()],[+p1[0]()]]" 0 rslv_to_eqs_eqs_2

rslv_to_eqs_2_ts :: String
rslv_to_eqs_2_ts = combine_test_results [rslv_to_eqs_2_t1]

rslv_to_eqs_sig_3 :: SOMetaSignature
rslv_to_eqs_sig_3 = SOSignature (Signature [read "p1[0]" --> read "p2[0]" --> EnumProc.Empty] [] (EnumProc.Empty)) (EnumProc.Empty) EnumProc.Empty EnumProc.Empty

rslv_to_eqs_cnf_3 :: SOMetaCNF
rslv_to_eqs_cnf_3 = read "[[+p1[0]()],[-p2[0]()]]"

rslv_to_eqs_wproof_3 :: EnumProc ([SOMetaUnifEquation],[SOMetaResProofStep])
rslv_to_eqs_wproof_3 = resolve_to_constraints_metacnf_enum rslv_to_eqs_sig_3 rslv_to_eqs_cnf_3

rslv_to_eqs_eqs_3 :: EnumProc [SOMetaUnifEquation]
rslv_to_eqs_eqs_3 = fst <$> rslv_to_eqs_wproof_3

rslv_to_eqs_3_t1 :: AutomatedTest
rslv_to_eqs_3_t1 = check_exactly_enum "Checking there are no proofs for [[+p1[0]()],[-p2[0]()]]" 0 rslv_to_eqs_eqs_3

rslv_to_eqs_3_ts :: String
rslv_to_eqs_3_ts = combine_test_results [rslv_to_eqs_3_t1]

rslv_to_eqs_n_4 :: Int
rslv_to_eqs_n_4 = 1000

rslv_to_eqs_sig_4 :: SOMetaSignature
rslv_to_eqs_sig_4 = SOSignature (Signature [read "p1[0]" --> read "p2[0]" --> EnumProc.Empty] [] (EnumProc.Empty)) (EnumProc.Empty) EnumProc.Empty EnumProc.Empty

rslv_to_eqs_cnf_4 :: SOMetaCNF
rslv_to_eqs_cnf_4 = read "[[+p1[0](),+p2[0]()],[-p1[0]()],[-p2[0]()]]"

rslv_to_eqs_wproof_4 :: EnumProc ([SOMetaUnifEquation],[SOMetaResProofStep])
rslv_to_eqs_wproof_4 = resolve_to_constraints_metacnf_enum rslv_to_eqs_sig_4 rslv_to_eqs_cnf_4

rslv_to_eqs_eqs_4 :: EnumProc [SOMetaUnifEquation]
rslv_to_eqs_eqs_4 = fst <$> rslv_to_eqs_wproof_4

rslv_to_eqs_d_eqs_4_1 :: [SOMetaUnifEquation]
rslv_to_eqs_d_eqs_4_1 = [read "u0 p1[0]() ~ u0 p1[0]()", read "u1 u0 p2[0]() ~ u1 p2[0]()"]

rslv_to_eqs_d_eqs_4_2 :: [SOMetaUnifEquation]
rslv_to_eqs_d_eqs_4_2 = [read "u0 p2[0]() ~ u0 p2[0]()", read "u1 u0 p1[0]() ~ u1 p1[0]()"]

rslv_to_eqs_4_t1 :: AutomatedTest
rslv_to_eqs_4_t1 = check_min_enum "Checking there are at least two proofs for [[+p1[0](),+p2[0]()],[-p1[0]()],[-p2[0]()]]" 2 rslv_to_eqs_eqs_4

rslv_to_eqs_4_t2 :: AutomatedTest
rslv_to_eqs_4_t2 = check_max_enum "Checking there is a limited number of proofs for [[+p1[0](),+p2[0]()],[-p1[0]()],[-p2[0]()]]" rslv_to_eqs_n_4 rslv_to_eqs_eqs_4

rslv_to_eqs_4_t3 :: AutomatedTest
rslv_to_eqs_4_t3 = check_any_enum rslv_to_eqs_n_4 "Checking that there is a proof with u0 p1[0]() ~ u0 p1[0]() and u1 p2[0] ~ u1 u0 p2[0]()" (check_eqs_alpha_eq rslv_to_eqs_d_eqs_4_1) rslv_to_eqs_eqs_4

rslv_to_eqs_4_t4 :: AutomatedTest
rslv_to_eqs_4_t4 = check_any_enum rslv_to_eqs_n_4 "Checking that there is a proof with u0 p2[0]() ~ u0 p2[0]() and u1 p1[0] ~ u1 u0 p1[0]()" (check_eqs_alpha_eq rslv_to_eqs_d_eqs_4_2) rslv_to_eqs_eqs_4

rslv_to_eqs_4_t5 :: AutomatedTest
rslv_to_eqs_4_t5 = check_all_enum rslv_to_eqs_n_4 "Checking that all proofs have 2 steps" (check_proof_length_exact 2) rslv_to_eqs_wproof_4

rslv_to_eqs_4_ts :: String
rslv_to_eqs_4_ts = combine_test_results [rslv_to_eqs_4_t1, rslv_to_eqs_4_t2, rslv_to_eqs_4_t3, rslv_to_eqs_4_t4, rslv_to_eqs_4_t5]

rslv_to_eqs_atests_4 :: String
rslv_to_eqs_atests_4 = "Additional tests to consider for EXAMPLE 4 (use rslv_to_eqs_wproof_4):\n\n  - Take a look at the results and see that they still make sense.\n\n"

rslv_to_eqs_n_5 :: Int
rslv_to_eqs_n_5 = 1000

rslv_to_eqs_sig_5 :: SOMetaSignature
rslv_to_eqs_sig_5 = SOSignature (Signature [read "p1[0]" --> read "p2[0]" --> EnumProc.Empty] [] (EnumProc.Empty)) (EnumProc.Empty) EnumProc.Empty EnumProc.Empty

rslv_to_eqs_cnf_5 :: SOMetaCNF
rslv_to_eqs_cnf_5 = read "[[+p1[0](),+p2[0]()],[+p1[0]()],[-p2[0]()]]"

rslv_to_eqs_wproof_5 :: EnumProc ([SOMetaUnifEquation],[SOMetaResProofStep])
rslv_to_eqs_wproof_5 = resolve_to_constraints_metacnf_enum rslv_to_eqs_sig_5 rslv_to_eqs_cnf_5

rslv_to_eqs_eqs_5 :: EnumProc [SOMetaUnifEquation]
rslv_to_eqs_eqs_5 = fst <$> rslv_to_eqs_wproof_5

rslv_to_eqs_5_t1 :: AutomatedTest
rslv_to_eqs_5_t1 = check_exactly_enum "Checking there are no proofs for [[+p1[0](),+p2[0]()],[+p1[0]()],[-p2[0]()]]" 0 rslv_to_eqs_eqs_5

rslv_to_eqs_5_ts :: String
rslv_to_eqs_5_ts = combine_test_results [rslv_to_eqs_5_t1]

rslv_to_eqs_n_6 :: Int
rslv_to_eqs_n_6 = 1000

rslv_to_eqs_sig_6 :: SOMetaSignature
rslv_to_eqs_sig_6 = SOSignature (Signature [read "p1[0]" --> read "p2[0]" --> EnumProc.Empty] [] (EnumProc.Empty)) (EnumProc.Empty) EnumProc.Empty EnumProc.Empty

rslv_to_eqs_cnf_6 :: SOMetaCNF
rslv_to_eqs_cnf_6 = read "[[-p1[0](),-p2[0]()],[+p1[0]()],[-p2[0]()]]"

rslv_to_eqs_wproof_6 :: EnumProc ([SOMetaUnifEquation],[SOMetaResProofStep])
rslv_to_eqs_wproof_6 = resolve_to_constraints_metacnf_enum rslv_to_eqs_sig_6 rslv_to_eqs_cnf_6

rslv_to_eqs_eqs_6 :: EnumProc [SOMetaUnifEquation]
rslv_to_eqs_eqs_6 = fst <$> rslv_to_eqs_wproof_6

rslv_to_eqs_6_t1 :: AutomatedTest
rslv_to_eqs_6_t1 = check_exactly_enum "Checking there are no proofs for [[-p1[0](),-p2[0]()],[+p1[0]()],[-p2[0]()]]" 0 rslv_to_eqs_eqs_6

rslv_to_eqs_6_ts :: String
rslv_to_eqs_6_ts = combine_test_results [rslv_to_eqs_6_t1]

rslv_to_eqs_n_7 :: Int
rslv_to_eqs_n_7 = 2000

rslv_to_eqs_sig_7 :: SOMetaSignature
rslv_to_eqs_sig_7 = SOSignature (Signature [read "p1[0]" --> read "p2[0]" --> read "p3[0]" --> read "p4[0]" --> read "p5[0]" --> read "p6[0]" --> EnumProc.Empty] [] (EnumProc.Empty)) (EnumProc.Empty) EnumProc.Empty EnumProc.Empty

rslv_to_eqs_cnf_7 :: SOMetaCNF
rslv_to_eqs_cnf_7 = read "[[+p1[0](),-p2[0](),+p3[0]()],[-p3[0](),+p4[0](),-p5[0]()],[-p5[0](),-p1[0]()],[+p3[0](),+p6[0]()],[+p2[0](),+p4[0]()],[+p5[0]()],[-p4[0](),-p4[0]()]]"

rslv_to_eqs_wproof_7 :: EnumProc ([SOMetaUnifEquation],[SOMetaResProofStep])
rslv_to_eqs_wproof_7 = resolve_to_constraints_metacnf_enum rslv_to_eqs_sig_7 rslv_to_eqs_cnf_7

rslv_to_eqs_eqs_7 :: EnumProc [SOMetaUnifEquation]
rslv_to_eqs_eqs_7 = fst <$> rslv_to_eqs_wproof_7

rslv_to_eqs_d_eqs_7 :: [SOMetaUnifEquation]
rslv_to_eqs_d_eqs_7 = [read "u0 p5[0]() ~ u0 p5[0]()", read "u1 u0 p1[0]() ~ u1 p1[0]()", read "u2 p5[0]() ~ u2 p5[0]()", read "u3 p4[0]() ~ u3 u2 p4[0]()", read "u3 p4[0]() ~ u3 u2 p4[0]()", read "u4 u3 u2 p3[0]() ~ u4 u1 p3[0]()", read "u5 u4 u1 p2[0]() ~ u5 p2[0]()", read "u6 p4[0]() ~ u6 p4[0]()", read "u0 p5[0]() ~ u0 p5[0]()", read "u1 u0 p1[0]() ~ u1 p1[0]()", read "u5 p4[0]() ~ u5 p4[0]()", read "u7 u8 p5[0]() ~ u7 p5[0]()", read "u9 u7 u8 p3[0]() ~ u9 u1 p3[0]()", read "u10 u9 u1 p2[0]() ~ u10 u6 p2[0]()", read "u11 u10 u6 p4[0]() ~ u11 u5 p4[0]()"]

-- [u0 p5[0]() = u0 p5[0](),u10 u0 p1[0]() = u10 p1[0](),u2 p5[0]() = u2 p5[0](),u3 p4[0]() = u3 u2 p4[0](),u3 p4[0]() = u3 u2 p4[0](),u12 u3 u2 p3[0]() = u12 u10 p3[0](),u16 u12 u10 p2[0]() = u16 p2[0](),u9 p4[0]() = u9 p4[0](),u0 p5[0]() = u0 p5[0](),u10 u0 p1[0]() = u10 p1[0](),u5 p4[0]() = u5 p4[0](),u5 p4[0]() = u5 p4[0](),u6 u5 p5[0]() = u6 p5[0](),u13 u6 u5 p3[0]() = u13 u10 p3[0](),u21 u13 u10 p2[0]() = u21 u9 p2[0](),u34 u21 u9 p4[0]() = u34 u16 p4[0]()]

rslv_to_eqs_7_t1 :: AutomatedTest
rslv_to_eqs_7_t1 = check_min_enum "Checking there are at least 10 proofs for [[+p1[0](),-p2[0](),+p3[0]()],[-p3[0](),+p4[0](),-p5[0]()],[-p5[0](),-p1[0]()],[+p3[0](),+p6[0]()],[+p2[0](),+p4[0]()],[+p5[0]()],[-p4[0](),-p4[0]()]]" 10 rslv_to_eqs_eqs_7

rslv_to_eqs_7_t2 :: AutomatedTest
rslv_to_eqs_7_t2 = check_any_enum rslv_to_eqs_n_7 "Checking there is a proof with u0 p3[0]() ~ u0 p3[0](), u1 u0 p1[0]() ~ u1 p1[0](), u2 u1 u0 p2[0]() ~ u2 p2[0](), u3 u2 u1 u0 p5[0]() ~ u3 p5[0](), u4 u3 u2 u1 u0 p4[0]() ~ u4 p4[0]()" (check_eqs_alpha_eq rslv_to_eqs_d_eqs_7) rslv_to_eqs_eqs_7

rslv_to_eqs_7_t3 :: AutomatedTest
rslv_to_eqs_7_t3 = check_all_enum rslv_to_eqs_n_7 "Checking that all proofs have at least 5 steps." (check_proof_length_min 5) rslv_to_eqs_wproof_7

-- HERE is where I said: To hell with this, I'm checking it manually! I keep everything in case I want to go back. But there's too many problems to spend any more time trying to do it properly.

rslv_to_eqs_sig_8 :: SOMetaSignature
rslv_to_eqs_sig_8 = SOSignature (Signature [read "p1[0]" --> EnumProc.Empty] [] (EnumProc.Empty)) (EnumProc.Empty) (read "P1[0]" --> EnumProc.Empty) EnumProc.Empty

rslv_to_eqs_cnf_8 :: SOMetaCNF
rslv_to_eqs_cnf_8 = read "[[+p1[0]()],[-P1[0]()]]"

rslv_to_eqs_wproof_8 :: EnumProc ([SOMetaUnifEquation],[SOMetaResProofStep])
rslv_to_eqs_wproof_8 = resolve_to_constraints_metacnf_enum rslv_to_eqs_sig_8 rslv_to_eqs_cnf_8

rslv_to_eqs_eqs_8 :: EnumProc [SOMetaUnifEquation]
rslv_to_eqs_eqs_8 = fst <$> rslv_to_eqs_wproof_8

rslv_to_eqs_sig_9 :: SOMetaSignature
rslv_to_eqs_sig_9 = SOSignature (Signature [read "p2[0]" --> EnumProc.Empty] [] (EnumProc.Empty)) (EnumProc.Empty) (read "P1[0]" --> EnumProc.Empty) EnumProc.Empty

rslv_to_eqs_cnf_9 :: SOMetaCNF
rslv_to_eqs_cnf_9 = read "[[+p2[0]()],[-P1[0]()]]"

rslv_to_eqs_wproof_9 :: EnumProc ([SOMetaUnifEquation],[SOMetaResProofStep])
rslv_to_eqs_wproof_9 = resolve_to_constraints_metacnf_enum rslv_to_eqs_sig_9 rslv_to_eqs_cnf_9

rslv_to_eqs_eqs_9 :: EnumProc [SOMetaUnifEquation]
rslv_to_eqs_eqs_9 = fst <$> rslv_to_eqs_wproof_9

rslv_to_eqs_sig_10 :: SOMetaSignature
rslv_to_eqs_sig_10 = SOSignature (Signature [read "p1[0]" --> read "p2[0]" --> EnumProc.Empty] [] (EnumProc.Empty)) (EnumProc.Empty) (read "P1[0]" --> read "P2[0]" --> EnumProc.Empty) EnumProc.Empty

rslv_to_eqs_cnf_10 :: SOMetaCNF
rslv_to_eqs_cnf_10 = read "[[+p1[0]()],[-P1[0]()],[-P2[0]()],[+p2[0]()]]"

rslv_to_eqs_wproof_10 :: EnumProc ([SOMetaUnifEquation],[SOMetaResProofStep])
rslv_to_eqs_wproof_10 = resolve_to_constraints_metacnf_enum rslv_to_eqs_sig_10 rslv_to_eqs_cnf_10

rslv_to_eqs_eqs_10 :: EnumProc [SOMetaUnifEquation]
rslv_to_eqs_eqs_10 = fst <$> rslv_to_eqs_wproof_10

rslv_to_eqs_sig_11 :: SOMetaSignature
rslv_to_eqs_sig_11 = SOSignature (Signature [read "p1[0]" --> read "p2[0]" --> EnumProc.Empty] [] (EnumProc.Empty)) (EnumProc.Empty) (read "P1[0]" --> read "P2[0]" --> EnumProc.Empty) EnumProc.Empty

rslv_to_eqs_cnf_11 :: SOMetaCNF
rslv_to_eqs_cnf_11 = read "[[+p1[0](),+P2[0]()],[-p1[0]()],[-p2[0]()]]"

rslv_to_eqs_wproof_11 :: EnumProc ([SOMetaUnifEquation],[SOMetaResProofStep])
rslv_to_eqs_wproof_11 = resolve_to_constraints_metacnf_enum rslv_to_eqs_sig_11 rslv_to_eqs_cnf_11

rslv_to_eqs_eqs_11 :: EnumProc [SOMetaUnifEquation]
rslv_to_eqs_eqs_11 = fst <$> rslv_to_eqs_wproof_11


rslv_to_eqs_test :: IO ()
rslv_to_eqs_test = putStr "EXAMPLE 1\n\n" >> putStr rslv_to_eqs_1_ts >>
			putStr "EXAMPLE 2\n\n" >> putStr rslv_to_eqs_2_ts >>
			putStr "EXAMPLE 3\n\n" >> putStr rslv_to_eqs_3_ts >>
			putStr "EXAMPLE 4\n\n" >> putStr rslv_to_eqs_4_ts >> putStr rslv_to_eqs_atests_4 >>
			putStr "EXAMPLE 5\n\n" >> putStr rslv_to_eqs_5_ts >>
			putStr "EXAMPLE 6\n\n" >> putStr rslv_to_eqs_6_ts












rslv_to_inst_sig_1 :: SOMetaSignature
rslv_to_inst_sig_1 = SOSignature (Signature [read "p1[0]" --> EnumProc.Empty] [] (EnumProc.Empty)) (EnumProc.Empty) (read "P1[0]" --> EnumProc.Empty) EnumProc.Empty

rslv_to_inst_cnf_1 :: SOMetaCNF
rslv_to_inst_cnf_1 = read "[[+p1[0]()],[-P1[0]()]]"

rslv_to_inst_wproof_1 :: EnumProc (SOMetaUnifSysSolution,[SOMetaResProofStep])
rslv_to_inst_wproof_1 = resolve_and_unify_metacnf rslv_to_inst_sig_1 rslv_to_inst_cnf_1

rslv_to_inst_inst_1 :: EnumProc SOMetaUnifSysSolution
rslv_to_inst_inst_1 = fst <$> rslv_to_inst_wproof_1

rslv_to_inst_sig_2 :: SOMetaSignature
rslv_to_inst_sig_2 = SOSignature (Signature [read "p2[0]" --> EnumProc.Empty] [] (EnumProc.Empty)) (EnumProc.Empty) (read "P1[0]" --> EnumProc.Empty) EnumProc.Empty

rslv_to_inst_cnf_2 :: SOMetaCNF
rslv_to_inst_cnf_2 = read "[[+p2[0]()],[-P1[0]()]]"

rslv_to_inst_wproof_2 :: EnumProc (SOMetaUnifSysSolution,[SOMetaResProofStep])
rslv_to_inst_wproof_2 = resolve_and_unify_metacnf rslv_to_inst_sig_2 rslv_to_inst_cnf_2

rslv_to_inst_inst_2 :: EnumProc SOMetaUnifSysSolution
rslv_to_inst_inst_2 = fst <$> rslv_to_inst_wproof_2

rslv_to_inst_sig_3 :: SOMetaSignature
rslv_to_inst_sig_3 = SOSignature (Signature [read "p1[0]" --> read "p2[0]" --> EnumProc.Empty] [] (EnumProc.Empty)) (EnumProc.Empty) (read "P1[0]" --> read "P2[0]" --> EnumProc.Empty) EnumProc.Empty

rslv_to_inst_cnf_3 :: SOMetaCNF
rslv_to_inst_cnf_3 = read "[[+p1[0]()],[-P1[0]()],[-P2[0]()],[+p2[0]()]]"

rslv_to_inst_wproof_3 :: EnumProc (SOMetaUnifSysSolution,[SOMetaResProofStep])
rslv_to_inst_wproof_3 = resolve_and_unify_metacnf rslv_to_inst_sig_3 rslv_to_inst_cnf_3

rslv_to_inst_inst_3 :: EnumProc SOMetaUnifSysSolution
rslv_to_inst_inst_3 = fst <$> rslv_to_inst_wproof_3

rslv_to_inst_sig_4 :: SOMetaSignature
rslv_to_inst_sig_4 = SOSignature (Signature [read "p1[0]" --> read "p2[0]" --> EnumProc.Empty] [] (EnumProc.Empty)) (EnumProc.Empty) (read "P1[0]" --> read "P2[0]" --> EnumProc.Empty) EnumProc.Empty

rslv_to_inst_cnf_4 :: SOMetaCNF
rslv_to_inst_cnf_4 = read "[[+p1[0](),+P2[0]()],[-p1[0]()],[-p2[0]()]]"

rslv_to_inst_wproof_4 :: EnumProc (SOMetaUnifSysSolution,[SOMetaResProofStep])
rslv_to_inst_wproof_4 = resolve_and_unify_metacnf rslv_to_inst_sig_4 rslv_to_inst_cnf_4

rslv_to_inst_inst_4 :: EnumProc SOMetaUnifSysSolution
rslv_to_inst_inst_4 = fst <$> rslv_to_inst_wproof_4

rslv_to_inst_sig_5 :: SOMetaSignature
rslv_to_inst_sig_5 = SOSignature (Signature [EnumProc.Empty, read "p1[1]" --> EnumProc.Empty] [read "f1[0]" --> EnumProc.Empty] (EnumProc.Empty)) (EnumProc.Empty) (EnumProc.Empty) EnumProc.Empty

rslv_to_inst_cnf_5 :: SOMetaCNF
rslv_to_inst_cnf_5 = read "[[+p1[1](x0)],[-p1[1](x0)]]"

rslv_to_inst_wproof_5 :: EnumProc (SOMetaUnifSysSolution,[SOMetaResProofStep])
rslv_to_inst_wproof_5 = resolve_and_unify_metacnf rslv_to_inst_sig_5 rslv_to_inst_cnf_5

rslv_to_inst_inst_5 :: EnumProc SOMetaUnifSysSolution
rslv_to_inst_inst_5 = fst <$> rslv_to_inst_wproof_5

rslv_to_inst_sig_6 :: SOMetaSignature
rslv_to_inst_sig_6 = SOSignature (Signature [EnumProc.Empty, read "p1[1]" --> EnumProc.Empty] [read "f1[0]" --> EnumProc.Empty] (EnumProc.Empty)) (EnumProc.Empty) (EnumProc.Empty) EnumProc.Empty

rslv_to_inst_cnf_6 :: SOMetaCNF
rslv_to_inst_cnf_6 = read "[[+p1[1](x0)],[-p1[1](x1)]]"

rslv_to_inst_wproof_6 :: EnumProc (SOMetaUnifSysSolution,[SOMetaResProofStep])
rslv_to_inst_wproof_6 = resolve_and_unify_metacnf rslv_to_inst_sig_6 rslv_to_inst_cnf_6

rslv_to_inst_inst_6 :: EnumProc SOMetaUnifSysSolution
rslv_to_inst_inst_6 = fst <$> rslv_to_inst_wproof_6

rslv_to_inst_sig_7 :: SOMetaSignature
rslv_to_inst_sig_7 = SOSignature (Signature [read "p3[0]" --> EnumProc.Empty, read "p1[1]" --> read "p2[1]" --> EnumProc.Empty] [read "f1[0]" --> EnumProc.Empty] (EnumProc.Empty)) (EnumProc.Empty) (EnumProc.Empty) EnumProc.Empty

rslv_to_inst_cnf_7 :: SOMetaCNF
rslv_to_inst_cnf_7 = read "[[+p1[1](x0)],[-p2[1](x1)],[-p3[0]()]]"

rslv_to_inst_wproof_7 :: EnumProc (SOMetaUnifSysSolution,[SOMetaResProofStep])
rslv_to_inst_wproof_7 = resolve_and_unify_metacnf rslv_to_inst_sig_7 rslv_to_inst_cnf_7

rslv_to_inst_inst_7 :: EnumProc SOMetaUnifSysSolution
rslv_to_inst_inst_7 = fst <$> rslv_to_inst_wproof_7

rslv_to_inst_sig_8 :: SOMetaSignature
rslv_to_inst_sig_8 = SOSignature (Signature [read "p3[0]" --> EnumProc.Empty, read "p1[1]" --> read "p2[1]" --> EnumProc.Empty] [read "f1[0]" --> EnumProc.Empty] (EnumProc.Empty)) (EnumProc.Empty) (EnumProc.Empty) EnumProc.Empty

rslv_to_inst_cnf_8 :: SOMetaCNF
rslv_to_inst_cnf_8 = read "[[+p1[1](f1[0]())],[-p1[1](f1[0]())]]"

rslv_to_inst_wproof_8 :: EnumProc (SOMetaUnifSysSolution,[SOMetaResProofStep])
rslv_to_inst_wproof_8 = resolve_and_unify_metacnf rslv_to_inst_sig_8 rslv_to_inst_cnf_8

rslv_to_inst_inst_8 :: EnumProc SOMetaUnifSysSolution
rslv_to_inst_inst_8 = fst <$> rslv_to_inst_wproof_8

rslv_to_inst_sig_9 :: SOMetaSignature
rslv_to_inst_sig_9 = SOSignature (Signature [read "p3[0]" --> EnumProc.Empty, read "p1[1]" --> read "p2[1]" --> EnumProc.Empty] [read "f1[0]" --> EnumProc.Empty, read "f2[1]" --> EnumProc.Empty] (EnumProc.Empty)) (EnumProc.Empty) (EnumProc.Empty) EnumProc.Empty

rslv_to_inst_cnf_9 :: SOMetaCNF
rslv_to_inst_cnf_9 = read "[[+p1[1](f1[0]())],[-p1[1](x0)]]"

rslv_to_inst_wproof_9 :: EnumProc (SOMetaUnifSysSolution,[SOMetaResProofStep])
rslv_to_inst_wproof_9 = resolve_and_unify_metacnf rslv_to_inst_sig_9 rslv_to_inst_cnf_9

rslv_to_inst_inst_9 :: EnumProc SOMetaUnifSysSolution
rslv_to_inst_inst_9 = fst <$> rslv_to_inst_wproof_9

rslv_to_inst_sig_10 :: SOMetaSignature
rslv_to_inst_sig_10 = SOSignature (Signature [read "p3[0]" --> EnumProc.Empty, read "p1[1]" --> read "p2[1]" --> EnumProc.Empty] [read "f1[0]" --> EnumProc.Empty, read "f2[1]" --> EnumProc.Empty] (EnumProc.Empty)) (EnumProc.Empty) (EnumProc.Empty) EnumProc.Empty

rslv_to_inst_cnf_10 :: SOMetaCNF
rslv_to_inst_cnf_10 = read "[[+p1[1](f1[0]())],[-p1[1](f2[1](x0))]]"

rslv_to_inst_wproof_10 :: EnumProc (SOMetaUnifSysSolution,[SOMetaResProofStep])
rslv_to_inst_wproof_10 = resolve_and_unify_metacnf rslv_to_inst_sig_10 rslv_to_inst_cnf_10

rslv_to_inst_inst_10 :: EnumProc SOMetaUnifSysSolution
rslv_to_inst_inst_10 = fst <$> rslv_to_inst_wproof_10

rslv_to_inst_sig_11 :: SOMetaSignature
rslv_to_inst_sig_11 = SOSignature (Signature [read "p3[0]" --> EnumProc.Empty, read "p1[1]" --> read "p2[1]" --> EnumProc.Empty] [read "f1[0]" --> EnumProc.Empty, read "f2[1]" --> EnumProc.Empty] (EnumProc.Empty)) (EnumProc.Empty) (EnumProc.Empty) EnumProc.Empty

rslv_to_inst_cnf_11 :: SOMetaCNF
rslv_to_inst_cnf_11 = read "[[+p1[1](f2[1](f1[0]()))],[-p1[1](f2[1](x0))]]"

rslv_to_inst_wproof_11 :: EnumProc (SOMetaUnifSysSolution,[SOMetaResProofStep])
rslv_to_inst_wproof_11 = resolve_and_unify_metacnf rslv_to_inst_sig_11 rslv_to_inst_cnf_11

rslv_to_inst_inst_11 :: EnumProc SOMetaUnifSysSolution
rslv_to_inst_inst_11 = fst <$> rslv_to_inst_wproof_11

rslv_to_inst_sig_12 :: SOMetaSignature
rslv_to_inst_sig_12 = SOSignature (Signature [read "p3[0]" --> EnumProc.Empty, read "p1[1]" --> read "p2[1]" --> EnumProc.Empty] [read "f1[0]" --> EnumProc.Empty, read "f2[1]" --> EnumProc.Empty] (EnumProc.Empty)) (EnumProc.Empty) (EnumProc.Empty) EnumProc.Empty

rslv_to_inst_cnf_12 :: SOMetaCNF
rslv_to_inst_cnf_12 = read "[[+p1[1](f2[1](f2[1](f1[0]())))],[-p1[1](f2[1](x0))]]"

rslv_to_inst_wproof_12 :: EnumProc (SOMetaUnifSysSolution,[SOMetaResProofStep])
rslv_to_inst_wproof_12 = resolve_and_unify_metacnf rslv_to_inst_sig_12 rslv_to_inst_cnf_12

rslv_to_inst_inst_12 :: EnumProc SOMetaUnifSysSolution
rslv_to_inst_inst_12 = fst <$> rslv_to_inst_wproof_12

rslv_to_inst_sig_13 :: SOMetaSignature
rslv_to_inst_sig_13 = SOSignature (Signature [read "p3[0]" --> EnumProc.Empty, read "p1[1]" --> read "p2[1]" --> EnumProc.Empty] [read "f1[0]" --> EnumProc.Empty, read "f2[1]" --> EnumProc.Empty] (EnumProc.Empty)) (EnumProc.Empty) (EnumProc.Empty) EnumProc.Empty

rslv_to_inst_cnf_13 :: SOMetaCNF
rslv_to_inst_cnf_13 = read "[[+p1[1](f2[1](f2[1](f1[0]())))],[-p1[1](f2[1](f2[1](f2[1](x0))))]]"

rslv_to_inst_wproof_13 :: EnumProc (SOMetaUnifSysSolution,[SOMetaResProofStep])
rslv_to_inst_wproof_13 = resolve_and_unify_metacnf rslv_to_inst_sig_13 rslv_to_inst_cnf_13

rslv_to_inst_inst_13 :: EnumProc SOMetaUnifSysSolution
rslv_to_inst_inst_13 = fst <$> rslv_to_inst_wproof_13

rslv_to_inst_sig_14 :: SOMetaSignature
rslv_to_inst_sig_14 = SOSignature (Signature [read "p3[0]" --> EnumProc.Empty, read "p1[1]" --> read "p2[1]" --> EnumProc.Empty] [read "f1[0]" --> EnumProc.Empty, read "f2[1]" --> EnumProc.Empty, read "f3[2]" --> EnumProc.Empty] (EnumProc.Empty)) (EnumProc.Empty) (EnumProc.Empty) EnumProc.Empty

rslv_to_inst_cnf_14 :: SOMetaCNF
rslv_to_inst_cnf_14 = read "[[+p1[1](f3[2](x0,x1))],[-p1[1](f3[2](x1,x0))]]"

rslv_to_inst_wproof_14 :: EnumProc (SOMetaUnifSysSolution,[SOMetaResProofStep])
rslv_to_inst_wproof_14 = resolve_and_unify_metacnf rslv_to_inst_sig_14 rslv_to_inst_cnf_14

rslv_to_inst_inst_14 :: EnumProc SOMetaUnifSysSolution
rslv_to_inst_inst_14 = fst <$> rslv_to_inst_wproof_14

rslv_to_inst_sig_15 :: SOMetaSignature
rslv_to_inst_sig_15 = SOSignature (Signature [read "p3[0]" --> EnumProc.Empty, read "p1[1]" --> read "p2[1]" --> EnumProc.Empty] [read "f1[0]" --> EnumProc.Empty, read "f2[1]" --> EnumProc.Empty, read "f3[2]" --> EnumProc.Empty] (EnumProc.Empty)) (EnumProc.Empty) (EnumProc.Empty) EnumProc.Empty

rslv_to_inst_cnf_15 :: SOMetaCNF
rslv_to_inst_cnf_15 = read "[[+p1[1](f3[2](f2[1](x0),f2[1](x1)))],[-p1[1](f3[2](x1,x0))]]"

rslv_to_inst_wproof_15 :: EnumProc (SOMetaUnifSysSolution,[SOMetaResProofStep])
rslv_to_inst_wproof_15 = resolve_and_unify_metacnf rslv_to_inst_sig_15 rslv_to_inst_cnf_15

rslv_to_inst_inst_15 :: EnumProc SOMetaUnifSysSolution
rslv_to_inst_inst_15 = fst <$> rslv_to_inst_wproof_15

rslv_to_inst_sig_16 :: SOMetaSignature
rslv_to_inst_sig_16 = SOSignature (Signature [read "p3[0]" --> EnumProc.Empty, read "p1[1]" --> read "p2[1]" --> EnumProc.Empty] [read "f1[0]" --> EnumProc.Empty, read "f2[1]" --> EnumProc.Empty, read "f3[2]" --> EnumProc.Empty] (EnumProc.Empty)) (EnumProc.Empty) (EnumProc.Empty) EnumProc.Empty

rslv_to_inst_cnf_16 :: SOMetaCNF
rslv_to_inst_cnf_16 = read "[[+p1[1](f3[2](f2[1](x0),f2[1](x1)))],[-p1[1](f3[2](x2,x3))]]"

rslv_to_inst_wproof_16 :: EnumProc (SOMetaUnifSysSolution,[SOMetaResProofStep])
rslv_to_inst_wproof_16 = resolve_and_unify_metacnf rslv_to_inst_sig_16 rslv_to_inst_cnf_16

rslv_to_inst_inst_16 :: EnumProc SOMetaUnifSysSolution
rslv_to_inst_inst_16 = fst <$> rslv_to_inst_wproof_16

rslv_to_inst_sig_17 :: SOMetaSignature
rslv_to_inst_sig_17 = SOSignature (Signature [read "p3[0]" --> EnumProc.Empty, read "p1[1]" --> read "p2[1]" --> EnumProc.Empty] [read "f1[0]" --> EnumProc.Empty, read "f2[1]" --> EnumProc.Empty, read "f3[2]" --> EnumProc.Empty] (EnumProc.Empty)) (read "F1[1]" --> EnumProc.Empty) (EnumProc.Empty) EnumProc.Empty

rslv_to_inst_cnf_17 :: SOMetaCNF
rslv_to_inst_cnf_17 = read "[[+p1[1](f3[2](f2[1](x0),f2[1](x1)))],[-p1[1](f3[2](F1[1](x2),x3))]]"

rslv_to_inst_wproof_17 :: EnumProc (SOMetaUnifSysSolution,[SOMetaResProofStep])
rslv_to_inst_wproof_17 = resolve_and_unify_metacnf rslv_to_inst_sig_17 rslv_to_inst_cnf_17

rslv_to_inst_inst_17 :: EnumProc SOMetaUnifSysSolution
rslv_to_inst_inst_17 = fst <$> rslv_to_inst_wproof_17

rslv_to_inst_sig_18 :: SOMetaSignature
rslv_to_inst_sig_18 = SOSignature (Signature [read "p3[0]" --> EnumProc.Empty, read "p1[1]" --> read "p2[1]" --> EnumProc.Empty] [read "f1[0]" --> EnumProc.Empty, read "f2[1]" --> EnumProc.Empty, read "f3[2]" --> EnumProc.Empty] (EnumProc.Empty)) (read "F1[1]" --> read "F2[1]" --> EnumProc.Empty) (read "P1[1]" --> EnumProc.Empty) EnumProc.Empty

rslv_to_inst_cnf_18 :: SOMetaCNF
rslv_to_inst_cnf_18 = read "[[+p1[1](F1[1](x0)),-p2[1](x1)],[+P1[1](F2[1](f1[0]())),+p1[1](f2[1](x2))],[-p1[1](f2[1](x4))]]"

rslv_to_inst_wproof_18 :: EnumProc (SOMetaUnifSysSolution,[SOMetaResProofStep])
rslv_to_inst_wproof_18 = resolve_and_unify_metacnf rslv_to_inst_sig_18 rslv_to_inst_cnf_18

rslv_to_inst_inst_18 :: EnumProc SOMetaUnifSysSolution
rslv_to_inst_inst_18 = fst <$> rslv_to_inst_wproof_18
