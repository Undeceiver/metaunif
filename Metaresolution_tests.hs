{-# LANGUAGE PartialTypeSignatures #-}
module Metaresolution_tests where

import AutoTests
import Metaresolution
import Constraints
import Metaresolution_heuristics
--import Constraint_tests
import Data.List
import Data.Maybe
import Data.Either
import Data.Time

-- Unifiers
u0 :: Unifier
u0 = U 0

resrule_nvars = 3
resrule_mvs = [read "X0",read "X1",read "X2"]

resrule_sig :: ExtendedSignature
resrule_sig = (([read "p1[0]",read "p2[0]",read "p3[0]",read "p4[2]",read "p5[1]"],[],3),([[read "X0",read "X1"]],3,[0]),[],[])

-- type ExtendedSignature = (Signature,MetavariablePartition,[Term],[MetavariableLink])
-- type Signature = ([Predicate],[Function],Int)
-- type MetavariablePartition = ([[Metavariable]],Int,[Int])
-- type MetavariableLink = (Metavariable,[(Metavariable,Either Term Literal -> Either Term Literal)])


-- Resolution rule tests
resolvent_eq_test :: Clause -> Clause -> AutomatedTestResult
resolvent_eq_test cl1 cl2 | (eq_clause cl1 cl2) = ATR True "Resolvent correct."
resolvent_eq_test cl1 cl2 = ATR False ("Resolvent " ++ (show cl2) ++ " is not equal to expected resolvent " ++ (show cl1) ++ ".")

generated_cstr_test :: Constraint -> Constraint -> AutomatedTestResult
generated_cstr_test cstr1 cstr2 | cstr1 == cstr2 = ATR True "Generated constraint correct."
generated_cstr_test cstr1 cstr2 = ATR False ("Generated constraint " ++ (show cstr2) ++ " is not equal to expected generated constraint " ++ (show cstr1) ++ ".")

empty_clause_possible_test :: Bool -> Bool -> AutomatedTestResult
empty_clause_possible_test True True = ATR True "Empty clause found."
empty_clause_possible_test False False = ATR True "Empty clause cannot be directly found."
empty_clause_possible_test True False = ATR False "The empty clause could not be found but it should have."
empty_clause_possible_test False True = ATR False "The empty clause was found but it should not have."

empty_clause_cstrs_test :: [Constraint] -> Bool -> [Constraint] -> AutomatedTestResult
empty_clause_cstrs_test _ False _ = ATR False "Empty clause could not be found, so there are no generated constraints."
empty_clause_cstrs_test cstrs1 True cstrs2 | (eq_no_order_wrt (==) cstrs1 cstrs2) = ATR True "Correct constraints generated for the empty clause."
empty_clause_cstrs_test cstrs1 True cstrs2 = ATR False ("The expected constraints for the empty clause were:\n\n" ++ (show cstrs1) ++ "\n\nBut the actually found ones were:\n\n" ++ (show cstrs2) ++ "\n")

resulting_cnf_test :: CNF -> CNF -> AutomatedTestResult
resulting_cnf_test cnf1 cnf2 | (eq_cnf cnf1 cnf2) = ATR True "Resulting CNF correct."
resulting_cnf_test cnf1 cnf2 = ATR False ("Resulting CNF " ++ (show cnf2) ++ " is not equal to expected resulting CNF " ++ (show cnf1) ++ ".")

-- Example 1

resrule_cnf1 :: CNF
resrule_cnf1 = read "[[+p1[0]()],[-p1[0]()]]"

resrule_std_sig1 :: ExtendedSignature
resrule_std_mvs1 :: [Metavariable]
resrule_std_cnf1 :: CNF
(resrule_std_sig1,resrule_std_mvs1,resrule_std_cnf1) = standardize_apart (resrule_sig,resrule_mvs,resrule_cnf1)

resrule_posclause1 :: Clause
resrule_posclause1 = resrule_std_cnf1 !! 0
resrule_negclause1 :: Clause
resrule_negclause1 = resrule_std_cnf1 !! 1

resrule_poslit1 :: Metaliteral
resrule_poslit1 = get_atom (resrule_posclause1 !! 0)
resrule_neglit1 :: Metaliteral
resrule_neglit1 = get_atom (resrule_negclause1 !! 0)

resrule_remposclause1 :: Clause
resrule_remposclause1 = resrule_posclause1 \\ [PosLit resrule_poslit1]
resrule_remnegclause1 :: Clause
resrule_remnegclause1 = resrule_negclause1 \\ [NegLit resrule_neglit1]

resrule_fs1 :: FullSolution
resrule_fs1 = (resrule_std_mvs1,[],(idinst,[]),(empty_graph,[],[]))

resrule_loginst1 :: LogicalInstantiation
resrule_loginst1 = idloginst

resrule_resolvent1 :: Clause
resrule_gencstr1 :: Constraint
(resrule_gencstr1,resrule_resolvent1) = apply_resolution_rule u0 resrule_poslit1 resrule_neglit1 resrule_remposclause1 resrule_remnegclause1

--resrule_std_sig1_2 :: ExtendedSignature
--resrule_std_mvs1_2 :: [Metavariable]
--resrule_std_resolvent1 :: Clause
--(resrule_std_sig1_2,resrule_std_mvs1_2,resrule_std_resolvent1) = standardize_new_clause (resrule_sig,resrule_mvs) (length resrule_std_cnf1) (resrule_std_sig1,resrule_std_mvs1,resrule_resolvent1)

resrule_rescnf1 :: CNF
resrule_rescnf1 = clean_deffo_cnf (append_clause resrule_std_cnf1 resrule_resolvent1)

resrule_parcresfs1 :: FullSolution
resrule_parcresfs1 = (mvs,mveqs,(inst,resrule_gencstr1:cs),(g,gsol,ueqs)) where (mvs,mveqs,(inst,cs),(g,gsol,ueqs)) = resrule_fs1

resrule_resfs1 :: FullSolution
resrule_resloginst1 :: LogicalInstantiation
resrule_canempty1 :: Bool
resrule_ifempty1 :: (FullSolution,LogicalInstantiation)
(resrule_ifempty1,resrule_canempty1) = (fromJust maybe,isJust maybe) where maybe = (force_empty_clause resrule_std_sig1 (resrule_parcresfs1,resrule_loginst1) u0 resrule_poslit1 resrule_neglit1 resrule_remposclause1 resrule_remnegclause1)
(resrule_resfs1,resrule_resloginst1) = resrule_ifempty1
resrule_emptycstrs1 :: [Constraint]
resrule_emptycstrs1 = cstrs where (_,_,(_,cstrs),_) = resrule_resfs1

resrule1_t1 = AT "Resolvent is the empty clause" (resolvent_eq_test (read "[]") resrule_resolvent1)
resrule1_t2 = AT "Generated constraint is up = up" (generated_cstr_test (Lcstr (read "u0 p1[0]()") (read "u0 p1[0]()")) resrule_gencstr1)
resrule1_t3 = AT "Empty clause can be found" (empty_clause_possible_test True resrule_canempty1)
resrule1_t4 = AT "Empty clause if up = up" (empty_clause_cstrs_test [Lcstr (read "u0 p1[0]()") (read "u0 p1[0]()")] resrule_canempty1 resrule_emptycstrs1)
resrule1_t5 = AT "Resulting CNF is [[+p],[-p],[]]" (resulting_cnf_test (read "[[+p1[0]()],[-p1[0]()],[]]") resrule_rescnf1)

resrule1_ts = [resrule1_t1,resrule1_t2,resrule1_t3,resrule1_t4,resrule1_t5]

resrule1_test = putStr (combine_test_results resrule1_ts)

-- Example 2

resrule_cnf2 :: CNF
resrule_cnf2 = read "[[+p1[0](),+p1[0]()],[-p1[0]()]]"

resrule_std_sig2 :: ExtendedSignature
resrule_std_mvs2 :: [Metavariable]
resrule_std_cnf2 :: CNF
(resrule_std_sig2,resrule_std_mvs2,resrule_std_cnf2) = standardize_apart (resrule_sig,resrule_mvs,resrule_cnf2)

resrule_posclause2 :: Clause
resrule_posclause2 = resrule_std_cnf2 !! 0
resrule_negclause2 :: Clause
resrule_negclause2 = resrule_std_cnf2 !! 1

resrule_poslit2 :: Metaliteral
resrule_poslit2 = get_atom (resrule_posclause2 !! 0)
resrule_neglit2 :: Metaliteral
resrule_neglit2 = get_atom (resrule_negclause2 !! 0)

resrule_remposclause2 :: Clause
resrule_remposclause2 = resrule_posclause2 \\ [PosLit resrule_poslit2]
resrule_remnegclause2 :: Clause
resrule_remnegclause2 = resrule_negclause2 \\ [NegLit resrule_neglit2]

resrule_fs2 :: FullSolution
resrule_fs2 = (resrule_std_mvs2,[],(idinst,[]),(empty_graph,[],[]))

resrule_loginst2 :: LogicalInstantiation
resrule_loginst2 = idloginst

resrule_resolvent2 :: Clause
resrule_gencstr2 :: Constraint
(resrule_gencstr2,resrule_resolvent2) = apply_resolution_rule u0 resrule_poslit2 resrule_neglit2 resrule_remposclause2 resrule_remnegclause2

--resrule_std_sig2_2 :: ExtendedSignature
--resrule_std_mvs2_2 :: [Metavariable]
--resrule_std_resolvent2 :: Clause
--(resrule_std_sig2_2,resrule_std_mvs2_2,resrule_std_resolvent2) = standardize_new_clause (resrule_sig,resrule_mvs) (length resrule_std_cnf2) (resrule_std_sig2,resrule_std_mvs2,resrule_resolvent2)

resrule_rescnf2 :: CNF
resrule_rescnf2 = clean_deffo_cnf (append_clause resrule_std_cnf2 resrule_resolvent2)

resrule_parcresfs2 :: FullSolution
resrule_parcresfs2 = (mvs,mveqs,(inst,resrule_gencstr2:cs),(g,gsol,ueqs)) where (mvs,mveqs,(inst,cs),(g,gsol,ueqs)) = resrule_fs2

resrule_resfs2 :: FullSolution
resrule_resloginst2 :: LogicalInstantiation
resrule_canempty2 :: Bool
resrule_ifempty2 :: (FullSolution,LogicalInstantiation)
(resrule_ifempty2,resrule_canempty2) = (fromJust maybe,isJust maybe) where maybe = (force_empty_clause resrule_std_sig2 (resrule_parcresfs2,resrule_loginst2) u0 resrule_poslit2 resrule_neglit2 resrule_remposclause2 resrule_remnegclause2)
(resrule_resfs2,resrule_resloginst2) = resrule_ifempty2
resrule_emptycstrs2 :: [Constraint]
resrule_emptycstrs2 = cstrs where (_,_,(_,cstrs),_) = resrule_resfs2

resrule2_t1 = AT "Resolvent is +up" (resolvent_eq_test (read "[+u0 p1[0]()]") resrule_resolvent2)
resrule2_t2 = AT "Generated constraint is up = up" (generated_cstr_test (Lcstr (read "u0 p1[0]()") (read "u0 p1[0]()")) resrule_gencstr2)
resrule2_t3 = AT "Empty clause can be found" (empty_clause_possible_test True resrule_canempty2)
resrule2_t4 = AT "Empty clause if up = up, up = up" (empty_clause_cstrs_test [Lcstr (read "u0 p1[0]()") (read "u0 p1[0]()"),Lcstr (read "u0 p1[0]()") (read "u0 p1[0]()")] resrule_canempty2 resrule_emptycstrs2)
resrule2_t5 = AT "Resulting CNF is [[+p,+p],[-p],[+up]]" (resulting_cnf_test (read "[[+p1[0](),+p1[0]()],[-p1[0]()],[+u0 p1[0]()]]") resrule_rescnf2)

resrule2_ts = [resrule2_t1,resrule2_t2,resrule2_t3,resrule2_t4,resrule2_t5]

resrule2_test = putStr (combine_test_results resrule2_ts)

-- Example 3

resrule_cnf3 :: CNF
resrule_cnf3 = read "[[+p1[0](),+p2[0]()],[-p1[0](),+p3[0]()]]"

resrule_std_sig3 :: ExtendedSignature
resrule_std_mvs3 :: [Metavariable]
resrule_std_cnf3 :: CNF
(resrule_std_sig3,resrule_std_mvs3,resrule_std_cnf3) = standardize_apart (resrule_sig,resrule_mvs,resrule_cnf3)

resrule_posclause3 :: Clause
resrule_posclause3 = resrule_std_cnf3 !! 0
resrule_negclause3 :: Clause
resrule_negclause3 = resrule_std_cnf3 !! 1

resrule_poslit3 :: Metaliteral
resrule_poslit3 = get_atom (resrule_posclause3 !! 0)
resrule_neglit3 :: Metaliteral
resrule_neglit3 = get_atom (resrule_negclause3 !! 0)

resrule_remposclause3 :: Clause
resrule_remposclause3 = resrule_posclause3 \\ [PosLit resrule_poslit3]
resrule_remnegclause3 :: Clause
resrule_remnegclause3 = resrule_negclause3 \\ [NegLit resrule_neglit3]

resrule_fs3 :: FullSolution
resrule_fs3 = (resrule_std_mvs3,[],(idinst,[]),(empty_graph,[],[]))

resrule_loginst3 :: LogicalInstantiation
resrule_loginst3 = idloginst

resrule_resolvent3 :: Clause
resrule_gencstr3 :: Constraint
(resrule_gencstr3,resrule_resolvent3) = apply_resolution_rule u0 resrule_poslit3 resrule_neglit3 resrule_remposclause3 resrule_remnegclause3

--resrule_std_sig3_2 :: ExtendedSignature
--resrule_std_mvs3_2 :: [Metavariable]
--resrule_std_resolvent3 :: Clause
--(resrule_std_sig3_2,resrule_std_mvs3_2,resrule_std_resolvent3) = standardize_new_clause (resrule_sig,resrule_mvs) (length resrule_std_cnf3) (resrule_std_sig3,resrule_std_mvs3,resrule_resolvent3)

resrule_rescnf3 :: CNF
resrule_rescnf3 = clean_deffo_cnf (append_clause resrule_std_cnf3 resrule_resolvent3)

resrule_parcresfs3 :: FullSolution
resrule_parcresfs3 = (mvs,mveqs,(inst,resrule_gencstr3:cs),(g,gsol,ueqs)) where (mvs,mveqs,(inst,cs),(g,gsol,ueqs)) = resrule_fs3

resrule_resfs3 :: FullSolution
resrule_resloginst3 :: LogicalInstantiation
resrule_canempty3 :: Bool
resrule_ifempty3 :: (FullSolution,LogicalInstantiation)
(resrule_ifempty3,resrule_canempty3) = (fromJust maybe,isJust maybe) where maybe = (force_empty_clause resrule_std_sig3 (resrule_parcresfs3,resrule_loginst3) u0 resrule_poslit3 resrule_neglit3 resrule_remposclause3 resrule_remnegclause3)
(resrule_resfs3,resrule_resloginst3) = resrule_ifempty3
resrule_emptycstrs3 :: [Constraint]
resrule_emptycstrs3 = cstrs where (_,_,(_,cstrs),_) = resrule_resfs3

resrule3_t1 = AT "Resolvent is [+uq,+ur]" (resolvent_eq_test (read "[+u0 p2[0](),+u0 p3[0]()]") resrule_resolvent3)
resrule3_t2 = AT "Generated constraint is up = up" (generated_cstr_test (Lcstr (read "u0 p1[0]()") (read "u0 p1[0]()")) resrule_gencstr3)
resrule3_t3 = AT "Empty clause cannot be found" (empty_clause_possible_test False resrule_canempty3)
resrule3_t4 = AT "Resulting CNF is [[+p,+q],[-p,+r],[+uq,+ur]]" (resulting_cnf_test (read "[[+p1[0](),+p2[0]()],[-p1[0](),+p3[0]()],[+u0 p2[0](),+u0 p3[0]()]]") resrule_rescnf3)

resrule3_ts = [resrule3_t1,resrule3_t2,resrule3_t3,resrule3_t4]

resrule3_test = putStr (combine_test_results resrule3_ts)

-- Example 4

resrule_cnf4 :: CNF
resrule_cnf4 = read "[[+p1[0](),+p2[0]()],[-p1[0](),-p3[0]()]]"

resrule_std_sig4 :: ExtendedSignature
resrule_std_mvs4 :: [Metavariable]
resrule_std_cnf4 :: CNF
(resrule_std_sig4,resrule_std_mvs4,resrule_std_cnf4) = standardize_apart (resrule_sig,resrule_mvs,resrule_cnf4)

resrule_posclause4 :: Clause
resrule_posclause4 = resrule_std_cnf4 !! 0
resrule_negclause4 :: Clause
resrule_negclause4 = resrule_std_cnf4 !! 1

resrule_poslit4 :: Metaliteral
resrule_poslit4 = get_atom (resrule_posclause4 !! 0)
resrule_neglit4 :: Metaliteral
resrule_neglit4 = get_atom (resrule_negclause4 !! 0)

resrule_remposclause4 :: Clause
resrule_remposclause4 = resrule_posclause4 \\ [PosLit resrule_poslit4]
resrule_remnegclause4 :: Clause
resrule_remnegclause4 = resrule_negclause4 \\ [NegLit resrule_neglit4]

resrule_fs4 :: FullSolution
resrule_fs4 = (resrule_std_mvs4,[],(idinst,[]),(empty_graph,[],[]))

resrule_loginst4 :: LogicalInstantiation
resrule_loginst4 = idloginst

resrule_resolvent4 :: Clause
resrule_gencstr4 :: Constraint
(resrule_gencstr4,resrule_resolvent4) = apply_resolution_rule u0 resrule_poslit4 resrule_neglit4 resrule_remposclause4 resrule_remnegclause4

--resrule_std_sig4_2 :: ExtendedSignature
--resrule_std_mvs4_2 :: [Metavariable]
--resrule_std_resolvent4 :: Clause
--(resrule_std_sig4_2,resrule_std_mvs4_2,resrule_std_resolvent4) = standardize_new_clause (resrule_sig,resrule_mvs) (length resrule_std_cnf4) (resrule_std_sig4,resrule_std_mvs4,resrule_resolvent4)

resrule_rescnf4 :: CNF
resrule_rescnf4 = clean_deffo_cnf (append_clause resrule_std_cnf4 resrule_resolvent4)

resrule_parcresfs4 :: FullSolution
resrule_parcresfs4 = (mvs,mveqs,(inst,resrule_gencstr4:cs),(g,gsol,ueqs)) where (mvs,mveqs,(inst,cs),(g,gsol,ueqs)) = resrule_fs4

resrule_resfs4 :: FullSolution
resrule_resloginst4 :: LogicalInstantiation
resrule_canempty4 :: Bool
resrule_ifempty4 :: (FullSolution,LogicalInstantiation)
(resrule_ifempty4,resrule_canempty4) = (fromJust maybe,isJust maybe) where maybe = (force_empty_clause resrule_std_sig4 (resrule_parcresfs4,resrule_loginst4) u0 resrule_poslit4 resrule_neglit4 resrule_remposclause4 resrule_remnegclause4)
(resrule_resfs4,resrule_resloginst4) = resrule_ifempty4
resrule_emptycstrs4 :: [Constraint]
resrule_emptycstrs4 = cstrs where (_,_,(_,cstrs),_) = resrule_resfs4

resrule4_t1 = AT "Resolvent is [+uq,-ur]" (resolvent_eq_test (read "[+u0 p2[0](),-u0 p3[0]()]") resrule_resolvent4)
resrule4_t2 = AT "Generated constraint is up = up" (generated_cstr_test (Lcstr (read "u0 p1[0]()") (read "u0 p1[0]()")) resrule_gencstr4)
resrule4_t3 = AT "Empty clause cannot be found" (empty_clause_possible_test False resrule_canempty4)
resrule4_t4 = AT "Resulting CNF is [[+p,+q],[-p,-r],[+uq,-ur]]" (resulting_cnf_test (read "[[+p1[0](),+p2[0]()],[-p1[0](),-p3[0]()],[+u0 p2[0](),-u0 p3[0]()]]") resrule_rescnf4)

resrule4_ts = [resrule4_t1,resrule4_t2,resrule4_t3,resrule4_t4]

resrule4_test = putStr (combine_test_results resrule4_ts)

-- Example 5

resrule_cnf5 :: CNF
resrule_cnf5 = read "[[+p4[2](x0,x1)],[-p4[2](x1,x0)]]"

resrule_std_sig5 :: ExtendedSignature
resrule_std_mvs5 :: [Metavariable]
resrule_std_cnf5 :: CNF
(resrule_std_sig5,resrule_std_mvs5,resrule_std_cnf5) = standardize_apart (resrule_sig,resrule_mvs,resrule_cnf5)

resrule_posclause5 :: Clause
resrule_posclause5 = resrule_std_cnf5 !! 0
resrule_negclause5 :: Clause
resrule_negclause5 = resrule_std_cnf5 !! 1

resrule_poslit5 :: Metaliteral
resrule_poslit5 = get_atom (resrule_posclause5 !! 0)
resrule_neglit5 :: Metaliteral
resrule_neglit5 = get_atom (resrule_negclause5 !! 0)

resrule_remposclause5 :: Clause
resrule_remposclause5 = resrule_posclause5 \\ [PosLit resrule_poslit5]
resrule_remnegclause5 :: Clause
resrule_remnegclause5 = resrule_negclause5 \\ [NegLit resrule_neglit5]

resrule_fs5 :: FullSolution
resrule_fs5 = (resrule_std_mvs5,[],(idinst,[]),(empty_graph,[],[]))

resrule_loginst5 :: LogicalInstantiation
resrule_loginst5 = idloginst

resrule_resolvent5 :: Clause
resrule_gencstr5 :: Constraint
(resrule_gencstr5,resrule_resolvent5) = apply_resolution_rule u0 resrule_poslit5 resrule_neglit5 resrule_remposclause5 resrule_remnegclause5

--resrule_std_sig5_2 :: ExtendedSignature
--resrule_std_mvs5_2 :: [Metavariable]
--resrule_std_resolvent5 :: Clause
--(resrule_std_sig5_2,resrule_std_mvs5_2,resrule_std_resolvent5) = standardize_new_clause (resrule_sig,resrule_mvs) (length resrule_std_cnf5) (resrule_std_sig5,resrule_std_mvs5,resrule_resolvent5)

resrule_rescnf5 :: CNF
resrule_rescnf5 = clean_deffo_cnf (append_clause resrule_std_cnf5 resrule_resolvent5)

resrule_parcresfs5 :: FullSolution
resrule_parcresfs5 = (mvs,mveqs,(inst,resrule_gencstr5:cs),(g,gsol,ueqs)) where (mvs,mveqs,(inst,cs),(g,gsol,ueqs)) = resrule_fs5

resrule_resfs5 :: FullSolution
resrule_resloginst5 :: LogicalInstantiation
resrule_canempty5 :: Bool
resrule_ifempty5 :: (FullSolution,LogicalInstantiation)
(resrule_ifempty5,resrule_canempty5) = (fromJust maybe,isJust maybe) where maybe = (force_empty_clause resrule_std_sig5 (resrule_parcresfs5,resrule_loginst5) u0 resrule_poslit5 resrule_neglit5 resrule_remposclause5 resrule_remnegclause5)
(resrule_resfs5,resrule_resloginst5) = resrule_ifempty5
resrule_emptycstrs5 :: [Constraint]
resrule_emptycstrs5 = cstrs where (_,_,(_,cstrs),_) = resrule_resfs5

resrule5_t1 = AT "Resolvent is the empty clause." (resolvent_eq_test (read "[]") resrule_resolvent5)
resrule5_t2 = AT "Generated constraint is up(x,y) = up(y',x')" (generated_cstr_test (Lcstr (read "u0 p4[2](x0,x1)") (MLitR u0 (standardize_metaliteral resrule_nvars resrule_mvs 1 (read "p4[2](x1,x0)")))) resrule_gencstr5)
resrule5_t3 = AT "Empty clause can be found" (empty_clause_possible_test True resrule_canempty5)
resrule5_t4 = AT "Empty clause if up(x,y) = up(y',x')" (empty_clause_cstrs_test [Lcstr (read "u0 p4[2](x0,x1)") (MLitR u0 (standardize_metaliteral resrule_nvars resrule_mvs 1 (read "p4[2](x1,x0)")))] resrule_canempty5 resrule_emptycstrs5)
resrule5_t5 = AT "Resulting CNF is [[+p(x,y)],[-p(y',x')],[]]" (resulting_cnf_test [read "[+p4[2](x0,x1)]",standardize_clause resrule_nvars resrule_mvs 1 (read "[-p4[2](x1,x0)]"),[]] resrule_rescnf5)

resrule5_ts = [resrule5_t1,resrule5_t2,resrule5_t3,resrule5_t4,resrule5_t5]

resrule5_test = putStr (combine_test_results resrule5_ts)

-- Example 6

resrule_cnf6 :: CNF
resrule_cnf6 = read "[[+p4[2](x0,x1),+p5[1](x0)],[-p4[2](x1,x0),+p5[1](x0)]]"

resrule_std_sig6 :: ExtendedSignature
resrule_std_mvs6 :: [Metavariable]
resrule_std_cnf6 :: CNF
(resrule_std_sig6,resrule_std_mvs6,resrule_std_cnf6) = standardize_apart (resrule_sig,resrule_mvs,resrule_cnf6)

resrule_posclause6 :: Clause
resrule_posclause6 = resrule_std_cnf6 !! 0
resrule_negclause6 :: Clause
resrule_negclause6 = resrule_std_cnf6 !! 1

resrule_poslit6 :: Metaliteral
resrule_poslit6 = get_atom (resrule_posclause6 !! 0)
resrule_neglit6 :: Metaliteral
resrule_neglit6 = get_atom (resrule_negclause6 !! 0)

resrule_remposclause6 :: Clause
resrule_remposclause6 = resrule_posclause6 \\ [PosLit resrule_poslit6]
resrule_remnegclause6 :: Clause
resrule_remnegclause6 = resrule_negclause6 \\ [NegLit resrule_neglit6]

resrule_fs6 :: FullSolution
resrule_fs6 = (resrule_std_mvs6,[],(idinst,[]),(empty_graph,[],[]))

resrule_loginst6 :: LogicalInstantiation
resrule_loginst6 = idloginst

resrule_resolvent6 :: Clause
resrule_gencstr6 :: Constraint
(resrule_gencstr6,resrule_resolvent6) = apply_resolution_rule u0 resrule_poslit6 resrule_neglit6 resrule_remposclause6 resrule_remnegclause6

--resrule_std_sig6_2 :: ExtendedSignature
--resrule_std_mvs6_2 :: [Metavariable]
--resrule_std_resolvent6 :: Clause
--(resrule_std_sig6_2,resrule_std_mvs6_2,resrule_std_resolvent6) = standardize_new_clause (resrule_sig,resrule_mvs) (length resrule_std_cnf6) (resrule_std_sig6,resrule_std_mvs6,resrule_resolvent6)

resrule_rescnf6 :: CNF
resrule_rescnf6 = clean_deffo_cnf (append_clause resrule_std_cnf6 resrule_resolvent6)

resrule_parcresfs6 :: FullSolution
resrule_parcresfs6 = (mvs,mveqs,(inst,resrule_gencstr6:cs),(g,gsol,ueqs)) where (mvs,mveqs,(inst,cs),(g,gsol,ueqs)) = resrule_fs6

resrule_resfs6 :: FullSolution
resrule_resloginst6 :: LogicalInstantiation
resrule_canempty6 :: Bool
resrule_ifempty6 :: (FullSolution,LogicalInstantiation)
(resrule_ifempty6,resrule_canempty6) = (fromJust maybe,isJust maybe) where maybe = (force_empty_clause resrule_std_sig6 (resrule_parcresfs6,resrule_loginst6) u0 resrule_poslit6 resrule_neglit6 resrule_remposclause6 resrule_remnegclause6)
(resrule_resfs6,resrule_resloginst6) = resrule_ifempty6
resrule_emptycstrs6 :: [Constraint]
resrule_emptycstrs6 = cstrs where (_,_,(_,cstrs),_) = resrule_resfs6

resrule6_t1 = AT "Resolvent is [+u q(x),+u q(x')]." (resolvent_eq_test [read "+u0 p5[1](x0)",PosLit (MLitR u0 (standardize_metaliteral resrule_nvars resrule_mvs 1 (read "p5[1](x0)")))] resrule_resolvent6)
resrule6_t2 = AT "Generated constraint is up(x,y) = up(y',x')" (generated_cstr_test (Lcstr (read "u0 p4[2](x0,x1)") (MLitR u0 (standardize_metaliteral resrule_nvars resrule_mvs 1 (read "p4[2](x1,x0)")))) resrule_gencstr6)
resrule6_t3 = AT "Empty clause cannot be found" (empty_clause_possible_test False resrule_canempty6)
resrule6_t4 = AT "Resulting CNF is [[+p(x,y),+q(x)],[-p(y',x'),+q(x')],[+u q(x),+u q(x')]]" (resulting_cnf_test [read "[+p4[2](x0,x1),+p5[1](x0)]",standardize_clause resrule_nvars resrule_mvs 1 (read "[-p4[2](x1,x0),+p5[1](x0)]"),[PosLit (MLitR u0 (read "p5[1](x0)")),PosLit (MLitR u0 (standardize_metaliteral resrule_nvars resrule_mvs 1 (read "p5[1](x0)")))]] resrule_rescnf6)

resrule6_ts = [resrule6_t1,resrule6_t2,resrule6_t3,resrule6_t4]

resrule6_test = putStr (combine_test_results resrule6_ts)

-- Example 7

resrule_cnf7 :: CNF
resrule_cnf7 = read "[[+p4[2](x0,x1),+p4[2](x0,x2)],[-p4[2](x1,x0),-p4[2](x0,x2)]]"

resrule_std_sig7 :: ExtendedSignature
resrule_std_mvs7 :: [Metavariable]
resrule_std_cnf7 :: CNF
(resrule_std_sig7,resrule_std_mvs7,resrule_std_cnf7) = standardize_apart (resrule_sig,resrule_mvs,resrule_cnf7)

resrule_posclause7 :: Clause
resrule_posclause7 = resrule_std_cnf7 !! 0
resrule_negclause7 :: Clause
resrule_negclause7 = resrule_std_cnf7 !! 1

resrule_poslit7 :: Metaliteral
resrule_poslit7 = get_atom (resrule_posclause7 !! 0)
resrule_neglit7 :: Metaliteral
resrule_neglit7 = get_atom (resrule_negclause7 !! 0)

resrule_remposclause7 :: Clause
resrule_remposclause7 = resrule_posclause7 \\ [PosLit resrule_poslit7]
resrule_remnegclause7 :: Clause
resrule_remnegclause7 = resrule_negclause7 \\ [NegLit resrule_neglit7]

resrule_fs7 :: FullSolution
resrule_fs7 = (resrule_std_mvs7,[],(idinst,[]),(empty_graph,[],[]))

resrule_loginst7 :: LogicalInstantiation
resrule_loginst7 = idloginst

resrule_resolvent7 :: Clause
resrule_gencstr7 :: Constraint
(resrule_gencstr7,resrule_resolvent7) = apply_resolution_rule u0 resrule_poslit7 resrule_neglit7 resrule_remposclause7 resrule_remnegclause7

--resrule_std_sig6_2 :: ExtendedSignature
--resrule_std_mvs6_2 :: [Metavariable]
--resrule_std_resolvent6 :: Clause
--(resrule_std_sig6_2,resrule_std_mvs6_2,resrule_std_resolvent6) = standardize_new_clause (resrule_sig,resrule_mvs) (length resrule_std_cnf6) (resrule_std_sig6,resrule_std_mvs6,resrule_resolvent6)

resrule_rescnf7 :: CNF
resrule_rescnf7 = clean_deffo_cnf (append_clause resrule_std_cnf7 resrule_resolvent7)

resrule_parcresfs7 :: FullSolution
resrule_parcresfs7 = (mvs,mveqs,(inst,resrule_gencstr7:cs),(g,gsol,ueqs)) where (mvs,mveqs,(inst,cs),(g,gsol,ueqs)) = resrule_fs7

resrule_resfs7 :: FullSolution
resrule_resloginst7 :: LogicalInstantiation
resrule_canempty7 :: Bool
resrule_ifempty7 :: (FullSolution,LogicalInstantiation)
(resrule_ifempty7,resrule_canempty7) = (fromJust maybe,isJust maybe) where maybe = (force_empty_clause resrule_std_sig7 (resrule_parcresfs7,resrule_loginst7) u0 resrule_poslit7 resrule_neglit7 resrule_remposclause7 resrule_remnegclause7)
(resrule_resfs7,resrule_resloginst7) = resrule_ifempty7
resrule_emptycstrs7 :: [Constraint]
resrule_emptycstrs7 = cstrs where (_,_,(_,cstrs),_) = resrule_resfs7

resrule7_t1 = AT "Resolvent is [+u p(x,z),-u p(x',z')]." (resolvent_eq_test [read "+u0 p4[2](x0,x2)",NegLit (MLitR u0 (standardize_metaliteral resrule_nvars resrule_mvs 1 (read "p4[2](x0,x2)")))] resrule_resolvent7)
resrule7_t2 = AT "Generated constraint is up(x,y) = up(y',x')" (generated_cstr_test (Lcstr (read "u0 p4[2](x0,x1)") (MLitR u0 (standardize_metaliteral resrule_nvars resrule_mvs 1 (read "p4[2](x1,x0)")))) resrule_gencstr7)
resrule7_t3 = AT "Empty clause can be found" (empty_clause_possible_test True resrule_canempty7)
resrule7_t4 = AT "Empty clause if up(x,y) = up(y',x'), up(x,y) = up(x,z), up(y',x') = up(x',z')" (empty_clause_cstrs_test [Lcstr (read "u0 p4[2](x0,x1)") (MLitR u0 (standardize_metaliteral resrule_nvars resrule_mvs 1 (read "p4[2](x1,x0)"))), Lcstr (read "u0 p4[2](x0,x1)") (read "u0 p4[2](x0,x2)"), Lcstr (MLitR u0 (standardize_metaliteral resrule_nvars resrule_mvs 1 (read "p4[2](x1,x0)"))) (MLitR u0 (standardize_metaliteral resrule_nvars resrule_mvs 1 (read "p4[2](x0,x2)")))] resrule_canempty7 resrule_emptycstrs7)
resrule7_t5 = AT "Resulting CNF is [[+p(x,y),+p(x,z)],[-p(y',x'),-p(x',z')],[+u p(x,z),-u p(x',z')]]" (resulting_cnf_test [read "[+p4[2](x0,x1),+p4[2](x0,x2)]",standardize_clause resrule_nvars resrule_mvs 1 (read "[-p4[2](x1,x0),-p4[2](x0,x2)]"),[PosLit (MLitR u0 (read "p4[2](x0,x2)")),NegLit (MLitR u0 (standardize_metaliteral resrule_nvars resrule_mvs 1 (read "p4[2](x0,x2)")))]] resrule_rescnf7)

resrule7_ts = [resrule7_t1,resrule7_t2,resrule7_t3,resrule7_t4,resrule7_t5]

resrule7_test = putStr (combine_test_results resrule7_ts)

-- Example 8

resrule_cnf8 :: CNF
resrule_cnf8 = read "[[+p4[2](x0,x1),+p4[2](x0,x2)],[-p4[2](x1,x0),+p4[2](x0,x2)]]"

resrule_std_sig8 :: ExtendedSignature
resrule_std_mvs8 :: [Metavariable]
resrule_std_cnf8 :: CNF
(resrule_std_sig8,resrule_std_mvs8,resrule_std_cnf8) = standardize_apart (resrule_sig,resrule_mvs,resrule_cnf8)

resrule_posclause8 :: Clause
resrule_posclause8 = resrule_std_cnf8 !! 0
resrule_negclause8 :: Clause
resrule_negclause8 = resrule_std_cnf8 !! 1

resrule_poslit8 :: Metaliteral
resrule_poslit8 = get_atom (resrule_posclause8 !! 0)
resrule_neglit8 :: Metaliteral
resrule_neglit8 = get_atom (resrule_negclause8 !! 0)

resrule_remposclause8 :: Clause
resrule_remposclause8 = resrule_posclause8 \\ [PosLit resrule_poslit8]
resrule_remnegclause8 :: Clause
resrule_remnegclause8 = resrule_negclause8 \\ [NegLit resrule_neglit8]

resrule_fs8 :: FullSolution
resrule_fs8 = (resrule_std_mvs8,[],(idinst,[]),(empty_graph,[],[]))

resrule_loginst8 :: LogicalInstantiation
resrule_loginst8 = idloginst

resrule_resolvent8 :: Clause
resrule_gencstr8 :: Constraint
(resrule_gencstr8,resrule_resolvent8) = apply_resolution_rule u0 resrule_poslit8 resrule_neglit8 resrule_remposclause8 resrule_remnegclause8

--resrule_std_sig6_2 :: ExtendedSignature
--resrule_std_mvs6_2 :: [Metavariable]
--resrule_std_resolvent6 :: Clause
--(resrule_std_sig6_2,resrule_std_mvs6_2,resrule_std_resolvent6) = standardize_new_clause (resrule_sig,resrule_mvs) (length resrule_std_cnf6) (resrule_std_sig6,resrule_std_mvs6,resrule_resolvent6)

resrule_rescnf8 :: CNF
resrule_rescnf8 = clean_deffo_cnf (append_clause resrule_std_cnf8 resrule_resolvent8)

resrule_parcresfs8 :: FullSolution
resrule_parcresfs8 = (mvs,mveqs,(inst,resrule_gencstr8:cs),(g,gsol,ueqs)) where (mvs,mveqs,(inst,cs),(g,gsol,ueqs)) = resrule_fs8

resrule_resfs8 :: FullSolution
resrule_resloginst8 :: LogicalInstantiation
resrule_canempty8 :: Bool
resrule_ifempty8 :: (FullSolution,LogicalInstantiation)
(resrule_ifempty8,resrule_canempty8) = (fromJust maybe,isJust maybe) where maybe = (force_empty_clause resrule_std_sig8 (resrule_parcresfs8,resrule_loginst8) u0 resrule_poslit8 resrule_neglit8 resrule_remposclause8 resrule_remnegclause8)
(resrule_resfs8,resrule_resloginst8) = resrule_ifempty8
resrule_emptycstrs8 :: [Constraint]
resrule_emptycstrs8 = cstrs where (_,_,(_,cstrs),_) = resrule_resfs8

resrule8_t1 = AT "Resolvent is [+u p(x,z),+u p(x',z')]." (resolvent_eq_test [read "+u0 p4[2](x0,x2)",PosLit (MLitR u0 (standardize_metaliteral resrule_nvars resrule_mvs 1 (read "p4[2](x0,x2)")))] resrule_resolvent8)
resrule8_t2 = AT "Generated constraint is up(x,y) = up(y',x')" (generated_cstr_test (Lcstr (read "u0 p4[2](x0,x1)") (MLitR u0 (standardize_metaliteral resrule_nvars resrule_mvs 1 (read "p4[2](x1,x0)")))) resrule_gencstr8)
resrule8_t3 = AT "Empty clause cannot be found" (empty_clause_possible_test False resrule_canempty8)
resrule8_t4 = AT "Resulting CNF is [[+p(x,y),+p(x,z)],[-p(y',x'),+p(x',z')],[+u p(x,z),+u p(x',z')]]" (resulting_cnf_test [read "[+p4[2](x0,x1),+p4[2](x0,x2)]",standardize_clause resrule_nvars resrule_mvs 1 (read "[-p4[2](x1,x0),+p4[2](x0,x2)]"),[PosLit (MLitR u0 (read "p4[2](x0,x2)")),PosLit (MLitR u0 (standardize_metaliteral resrule_nvars resrule_mvs 1 (read "p4[2](x0,x2)")))]] resrule_rescnf8)

resrule8_ts = [resrule8_t1,resrule8_t2,resrule8_t3,resrule8_t4]

resrule8_test = putStr (combine_test_results resrule8_ts)

-- Example 9

resrule_cnf9 :: CNF
resrule_cnf9 = read "[[+p1[0]()],[-X0]]"

resrule_std_sig9 :: ExtendedSignature
resrule_std_mvs9 :: [Metavariable]
resrule_std_cnf9 :: CNF
(resrule_std_sig9,resrule_std_mvs9,resrule_std_cnf9) = standardize_apart (resrule_sig,resrule_mvs,resrule_cnf9)

resrule_posclause9 :: Clause
resrule_posclause9 = resrule_std_cnf9 !! 0
resrule_negclause9 :: Clause
resrule_negclause9 = resrule_std_cnf9 !! 1

resrule_poslit9 :: Metaliteral
resrule_poslit9 = get_atom (resrule_posclause9 !! 0)
resrule_neglit9 :: Metaliteral
resrule_neglit9 = get_atom (resrule_negclause9 !! 0)

resrule_remposclause9 :: Clause
resrule_remposclause9 = resrule_posclause9 \\ [PosLit resrule_poslit9]
resrule_remnegclause9 :: Clause
resrule_remnegclause9 = resrule_negclause9 \\ [NegLit resrule_neglit9]

resrule_fs9 :: FullSolution
resrule_fs9 = (resrule_std_mvs9,[],(idinst,[]),(empty_graph,[],[]))

resrule_loginst9 :: LogicalInstantiation
resrule_loginst9 = idloginst

resrule_resolvent9 :: Clause
resrule_gencstr9 :: Constraint
(resrule_gencstr9,resrule_resolvent9) = apply_resolution_rule u0 resrule_poslit9 resrule_neglit9 resrule_remposclause9 resrule_remnegclause9

--resrule_std_sig6_2 :: ExtendedSignature
--resrule_std_mvs6_2 :: [Metavariable]
--resrule_std_resolvent6 :: Clause
--(resrule_std_sig6_2,resrule_std_mvs6_2,resrule_std_resolvent6) = standardize_new_clause (resrule_sig,resrule_mvs) (length resrule_std_cnf6) (resrule_std_sig6,resrule_std_mvs6,resrule_resolvent6)

resrule_rescnf9 :: CNF
resrule_rescnf9 = clean_deffo_cnf (append_clause resrule_std_cnf9 resrule_resolvent9)

resrule_parcresfs9 :: FullSolution
resrule_parcresfs9 = (mvs,mveqs,(inst,resrule_gencstr9:cs),(g,gsol,ueqs)) where (mvs,mveqs,(inst,cs),(g,gsol,ueqs)) = resrule_fs9

resrule_resfs9 :: FullSolution
resrule_resloginst9 :: LogicalInstantiation
resrule_canempty9 :: Bool
resrule_ifempty9 :: (FullSolution,LogicalInstantiation)
(resrule_ifempty9,resrule_canempty9) = (fromJust maybe,isJust maybe) where maybe = (force_empty_clause resrule_std_sig9 (resrule_parcresfs9,resrule_loginst9) u0 resrule_poslit9 resrule_neglit9 resrule_remposclause9 resrule_remnegclause9)
(resrule_resfs9,resrule_resloginst9) = resrule_ifempty9
resrule_emptycstrs9 :: [Constraint]
resrule_emptycstrs9 = cstrs where (_,_,(_,cstrs),_) = resrule_resfs9

resrule9_t1 = AT "Resolvent is the empty clause." (resolvent_eq_test [] resrule_resolvent9)
resrule9_t2 = AT "Generated constraint is up = uA" (generated_cstr_test (Lcstr (read "u0 p1[0]()") (MLitR u0 (standardize_metaliteral resrule_nvars resrule_mvs 1 (read "X0")))) resrule_gencstr9)
resrule9_t3 = AT "Empty clause can be found" (empty_clause_possible_test True resrule_canempty9)
resrule9_t4 = AT "Empty clause if up = uA" (empty_clause_cstrs_test [Lcstr (read "u0 p1[0]()") (MLitR u0 (standardize_metaliteral resrule_nvars resrule_mvs 1 (read "X0")))] resrule_canempty9 resrule_emptycstrs9)
resrule9_t5 = AT "Resulting CNF is [[+p],[-A],[]]" (resulting_cnf_test [read "[+p1[0]()]",[NegLit (standardize_metaliteral resrule_nvars resrule_mvs 1 (read "X0"))],[]] resrule_rescnf9)

resrule9_ts = [resrule9_t1,resrule9_t2,resrule9_t3,resrule9_t4,resrule9_t5]

resrule9_test = putStr (combine_test_results resrule9_ts)

-- Example 10

resrule_cnf10 :: CNF
resrule_cnf10 = read "[[+p1[0](),+p1[0]()],[-X0]]"

resrule_std_sig10 :: ExtendedSignature
resrule_std_mvs10 :: [Metavariable]
resrule_std_cnf10 :: CNF
(resrule_std_sig10,resrule_std_mvs10,resrule_std_cnf10) = standardize_apart (resrule_sig,resrule_mvs,resrule_cnf10)

resrule_posclause10 :: Clause
resrule_posclause10 = resrule_std_cnf10 !! 0
resrule_negclause10 :: Clause
resrule_negclause10 = resrule_std_cnf10 !! 1

resrule_poslit10 :: Metaliteral
resrule_poslit10 = get_atom (resrule_posclause10 !! 0)
resrule_neglit10 :: Metaliteral
resrule_neglit10 = get_atom (resrule_negclause10 !! 0)

resrule_remposclause10 :: Clause
resrule_remposclause10 = resrule_posclause10 \\ [PosLit resrule_poslit10]
resrule_remnegclause10 :: Clause
resrule_remnegclause10 = resrule_negclause10 \\ [NegLit resrule_neglit10]

resrule_fs10 :: FullSolution
resrule_fs10 = (resrule_std_mvs10,[],(idinst,[]),(empty_graph,[],[]))

resrule_loginst10 :: LogicalInstantiation
resrule_loginst10 = idloginst

resrule_resolvent10 :: Clause
resrule_gencstr10 :: Constraint
(resrule_gencstr10,resrule_resolvent10) = apply_resolution_rule u0 resrule_poslit10 resrule_neglit10 resrule_remposclause10 resrule_remnegclause10

--resrule_std_sig6_2 :: ExtendedSignature
--resrule_std_mvs6_2 :: [Metavariable]
--resrule_std_resolvent6 :: Clause
--(resrule_std_sig6_2,resrule_std_mvs6_2,resrule_std_resolvent6) = standardize_new_clause (resrule_sig,resrule_mvs) (length resrule_std_cnf6) (resrule_std_sig6,resrule_std_mvs6,resrule_resolvent6)

resrule_rescnf10 :: CNF
resrule_rescnf10 = clean_deffo_cnf (append_clause resrule_std_cnf10 resrule_resolvent10)

resrule_parcresfs10 :: FullSolution
resrule_parcresfs10 = (mvs,mveqs,(inst,resrule_gencstr10:cs),(g,gsol,ueqs)) where (mvs,mveqs,(inst,cs),(g,gsol,ueqs)) = resrule_fs10

resrule_resfs10 :: FullSolution
resrule_resloginst10 :: LogicalInstantiation
resrule_canempty10 :: Bool
resrule_ifempty10 :: (FullSolution,LogicalInstantiation)
(resrule_ifempty10,resrule_canempty10) = (fromJust maybe,isJust maybe) where maybe = (force_empty_clause resrule_std_sig10 (resrule_parcresfs10,resrule_loginst10) u0 resrule_poslit10 resrule_neglit10 resrule_remposclause10 resrule_remnegclause10)
(resrule_resfs10,resrule_resloginst10) = resrule_ifempty10
resrule_emptycstrs10 :: [Constraint]
resrule_emptycstrs10 = cstrs where (_,_,(_,cstrs),_) = resrule_resfs10

resrule10_t1 = AT "Resolvent is [+up]" (resolvent_eq_test (read "[+u0 p1[0]()]") resrule_resolvent10)
resrule10_t2 = AT "Generated constraint is up = uA" (generated_cstr_test (Lcstr (read "u0 p1[0]()") (MLitR u0 (standardize_metaliteral resrule_nvars resrule_mvs 1 (read "X0")))) resrule_gencstr10)
resrule10_t3 = AT "Empty clause can be found" (empty_clause_possible_test True resrule_canempty10)
resrule10_t4 = AT "Empty clause if up = uA, up = up" (empty_clause_cstrs_test [Lcstr (read "u0 p1[0]()") (MLitR u0 (standardize_metaliteral resrule_nvars resrule_mvs 1 (read "X0"))),Lcstr (read "u0 p1[0]()") (read "u0 p1[0]()")] resrule_canempty10 resrule_emptycstrs10)
resrule10_t5 = AT "Resulting CNF is [[+p,+p],[-A],[+up]]" (resulting_cnf_test [read "[+p1[0](),+p1[0]()]",[NegLit (standardize_metaliteral resrule_nvars resrule_mvs 1 (read "X0"))],read "[+u0 p1[0]()]"] resrule_rescnf10)

resrule10_ts = [resrule10_t1,resrule10_t2,resrule10_t3,resrule10_t4,resrule10_t5]

resrule10_test = putStr (combine_test_results resrule10_ts)

-- Example 11

resrule_cnf11 :: CNF
resrule_cnf11 = read "[[+p1[0](),+X0],[-p1[0]()]]"

resrule_std_sig11 :: ExtendedSignature
resrule_std_mvs11 :: [Metavariable]
resrule_std_cnf11 :: CNF
(resrule_std_sig11,resrule_std_mvs11,resrule_std_cnf11) = standardize_apart (resrule_sig,resrule_mvs,resrule_cnf11)

resrule_posclause11 :: Clause
resrule_posclause11 = resrule_std_cnf11 !! 0
resrule_negclause11 :: Clause
resrule_negclause11 = resrule_std_cnf11 !! 1

resrule_poslit11 :: Metaliteral
resrule_poslit11 = get_atom (resrule_posclause11 !! 0)
resrule_neglit11 :: Metaliteral
resrule_neglit11 = get_atom (resrule_negclause11 !! 0)

resrule_remposclause11 :: Clause
resrule_remposclause11 = resrule_posclause11 \\ [PosLit resrule_poslit11]
resrule_remnegclause11 :: Clause
resrule_remnegclause11 = resrule_negclause11 \\ [NegLit resrule_neglit11]

resrule_fs11 :: FullSolution
resrule_fs11 = (resrule_std_mvs11,[],(idinst,[]),(empty_graph,[],[]))

resrule_loginst11 :: LogicalInstantiation
resrule_loginst11 = idloginst

resrule_resolvent11 :: Clause
resrule_gencstr11 :: Constraint
(resrule_gencstr11,resrule_resolvent11) = apply_resolution_rule u0 resrule_poslit11 resrule_neglit11 resrule_remposclause11 resrule_remnegclause11

--resrule_std_sig6_2 :: ExtendedSignature
--resrule_std_mvs6_2 :: [Metavariable]
--resrule_std_resolvent6 :: Clause
--(resrule_std_sig6_2,resrule_std_mvs6_2,resrule_std_resolvent6) = standardize_new_clause (resrule_sig,resrule_mvs) (length resrule_std_cnf6) (resrule_std_sig6,resrule_std_mvs6,resrule_resolvent6)

resrule_rescnf11 :: CNF
resrule_rescnf11 = clean_deffo_cnf (append_clause resrule_std_cnf11 resrule_resolvent11)

resrule_parcresfs11 :: FullSolution
resrule_parcresfs11 = (mvs,mveqs,(inst,resrule_gencstr11:cs),(g,gsol,ueqs)) where (mvs,mveqs,(inst,cs),(g,gsol,ueqs)) = resrule_fs11

resrule_resfs11 :: FullSolution
resrule_resloginst11 :: LogicalInstantiation
resrule_canempty11 :: Bool
resrule_ifempty11 :: (FullSolution,LogicalInstantiation)
(resrule_ifempty11,resrule_canempty11) = (fromJust maybe,isJust maybe) where maybe = (force_empty_clause resrule_std_sig11 (resrule_parcresfs11,resrule_loginst11) u0 resrule_poslit11 resrule_neglit11 resrule_remposclause11 resrule_remnegclause11)
(resrule_resfs11,resrule_resloginst11) = resrule_ifempty11
resrule_emptycstrs11 :: [Constraint]
resrule_emptycstrs11 = cstrs where (_,_,(_,cstrs),_) = resrule_resfs11

resrule11_t1 = AT "Resolvent is [+uA]" (resolvent_eq_test (read "[+u0 X0]") resrule_resolvent11)
resrule11_t2 = AT "Generated constraint is up = up" (generated_cstr_test (Lcstr (read "u0 p1[0]()") (read "u0 p1[0]()")) resrule_gencstr11)
resrule11_t3 = AT "Empty clause can be found" (empty_clause_possible_test True resrule_canempty11)
resrule11_t4 = AT "Empty clause if up = up, up = uA" (empty_clause_cstrs_test [Lcstr (read "u0 p1[0]()") (read "u0 p1[0]()"), Lcstr (read "u0 p1[0]()") (read "u0 X0")] resrule_canempty11 resrule_emptycstrs11)
resrule11_t5 = AT "Resulting CNF is [[+p,+A],[-p],[+uA]]" (resulting_cnf_test [read "[+p1[0](),+X0]",read "[-p1[0]()]",read "[+u0 X0]"] resrule_rescnf11)

resrule11_ts = [resrule11_t1,resrule11_t2,resrule11_t3,resrule11_t4,resrule11_t5]

resrule11_test = putStr (combine_test_results resrule11_ts)

-- Example 12

resrule_cnf12 :: CNF
resrule_cnf12 = read "[[+p1[0](),-X0],[-p1[0]()]]"

resrule_std_sig12 :: ExtendedSignature
resrule_std_mvs12 :: [Metavariable]
resrule_std_cnf12 :: CNF
(resrule_std_sig12,resrule_std_mvs12,resrule_std_cnf12) = standardize_apart (resrule_sig,resrule_mvs,resrule_cnf12)

resrule_posclause12 :: Clause
resrule_posclause12 = resrule_std_cnf12 !! 0
resrule_negclause12 :: Clause
resrule_negclause12 = resrule_std_cnf12 !! 1

resrule_poslit12 :: Metaliteral
resrule_poslit12 = get_atom (resrule_posclause12 !! 0)
resrule_neglit12 :: Metaliteral
resrule_neglit12 = get_atom (resrule_negclause12 !! 0)

resrule_remposclause12 :: Clause
resrule_remposclause12 = resrule_posclause12 \\ [PosLit resrule_poslit12]
resrule_remnegclause12 :: Clause
resrule_remnegclause12 = resrule_negclause12 \\ [NegLit resrule_neglit12]

resrule_fs12 :: FullSolution
resrule_fs12 = (resrule_std_mvs12,[],(idinst,[]),(empty_graph,[],[]))

resrule_loginst12 :: LogicalInstantiation
resrule_loginst12 = idloginst

resrule_resolvent12 :: Clause
resrule_gencstr12 :: Constraint
(resrule_gencstr12,resrule_resolvent12) = apply_resolution_rule u0 resrule_poslit12 resrule_neglit12 resrule_remposclause12 resrule_remnegclause12

--resrule_std_sig6_2 :: ExtendedSignature
--resrule_std_mvs6_2 :: [Metavariable]
--resrule_std_resolvent6 :: Clause
--(resrule_std_sig6_2,resrule_std_mvs6_2,resrule_std_resolvent6) = standardize_new_clause (resrule_sig,resrule_mvs) (length resrule_std_cnf6) (resrule_std_sig6,resrule_std_mvs6,resrule_resolvent6)

resrule_rescnf12 :: CNF
resrule_rescnf12 = clean_deffo_cnf (append_clause resrule_std_cnf12 resrule_resolvent12)

resrule_parcresfs12 :: FullSolution
resrule_parcresfs12 = (mvs,mveqs,(inst,resrule_gencstr12:cs),(g,gsol,ueqs)) where (mvs,mveqs,(inst,cs),(g,gsol,ueqs)) = resrule_fs12

resrule_resfs12 :: FullSolution
resrule_resloginst12 :: LogicalInstantiation
resrule_canempty12 :: Bool
resrule_ifempty12 :: (FullSolution,LogicalInstantiation)
(resrule_ifempty12,resrule_canempty12) = (fromJust maybe,isJust maybe) where maybe = (force_empty_clause resrule_std_sig12 (resrule_parcresfs12,resrule_loginst12) u0 resrule_poslit12 resrule_neglit12 resrule_remposclause12 resrule_remnegclause12)
(resrule_resfs12,resrule_resloginst12) = resrule_ifempty12
resrule_emptycstrs12 :: [Constraint]
resrule_emptycstrs12 = cstrs where (_,_,(_,cstrs),_) = resrule_resfs12

resrule12_t1 = AT "Resolvent is [-uA]" (resolvent_eq_test (read "[-u0 X0]") resrule_resolvent12)
resrule12_t2 = AT "Generated constraint is up = up" (generated_cstr_test (Lcstr (read "u0 p1[0]()") (read "u0 p1[0]()")) resrule_gencstr12)
resrule12_t3 = AT "Empty clause can be found" (empty_clause_possible_test True resrule_canempty12)
resrule12_t4 = AT "Empty clause if up = up, up = uC" (empty_clause_cstrs_test [Lcstr (read "u0 p1[0]()") (read "u0 p1[0]()"), Lcstr (read "u0 p1[0]()") (read "u0 X6")] resrule_canempty12 resrule_emptycstrs12)
resrule12_t5 = AT "Resulting CNF is [[+p,-A],[-p],[-uA]]" (resulting_cnf_test [read "[+p1[0](),-X0]",read "[-p1[0]()]",read "[-u0 X0]"] resrule_rescnf12)

resrule12_ts = [resrule12_t1,resrule12_t2,resrule12_t3,resrule12_t4,resrule12_t5]

resrule12_test = putStr (combine_test_results resrule12_ts)

-- Example 13

resrule_cnf13 :: CNF
resrule_cnf13 = read "[[+p1[0](),-X0],[-p1[0](),+p1[0]()]]"

resrule_std_sig13 :: ExtendedSignature
resrule_std_mvs13 :: [Metavariable]
resrule_std_cnf13 :: CNF
(resrule_std_sig13,resrule_std_mvs13,resrule_std_cnf13) = standardize_apart (resrule_sig,resrule_mvs,resrule_cnf13)

resrule_posclause13 :: Clause
resrule_posclause13 = resrule_std_cnf13 !! 0
resrule_negclause13 :: Clause
resrule_negclause13 = resrule_std_cnf13 !! 1

resrule_poslit13 :: Metaliteral
resrule_poslit13 = get_atom (resrule_posclause13 !! 0)
resrule_neglit13 :: Metaliteral
resrule_neglit13 = get_atom (resrule_negclause13 !! 0)

resrule_remposclause13 :: Clause
resrule_remposclause13 = resrule_posclause13 \\ [PosLit resrule_poslit13]
resrule_remnegclause13 :: Clause
resrule_remnegclause13 = resrule_negclause13 \\ [NegLit resrule_neglit13]

resrule_fs13 :: FullSolution
resrule_fs13 = (resrule_std_mvs13,[],(idinst,[]),(empty_graph,[],[]))

resrule_loginst13 :: LogicalInstantiation
resrule_loginst13 = idloginst

resrule_resolvent13 :: Clause
resrule_gencstr13 :: Constraint
(resrule_gencstr13,resrule_resolvent13) = apply_resolution_rule u0 resrule_poslit13 resrule_neglit13 resrule_remposclause13 resrule_remnegclause13

--resrule_std_sig6_2 :: ExtendedSignature
--resrule_std_mvs6_2 :: [Metavariable]
--resrule_std_resolvent6 :: Clause
--(resrule_std_sig6_2,resrule_std_mvs6_2,resrule_std_resolvent6) = standardize_new_clause (resrule_sig,resrule_mvs) (length resrule_std_cnf6) (resrule_std_sig6,resrule_std_mvs6,resrule_resolvent6)

resrule_rescnf13 :: CNF
resrule_rescnf13 = clean_deffo_cnf (append_clause resrule_std_cnf13 resrule_resolvent13)

resrule_parcresfs13 :: FullSolution
resrule_parcresfs13 = (mvs,mveqs,(inst,resrule_gencstr13:cs),(g,gsol,ueqs)) where (mvs,mveqs,(inst,cs),(g,gsol,ueqs)) = resrule_fs13

resrule_resfs13 :: FullSolution
resrule_resloginst13 :: LogicalInstantiation
resrule_canempty13 :: Bool
resrule_ifempty13 :: (FullSolution,LogicalInstantiation)
(resrule_ifempty13,resrule_canempty13) = (fromJust maybe,isJust maybe) where maybe = (force_empty_clause resrule_std_sig13 (resrule_parcresfs13,resrule_loginst13) u0 resrule_poslit13 resrule_neglit13 resrule_remposclause13 resrule_remnegclause13)
(resrule_resfs13,resrule_resloginst13) = resrule_ifempty13
resrule_emptycstrs13 :: [Constraint]
resrule_emptycstrs13 = cstrs where (_,_,(_,cstrs),_) = resrule_resfs13

resrule13_t1 = AT "Resolvent is [-uA,+up]" (resolvent_eq_test (read "[-u0 X0,+u0 p1[0]()]") resrule_resolvent13)
resrule13_t2 = AT "Generated constraint is up = up" (generated_cstr_test (Lcstr (read "u0 p1[0]()") (read "u0 p1[0]()")) resrule_gencstr13)
resrule13_t3 = AT "Empty clause cannot be found" (empty_clause_possible_test False resrule_canempty13)
resrule13_t4 = AT "Resulting CNF is [[+p,-A],[-uA,+up]]" (resulting_cnf_test [read "[+p1[0](),-X0]",read "[-u0 X0,+u0 p1[0]()]"] resrule_rescnf13)

resrule13_ts = [resrule13_t1,resrule13_t2,resrule13_t3,resrule13_t4]

resrule13_test = putStr (combine_test_results resrule13_ts)

-- Example 14

resrule_cnf14 :: CNF
resrule_cnf14 = read "[[+p1[0](),-X0],[-p1[0](),-p2[0]()]]"

resrule_std_sig14 :: ExtendedSignature
resrule_std_mvs14 :: [Metavariable]
resrule_std_cnf14 :: CNF
(resrule_std_sig14,resrule_std_mvs14,resrule_std_cnf14) = standardize_apart (resrule_sig,resrule_mvs,resrule_cnf14)

resrule_posclause14 :: Clause
resrule_posclause14 = resrule_std_cnf14 !! 0
resrule_negclause14 :: Clause
resrule_negclause14 = resrule_std_cnf14 !! 1

resrule_poslit14 :: Metaliteral
resrule_poslit14 = get_atom (resrule_posclause14 !! 0)
resrule_neglit14 :: Metaliteral
resrule_neglit14 = get_atom (resrule_negclause14 !! 0)

resrule_remposclause14 :: Clause
resrule_remposclause14 = resrule_posclause14 \\ [PosLit resrule_poslit14]
resrule_remnegclause14 :: Clause
resrule_remnegclause14 = resrule_negclause14 \\ [NegLit resrule_neglit14]

resrule_fs14 :: FullSolution
resrule_fs14 = (resrule_std_mvs14,[],(idinst,[]),(empty_graph,[],[]))

resrule_loginst14 :: LogicalInstantiation
resrule_loginst14 = idloginst

resrule_resolvent14 :: Clause
resrule_gencstr14 :: Constraint
(resrule_gencstr14,resrule_resolvent14) = apply_resolution_rule u0 resrule_poslit14 resrule_neglit14 resrule_remposclause14 resrule_remnegclause14

--resrule_std_sig6_2 :: ExtendedSignature
--resrule_std_mvs6_2 :: [Metavariable]
--resrule_std_resolvent6 :: Clause
--(resrule_std_sig6_2,resrule_std_mvs6_2,resrule_std_resolvent6) = standardize_new_clause (resrule_sig,resrule_mvs) (length resrule_std_cnf6) (resrule_std_sig6,resrule_std_mvs6,resrule_resolvent6)

resrule_rescnf14 :: CNF
resrule_rescnf14 = clean_deffo_cnf (append_clause resrule_std_cnf14 resrule_resolvent14)

resrule_parcresfs14 :: FullSolution
resrule_parcresfs14 = (mvs,mveqs,(inst,resrule_gencstr14:cs),(g,gsol,ueqs)) where (mvs,mveqs,(inst,cs),(g,gsol,ueqs)) = resrule_fs14

resrule_resfs14 :: FullSolution
resrule_resloginst14 :: LogicalInstantiation
resrule_canempty14 :: Bool
resrule_ifempty14 :: (FullSolution,LogicalInstantiation)
(resrule_ifempty14,resrule_canempty14) = (fromJust maybe,isJust maybe) where maybe = (force_empty_clause resrule_std_sig14 (resrule_parcresfs14,resrule_loginst14) u0 resrule_poslit14 resrule_neglit14 resrule_remposclause14 resrule_remnegclause14)
(resrule_resfs14,resrule_resloginst14) = resrule_ifempty14
resrule_emptycstrs14 :: [Constraint]
resrule_emptycstrs14 = cstrs where (_,_,(_,cstrs),_) = resrule_resfs14

resrule14_t1 = AT "Resolvent is [-uA,-uq]" (resolvent_eq_test (read "[-u0 X0,-u0 p2[0]()]") resrule_resolvent14)
resrule14_t2 = AT "Generated constraint is up = up" (generated_cstr_test (Lcstr (read "u0 p1[0]()") (read "u0 p1[0]()")) resrule_gencstr14)
resrule14_t3 = AT "Empty clause cannot be found" (empty_clause_possible_test False resrule_canempty14)
resrule14_t4 = AT "Resulting CNF is [[+p,-A],[-p,-q],[-uA,-uq]]" (resulting_cnf_test [read "[+p1[0](),-X0]",read "[-p1[0](),-p2[0]()]",read "[-u0 X0,-u0 p2[0]()]"] resrule_rescnf14)

resrule14_ts = [resrule14_t1,resrule14_t2,resrule14_t3,resrule14_t4]

resrule14_test = putStr (combine_test_results resrule14_ts)	

-- Example 15

resrule_cnf15 :: CNF
resrule_cnf15 = read "[[+p1[0](),-X0],[-p1[0](),-X0]]"

resrule_std_sig15 :: ExtendedSignature
resrule_std_mvs15 :: [Metavariable]
resrule_std_cnf15 :: CNF
(resrule_std_sig15,resrule_std_mvs15,resrule_std_cnf15) = standardize_apart (resrule_sig,resrule_mvs,resrule_cnf15)

resrule_posclause15 :: Clause
resrule_posclause15 = resrule_std_cnf15 !! 0
resrule_negclause15 :: Clause
resrule_negclause15 = resrule_std_cnf15 !! 1

resrule_poslit15 :: Metaliteral
resrule_poslit15 = get_atom (resrule_posclause15 !! 0)
resrule_neglit15 :: Metaliteral
resrule_neglit15 = get_atom (resrule_negclause15 !! 0)

resrule_remposclause15 :: Clause
resrule_remposclause15 = resrule_posclause15 \\ [PosLit resrule_poslit15]
resrule_remnegclause15 :: Clause
resrule_remnegclause15 = resrule_negclause15 \\ [NegLit resrule_neglit15]

resrule_fs15 :: FullSolution
resrule_fs15 = (resrule_std_mvs15,[],(idinst,[]),(empty_graph,[],[]))

resrule_loginst15 :: LogicalInstantiation
resrule_loginst15 = idloginst

resrule_resolvent15 :: Clause
resrule_gencstr15 :: Constraint
(resrule_gencstr15,resrule_resolvent15) = apply_resolution_rule u0 resrule_poslit15 resrule_neglit15 resrule_remposclause15 resrule_remnegclause15

--resrule_std_sig6_2 :: ExtendedSignature
--resrule_std_mvs6_2 :: [Metavariable]
--resrule_std_resolvent6 :: Clause
--(resrule_std_sig6_2,resrule_std_mvs6_2,resrule_std_resolvent6) = standardize_new_clause (resrule_sig,resrule_mvs) (length resrule_std_cnf6) (resrule_std_sig6,resrule_std_mvs6,resrule_resolvent6)

resrule_rescnf15 :: CNF
resrule_rescnf15 = clean_deffo_cnf (append_clause resrule_std_cnf15 resrule_resolvent15)

resrule_parcresfs15 :: FullSolution
resrule_parcresfs15 = (mvs,mveqs,(inst,resrule_gencstr15:cs),(g,gsol,ueqs)) where (mvs,mveqs,(inst,cs),(g,gsol,ueqs)) = resrule_fs15

resrule_resfs15 :: FullSolution
resrule_resloginst15 :: LogicalInstantiation
resrule_canempty15 :: Bool
resrule_ifempty15 :: (FullSolution,LogicalInstantiation)
(resrule_ifempty15,resrule_canempty15) = (fromJust maybe,isJust maybe) where maybe = (force_empty_clause resrule_std_sig15 (resrule_parcresfs15,resrule_loginst15) u0 resrule_poslit15 resrule_neglit15 resrule_remposclause15 resrule_remnegclause15)
(resrule_resfs15,resrule_resloginst15) = resrule_ifempty15
resrule_emptycstrs15 :: [Constraint]
resrule_emptycstrs15 = cstrs where (_,_,(_,cstrs),_) = resrule_resfs15

resrule15_t1 = AT "Resolvent is [-uA,-uA']" (resolvent_eq_test [(read "-u0 X0"),NegLit (MLitR u0 (standardize_metaliteral resrule_nvars resrule_mvs 1 (read "X0")))] resrule_resolvent15)
resrule15_t2 = AT "Generated constraint is up = up" (generated_cstr_test (Lcstr (read "u0 p1[0]()") (read "u0 p1[0]()")) resrule_gencstr15)
resrule15_t3 = AT "Empty clause cannot be found" (empty_clause_possible_test False resrule_canempty15)
resrule15_t4 = AT "Resulting CNF is [[+p,-A],[-p,-A],[-uA,-uA']]" (resulting_cnf_test [read "[+p1[0](),-X0]",[read "-p1[0]()",NegLit (standardize_metaliteral resrule_nvars resrule_mvs 1 (read "X0"))],[read "-u0 X0",NegLit (MLitR u0 (standardize_metaliteral resrule_nvars resrule_mvs 1 (read "X0")))]] resrule_rescnf15)

resrule15_ts = [resrule15_t1,resrule15_t2,resrule15_t3,resrule15_t4]

resrule15_test = putStr (combine_test_results resrule15_ts)

-- Example 16

resrule_cnf16 :: CNF
resrule_cnf16 = read "[[+X0,+p1[0]()],[-p1[0]()]]"

resrule_std_sig16 :: ExtendedSignature
resrule_std_mvs16 :: [Metavariable]
resrule_std_cnf16 :: CNF
(resrule_std_sig16,resrule_std_mvs16,resrule_std_cnf16) = standardize_apart (resrule_sig,resrule_mvs,resrule_cnf16)

resrule_posclause16 :: Clause
resrule_posclause16 = resrule_std_cnf16 !! 0
resrule_negclause16 :: Clause
resrule_negclause16 = resrule_std_cnf16 !! 1

resrule_poslit16 :: Metaliteral
resrule_poslit16 = get_atom (resrule_posclause16 !! 0)
resrule_neglit16 :: Metaliteral
resrule_neglit16 = get_atom (resrule_negclause16 !! 0)

resrule_remposclause16 :: Clause
resrule_remposclause16 = resrule_posclause16 \\ [PosLit resrule_poslit16]
resrule_remnegclause16 :: Clause
resrule_remnegclause16 = resrule_negclause16 \\ [NegLit resrule_neglit16]

resrule_fs16 :: FullSolution
resrule_fs16 = (resrule_std_mvs16,[],(idinst,[]),(empty_graph,[],[]))

resrule_loginst16 :: LogicalInstantiation
resrule_loginst16 = idloginst

resrule_resolvent16 :: Clause
resrule_gencstr16 :: Constraint
(resrule_gencstr16,resrule_resolvent16) = apply_resolution_rule u0 resrule_poslit16 resrule_neglit16 resrule_remposclause16 resrule_remnegclause16

--resrule_std_sig6_2 :: ExtendedSignature
--resrule_std_mvs6_2 :: [Metavariable]
--resrule_std_resolvent6 :: Clause
--(resrule_std_sig6_2,resrule_std_mvs6_2,resrule_std_resolvent6) = standardize_new_clause (resrule_sig,resrule_mvs) (length resrule_std_cnf6) (resrule_std_sig6,resrule_std_mvs6,resrule_resolvent6)

resrule_rescnf16 :: CNF
resrule_rescnf16 = clean_deffo_cnf (append_clause resrule_std_cnf16 resrule_resolvent16)

resrule_parcresfs16 :: FullSolution
resrule_parcresfs16 = (mvs,mveqs,(inst,resrule_gencstr16:cs),(g,gsol,ueqs)) where (mvs,mveqs,(inst,cs),(g,gsol,ueqs)) = resrule_fs16

resrule_resfs16 :: FullSolution
resrule_resloginst16 :: LogicalInstantiation
resrule_canempty16 :: Bool
resrule_ifempty16 :: (FullSolution,LogicalInstantiation)
(resrule_ifempty16,resrule_canempty16) = (fromJust maybe,isJust maybe) where maybe = (force_empty_clause resrule_std_sig16 (resrule_parcresfs16,resrule_loginst16) u0 resrule_poslit16 resrule_neglit16 resrule_remposclause16 resrule_remnegclause16)
(resrule_resfs16,resrule_resloginst16) = resrule_ifempty16
resrule_emptycstrs16 :: [Constraint]
resrule_emptycstrs16 = cstrs where (_,_,(_,cstrs),_) = resrule_resfs16

resrule16_t1 = AT "Resolvent is [+up]" (resolvent_eq_test (read "[+u0 p1[0]()]") resrule_resolvent16)
resrule16_t2 = AT "Generated constraint is uA = up" (generated_cstr_test (Lcstr (read "u0 X0") (read "u0 p1[0]()")) resrule_gencstr16)
resrule16_t3 = AT "Empty clause can be found" (empty_clause_possible_test True resrule_canempty16)
resrule16_t4 = AT "Empty clause if uA = up, uA = up" (empty_clause_cstrs_test [Lcstr (read "u0 X0") (read "u0 p1[0]()"), Lcstr (read "u0 X0") (read "u0 p1[0]()")] resrule_canempty16 resrule_emptycstrs16)
resrule16_t5 = AT "Resulting CNF is [[+A,+p],[-p],[+up]]" (resulting_cnf_test [read "[+X0,+p1[0]()]",read "[-p1[0]()]",read "[+u0 p1[0]()]"] resrule_rescnf16)

resrule16_ts = [resrule16_t1,resrule16_t2,resrule16_t3,resrule16_t4,resrule16_t5]

resrule16_test = putStr (combine_test_results resrule16_ts)

-- Example 17

resrule_cnf17 :: CNF
resrule_cnf17 = read "[[+X0,-p1[0]()],[-p1[0]()]]"

resrule_std_sig17 :: ExtendedSignature
resrule_std_mvs17 :: [Metavariable]
resrule_std_cnf17 :: CNF
(resrule_std_sig17,resrule_std_mvs17,resrule_std_cnf17) = standardize_apart (resrule_sig,resrule_mvs,resrule_cnf17)

resrule_posclause17 :: Clause
resrule_posclause17 = resrule_std_cnf17 !! 0
resrule_negclause17 :: Clause
resrule_negclause17 = resrule_std_cnf17 !! 1

resrule_poslit17 :: Metaliteral
resrule_poslit17 = get_atom (resrule_posclause17 !! 0)
resrule_neglit17 :: Metaliteral
resrule_neglit17 = get_atom (resrule_negclause17 !! 0)

resrule_remposclause17 :: Clause
resrule_remposclause17 = resrule_posclause17 \\ [PosLit resrule_poslit17]
resrule_remnegclause17 :: Clause
resrule_remnegclause17 = resrule_negclause17 \\ [NegLit resrule_neglit17]

resrule_fs17 :: FullSolution
resrule_fs17 = (resrule_std_mvs17,[],(idinst,[]),(empty_graph,[],[]))

resrule_loginst17 :: LogicalInstantiation
resrule_loginst17 = idloginst

resrule_resolvent17 :: Clause
resrule_gencstr17 :: Constraint
(resrule_gencstr17,resrule_resolvent17) = apply_resolution_rule u0 resrule_poslit17 resrule_neglit17 resrule_remposclause17 resrule_remnegclause17

--resrule_std_sig6_2 :: ExtendedSignature
--resrule_std_mvs6_2 :: [Metavariable]
--resrule_std_resolvent6 :: Clause
--(resrule_std_sig6_2,resrule_std_mvs6_2,resrule_std_resolvent6) = standardize_new_clause (resrule_sig,resrule_mvs) (length resrule_std_cnf6) (resrule_std_sig6,resrule_std_mvs6,resrule_resolvent6)

resrule_rescnf17 :: CNF
resrule_rescnf17 = clean_deffo_cnf (append_clause resrule_std_cnf17 resrule_resolvent17)

resrule_parcresfs17 :: FullSolution
resrule_parcresfs17 = (mvs,mveqs,(inst,resrule_gencstr17:cs),(g,gsol,ueqs)) where (mvs,mveqs,(inst,cs),(g,gsol,ueqs)) = resrule_fs17

resrule_resfs17 :: FullSolution
resrule_resloginst17 :: LogicalInstantiation
resrule_canempty17 :: Bool
resrule_ifempty17 :: (FullSolution,LogicalInstantiation)
(resrule_ifempty17,resrule_canempty17) = (fromJust maybe,isJust maybe) where maybe = (force_empty_clause resrule_std_sig17 (resrule_parcresfs17,resrule_loginst17) u0 resrule_poslit17 resrule_neglit17 resrule_remposclause17 resrule_remnegclause17)
(resrule_resfs17,resrule_resloginst17) = resrule_ifempty17
resrule_emptycstrs17 :: [Constraint]
resrule_emptycstrs17 = cstrs where (_,_,(_,cstrs),_) = resrule_resfs17

resrule17_t1 = AT "Resolvent is [-up]" (resolvent_eq_test (read "[-u0 p1[0]()]") resrule_resolvent17)
resrule17_t2 = AT "Generated constraint is uA = up" (generated_cstr_test (Lcstr (read "u0 X0") (read "u0 p1[0]()")) resrule_gencstr17)
resrule17_t3 = AT "Empty clause cannot be found" (empty_clause_possible_test False resrule_canempty17)
resrule17_t4 = AT "Resulting CNF is [[+A,-p],[-p],[-up]]" (resulting_cnf_test [read "[+X0,-p1[0]()]",read "[-p1[0]()]",read "[-u0 p1[0]()]"] resrule_rescnf17)

resrule17_ts = [resrule17_t1,resrule17_t2,resrule17_t3,resrule17_t4]

resrule17_test = putStr (combine_test_results resrule17_ts)

-- Example 18

resrule_cnf18 :: CNF
resrule_cnf18 = read "[[+X0,+X1],[-p1[0]()]]"

resrule_std_sig18 :: ExtendedSignature
resrule_std_mvs18 :: [Metavariable]
resrule_std_cnf18 :: CNF
(resrule_std_sig18,resrule_std_mvs18,resrule_std_cnf18) = standardize_apart (resrule_sig,resrule_mvs,resrule_cnf18)

resrule_posclause18 :: Clause
resrule_posclause18 = resrule_std_cnf18 !! 0
resrule_negclause18 :: Clause
resrule_negclause18 = resrule_std_cnf18 !! 1

resrule_poslit18 :: Metaliteral
resrule_poslit18 = get_atom (resrule_posclause18 !! 0)
resrule_neglit18 :: Metaliteral
resrule_neglit18 = get_atom (resrule_negclause18 !! 0)

resrule_remposclause18 :: Clause
resrule_remposclause18 = resrule_posclause18 \\ [PosLit resrule_poslit18]
resrule_remnegclause18 :: Clause
resrule_remnegclause18 = resrule_negclause18 \\ [NegLit resrule_neglit18]

resrule_fs18 :: FullSolution
resrule_fs18 = (resrule_std_mvs18,[],(idinst,[]),(empty_graph,[],[]))

resrule_loginst18 :: LogicalInstantiation
resrule_loginst18 = idloginst

resrule_resolvent18 :: Clause
resrule_gencstr18 :: Constraint
(resrule_gencstr18,resrule_resolvent18) = apply_resolution_rule u0 resrule_poslit18 resrule_neglit18 resrule_remposclause18 resrule_remnegclause18

--resrule_std_sig6_2 :: ExtendedSignature
--resrule_std_mvs6_2 :: [Metavariable]
--resrule_std_resolvent6 :: Clause
--(resrule_std_sig6_2,resrule_std_mvs6_2,resrule_std_resolvent6) = standardize_new_clause (resrule_sig,resrule_mvs) (length resrule_std_cnf6) (resrule_std_sig6,resrule_std_mvs6,resrule_resolvent6)

resrule_rescnf18 :: CNF
resrule_rescnf18 = clean_deffo_cnf (append_clause resrule_std_cnf18 resrule_resolvent18)

resrule_parcresfs18 :: FullSolution
resrule_parcresfs18 = (mvs,mveqs,(inst,resrule_gencstr18:cs),(g,gsol,ueqs)) where (mvs,mveqs,(inst,cs),(g,gsol,ueqs)) = resrule_fs18

resrule_resfs18 :: FullSolution
resrule_resloginst18 :: LogicalInstantiation
resrule_canempty18 :: Bool
resrule_ifempty18 :: (FullSolution,LogicalInstantiation)
(resrule_ifempty18,resrule_canempty18) = (fromJust maybe,isJust maybe) where maybe = (force_empty_clause resrule_std_sig18 (resrule_parcresfs18,resrule_loginst18) u0 resrule_poslit18 resrule_neglit18 resrule_remposclause18 resrule_remnegclause18)
(resrule_resfs18,resrule_resloginst18) = resrule_ifempty18
resrule_emptycstrs18 :: [Constraint]
resrule_emptycstrs18 = cstrs where (_,_,(_,cstrs),_) = resrule_resfs18

resrule18_t1 = AT "Resolvent is [+uB]" (resolvent_eq_test (read "[+u0 X1]") resrule_resolvent18)
resrule18_t2 = AT "Generated constraint is uA = up" (generated_cstr_test (Lcstr (read "u0 X0") (read "u0 p1[0]()")) resrule_gencstr18)
resrule18_t3 = AT "Empty clause can be found" (empty_clause_possible_test True resrule_canempty18)
resrule18_t4 = AT "Empty clause if uA = up, uA = uB" (empty_clause_cstrs_test [Lcstr (read "u0 X0") (read "u0 p1[0]()"), Lcstr (read "u0 X0") (read "u0 X1")] resrule_canempty18 resrule_emptycstrs18)
resrule18_t5 = AT "Resulting CNF is [[+A,+B],[-p],[+uB]]" (resulting_cnf_test [read "[+X0,+X1]",read "[-p1[0]()]",read "[+u0 X1]"] resrule_rescnf18)

resrule18_ts = [resrule18_t1,resrule18_t2,resrule18_t3,resrule18_t4,resrule18_t5]

resrule18_test = putStr (combine_test_results resrule18_ts)

-- Example 19

resrule_cnf19 :: CNF
resrule_cnf19 = read "[[+X0,-X1],[-p1[0]()]]"

resrule_std_sig19 :: ExtendedSignature
resrule_std_mvs19 :: [Metavariable]
resrule_std_cnf19 :: CNF
(resrule_std_sig19,resrule_std_mvs19,resrule_std_cnf19) = standardize_apart (resrule_sig,resrule_mvs,resrule_cnf19)

resrule_posclause19 :: Clause
resrule_posclause19 = resrule_std_cnf19 !! 0
resrule_negclause19 :: Clause
resrule_negclause19 = resrule_std_cnf19 !! 1

resrule_poslit19 :: Metaliteral
resrule_poslit19 = get_atom (resrule_posclause19 !! 0)
resrule_neglit19 :: Metaliteral
resrule_neglit19 = get_atom (resrule_negclause19 !! 0)

resrule_remposclause19 :: Clause
resrule_remposclause19 = resrule_posclause19 \\ [PosLit resrule_poslit19]
resrule_remnegclause19 :: Clause
resrule_remnegclause19 = resrule_negclause19 \\ [NegLit resrule_neglit19]

resrule_fs19 :: FullSolution
resrule_fs19 = (resrule_std_mvs19,[],(idinst,[]),(empty_graph,[],[]))

resrule_loginst19 :: LogicalInstantiation
resrule_loginst19 = idloginst

resrule_resolvent19 :: Clause
resrule_gencstr19 :: Constraint
(resrule_gencstr19,resrule_resolvent19) = apply_resolution_rule u0 resrule_poslit19 resrule_neglit19 resrule_remposclause19 resrule_remnegclause19

--resrule_std_sig6_2 :: ExtendedSignature
--resrule_std_mvs6_2 :: [Metavariable]
--resrule_std_resolvent6 :: Clause
--(resrule_std_sig6_2,resrule_std_mvs6_2,resrule_std_resolvent6) = standardize_new_clause (resrule_sig,resrule_mvs) (length resrule_std_cnf6) (resrule_std_sig6,resrule_std_mvs6,resrule_resolvent6)

resrule_rescnf19 :: CNF
resrule_rescnf19 = clean_deffo_cnf (append_clause resrule_std_cnf19 resrule_resolvent19)

resrule_parcresfs19 :: FullSolution
resrule_parcresfs19 = (mvs,mveqs,(inst,resrule_gencstr19:cs),(g,gsol,ueqs)) where (mvs,mveqs,(inst,cs),(g,gsol,ueqs)) = resrule_fs19

resrule_resfs19 :: FullSolution
resrule_resloginst19 :: LogicalInstantiation
resrule_canempty19 :: Bool
resrule_ifempty19 :: (FullSolution,LogicalInstantiation)
(resrule_ifempty19,resrule_canempty19) = (fromJust maybe,isJust maybe) where maybe = (force_empty_clause resrule_std_sig19 (resrule_parcresfs19,resrule_loginst19) u0 resrule_poslit19 resrule_neglit19 resrule_remposclause19 resrule_remnegclause19)
(resrule_resfs19,resrule_resloginst19) = resrule_ifempty19
resrule_emptycstrs19 :: [Constraint]
resrule_emptycstrs19 = cstrs where (_,_,(_,cstrs),_) = resrule_resfs19

resrule19_t1 = AT "Resolvent is [-uB]" (resolvent_eq_test (read "[-u0 X1]") resrule_resolvent19)
resrule19_t2 = AT "Generated constraint is uA = up" (generated_cstr_test (Lcstr (read "u0 X0") (read "u0 p1[0]()")) resrule_gencstr19)
resrule19_t3 = AT "Empty clause can be found" (empty_clause_possible_test True resrule_canempty19)
resrule19_t4 = AT "Empty clause if uA = up, uA = uC" (empty_clause_cstrs_test [Lcstr (read "u0 X0") (read "u0 p1[0]()"), Lcstr (read "u0 X0") (read "u0 X6")] resrule_canempty19 resrule_emptycstrs19)
resrule19_t5 = AT "Resulting CNF is [[+A,-B],[-p],[-uB]]" (resulting_cnf_test [read "[+X0,-X1]",read "[-p1[0]()]",read "[-u0 X1]"] resrule_rescnf19)

resrule19_ts = [resrule19_t1,resrule19_t2,resrule19_t3,resrule19_t4,resrule19_t5]

resrule19_test = putStr (combine_test_results resrule19_ts)

-- Example 20

resrule_cnf20 :: CNF
resrule_cnf20 = read "[[+X0,-X0],[-p1[0]()]]"

resrule_std_sig20 :: ExtendedSignature
resrule_std_mvs20 :: [Metavariable]
resrule_std_cnf20 :: CNF
(resrule_std_sig20,resrule_std_mvs20,resrule_std_cnf20) = standardize_apart (resrule_sig,resrule_mvs,resrule_cnf20)

resrule_posclause20 :: Clause
resrule_posclause20 = resrule_std_cnf20 !! 0
resrule_negclause20 :: Clause
resrule_negclause20 = resrule_std_cnf20 !! 1

resrule_poslit20 :: Metaliteral
resrule_poslit20 = get_atom (resrule_posclause20 !! 0)
resrule_neglit20 :: Metaliteral
resrule_neglit20 = get_atom (resrule_negclause20 !! 0)

resrule_remposclause20 :: Clause
resrule_remposclause20 = resrule_posclause20 \\ [PosLit resrule_poslit20]
resrule_remnegclause20 :: Clause
resrule_remnegclause20 = resrule_negclause20 \\ [NegLit resrule_neglit20]

resrule_fs20 :: FullSolution
resrule_fs20 = (resrule_std_mvs20,[],(idinst,[]),(empty_graph,[],[]))

resrule_loginst20 :: LogicalInstantiation
resrule_loginst20 = idloginst

resrule_resolvent20 :: Clause
resrule_gencstr20 :: Constraint
(resrule_gencstr20,resrule_resolvent20) = apply_resolution_rule u0 resrule_poslit20 resrule_neglit20 resrule_remposclause20 resrule_remnegclause20

--resrule_std_sig6_2 :: ExtendedSignature
--resrule_std_mvs6_2 :: [Metavariable]
--resrule_std_resolvent6 :: Clause
--(resrule_std_sig6_2,resrule_std_mvs6_2,resrule_std_resolvent6) = standardize_new_clause (resrule_sig,resrule_mvs) (length resrule_std_cnf6) (resrule_std_sig6,resrule_std_mvs6,resrule_resolvent6)

resrule_rescnf20 :: CNF
resrule_rescnf20 = clean_deffo_cnf (append_clause resrule_std_cnf20 resrule_resolvent20)

resrule_parcresfs20 :: FullSolution
resrule_parcresfs20 = (mvs,mveqs,(inst,resrule_gencstr20:cs),(g,gsol,ueqs)) where (mvs,mveqs,(inst,cs),(g,gsol,ueqs)) = resrule_fs20

resrule_resfs20 :: FullSolution
resrule_resloginst20 :: LogicalInstantiation
resrule_canempty20 :: Bool
resrule_ifempty20 :: (FullSolution,LogicalInstantiation)
(resrule_ifempty20,resrule_canempty20) = (fromJust maybe,isJust maybe) where maybe = (force_empty_clause resrule_std_sig20 (resrule_parcresfs20,resrule_loginst20) u0 resrule_poslit20 resrule_neglit20 resrule_remposclause20 resrule_remnegclause20)
(resrule_resfs20,resrule_resloginst20) = resrule_ifempty20
resrule_emptycstrs20 :: [Constraint]
resrule_emptycstrs20 = cstrs where (_,_,(_,cstrs),_) = resrule_resfs20

resrule20_t1 = AT "Resolvent is [-uA]" (resolvent_eq_test (read "[-u0 X0]") resrule_resolvent20)
resrule20_t2 = AT "Generated constraint is uA = up" (generated_cstr_test (Lcstr (read "u0 X0") (read "u0 p1[0]()")) resrule_gencstr20)
resrule20_t3 = AT "Empty clause cannot be found" (empty_clause_possible_test False resrule_canempty20)
resrule20_t4 = AT "Resulting CNF is [[-p],[-uA]]" (resulting_cnf_test [read "[-p1[0]()]",read "[-u0 X0]"] resrule_rescnf20)

resrule20_ts = [resrule20_t1,resrule20_t2,resrule20_t3,resrule20_t4]

resrule20_test = putStr (combine_test_results resrule20_ts)

resrule_tests :: IO ()
resrule_tests = (putStr "***EXAMPLE 1***\n\n") >> resrule1_test >>
		(putStr "***EXAMPLE 2***\n\n") >> resrule2_test >>
		(putStr "***EXAMPLE 3***\n\n") >> resrule3_test >>
		(putStr "***EXAMPLE 4***\n\n") >> resrule4_test >>
		(putStr "***EXAMPLE 5***\n\n") >> resrule5_test >>
		(putStr "***EXAMPLE 6***\n\n") >> resrule6_test >>
		(putStr "***EXAMPLE 7***\n\n") >> resrule7_test >>
		(putStr "***EXAMPLE 8***\n\n") >> resrule8_test >>
		(putStr "***EXAMPLE 9***\n\n") >> resrule9_test >>
		(putStr "***EXAMPLE 10***\n\n") >> resrule10_test >>
		(putStr "***EXAMPLE 11***\n\n") >> resrule11_test >>
		(putStr "***EXAMPLE 12***\n\n") >> resrule12_test >>
		(putStr "***EXAMPLE 13***\n\n") >> resrule13_test >>
		(putStr "***EXAMPLE 14***\n\n") >> resrule14_test >>
		(putStr "***EXAMPLE 15***\n\n") >> resrule15_test >>
		(putStr "***EXAMPLE 16***\n\n") >> resrule16_test >>
		(putStr "***EXAMPLE 17***\n\n") >> resrule17_test >>
		(putStr "***EXAMPLE 18***\n\n") >> resrule18_test >>
		(putStr "***EXAMPLE 19***\n\n") >> resrule19_test >>
		(putStr "***EXAMPLE 20***\n\n") >> resrule20_test


-- There are proofs as short as 9 steps (8 proof depth), but first ones to appear are 12 steps (11 proof depth)
pepper_maxproofdepth = 11
pepper_nvars = 2

pepper_mvs :: [Metavariable]
pepper_mvs = [read "X0",read "X1"]

pepper_sig :: ExtendedSignature
-- p1 == pepperPizza(x)
-- p2 == pizza(x)
-- p3 == hasTopping(x,y)
-- p4 == pepper(x)
-- p5 == margherita(x)
-- f1 == x1
-- f2 == x2
-- f3 == y2
-- f4 == y0(x)
-- f5 == y1(x)
pepper_sig = (([read "p1[1]",read "p2[1]",read "p3[2]",read "p4[1]",read "p5[1]"],[],pepper_nvars),([[read "X0",read "X1"],[]],0,[0,2]),[read "f1[0]()", read "f2[0]()", read "f3[0]()", read "f4[1](x0)", read "f5[1](x0)"],[(read "X0",[(read "X1",pepper_metalink_1)]),(read "X1",[(read "X0",pepper_metalink_2)])])

pepper_metalink_1 :: Either Term Literal -> Either Term Literal
pepper_metalink_1 (Left (TVar x)) = Left (TVar x)
pepper_metalink_1 (Left (TFun f ts)) | f == (read "f1[0]") = Left (TFun (read "f2[0]") (map ((fromLeft (read "x0")) . pepper_metalink_1 . Left) ts))
pepper_metalink_1 (Left (TFun f ts)) = Left (TFun f (map ((fromLeft (read "x0")) . pepper_metalink_1 . Left) ts))
pepper_metalink_1 (Left (TMeta mx)) = Left (TMeta mx)
pepper_metalink_1 (Right (Lit p ts)) = Right (Lit p (map ((fromLeft (read "x0")) . pepper_metalink_1 . Left) ts))
pepper_metalink_1 (Right (LitM mv)) = Right (LitM mv)

pepper_metalink_2 :: Either Term Literal -> Either Term Literal
pepper_metalink_2 (Left (TVar x)) = Left (TVar x)
pepper_metalink_2 (Left (TFun f ts)) | f == (read "f2[0]") = Left (TFun (read "f1[0]") (map ((fromLeft (read "x0")) . pepper_metalink_1 . Left) ts))
pepper_metalink_2 (Left (TFun f ts)) = Left (TFun f (map ((fromLeft (read "x0")) . pepper_metalink_1 . Left) ts))
pepper_metalink_2 (Left (TMeta mx)) = Left (TMeta mx)
pepper_metalink_2 (Right (Lit p ts)) = Right (Lit p (map ((fromLeft (read "x0")) . pepper_metalink_1 . Left) ts))
pepper_metalink_2 (Right (LitM mv)) = Right (LitM mv)

pepper_cnf :: CNF
--pepper_cnf = read "[\
--	[-p1[1](x0),+p2[1](x0)],\
--	[-p1[1](x0),-p3[2](x0,x1),+p4[1](x1)],\
--	[-p2[1](x0),+p3[2](x0,f4[1](x0)),+p1[1](x0)],\
--	[-p2[1](x0),-p4[1](f4[1](x0)),+p1[1](x0)],\
--	[-p5[1](x0),+p2[1](x0)],\
--	[-p5[1](x0),-p3[2](x0,x1)],\
--	[-p2[1](x0),+p3[2](x0,f5[1](x0)),+p5[1](x0)],\
--	[+X0,+X1],\
--	[+X0,+p3[2](f1[0](),f3[0]())],\
--	[+X1,-p1[1](f1[0]())],\
--	[-p1[1](f1[0]()),p3[2](f2[0](),f3[0]())]\
--]"
--pepper_cnf = read "[[-p1[1](x0),+p2[1](x0)],[-p1[1](x0),-p3[2](x0,x1),+p4[1](x1)],[-p2[1](x0),+p3[2](x0,f4[1](x0)),+p1[1](x0)],[-p2[1](x0),-p4[1](f4[1](x0)),+p1[1](x0)],[-p5[1](x0),+p2[1](x0)],[-p5[1](x0),-p3[2](x0,x1)],[-p2[1](x0),+p3[2](x0,f5[1](x0)),+p5[1](x0)],[+X0,+X1],[+X0,+p3[2](f2[0](),f3[0]())],[+X1,-p1[1](f1[0]())],[-p1[1](f1[0]()),+p3[2](f2[0](),f3[0]())]]"
pepper_cnf = read "[[-p2[1](x0),+p3[2](x0,f4[1](x0)),+p1[1](x0)],[-p5[1](x0),+p2[1](x0)],[-p5[1](x0),-p3[2](x0,x1)],[+X0,+X1],[+X0,+p3[2](f2[0](),f3[0]())],[+X1,-p1[1](f1[0]())],[-p1[1](f1[0]()),+p3[2](f2[0](),f3[0]())]]"

--pepper_sols = enumerate_cnf_unsat_instantiations default_metaresolution_heuristic default_metaunification_heuristic pepper_sig pepper_mvs pepper_cnf
--pepper_sols = enumerate_cnf_unsat_instantiations (simple_numeric_metaresolution_heuristic pepper_maxproofdepth) default_metaunification_heuristic pepper_sig pepper_mvs pepper_cnf
pepper_sols = enumerate_cnf_unsat_instantiations (numeric_metaresolution_heuristic_2 pepper_maxproofdepth) default_metaunification_heuristic pepper_sig pepper_mvs pepper_cnf

-- With no meta-variables, for the purpose of sanity checking.
pepper_nmv_nvars = 2

pepper_nmv_mvs :: [Metavariable]
pepper_nmv_mvs = []

pepper_nmv_sig :: ExtendedSignature
-- p1 == pepperPizza(x)
-- p2 == pizza(x)
-- p3 == hasTopping(x,y)
-- p4 == pepper(x)
-- p5 == margherita(x)
-- f1 == x1
-- f2 == x2
-- f3 == y2
-- f4 == y0(x)
-- f5 == y1(x)
pepper_nmv_sig = (([read "p1[1]",read "p2[1]",read "p3[2]",read "p4[1]",read "p5[1]"],[],pepper_nmv_nvars),([],0,[]),[read "f1[0]()", read "f2[0]()", read "f3[0]()", read "f4[1](x0)", read "f5[1](x0)"],[])

pepper_nmv_cnf :: CNF
--pepper_cnf = read "[\
--	[-p1[1](x0),+p2[1](x0)],\
--	[-p1[1](x0),-p3[2](x0,x1),+p4[1](x1)],\
--	[-p2[1](x0),+p3[2](x0,f4[1](x0)),+p1[1](x0)],\
--	[-p2[1](x0),-p4[1](f4[1](x0)),+p1[1](x0)],\
--	[-p5[1](x0),+p2[1](x0)],\
--	[-p5[1](x0),-p3[2](x0,x1)],\
--	[-p2[1](x0),+p3[2](x0,f5[1](x0)),+p5[1](x0)],\
--	[+X0,+X1],\
--	[+X0,+p3[2](f1[0](),f3[0]())],\
--	[+X1,-p1[1](f1[0]())],\
--	[-p1[1](f1[0]()),p3[2](f2[0](),f3[0]())]\
--]"
--pepper_nmv_cnf = read "[[-p1[1](x0),+p2[1](x0)],[-p1[1](x0),-p3[2](x0,x1),+p4[1](x1)],[-p2[1](x0),+p3[2](x0,f4[1](x0)),+p1[1](x0)],[-p2[1](x0),-p4[1](f4[1](x0)),+p1[1](x0)],[-p5[1](x0),+p2[1](x0)],[-p5[1](x0),-p3[2](x0,x1)],[-p2[1](x0),+p3[2](x0,f5[1](x0)),+p5[1](f1[0]())],[+p5[1](f1[0]()),+p5[1](f2[0]())],[+p5[1](f1[0]()),+p3[2](f2[0](),f3[0]())],[+p5[1](f2[0]()),-p1[1](f1[0]())],[-p1[1](f1[0]()),+p3[2](f2[0](),f3[0]())]]"
-- ALL FROM HERE DOWNWARDS WORK
pepper_nmv_cnf = read "[[-p2[1](x0),+p3[2](x0,f4[1](x0)),+p1[1](x0)],[-p5[1](x0),+p2[1](x0)],[-p5[1](x0),-p3[2](x0,x1)],[+p5[1](f1[0]()),+p5[1](f2[0]())],[+p5[1](f1[0]()),+p3[2](f2[0](),f3[0]())],[+p5[1](f2[0]()),-p1[1](f1[0]())],[-p1[1](f1[0]()),+p3[2](f2[0](),f3[0]())]]"


pepper_nmv_cl_cheatlist :: [Clause]
pepper_nmv_cl_cheatlist = read "[[+p5[1](f2[0]()),-p5[1](f1[0]())],[+p5[1](f2[0]())],[-p3[2](x0,x1)],[+p5[1](f1[0]())]]"

pepper_nmv_clenum :: ClauseEnumeration _
pepper_nmv_clenum = specific_clause_enum pepper_nmv_cl_cheatlist

pepper_nmv_lit_cheatlist :: [ActualLiteral]
pepper_nmv_lit_cheatlist = read "[-p5[1](f1[0]()),+p5[1](f2[0]()),-p3[2](x0,x1),+p5[1](f1[0]())]"

pepper_nmv_lit_choice :: InClauseLiteralChoice
pepper_nmv_lit_choice = specific_lit_choice pepper_nmv_lit_cheatlist

pepper_nmv_res_cheatlist :: [(Clause,ActualLiteral)]
pepper_nmv_res_cheatlist = read "[([+p5[1](f1[0]()),+p5[1](f2[0]())],+p5[1](f1[0]())),([-p5[1](x0),-p3[2](x0,x1)],-p5[1](x0)),([+p5[1](f1[0]()),+p3[2](f2[0]())],+p3[2](f2[0]())),([-p5[1](x0),-p3[2](x0,x1)],-p5[1](f1[0]()))]"

pepper_nmv_res_enum :: ResolventEnumeration _
pepper_nmv_res_enum = specific_resolvent_enum pepper_nmv_res_cheatlist

pepper_nmv_heur :: MetaresolutionHeuristic _ _
pepper_nmv_heur = (pepper_nmv_lit_choice,pepper_nmv_res_enum,pepper_nmv_clenum,500)

--pepper_nmv_sols = enumerate_cnf_unsat_instantiations default_metaresolution_heuristic default_metaunification_heuristic pepper_nmv_sig pepper_nmv_mvs pepper_nmv_cnf
pepper_nmv_sols = enumerate_cnf_unsat_instantiations (numeric_metaresolution_heuristic_2 pepper_maxproofdepth) default_metaunification_heuristic pepper_nmv_sig pepper_nmv_mvs pepper_nmv_cnf
--pepper_nmv_cheat_sols = enumerate_cnf_unsat_instantiations pepper_nmv_heur default_metaunification_heuristic pepper_nmv_sig pepper_nmv_mvs pepper_nmv_cnf
pepper_nmv_simpl_sols = enumerate_cnf_unsat_instantiations (simple_numeric_metaresolution_heuristic pepper_maxproofdepth) default_metaunification_heuristic pepper_nmv_sig pepper_nmv_mvs pepper_nmv_cnf
pepper_nmv_dflt_sols = enumerate_cnf_unsat_instantiations default_metaresolution_heuristic default_metaunification_heuristic pepper_nmv_sig pepper_nmv_mvs pepper_nmv_cnf

just_complex_nvars = 2

just_complex_mvs :: [Metavariable]
just_complex_mvs = [read "X0",read "X1"]

just_complex_sig :: ExtendedSignature
just_complex_sig = (([read "p1[1]",read "p2[1]",read "p3[1]",read "p4[1]",read "p5[2]", read "p6[0]", read "p7[0]"],[read "f2[1]"],just_complex_nvars),([[read "X0",read "X1"]],just_complex_nvars,[0]),[read "f1[0]()"],[])

just_complex_cnf :: CNF
--just_complex_cnf = read "[[-p1[1](x0),+p1[1](x1)],[+p1[1](x0)],[-p1[1](x0)]]"
--just_complex_cnf = read "[[-p1[1](x0),+p4[1](x0),-p5[2](f2[1](x0),x0)],[+p1[1](x0),-p5[2](x1,x0),+p2[1](x1)],[-p4[1](x0)],[+p5[2](x0,x1)],[-p2[1](f2[1](x0))]]"
--just_complex_cnf = read "[[-X0,+p4[1](x0),-p5[2](f2[1](x0),x0)],[+p1[1](x0),-p5[2](x1,x0),+p2[1](x1)],[-p4[1](x0)],[+p5[2](x0,x1)],[-p2[1](f2[1](x0))]]"
--just_complex_cnf = read "[[-X0,+p4[1](x0),-p5[2](f2[1](x0),x0)],[+p1[1](x0),+X1,+p2[1](x1)],[-p4[1](x0)],[+p5[2](x0,x1)],[-p2[1](f2[1](x0))]]"
just_complex_cnf = read "[[-p1[1](x0),+p4[1](x0),-p5[2](f2[1](x0),x0)],[+p1[1](x0),-p5[2](x1,x0),+p2[1](x1)],[-p4[1](x0)],[+X0],[-p2[1](f2[1](x0))]]"


just_complex_cl_cheatlist :: [Clause]
just_complex_cl_cheatlist = read "[[+p5[1](f2[0]()),-p1[1](f1[0]())],[+p5[1](f2[0]()),-p2[1](f1[0]()),+p3[2](f1[0](),f4[1](x0))],[+p5[1](f2[0]()),-p2[1](f1[0]()),-p5[1](f1[0]())],[+p5[1](f2[0]()),-p5[1](f1[0]())],[+p5[1](f2[0]())],[-p3[2](x0,x1)],[+p5[1](f1[0]())],[-p3[2](x0,x1)],[-p1[1](f1[0]())],[-p3[2](x0,x1)],[+p5[1](f1[0]())],[-p2[1](f1[0]())]]"

just_complex_clenum :: ClauseEnumeration _
just_complex_clenum = specific_clause_enum just_complex_cl_cheatlist

just_complex_lit_cheatlist :: [ActualLiteral]
just_complex_lit_cheatlist = read "[-p1[1](f1[0]()),+p3[2](f1[0](),f4[1](x0)),-p2[1](f1[0]()),-p5[1](f1[0]()),+p5[1](f2[0]()),-p3[2](x0,x1),+p5[1](f1[0]()),-p3[2](x0,x1),-p1[1](f1[0]()),-p3[2](x0,x1),+p5[1](f1[0]()),-p2[1](f1[0]())]"

just_complex_lit_choice :: InClauseLiteralChoice
just_complex_lit_choice = specific_lit_choice just_complex_lit_cheatlist

just_complex_res_cheatlist :: [(Clause,ActualLiteral)]
just_complex_res_cheatlist = read "[([-p2[1](x0),+p3[2](x0,f4[1](x0)),+p1[1](x0)],+p1[1](x0)),([-p5[1](x0),-p3[2](x0,x1)],-p3[2](x0,x1)),([-p5[1](x0),+p2[1](x0)],+p2[1](x0)),([+p5[1](f1[0]()),+p5[1](f2[0]())],+p5[1](f1[0]())),([-p5[1](x0),-p3[2](x0,x1)],-p5[1](x0)),([+p5[1](f1[0]()),+p3[2](f2[0](),f3[0]())],+p3[2](f2[0](),f3[0]())),([-p5[1](x0),-p3[2](x0,x1)],-p5[1](x0)),([-p1[1](f1[0]()),+p3[2](f2[0](),f3[0]())],+p3[2](f2[0](),f3[0]())),([-p2[1](x0),+p3[2](x0,f4[1](x0)),+p1[1](x0)],+p1[1](x0)),([-p2[1](f1[0]()),+p3[2](f1[0](),f4[1](f1[0]()))],+p3[2](f1[0](),f4[1](f1[0]()))),([-p5[1](x0),+p2[1](x0)],-p5[1](x0)),([+p2[1](x0)],+p2[1](x0))]"

just_complex_res_enum :: ResolventEnumeration _
just_complex_res_enum = specific_resolvent_enum just_complex_res_cheatlist

just_complex_heur :: MetaresolutionHeuristic _ _
just_complex_heur = (just_complex_lit_choice,just_complex_res_enum,just_complex_clenum,500)

just_complex_sols = enumerate_cnf_unsat_instantiations (numeric_metaresolution_heuristic_2 pepper_maxproofdepth) default_metaunification_heuristic just_complex_sig just_complex_mvs just_complex_cnf
just_complex_cheat_sols = enumerate_cnf_unsat_instantiations just_complex_heur default_metaunification_heuristic just_complex_sig just_complex_mvs just_complex_cnf



unsat_maxproofdepth = 15
unsat_nvars = 2

unsat_mvs :: [Metavariable]
unsat_mvs = [read "X0"]

unsat_sig :: ExtendedSignature
-- p1 == pizza(x)
-- p2 == hasTopping(x,y)
-- p3 == margherita(x)
-- f1 == x0
-- f2 == y1(x)
unsat_sig = (([read "p1[1]",read "p2[2]",read "p3[1]"],[],unsat_nvars),([[read "X0"],[]],0,[0,2]),[read "f1[0]()", read "f2[1](x0)"],[])

unsat_cnf :: CNF
unsat_cnf = [read "[-p3[1](x0),-p2[2](x0,x1)]", read "[-p3[1](x0),+p1[1](x0)]", read "[-p1[1](x0),+p2[2](x0,f2[1](x0))]", read "[+X0]"]
unsat_sols = enumerate_cnf_unsat_instantiations (numeric_metaresolution_heuristic_2 unsat_maxproofdepth) default_metaunification_heuristic unsat_sig unsat_mvs unsat_cnf


unsat_f_nvars = 2

unsat_f_mvs :: [Metavariable]
unsat_f_mvs = [read "X0"]

unsat_f_mvpart :: MetavariablePartition
unsat_f_mvpart = ([[read "X0"],[]],0,[0,2])

unsat_f_sks :: [Term]
unsat_f_sks = [read "f1[0]()", read "f2[1](x0)"]

unsat_f_ps :: Int -> [Predicate]
unsat_f_ps 0 = [read "p1[1]", read "p2[2]", read "p3[1]"]
unsat_f_ps n = (Pred (n+3) 1):(unsat_f_ps (n-1))

unsat_f_sig :: Int -> ExtendedSignature
unsat_f_sig n = ((unsat_f_ps n,[],unsat_f_nvars),unsat_f_mvpart,unsat_f_sks,[])

unsat_f_levelpred :: Int -> Predicate
unsat_f_levelpred 0 = Pred 1 1
unsat_f_levelpred n = Pred (n+3) 1

unsat_f_cnf_base :: Int -> CNF
unsat_f_cnf_base 0 = [read "[-p3[1](x0),-p2[2](x0,x1)]", read "[-p1[1](x0),+p2[2](x0,f2[1](x0))]", read "[+X0]"]
unsat_f_cnf_base n = ([NegLit (MLitL (Lit (unsat_f_levelpred n)  [read "x0"])),PosLit (MLitL (Lit (unsat_f_levelpred (n-1)) [read "x0"]))]):(unsat_f_cnf_base (n-1))

unsat_f_cnf :: Int -> CNF
unsat_f_cnf n = ([read "-p3[1](x0)",PosLit (MLitL (Lit (unsat_f_levelpred n) [read "x0"]))]):(unsat_f_cnf_base n)

-- First parameter is the index of the CNF
-- Second parameter is the maximum proof depth
unsat_f_sols :: Int -> Int -> Enumeration (_,Maybe (LogicalInstantiation,[Unifier],ResolutionProof,FullSolution,[UnifierDescription],Instantiation))
unsat_f_sols n maxproofdepth = enumerate_cnf_unsat_instantiations (numeric_metaresolution_heuristic_2 maxproofdepth) default_metaunification_heuristic (unsat_f_sig n) unsat_f_mvs (unsat_f_cnf n)

-- (Depth of the chain of implications,Maximum depth of the proof search,Number of solutions,Machine ID)
type UnsatFTest = (Int,Int,Int,String)
-- Nothing indicates that there was not so many solutions.
type UnsatFTestResult = Maybe Float

run_unsat_f_test :: Int -> Int -> Int -> String -> IO UnsatFTestResult
run_unsat_f_test n maxdepth sols id = if ((length rs) >= (sols+1)) then (measure_time (map (\i -> show_unsat_instantiation (unsat_f_sig n) unsat_f_mvs ((enum_up_to_h i (unsat_f_sols n maxdepth)) !! i)) [1..sols]) >>= (return . Just)) else (return Nothing) where rs = (enum_up_to_h sols (unsat_f_sols n maxdepth))

print_unsat_f_test :: UnsatFTest -> IO ()
print_unsat_f_test (n,maxdepth,sols,id) =
	(putStr (show n)) >> (putStr "\t") >>
	(putStr (show maxdepth)) >> (putStr "\t") >>
	(putStr (show sols)) >> (putStr "\t") >>
	(putStr (show id)) >> (putStr "\t") >>
	getCurrentTime >>= (putStr . show) >> (putStr "\t") >>
	(print_unsat_f_test_result (run_unsat_f_test n maxdepth sols id)) >> (putStr "\n")

print_unsat_f_test_result :: IO UnsatFTestResult -> IO ()
print_unsat_f_test_result x = x >>= (putStr . print_unsat_f_test_helper)

print_unsat_f_test_helper :: UnsatFTestResult -> String
print_unsat_f_test_helper Nothing = "Not enough solutions"
print_unsat_f_test_helper (Just r) = (show r)

-- Parameters, in order:
-- Depths of chain of implications to try
-- Depths of proof searches to try
-- Numbers of solutions to try
-- Machine ID
-- Number of times to run each test.
do_batch_unsat_f_tests :: [Int] -> [Int] -> [Int] -> String -> Int -> IO ()
do_batch_unsat_f_tests _ _ _ _ 0 = putStr ""
do_batch_unsat_f_tests ns maxdepths solss id i = foldr (>>) (do_batch_unsat_f_tests ns maxdepths solss id (i-1)) (map (\vs -> print_unsat_f_test (vs !! 0,vs !! 1,vs !! 2,id)) values) where values = combinations [ns,maxdepths,solss]







-----------------------------------
-- Meta-resolution global tests
-----------------------------------

-- Evaluating functions
metares_all_insts_diff :: [Metavariable] -> Int -> Enumeration (_,Maybe (LogicalInstantiation,[Unifier],ResolutionProof,FullSolution,[UnifierDescription],Instantiation)) -> AutomatedTestResult
metares_all_insts_diff mvs n en = metares_all_insts_diff_helper_3 mvs aslist where aslist = enum_up_to_h n en

metares_all_insts_diff_helper_3 :: [Metavariable] -> [Maybe (LogicalInstantiation,[Unifier],ResolutionProof,FullSolution,[UnifierDescription],Instantiation)] -> AutomatedTestResult
metares_all_insts_diff_helper_3 _ [] = ATR True "All instantiations distinct."
metares_all_insts_diff_helper_3 mvs (s1:ss) = if (any (\s2 -> metares_all_insts_diff_helper s1 s2) ss) then (ATR False ("At least instantiation \n" ++ (metares_all_insts_diff_helper_2 mvs s1) ++ " is repeated.")) else (metares_all_insts_diff_helper_3 mvs ss)

metares_all_insts_diff_helper :: Maybe (LogicalInstantiation,[Unifier],ResolutionProof,FullSolution,[UnifierDescription],Instantiation) -> Maybe (LogicalInstantiation,[Unifier],ResolutionProof,FullSolution,[UnifierDescription],Instantiation) -> Bool
metares_all_insts_diff_helper Nothing _ = False
metares_all_insts_diff_helper _ Nothing = False
metares_all_insts_diff_helper (Just (_,_,_,_,uds1,inst1)) (Just (_,_,_,_,uds2,inst2)) = (eq_inst inst1 inst2) && (all (\(ud1,ud2) -> eq_unifier ud1 ud2) (zip uds1 uds2))

metares_all_insts_diff_helper_2 :: [Metavariable] -> Maybe (LogicalInstantiation,[Unifier],ResolutionProof,FullSolution,[UnifierDescription],Instantiation) -> String
metares_all_insts_diff_helper_2 _ Nothing = "Unsatisfiable solution\n"
metares_all_insts_diff_helper_2 mvs (Just (_,_,_,_,uds1,inst1)) = (show_inst inst1 mvs) ++ "\nwith\n" ++ (show uds1) ++ "\n"
