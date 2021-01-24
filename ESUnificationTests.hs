{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
--{-# LANGUAGE UndecidableInstances #-}
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


-- Dependency graph operation tests
-- Note that on the tests we always assume that we start from an empty graph, to build the StateT.
newtype RTestSOMetaUnifDGraph s = RTestSOMetaUnifDGraph {fromMudg :: SOMetaUnifDGraph s}

lens_RTestSOMetaUnifDGraph :: Lens' (RTestSOMetaUnifDGraph s) (SOMetaUnifDGraph s)
lens_RTestSOMetaUnifDGraph f rrmudg = fmap (\rmudg -> RTestSOMetaUnifDGraph rmudg) (f (fromMudg rrmudg))

emptyRMUDG :: SOMetaSignature -> RTestSOMetaUnifDGraph s
emptyRMUDG sig = RTestSOMetaUnifDGraph (emptyVDGraph sig)

on_vdgraph :: StateT (ESUnifVDGraph s CTermF SOPredicate OPredicate OFunction OVariable SOAMVariable SOMVariable UnifVariable) (ST s) a -> StateT (RTestSOMetaUnifDGraph s) (ST s) a
on_vdgraph = mzoom lens_RTestSOMetaUnifDGraph

on_dgraph :: StateT (ESUnifDGraph s CTermF OPredicate OFunction OVariable SOAMVariable SOMVariable UnifVariable) (ST s) a -> StateT (RTestSOMetaUnifDGraph s) (ST s) a
on_dgraph = mzoom (lens_RTestSOMetaUnifDGraph . lens_esunifdgraph_dgraph)

to_rsomudg :: SOMetaSignature -> (forall s. StateT (RTestSOMetaUnifDGraph s) (ST s) a) -> RSOMetaUnifDGraph
to_rsomudg sig mudg = RESUnifVDGraph ((fromMudg . snd) <$> runStateT mudg (emptyRMUDG sig))

show_mudg :: SOMetaSignature -> (forall s. StateT (RTestSOMetaUnifDGraph s) (ST s) a) -> IO ()
--show_mudg s = putStr (runST ((show_eqdgraph . esunifdgraph . fromESUnifNDGraph . fromMudg . snd) <$> (runStateT s emptyRMUDG)))
show_mudg sig s = putStr (runST (fst <$> (runStateT (s >> (mzoom lens_RTestSOMetaUnifDGraph show_esuvdg)) (emptyRMUDG sig))))

-- Check that horizontal edge exists / does not exist
check_hfoedge :: SOMetaSignature -> String -> (forall s. StateT (RTestSOMetaUnifDGraph s) (ST s) a) -> SOMetatermF -> [SOMetaTermDependant] -> SOMetaTermDependant -> AutomatedTest
check_hfoedge sig title stmudg h ss t = AT title (if result then (ATR True "The horizontal edge was correctly found.") else (ATR False "Could not find the expected horizontal edge.")) where hid = relbwEqDGSoId (FSONode h); sids = Prelude.map relbwEqDGFoId ss; tid = relbwEqDGFoId t; checked = do {stmudg; on_dgraph (st_checkEqDGFOEdge hid sids tid)}; result = getStateTSTValue checked (emptyRMUDG sig)

check_hsoedge :: SOMetaSignature -> String -> (forall s. StateT (RTestSOMetaUnifDGraph s) (ST s) a) -> SOMetatermF -> [SOMetatermF] -> SOMetatermF -> AutomatedTest
check_hsoedge sig title stmudg h ss t = AT title (if result then (ATR True "The horizontal edge was correctly found.") else (ATR False "Could not find the expected horizontal edge.")) where hid = relbwEqDGSoId (FSONode h); sids = Prelude.map (relbwEqDGSoId . FSONode) ss; tid = relbwEqDGSoId (FSONode t); checked = do {stmudg; on_dgraph (st_checkEqDGSOEdge hid sids tid)}; result = getStateTSTValue checked (emptyRMUDG sig)

check_not_hfoedge :: SOMetaSignature -> String -> (forall s. StateT (RTestSOMetaUnifDGraph s) (ST s) a) -> SOMetatermF -> [SOMetaTermDependant] -> SOMetaTermDependant -> AutomatedTest
check_not_hfoedge sig title stmudg h ss t = AT title (if result then (ATR True "The horizontal edge was correctly not found.") else (ATR False "Found the horizontal edge, but we should not have done so.")) where hid = relbwEqDGSoId (FSONode h); sids = Prelude.map relbwEqDGFoId ss; tid = relbwEqDGFoId t; checked = do {stmudg; on_dgraph (st_checkEqDGFOEdge hid sids tid)}; result = not (getStateTSTValue checked (emptyRMUDG sig))

check_not_hsoedge :: SOMetaSignature -> String -> (forall s. StateT (RTestSOMetaUnifDGraph s) (ST s) a) -> SOMetatermF -> [SOMetatermF] -> SOMetatermF -> AutomatedTest
check_not_hsoedge sig title stmudg h ss t = AT title (if result then (ATR True "The horizontal edge was correctly not found.") else (ATR False "Found the horizontal edge, but we should not have done so.")) where hid = relbwEqDGSoId (FSONode h); sids = Prelude.map (relbwEqDGSoId . FSONode) ss; tid = relbwEqDGSoId (FSONode t); checked = do {stmudg; on_dgraph (st_checkEqDGSOEdge hid sids tid)}; result = not (getStateTSTValue checked (emptyRMUDG sig))


-- Check that vertical edge exists / does not exist
check_vedge :: SOMetaSignature -> String -> (forall s. StateT (RTestSOMetaUnifDGraph s) (ST s) a) -> SOMetaTermDependant -> SOMetaTermDependant -> AutomatedTest
check_vedge sig title stmudg s t = AT title (if result then (ATR True "The vertical edge was correctly found.") else (ATR False "Could not find the expected vertical edge.")) where sid = relbwEqDGFoId s; tid = relbwEqDGFoId t; checked = do {stmudg; on_vdgraph (checkVFoEdge sid tid)}; result = getStateTSTValue checked (emptyRMUDG sig)

check_not_vedge :: SOMetaSignature -> String -> (forall s. StateT (RTestSOMetaUnifDGraph s) (ST s) a) -> SOMetaTermDependant -> SOMetaTermDependant -> AutomatedTest
check_not_vedge sig title stmudg s t = AT title (if result then (ATR True "The vertical edge was correctly not found.") else (ATR False "Found the vertical edge, but we should not have done so.")) where sid = relbwEqDGFoId s; tid = relbwEqDGFoId t; checked = do {stmudg; on_vdgraph (checkVFoEdge sid tid)}; result = not (getStateTSTValue checked (emptyRMUDG sig))

-- Check that two elements are equivalent / not equivalent
check_foequiv :: SOMetaSignature -> String -> (forall s. StateT (RTestSOMetaUnifDGraph s) (ST s) a) -> SOMetaTermDependant -> SOMetaTermDependant -> AutomatedTest
check_foequiv sig title stmudg a b = AT title (if result then (ATR True "The two elements were indeed found to be equivalent.") else (ATR False "The two elements were not equivalent, but they should be.")) where aid = relbwEqDGFoId a; bid = relbwEqDGFoId b; checked = do {stmudg; on_dgraph (eqSTRelativeIds aid bid)}; result = getStateTSTValue checked (emptyRMUDG sig)

check_soequiv :: SOMetaSignature -> String -> (forall s. StateT (RTestSOMetaUnifDGraph s) (ST s) a) -> SOMetatermF -> SOMetatermF -> AutomatedTest
check_soequiv sig title stmudg a b = AT title (if result then (ATR True "The two elements were indeed found to be equivalent.") else (ATR False "The two elements were not equivalent, but they should be.")) where aid = relbwEqDGSoId (FSONode a); bid = relbwEqDGSoId (FSONode b); checked = do {stmudg; on_dgraph (eqSTRelativeIds aid bid)}; result = getStateTSTValue checked (emptyRMUDG sig)

check_not_foequiv :: SOMetaSignature -> String -> (forall s. StateT (RTestSOMetaUnifDGraph s) (ST s) a) -> SOMetaTermDependant -> SOMetaTermDependant -> AutomatedTest
check_not_foequiv sig title stmudg a b = AT title (if result then (ATR True "The two elements were indeed found to be not equivalent.") else (ATR False "The two elements were equivalent, but they should not be.")) where aid = relbwEqDGFoId a; bid = relbwEqDGFoId b; checked = do {stmudg; on_dgraph (eqSTRelativeIds aid bid)}; result = not (getStateTSTValue checked (emptyRMUDG sig))

check_not_soequiv :: SOMetaSignature -> String -> (forall s. StateT (RTestSOMetaUnifDGraph s) (ST s) a) -> SOMetatermF -> SOMetatermF -> AutomatedTest
check_not_soequiv sig title stmudg a b = AT title (if result then (ATR True "The two elements were indeed found to be not equivalent.") else (ATR False "The two elements were equivalent, but they should not be.")) where aid = relbwEqDGSoId (FSONode a); bid = relbwEqDGSoId (FSONode b); checked = do {stmudg; on_dgraph (eqSTRelativeIds aid bid)}; result = not (getStateTSTValue checked (emptyRMUDG sig))


-- Checking with expressions
check_foexp :: SOMetaSignature -> String -> (forall s. StateT (RTestSOMetaUnifDGraph s) (ST s) a) -> SOMetaUnifFOExp -> SOMetaTermDependant -> AutomatedTest
check_foexp sig title stmudg exp t = AT title (if result then (ATR True "The dependant matches the expression in the graph.") else (ATR False "The dependant does not match the expression in the graph, but it should.")) where checked = do {stmudg; on_vdgraph (match_foexp exp (relbwEqDGFoId t))}; result = getStateTSTValue checked (emptyRMUDG sig)

check_not_foexp :: SOMetaSignature -> String -> (forall s. StateT (RTestSOMetaUnifDGraph s) (ST s) a) -> SOMetaUnifFOExp -> SOMetaTermDependant -> AutomatedTest
check_not_foexp sig title stmudg exp t = AT title (if result then (ATR True "The dependant does not match the expression in the graph.") else (ATR False "The dependant matches the expression in the graph, but it should not.")) where checked = do {stmudg; on_vdgraph (match_foexp exp (relbwEqDGFoId t))}; result = not (getStateTSTValue checked (emptyRMUDG sig))

check_soexp :: SOMetaSignature -> String -> (forall s. StateT (RTestSOMetaUnifDGraph s) (ST s) a) -> SOMetaUnifSOExp -> SOMetatermF -> AutomatedTest
check_soexp sig title stmudg exp t = AT title (if result then (ATR True "The dependant matches the expression in the graph.") else (ATR False "The dependant does not match the expression in the graph, but it should.")) where checked = do {stmudg; on_vdgraph (match_soexp exp (relbwEqDGSoId (FSONode t)))}; result = getStateTSTValue checked (emptyRMUDG sig)

check_not_soexp :: SOMetaSignature -> String -> (forall s. StateT (RTestSOMetaUnifDGraph s) (ST s) a) -> SOMetaUnifSOExp -> SOMetatermF -> AutomatedTest
check_not_soexp sig title stmudg exp t = AT title (if result then (ATR True "The dependant does not match the expression in the graph.") else (ATR False "The dependant matches the expression in the graph, but it should not.")) where checked = do {stmudg; on_vdgraph (match_soexp exp (relbwEqDGSoId (FSONode t)))}; result = not (getStateTSTValue checked (emptyRMUDG sig))


-- For answer sets
check_min_as :: String -> Int -> AnswerSet s t -> AutomatedTest
check_min_as title n as = if l < n then (AT title (ATR False ("Expected at least " ++ (show n) ++ " results, but could only find " ++ (show l) ++ "."))) else (AT title (ATR True ("Correctly found at least " ++ (show n) ++ " results."))) where l = uns_produce_next (elength (etake n ((implicitOnly as) \$ ())))

check_max_as :: String -> Int -> AnswerSet s t -> AutomatedTest
check_max_as title n as = if l > n then (AT title (ATR False ("Expected at most " ++ (show n) ++ " results, but found " ++ (show l) ++ "."))) else (AT title (ATR True ("Correctly found less than " ++ (show n) ++ " results."))) where l = uns_produce_next (elength (etake (n+1) ((implicitOnly as) \$ ())))

check_exactly_as :: String -> Int -> AnswerSet s t -> AutomatedTest
check_exactly_as title n as = if l /= n then (AT title (ATR False ("Expected exactly " ++ (show n) ++ " results, but found " ++ (show l) ++ " instead."))) else (AT title (ATR True ("Correctly found exactly " ++ (show n) ++ " results."))) where l = uns_produce_next (elength (etake (n+1) ((implicitOnly as) \$ ())))

check_min_exp_as :: String -> Int -> AnswerSet s t -> AutomatedTest
check_min_exp_as title n as = if l < n then (AT title (ATR False ("Expected at least " ++ (show n) ++ " results, but could only find " ++ (show l) ++ "."))) else (AT title (ATR True ("Correctly found at least " ++ (show n)  ++ " results."))) where l = uns_produce_next (elength (etake n ((enumAS as) \$ ())))

check_max_exp_as :: String -> Int -> AnswerSet s t -> AutomatedTest
check_max_exp_as title n as = if l > n then (AT title (ATR False ("Expected at most " ++ (show n) ++ " results, but found " ++ (show l) ++ "."))) else (AT title (ATR True ("Correctly found less than " ++ (show n)  ++ " results."))) where l = uns_produce_next (elength (etake (n+1) ((enumAS as) \$ ())))

check_exactly_exp_as :: String -> Int -> AnswerSet s t -> AutomatedTest
check_exactly_exp_as title n as = if l /= n then (AT title (ATR False ("Expected exactly " ++ (show n) ++ " results, but found " ++ (show l) ++ " instead."))) else (AT title (ATR True ("Correctly found exactly " ++ (show n)  ++ " results."))) where l = uns_produce_next (elength (etake (n+1) ((enumAS as) \$ ())))



check_any_resuvdg :: Int -> String -> (forall a. String -> (forall s. StateT (RTestSOMetaUnifDGraph s) (ST s) a) -> AutomatedTest) -> AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution -> AutomatedTest
check_any_resuvdg maxen title ftest as = case filtered of {EnumProc.Empty -> AT title (ATR False ("None of the first " ++ (show maxen) ++ " results produced passed the check.")); Produce at _ -> at} where imp = etake maxen ((implicitOnly as) \$ ()); impat = (\resuvdg -> ftest title (StateT (\rtest -> (((),) . RTestSOMetaUnifDGraph) <$> (fromRESUnifVDGraph resuvdg)))) <$> imp; filtered = uns_ecollapse (efilter (\(AT title (ATR res str)) -> res) impat)

check_all_resuvdg :: Int -> String -> (forall a. String -> (forall s. StateT (RTestSOMetaUnifDGraph s) (ST s) a) -> AutomatedTest) -> AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution -> AutomatedTest
check_all_resuvdg maxen title ftest as = case filtered of {EnumProc.Empty -> AT title (ATR True ("All of the first " ++ (show maxen) ++ " results produced passed the check.")); Produce at _ -> AT title (ATR False ("Found a result amongst the first " ++ (show maxen) ++ " produced that did not pass the check."))} where imp = etake maxen ((implicitOnly as) \$ ()); impat = (\resuvdg -> ftest title (StateT (\rtest -> (((),) . RTestSOMetaUnifDGraph) <$> (fromRESUnifVDGraph resuvdg)))) <$> imp; filtered = uns_ecollapse (efilter (\(AT title (ATR res str)) -> not res) impat)



-- UnifSysSolution tests
check_map :: (Normalizable b b, Eq b, Ord a) => (a := b) -> (a := b) -> Bool
check_map desired sol = all f (toList desired) where f = (\(k,v) -> NormalizedFunctor (sol !? k) ~~ NormalizedFunctor (Just v))

check_usol :: String -> SOMetaUnifSysSolution -> SOMetaUnifSysSolution -> AutomatedTest
check_usol title desired sol = if ((check_map (uss_fnsol desired) (uss_fnsol sol)) && (check_map (uss_pdsol desired) (uss_pdsol sol))) then (AT title (ATR True "All the values in the desired solution were found in the actual solution.")) else (AT title (ATR False "Some values in the desired solution could not be found in the actual solution."))	

check_not_usol :: String -> SOMetaUnifSysSolution -> SOMetaUnifSysSolution -> AutomatedTest
check_not_usol title desired sol = if ((check_map (uss_fnsol desired) (uss_fnsol sol)) && (check_map (uss_pdsol desired) (uss_pdsol sol))) then (AT title (ATR False "Some of the values in the undesired solution were found in the actual solution.")) else (AT title (ATR True "None of the values from the undesired solution could be found in the actual solution."))


check_en_any_usol :: Int -> String -> (String -> SOMetaUnifSysSolution -> AutomatedTest) -> AnswerSet s SOMetaUnifSysSolution -> AutomatedTest
check_en_any_usol maxen title ftest as = case filtered of {EnumProc.Empty -> AT title (ATR False ("None of the first " ++ (show maxen) ++ " results produced passed the check.")); Produce at _ -> at}
	where imp = etake maxen (enumAS as \$ ()); impat = ftest title <$> imp; filtered = uns_ecollapse (efilter (\(AT title (ATR res str)) -> res) impat)

check_en_all_usol :: Int -> String -> (String -> SOMetaUnifSysSolution -> AutomatedTest) -> AnswerSet s SOMetaUnifSysSolution -> AutomatedTest
check_en_all_usol maxen title ftest as = case filtered of {EnumProc.Empty -> AT title (ATR True ("All of the first " ++ (show maxen)  ++ " results produced passed the check.")); Produce at _ -> AT title (ATR False ("Found a result amongst the first " ++ (show maxen) ++ " produced that did not pass the check."))}
	where imp = etake maxen (enumAS as \$ ()); impat = ftest title <$> imp; filtered = uns_ecollapse (efilter (\(AT tile (ATR res str)) -> not res) impat)

check_imp_usol :: String -> SOMetaUnifSysSolution -> AnswerSet s SOMetaUnifSysSolution -> AutomatedTest
check_imp_usol title desired as = if (uns_produce_next (checkAS as desired \$ ())) then (AT title (ATR True "The solution correctly was implicitly found in the answer set.")) else (AT title (ATR False "The solution could not be implicitly found in the answer set, but it should have."))

check_not_imp_usol :: String -> SOMetaUnifSysSolution -> AnswerSet s SOMetaUnifSysSolution -> AutomatedTest
check_not_imp_usol title desired as = if (uns_produce_next (checkAS as desired \$ ())) then (AT title (ATR False "The solution was implicitly found in the answer set, but it should not have.")) else (AT title (ATR True "The solution was correctly not implicitly found in the answer set."))



check_usys_usol_at :: String -> [SOMetaUnifEquation] -> SOMetaUnifSysSolution -> AutomatedTest
check_usys_usol_at title usys usol = AT title (if (check_usys_usol usol usys) then (ATR True "The equations are correctly satisfied in the solution.") else (ATR False "Some of the equations were not satisfied in the solution, but they should."))

check_not_usys_usol_at :: String -> [SOMetaUnifEquation] -> SOMetaUnifSysSolution -> AutomatedTest
check_not_usys_usol_at title usys usol = AT title (if (check_usys_usol usol usys) then (ATR False "The equations are satisfied in the solution, but they should not.") else (ATR True "Some of the equations were correctly not satisfied in the solution."))


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
vcommute1_sotid1 = relbwEqDGSoId (FSONode vcommute1_soterm1)

vcommute1_sig :: SOMetaSignature
vcommute1_sig = SOSignature (Signature [] [EnumProc.Empty,read "f1[1]" --> EnumProc.Empty] (read "x0" --> read "x1" --> EnumProc.Empty)) EnumProc.Empty EnumProc.Empty EnumProc.Empty

vcommute1_mudg1 :: StateT (RTestSOMetaUnifDGraph s) (ST s) _
vcommute1_mudg1 = do {on_dgraph (newEqDGFOEdge vcommute1_sotid1 [vcommute1_tid1] vcommute1_tid2); on_vdgraph (addVFoEdge vcommute1_tid2 vcommute1_tid3 (read "u1")); pass}

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
vcommute2_sotid1 = relbwEqDGSoId (FSONode vcommute2_soterm1)

vcommute2_sig :: SOMetaSignature
vcommute2_sig = SOSignature (Signature [] [EnumProc.Empty,EnumProc.Empty,read "f1[2]" --> EnumProc.Empty] (read "x0" --> read "x1" --> read "x2" --> EnumProc.Empty)) EnumProc.Empty EnumProc.Empty EnumProc.Empty

vcommute2_mudg1 :: StateT (RTestSOMetaUnifDGraph s) (ST s) _
vcommute2_mudg1 = do {on_dgraph (newEqDGFOEdge vcommute2_sotid1 [vcommute2_tid1,vcommute2_tid2] vcommute2_tid3); on_vdgraph (addVFoEdge vcommute2_tid3 vcommute2_tid4 (read "u1")); pass}

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
vcommute3_sotid1 = relbwEqDGSoId (FSONode vcommute3_soterm1)

vcommute3_soterm2 :: SOMetatermF
vcommute3_soterm2 = read "f2[1]"

vcommute3_sotid2 :: SOMetaUnifRelSoId s
vcommute3_sotid2 = relbwEqDGSoId (FSONode vcommute3_soterm2)

vcommute3_sig :: SOMetaSignature
vcommute3_sig = SOSignature (Signature [] [EnumProc.Empty,read "f1[1]" --> read "f2[1]" --> EnumProc.Empty] (read "x0" --> read "x1" --> read "x2" --> EnumProc.Empty)) EnumProc.Empty EnumProc.Empty EnumProc.Empty

vcommute3_mudg1 :: StateT (RTestSOMetaUnifDGraph s) (ST s) _
vcommute3_mudg1 = do {on_dgraph (newEqDGFOEdge vcommute3_sotid1 [vcommute3_tid1] vcommute3_tid2); on_dgraph (newEqDGFOEdge vcommute3_sotid2 [vcommute3_tid5] vcommute3_tid1); on_vdgraph (addVFoEdge vcommute3_tid2 vcommute3_tid3 (read "u1")); pass}

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
vcommute4_sotid1 = relbwEqDGSoId (FSONode vcommute4_soterm1)

vcommute4_sig :: SOMetaSignature
vcommute4_sig = SOSignature (Signature [] [EnumProc.Empty,read "f1[1]" --> EnumProc.Empty] (read "x0" --> read "x1" --> EnumProc.Empty)) EnumProc.Empty EnumProc.Empty EnumProc.Empty

vcommute4_mudg1 :: StateT (RTestSOMetaUnifDGraph s) (ST s) _
vcommute4_mudg1 = do {on_dgraph (newEqDGFOEdge vcommute4_sotid1 [vcommute4_tid1] vcommute4_tid2); on_vdgraph (addVFoEdge vcommute4_tid1 vcommute4_tid4 (read "u1")); pass}

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
valign1_sig = SOSignature (Signature [] [] (read "x0" --> read "x1" --> EnumProc.Empty)) EnumProc.Empty EnumProc.Empty EnumProc.Empty

valign1_mudg1 :: StateT (RTestSOMetaUnifDGraph s) (ST s) _
valign1_mudg1 = do {on_vdgraph (addVFoEdge valign1_tid3 valign1_tid1 (read "u1")); on_dgraph (newEqDGFONode valign1_term6); on_dgraph (newEqDGFONode valign1_term2); return ()}

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
zip1_sotid1 = relbwEqDGSoId (FSONode zip1_soterm1)

zip1_soterm2 :: SOMetatermF
zip1_soterm2 = read "f2[2]"

zip1_sotid2 :: SOMetaUnifRelSoId s
zip1_sotid2 = relbwEqDGSoId (FSONode zip1_soterm2)

zip1_soterm3 :: SOMetatermF
zip1_soterm3 = read "F0[1]"

zip1_sotid3 :: SOMetaUnifRelSoId s
zip1_sotid3 = relbwEqDGSoId (FSONode zip1_soterm3)

zip1_soterm4 :: SOMetatermF
zip1_soterm4 = read "F1[1]"

zip1_sotid4 :: SOMetaUnifRelSoId s
zip1_sotid4 = relbwEqDGSoId (FSONode zip1_soterm4)

zip1_soterm5 :: SOMetatermF
zip1_soterm5 = read "F2[1]"

zip1_sotid5 :: SOMetaUnifRelSoId s
zip1_sotid5 = relbwEqDGSoId (FSONode zip1_soterm5)

zip1_soterm6 :: SOMetatermF
zip1_soterm6 = read "F3[1]"

zip1_sotid6 :: SOMetaUnifRelSoId s
zip1_sotid6 = relbwEqDGSoId (FSONode zip1_soterm6)

zip1_soterm7 :: SOMetatermF
zip1_soterm7 = read "F4[1]"

zip1_sotid7 :: SOMetaUnifRelSoId s
zip1_sotid7 = relbwEqDGSoId (FSONode zip1_soterm7)

zip1_soterm8 :: SOMetatermF
zip1_soterm8 = read "F5[1]"

zip1_sotid8 :: SOMetaUnifRelSoId s
zip1_sotid8 = relbwEqDGSoId (FSONode zip1_soterm8)

zip1_soterm9 :: SOMetatermF
zip1_soterm9 = read "F6[1]"

zip1_sotid9 :: SOMetaUnifRelSoId s
zip1_sotid9 = relbwEqDGSoId (FSONode zip1_soterm9)

zip1_soterm10 :: SOMetatermF
zip1_soterm10 = read "F7[1]"

zip1_sotid10 :: SOMetaUnifRelSoId s
zip1_sotid10 = relbwEqDGSoId (FSONode zip1_soterm10)

zip1_sig :: SOMetaSignature
zip1_sig = SOSignature (Signature [] [EnumProc.Empty,EnumProc.Empty,read "f1[2]" --> read "f2[2]" --> EnumProc.Empty] EnumProc.Empty) (read "F0[1]" --> read "F1[1]" --> read "F2[1]" --> read "F3[1]" --> read "F4[1]" --> read "F5[1]" --> read "F6[1]" --> read "F7[1]" --> EnumProc.Empty) EnumProc.Empty EnumProc.Empty

zip1_mudg1 :: StateT (RTestSOMetaUnifDGraph s) (ST s) _
zip1_mudg1 = do
	{
		on_dgraph (newEqDGSONode (FSONode zip1_soterm1));
		on_dgraph (newEqDGSONode (FSONode zip1_soterm2));
		on_dgraph (newEqDGSONode (FSONode zip1_soterm3));
		on_dgraph (newEqDGSONode (FSONode zip1_soterm4));
		on_dgraph (newEqDGSONode (FSONode zip1_soterm5));
		on_dgraph (newEqDGSONode (FSONode zip1_soterm6));
		on_dgraph (newEqDGSONode (FSONode zip1_soterm7));
		on_dgraph (newEqDGSONode (FSONode zip1_soterm8));
		on_dgraph (newEqDGSONode (FSONode zip1_soterm9));
		on_dgraph (newEqDGSONode (FSONode zip1_soterm10));
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
zip2_sotid1 = relbwEqDGSoId (FSONode zip2_soterm1)

zip2_soterm2 :: SOMetatermF
zip2_soterm2 = read "F1[1]"

zip2_sotid2 :: SOMetaUnifRelSoId s
zip2_sotid2 = relbwEqDGSoId (FSONode zip2_soterm2)

zip2_soterm3 :: SOMetatermF
zip2_soterm3 = read "F2[1]"

zip2_sotid3 :: SOMetaUnifRelSoId s
zip2_sotid3 = relbwEqDGSoId (FSONode zip2_soterm3)

zip2_soterm4 :: SOMetatermF
zip2_soterm4 = read "F3[1]"

zip2_sotid4 :: SOMetaUnifRelSoId s
zip2_sotid4 = relbwEqDGSoId (FSONode zip2_soterm4)

zip2_soterm5 :: SOMetatermF
zip2_soterm5 = read "F4[1]"

zip2_sotid5 :: SOMetaUnifRelSoId s
zip2_sotid5 = relbwEqDGSoId (FSONode zip2_soterm5)

zip2_soterm6 :: SOMetatermF
zip2_soterm6 = read "f0[1]"

zip2_sotid6 :: SOMetaUnifRelSoId s
zip2_sotid6 = relbwEqDGSoId (FSONode zip2_soterm6)

zip2_soterm7 :: SOMetatermF
zip2_soterm7 = read "f1[1]"

zip2_sotid7 :: SOMetaUnifRelSoId s
zip2_sotid7 = relbwEqDGSoId (FSONode zip2_soterm7)

zip2_sig :: SOMetaSignature
zip2_sig = SOSignature (Signature [] [EnumProc.Empty,read "f0[1]" --> read "f1[1]" --> EnumProc.Empty] EnumProc.Empty) (read "F0[1]" --> read "F1[1]" --> read "F2[1]" --> read "F3[1]" --> read "F4[1]" --> EnumProc.Empty) EnumProc.Empty EnumProc.Empty

zip2_mudg1 :: StateT (RTestSOMetaUnifDGraph s) (ST s) _
zip2_mudg1 = do
	{
		on_dgraph (newEqDGSONode (FSONode zip2_soterm1));
		on_dgraph (newEqDGSONode (FSONode zip2_soterm2));
		on_dgraph (newEqDGSONode (FSONode zip2_soterm3));
		on_dgraph (newEqDGSONode (FSONode zip2_soterm4));
		on_dgraph (newEqDGSONode (FSONode zip2_soterm5));
		on_dgraph (newEqDGSONode (FSONode zip2_soterm6));
		on_dgraph (newEqDGSONode (FSONode zip2_soterm7));
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
zip3_sotid6 = relbwEqDGSoId (FSONode zip3_soterm6)

zip3_soterm7 :: SOMetatermF
zip3_soterm7 = read "f1[1]"

zip3_sotid7 :: SOMetaUnifRelSoId s
zip3_sotid7 = relbwEqDGSoId (FSONode zip3_soterm7)

zip3_sig :: SOMetaSignature
zip3_sig = SOSignature (Signature [] [EnumProc.Empty,read "f0[1]" --> read "f1[1]" --> EnumProc.Empty] (read "x0" --> read "x1" --> read "x2" --> read "x3" --> read "x4" --> EnumProc.Empty)) EnumProc.Empty EnumProc.Empty EnumProc.Empty

zip3_mudg1 :: StateT (RTestSOMetaUnifDGraph s) (ST s) _
zip3_mudg1 = do
	{
		on_dgraph (newEqDGFONode zip3_term1);
		on_dgraph (newEqDGFONode zip3_term2);
		on_dgraph (newEqDGFONode zip3_term3);
		on_dgraph (newEqDGFONode zip3_term4);
		on_dgraph (newEqDGFONode zip3_term5);
		on_dgraph (newEqDGSONode (FSONode zip3_soterm6));
		on_dgraph (newEqDGSONode (FSONode zip3_soterm7));
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
zip4_sotid1 = relbwEqDGSoId (FSONode zip4_soterm1)

zip4_soterm2 :: SOMetatermF
zip4_soterm2 = read "f2[1]"

zip4_sotid2 :: SOMetaUnifRelSoId s
zip4_sotid2 = relbwEqDGSoId (FSONode zip4_soterm2)

zip4_soterm3 :: SOMetatermF
zip4_soterm3 = read "f3[1]"

zip4_sotid3 :: SOMetaUnifRelSoId s
zip4_sotid3 = relbwEqDGSoId (FSONode zip4_soterm3)

zip4_sig :: SOMetaSignature
zip4_sig = SOSignature (Signature [] [EnumProc.Empty,read "f1[1]" --> read "f2[1]" --> read "f3[1]" --> EnumProc.Empty] (read "x0" --> read "x1" --> read "x2" --> read "x3" --> EnumProc.Empty)) EnumProc.Empty EnumProc.Empty EnumProc.Empty

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
		on_dgraph (newEqDGSONode (FSONode zip4_soterm1));
		on_dgraph (newEqDGSONode (FSONode zip4_soterm2));
		on_dgraph (newEqDGSONode (FSONode zip4_soterm3));
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
simpproj1_tid1 = relbwEqDGSoId (FSONode simpproj1_term1)

simpproj1_term2 :: SOMetatermF
simpproj1_term2 = read "f2[0]"

simpproj1_tid2 :: SOMetaUnifRelSoId s
simpproj1_tid2 = relbwEqDGSoId (FSONode simpproj1_term2)

simpproj1_term3 :: SOMetatermF
simpproj1_term3 = read "f3[0]"

simpproj1_tid3 :: SOMetaUnifRelSoId s
simpproj1_tid3 = relbwEqDGSoId (FSONode simpproj1_term3)

simpproj1_term4 :: SOMetatermF
simpproj1_term4 = read "f4[0]"

simpproj1_tid4 :: SOMetaUnifRelSoId s
simpproj1_tid4 = relbwEqDGSoId (FSONode simpproj1_term4)

simpproj1_term5 :: SOMetatermF
simpproj1_term5 = read "f5[3]"

simpproj1_tid5 :: SOMetaUnifRelSoId s
simpproj1_tid5 = relbwEqDGSoId (FSONode simpproj1_term5)

simpproj1_term6 :: SOMetatermF
simpproj1_term6 = read "pi1"

simpproj1_tid6 :: SOMetaUnifRelSoId s
simpproj1_tid6 = relbwEqDGSoId (FSONode simpproj1_term6)

simpproj1_sig :: SOMetaSignature
simpproj1_sig = SOSignature (Signature [] [read "f1[0]" --> read "f2[0]" --> read "f3[0]" --> read "f4[0]" --> EnumProc.Empty,EnumProc.Empty,EnumProc.Empty,read "f5[3]" --> EnumProc.Empty] EnumProc.Empty) EnumProc.Empty EnumProc.Empty EnumProc.Empty

simpproj1_mudg1 :: StateT (RTestSOMetaUnifDGraph s) (ST s) _
simpproj1_mudg1 = do
	{
		on_dgraph (newEqDGSONode (FSONode simpproj1_term1));
		on_dgraph (newEqDGSONode (FSONode simpproj1_term2));
		on_dgraph (newEqDGSONode (FSONode simpproj1_term3));
		on_dgraph (newEqDGSONode (FSONode simpproj1_term4));
		on_dgraph (newEqDGSONode (FSONode simpproj1_term5));
		on_dgraph (newEqDGSONode (FSONode simpproj1_term6));
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
simpproj2_tid5 = relbwEqDGSoId (FSONode simpproj2_term5)

simpproj2_term6 :: SOMetatermF
simpproj2_term6 = read "pi1"

simpproj2_tid6 :: SOMetaUnifRelSoId s
simpproj2_tid6 = relbwEqDGSoId (FSONode simpproj2_term6)

simpproj2_sig :: SOMetaSignature
simpproj2_sig = SOSignature (Signature [] [read "f1[0]" --> read "f2[0]" --> read "f3[0]" --> read "f4[0]" --> EnumProc.Empty,EnumProc.Empty,EnumProc.Empty,read "f5[3]" --> EnumProc.Empty] EnumProc.Empty) EnumProc.Empty EnumProc.Empty EnumProc.Empty

simpproj2_mudg1 :: StateT (RTestSOMetaUnifDGraph s) (ST s) _
simpproj2_mudg1 = do
	{
		on_dgraph (newEqDGFONode simpproj2_term1);
		on_dgraph (newEqDGFONode simpproj2_term2);
		on_dgraph (newEqDGFONode simpproj2_term3);
		on_dgraph (newEqDGFONode simpproj2_term4);
		on_dgraph (newEqDGSONode (FSONode simpproj2_term5));
		on_dgraph (newEqDGSONode (FSONode simpproj2_term6));
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
dump1_sotid1 = relbwEqDGSoId (FSONode dump1_soterm1)

dump1_soterm2 :: SOMetatermF
dump1_soterm2 = read "F4[2]"

dump1_sotid2 :: SOMetaUnifRelSoId s
dump1_sotid2 = relbwEqDGSoId (FSONode dump1_soterm2)

dump1_soterm3 :: SOMetatermF
dump1_soterm3 = read "F5[2]"

dump1_sotid3 :: SOMetaUnifRelSoId s
dump1_sotid3 = relbwEqDGSoId (FSONode dump1_soterm3)

dump1_soterm4 :: SOMetatermF
dump1_soterm4 = read "F6[2]"

dump1_sotid4 :: SOMetaUnifRelSoId s
dump1_sotid4 = relbwEqDGSoId (FSONode dump1_soterm4)

dump1_exp1 :: SOMetaUnifFOExp
dump1_exp1 = read "F6[2](F4[2](F0[0](),F1[0]()),F5[2](F0[0](),F1[0]()))"

dump1_sig :: SOMetaSignature
dump1_sig = SOSignature (Signature [] [] EnumProc.Empty) (read "F0[0]" --> read "F1[0]" --> read "F2[0]" --> read "F3[2]" --> read "F4[2]" --> read "F5[2]" --> read "F6[2]" --> EnumProc.Empty) EnumProc.Empty EnumProc.Empty

dump1_mudg1 :: StateT (RTestSOMetaUnifDGraph s) (ST s) _
dump1_mudg1 = do
	{
		on_dgraph (newEqDGFONode dump1_term1);
		on_dgraph (newEqDGFONode dump1_term2);
		on_dgraph (newEqDGFONode dump1_term3);
		on_dgraph (newEqDGSONode (FSONode dump1_soterm1));
		on_dgraph (newEqDGSONode (FSONode dump1_soterm2));
		on_dgraph (newEqDGSONode (FSONode dump1_soterm3));
		on_dgraph (newEqDGSONode (FSONode dump1_soterm4));
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
dump2_tid1 = relbwEqDGSoId (FSONode dump2_term1)

dump2_term2 :: SOMetatermF
dump2_term2 = read "F1[0]"

dump2_tid2 :: SOMetaUnifRelSoId s
dump2_tid2 = relbwEqDGSoId (FSONode dump2_term2)

dump2_term3 :: SOMetatermF
dump2_term3 = read "F2[0]"

dump2_tid3 :: SOMetaUnifRelSoId s
dump2_tid3 = relbwEqDGSoId (FSONode dump2_term3)

dump2_soterm1 :: SOMetatermF
dump2_soterm1 = read "F3[2]"

dump2_sotid1 :: SOMetaUnifRelSoId s
dump2_sotid1 = relbwEqDGSoId (FSONode dump2_soterm1)

dump2_soterm2 :: SOMetatermF
dump2_soterm2 = read "F4[2]"

dump2_sotid2 :: SOMetaUnifRelSoId s
dump2_sotid2 = relbwEqDGSoId (FSONode dump2_soterm2)

dump2_soterm3 :: SOMetatermF
dump2_soterm3 = read "F5[2]"

dump2_sotid3 :: SOMetaUnifRelSoId s
dump2_sotid3 = relbwEqDGSoId (FSONode dump2_soterm3)

dump2_soterm4 :: SOMetatermF
dump2_soterm4 = read "F6[2]"

dump2_sotid4 :: SOMetaUnifRelSoId s
dump2_sotid4 = relbwEqDGSoId (FSONode dump2_soterm4)

dump2_exp1 :: SOMetaUnifSOExp
dump2_exp1 = read "F6[2]{F4[2]{F0[0],F1[0]},F5[2]{F0[0],F1[0]}}"

dump2_sig :: SOMetaSignature
dump2_sig = SOSignature (Signature [] [] EnumProc.Empty) (read "F0[0]" --> read "F1[0]" --> read "F2[0]" --> read "F3[2]" --> read "F4[2]" --> read "F5[2]" --> read "F6[2]" --> EnumProc.Empty) EnumProc.Empty EnumProc.Empty

dump2_mudg1 :: StateT (RTestSOMetaUnifDGraph s) (ST s) _
dump2_mudg1 = do
	{
		on_dgraph (newEqDGSONode (FSONode dump2_term1));
		on_dgraph (newEqDGSONode (FSONode dump2_term2));
		on_dgraph (newEqDGSONode (FSONode dump2_term3));
		on_dgraph (newEqDGSONode (FSONode dump2_soterm1));
		on_dgraph (newEqDGSONode (FSONode dump2_soterm2));
		on_dgraph (newEqDGSONode (FSONode dump2_soterm3));
		on_dgraph (newEqDGSONode (FSONode dump2_soterm4));
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
sotconsistency1_tid1 = relbwEqDGSoId (FSONode sotconsistency1_term1)

sotconsistency1_term2 :: SOMetatermF
sotconsistency1_term2 = read "f2[1]"

sotconsistency1_tid2 :: SOMetaUnifRelSoId s
sotconsistency1_tid2 = relbwEqDGSoId (FSONode sotconsistency1_term2)

sotconsistency1_sig :: SOMetaSignature
sotconsistency1_sig = SOSignature (Signature [] [EnumProc.Empty,read "f1[1]" --> read "f2[1]" --> EnumProc.Empty] EnumProc.Empty) EnumProc.Empty EnumProc.Empty EnumProc.Empty

sotconsistency1_mudg1 :: StateT (RTestSOMetaUnifDGraph s) (ST s) Bool
sotconsistency1_mudg1 = do
	{
		on_dgraph (newEqDGSONode (FSONode sotconsistency1_term1));
		on_dgraph (newEqDGSONode (FSONode sotconsistency1_term2));
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
sotconsistency2_tid1 = relbwEqDGSoId (FSONode sotconsistency2_term1)

sotconsistency2_term2 :: SOMetatermF
sotconsistency2_term2 = read "F2[1]"

sotconsistency2_tid2 :: SOMetaUnifRelSoId s
sotconsistency2_tid2 = relbwEqDGSoId (FSONode sotconsistency2_term2)

sotconsistency2_sig :: SOMetaSignature
sotconsistency2_sig = SOSignature (Signature [] [EnumProc.Empty,read "f1[1]" --> EnumProc.Empty] EnumProc.Empty) (read "F2[1]" --> EnumProc.Empty) EnumProc.Empty EnumProc.Empty

sotconsistency2_mudg1 :: StateT (RTestSOMetaUnifDGraph s) (ST s) Bool
sotconsistency2_mudg1 = do
	{
		on_dgraph (newEqDGSONode (FSONode sotconsistency2_term1));
		on_dgraph (newEqDGSONode (FSONode sotconsistency2_term2));
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
head_arity1_tid1 = relbwEqDGSoId (FSONode head_arity1_term1)

head_arity1_term2 :: SOMetatermF
head_arity1_term2 = read "f2[1]"

head_arity1_tid2 :: SOMetaUnifRelSoId s
head_arity1_tid2 = relbwEqDGSoId (FSONode head_arity1_term2)

head_arity1_term3 :: SOMetatermF
head_arity1_term3 = read "F3[4]"

head_arity1_tid3 :: SOMetaUnifRelSoId s
head_arity1_tid3 = relbwEqDGSoId (FSONode head_arity1_term3)

head_arity1_term4 :: SOMetatermF
head_arity1_term4 = read "f4[3]"

head_arity1_tid4 :: SOMetaUnifRelSoId s
head_arity1_tid4 = relbwEqDGSoId (FSONode head_arity1_term4)

head_arity1_term5 :: SOMetatermF
head_arity1_term5 = read "f5[1]"

head_arity1_tid5 :: SOMetaUnifRelSoId s
head_arity1_tid5 = relbwEqDGSoId (FSONode head_arity1_term5)

head_arity1_sig :: SOMetaSignature
head_arity1_sig = SOSignature (Signature [] [EnumProc.Empty,read "f1[1]" --> read "f2[1]" --> read "f5[1]" --> EnumProc.Empty, EnumProc.Empty, read "f4[3]" --> EnumProc.Empty] EnumProc.Empty) (read "F3[4]" --> EnumProc.Empty) EnumProc.Empty EnumProc.Empty

head_arity1_mudg1 :: StateT (RTestSOMetaUnifDGraph s) (ST s) Bool
head_arity1_mudg1 = do
	{
		on_dgraph (newEqDGSONode (FSONode head_arity1_term1));
		on_dgraph (newEqDGSONode (FSONode head_arity1_term2));
		on_dgraph (newEqDGSONode (FSONode head_arity1_term3));
		on_dgraph (newEqDGSONode (FSONode head_arity1_term4));
		on_dgraph (newEqDGSONode (FSONode head_arity1_term5));
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
target_arity1_tid1 = relbwEqDGSoId (FSONode target_arity1_term1)

target_arity1_term2 :: SOMetatermF
target_arity1_term2 = read "f2[1]"

target_arity1_tid2 :: SOMetaUnifRelSoId s
target_arity1_tid2 = relbwEqDGSoId (FSONode target_arity1_term2)

target_arity1_term3 :: SOMetatermF
target_arity1_term3 = read "f3[2]"

target_arity1_tid3 :: SOMetaUnifRelSoId s
target_arity1_tid3 = relbwEqDGSoId (FSONode target_arity1_term3)

target_arity1_sig :: SOMetaSignature
target_arity1_sig = SOSignature (Signature [] [EnumProc.Empty,read "f1[1]" --> read "f2[1]" --> EnumProc.Empty, read "f3[2]" --> EnumProc.Empty] EnumProc.Empty) EnumProc.Empty EnumProc.Empty EnumProc.Empty

target_arity1_mudg1 :: StateT (RTestSOMetaUnifDGraph s) (ST s) Bool
target_arity1_mudg1 = do
	{
		on_dgraph (newEqDGSONode (FSONode target_arity1_term1));
		on_dgraph (newEqDGSONode (FSONode target_arity1_term2));
		on_dgraph (newEqDGSONode (FSONode target_arity1_term3));
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
target_arity2_tid1 = relbwEqDGSoId (FSONode target_arity2_term1)

target_arity2_term2 :: SOMetatermF
target_arity2_term2 = read "f2[1]"

target_arity2_tid2 :: SOMetaUnifRelSoId s
target_arity2_tid2 = relbwEqDGSoId (FSONode target_arity2_term2)

target_arity2_term3 :: SOMetatermF
target_arity2_term3 = read "F3[1]"

target_arity2_tid3 :: SOMetaUnifRelSoId s
target_arity2_tid3 = relbwEqDGSoId (FSONode target_arity2_term3)

target_arity2_sig :: SOMetaSignature
target_arity2_sig = SOSignature (Signature [] [EnumProc.Empty,read "f2[1]" --> EnumProc.Empty, read "f1[2]" --> EnumProc.Empty] EnumProc.Empty) (read "F3[1]" --> EnumProc.Empty) EnumProc.Empty EnumProc.Empty

target_arity2_mudg1 :: StateT (RTestSOMetaUnifDGraph s) (ST s) Bool
target_arity2_mudg1 = do
	{
		on_dgraph (newEqDGSONode (FSONode target_arity2_term1));
		on_dgraph (newEqDGSONode (FSONode target_arity2_term2));
		on_dgraph (newEqDGSONode (FSONode target_arity2_term3));
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
target_arity3_tid1 = relbwEqDGSoId (FSONode target_arity3_term1)

target_arity3_term2 :: SOMetatermF
target_arity3_term2 = read "f2[1]"

target_arity3_tid2 :: SOMetaUnifRelSoId s
target_arity3_tid2 = relbwEqDGSoId (FSONode target_arity3_term2)

target_arity3_term3 :: SOMetatermF
target_arity3_term3 = read "F3[2]"

target_arity3_tid3 :: SOMetaUnifRelSoId s
target_arity3_tid3 = relbwEqDGSoId (FSONode target_arity3_term3)

target_arity3_sig :: SOMetaSignature
target_arity3_sig = SOSignature (Signature [] [EnumProc.Empty,read "f2[1]" --> EnumProc.Empty, read "f1[2]" --> EnumProc.Empty] EnumProc.Empty) (read "F3[2]" --> EnumProc.Empty) EnumProc.Empty EnumProc.Empty

target_arity3_mudg1 :: StateT (RTestSOMetaUnifDGraph s) (ST s) Bool
target_arity3_mudg1 = do
	{
		on_dgraph (newEqDGSONode (FSONode target_arity3_term1));
		on_dgraph (newEqDGSONode (FSONode target_arity3_term2));
		on_dgraph (newEqDGSONode (FSONode target_arity3_term3));
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
target_arity4_tid1 = relbwEqDGSoId (FSONode target_arity4_term1)

target_arity4_term2 :: SOMetatermF
target_arity4_term2 = read "f2[1]"

target_arity4_tid2 :: SOMetaUnifRelSoId s
target_arity4_tid2 = relbwEqDGSoId (FSONode target_arity4_term2)

target_arity4_term3 :: SOMetatermF
target_arity4_term3 = read "f3[2]"

target_arity4_tid3 :: SOMetaUnifRelSoId s
target_arity4_tid3 = relbwEqDGSoId (FSONode target_arity4_term3)

target_arity4_term4 :: SOMetatermF
target_arity4_term4 = read "F4[3]"

target_arity4_tid4 :: SOMetaUnifRelSoId s
target_arity4_tid4 = relbwEqDGSoId (FSONode target_arity4_term4)

target_arity4_term5 :: SOMetatermF
target_arity4_term5 = read "f5[1]"

target_arity4_tid5 :: SOMetaUnifRelSoId s
target_arity4_tid5 = relbwEqDGSoId (FSONode target_arity4_term5)

target_arity4_term6 :: SOMetatermF
target_arity4_term6 = read "F6[1]"

target_arity4_tid6 :: SOMetaUnifRelSoId s
target_arity4_tid6 = relbwEqDGSoId (FSONode target_arity4_term6)

target_arity4_sig :: SOMetaSignature
target_arity4_sig = SOSignature (Signature [] [EnumProc.Empty,read "f1[1]" --> read "f2[1]" --> read "f5[1]" --> EnumProc.Empty, read "f3[2]" --> EnumProc.Empty] EnumProc.Empty) (read "F4[3]" --> read "F6[1]" --> EnumProc.Empty) EnumProc.Empty EnumProc.Empty

target_arity4_mudg1 :: StateT (RTestSOMetaUnifDGraph s) (ST s) Bool
target_arity4_mudg1 = do
	{
		on_dgraph (newEqDGSONode (FSONode target_arity4_term1));
		on_dgraph (newEqDGSONode (FSONode target_arity4_term2));
		on_dgraph (newEqDGSONode (FSONode target_arity4_term3));
		on_dgraph (newEqDGSONode (FSONode target_arity4_term4));
		on_dgraph (newEqDGSONode (FSONode target_arity4_term5));
		on_dgraph (newEqDGSONode (FSONode target_arity4_term6));
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
occurs_check1_term1 = read "f1[1]"

occurs_check1_tid1 :: SOMetaUnifRelSoId s
occurs_check1_tid1 = relbwEqDGSoId (FSONode occurs_check1_term1)

occurs_check1_term2 :: SOMetatermF
occurs_check1_term2 = read "f2[1]"

occurs_check1_tid2 :: SOMetaUnifRelSoId s
occurs_check1_tid2 = relbwEqDGSoId (FSONode occurs_check1_term2)

occurs_check1_term3 :: SOMetatermF
occurs_check1_term3 = read "f3[1]"

occurs_check1_tid3 :: SOMetaUnifRelSoId s
occurs_check1_tid3 = relbwEqDGSoId (FSONode occurs_check1_term3)

occurs_check1_term4 :: SOMetatermF
occurs_check1_term4 = read "f4[1]"

occurs_check1_tid4 :: SOMetaUnifRelSoId s
occurs_check1_tid4 = relbwEqDGSoId (FSONode occurs_check1_term4)

occurs_check1_term5 :: SOMetatermF
occurs_check1_term5 = read "f5[1]"

occurs_check1_tid5 :: SOMetaUnifRelSoId s
occurs_check1_tid5 = relbwEqDGSoId (FSONode occurs_check1_term5)

occurs_check1_term6 :: SOMetatermF
occurs_check1_term6 = read "f6[1]"

occurs_check1_tid6 :: SOMetaUnifRelSoId s
occurs_check1_tid6 = relbwEqDGSoId (FSONode occurs_check1_term6)

occurs_check1_sig :: SOMetaSignature
occurs_check1_sig = SOSignature (Signature [] [EnumProc.Empty, read "f1[1]" --> read "f2[1]" --> read "f3[1]" --> read "f4[1]" --> read "f5[1]" --> read "f6[1]" --> EnumProc.Empty] EnumProc.Empty) EnumProc.Empty EnumProc.Empty EnumProc.Empty

occurs_check1_mudg1 :: StateT (RTestSOMetaUnifDGraph s) (ST s) Bool
occurs_check1_mudg1 = do
	{
		on_dgraph (newEqDGSONode (FSONode occurs_check1_term1));
		on_dgraph (newEqDGSONode (FSONode occurs_check1_term2));
		on_dgraph (newEqDGSONode (FSONode occurs_check1_term3));
		on_dgraph (newEqDGSONode (FSONode occurs_check1_term4));
		on_dgraph (newEqDGSONode (FSONode occurs_check1_term5));
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
factorize1_sotid1 = relbwEqDGSoId (FSONode factorize1_soterm1)

factorize1_sig :: SOMetaSignature
factorize1_sig = SOSignature (Signature [] [EnumProc.Empty, read "f1[1]" --> EnumProc.Empty] (read "x0" --> read "x1" --> read "x2" --> EnumProc.Empty)) EnumProc.Empty EnumProc.Empty EnumProc.Empty

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
factorize2_tid1 = relbwEqDGSoId (FSONode factorize2_term1)

factorize2_term2 :: SOMetatermF
factorize2_term2 = read "F1[1]"

factorize2_tid2 :: SOMetaUnifRelSoId s
factorize2_tid2 = relbwEqDGSoId (FSONode factorize2_term2)

factorize2_term3 :: SOMetatermF
factorize2_term3 = read "F2[1]"

factorize2_tid3 :: SOMetaUnifRelSoId s
factorize2_tid3 = relbwEqDGSoId (FSONode factorize2_term3)

factorize2_soterm1 :: SOMetatermF
factorize2_soterm1 = read "f1[1]"

factorize2_sotid1 :: SOMetaUnifRelSoId s
factorize2_sotid1 = relbwEqDGSoId (FSONode factorize2_soterm1)

factorize2_sig :: SOMetaSignature
factorize2_sig = SOSignature (Signature [] [EnumProc.Empty, read "f1[1]" --> EnumProc.Empty] EnumProc.Empty) (read "F0[1]" --> read "F1[1]" --> read "F2[1]" --> EnumProc.Empty) EnumProc.Empty EnumProc.Empty

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
factorize3_sotid1 = relbwEqDGSoId (FSONode factorize3_soterm1)

factorize3_soterm2 :: SOMetatermF
factorize3_soterm2 = read "f2[1]"

factorize3_sotid2 :: SOMetaUnifRelSoId s
factorize3_sotid2 = relbwEqDGSoId (FSONode factorize3_soterm2)

factorize3_sig :: SOMetaSignature
factorize3_sig = SOSignature (Signature [] [EnumProc.Empty, read "f1[1]" --> read "f2[1]" --> EnumProc.Empty] (read "x0" --> read "x1" --> read "x2" --> EnumProc.Empty)) EnumProc.Empty EnumProc.Empty EnumProc.Empty

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
factorize4_tid1 = relbwEqDGSoId (FSONode factorize4_term1)

factorize4_term2 :: SOMetatermF
factorize4_term2 = read "F1[1]"

factorize4_tid2 :: SOMetaUnifRelSoId s
factorize4_tid2 = relbwEqDGSoId (FSONode factorize4_term2)

factorize4_term3 :: SOMetatermF
factorize4_term3 = read "F2[1]"

factorize4_tid3 :: SOMetaUnifRelSoId s
factorize4_tid3 = relbwEqDGSoId (FSONode factorize4_term3)

factorize4_soterm1 :: SOMetatermF
factorize4_soterm1 = read "f1[1]"

factorize4_sotid1 :: SOMetaUnifRelSoId s
factorize4_sotid1 = relbwEqDGSoId (FSONode factorize4_soterm1)

factorize4_soterm2 :: SOMetatermF
factorize4_soterm2 = read "f2[1]"

factorize4_sotid2 :: SOMetaUnifRelSoId s
factorize4_sotid2 = relbwEqDGSoId (FSONode factorize4_soterm2)

factorize4_sig :: SOMetaSignature
factorize4_sig = SOSignature (Signature [] [EnumProc.Empty, read "f1[1]" --> read "f2[1]" --> EnumProc.Empty] EnumProc.Empty) (read "F0[1]" --> read "F1[1]" --> read "F2[1]" --> EnumProc.Empty) EnumProc.Empty EnumProc.Empty

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
factorize5_sotid1 = relbwEqDGSoId (FSONode factorize5_soterm1)

factorize5_soterm2 :: SOMetatermF
factorize5_soterm2 = read "f2[1]"

factorize5_sotid2 :: SOMetaUnifRelSoId s
factorize5_sotid2 = relbwEqDGSoId (FSONode factorize5_soterm2)

factorize5_sig :: SOMetaSignature
factorize5_sig = SOSignature (Signature [] [EnumProc.Empty, read "f1[1]" --> read "f2[1]" --> EnumProc.Empty] (read "x0" --> read "x1" --> read "x2" --> read "x3" --> read "x4" --> read "x5" --> read "x6" --> read "x7" --> read "x8" --> EnumProc.Empty)) EnumProc.Empty EnumProc.Empty EnumProc.Empty

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
factorize6_sotid1 = relbwEqDGSoId (FSONode factorize6_soterm1)

factorize6_soterm2 :: SOMetatermF
factorize6_soterm2 = read "F0[2]"

factorize6_sotid2 :: SOMetaUnifRelSoId s
factorize6_sotid2 = relbwEqDGSoId (FSONode factorize6_soterm2)

factorize6_soterm3 :: SOMetatermF
factorize6_soterm3 = read "f1[1]{pi1}"

factorize6_soterm4 :: SOMetatermF
factorize6_soterm4 = read "F1[2]"

factorize6_exp1 :: SOMetaUnifSOExp
factorize6_exp1 = read "f1[1]{F1[2]}"

factorize6_exp2 :: SOMetaUnifFOExp
factorize6_exp2 = read "F1[2](u0 x1, u0 x2)"

factorize6_sig :: SOMetaSignature
factorize6_sig = SOSignature (Signature [] [EnumProc.Empty, read "f1[1]" --> EnumProc.Empty] (read "x0" --> read "x1" --> read "x2" --> read "x3" --> EnumProc.Empty)) (read "F0[2]" --> EnumProc.Empty) EnumProc.Empty EnumProc.Empty

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
factorize7_sotid1 = relbwEqDGSoId (FSONode factorize7_soterm1)

factorize7_soterm2 :: SOMetatermF
factorize7_soterm2 = read "F0[1]"

factorize7_sotid2 :: SOMetaUnifRelSoId s
factorize7_sotid2 = relbwEqDGSoId (FSONode factorize7_soterm2)

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
factorize7_sig = SOSignature (Signature [] [EnumProc.Empty, read "f1[2]" --> EnumProc.Empty] (read "x0" --> read "x1" --> read "x2" --> read "x3" --> EnumProc.Empty)) (read "F0[1]" --> EnumProc.Empty) EnumProc.Empty EnumProc.Empty

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
factorize8_sotid1 = relbwEqDGSoId (FSONode factorize8_soterm1)

factorize8_soterm2 :: SOMetatermF
factorize8_soterm2 = read "F0[15]"

factorize8_sotid2 :: SOMetaUnifRelSoId s
factorize8_sotid2 = relbwEqDGSoId (FSONode factorize8_soterm2)

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
factorize8_sig = SOSignature (Signature [] [EnumProc.Empty, read "f1[2]" --> EnumProc.Empty] (read "x0" --> read "x1" --> read "x2" --> read "x3" --> EnumProc.Empty)) (read "F0[15]" --> EnumProc.Empty) EnumProc.Empty EnumProc.Empty

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

-- This number is low because of the performance properties of the algorithm.
factorize9_tests_n :: Int
factorize9_tests_n = 5

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
factorize9_sotid1 = relbwEqDGSoId (FSONode factorize9_soterm1)

factorize9_soterm2 :: SOMetatermF
factorize9_soterm2 = read "f2[2]"

factorize9_sotid2 :: SOMetaUnifRelSoId s
factorize9_sotid2 = relbwEqDGSoId (FSONode factorize9_soterm2)

factorize9_soterm3 :: SOMetatermF
factorize9_soterm3 = read "F0[2]"

factorize9_sotid3 :: SOMetaUnifRelSoId s
factorize9_sotid3 = relbwEqDGSoId (FSONode factorize9_soterm3)

factorize9_soterm4 :: SOMetatermF
factorize9_soterm4 = read "F1[1]"

factorize9_sotid4 :: SOMetaUnifRelSoId s
factorize9_sotid4 = relbwEqDGSoId (FSONode factorize9_soterm4)

factorize9_exp1 :: SOMetaUnifSOExp
factorize9_exp1 = read "f1[1]{F3[2]}"

factorize9_exp2 :: SOMetaUnifSOExp
factorize9_exp2 = read "pi0"

factorize9_exp3 :: SOMetaUnifSOExp
factorize9_exp3 = read "f2[1]{F3[2]}"

factorize9_sig :: SOMetaSignature
factorize9_sig = SOSignature (Signature [] [EnumProc.Empty, read "f1[1]" --> read "f2[1]" --> EnumProc.Empty, read "f3[2]" --> EnumProc.Empty] (read "x0" --> read "x1" --> read "x2" --> EnumProc.Empty)) (read "F0[2]" --> read "F1[1]" --> EnumProc.Empty) EnumProc.Empty EnumProc.Empty

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
factorize9_t5 = check_min_as "Checking there are at least five solutions after normalizing" 5 factorize9_as5

-- These tests are fairly specific and informed by the algorithm results themselves, but this is unavoidable given the performance issues of the algorithm.
factorize9_t6 :: AutomatedTest
factorize9_t6 = check_all_resuvdg factorize9_tests_n "Checking that F0 is never equivalent to f{F3[2]} after quasinormalizing" (\title -> \st -> check_not_soexp factorize9_sig title st factorize9_exp1 factorize9_soterm3) factorize9_as4

factorize9_t7 :: AutomatedTest
factorize9_t7 = check_all_resuvdg factorize9_tests_n "Checking that F0 is never equivalent to pi0 after quasinormalizing" (\title -> \st -> check_not_soexp factorize9_sig title st factorize9_exp2 factorize9_soterm3) factorize9_as4

factorize9_t8 :: AutomatedTest
factorize9_t8 = check_any_resuvdg factorize9_tests_n "Checking that F0 is sometimes equivalent to f{F3[2]} after normalizing" (\title -> \st -> check_soexp factorize9_sig title st factorize9_exp1 factorize9_soterm3) factorize9_as5

factorize9_t9 :: AutomatedTest
factorize9_t9 = check_any_resuvdg factorize9_tests_n "Checking that F0 is sometimes not equivalent to f{F3[2]} after normalizing" (\title -> \st -> check_not_soexp factorize9_sig title st factorize9_exp1 factorize9_soterm3) factorize9_as5

factorize9_t10 :: AutomatedTest
factorize9_t10 = check_any_resuvdg factorize9_tests_n "Checking that F0 is sometimes equivalent to pi0 after normalizing" (\title -> \st -> check_soexp factorize9_sig title st factorize9_exp2 factorize9_soterm3) factorize9_as5

factorize9_t11 :: AutomatedTest
factorize9_t11 = check_any_resuvdg factorize9_tests_n "Checking that F0 is sometimes not equivalent to pi0 after normalizing" (\title -> \st -> check_not_soexp factorize9_sig title st factorize9_exp2 factorize9_soterm3) factorize9_as5

factorize9_t12 :: AutomatedTest
factorize9_t12 = check_all_resuvdg factorize9_tests_n "Checking that F0 is never equivalent to g{F3[2]} after quasinormalizing" (\title -> \st -> check_not_soexp factorize9_sig title st factorize9_exp3 factorize9_soterm3) factorize9_as4

factorize9_t13 :: AutomatedTest
factorize9_t13 = check_any_resuvdg factorize9_tests_n "Checking that F0 is sometimes equivalent to g{F3[2]} after normalizing" (\title -> \st -> check_soexp factorize9_sig title st factorize9_exp3 factorize9_soterm3) factorize9_as5

factorize9_t14 :: AutomatedTest
factorize9_t14 = check_any_resuvdg factorize9_tests_n "Checking that F0 is sometimes not equivalent to g{F3[2]} after normalizing" (\title -> \st -> check_not_soexp factorize9_sig title st factorize9_exp3 factorize9_soterm3) factorize9_as5

factorize9_tests :: String
factorize9_tests = combine_test_results [factorize9_t1,factorize9_t2,factorize9_t3,factorize9_t4,factorize9_t5,factorize9_t6,factorize9_t7,factorize9_t8,factorize9_t9,factorize9_t10,factorize9_t11,factorize9_t12,factorize9_t13,factorize9_t14]

factorize10_tests_n :: Int
factorize10_tests_n = 20

factorize10_term1 :: SOMetaTermDependant
factorize10_term1 = read "u0 x0"

factorize10_tid1 :: SOMetaUnifRelFoId s
factorize10_tid1 = relbwEqDGFoId factorize10_term1

factorize10_term2 :: SOMetaTermDependant
factorize10_term2 = read "u0 x1"

factorize10_tid2 :: SOMetaUnifRelFoId s
factorize10_tid2 = relbwEqDGFoId factorize10_term2

factorize10_term3 :: SOMetaTermDependant
factorize10_term3 = read "u0 x2"

factorize10_tid3 :: SOMetaUnifRelFoId s
factorize10_tid3 = relbwEqDGFoId factorize10_term3

factorize10_term4 :: SOMetaTermDependant
factorize10_term4 = read "u0 x3"

factorize10_tid4 :: SOMetaUnifRelFoId s
factorize10_tid4 = relbwEqDGFoId factorize10_term4

factorize10_term5 :: SOMetaTermDependant
factorize10_term5 = read "u0 x4"

factorize10_tid5 :: SOMetaUnifRelFoId s
factorize10_tid5 = relbwEqDGFoId factorize10_term5

factorize10_term6 :: SOMetaTermDependant
factorize10_term6 = read "u0 x5"

factorize10_tid6 :: SOMetaUnifRelFoId s
factorize10_tid6 = relbwEqDGFoId factorize10_term6

factorize10_term7 :: SOMetaTermDependant
factorize10_term7 = read "u0 x6"

factorize10_tid7 :: SOMetaUnifRelFoId s
factorize10_tid7 = relbwEqDGFoId factorize10_term7

factorize10_term8 :: SOMetaTermDependant
factorize10_term8 = read "u0 x7"

factorize10_tid8 :: SOMetaUnifRelFoId s
factorize10_tid8 = relbwEqDGFoId factorize10_term8

factorize10_term9 :: SOMetaTermDependant
factorize10_term9 = read "u0 x8"

factorize10_tid9 :: SOMetaUnifRelFoId s
factorize10_tid9 = relbwEqDGFoId factorize10_term9

factorize10_soterm1 :: SOMetatermF
factorize10_soterm1 = read "f1[1]"

factorize10_sotid1 :: SOMetaUnifRelSoId s
factorize10_sotid1 = relbwEqDGSoId (FSONode factorize10_soterm1)

factorize10_soterm2 :: SOMetatermF
factorize10_soterm2 = read "F0[1]"

factorize10_sotid2 :: SOMetaUnifRelSoId s
factorize10_sotid2 = relbwEqDGSoId (FSONode factorize10_soterm2)

factorize10_soterm3 :: SOMetatermF
factorize10_soterm3 = read "F1[1]"

factorize10_sotid3 :: SOMetaUnifRelSoId s
factorize10_sotid3 = relbwEqDGSoId (FSONode factorize10_soterm3)

factorize10_soterm4 :: SOMetatermF
factorize10_soterm4 = read "F2[1]"

factorize10_sotid4 :: SOMetaUnifRelSoId s
factorize10_sotid4 = relbwEqDGSoId (FSONode factorize10_soterm4)

factorize10_soterm5 :: SOMetatermF
factorize10_soterm5 = read "F3[1]"

factorize10_sotid5 :: SOMetaUnifRelSoId s
factorize10_sotid5 = relbwEqDGSoId (FSONode factorize10_soterm5)

factorize10_soterm6 :: SOMetatermF
factorize10_soterm6 = read "F4[1]"

factorize10_sotid6 :: SOMetaUnifRelSoId s
factorize10_sotid6 = relbwEqDGSoId (FSONode factorize10_soterm6)

factorize10_exp1 :: SOMetaUnifSOExp
factorize10_exp1 = read "f1[1]{F7[1]}"

factorize10_exp2 :: SOMetaUnifSOExp
factorize10_exp2 = read "pi0"

factorize10_sig :: SOMetaSignature
factorize10_sig = SOSignature (Signature [] [EnumProc.Empty, read "f1[1]" --> EnumProc.Empty] (read "x0" --> read "x1" --> read "x2" --> read "x3" --> read "x4" --> read "x5" --> read "x6" --> read "x7" --> read "x8" --> EnumProc.Empty)) (read "F0[1]" --> read "F1[1]" --> read "F2[1]" --> read "F3[1]" --> read "F4[1]" --> EnumProc.Empty) EnumProc.Empty EnumProc.Empty

factorize10_mudg1 :: RSOMetaUnifDGraph
factorize10_mudg1 = RESUnifVDGraph (snd <$> runStateT (mzoom lens_esunifdgraph_dgraph (do
	{
		newEqDGFOEdge factorize10_sotid2 [factorize10_tid1] factorize10_tid3;
		newEqDGFOEdge factorize10_sotid3 [factorize10_tid2] factorize10_tid3;
		newEqDGFOEdge factorize10_sotid4 [factorize10_tid3] factorize10_tid5;
		newEqDGFOEdge factorize10_sotid1 [factorize10_tid4] factorize10_tid5;
		newEqDGFOEdge factorize10_sotid5 [factorize10_tid8] factorize10_tid6;
		newEqDGFOEdge factorize10_sotid6 [factorize10_tid9] factorize10_tid6;
		newEqDGFOEdge factorize10_sotid1 [factorize10_tid5] factorize10_tid7;
		newEqDGFOEdge factorize10_sotid1 [factorize10_tid6] factorize10_tid7
	})) (emptyVDGraph factorize10_sig))

factorize10_as1 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize10_as1 = ImplicitAS factorize10_mudg1

factorize10_as2 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize10_as2 = metaunif_prenormalize factorize10_as1

factorize10_as3 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize10_as3 = metaunif_seminormalize factorize10_as1

factorize10_as4 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize10_as4 = metaunif_quasinormalize factorize10_as1

factorize10_as5 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize10_as5 = metaunif_normalize factorize10_as1

factorize10_t1 :: AutomatedTest
factorize10_t1 = check_exactly_as "Checking there is exactly one solution before" 1 factorize10_as1

factorize10_t2 :: AutomatedTest
factorize10_t2 = check_exactly_as "Checking there is exactly one solution after prenormalizing" 1 factorize10_as2

factorize10_t3 :: AutomatedTest
factorize10_t3 = check_exactly_as "Checking there is exactly one solution after seminormalizing" 1 factorize10_as3

factorize10_t4 :: AutomatedTest
factorize10_t4 = check_min_as "Checking there are at least two solutions after quasinormalizing" 2 factorize10_as4

factorize10_t5 :: AutomatedTest
factorize10_t5 = check_min_as "Checking there are at least five solutions after normalizing" 5 factorize10_as5

-- These tests are fairly specific and informed by the algorithm results themselves, but this is unavoidable given the performance issues of the algorithm.
factorize10_t6 :: AutomatedTest
factorize10_t6 = check_all_resuvdg factorize10_tests_n "Checking that F0 is never equivalent to f{F7[1]} after seminormalizing" (\title -> \st -> check_not_soexp factorize10_sig title st factorize10_exp1 factorize10_soterm2) factorize10_as3

factorize10_t7 :: AutomatedTest
factorize10_t7 = check_all_resuvdg factorize10_tests_n "Checking that F0 is never equivalent to pi0 after seminormalizing" (\title -> \st -> check_not_soexp factorize10_sig title st factorize10_exp2 factorize10_soterm2) factorize10_as3

factorize10_t8 :: AutomatedTest
factorize10_t8 = check_any_resuvdg factorize10_tests_n "Checking that F0 is sometimes equivalent to f{F7[2]} after quasinormalizing" (\title -> \st -> check_soexp factorize10_sig title st factorize10_exp1 factorize10_soterm2) factorize10_as4

factorize10_t9 :: AutomatedTest
factorize10_t9 = check_any_resuvdg factorize10_tests_n "Checking that F0 is sometimes not equivalent to f{F7[2]} after quasinormalizing" (\title -> \st -> check_not_soexp factorize10_sig title st factorize10_exp1 factorize10_soterm2) factorize10_as4

factorize10_t10 :: AutomatedTest
factorize10_t10 = check_any_resuvdg factorize10_tests_n "Checking that F0 is sometimes equivalent to pi0 after quasinormalizing" (\title -> \st -> check_soexp factorize10_sig title st factorize10_exp2 factorize10_soterm2) factorize10_as4

factorize10_t11 :: AutomatedTest
factorize10_t11 = check_any_resuvdg factorize10_tests_n "Checking that F0 is sometimes not equivalent to pi0 after quasinormalizing" (\title -> \st -> check_not_soexp factorize10_sig title st factorize10_exp2 factorize10_soterm2) factorize10_as4

factorize10_t12 :: AutomatedTest
factorize10_t12 = check_any_resuvdg factorize10_tests_n "Checking that F0 is sometimes equivalent to f{F7[2]} after normalizing" (\title -> \st -> check_soexp factorize10_sig title st factorize10_exp1 factorize10_soterm2) factorize10_as5

factorize10_t13 :: AutomatedTest
factorize10_t13 = check_any_resuvdg factorize10_tests_n "Checking that F0 is sometimes not equivalent to f{F7[2]} after normalizing" (\title -> \st -> check_not_soexp factorize10_sig title st factorize10_exp1 factorize10_soterm2) factorize10_as5

factorize10_t14 :: AutomatedTest
factorize10_t14 = check_any_resuvdg factorize10_tests_n "Checking that F0 is sometimes equivalent to pi0 after normalizing" (\title -> \st -> check_soexp factorize10_sig title st factorize10_exp2 factorize10_soterm2) factorize10_as5

factorize10_t15 :: AutomatedTest
factorize10_t15 = check_any_resuvdg factorize10_tests_n "Checking that F0 is sometimes not equivalent to pi0 after normalizing" (\title -> \st -> check_not_soexp factorize10_sig title st factorize10_exp2 factorize10_soterm2) factorize10_as5

factorize10_tests :: String
factorize10_tests = combine_test_results [factorize10_t1,factorize10_t2,factorize10_t3,factorize10_t4,factorize10_t5,factorize10_t6,factorize10_t7,factorize10_t8,factorize10_t9,factorize10_t10,factorize10_t11,factorize10_t12,factorize10_t13,factorize10_t14,factorize10_t15]

factorize11_tests_n :: Int
factorize11_tests_n = 1000

factorize11_soterm1 :: SOMetatermF
factorize11_soterm1 = read "f1[1]"

factorize11_sotid1 :: SOMetaUnifRelSoId s
factorize11_sotid1 = relbwEqDGSoId (FSONode factorize11_soterm1)

factorize11_soterm2 :: SOMetatermF
factorize11_soterm2 = read "F0[1]"

factorize11_sotid2 :: SOMetaUnifRelSoId s
factorize11_sotid2 = relbwEqDGSoId (FSONode factorize11_soterm2)

factorize11_soterm3 :: SOMetatermF
factorize11_soterm3 = read "pi0"

factorize11_sotid3 :: SOMetaUnifRelSoId s
factorize11_sotid3 = relbwEqDGSoId (FSONode factorize11_soterm3)

factorize11_sig :: SOMetaSignature
factorize11_sig = SOSignature (Signature [] [EnumProc.Empty, read "f1[1]" --> EnumProc.Empty] EnumProc.Empty) (read "F0[1]" --> EnumProc.Empty) EnumProc.Empty EnumProc.Empty

factorize11_mudg1 :: RSOMetaUnifDGraph
factorize11_mudg1 = RESUnifVDGraph (snd <$> runStateT (mzoom lens_esunifdgraph_dgraph (do
	{
		newEqDGSOEdge factorize11_sotid2 [factorize11_sotid1] factorize11_sotid1		
	})) (emptyVDGraph factorize11_sig))

factorize11_as1 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize11_as1 = ImplicitAS factorize11_mudg1

factorize11_as2 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize11_as2 = metaunif_prenormalize factorize11_as1

factorize11_as3 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize11_as3 = metaunif_seminormalize factorize11_as1

factorize11_as4 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize11_as4 = metaunif_quasinormalize factorize11_as1

factorize11_as5 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize11_as5 = metaunif_normalize factorize11_as1

factorize11_t1 :: AutomatedTest
factorize11_t1 = check_exactly_as "Checking there is exactly one solution before" 1 factorize11_as1

factorize11_t2 :: AutomatedTest
factorize11_t2 = check_exactly_as "Checking there is exactly one solution after prenormalizing" 1 factorize11_as2

factorize11_t3 :: AutomatedTest
factorize11_t3 = check_exactly_as "Checking there is exactly one solution after seminormalizing" 1 factorize11_as3

factorize11_t4 :: AutomatedTest
factorize11_t4 = check_exactly_as "Checking there is exactly one solution after quasinormalizing" 1 factorize11_as4

factorize11_t5 :: AutomatedTest
factorize11_t5 = check_exactly_as "Checking there is exactly one solution after normalizing" 1 factorize11_as5

factorize11_t6 :: AutomatedTest
factorize11_t6 = check_all_resuvdg factorize11_tests_n "Checking that F0 is never equivalent to pi0 before" (\title -> \st -> check_not_soequiv factorize11_sig title st factorize11_soterm2 factorize11_soterm3) factorize11_as1

factorize11_t7 :: AutomatedTest
factorize11_t7 = check_all_resuvdg factorize11_tests_n "Checking that F0 is never equivalent to pi0 after prenormalizing" (\title -> \st -> check_not_soequiv factorize11_sig title st factorize11_soterm2 factorize11_soterm3) factorize11_as2

factorize11_t8 :: AutomatedTest
factorize11_t8 = check_all_resuvdg factorize11_tests_n "Checking that F0 is never equivalent to pi0 after seminormalizing" (\title -> \st -> check_not_soequiv factorize11_sig title st factorize11_soterm2 factorize11_soterm3) factorize11_as3

factorize11_t9 :: AutomatedTest
factorize11_t9 = check_all_resuvdg factorize11_tests_n "Checking that F0 is always equivalent to pi0 after quasinormalizing" (\title -> \st -> check_soequiv factorize11_sig title st factorize11_soterm2 factorize11_soterm3) factorize11_as4

factorize11_t10 :: AutomatedTest
factorize11_t10 = check_all_resuvdg factorize11_tests_n "Checking that F0 is always equivalent to pi0 after normalizing" (\title -> \st -> check_soequiv factorize11_sig title st factorize11_soterm2 factorize11_soterm3) factorize11_as5

factorize11_tests :: String
factorize11_tests = combine_test_results [factorize11_t1,factorize11_t2,factorize11_t3,factorize11_t4,factorize11_t5,factorize11_t6,factorize11_t7,factorize11_t8,factorize11_t9,factorize11_t10]

factorize12_tests_n :: Int
factorize12_tests_n = 1000

factorize12_soterm1 :: SOMetatermF
factorize12_soterm1 = read "f1[1]"

factorize12_sotid1 :: SOMetaUnifRelSoId s
factorize12_sotid1 = relbwEqDGSoId (FSONode factorize12_soterm1)

factorize12_soterm2 :: SOMetatermF
factorize12_soterm2 = read "F0[1]"

factorize12_sotid2 :: SOMetaUnifRelSoId s
factorize12_sotid2 = relbwEqDGSoId (FSONode factorize12_soterm2)

factorize12_soterm3 :: SOMetatermF
factorize12_soterm3 = read "f2[1]"

factorize12_sotid3 :: SOMetaUnifRelSoId s
factorize12_sotid3 = relbwEqDGSoId (FSONode factorize12_soterm3)

factorize12_sig :: SOMetaSignature
factorize12_sig = SOSignature (Signature [] [EnumProc.Empty, read "f1[1]" --> read "f2[1]" --> EnumProc.Empty] EnumProc.Empty) (read "F0[1]" --> EnumProc.Empty) EnumProc.Empty EnumProc.Empty

factorize12_mudg1 :: RSOMetaUnifDGraph
factorize12_mudg1 = RESUnifVDGraph (snd <$> runStateT (mzoom lens_esunifdgraph_dgraph (do
	{
		newEqDGSOEdge factorize12_sotid2 [factorize12_sotid3] factorize12_sotid1		
	})) (emptyVDGraph factorize12_sig))

factorize12_as1 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize12_as1 = ImplicitAS factorize12_mudg1

factorize12_as2 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize12_as2 = metaunif_prenormalize factorize12_as1

factorize12_as3 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize12_as3 = metaunif_seminormalize factorize12_as1

factorize12_as4 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize12_as4 = metaunif_quasinormalize factorize12_as1

factorize12_as5 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize12_as5 = metaunif_normalize factorize12_as1

factorize12_t1 :: AutomatedTest
factorize12_t1 = check_exactly_as "Checking there is exactly one solution before" 1 factorize12_as1

factorize12_t2 :: AutomatedTest
factorize12_t2 = check_exactly_as "Checking there is exactly one solution after prenormalizing" 1 factorize12_as2

factorize12_t3 :: AutomatedTest
factorize12_t3 = check_exactly_as "Checking there is exactly one solution after seminormalizing" 1 factorize12_as3

factorize12_t4 :: AutomatedTest
factorize12_t4 = check_exactly_as "Checking there are no solutions after quasinormalizing" 0 factorize12_as4

factorize12_t5 :: AutomatedTest
factorize12_t5 = check_exactly_as "Checking there are no solutions after normalizing" 0 factorize12_as5

factorize12_tests :: String
factorize12_tests = combine_test_results [factorize12_t1,factorize12_t2,factorize12_t3,factorize12_t4,factorize12_t5]

factorize13_tests_n :: Int
factorize13_tests_n = 1000

factorize13_soterm1 :: SOMetatermF
factorize13_soterm1 = read "f1[1]"

factorize13_sotid1 :: SOMetaUnifRelSoId s
factorize13_sotid1 = relbwEqDGSoId (FSONode factorize13_soterm1)

factorize13_soterm2 :: SOMetatermF
factorize13_soterm2 = read "F0[1]"

factorize13_sotid2 :: SOMetaUnifRelSoId s
factorize13_sotid2 = relbwEqDGSoId (FSONode factorize13_soterm2)

factorize13_soterm3 :: SOMetatermF
factorize13_soterm3 = read "pi0"

factorize13_sotid3 :: SOMetaUnifRelSoId s
factorize13_sotid3 = relbwEqDGSoId (FSONode factorize13_soterm3)

factorize13_sig :: SOMetaSignature
factorize13_sig = SOSignature (Signature [] [EnumProc.Empty, read "f1[1]" --> EnumProc.Empty] EnumProc.Empty) (read "F0[1]" --> EnumProc.Empty) EnumProc.Empty EnumProc.Empty

factorize13_mudg1 :: RSOMetaUnifDGraph
factorize13_mudg1 = RESUnifVDGraph (snd <$> runStateT (mzoom lens_esunifdgraph_dgraph (do
	{
		newEqDGSOEdge factorize13_sotid1 [factorize13_sotid2] factorize13_sotid1		
	})) (emptyVDGraph factorize13_sig))

factorize13_as1 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize13_as1 = ImplicitAS factorize13_mudg1

factorize13_as2 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize13_as2 = metaunif_prenormalize factorize13_as1

factorize13_as3 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize13_as3 = metaunif_seminormalize factorize13_as1

factorize13_as4 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize13_as4 = metaunif_quasinormalize factorize13_as1

factorize13_as5 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize13_as5 = metaunif_normalize factorize13_as1

factorize13_t1 :: AutomatedTest
factorize13_t1 = check_exactly_as "Checking there is exactly one solution before" 1 factorize13_as1

factorize13_t2 :: AutomatedTest
factorize13_t2 = check_exactly_as "Checking there is exactly one solution after prenormalizing" 1 factorize13_as2

factorize13_t3 :: AutomatedTest
factorize13_t3 = check_exactly_as "Checking there is exactly one solution after seminormalizing" 1 factorize13_as3

factorize13_t4 :: AutomatedTest
factorize13_t4 = check_exactly_as "Checking there is exactly one solution after quasinormalizing" 1 factorize13_as4

factorize13_t5 :: AutomatedTest
factorize13_t5 = check_exactly_as "Checking there is exactly one solution after normalizing" 1 factorize13_as5

factorize13_t6 :: AutomatedTest
factorize13_t6 = check_all_resuvdg factorize13_tests_n "Checking that F0 is never equivalent to pi0 before" (\title -> \st -> check_not_soequiv factorize13_sig title st factorize13_soterm2 factorize13_soterm3) factorize13_as1

factorize13_t7 :: AutomatedTest
factorize13_t7 = check_all_resuvdg factorize13_tests_n "Checking that F0 is never equivalent to pi0 after prenormalizing" (\title -> \st -> check_not_soequiv factorize13_sig title st factorize13_soterm2 factorize13_soterm3) factorize13_as2

factorize13_t8 :: AutomatedTest
factorize13_t8 = check_all_resuvdg factorize13_tests_n "Checking that F0 is never equivalent to pi0 after seminormalizing" (\title -> \st -> check_not_soequiv factorize13_sig title st factorize13_soterm2 factorize13_soterm3) factorize13_as3

factorize13_t9 :: AutomatedTest
factorize13_t9 = check_all_resuvdg factorize13_tests_n "Checking that F0 is always equivalent to pi0 after quasinormalizing" (\title -> \st -> check_soequiv factorize13_sig title st factorize13_soterm2 factorize13_soterm3) factorize13_as4

factorize13_t10 :: AutomatedTest
factorize13_t10 = check_all_resuvdg factorize13_tests_n "Checking that F0 is always equivalent to pi0 after normalizing" (\title -> \st -> check_soequiv factorize13_sig title st factorize13_soterm2 factorize13_soterm3) factorize13_as5

factorize13_tests :: String
factorize13_tests = combine_test_results [factorize13_t1,factorize13_t2,factorize13_t3,factorize13_t4,factorize13_t5,factorize13_t6,factorize13_t7,factorize13_t8,factorize13_t9,factorize13_t10]

factorize14_tests_n :: Int
factorize14_tests_n = 1000

factorize14_soterm1 :: SOMetatermF
factorize14_soterm1 = read "f1[1]"

factorize14_sotid1 :: SOMetaUnifRelSoId s
factorize14_sotid1 = relbwEqDGSoId (FSONode factorize14_soterm1)

factorize14_soterm2 :: SOMetatermF
factorize14_soterm2 = read "F0[1]"

factorize14_sotid2 :: SOMetaUnifRelSoId s
factorize14_sotid2 = relbwEqDGSoId (FSONode factorize14_soterm2)

factorize14_soterm3 :: SOMetatermF
factorize14_soterm3 = read "F1[1]"

factorize14_sotid3 :: SOMetaUnifRelSoId s
factorize14_sotid3 = relbwEqDGSoId (FSONode factorize14_soterm3)

factorize14_soterm4 :: SOMetatermF
factorize14_soterm4 = read "pi0"

factorize14_sotid4 :: SOMetaUnifRelSoId s
factorize14_sotid4 = relbwEqDGSoId (FSONode factorize14_soterm4)

factorize14_exp1 :: SOMetaUnifSOExp
factorize14_exp1 = read "f1[1]{pi0}"

factorize14_sig :: SOMetaSignature
factorize14_sig = SOSignature (Signature [] [EnumProc.Empty, read "f1[1]" --> EnumProc.Empty] EnumProc.Empty) (read "F0[1]" --> read "F1[1]" --> EnumProc.Empty) EnumProc.Empty EnumProc.Empty

factorize14_mudg1 :: RSOMetaUnifDGraph
factorize14_mudg1 = RESUnifVDGraph (snd <$> runStateT (mzoom lens_esunifdgraph_dgraph (do
	{
		newEqDGSOEdge factorize14_sotid2 [factorize14_sotid3] factorize14_sotid1		
	})) (emptyVDGraph factorize14_sig))

factorize14_as1 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize14_as1 = ImplicitAS factorize14_mudg1

factorize14_as2 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize14_as2 = metaunif_prenormalize factorize14_as1

factorize14_as3 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize14_as3 = metaunif_seminormalize factorize14_as1

factorize14_as4 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize14_as4 = metaunif_quasinormalize factorize14_as1

factorize14_as5 :: AnswerSet RSOMetaUnifDGraph SOMetaUnifSysSolution
factorize14_as5 = metaunif_normalize factorize14_as1

factorize14_t1 :: AutomatedTest
factorize14_t1 = check_exactly_as "Checking there is exactly one solution before" 1 factorize14_as1

factorize14_t2 :: AutomatedTest
factorize14_t2 = check_exactly_as "Checking there is exactly one solution after prenormalizing" 1 factorize14_as2

factorize14_t3 :: AutomatedTest
factorize14_t3 = check_exactly_as "Checking there is exactly one solution after seminormalizing" 1 factorize14_as3

factorize14_t4 :: AutomatedTest
factorize14_t4 = check_exactly_as "Checking there are exactly two solutions after quasinormalizing" 2 factorize14_as4

factorize14_t5 :: AutomatedTest
factorize14_t5 = check_exactly_as "Checking there are exactly two solutions after normalizing" 2 factorize14_as5

factorize14_t6 :: AutomatedTest
factorize14_t6 = check_all_resuvdg factorize14_tests_n "Checking that F0 is never equivalent to pi0 before" (\title -> \st -> check_not_soequiv factorize14_sig title st factorize14_soterm2 factorize14_soterm4) factorize14_as1

factorize14_t7 :: AutomatedTest
factorize14_t7 = check_all_resuvdg factorize14_tests_n "Checking that F0 is never equivalent to f before" (\title -> \st -> check_not_soexp factorize14_sig title st factorize14_exp1 factorize14_soterm2) factorize14_as1

factorize14_t8 :: AutomatedTest
factorize14_t8 = check_all_resuvdg factorize14_tests_n "Checking that F1 is never equivalent to pi0 before" (\title -> \st -> check_not_soequiv factorize14_sig title st factorize14_soterm3 factorize14_soterm4) factorize14_as1

factorize14_t9 :: AutomatedTest
factorize14_t9 = check_all_resuvdg factorize14_tests_n "Checking that F1 is never equivalent to f before" (\title -> \st -> check_not_soexp factorize14_sig title st factorize14_exp1 factorize14_soterm3) factorize14_as1

factorize14_t10 :: AutomatedTest
factorize14_t10 = check_all_resuvdg factorize14_tests_n "Checking that F0 is never equivalent to pi0 after prenormalizing" (\title -> \st -> check_not_soequiv factorize14_sig title st factorize14_soterm2 factorize14_soterm4) factorize14_as2

factorize14_t11 :: AutomatedTest
factorize14_t11 = check_all_resuvdg factorize14_tests_n "Checking that F0 is never equivalent to f after prenormalizing" (\title -> \st -> check_not_soexp factorize14_sig title st factorize14_exp1 factorize14_soterm2) factorize14_as2

factorize14_t12 :: AutomatedTest
factorize14_t12 = check_all_resuvdg factorize14_tests_n "Checking that F1 is never equivalent to pi0 after prenormalizing" (\title -> \st -> check_not_soequiv factorize14_sig title st factorize14_soterm3 factorize14_soterm4) factorize14_as2

factorize14_t13 :: AutomatedTest
factorize14_t13 = check_all_resuvdg factorize14_tests_n "Checking that F1 is never equivalent to f after prenormalizing" (\title -> \st -> check_not_soexp factorize14_sig title st factorize14_exp1 factorize14_soterm3) factorize14_as2

factorize14_t14 :: AutomatedTest
factorize14_t14 = check_all_resuvdg factorize14_tests_n "Checking that F0 is never equivalent to pi0 after seminormalizing" (\title -> \st -> check_not_soequiv factorize14_sig title st factorize14_soterm2 factorize14_soterm4) factorize14_as3

factorize14_t15 :: AutomatedTest
factorize14_t15 = check_all_resuvdg factorize14_tests_n "Checking that F0 is never equivalent to f after seminormalizing" (\title -> \st -> check_not_soexp factorize14_sig title st factorize14_exp1 factorize14_soterm2) factorize14_as3

factorize14_t16 :: AutomatedTest
factorize14_t16 = check_all_resuvdg factorize14_tests_n "Checking that F1 is never equivalent to pi0 after seminormalizing" (\title -> \st -> check_not_soequiv factorize14_sig title st factorize14_soterm3 factorize14_soterm4) factorize14_as3

factorize14_t17 :: AutomatedTest
factorize14_t17 = check_all_resuvdg factorize14_tests_n "Checking that F1 is never equivalent to f after seminormalizing" (\title -> \st -> check_not_soexp factorize14_sig title st factorize14_exp1 factorize14_soterm3) factorize14_as3

factorize14_t18 :: AutomatedTest
factorize14_t18 = check_any_resuvdg factorize14_tests_n "Checking that F0 is sometimes equivalent to pi0 after quasinormalizing" (\title -> \st -> check_soequiv factorize14_sig title st factorize14_soterm2 factorize14_soterm4) factorize14_as4

factorize14_t19 :: AutomatedTest
factorize14_t19 = check_any_resuvdg factorize14_tests_n "Checking that F0 is sometimes not equivalent to pi0 after quasinormalizing" (\title -> \st -> check_not_soequiv factorize14_sig title st factorize14_soterm2 factorize14_soterm4) factorize14_as4

factorize14_t20 :: AutomatedTest
factorize14_t20 = check_any_resuvdg factorize14_tests_n "Checking that F0 is sometimes equivalent to f after quasinormalizing" (\title -> \st -> check_soexp factorize14_sig title st factorize14_exp1 factorize14_soterm2) factorize14_as4

factorize14_t21 :: AutomatedTest
factorize14_t21 = check_any_resuvdg factorize14_tests_n "Checking that F0 is sometimes not equivalent to f after quasinormalizing" (\title -> \st -> check_not_soexp factorize14_sig title st factorize14_exp1 factorize14_soterm2) factorize14_as4

factorize14_t22 :: AutomatedTest
factorize14_t22 = check_any_resuvdg factorize14_tests_n "Checking that F1 is sometimes equivalent to pi0 after quasinormalizing" (\title -> \st -> check_soequiv factorize14_sig title st factorize14_soterm3 factorize14_soterm4) factorize14_as4

factorize14_t23 :: AutomatedTest
factorize14_t23 = check_any_resuvdg factorize14_tests_n "Checking that F1 is sometimes not equivalent to pi0 after quasinormalizing" (\title -> \st -> check_not_soequiv factorize14_sig title st factorize14_soterm3 factorize14_soterm4) factorize14_as4

factorize14_t24 :: AutomatedTest
factorize14_t24 = check_any_resuvdg factorize14_tests_n "Checking that F0 is sometimes equivalent to f after quasinormalizing" (\title -> \st -> check_soexp factorize14_sig title st factorize14_exp1 factorize14_soterm3) factorize14_as4

factorize14_t25 :: AutomatedTest
factorize14_t25 = check_any_resuvdg factorize14_tests_n "Checking that F0 is sometimes not equivalent to f after quasinormalizing" (\title -> \st -> check_not_soexp factorize14_sig title st factorize14_exp1 factorize14_soterm3) factorize14_as4

factorize14_t26 :: AutomatedTest
factorize14_t26 = check_any_resuvdg factorize14_tests_n "Checking that F0 is sometimes equivalent to pi0 after normalizing" (\title -> \st -> check_soequiv factorize14_sig title st factorize14_soterm2 factorize14_soterm4) factorize14_as5

factorize14_t27 :: AutomatedTest
factorize14_t27 = check_any_resuvdg factorize14_tests_n "Checking that F0 is sometimes not equivalent to pi0 after normalizing" (\title -> \st -> check_not_soequiv factorize14_sig title st factorize14_soterm2 factorize14_soterm4) factorize14_as5

factorize14_t28 :: AutomatedTest
factorize14_t28 = check_any_resuvdg factorize14_tests_n "Checking that F0 is sometimes equivalent to f after normalizing" (\title -> \st -> check_soexp factorize14_sig title st factorize14_exp1 factorize14_soterm2) factorize14_as5

factorize14_t29 :: AutomatedTest
factorize14_t29 = check_any_resuvdg factorize14_tests_n "Checking that F0 is sometimes not equivalent to f after normalizing" (\title -> \st -> check_not_soexp factorize14_sig title st factorize14_exp1 factorize14_soterm2) factorize14_as5

factorize14_t30 :: AutomatedTest
factorize14_t30 = check_any_resuvdg factorize14_tests_n "Checking that F1 is sometimes equivalent to pi0 after normalizing" (\title -> \st -> check_soequiv factorize14_sig title st factorize14_soterm3 factorize14_soterm4) factorize14_as5

factorize14_t31 :: AutomatedTest
factorize14_t31 = check_any_resuvdg factorize14_tests_n "Checking that F1 is sometimes not equivalent to pi0 after normalizing" (\title -> \st -> check_not_soequiv factorize14_sig title st factorize14_soterm3 factorize14_soterm4) factorize14_as5

factorize14_t32 :: AutomatedTest
factorize14_t32 = check_any_resuvdg factorize14_tests_n "Checking that F0 is sometimes equivalent to f after normalizing" (\title -> \st -> check_soexp factorize14_sig title st factorize14_exp1 factorize14_soterm3) factorize14_as5

factorize14_t33 :: AutomatedTest
factorize14_t33 = check_any_resuvdg factorize14_tests_n "Checking that F0 is sometimes not equivalent to f after normalizing" (\title -> \st -> check_not_soexp factorize14_sig title st factorize14_exp1 factorize14_soterm3) factorize14_as5

factorize14_tests :: String
factorize14_tests = combine_test_results [factorize14_t1,factorize14_t2,factorize14_t3,factorize14_t4,factorize14_t5,factorize14_t6,factorize14_t7,factorize14_t8,factorize14_t9,factorize14_t10,factorize14_t11,factorize14_t12,factorize14_t13,factorize14_t14,factorize14_t15,factorize14_t16,factorize14_t17,factorize14_t18,factorize14_t19,factorize14_t20,factorize14_t21,factorize14_t22,factorize14_t23,factorize14_t24,factorize14_t25,factorize14_t26,factorize14_t27,factorize14_t28,factorize14_t29,factorize14_t30,factorize14_t31,factorize14_t32,factorize14_t33]



factorize_test :: IO ()
factorize_test = putStr "EXAMPLE 1\n\n" >> putStr factorize1_tests >>
		putStr "EXAMPLE 2\n\n" >> putStr factorize2_tests >>
		putStr "EXAMPLE 3\n\n" >> putStr factorize3_tests >>
		putStr "EXAMPLE 4\n\n" >> putStr factorize4_tests >>
		putStr "EXAMPLE 5\n\n" >> putStr factorize5_tests >>
		putStr "EXAMPLE 6\n\n" >> putStr factorize6_tests >>
		putStr "EXAMPLE 7\n\n" >> putStr factorize7_tests >>
		putStr "EXAMPLE 8\n\n" >> putStr factorize8_tests >>
		putStr "EXAMPLE 9\n\n" >> putStr factorize9_tests >>
		putStr "EXAMPLE 10\n\n" >> putStr factorize10_tests >>
		putStr "EXAMPLE 11\n\n" >> putStr factorize11_tests >>
		putStr "EXAMPLE 12\n\n" >> putStr factorize12_tests >>
		putStr "EXAMPLE 13\n\n" >> putStr factorize13_tests >>
		putStr "EXAMPLE 14\n\n" >> putStr factorize14_tests



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



unifsys1_nsols :: Int
unifsys1_nsols = 20

unifsys1_sig :: SOMetaSignature
unifsys1_sig = SOSignature (Signature [] [EnumProc.Empty, read "f0[1]" --> EnumProc.Empty] (read "x0" --> read "x1" --> EnumProc.Empty)) (read "F0[1]" --> EnumProc.Empty) EnumProc.Empty EnumProc.Empty

unifsys1_eq1 :: SOMetaUnifEquation
unifsys1_eq1 = read "u0 x0 = u0 F0[1](x1)"

unifsys1_sys :: SOMetaUnifSystem
unifsys1_sys = USys unifsys1_sig [unifsys1_eq1]

unifsys1_as :: AnswerSet SOMetaUnifSystem SOMetaUnifSysSolution
unifsys1_as = ImplicitAS unifsys1_sys

unifsys1_sol1 :: SOMetaUnifSysSolution
unifsys1_sol1 = UnifSysSolution (fromList [(read "F0[1]", read "f0[1]")]) (fromList [])

unifsys1_sol2 :: SOMetaUnifSysSolution
unifsys1_sol2 = UnifSysSolution (fromList [(read "F0[1]", read "f0[1]{f0[1]}")]) (fromList [])

unifsys1_sol3 :: SOMetaUnifSysSolution
unifsys1_sol3 = UnifSysSolution (fromList [(read "F0[1]", read "f0[1]{f0[1]{f0[1]{f0[1]{f0[1]{f0[1]}}}}}")]) (fromList [])

unifsys1_sol4 :: SOMetaUnifSysSolution
unifsys1_sol4 = UnifSysSolution (fromList [(read "F0[1]", read "pi1")]) (fromList [])
	
unifsys1_t1 :: AutomatedTest
unifsys1_t1 = check_en_any_usol unifsys1_nsols "Checking F0[1] = f0[1] is explicitly a solution" (\title -> \sol -> check_usol title unifsys1_sol1 sol) unifsys1_as

unifsys1_t2 :: AutomatedTest
unifsys1_t2 = check_imp_usol "Checking F0[1] = f0[1] is implicitly a solution" unifsys1_sol1 unifsys1_as

unifsys1_t3 :: AutomatedTest
unifsys1_t3 = check_en_any_usol unifsys1_nsols "Checking F0[1] = f0[1]{f0[1]} is explicitly a solution" (\title -> \sol -> check_usol title unifsys1_sol2 sol) unifsys1_as

unifsys1_t4 :: AutomatedTest
unifsys1_t4 = check_imp_usol "Checking F0[1] = f0[1]{f0[1]} is implicitly a solution" unifsys1_sol2 unifsys1_as

unifsys1_t5 :: AutomatedTest
unifsys1_t5 = check_en_any_usol unifsys1_nsols "Checking F0[1] = f0[1]{f0[1]{f0[1]{f0[1]{f0[1]{f0[1]}}}}} is explicitly a solution" (\title -> \sol -> check_usol title unifsys1_sol3 sol) unifsys1_as

unifsys1_t6 :: AutomatedTest
unifsys1_t6 = check_imp_usol "Checking F0[1] = f0[1]{f0[1]{f0[1]{f0[1]{f0[1]{f0[1]}}}}} is implicitly a solution" unifsys1_sol3 unifsys1_as

unifsys1_t7 :: AutomatedTest
unifsys1_t7 = check_en_all_usol unifsys1_nsols "Checking F0[1] = pi1 is not explicitly a solution" (\title -> \sol -> check_not_usol title unifsys1_sol4 sol) unifsys1_as

unifsys1_t8 :: AutomatedTest
unifsys1_t8 = check_not_imp_usol "Checking F0[1] = pi1 is not explicitly a solution" unifsys1_sol4 unifsys1_as

unifsys1_t9 :: AutomatedTest
unifsys1_t9 = check_min_exp_as "Checking that the equation system has at least 20 solutions" 20 unifsys1_as

unifsys1_tests :: String
unifsys1_tests = combine_test_results [unifsys1_t1,unifsys1_t2,unifsys1_t3,unifsys1_t4,unifsys1_t5,unifsys1_t6,unifsys1_t7,unifsys1_t8,unifsys1_t9]

unifsys2_nsols :: Int
unifsys2_nsols = 20

unifsys2_sig :: SOMetaSignature
unifsys2_sig = SOSignature (Signature [] [EnumProc.Empty, EnumProc.Empty, read "f0[2]" --> EnumProc.Empty] (read "x0" --> read "x1" --> read "x2" --> EnumProc.Empty)) (read "F0[2]" --> EnumProc.Empty) EnumProc.Empty EnumProc.Empty

unifsys2_eq1 :: SOMetaUnifEquation
unifsys2_eq1 = read "u0 x0 = u0 F0[2](x1,x2)"

unifsys2_sys :: SOMetaUnifSystem
unifsys2_sys = USys unifsys2_sig [unifsys2_eq1]

unifsys2_as :: AnswerSet SOMetaUnifSystem SOMetaUnifSysSolution
unifsys2_as = ImplicitAS unifsys2_sys

unifsys2_sol1 :: SOMetaUnifSysSolution
unifsys2_sol1 = UnifSysSolution (fromList [(read "F0[2]", read "f0[2]")]) (fromList [])

unifsys2_sol2 :: SOMetaUnifSysSolution
unifsys2_sol2 = UnifSysSolution (fromList [(read "F0[2]", read "f0[2]{f0[2],pi0}")]) (fromList [])

unifsys2_sol3 :: SOMetaUnifSysSolution
unifsys2_sol3 = UnifSysSolution (fromList [(read "F0[2]", read "f0[2]{f0[2]{pi0,pi0},pi1}")]) (fromList [])

unifsys2_sol4 :: SOMetaUnifSysSolution
unifsys2_sol4 = UnifSysSolution (fromList [(read "F0[2]", read "pi1")]) (fromList [])

unifsys2_sol5 :: SOMetaUnifSysSolution
unifsys2_sol5 = UnifSysSolution (fromList [(read "F0[2]", read "pi0")]) (fromList [])

unifsys2_sol6 :: SOMetaUnifSysSolution
unifsys2_sol6 = UnifSysSolution (fromList [(read "F0[2]", read "pi2")]) (fromList [])

unifsys2_sol7 :: SOMetaUnifSysSolution
unifsys2_sol7 = UnifSysSolution (fromList [(read "F0[2]", read "f0[2]{pi0,pi2}")]) (fromList [])
	
unifsys2_t1 :: AutomatedTest
unifsys2_t1 = check_en_any_usol unifsys1_nsols "Checking F0[2] = f0[2] is explicitly a solution" (\title -> \sol -> check_usol title unifsys2_sol1 sol) unifsys2_as

unifsys2_t2 :: AutomatedTest
unifsys2_t2 = check_imp_usol "Checking F0[2] = f0[2] is implicitly a solution" unifsys2_sol1 unifsys2_as

unifsys2_t3 :: AutomatedTest
unifsys2_t3 = check_en_any_usol unifsys2_nsols "Checking F0[2] = f0[2]{f0[2],pi0} is explicitly a solution" (\title -> \sol -> check_usol title unifsys2_sol2 sol) unifsys2_as

unifsys2_t4 :: AutomatedTest
unifsys2_t4 = check_imp_usol "Checking F0[2] = f0[2]{f0[2],pi0} is implicitly a solution" unifsys2_sol2 unifsys2_as

unifsys2_t5 :: AutomatedTest
unifsys2_t5 = check_en_any_usol unifsys2_nsols "Checking F0[2] = f0[2]{f0[2]{pi0,pi0},pi1} is explicitly a solution" (\title -> \sol -> check_usol title unifsys2_sol3 sol) unifsys2_as

unifsys2_t6 :: AutomatedTest
unifsys2_t6 = check_imp_usol "Checking F0[2] = f0[2]{f0[2]{pi0,pi0},pi1} is implicitly a solution" unifsys2_sol3 unifsys2_as

unifsys2_t7 :: AutomatedTest
unifsys2_t7 = check_en_any_usol unifsys2_nsols "Checking F0[2] = pi1 is explicitly a solution" (\title -> \sol -> check_usol title unifsys2_sol4 sol) unifsys2_as

unifsys2_t8 :: AutomatedTest
unifsys2_t8 = check_imp_usol "Checking F0[2] = pi1 is implicitly a solution" unifsys2_sol4 unifsys2_as

unifsys2_t9 :: AutomatedTest
unifsys2_t9 = check_en_any_usol unifsys2_nsols "Checking F0[2] = pi0 is explicitly a solution" (\title -> \sol -> check_usol title unifsys2_sol5 sol) unifsys2_as

unifsys2_t10 :: AutomatedTest
unifsys2_t10 = check_imp_usol "Checking F0[2] = pi0 is implicitly a solution" unifsys2_sol5 unifsys2_as

unifsys2_t11 :: AutomatedTest
unifsys2_t11 = check_en_all_usol unifsys2_nsols "Checking F0[2] = pi2 is not explicitly a solution" (\title -> \sol -> check_not_usol title unifsys2_sol6 sol) unifsys2_as

unifsys2_t12 :: AutomatedTest
unifsys2_t12 = check_not_imp_usol "Checking F0[2] = pi2 is not explicitly a solution" unifsys2_sol6 unifsys2_as

unifsys2_t13 :: AutomatedTest
unifsys2_t13 = check_en_all_usol unifsys2_nsols "Checking F0[2] = f0[2]{pi0,pi2} is not explicitly a solution" (\title -> \sol -> check_not_usol title unifsys2_sol7 sol) unifsys2_as

unifsys2_t14 :: AutomatedTest
unifsys2_t14 = check_not_imp_usol "Checking F0[2] = f0[2]{pi0,pi2} is not explicitly a solution" unifsys2_sol7 unifsys2_as

unifsys2_t15 :: AutomatedTest
unifsys2_t15 = check_min_exp_as "Checking that the equation system has at least 20 solutions" 20 unifsys2_as

unifsys2_tests :: String
unifsys2_tests = combine_test_results [unifsys2_t1,unifsys2_t2,unifsys2_t3,unifsys2_t4,unifsys2_t5,unifsys2_t6,unifsys2_t7,unifsys2_t8,unifsys2_t9,unifsys2_t10,unifsys2_t11,unifsys2_t12,unifsys2_t13,unifsys2_t14,unifsys2_t15]

unifsys3_nsols :: Int
unifsys3_nsols = 20

unifsys3_sig :: SOMetaSignature
unifsys3_sig = SOSignature (Signature [] [EnumProc.Empty, read "f0[1]" --> read "f1[1]" --> EnumProc.Empty] (read "x0" --> read "x1" --> read "x2" --> EnumProc.Empty)) (read "F0[1]" --> EnumProc.Empty) EnumProc.Empty EnumProc.Empty

unifsys3_eq1 :: SOMetaUnifEquation
unifsys3_eq1 = read "u0 x0 = u0 f0[1](x1)"

unifsys3_eq2 :: SOMetaUnifEquation
unifsys3_eq2 = read "u0 x1 = u0 f1[1](x2)"

unifsys3_eq3 :: SOMetaUnifEquation
unifsys3_eq3 = read "u0 x0 = u0 F0[1](x2)"

unifsys3_sys :: SOMetaUnifSystem
unifsys3_sys = USys unifsys3_sig [unifsys3_eq1,unifsys3_eq2,unifsys3_eq3]

unifsys3_as :: AnswerSet SOMetaUnifSystem SOMetaUnifSysSolution
unifsys3_as = ImplicitAS unifsys3_sys

unifsys3_sol1 :: SOMetaUnifSysSolution
unifsys3_sol1 = UnifSysSolution (fromList [(read "F0[1]", read "f0[1]{f1[1]}")]) (fromList [])

unifsys3_sol2 :: SOMetaUnifSysSolution
unifsys3_sol2 = UnifSysSolution (fromList [(read "F0[1]", read "f1[1]{f0[1]}")]) (fromList [])

unifsys3_sol3 :: SOMetaUnifSysSolution
unifsys3_sol3 = UnifSysSolution (fromList [(read "F0[1]", read "f0[1]")]) (fromList [])

unifsys3_t1 :: AutomatedTest
unifsys3_t1 = check_exactly_exp_as "Checking that the equation system has exactly 1 solution" 1 unifsys3_as

unifsys3_t2 :: AutomatedTest
unifsys3_t2 = check_en_any_usol unifsys3_nsols "Checking F0[1] = f0[1]{f1[1]} is explicitly a solution" (\title -> \sol -> check_usol title unifsys3_sol1 sol) unifsys3_as

unifsys3_t3 :: AutomatedTest
unifsys3_t3 = check_imp_usol "Checking F0[1] = f0[1]{f1[1]} is implicitly a solution" unifsys3_sol1 unifsys3_as

unifsys3_t4 :: AutomatedTest
unifsys3_t4 = check_en_all_usol unifsys3_nsols "Checking F0[1] = f1[1]{f0[1]} is not explicitly a solution" (\title -> \sol -> check_not_usol title unifsys3_sol2 sol) unifsys3_as

unifsys3_t5 :: AutomatedTest
unifsys3_t5 = check_not_imp_usol "Checking F0[1] = f1[1]{f0[1]} is not implicitly a solution" unifsys3_sol2 unifsys3_as

unifsys3_t6 :: AutomatedTest
unifsys3_t6 = check_en_all_usol unifsys3_nsols "Checking F0[1] = f0[1] is not explicitly a solution" (\title -> \sol -> check_not_usol title unifsys3_sol3 sol) unifsys3_as

unifsys3_t7 :: AutomatedTest
unifsys3_t7 = check_not_imp_usol "Checking F0[1] = f0[1] is not implicitly a solution" unifsys3_sol3 unifsys3_as

unifsys3_tests :: String
unifsys3_tests = combine_test_results [unifsys3_t1,unifsys3_t2,unifsys3_t3,unifsys3_t4,unifsys3_t5,unifsys3_t6,unifsys3_t7]

unifsys4_nsols :: Int
unifsys4_nsols = 20

unifsys4_sig :: SOMetaSignature
unifsys4_sig = SOSignature (Signature [] [EnumProc.Empty, EnumProc.Empty, read "f0[2]" --> EnumProc.Empty] (read "x0" --> read "x1" --> read "x2" --> EnumProc.Empty)) (read "F0[1]" --> EnumProc.Empty) EnumProc.Empty EnumProc.Empty

unifsys4_eq1 :: SOMetaUnifEquation
unifsys4_eq1 = read "u0 x0 = u0 f0[2](x1,x2)"

unifsys4_eq2 :: SOMetaUnifEquation
unifsys4_eq2 = read "u1 u0 x0 = u1 x1"

unifsys4_eq3 :: SOMetaUnifEquation
unifsys4_eq3 = read "u1 x1 = u1 F0[1](x2)"

unifsys4_sys :: SOMetaUnifSystem
unifsys4_sys = USys unifsys4_sig [unifsys4_eq1,unifsys4_eq2,unifsys4_eq3]

unifsys4_as :: AnswerSet SOMetaUnifSystem SOMetaUnifSysSolution
unifsys4_as = ImplicitAS unifsys4_sys

unifsys4_sol1 :: SOMetaUnifSysSolution
unifsys4_sol1 = UnifSysSolution (fromList [(read "F0[1]", read "pi0")]) (fromList [])

unifsys4_sol2 :: SOMetaUnifSysSolution
unifsys4_sol2 = UnifSysSolution (fromList [(read "F0[1]", read "f0[2]{pi0,pi0}")]) (fromList [])

unifsys4_sol3 :: SOMetaUnifSysSolution
unifsys4_sol3 = UnifSysSolution (fromList [(read "F0[1]", read "f0[2]{pi0,f0[2]{pi0,pi0}}")]) (fromList [])

unifsys4_sol4 :: SOMetaUnifSysSolution
unifsys4_sol4 = UnifSysSolution (fromList [(read "F0[1]", read "pi1")]) (fromList [])

unifsys4_sol5 :: SOMetaUnifSysSolution
unifsys4_sol5 = UnifSysSolution (fromList [(read "F0[1]", read "f0[2]")]) (fromList [])

unifsys4_t1 :: AutomatedTest
unifsys4_t1 = check_min_exp_as "Checking that the equation system has at least 20 solutions" 20 unifsys4_as

unifsys4_t2 :: AutomatedTest
unifsys4_t2 = check_en_any_usol unifsys4_nsols "Checking F0[1] = pi0 is explicitly a solution" (\title -> \sol -> check_usol title unifsys4_sol1 sol) unifsys4_as

unifsys4_t3 :: AutomatedTest
unifsys4_t3 = check_imp_usol "Checking F0[1] = pi0 is implicitly a solution" unifsys4_sol1 unifsys4_as

unifsys4_t4 :: AutomatedTest
unifsys4_t4 = check_en_any_usol unifsys4_nsols "Checking F0[1] = f0[2]{pi0,pi0} is explicitly a solution" (\title -> \sol -> check_usol title unifsys4_sol2 sol) unifsys4_as

unifsys4_t5 :: AutomatedTest
unifsys4_t5 = check_imp_usol "Checking F0[1] = f0[2]{pi0,pi0} is implicitly a solution" unifsys4_sol2 unifsys4_as

unifsys4_t6 :: AutomatedTest
unifsys4_t6 = check_en_any_usol unifsys4_nsols "Checking F0[1] = f0[2]{pi0,f0[2]{pi0,pi0}} is explicitly a solution" (\title -> \sol -> check_usol title unifsys4_sol3 sol) unifsys4_as

unifsys4_t7 :: AutomatedTest
unifsys4_t7 = check_imp_usol "Checking F0[1] = f0[2]{pi0,f0[2]{pi0,pi0}} is implicitly a solution" unifsys4_sol3 unifsys4_as

unifsys4_t8 :: AutomatedTest
unifsys4_t8 = check_en_all_usol unifsys4_nsols "Checking F0[1] = pi1 is not explicitly a solution" (\title -> \sol -> check_not_usol title unifsys4_sol4 sol) unifsys4_as

unifsys4_t9 :: AutomatedTest
unifsys4_t9 = check_not_imp_usol "Checking F0[1] = pi1 is not implicitly a solution" unifsys4_sol4 unifsys4_as

unifsys4_t10 :: AutomatedTest
unifsys4_t10 = check_en_all_usol unifsys4_nsols "Checking F0[1] = f0[2] is not explicitly a solution" (\title -> \sol -> check_not_usol title unifsys4_sol5 sol) unifsys4_as

unifsys4_t11 :: AutomatedTest
unifsys4_t11 = check_not_imp_usol "Checking F0[1] = f0[2] is not implicitly a solution" unifsys4_sol5 unifsys4_as

unifsys4_tests :: String
unifsys4_tests = combine_test_results [unifsys4_t1,unifsys4_t2,unifsys4_t3,unifsys4_t4,unifsys4_t5,unifsys4_t6,unifsys4_t7,unifsys4_t8,unifsys4_t9,unifsys4_t10,unifsys4_t11]

unifsys5_nsols :: Int
unifsys5_nsols = 20

unifsys5_sig :: SOMetaSignature
unifsys5_sig = SOSignature (Signature [] [EnumProc.Empty, EnumProc.Empty, read "f0[2]" --> EnumProc.Empty] (read "x0" --> read "x1" --> read "x2" --> EnumProc.Empty)) (EnumProc.Empty) EnumProc.Empty EnumProc.Empty

unifsys5_eq1 :: SOMetaUnifEquation
unifsys5_eq1 = read "u0 x0 = u0 f0[2](x1,x2)"

unifsys5_eq2 :: SOMetaUnifEquation
unifsys5_eq2 = read "u1 u0 x0 = u1 u0 x1"

unifsys5_sys :: SOMetaUnifSystem
unifsys5_sys = USys unifsys5_sig [unifsys5_eq1,unifsys5_eq2]

unifsys5_as :: AnswerSet SOMetaUnifSystem SOMetaUnifSysSolution
unifsys5_as = ImplicitAS unifsys5_sys

unifsys5_t1 :: AutomatedTest
unifsys5_t1 = check_exactly_exp_as "Checking that the equation system has no solutions" 0 unifsys5_as

unifsys5_tests :: String
unifsys5_tests = combine_test_results [unifsys5_t1]

unifsys6_nsols :: Int
unifsys6_nsols = 20

unifsys6_sig :: SOMetaSignature
unifsys6_sig = SOSignature (Signature [] [EnumProc.Empty, read "f0[2]" --> read "f1[2]" --> EnumProc.Empty] (read "x0" --> read "x1" --> read "x2" --> EnumProc.Empty)) (EnumProc.Empty) EnumProc.Empty EnumProc.Empty

unifsys6_eq1 :: SOMetaUnifEquation
unifsys6_eq1 = read "u0 x0 = u0 f0[2](x1,x2)"

unifsys6_eq2 :: SOMetaUnifEquation
unifsys6_eq2 = read "u1 u0 x0 = u1 f1[2](x1,x2)"

unifsys6_sys :: SOMetaUnifSystem
unifsys6_sys = USys unifsys6_sig [unifsys6_eq1,unifsys6_eq2]

unifsys6_as :: AnswerSet SOMetaUnifSystem SOMetaUnifSysSolution
unifsys6_as = ImplicitAS unifsys6_sys

unifsys6_t1 :: AutomatedTest
unifsys6_t1 = check_exactly_exp_as "Checking that the equation system has no solutions" 0 unifsys6_as

unifsys6_tests :: String
unifsys6_tests = combine_test_results [unifsys6_t1]

unifsys7_nsols :: Int
unifsys7_nsols = 20

unifsys7_sig :: SOMetaSignature
unifsys7_sig = SOSignature (Signature [] [EnumProc.Empty, EnumProc.Empty, read "f0[2]" --> read "f1[2]" --> EnumProc.Empty] (read "x0" --> read "x1" --> read "x2" --> read "x3" --> EnumProc.Empty)) (read "F0[2]" --> EnumProc.Empty) EnumProc.Empty EnumProc.Empty

unifsys7_eq1 :: SOMetaUnifEquation
unifsys7_eq1 = read "u0 x0 = u0 f0[2](x1,x2)"

unifsys7_eq2 :: SOMetaUnifEquation
unifsys7_eq2 = read "u1 f1[2](x3,x3) = u1 u0 f1[2](x0,x3)"

unifsys7_eq3 :: SOMetaUnifEquation
unifsys7_eq3 = read "u2 u0 x0 = u2 u1 x3"

unifsys7_eq4 :: SOMetaUnifEquation
unifsys7_eq4 = read "u1 u0 F0[2](x1,x2) = u1 x3"

unifsys7_sys :: SOMetaUnifSystem
unifsys7_sys = USys unifsys7_sig [unifsys7_eq1,unifsys7_eq2,unifsys7_eq3,unifsys7_eq4]

unifsys7_as :: AnswerSet SOMetaUnifSystem SOMetaUnifSysSolution
unifsys7_as = ImplicitAS unifsys7_sys

unifsys7_cheq1_1 :: SOMetaUnifEquation
unifsys7_cheq1_1 = read "F0[2](x0,x1) = f0[2]{F1[2],F2[2]}(x0,x1)"

unifsys7_chsys1 :: [SOMetaUnifEquation]
unifsys7_chsys1 = [unifsys7_cheq1_1]

unifsys7_sol1 :: SOMetaUnifSysSolution
unifsys7_sol1 = UnifSysSolution (fromList [(read "F0[2]", read "f0[2]{pi0,pi1}")]) (fromList [])

unifsys7_sol2 :: SOMetaUnifSysSolution
unifsys7_sol2 = UnifSysSolution (fromList [(read "F0[2]", read "f0[2]{pi1,pi0}")]) (fromList [])

unifsys7_sol3 :: SOMetaUnifSysSolution
unifsys7_sol3 = UnifSysSolution (fromList [(read "F0[2]", read "f0[2]{pi1,pi1}")]) (fromList [])

unifsys7_t1 :: AutomatedTest
unifsys7_t1 = check_min_exp_as "Checking that the equation system has at least 1 solution" 1 unifsys7_as

unifsys7_t2 :: AutomatedTest
unifsys7_t2 = check_en_all_usol unifsys7_nsols "Checking F0[2] = f0[2]{F1[2],F2[2]} is true for every solution" (\title -> \sol -> check_usys_usol_at title unifsys7_chsys1 sol) unifsys7_as

unifsys7_t3 :: AutomatedTest
unifsys7_t3 = check_imp_usol "Checking F0[2] = f0[2]{pi0,pi1} is implicitly a solution" unifsys7_sol1 unifsys7_as

unifsys7_t4 :: AutomatedTest
unifsys7_t4 = check_imp_usol "Checking F0[2] = f0[2]{pi1,pi0} is implicitly a solution" unifsys7_sol2 unifsys7_as

unifsys7_t5 :: AutomatedTest
unifsys7_t5 = check_imp_usol "Checking F0[2] = f0[2]{pi1,pi1} is implicitly a solution" unifsys7_sol3 unifsys7_as

unifsys7_tests :: String
unifsys7_tests = combine_test_results [unifsys7_t1,unifsys7_t2,unifsys7_t3,unifsys7_t4,unifsys7_t5]

unifsys8_nsols :: Int
unifsys8_nsols = 20

unifsys8_sig :: SOMetaSignature
unifsys8_sig = SOSignature (Signature [] [EnumProc.Empty, EnumProc.Empty, read "f0[2]" --> read "f1[2]" --> EnumProc.Empty] (read "x0" --> read "x1" --> read "x2" --> read "x3" --> EnumProc.Empty)) (read "F0[2]" --> EnumProc.Empty) EnumProc.Empty EnumProc.Empty

unifsys8_eq1 :: SOMetaUnifEquation
unifsys8_eq1 = read "u0 x0 = u0 f0[2](x1,x2)"

unifsys8_eq2 :: SOMetaUnifEquation
unifsys8_eq2 = read "u1 f1[2](x3,x3) = u1 u0 f1[2](x0,x3)"

unifsys8_eq3 :: SOMetaUnifEquation
unifsys8_eq3 = read "u2 u0 f0[2](x2,x1) = u2 u1 x3"

unifsys8_eq4 :: SOMetaUnifEquation
unifsys8_eq4 = read "u1 u0 F0[2](x1,x2) = u1 x3"

unifsys8_sys :: SOMetaUnifSystem
unifsys8_sys = USys unifsys8_sig [unifsys8_eq1,unifsys8_eq2,unifsys8_eq3,unifsys8_eq4]

unifsys8_as :: AnswerSet SOMetaUnifSystem SOMetaUnifSysSolution
unifsys8_as = ImplicitAS unifsys8_sys

unifsys8_cheq1_1 :: SOMetaUnifEquation
unifsys8_cheq1_1 = read "F0[2](x0,x1) = f0[2]{F1[2],F2[2]}(x0,x1)"

unifsys8_chsys1 :: [SOMetaUnifEquation]
unifsys8_chsys1 = [unifsys8_cheq1_1]

unifsys8_sol1 :: SOMetaUnifSysSolution
unifsys8_sol1 = UnifSysSolution (fromList [(read "F0[2]", read "f0[2]{pi0,pi1}")]) (fromList [])

unifsys8_sol2 :: SOMetaUnifSysSolution
unifsys8_sol2 = UnifSysSolution (fromList [(read "F0[2]", read "f0[2]{pi1,pi0}")]) (fromList [])

unifsys8_sol3 :: SOMetaUnifSysSolution
unifsys8_sol3 = UnifSysSolution (fromList [(read "F0[2]", read "f0[2]{pi1,pi1}")]) (fromList [])

unifsys8_t1 :: AutomatedTest
unifsys8_t1 = check_min_exp_as "Checking that the equation system has at least 1 solution" 1 unifsys8_as

unifsys8_t2 :: AutomatedTest
unifsys8_t2 = check_en_all_usol unifsys8_nsols "Checking F0[2] = f0[2]{F1[2],F2[2]} is true for every solution" (\title -> \sol -> check_usys_usol_at title unifsys8_chsys1 sol) unifsys8_as

unifsys8_t3 :: AutomatedTest
unifsys8_t3 = check_imp_usol "Checking F0[2] = f0[2]{pi0,pi1} is implicitly a solution" unifsys8_sol1 unifsys8_as

unifsys8_t4 :: AutomatedTest
unifsys8_t4 = check_imp_usol "Checking F0[2] = f0[2]{pi1,pi0} is implicitly a solution" unifsys8_sol2 unifsys8_as

unifsys8_t5 :: AutomatedTest
unifsys8_t5 = check_imp_usol "Checking F0[2] = f0[2]{pi1,pi1} is implicitly a solution" unifsys8_sol3 unifsys8_as

unifsys8_tests :: String
unifsys8_tests = combine_test_results [unifsys8_t1,unifsys8_t2,unifsys8_t3,unifsys8_t4,unifsys8_t5]

unifsys9_nsols :: Int
unifsys9_nsols = 20

unifsys9_sig :: SOMetaSignature
unifsys9_sig = SOSignature (Signature [] [EnumProc.Empty, EnumProc.Empty, read "f0[2]" --> read "f1[2]" --> EnumProc.Empty] (read "x0" --> read "x1" --> read "x2" --> read "x3" --> EnumProc.Empty)) (read "F0[2]" --> EnumProc.Empty) EnumProc.Empty EnumProc.Empty

unifsys9_eq1 :: SOMetaUnifEquation
unifsys9_eq1 = read "u0 x0 = u0 f0[2](x1,x2)"

unifsys9_eq2 :: SOMetaUnifEquation
unifsys9_eq2 = read "u1 f1[2](x3,x3) = u1 u0 f1[2](x0,x3)"

unifsys9_eq3 :: SOMetaUnifEquation
unifsys9_eq3 = read "u2 u0 x0 = u2 u1 x3"

unifsys9_eq4 :: SOMetaUnifEquation
unifsys9_eq4 = read "u1 F0[2](x1,x2) = u1 x3"

unifsys9_sys :: SOMetaUnifSystem
unifsys9_sys = USys unifsys9_sig [unifsys9_eq1,unifsys9_eq2,unifsys9_eq3,unifsys9_eq4]

unifsys9_as :: AnswerSet SOMetaUnifSystem SOMetaUnifSysSolution
unifsys9_as = ImplicitAS unifsys9_sys

unifsys9_cheq1_1 :: SOMetaUnifEquation
unifsys9_cheq1_1 = read "F0[2](x0,x1) = f0[2]{F1[2],F2[2]}(x0,x1)"

unifsys9_chsys1 :: [SOMetaUnifEquation]
unifsys9_chsys1 = [unifsys9_cheq1_1]

unifsys9_sol1 :: SOMetaUnifSysSolution
unifsys9_sol1 = UnifSysSolution (fromList [(read "F0[2]", read "f0[2]{pi0,pi1}")]) (fromList [])

unifsys9_sol2 :: SOMetaUnifSysSolution
unifsys9_sol2 = UnifSysSolution (fromList [(read "F0[2]", read "f0[2]{pi1,pi0}")]) (fromList [])

unifsys9_sol3 :: SOMetaUnifSysSolution
unifsys9_sol3 = UnifSysSolution (fromList [(read "F0[2]", read "f0[2]{pi1,pi1}")]) (fromList [])

unifsys9_sol4 :: SOMetaUnifSysSolution
unifsys9_sol4 = UnifSysSolution (fromList [(read "F0[2]", read "pi0")]) (fromList [])

unifsys9_sol5 :: SOMetaUnifSysSolution
unifsys9_sol5 = UnifSysSolution (fromList [(read "F0[2]", read "pi1")]) (fromList [])

unifsys9_t1 :: AutomatedTest
unifsys9_t1 = check_min_exp_as "Checking that the equation system has at least 1 solution" 1 unifsys9_as

unifsys9_t2 :: AutomatedTest
unifsys9_t2 = check_en_any_usol unifsys9_nsols "Checking F0[2] = f0[2]{F1[2],F2[2]} is not true for every solution" (\title -> \sol -> check_not_usys_usol_at title unifsys9_chsys1 sol) unifsys9_as

unifsys9_t3 :: AutomatedTest
unifsys9_t3 = check_imp_usol "Checking F0[2] = f0[2]{pi0,pi1} is implicitly a solution" unifsys9_sol1 unifsys9_as

unifsys9_t4 :: AutomatedTest
unifsys9_t4 = check_imp_usol "Checking F0[2] = f0[2]{pi1,pi0} is implicitly a solution" unifsys9_sol2 unifsys9_as

unifsys9_t5 :: AutomatedTest
unifsys9_t5 = check_imp_usol "Checking F0[2] = f0[2]{pi1,pi1} is implicitly a solution" unifsys9_sol3 unifsys9_as

unifsys9_t6 :: AutomatedTest
unifsys9_t6 = check_imp_usol "Checking F0[2] = pi0 is implicitly a solution" unifsys9_sol4 unifsys9_as

unifsys9_t7 :: AutomatedTest
unifsys9_t7 = check_imp_usol "Checking F0[2] = pi1 is implicitly a solution" unifsys9_sol5 unifsys9_as

unifsys9_tests :: String
unifsys9_tests = combine_test_results [unifsys9_t1,unifsys9_t2,unifsys9_t3,unifsys9_t4,unifsys9_t5,unifsys9_t6,unifsys9_t7]

unifsys10_nsols :: Int
unifsys10_nsols = 4

unifsys10_sig :: SOMetaSignature
unifsys10_sig = SOSignature (Signature [] [EnumProc.Empty, read "f2[1]" --> EnumProc.Empty, read "f0[2]" --> read "f1[2]" --> EnumProc.Empty] (read "x0" --> read "x1" --> read "x2" --> read "x3" --> EnumProc.Empty)) (read "F0[2]" --> EnumProc.Empty) EnumProc.Empty EnumProc.Empty

unifsys10_eq1 :: SOMetaUnifEquation
unifsys10_eq1 = read "u0 x0 = u0 f0[2](x1,x2)"

unifsys10_eq2 :: SOMetaUnifEquation
unifsys10_eq2 = read "u1 f1[2](x3,x3) = u1 u0 f1[2](x0,x3)"

unifsys10_eq3 :: SOMetaUnifEquation
unifsys10_eq3 = read "u2 u0 x0 = u2 u1 x3"

unifsys10_eq4 :: SOMetaUnifEquation
unifsys10_eq4 = read "u1 u0 F0[2](f2[1](x2),x2) = u1 x3"

unifsys10_sys :: SOMetaUnifSystem
unifsys10_sys = USys unifsys10_sig [unifsys10_eq1,unifsys10_eq2,unifsys10_eq3,unifsys10_eq4]

unifsys10_as :: AnswerSet SOMetaUnifSystem SOMetaUnifSysSolution
unifsys10_as = ImplicitAS unifsys10_sys

unifsys10_cheq1_1 :: SOMetaUnifEquation
unifsys10_cheq1_1 = read "F0[2](x0,x1) = f0[2]{F1[2],F2[2]}(x0,x1)"

unifsys10_chsys1 :: [SOMetaUnifEquation]
unifsys10_chsys1 = [unifsys10_cheq1_1]

unifsys10_sol1 :: SOMetaUnifSysSolution
unifsys10_sol1 = UnifSysSolution (fromList [(read "F0[2]", read "f0[2]{pi0,pi1}")]) (fromList [])

unifsys10_sol2 :: SOMetaUnifSysSolution
unifsys10_sol2 = UnifSysSolution (fromList [(read "F0[2]", read "f0[2]{pi1,pi0}")]) (fromList [])

unifsys10_sol3 :: SOMetaUnifSysSolution
unifsys10_sol3 = UnifSysSolution (fromList [(read "F0[2]", read "f0[2]{pi0,pi0}")]) (fromList [])

unifsys10_t1 :: AutomatedTest
unifsys10_t1 = check_min_exp_as "Checking that the equation system has at least 1 solution" 1 unifsys10_as

unifsys10_t2 :: AutomatedTest
unifsys10_t2 = check_en_all_usol unifsys10_nsols "Checking F0[2] = f0[2]{F1[2],F2[2]} is true for every solution" (\title -> \sol -> check_usys_usol_at title unifsys10_chsys1 sol) unifsys10_as

unifsys10_t3 :: AutomatedTest
unifsys10_t3 = check_imp_usol "Checking F0[2] = f0[2]{pi0,pi1} is implicitly a solution" unifsys10_sol1 unifsys10_as

unifsys10_t4 :: AutomatedTest
unifsys10_t4 = check_not_imp_usol "Checking F0[2] = f0[2]{pi1,pi0} is not implicitly a solution" unifsys10_sol2 unifsys10_as

unifsys10_t5 :: AutomatedTest
unifsys10_t5 = check_not_imp_usol "Checking F0[2] = f0[2]{pi0,pi0} is not implicitly a solution" unifsys10_sol3 unifsys10_as

unifsys10_tests :: String
unifsys10_tests = combine_test_results [unifsys10_t1,unifsys10_t2,unifsys10_t3,unifsys10_t4,unifsys10_t5]

unifsys11_nsols :: Int
unifsys11_nsols = 20

unifsys11_sig :: SOMetaSignature
unifsys11_sig = SOSignature (Signature [] [EnumProc.Empty, read "f2[1]" --> EnumProc.Empty, read "f0[2]" --> read "f1[2]" --> EnumProc.Empty] (read "x0" --> read "x1" --> read "x2" --> read "x3" --> EnumProc.Empty)) (read "F0[2]" --> EnumProc.Empty) EnumProc.Empty EnumProc.Empty

unifsys11_eq1 :: SOMetaUnifEquation
unifsys11_eq1 = read "u0 x0 = u0 f0[2](x1,x2)"

unifsys11_eq2 :: SOMetaUnifEquation
unifsys11_eq2 = read "u1 u0 x0 = u1 f2[1](x1)"

unifsys11_eq3 :: SOMetaUnifEquation
unifsys11_eq3 = read "u1 u0 F0[2](x1,x2) = u1 u0 x0"

unifsys11_sys :: SOMetaUnifSystem
unifsys11_sys = USys unifsys11_sig [unifsys11_eq1,unifsys11_eq2,unifsys11_eq3]

unifsys11_as :: AnswerSet SOMetaUnifSystem SOMetaUnifSysSolution
unifsys11_as = ImplicitAS unifsys11_sys

unifsys11_t1 :: AutomatedTest
unifsys11_t1 = check_exactly_exp_as "Checking that the equation system has no solutions" 0 unifsys11_as

unifsys11_tests :: String
unifsys11_tests = combine_test_results [unifsys11_t1]

unifsys12_nsols :: Int
unifsys12_nsols = 20

unifsys12_sig :: SOMetaSignature
unifsys12_sig = SOSignature (Signature [] [EnumProc.Empty, read "f2[1]" --> EnumProc.Empty, read "f0[2]" --> read "f1[2]" --> EnumProc.Empty] (read "x0" --> read "x1" --> read "x2" --> read "x3" --> EnumProc.Empty)) (read "F0[2]" --> EnumProc.Empty) EnumProc.Empty EnumProc.Empty

unifsys12_eq1 :: SOMetaUnifEquation
unifsys12_eq1 = read "u0 x0 = u0 f0[2](x1,x2)"

unifsys12_eq2 :: SOMetaUnifEquation
unifsys12_eq2 = read "u1 x0 = u1 f2[1](x1)"

unifsys12_eq3 :: SOMetaUnifEquation
unifsys12_eq3 = read "u1 u0 F0[2](f2[1](x2),x2) = u1 u0 x0"

unifsys12_sys :: SOMetaUnifSystem
unifsys12_sys = USys unifsys12_sig [unifsys12_eq1,unifsys12_eq2,unifsys12_eq3]

unifsys12_as :: AnswerSet SOMetaUnifSystem SOMetaUnifSysSolution
unifsys12_as = ImplicitAS unifsys12_sys

unifsys12_cheq1_1 :: SOMetaUnifEquation
unifsys12_cheq1_1 = read "F0[2](x0,x1) = f0[2]{F1[2],F2[2]}(x0,x1)"

unifsys12_chsys1 :: [SOMetaUnifEquation]
unifsys12_chsys1 = [unifsys12_cheq1_1]

unifsys12_sol1 :: SOMetaUnifSysSolution
unifsys12_sol1 = UnifSysSolution (fromList [(read "F0[2]", read "f0[2]{pi0,pi1}")]) (fromList [])

unifsys12_sol2 :: SOMetaUnifSysSolution
unifsys12_sol2 = UnifSysSolution (fromList [(read "F0[2]", read "f0[2]{pi1,pi0}")]) (fromList [])

unifsys12_sol3 :: SOMetaUnifSysSolution
unifsys12_sol3 = UnifSysSolution (fromList [(read "F0[2]", read "f0[2]{pi0,pi0}")]) (fromList [])

unifsys12_t1 :: AutomatedTest
unifsys12_t1 = check_min_exp_as "Checking that the equation system has at least 1 solution" 1 unifsys12_as

unifsys12_t2 :: AutomatedTest
unifsys12_t2 = check_en_all_usol unifsys12_nsols "Checking F0[2] = f0[2]{F1[2],F2[2]} is true for every solution" (\title -> \sol -> check_usys_usol_at title unifsys12_chsys1 sol) unifsys12_as

unifsys12_t3 :: AutomatedTest
unifsys12_t3 = check_imp_usol "Checking F0[2] = f0[2]{pi0,pi1} is implicitly a solution" unifsys12_sol1 unifsys12_as

unifsys12_t4 :: AutomatedTest
unifsys12_t4 = check_not_imp_usol "Checking F0[2] = f0[2]{pi1,pi0} is not implicitly a solution" unifsys12_sol2 unifsys12_as

unifsys12_t5 :: AutomatedTest
unifsys12_t5 = check_not_imp_usol "Checking F0[2] = f0[2]{pi0,pi0} is not implicitly a solution" unifsys12_sol3 unifsys12_as

unifsys12_tests :: String
unifsys12_tests = combine_test_results [unifsys12_t1,unifsys12_t2,unifsys12_t3,unifsys12_t4,unifsys12_t5]

unifsys13_nsols :: Int
unifsys13_nsols = 20

unifsys13_sig :: SOMetaSignature
unifsys13_sig = SOSignature (Signature [EnumProc.Empty, EnumProc.Empty, read "p0[2]" --> EnumProc.Empty] [EnumProc.Empty, read "f2[1]" --> EnumProc.Empty, read "f0[2]" --> read "f1[2]" --> EnumProc.Empty] (read "x0" --> read "x1" --> read "x2" --> read "x3" --> EnumProc.Empty)) (read "F0[2]" --> EnumProc.Empty) (read "P0[2]" --> EnumProc.Empty) EnumProc.Empty

unifsys13_eq1 :: SOMetaUnifEquation
unifsys13_eq1 = read "u0 x0 = u0 f0[2](x1,x2)"

unifsys13_eq2 :: SOMetaUnifEquation
unifsys13_eq2 = read "u1 x0 = u1 f2[1](x1)"

unifsys13_eq3 :: SOMetaUnifEquation
unifsys13_eq3 = read "u1 u0 P0[2](f2[1](x2),x2) ~ u1 u0 p0[2](x1,x2)"

unifsys13_sys :: SOMetaUnifSystem
unifsys13_sys = USys unifsys13_sig [unifsys13_eq1,unifsys13_eq2,unifsys13_eq3]

unifsys13_as :: AnswerSet SOMetaUnifSystem SOMetaUnifSysSolution
unifsys13_as = ImplicitAS unifsys13_sys

unifsys13_sol1 :: SOMetaUnifSysSolution
unifsys13_sol1 = UnifSysSolution (fromList []) (fromList [(read "P0[2]", read "p0[2]{pi0,pi1}")])

unifsys13_sol2 :: SOMetaUnifSysSolution
unifsys13_sol2 = UnifSysSolution (fromList []) (fromList [(read "P0[2]", read "p0[2]{pi1,pi0}")])

unifsys13_sol3 :: SOMetaUnifSysSolution
unifsys13_sol3 = UnifSysSolution (fromList []) (fromList [(read "P0[2]", read "p0[2]{pi0,pi0}")])

unifsys13_t1 :: AutomatedTest
unifsys13_t1 = check_min_exp_as "Checking that the equation system has at least 1 solution" 1 unifsys13_as

unifsys13_t3 :: AutomatedTest
unifsys13_t3 = check_imp_usol "Checking P0[2] = p0[2]{pi0,pi1} is implicitly a solution" unifsys13_sol1 unifsys13_as

unifsys13_t4 :: AutomatedTest
unifsys13_t4 = check_not_imp_usol "Checking P0[2] = p0[2]{pi1,pi0} is not implicitly a solution" unifsys13_sol2 unifsys13_as

unifsys13_t5 :: AutomatedTest
unifsys13_t5 = check_not_imp_usol "Checking P0[2] = p0[2]{pi0,pi0} is not implicitly a solution" unifsys13_sol3 unifsys13_as

unifsys13_tests :: String
unifsys13_tests = combine_test_results [unifsys13_t1,unifsys13_t3,unifsys13_t4,unifsys13_t5]



unifsys_test :: IO ()
unifsys_test = putStr "EXAMPLE 1\n\n" >> putStr unifsys1_tests >>
		putStr "EXAMPLE 2\n\n" >> putStr unifsys2_tests >>
		putStr "EXAMPLE 3\n\n" >> putStr unifsys3_tests >>
		putStr "EXAMPLE 4\n\n" >> putStr unifsys4_tests >>
		putStr "EXAMPLE 5\n\n" >> putStr unifsys5_tests >>
		putStr "EXAMPLE 6\n\n" >> putStr unifsys6_tests >>
		putStr "EXAMPLE 7\n\n" >> putStr unifsys7_tests >>
		putStr "EXAMPLE 8\n\n" >> putStr unifsys8_tests >>
		putStr "EXAMPLE 9\n\n" >> putStr unifsys9_tests >>
		putStr "EXAMPLE 10\n\n" >> putStr unifsys10_tests >>
		putStr "EXAMPLE 11\n\n" >> putStr unifsys11_tests >>
		putStr "EXAMPLE 12\n\n" >> putStr unifsys12_tests >>
		putStr "EXAMPLE 13\n\n" >> putStr unifsys13_tests



all_test :: IO ()
all_test = putStr "DEPENDENCY GRAPH OPERATION TESTS\n\n\n" >> dgraphop_test >>
		putStr "UNIFICATION SYSTEM SOLVING TESTS\n\n\n" >> unifsys_test
