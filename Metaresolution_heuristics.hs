{-# LANGUAGE PartialTypeSignatures #-}
module Metaresolution_heuristics where

import Metaresolution
import Constraints
import Data.List
import Data.Maybe
import Data.Either

remove_unifs_term :: Metaterm -> Metaterm
remove_unifs_term (MTermR _ t) = remove_unifs_term t
remove_unifs_term (MTermT t) = MTermT t
remove_unifs_term (MTermF f ts) = MTermF f (map remove_unifs_term ts)

remove_unifs_atom :: Metaliteral -> Metaliteral
remove_unifs_atom (MLitR _ l) = remove_unifs_atom l
remove_unifs_atom (MLitL l) = MLitL l
remove_unifs_atom (MLitP p ts) = MLitP p (map remove_unifs_term ts)

remove_unifs_lit :: ActualLiteral -> ActualLiteral
remove_unifs_lit (PosLit l) = PosLit (remove_unifs_atom l)
remove_unifs_lit (NegLit l) = NegLit (remove_unifs_atom l)

remove_unifs_clause :: Clause -> Clause
remove_unifs_clause cl = map remove_unifs_lit cl

remove_unifs_cnf :: CNF -> CNF
remove_unifs_cnf cnf = map remove_unifs_clause cnf

term_like :: Metaterm -> Metaterm -> Bool
term_like mt1 mt2 = (remove_unifs_term mt1) == (remove_unifs_term mt2)

atom_like :: Metaliteral -> Metaliteral -> Bool
atom_like ml1 ml2 = (remove_unifs_atom ml1) == (remove_unifs_atom ml2)

lit_like :: ActualLiteral -> ActualLiteral -> Bool
lit_like l1 l2 = (remove_unifs_lit l1) == (remove_unifs_lit l2)

clause_like :: Clause -> Clause -> Bool
clause_like cl1 cl2 = (remove_unifs_clause cl1) == (remove_unifs_clause cl2)

cnf_like :: CNF -> CNF -> Bool
cnf_like cnf1 cnf2 = (remove_unifs_cnf cnf1) == (remove_unifs_cnf cnf2)

-- Specific clause enumeration: Give a list of clauses (first one to apply comes first in the input). This heuristic then tries to always apply resolution to the latest of these clauses (or something that looks like it) if that is possible. Keep in mind that this may not work perfectly if similar clauses are used throughout the proof. But this should not really happen??
specific_clause_enum :: [Clause] -> ClauseEnumeration _
specific_clause_enum cls sig cnf = enum_from_list (specific_clause_enum_helper (reverse cls) sig cnf)

specific_clause_enum_helper :: [Clause] -> ExtendedSignature -> CNF -> [Int]
-- If there are no more hints, just try in order.
specific_clause_enum_helper [] sig cnf = [0..((length cnf) - 1)]
--specific_clause_enum_helper [] sig cnf = []
specific_clause_enum_helper (cl:cls) sig cnf = case res of {Nothing -> rest; Just rcl -> rcl:rest} where res = findIndex (clause_like cl) cnf; rest = specific_clause_enum_helper cls sig cnf

specific_lit_choice :: [ActualLiteral] -> InClauseLiteralChoice
specific_lit_choice lits sig (fs,loginst) cnf iclause = specific_lit_choice_helper (reverse lits) sig (fs,loginst) cnf iclause

specific_lit_choice_helper :: [ActualLiteral] -> ExtendedSignature -> (FullSolution,LogicalInstantiation) -> CNF -> Int -> [Int]
-- If there are no more hints, just try in order
specific_lit_choice_helper [] sig (fs,loginst) cnf iclause = default_literal_choice sig (fs,loginst) cnf iclause
--specific_lit_choice_helper [] sig (fs,loginst) cnf iclause = []
specific_lit_choice_helper (lit:lits) sig (fs,loginst) cnf iclause = case res of {Nothing -> rest; Just rlit -> rlit:rest} where res = findIndex (lit_like lit) (cnf !! iclause); rest = specific_lit_choice_helper lits sig (fs,loginst) cnf iclause

specific_resolvent_enum :: [(Clause,ActualLiteral)] -> ResolventEnumeration _
specific_resolvent_enum rss sig (fs,loginst) cnf iclause ilit = Just (enum_from_list (specific_resolvent_enum_helper (reverse rss) sig (fs,loginst) cnf iclause ilit))

specific_resolvent_enum_helper :: [(Clause,ActualLiteral)] -> ExtendedSignature -> (FullSolution,LogicalInstantiation) -> CNF -> Int -> Int -> [(Int,Int)]
-- If there are no more hints, just try in order 
specific_resolvent_enum_helper [] sig (fs,loginst) cnf iclause ilit = enum_up_to_h infinity (fromJust (choose_complementary_literal cnf iclause ilit))
--specific_resolvent_enum_helper [] sig (fs,loginst) cnf iclause ilit = []
specific_resolvent_enum_helper ((cl,lit):rss) sig (fs,loginst) cnf iclause ilit = case resClause of {Nothing -> rest; Just rcl -> case resLit of {Nothing -> rest; Just rlit -> (rcl,rlit):rest}} where resClause = findIndex (clause_like cl) cnf; rcl = fromJust resClause; resLit = findIndex (lit_like lit) (cnf !! rcl); rest = specific_resolvent_enum_helper rss sig (fs,loginst) cnf iclause ilit



-- More realistic heuristics, but still very simple.
-- Clause with least literals first.
least_size_clause_enum :: ClauseEnumeration _
least_size_clause_enum sig cnf = enum_from_list (least_size_clause_enum_helper sig cnf [] (\x -> x))

-- We do insert sort, as we do not really expect the CNF to have a large number of clauses (there would be plenty of other problems if that were the case)
least_size_clause_enum_helper :: ExtendedSignature -> [Clause] -> [Int] -> (Int -> Int) -> [Int]
least_size_clause_enum_helper sig [] res adjust = reverse res
least_size_clause_enum_helper sig (cl:cls) res adjust = least_size_clause_enum_helper sig rem (rfirst:res) (adjust . (least_size_clause_enum_adjuster first)) where (first,rem) = least_size_clause_enum_helper_2 0 cl (length cl) cls 1 []; rfirst = adjust first

least_size_clause_enum_adjuster :: Int -> Int -> Int
least_size_clause_enum_adjuster removed x | x < removed = x
least_size_clause_enum_adjuster removed x = (x+1)

least_size_clause_enum_helper_2 :: Int -> Clause -> Int -> [Clause] -> Int -> [Clause] -> (Int,[Clause])
least_size_clause_enum_helper_2 ipref pref lpref [] i rem = (ipref,rem)
least_size_clause_enum_helper_2 ipref pref lpref (cl:cls) i rem | lcl < lpref = least_size_clause_enum_helper_2 i cl lcl cls (i+1) (insert_at_pos rem ipref pref) where lcl = length cl
least_size_clause_enum_helper_2 ipref pref lpref (cl:cls) i rem = least_size_clause_enum_helper_2 ipref pref lpref cls (i+1) (rem ++ [cl])

insert_at_pos :: [t] -> Int -> t -> [t]
insert_at_pos xs 0 y = y:xs
insert_at_pos (x:xs) i y = x:(insert_at_pos xs (i-1) y)
insert_at_pos [] _ y = [y]

count :: (a -> Bool) -> [a] -> Int
count cond = length . filter cond


-- Literal which can be resolved with the least others first.
--type InClauseLiteralChoice = ExtendedSignature -> (FullSolution,LogicalInstantiation) -> CNF -> Int -> [Int]
least_frequent_lit_choice :: InClauseLiteralChoice
least_frequent_lit_choice _ _ cnf iclause = [least_frequent_lit_choice_helper cnf 0 (sum (map (\cl -> count (can_resolve_literals (head (cnf !! iclause))) cl) cnf)) (rest (cnf !! iclause)) 1]

-- We know we will only really use the first one, so we only return that one in this heuristic, to avoid extra computations.
least_frequent_lit_choice_helper :: CNF -> Int -> Int -> [ActualLiteral] -> Int -> Int
least_frequent_lit_choice_helper cnf ipref npref [] i = ipref
least_frequent_lit_choice_helper cnf ipref npref (l:ls) i | nl < npref = least_frequent_lit_choice_helper cnf i nl ls (i+1) where nl = sum (map (\cl -> count (can_resolve_literals l) cl) cnf)
least_frequent_lit_choice_helper cnf ipref npref (l:ls) i = least_frequent_lit_choice_helper cnf ipref npref ls (i+1)


-- Resolvent in the clause with the least literals
-- type ResolventEnumeration h = ExtendedSignature -> (FullSolution,LogicalInstantiation) -> CNF -> Int -> Int -> Maybe (Enumeration (h,(Int,Int)))
least_size_resolvent_enum :: ResolventEnumeration _
least_size_resolvent_enum _ _ cnf iclause ilit = case aslist of {[] -> Nothing; otherwise -> Just (enum_from_list (map (\(a,b,_) -> (a,b)) aslist))} where clause = cnf !! iclause; lit = clause !! ilit; aslist = least_size_resolvent_enum_helper cnf clause lit 0 0 (length cnf) (case cnf of {[] -> 0; (h:_) -> (length h)}) iclause

-- This is like the naive one, except when it has to insert the newly found resolvent, it makes sure it does so in the list in the position which corresponds to the length of its clause, and including the length data.
least_size_resolvent_enum_helper :: CNF -> Clause -> ActualLiteral -> Int -> Int -> Int -> Int -> Int -> [(Int,Int,Int)]
least_size_resolvent_enum_helper cnf clause lit ccl clit lcnf lclause bcl | ccl >= lcnf = []
least_size_resolvent_enum_helper cnf clause lit ccl clit lcnf lclause bcl | clit >= lclause = least_size_resolvent_enum_helper cnf clause lit (ccl+1) 0 lcnf (length (cnf !! (ccl+1))) bcl
least_size_resolvent_enum_helper cnf clause lit ccl clit lcnf lclause bcl | ccl == bcl = least_size_resolvent_enum_helper cnf clause lit (ccl+1) 0 lcnf (length (cnf !! (ccl+1))) bcl
least_size_resolvent_enum_helper cnf clause lit ccl clit lcnf lclause bcl | (can_resolve_literals lit plit) = least_size_resolvent_enum_helper_2 (least_size_resolvent_enum_helper cnf clause lit ccl (clit+1) lcnf lclause bcl) (ccl,clit,length pclause) where pclause = cnf !! ccl; plit = pclause !! clit
least_size_resolvent_enum_helper cnf clause lit ccl clit lcnf lclause bcl = least_size_resolvent_enum_helper cnf clause lit ccl (clit+1) lcnf lclause bcl

least_size_resolvent_enum_helper_2 :: [(Int,Int,Int)] -> (Int,Int,Int) -> [(Int,Int,Int)]
least_size_resolvent_enum_helper_2 [] (ccl,clit,cclen) = [(ccl,clit,cclen)]
least_size_resolvent_enum_helper_2 ((pcl,plit,pclen):rs) (ccl,clit,cclen) | cclen <= pclen = (ccl,clit,cclen):(pcl,plit,pclen):rs
least_size_resolvent_enum_helper_2 ((pcl,plit,pclen):rs) (ccl,clit,cclen) = (pcl,plit,pclen):(least_size_resolvent_enum_helper_2 rs (ccl,clit,cclen))

-- Slightly more complex resolvent enumeration: Resolvent in the clause with the least literals <<that are not resolvable with literals in the original clause choice>>
least_new_resolvent_enum :: ResolventEnumeration _
least_new_resolvent_enum _ _ cnf iclause ilit = case aslist of {[] -> Nothing; otherwise -> Just (enum_from_list (map (\(a,b,_) -> (a,b)) aslist))} where clause = cnf !! iclause; lit = clause !! ilit; aslist = least_new_resolvent_enum_helper cnf clause lit 0 0 (length cnf) (case cnf of {[] -> 0; (h:_) -> (length h)}) iclause

-- This is like the naive one, except when it has to insert the newly found resolvent, it makes sure it does so in the list in the position which corresponds to the length of its clause (save resolvable ones), and including the length data.
least_new_resolvent_enum_helper :: CNF -> Clause -> ActualLiteral -> Int -> Int -> Int -> Int -> Int -> [(Int,Int,Int)]
least_new_resolvent_enum_helper cnf clause lit ccl clit lcnf lclause bcl | ccl >= lcnf = []
least_new_resolvent_enum_helper cnf clause lit ccl clit lcnf lclause bcl | clit >= lclause = least_new_resolvent_enum_helper cnf clause lit (ccl+1) 0 lcnf (length (cnf !! (ccl+1))) bcl
least_new_resolvent_enum_helper cnf clause lit ccl clit lcnf lclause bcl | ccl == bcl = least_new_resolvent_enum_helper cnf clause lit (ccl+1) 0 lcnf (length (cnf !! (ccl+1))) bcl
least_new_resolvent_enum_helper cnf clause lit ccl clit lcnf lclause bcl | (can_resolve_literals lit plit) = least_new_resolvent_enum_helper_2 (least_new_resolvent_enum_helper cnf clause lit ccl (clit+1) lcnf lclause bcl) (ccl,clit,least_new_resolvent_enum_helper_3 clause pclause) where pclause = cnf !! ccl; plit = pclause !! clit
least_new_resolvent_enum_helper cnf clause lit ccl clit lcnf lclause bcl = least_new_resolvent_enum_helper cnf clause lit ccl (clit+1) lcnf lclause bcl

least_new_resolvent_enum_helper_2 :: [(Int,Int,Int)] -> (Int,Int,Int) -> [(Int,Int,Int)]
least_new_resolvent_enum_helper_2 [] (ccl,clit,cclen) = [(ccl,clit,cclen)]
least_new_resolvent_enum_helper_2 ((pcl,plit,pclen):rs) (ccl,clit,cclen) | cclen <= pclen = (ccl,clit,cclen):(pcl,plit,pclen):rs
least_new_resolvent_enum_helper_2 ((pcl,plit,pclen):rs) (ccl,clit,cclen) = (pcl,plit,pclen):(least_new_resolvent_enum_helper_2 rs (ccl,clit,cclen))

least_new_resolvent_enum_helper_3 :: Clause -> Clause -> Int
least_new_resolvent_enum_helper_3 scl pcl = count (\lit -> not (any (can_resolve_literals lit) scl)) pcl

-- Same as before, but we use the clause enumeration to only enumerate resolvents in clauses that come afterwards in the clause enumeration
least_new_resolvent_enum_norep :: ClauseEnumeration t -> ResolventEnumeration _
-- When it is the last one, it means it might be fixed due to a continuation. We don't do too clever things then. This is not beautiful, to be honest.
least_new_resolvent_enum_norep cenum sig otherstuff cnf iclause ilit | iclause == ((length cnf) - 1) = least_new_resolvent_enum sig otherstuff cnf iclause ilit
least_new_resolvent_enum_norep cenum sig otherstuff cnf iclause ilit = case aslist of {[] -> Nothing; otherwise -> Just (enum_from_list (map (\(a,b,_) -> (a,b)) aslist))} where clause = cnf !! iclause; lit = clause !! ilit; all_clauses = (enum_up_to_h infinity (cenum sig cnf)); clauses = least_new_resolvent_enum_norep_helper_666 iclause all_clauses; aslist = least_new_resolvent_enum_norep_helper cnf clause lit clauses 0 (case clauses of {[] -> 0; _ -> length (cnf !! (head clauses))}) iclause

-- Start with the next clause.
least_new_resolvent_enum_norep_helper_666 :: Int -> [Int] -> [Int]
least_new_resolvent_enum_norep_helper_666 i0 [] = []
least_new_resolvent_enum_norep_helper_666 i0 (i1:is) | i0 == i1 = is
least_new_resolvent_enum_norep_helper_666 i0 (i1:is) = least_new_resolvent_enum_norep_helper_666 i0 is

least_new_resolvent_enum_norep_helper :: CNF -> Clause -> ActualLiteral -> [Int] -> Int -> Int -> Int -> [(Int,Int,Int)]
least_new_resolvent_enum_norep_helper cnf clause lit [] clit lclause bcl = []
least_new_resolvent_enum_norep_helper cnf clause lit (ccl:cls) clit lclause bcl | clit >= lclause = least_new_resolvent_enum_norep_helper cnf clause lit cls 0 (length (cnf !! (head cls))) bcl
least_new_resolvent_enum_norep_helper cnf clause lit (ccl:cls) clit lclause bcl | ccl == bcl = least_new_resolvent_enum_norep_helper cnf clause lit cls 0 (length (cnf !! (head cls))) bcl
least_new_resolvent_enum_norep_helper cnf clause lit (ccl:cls) clit lclause bcl | (can_resolve_literals lit plit) = least_new_resolvent_enum_helper_2 (least_new_resolvent_enum_norep_helper cnf clause lit (ccl:cls) (clit+1) lclause bcl) (ccl,clit,least_new_resolvent_enum_helper_3 clause pclause) where pclause = cnf !! ccl; plit = pclause !! clit
least_new_resolvent_enum_norep_helper cnf clause lit (ccl:cls) clit lclause bcl = least_new_resolvent_enum_norep_helper cnf clause lit (ccl:cls) (clit+1) lclause bcl

simple_numeric_metaresolution_heuristic :: Int -> MetaresolutionHeuristic _ _
simple_numeric_metaresolution_heuristic maxdepth = (least_frequent_lit_choice,least_size_resolvent_enum,least_size_clause_enum,maxdepth)

numeric_metaresolution_heuristic_2 :: Int -> MetaresolutionHeuristic _ _
numeric_metaresolution_heuristic_2 maxdepth = (least_frequent_lit_choice,least_new_resolvent_enum,least_size_clause_enum,maxdepth)

