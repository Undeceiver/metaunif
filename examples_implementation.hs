{-# LANGUAGE PartialTypeSignatures #-}
import Constraints
import Metaresolution
--import Metaresolution_tests
import AutoTests
import Metaresolution_heuristics

-----------------------------------------------
-- MARGHERITAS ARE PEPPER PIZZAS
-----------------------------------------------

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
--	[-p1[1](f1[0]()),+p3[2](f2[0](),f3[0]())]\
--]"
pepper_cnf = read "[[-p1[1](x0),+p2[1](x0)],[-p1[1](x0),-p3[2](x0,x1),+p4[1](x1)],[-p2[1](x0),+p3[2](x0,f4[1](x0)),+p1[1](x0)],[-p2[1](x0),-p4[1](f4[1](x0)),+p1[1](x0)],[-p5[1](x0),+p2[1](x0)],[-p5[1](x0),-p3[2](x0,x1)],[-p2[1](x0),+p3[2](x0,f5[1](x0)),+p5[1](x0)],[+X0,+X1],[+X0,+p3[2](f2[0](),f3[0]())],[+X1,-p1[1](f1[0]())],[-p1[1](f1[0]()),+p3[2](f2[0](),f3[0]())]]"

pepper_sols = enumerate_cnf_unsat_instantiations (numeric_metaresolution_heuristic_2 pepper_maxproofdepth) default_metaunification_heuristic pepper_sig pepper_mvs pepper_cnf

run_pepper_sols :: IO ()
run_pepper_sols = show_all_unsat_instantiations pepper_sig pepper_mvs pepper_sols

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
--pepper_nmv_cnf = read "[[-p1[1](x0),+p2[1](x0)],[-p1[1](x0),-p3[2](x0,x1),+p4[1](x1)],[-p2[1](x0),+p3[2](x0,f4[1](x0)),+p1[1](x0)],[-p2[1](x0),-p4[1](f4[1](x0)),+p1[1](x0)],[-p5[1](x0),+p2[1](x0)],[-p5[1](x0),-p3[2](x0,x1)],[-p2[1](x0),+p3[2](x0,f5[1](x0)),+p5[1](f1[0]())],[+p5[1](f1[0]()),+p5[1](f2[0]())],[+p5[1](f1[0]()),+p3[2](f2[0](),f3[0]())],[+p5[1](f2[0]()),-p1[1](f1[0]())],[-p1[1](f1[0]()),+p3[2](f2[0](),f3[0]())]]"
-- ALL FROM HERE DOWNWARDS WORK
pepper_nmv_cnf = read "[[-p2[1](x0),+p3[2](x0,f4[1](x0)),+p1[1](x0)],[-p5[1](x0),+p2[1](x0)],[-p5[1](x0),-p3[2](x0,x1)],[+p5[1](f1[0]()),+p5[1](f2[0]())],[+p5[1](f1[0]()),+p3[2](f2[0](),f3[0]())],[+p5[1](f2[0]()),-p1[1](f1[0]())],[-p1[1](f1[0]()),+p3[2](f2[0](),f3[0]())]]"

pepper_nmv_sols = enumerate_cnf_unsat_instantiations (numeric_metaresolution_heuristic_2 pepper_maxproofdepth) default_metaunification_heuristic pepper_nmv_sig pepper_nmv_mvs pepper_nmv_cnf

run_pepper_nmv_sols :: IO ()
run_pepper_nmv_sols = show_all_unsat_instantiations pepper_nmv_sig pepper_nmv_mvs pepper_nmv_sols

run_pepper_nmv_sols_one :: IO ()
run_pepper_nmv_sols_one = show_nth_unsat_instantiation pepper_nmv_sig pepper_nmv_mvs pepper_nmv_sols 1







-----------------------------------------------
-- CHAIN OF IMPLICATIONS
-----------------------------------------------

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

run_unsat_f_sols :: Int -> IO ()
run_unsat_f_sols n = show_all_unsat_instantiations (unsat_f_sig n) unsat_f_mvs (unsat_f_sols n 15)






-----------------------------------------------
-- SYNTAX
-----------------------------------------------

-- data Term = TVar Variable | TMeta Metavariable | TFun Function [Term] deriving Eq
-- data Metaterm = MTermT Term | MTermR Unifier Metaterm | MTermF Function [Metaterm] deriving Eq
-- data Dependent = DVar Variable | DMetaT Metavariable | DMetaL Metavariable | DRec Unifier Dependent deriving Eq
-- data MetatermModUnif = MTermFixed Term | MTermTMU Term | MTermRMU Unifier MetatermModUnif | MTermFMU Function [MetatermModUnif]
-- data DependencyConstraintSide = DDep Dependent | DFun [Dependent] TermHorizontalDependency | DFixedT Term | DFixedL Literal
-- type DependencyGraphSolution = [(Dependent,Either Term Literal)]

-- Possible sources of multiforest edges in the middle of the reduction: Actual dependents, fixed values or a function or predicate applied to other pseudodependents.
-- Predicates cannot occur, so we don't consider them.
-- In theory, fixed literals also cannot occur, because they'd have to be metavariables without unifiers, but it's worth keeping around just in case our way to handle metavariables changes.
-- data PseudoDependent = PDDep Dependent | PDFixedT Term | PDFixedL Literal | PDRecF Function [PseudoDependent] 
-- data PseudoDependentHead = PDHeadVoid | PDHeadF Function
-- data PseudoDependentBody = PDBodyVoidD Dependent | PDBodyVoidV Variable | PDBodyVoidM Metavariable | PDBodyF [PseudoDependent] | PDBodyFixedF [Term] | PDBodySubD Dependent PseudoDependentBody
-- type PseudoDependentDecomposition = (PseudoDependentHead,PseudoDependentBody)


-- apply_subst :: Substitution -> Term -> Term
-- apply_inst_term :: Instantiation -> Term -> Term
-- apply_inst_mterm :: Instantiation -> Metaterm -> Metaterm
-- replace_mterm_mterm :: Metaterm -> Metaterm -> Metaterm -> Metaterm
-- substitute_unifier_metaterm :: Unifier -> Substitution -> Metaterm -> Metaterm
-- apply_graph_solution_term :: DependencyGraphSolution -> Metaterm -> Metaterm

-- Normalize metaterms and metaliterals by making them of the form "u ml", using the identity if necessary.
-- Notice that these functions are *not* recursive.
-- norm_mterm :: Metaterm -> Metaterm
-- simpl_mterm :: Metaterm -> Metaterm
-- all_simpl_mterm :: Metaterm -> Metaterm

-- extract_inner_term :: Metaterm -> MetatermModUnif

-- decompose_pseudodep :: PseudoDependent -> PseudoDependentDecomposition
-- The difference with normal decomposition is that, if the pseudodependent is a dependent with one incoming dependency, returns the head for that incoming dependency, and a PDBodySubD body with the dependent and the body for the incoming pseudodependent.
-- Functions using this result can use this to know that there is a dependent there, but also know what the actual body of the dependent needs to look like.
-- decompose_pseudodep_in_graph :: DependencyGraph -> PseudoDependent -> PseudoDependentDecomposition





-----------------------------------------------
-- HEURISTICS
-----------------------------------------------

-- Efficient way to encode relevant sets of variables
-- data VariableSet = Dom Unifier | Rg Unifier deriving (Eq, Show)

-- type LiteralEnumeration h = ExtendedSignature -> VariableSet -> [Variable] -> (Variable -> Bool) -> Enumeration (h,Literal)
-- type TermEnumeration h = ExtendedSignature -> VariableSet -> [Variable] -> (Variable -> Bool) -> Enumeration (h,Term)
-- type MetaunificationHeuristic hl ht = (Maybe (LiteralEnumeration hl),Maybe (TermEnumeration ht))



-- type ClauseEnumeration h = ExtendedSignature -> CNF -> Enumeration (h,Int)
-- type InClauseLiteralChoice = ExtendedSignature -> (FullSolution,LogicalInstantiation) -> CNF -> Int -> [Int]
-- type ResolventEnumeration h = ExtendedSignature -> (FullSolution,LogicalInstantiation) -> CNF -> Int -> Int -> Maybe (Enumeration (h,(Int,Int)))
-- type MetaresolutionHeuristic hresenum hclauseenum = (InClauseLiteralChoice,ResolventEnumeration hresenum,ClauseEnumeration hclauseenum,Int)







-----------------------------------------------
-- NON-DETERMINISM
-----------------------------------------------

-- diagonalize_h :: (a -> Enumeration (h2,b)) -> Enumeration (h1,a) -> Enumeration (Diagonalizer h1 a h2 b,b)
-- recursively_diagonalize_h :: (t -> Either ([r] -> Enumeration (h1,r)) (t,([r] -> Enumeration (h1,r),CombinationScheme r))) -> (t -> Enumeration (RecursiveDiagonalization h1 r,r))
-- data CombinationScheme r = Comb (r -> r -> r) (r -> (r,r))

naturals :: Enumeration ((),Int)
naturals = Enum ((),1) (\idx -> \(_,prev) -> Just ((),prev + 1))

multiples :: Int -> Enumeration ((),(Int,Int))
multiples n = Enum ((),(n,0)) (\idx -> \(_,(_,prev)) -> Just ((),(n,prev + n)))

naturals_and_multiples :: Enumeration (_,(Int,Int))
naturals_and_multiples = diagonalize_h multiples naturals

show_naturals_and_multiples :: IO ()
show_naturals_and_multiples = print (show (enum_up_to_h 100 naturals_and_multiples))


multiples_2 :: Int -> Enumeration ((),[Int])
multiples_2 n = Enum ((),[0]) (\idx -> \(_,(prev:_)) -> Just ((),[prev + n]))

multiples_comb_scheme :: CombinationScheme [Int]
multiples_comb_scheme = Comb (\prev -> \new -> new ++ prev) (\(new:prev) -> (prev,[new]))

multiples_decision :: [Int] -> Either ([[Int]] -> Enumeration (_,[Int])) ([Int],([[Int]] -> Enumeration (_,[Int]),CombinationScheme [Int]))
multiples_decision [] = Left (\is -> enum_hleft_h (enum_from_list [[]]))
multiples_decision (x:xs) = Right (xs,(\rs -> enum_hright_h (multiples_decision_helper x rs),multiples_comb_scheme))

multiples_decision_helper :: Int -> [[Int]] -> Enumeration (_,[Int])
multiples_decision_helper x [] = multiples_2 x
multiples_decision_helper x ((i:is):js) = multiples_2 (x + i)

all_multiples :: [Int] -> Enumeration (_,[Int])
all_multiples xs = apply_enum_1_h reverse (recursively_diagonalize_h multiples_decision xs)

show_all_multiples :: [Int] -> IO()
show_all_multiples i = print (show (enum_up_to_h 100 (all_multiples i)))




-----------------------------------------------
-- DEPENDENCY GRAPH DATA STRUCTURE
-----------------------------------------------

-- data DependencyGraph = DGraph (RSet DependencyNode) [EqDependencyClass] EqDepDAG

-- add_outgoing_hdep :: HDependencyEdge -> DependencyNode -> DependencyNode
-- del_outgoing_hdep :: HDependencyEdge -> DependencyNode -> DependencyNode
-- update_outgoing_hdep :: HDependencyEdge -> HDependencyEdge -> DependencyNode -> DependencyNode
-- add_incoming_hdep :: HDependencyEdge -> DependencyNode -> DependencyNode
-- del_incoming_hdep :: HDependencyEdge -> DependencyNode -> DependencyNode
-- update_incoming_hdep :: HDependencyEdge -> HDependencyEdge -> DependencyNode -> DependencyNode
-- add_outgoing_vdep :: VDependencyEdge -> DependencyNode -> DependencyNode
-- del_outgoing_vdep :: VDependencyEdge -> DependencyNode -> DependencyNode
-- update_outgoing_vdep :: VDependencyEdge -> VDependencyEdge -> DependencyNode -> DependencyNode
-- add_incoming_vdep :: VDependencyEdge -> DependencyNode -> DependencyNode
-- del_incoming_vdep :: VDependencyEdge -> DependencyNode -> DependencyNode
-- update_incoming_vdep :: VDependencyEdge -> VDependencyEdge -> DependencyNode -> DependencyNode


-- do_one_update_to_graph :: ExtendedSignature -> (FullSolution -> t -> (FullSolution,[Dependent])) -> FullSolution -> t -> (FullSolution,[(Dependent,Either Term Literal)])

-- Updates the graph as long as there is something to update that is certain (i.e. no search).
-- We have two lists, the ones that we did not consider even for horizontal updates and those that are pending updating through vertical updates.
-- update_graph_all :: ExtendedSignature -> FullSolution -> [(Dependent, Either Term Literal)] -> [(Dependent, Either Term Literal)] -> FullSolution

-- Finds all leaves, and then factorizes from every and each of them.
-- factorize_dgraph_all :: FullSolution -> (FullSolution,[(Dependent,Either Term Literal)])

u0 :: Unifier
u0 = U 0

u1 :: Unifier
u1 = U 1

xmt21 :: Metaterm
xmt21 = MTermR u0 (MTermT (read "f1[1](X0)"))

xmt22 :: Metaterm
xmt22 = MTermR u0 (MTermT (read "f1[1](x0)"))

xmt23 :: Metaterm
xmt23 = MTermR u0 (MTermT (read "x1"))

xmt24 :: Metaterm
xmt24 = MTermR u1 (MTermT (read "f1[1](x0)"))

xmt25 :: Metaterm
xmt25 = MTermR u1 (MTermT (read "x1"))

xc21 :: Constraint
xc21 = Tcstr xmt21 xmt23

xc22 :: Constraint
xc22 = Tcstr xmt22 xmt23

xc23 :: Constraint
xc23 = Tcstr xmt24 xmt25

xcs2 = [xc21,xc22,xc23]

(xrmvs2,(xrinst2,xscs2)) = all_simpl_cstr [read "X0"] (idinst,xcs2)

xg2 = build_graph_from_constraints xscs2







-----------------------------------------------
-- BIG DATA STRUCTURES CARRIED AROUND
-----------------------------------------------

-- type Signature = ([Predicate],[Function],Int)
-- type MetavariablePartition = ([[Metavariable]],Int,[Int])
-- type MetavariableLink = (Metavariable,[(Metavariable,Either Term Literal -> Either Term Literal)])
-- type ExtendedSignature = (Signature,MetavariablePartition,[Term],[MetavariableLink])
-- type DependencyGraphSolution = [(Dependent,Either Term Literal)]
-- type PartiallySolvedDGraph = (DependencyGraph,DependencyGraphSolution,[UnifierEquation])
-- type FullSolution = ([Metavariable],[MetavariableEquation],UnifSolution,PartiallySolvedDGraph)


-- do_one_update_to_graph :: ExtendedSignature -> (FullSolution -> t -> (FullSolution,[Dependent])) -> FullSolution -> t -> (FullSolution,[(Dependent,Either Term Literal)])









































-- instantiation_from_dgraph_sol_step :: ExtendedSignature -> FullSolution -> [Unifier] -> Either ([(Maybe ([UnifierDescription],Instantiation),[Either (Metaterm,Term) (Metaliteral,Literal)])] -> Enumeration (_,(Maybe ([UnifierDescription],Instantiation),[Either (Metaterm,Term) (Metaliteral,Literal)]))) ([Unifier],([(Maybe ([UnifierDescription],Instantiation),[Either (Metaterm,Term) (Metaliteral,Literal)])] -> Enumeration (_,(Maybe ([UnifierDescription],Instantiation),[Either (Metaterm,Term) (Metaliteral,Literal)])),CombinationScheme ((Maybe ([UnifierDescription],Instantiation),[Either (Metaterm,Term) (Metaliteral,Literal)]))))
