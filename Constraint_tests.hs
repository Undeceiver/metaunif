{-# LANGUAGE PartialTypeSignatures #-}
import Constraints

t1 :: Term
t1 = (read "f1[0]()")
t2 :: Term
t2 = (read "f2[2](f3[1](x1),x2)")

p :: Predicate
p = (read "p1[2]")

f :: Function
f = (read "f1[2]")

x :: Variable
x = (read "x1")

y :: Variable
y = (read "x2")

z :: Variable
z = (read "x3")

mx :: Metavariable
mx = (read "X1")

my :: Metavariable
my = (read "X2")

u :: Unifier
u = (U 1)

v :: Unifier
v = (U 2)

w :: Unifier
w = (U 3)

ml1 :: Metaliteral
ml1 = MLitR v (MLitR u (MLitL (Lit p [t1,t2])))

ml2 :: Metaliteral
ml2 = MLitR v (MLitL (LitM mx))

c1 :: Constraint
c1 = Lcstr ml1 ml2

ml3 :: Metaliteral
ml3 = MLitR w (MLitL (LitM mx))

ml4 :: Metaliteral
ml4 = MLitR w (MLitL (LitM my))

c2 :: Constraint
c2 = Lcstr ml3 ml4

d1 :: Dependent
d1 = DRec u (DVar x)

d2 :: Dependent
d2 = DRec u (DVar y)

d3 :: Dependent
d3 = DRec u (DVar z)

d4 :: Dependent
d4 = DRec v d1

d5 :: Dependent
d5 = DRec v d2

d6 :: Dependent
d6 = DRec v (DVar z)

hdep1 :: HorizontalDependency
hdep1 = THDep (FApp f [TInDependent,TInDependent])

vdep1 :: VerticalDependency
vdep1 = TVDep (\ux -> MTermR v (MTermT ux))

vdep2 :: VerticalDependency
vdep2 = TVDep (\uy -> MTermR v (MTermT uy))

phdep1 :: PossibleHorizontalDependency
phdep1 = PTHDep (\l -> case l of (ux:[]) -> \uy -> [])

g0 :: DependencyGraph
g0 = foldl add_node empty_graph [d1,d2,d3,d4,d5]

g1 :: DependencyGraph
g1 = add_hdep g0 hdep1 [d1,d2] d3

g2 :: DependencyGraph
g2 = add_vdep g1 vdep1 d1 d4

g3 :: DependencyGraph
g3 = add_vdep g2 vdep2 d2 d5

g4 :: DependencyGraph
g4 = add_phdep g3 phdep1 [d4] d5

oclist :: [Constraint]
oclist = [c1,c2]

ircs :: ([Metavariable],UnifSolution)
ircs = all_simpl_cstr [mx,my] (idinst,oclist)

clist :: [Constraint]
clist = (snd (snd ircs))

temp_gg :: DependencyGraph
(temp_gg,_,_) = foldl apply_dependency_constraint (empty_graph,[],[]) clist

gg :: DependencyGraph
gg = calculate_vertical_dependencies (foldl update_equivalence_classes temp_gg clist)

ggs :: PartiallySolvedDGraph
ggs = (gg,[],[])

tomega :: Term
tomega = read "f999[0]()"

hhd :: (DependencyGraph,[Dependent])
hhd = update_graph_from_value_hdep ggs (d4,Left tomega)

hh :: DependencyGraph
hh = fst hhd

dd :: [Dependent]
dd = snd hhd

-- Testing partial evaluation of dependencies.
tt :: Term -> Term
tt = (\t -> (TFun (read "f1[1]") [t]))

ts :: [Term]
ts = [t1,tt t1,tt (tt t1), tt (tt (tt t1)), tt (tt (tt (tt t1)))]

ff :: TermHorizontalDependency
ff = FApp (read "f15[5]") [TInDependent,TInDependent,TInDependent,TInDependent,TInDependent]

ds :: [Dependent]
ds = [d1,d2,d3,d4,d5]

tts = [t1,tt t1,tt (tt (tt t1)),tt (tt (tt (tt t1)))]

(r,_,_,_) = update_hdep_f_from_value d3 ds t2 [TInDependent,TInDependent,TInDependent,TInDependent,TInDependent]
rrff = apply_thdep_helper r tts
fft = apply_thdep (THDep ff) ts


-- Dependency graph solving
mt21 :: Metaterm
mt21 = MTermR u (MTermT (read "x1"))

mt22 :: Metaterm
mt22 = MTermR u (MTermT (read "f1[1](x2)"))

mt23 :: Metaterm
mt23 = MTermR u (MTermT (read "x3"))

mt24 :: Metaterm
--mt24 = MTermR v mt21
mt24 = MTermR v (MTermF (read "f1[1]") [mt21])

mt25 :: Metaterm
--mt25 = MTermR v mt22
mt25 = MTermR v (MTermF (read "f1[1]") [mt23])

mt26 :: Metaterm
mt26 = MTermR u (MTermT (read "f1[1](x1)"))

mt27 :: Metaterm
mt27 = MTermR u (MTermT (read "x4"))

c21 :: Constraint
c21 = Tcstr mt21 mt22

c22 :: Constraint
c22 = Tcstr mt21 mt23

c23 :: Constraint
c23 = Tcstr mt24 mt25

c24 :: Constraint
c24 = Tcstr mt26 mt27

ml21 :: Metaliteral
ml21 = MLitR u (MLitL (read "X1"))

ml22 :: Metaliteral
ml22 = MLitR u (MLitL (read "p1[2](x1,x2)"))

c25 :: Constraint
c25 = Lcstr ml21 ml22

oclist2 :: [Constraint]
oclist2 = [c21,c22,c23,c24]
--oclist2 = [c25]

ircs2 :: ([Metavariable],UnifSolution)
ircs2 = all_simpl_cstr [] (idinst,oclist2)

clist2 :: [Constraint]
clist2 = (snd (snd ircs2))

ggs2 :: PartiallySolvedDGraph
--gg2old = calculate_vertical_dependencies (foldl update_equivalence_classes (foldl apply_dependency_constraint empty_graph clist2) clist2)
--gg2 = foldl update_graph_with_constraints empty_graph clist2
ggs2 = build_graph_from_constraints clist2

d21 :: Dependent
d21 = DRec u (DVar (read "x2"))

d22 :: Dependent
d22 = DRec u (DVar (read "x1"))

fsolg :: FullSolution
fsolg = (fst ircs2,[],(fst (snd ircs2),[]),ggs2)

((mvs2,[],(hinst2,hcs2),(hh2,sol2,hueqs2)),rdeps2) = do_one_update_to_graph update_graph_from_value_hdep_full fsolg (d21,Left (read "x666"))
r2 :: FullSolution
r2 = (mvs2,[],(hinst2,hcs2),(hh2,sol2,hueqs2))
--r2 = do_one_update_to_graph update_graph_from_value_hdep_full (fsolg,[]) (d21,Left (read "x666"))
--hh2 :: DependencyGraph
--hh2 = (fst (fst r2))
--sol2 :: DependencyGraphSolution
--sol2 = (snd (fst r2))
--rdeps2 :: [(Dependent,Either Term Literal)]
--rdeps2 = snd r2
--(hh2,sol2,rdeps2) = case r2 of {((mvs,(inst,cs),(g,sol)),l) -> (g,sol,l)}

--(mvs3,(hinst3,hcs3)) = recalculate_constraints_eqdep mvs2 (hinst2,hcs2) (Left (MTermT (read "x1"))) (Left (MTermT (read "x777"))) hh2 [d22]
((mvs3,[],(hinst3,hcs3),(hh3,sol3,hueqs3)),rdeps3) = do_one_update_to_graph update_graph_from_value_vdep r2 ((DRec u (DVar (read "x1"))),Left (read "x777"))
r3 :: FullSolution
r3 = (mvs3,[],(hinst3,hcs3),(hh3,sol3,hueqs3))
--recalculate_constraints_eqdep :: [Metavariable] -> UnifSolution -> Either Metaterm Metaliteral -> Either Metaterm Metaliteral -> DependencyGraph -> [Dependent] -> ([Metavariable],UnifSolution)

dep_to_upd :: Dependent
dep_to_upd = (DRec u (DVar (read "x1")))

dep_value :: Term
dep_value = (read "f1[1](x666)")

r4 :: FullSolution
r4 = update_graph_all r2 [(dep_to_upd,Left (dep_value))] []
(mvs4,[],(hinst4,hcs4),(hh4,sol4,hueqs4)) = r4
(hh5,sol5,hueqs5) = clean_dep_graph (hh4,sol4,hueqs4)

r5 :: FullSolution
r5 = (mvs4,[],(hinst4,hcs4),(hh5,sol5,hueqs5))

r6 :: FullSolution
r6 = update_graph_all r5 [(dep_to_upd,Left (dep_value))] []

step_solns :: Int -> ([(Dependent,Either Term Literal)],(FullSolution,[(Dependent,Either Term Literal)]))
step_solns 1 = ([],(r2,[(dep_to_upd,Left dep_value)]))
step_solns i = case prev of {(vs,(s,(h:hs))) -> ((h:vs),(fst (do_one_update_to_graph update_graph_from_value_hdep_full s h),hs ++ (snd (do_one_update_to_graph update_graph_from_value_hdep_full s h))));
				((v:vs),(s,[])) -> (vs,do_one_update_to_graph update_graph_from_value_vdep s v);
				([],(s,[])) -> ([],(s,[]))}
				where prev = step_solns (i-1)

--update_graph_all fs [] (dv:dvs) s = update_graph_all rs rl dvs (s ++ rl) where (rs,rl) = do_one_update_to_graph update_graph_from_value_vdep (fs,s) dv
--update_graph_all fs (dh:dhs) dvs s = update_graph_all rs (dhs ++ rl) (dh:dvs) (s ++ rl) where (rs,rl) = do_one_update_to_graph update_graph_from_value_hdep_full (fs,s) dh


step_vs :: Int -> [(Dependent,Either Term Literal)]
step_vs i = fst (step_solns i)

step_hs :: Int -> [(Dependent,Either Term Literal)]
step_hs i = snd (snd (step_solns i))

step_s :: Int -> FullSolution
step_s i = fst (snd (step_solns i))


-- Testing DAGs
leaf :: DAGNode Integer
leaf = DAGNode 4 []

othernode :: DAGNode Integer
othernode = DAGNode 5 [leaf]

testdag :: DAG Integer
testdag = DAG [DAGNode 1 [DAGNode 2 [othernode], DAGNode 3 [othernode]]]








-- Testing proper systems where variables and unifiers have the ordering they must, and where there are meta-variables.
n_base_vars :: Int
n_base_vars = 2

-- Variables
x0 :: Variable
x0 = Var 0

x1 :: Variable
x1 = Var 1

-- Metavariables
mx0 :: Metavariable
mx0 = Metavar 0

mx1 :: Metavariable
mx1 = Metavar 1

metavars = [mx0,mx1]

-- Unifiers
u0 :: Unifier
u0 = U 0

u1 :: Unifier
u1 = U 1

-- Derived variables
x0u0 :: Variable
x0u0 = get_image_var n_base_vars u0 x0

x1u0 :: Variable
x1u0 = get_image_var n_base_vars u0 x1

-- Function symbols
f1 :: Function
f1 = read "f1[1]"

-- Predicate symbols
p1 :: Predicate
p1 = read "p1[1]"

xsig :: Signature
xsig = ([p1],[f1],n_base_vars)


-- Examples

-- Example 1
xmt11 :: Metaterm
xmt11 = MTermR u0 (MTermT (read "x0"))

xmt12 :: Metaterm
xmt12 = MTermR u0 (MTermT (read "f1[1](x1)"))

xc11 :: Constraint
xc11 = Tcstr xmt11 xmt12

xcs1 = [xc11]

(xrmvs1,(xrinst1,xscs1)) = all_simpl_cstr metavars (idinst,xcs1)

xg1 = build_graph_from_constraints xscs1

xfs1 :: FullSolution
xfs1 = (xrmvs1,[],(xrinst1,[]),xg1)

xres1 = find_best_root_class n_base_vars xfs1


-- Example 2
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

(xrmvs2,(xrinst2,xscs2)) = all_simpl_cstr metavars (idinst,xcs2)

xg2 = build_graph_from_constraints xscs2

xfs2 :: FullSolution
xfs2 = (xrmvs2,[],(xrinst2,[]),xg2)

xres2 = find_best_root_class n_base_vars xfs2


-- Example 3
xmt31 :: Metaterm
xmt31 = MTermR u0 (MTermT (read "f1[1](X0)"))

xmt32 :: Metaterm
xmt32 = MTermR u0 (MTermT (read "f1[1](x0)"))

xmt33 :: Metaterm
xmt33 = MTermR u0 (MTermT (read "x1"))

xc31 :: Constraint
xc31 = Tcstr xmt31 xmt33

xc32 :: Constraint
xc32 = Tcstr xmt32 xmt33

xcs3 = [xc31,xc32]

(xrmvs3,(xrinst3,xscs3)) = all_simpl_cstr metavars (idinst,xcs3)

xg3 = build_graph_from_constraints xscs3

xfs3 :: FullSolution
xfs3 = (xrmvs3,[],(xrinst3,[]),xg3)

xres3 = find_best_root_class n_base_vars xfs3


-- Example 4
xmt41 :: Metaterm
xmt41 = MTermR u0 (MTermT (read "f1[1](X0)"))

xmt42 :: Metaterm
xmt42 = MTermR u0 (MTermT (read "f1[1](x0)"))

xmt43 :: Metaterm
xmt43 = MTermR u0 (MTermT (read "x1"))

-- x2 is the canonic image of x0 through u0.
xmt44 :: Metaterm
xmt44 = MTermR u1 (MTermT (read "f1[1](x2)"))

xmt45 :: Metaterm
xmt45 = MTermR u1 (MTermR u0 (MTermT (read "x1")))

xc41 :: Constraint
xc41 = Tcstr xmt41 xmt43

xc42 :: Constraint
xc42 = Tcstr xmt42 xmt43

xc43 :: Constraint
xc43 = Tcstr xmt44 xmt45

xcs4 = [xc41,xc42,xc43]

(xrmvs4,(xrinst4,xscs4)) = all_simpl_cstr metavars (idinst,xcs4)

xg4 = build_graph_from_constraints xscs4

xfs4 :: FullSolution
xfs4 = (xrmvs4,[],(xrinst4,[]),xg4)

xres4 = find_best_root_class n_base_vars xfs4


-- Example 5
xmt51 :: Metaterm
xmt51 = MTermR u0 (MTermT (read "f1[1](X0)"))

xmt52 :: Metaterm
xmt52 = MTermR u0 (MTermT (read "f1[1](x0)"))

xmt53 :: Metaterm
xmt53 = MTermR u0 (MTermT (read "x1"))

xmt54 :: Metaterm
xmt54 = MTermR u1 (MTermT (read "f1[1](x0)"))

xmt55 :: Metaterm
xmt55 = MTermR u1 (MTermR u0 (MTermT (read "x1")))

xc51 :: Constraint
xc51 = Tcstr xmt51 xmt53

xc52 :: Constraint
xc52 = Tcstr xmt52 xmt53

xc53 :: Constraint
xc53 = Tcstr xmt54 xmt55

xcs5 = [xc51,xc52,xc53]

(xrmvs5,(xrinst5,xscs5)) = all_simpl_cstr metavars (idinst,xcs5)

xg5 = build_graph_from_constraints xscs5

xfs5 :: FullSolution
xfs5 = (xrmvs5,[],(xrinst5,[]),xg5)

xres5 = find_best_root_class n_base_vars xfs5


-- Example 6
xmt61 :: Metaterm
xmt61 = MTermR u0 (MTermT (read "f1[1](x0)"))

xmt62 :: Metaterm
xmt62 = MTermR u0 (MTermT (read "X0"))

xc61 :: Constraint
xc61 = Tcstr xmt62 xmt61

xcs6 = [xc61]

(xrmvs6,(xrinst6,xscs6)) = all_simpl_cstr metavars (idinst,xcs6)

xg6 = build_graph_from_constraints xscs6

xfs6 :: FullSolution
xfs6 = (xrmvs6,[],(xrinst6,[]),xg6)

xres6 = find_best_root_class n_base_vars xfs6


-- Example 7
xmt71 :: Metaterm
xmt71 = MTermR u0 (MTermT (read "f1[1](x0)"))

xmt72 :: Metaterm
xmt72 = MTermR u0 (MTermT (read "X0"))

-- x2 is the canonic image through u0 of x0.
xmt73 :: Metaterm
xmt73 = MTermR u1 (MTermT (read "f1[1](x2)"))

xmt74 :: Metaterm
xmt74 = MTermR u1 (MTermT (read "X0"))

xc71 :: Constraint
xc71 = Tcstr xmt72 xmt71

xc72 :: Constraint
xc72 = Tcstr xmt73 xmt74

xcs7 = [xc71,xc72]

(xrmvs7,(xrinst7,xscs7)) = all_simpl_cstr metavars (idinst,xcs7)

xg7 = build_graph_from_constraints xscs7

xfs7 :: FullSolution
xfs7 = (xrmvs7,[],(xrinst7,[]),xg7)

xres7 = find_best_root_class n_base_vars xfs7


-- Example 8 (like 7, but with literals)
xml81 :: Metaliteral
xml81 = MLitR u0 (MLitL (read "p1[1](f1[1](x0))"))

xml82 :: Metaliteral
xml82 = MLitR u0 (MLitL (read "X1"))

-- x2 is the canonic image through u0 of x0.
xml83 :: Metaliteral
xml83 = MLitR u1 (MLitL (read "p1[1](f1[1](x2))"))

xml84 :: Metaliteral
xml84 = MLitR u1 (MLitL (read "X1"))

xc81 :: Constraint
xc81 = Lcstr xml82 xml81

xc82 :: Constraint
xc82 = Lcstr xml83 xml84

xcs8 = [xc81,xc82]

(xrmvs8,(xrinst8,xscs8)) = all_simpl_cstr metavars (idinst,xcs8)

xg8 = build_graph_from_constraints xscs8

xfs8 :: FullSolution
xfs8 = (xrmvs8,[],(xrinst8,[]),xg8)

xres8 = find_best_root_class n_base_vars xfs8



-- Example 9
xmt91 :: Metaterm
xmt91 = MTermR u0 (MTermT (read "f1[1](x0)"))

xmt92 :: Metaterm
xmt92 = MTermR u0 (MTermT (read "X0"))

xmt93 :: Metaterm
xmt93 = MTermR u1 (MTermT (read "f1[1](x0)"))

xmt94 :: Metaterm
xmt94 = MTermR u1 (MTermT (read "X0"))

xc91 :: Constraint
xc91 = Tcstr xmt92 xmt91

xc92 :: Constraint
xc92 = Tcstr xmt93 xmt94

xcs9 = [xc91,xc92]

(xrmvs9,(xrinst9,xscs9)) = all_simpl_cstr metavars (idinst,xcs9)

xg9 = build_graph_from_constraints xscs9

xfs9 :: FullSolution
xfs9 = (xrmvs9,[],(xrinst9,[]),xg9)

xres9 = find_best_root_class n_base_vars xfs9



-- Example 10

xmt101 :: Metaterm
xmt101 = MTermR u0 (MTermT (read "f1[1](x0)"))

xmt102 :: Metaterm
xmt102 = MTermR u0 (MTermT (read "X0"))

-- x2 is the canonic image through u0 of x0.
xmt103 :: Metaterm
xmt103 = MTermR u1 (MTermT (read "f1[1](x2)"))

xmt104 :: Metaterm
xmt104 = MTermR u1 (MTermT (read "X1"))

xc101 :: Constraint
xc101 = Tcstr xmt102 xmt101

xc102 :: Constraint
xc102 = Tcstr xmt103 xmt104

xcs10 = [xc101,xc102]

(xrmvs10,(xrinst10,xscs10)) = all_simpl_cstr metavars (idinst,xcs10)

xg10 = build_graph_from_constraints xscs10

-- Equation indicating that X1 = u X0
xeq101 :: MetavariableEquation
xeq101 = MetaEq mx1 u0 mx0

xeqs10 = [xeq101]

xfs10 :: FullSolution
xfs10 = (xrmvs10,xeqs10,(xrinst10,[]),xg10)

xres10 = find_best_root_class n_base_vars xfs10



-- Enumeration tests
nums = [2,3,7,11]
multiples = (\x -> Enum x (\idx -> \prev -> Just (x+prev)))
multiples_h = (\x -> (no_help (multiples x)))
multiples_l_h = (\y -> apply_enum_1_h (\x -> [x]) (multiples_h y))
diagtest = (\x -> case x of {[y] -> Left (\z -> (multiples_l_h y)); (y:ys) -> Right (ys,((\w -> multiples_l_h y),Comb (\z -> \zs -> z++zs) (\zss -> case zss of {(z:zs) -> ([z],zs)})))})
diagtestfun = recursively_diagonalize_h diagtest
diagtestenum = diagtestfun nums

sig :: Signature
--sig = ([read "p1[0]",read "p2[1]",read "p3[2]"],[read "f1[0]",read "f2[1]",read "f3[2]"],2)
sig = ([read "p1[0]",read "p2[1]",read "p3[2]"],[read "f1[0]",read "f2[1]",read "f3[2]"],2)
--zeroterms :: Enumeration (_,Term)
--zeroterms = enumerate_zero_terms_dependent sig (Dom (U 2)) [read "x5"]

--withfun :: Enumeration (_,Term)
--withfun = enumerate_terms_function zeroterms (read "f3[2]")

-- Multiple recursion scheme
-- data MultipleRecursionScheme t r p = MRecSch (t -> Either r ([t],p)) (p -> [r] -> r)
-- Test function: Recursive fibonacci, with a twist (so that there are partial results): f(x) = (f(x-1)+f(x-2) + x)
rec_fib :: Int -> Int
rec_fib 1 = 1
rec_fib 2 = 1
rec_fib x = (rec_fib (x-1)) + (rec_fib (x-2)) + x

-- Now with recursion scheme
rec_fib_sch :: MultipleRecursionScheme Int Int Int
rec_fib_sch = MRecSch (\x -> case x of {1 -> Left 1; 2 -> Left 1; x -> Right ([x-1,x-2],x)}) (\p -> \r -> case r of {(a:b:[]) -> a+b+p})
rec_fib_2 = apply_multiple_recursion_scheme rec_fib_sch

rec_fib_2_desc = convert_multiple_rec_scheme rec_fib_sch
rec_fib_2_desc_step = case rec_fib_2_desc of RecSch x _ -> x
rec_fib_2_desc_comb = case rec_fib_2_desc of RecSch _ x -> x





-- Simplifying unifier equations
ueq1 :: UnifierEquation
ueq1 = TUEq (MTermR u0 (MTermT (TVar x0))) (TVar x1)

ueq1simp = simplify_unif_eq ueq1

ueq2 :: UnifierEquation
ueq2 = TUEq (MTermF (read "f1[0]") []) (TFun (read "f1[0]") [])

ueq2simp = simplify_unif_eq ueq2

ueq3 :: UnifierEquation
ueq3 = TUEq (MTermF (read "f1[0]") []) (TFun (read "f2[0]") [])

ueq3simp = simplify_unif_eq ueq3

ueq4 :: UnifierEquation
ueq4 = TUEq (MTermF (read "f1[1]") [MTermR u0 (MTermT (TVar x0))]) (TFun (read "f1[1]") [TVar x1])

ueq4simp = simplify_unif_eq ueq4

ueq5 :: UnifierEquation
ueq5 = TUEq (MTermR u0 (MTermT (read "f1[1](x0)"))) (TFun (read "f1[1]") [TVar x1])

ueq5simp = simplify_unif_eq (simpl_side_unif_eq ueq5)

ueq6 :: UnifierEquation
ueq6 = TUEq (MTermR u0 (MTermR u1 (MTermT (read "f1[1](x0)")))) (TFun (read "f1[1]") [TVar x1])

ueq6simp = simplify_unif_eq (simpl_side_unif_eq ueq6)

ueq7 :: UnifierEquation
ueq7 = TUEq (MTermR u0 (MTermT (read "X0"))) (TVar x1)

ueq7simp = simplify_unif_eq (simpl_side_unif_eq ueq7)

ueq8 :: UnifierEquation
ueq8 = TUEq (MTermR u0 (MTermT (read "f1[2](x0,X0)"))) (read "f1[2](x1,x2)")

ueq8simp = simplify_unif_eq (simpl_side_unif_eq ueq8)


-- Backwards propagation testing

bw_n_base_vars :: Int
bw_n_base_vars = 5

-- Variables
--x0 :: Variable
--x0 = Var 0

--x1 :: Variable
--x1 = Var 1

x2 :: Variable
x2 = Var 2

x3 :: Variable
x3 = Var 3

x4 :: Variable
x4 = Var 4

-- Metavariables
--mx0 :: Metavariable
--mx0 = Metavar 0

--mx1 :: Metavariable
--mx1 = Metavar 1

bwmetavars = [mx0,mx1]

-- Unifiers
--u0 :: Unifier
--u0 = U 0

--u1 :: Unifier
--u1 = U 1

-- Derived variables
bwx0u0 :: Variable
bwx0u0 = get_image_var bw_n_base_vars u0 x0

bwx1u0 :: Variable
bwx1u0 = get_image_var bw_n_base_vars u0 x1

bwx2u0 :: Variable
bwx2u0 = get_image_var bw_n_base_vars u0 x2

bwx3u0 :: Variable
bwx3u0 = get_image_var bw_n_base_vars u0 x3

bwx0u1 :: Variable
bwx0u1 = get_image_var bw_n_base_vars u1 x0


-- Example 1
bwxmt11 :: Metaterm
bwxmt11 = MTermR u0 (MTermT (read "f1[1](x0)"))

bwxmt12 :: Metaterm
bwxmt12 = MTermR u0 (MTermT (read "x1"))

bwxmt13 :: Metaterm
bwxmt13 = MTermR u0 (MTermT (read "f1[1](x2)"))

bwxc11 :: Constraint
bwxc11 = Tcstr bwxmt12 bwxmt11

bwxc12 :: Constraint
bwxc12 = Tcstr bwxmt12 bwxmt13

bwxcs1 = [bwxc11,bwxc12]

(bwxrmvs1,(bwxrinst1,bwxscs1)) = all_simpl_cstr bwmetavars (idinst,bwxcs1)

bwxg1 = build_graph_from_constraints bwxscs1

bwxfs1 :: FullSolution
bwxfs1 = (bwxrmvs1,[],(bwxrinst1,[]),bwxg1)

bwxdep1 :: Dependent
bwxdep1 = (DRec u0 (DVar x0))

bwxt1 :: Term
bwxt1 = TVar bwx0u0

bwpair1 :: (Dependent,Either Term Literal)
bwpair1 = (bwxdep1,Left bwxt1)

bwxres1 = update_graph_all (set_solution bwxfs1 bwpair1) [bwpair1] []

-- Example 2
bwxmt21 :: Metaterm
bwxmt21 = MTermR u0 (MTermT (read "f1[1](x0)"))

bwxmt22 :: Metaterm
bwxmt22 = MTermR u0 (MTermT (read "x1"))

bwxmt23 :: Metaterm
bwxmt23 = MTermR u0 (MTermT (read "f2[1](x2)"))

bwxc21 :: Constraint
bwxc21 = Tcstr bwxmt22 bwxmt21

bwxc22 :: Constraint
bwxc22 = Tcstr bwxmt22 bwxmt23

bwxcs2 = [bwxc21,bwxc22]

(bwxrmvs2,(bwxrinst2,bwxscs2)) = all_simpl_cstr bwmetavars (idinst,bwxcs2)

bwxg2 = build_graph_from_constraints bwxscs2

bwxfs2 :: FullSolution
bwxfs2 = (bwxrmvs2,[],(bwxrinst2,[]),bwxg2)

bwxdep2 :: Dependent
bwxdep2 = (DRec u0 (DVar x0))

bwxt2 :: Term
bwxt2 = TVar bwx0u0

bwpair2 :: (Dependent,Either Term Literal)
bwpair2 = (bwxdep2,Left bwxt2)

bwxres2 = update_graph_all (set_solution bwxfs2 bwpair2) [bwpair2] []

-- Example 3
bwxmt31 :: Metaterm
bwxmt31 = MTermR u0 (MTermT (read "f1[1](x0)"))

bwxmt32 :: Metaterm
bwxmt32 = MTermR u0 (MTermT (read "x1"))

bwxmt33 :: Metaterm
bwxmt33 = MTermR u0 (MTermT (read "f1[1](f2[1](x2))"))

bwxc31 :: Constraint
bwxc31 = Tcstr bwxmt32 bwxmt31

bwxc32 :: Constraint
bwxc32 = Tcstr bwxmt32 bwxmt33

bwxcs3 = [bwxc31,bwxc32]

(bwxrmvs3,(bwxrinst3,bwxscs3)) = all_simpl_cstr bwmetavars (idinst,bwxcs3)

bwxg3 = build_graph_from_constraints bwxscs3

bwxfs3 :: FullSolution
bwxfs3 = (bwxrmvs3,[],(bwxrinst3,[]),bwxg3)

bwxdep3 :: Dependent
bwxdep3 = (DRec u0 (DVar x0))

bwxt3 :: Term
bwxt3 = TVar bwx0u0

bwpair3 :: (Dependent,Either Term Literal)
bwpair3 = (bwxdep3,Left bwxt3)

bwxres3 = update_graph_all (set_solution bwxfs3 bwpair3) [bwpair3] []

-- Example 4
bwxmt41 :: Metaterm
bwxmt41 = MTermR u0 (MTermT (read "f1[1](x0)"))

bwxmt42 :: Metaterm
bwxmt42 = MTermR u0 (MTermT (read "x1"))

bwxmt43 :: Metaterm
bwxmt43 = MTermR u0 (MTermT (read "f1[1](f2[1](x2))"))

bwxc41 :: Constraint
bwxc41 = Tcstr bwxmt42 bwxmt41

bwxc42 :: Constraint
bwxc42 = Tcstr bwxmt42 bwxmt43

bwxcs4 = [bwxc41,bwxc42]

(bwxrmvs4,(bwxrinst4,bwxscs4)) = all_simpl_cstr bwmetavars (idinst,bwxcs4)

bwxg4 = build_graph_from_constraints bwxscs4

bwxfs4 :: FullSolution
bwxfs4 = (bwxrmvs4,[],(bwxrinst4,[]),bwxg4)

bwxdep4 :: Dependent
bwxdep4 = (DRec u0 (DVar x0))

bwxt4 :: Term
bwxt4 = (TFun (read "f2[1]") [TVar bwx0u0])

bwpair4 :: (Dependent,Either Term Literal)
bwpair4 = (bwxdep4,Left bwxt4)

bwxres4 = update_graph_all (set_solution bwxfs4 bwpair4) [bwpair4] []

-- Example 5
bwxmt51 :: Metaterm
bwxmt51 = MTermR u0 (MTermT (read "f1[1](f2[1](x0))"))

bwxmt52 :: Metaterm
bwxmt52 = MTermR u0 (MTermT (read "x1"))

bwxmt53 :: Metaterm
bwxmt53 = MTermR u0 (MTermT (read "f1[1](x2)"))

bwxc51 :: Constraint
bwxc51 = Tcstr bwxmt52 bwxmt51

bwxc52 :: Constraint
bwxc52 = Tcstr bwxmt52 bwxmt53

bwxcs5 = [bwxc51,bwxc52]

(bwxrmvs5,(bwxrinst5,bwxscs5)) = all_simpl_cstr bwmetavars (idinst,bwxcs5)

bwxg5 = build_graph_from_constraints bwxscs5

bwxfs5 :: FullSolution
bwxfs5 = (bwxrmvs5,[],(bwxrinst5,[]),bwxg5)

bwxdep5 :: Dependent
bwxdep5 = (DRec u0 (DVar x0))

bwxt5 :: Term
bwxt5 = TVar bwx0u0

bwpair5 :: (Dependent,Either Term Literal)
bwpair5 = (bwxdep5,Left bwxt5)

bwxres5 = update_graph_all (set_solution bwxfs5 bwpair5) [bwpair5] []

-- Example 6
bwxmt61 :: Metaterm
bwxmt61 = MTermR u0 (MTermT (read "f1[1](x0)"))

bwxmt62 :: Metaterm
bwxmt62 = MTermR u0 (MTermT (read "x1"))

bwxmt63 :: Metaterm
bwxmt63 = MTermR u0 (MTermT (read "f1[1](f2[1](X0))"))

bwxc61 :: Constraint
bwxc61 = Tcstr bwxmt62 bwxmt61

bwxc62 :: Constraint
bwxc62 = Tcstr bwxmt62 bwxmt63

bwxcs6 = [bwxc61,bwxc62]

(bwxrmvs6,(bwxrinst6,bwxscs6)) = all_simpl_cstr bwmetavars (idinst,bwxcs6)

bwxg6 = build_graph_from_constraints bwxscs6

bwxfs6 :: FullSolution
bwxfs6 = (bwxrmvs6,[],(bwxrinst6,[]),bwxg6)

bwxdep6 :: Dependent
bwxdep6 = (DRec u0 (DVar x0))

bwxt6 :: Term
bwxt6 = TVar bwx0u0

bwpair6 :: (Dependent,Either Term Literal)
bwpair6 = (bwxdep6,Left bwxt6)

bwxres6 = update_graph_all (set_solution bwxfs6 bwpair6) [bwpair6] []

-- Example 7
bwxmt71 :: Metaterm
bwxmt71 = MTermR u0 (MTermT (read "f1[1](f2[1](x0))"))

bwxmt72 :: Metaterm
bwxmt72 = MTermR u0 (MTermT (read "x1"))

bwxmt73 :: Metaterm
bwxmt73 = MTermR u0 (MTermT (read "f1[1](X0)"))

bwxc71 :: Constraint
bwxc71 = Tcstr bwxmt72 bwxmt71

bwxc72 :: Constraint
bwxc72 = Tcstr bwxmt72 bwxmt73

bwxcs7 = [bwxc71,bwxc72]

(bwxrmvs7,(bwxrinst7,bwxscs7)) = all_simpl_cstr bwmetavars (idinst,bwxcs7)

bwxg7 = build_graph_from_constraints bwxscs7

bwxfs7 :: FullSolution
bwxfs7 = (bwxrmvs7,[],(bwxrinst7,[]),bwxg7)

bwxdep7 :: Dependent
bwxdep7 = (DRec u0 (DVar x0))

bwxt7 :: Term
bwxt7 = TVar bwx0u0

bwpair7 :: (Dependent,Either Term Literal)
bwpair7 = (bwxdep7,Left bwxt7)

bwxres7 = update_graph_all (set_solution bwxfs7 bwpair7) [bwpair7] []

-- Example 8
bwxmt81 :: Metaterm
bwxmt81 = MTermR u0 (MTermT (read "f1[1](x0)"))

bwxmt82 :: Metaterm
bwxmt82 = MTermR u0 (MTermT (read "x1"))

bwxmt83 :: Metaterm
bwxmt83 = MTermR u0 (MTermT (read "f1[1](x2)"))

bwxc81 :: Constraint
bwxc81 = Tcstr bwxmt82 bwxmt81

bwxc82 :: Constraint
bwxc82 = Tcstr bwxmt82 bwxmt83

bwxcs8 = [bwxc81,bwxc82]

(bwxrmvs8,(bwxrinst8,bwxscs8)) = all_simpl_cstr bwmetavars (idinst,bwxcs8)

bwxg8 = build_graph_from_constraints bwxscs8

bwxfs8 :: FullSolution
bwxfs8 = (bwxrmvs8,[],(bwxrinst8,[]),bwxg8)

bwxdep8 :: Dependent
bwxdep8 = (DRec u0 (DVar x0))

bwxt8 :: Term
bwxt8 = (TFun (read "f2[1]") [TVar bwx0u0])

bwpair8 :: (Dependent,Either Term Literal)
bwpair8 = (bwxdep8,Left bwxt8)

bwxres8 = update_graph_all (set_solution bwxfs8 bwpair8) [bwpair8] []

-- Example 9
bwxmt91 :: Metaterm
bwxmt91 = MTermR u1 (MTermT (read "f1[1](x0)"))

bwxmt92 :: Metaterm
bwxmt92 = MTermR u1 (MTermT (read "x1"))

bwxmt93 :: Metaterm
bwxmt93 = MTermR u1 (MTermR u0 (MTermT (read "f1[1](f2[1](x2))")))

bwxc91 :: Constraint
bwxc91 = Tcstr bwxmt92 bwxmt91

bwxc92 :: Constraint
bwxc92 = Tcstr bwxmt92 bwxmt93

bwxcs9 = [bwxc91,bwxc92]

(bwxrmvs9,(bwxrinst9,bwxscs9)) = all_simpl_cstr bwmetavars (idinst,bwxcs9)

bwxg9 = build_graph_from_constraints bwxscs9

bwxfs9 :: FullSolution
bwxfs9 = (bwxrmvs9,[],(bwxrinst9,[]),bwxg9)

bwxdep9 :: Dependent
bwxdep9 = (DRec u1 (DVar x0))

bwxt9 :: Term
bwxt9 = TVar bwx0u0

bwpair9 :: (Dependent,Either Term Literal)
bwpair9 = (bwxdep9,Left bwxt9)

bwxres9 = update_graph_all (set_solution bwxfs9 bwpair9) [bwpair9] []

-- Example 10
bwxmt101 :: Metaterm
bwxmt101 = MTermR u1 (MTermT (read "f1[1](f2[1](x0))"))

bwxmt102 :: Metaterm
bwxmt102 = MTermR u1 (MTermT (read "x1"))

bwxmt103 :: Metaterm
bwxmt103 = MTermR u1 (MTermR u0 (MTermT (read "f1[1](x2)")))

bwxc101 :: Constraint
bwxc101 = Tcstr bwxmt102 bwxmt101

bwxc102 :: Constraint
bwxc102 = Tcstr bwxmt102 bwxmt103

bwxcs10 = [bwxc101,bwxc102]

(bwxrmvs10,(bwxrinst10,bwxscs10)) = all_simpl_cstr bwmetavars (idinst,bwxcs10)

bwxg10 = build_graph_from_constraints bwxscs10

bwxfs10 :: FullSolution
bwxfs10 = (bwxrmvs10,[],(bwxrinst10,[]),bwxg10)

bwxdep10 :: Dependent
bwxdep10 = (DRec u1 (DVar x0))

bwxt10 :: Term
bwxt10 = TVar bwx0u1

bwpair10 :: (Dependent,Either Term Literal)
bwpair10 = (bwxdep10,Left bwxt10)

bwxres10 = update_graph_all (set_solution bwxfs10 bwpair10) [bwpair10] []

-- Example 11
bwxmt111 :: Metaterm
bwxmt111 = MTermR u1 (MTermT (read "f1[1](x0)"))

bwxmt112 :: Metaterm
bwxmt112 = MTermR u1 (MTermT (read "x1"))

bwxmt113 :: Metaterm
bwxmt113 = MTermR u1 (MTermR u0 (MTermT (read "f1[1](x2)")))

bwxc111 :: Constraint
bwxc111 = Tcstr bwxmt112 bwxmt111

bwxc112 :: Constraint
bwxc112 = Tcstr bwxmt112 bwxmt113

bwxcs11 = [bwxc111,bwxc112]

(bwxrmvs11,(bwxrinst11,bwxscs11)) = all_simpl_cstr bwmetavars (idinst,bwxcs11)

bwxg11 = build_graph_from_constraints bwxscs11

bwxfs11 :: FullSolution
bwxfs11 = (bwxrmvs11,[],(bwxrinst11,[]),bwxg11)

bwxdep11 :: Dependent
bwxdep11 = (DRec u1 (DVar x0))

bwxt11 :: Term
bwxt11 = TVar bwx0u1

bwpair11 :: (Dependent,Either Term Literal)
bwpair11 = (bwxdep11,Left bwxt11)

bwxres11 = update_graph_all (set_solution bwxfs11 bwpair11) [bwpair11] []

-- Example 12
bwxmt121 :: Metaterm
bwxmt121 = MTermR u0 (MTermT (read "f1[2](x0,x3)"))

bwxmt122 :: Metaterm
bwxmt122 = MTermR u0 (MTermT (read "x1"))

bwxmt123 :: Metaterm
bwxmt123 = MTermR u0 (MTermT (read "f1[2](x2,x4)"))

bwxc121 :: Constraint
bwxc121 = Tcstr bwxmt122 bwxmt121

bwxc122 :: Constraint
bwxc122 = Tcstr bwxmt122 bwxmt123

bwxcs12 = [bwxc121,bwxc122]

(bwxrmvs12,(bwxrinst12,bwxscs12)) = all_simpl_cstr bwmetavars (idinst,bwxcs12)

bwxg12 = build_graph_from_constraints bwxscs12

bwxfs12 :: FullSolution
bwxfs12 = (bwxrmvs12,[],(bwxrinst12,[]),bwxg12)

bwxdep121 :: Dependent
bwxdep121 = (DRec u0 (DVar x0))

bwxt121 :: Term
bwxt121 = TVar bwx0u0

bwxdep122 :: Dependent
bwxdep122 = (DRec u0 (DVar x3))

bwxt122 :: Term
bwxt122 = TFun (read "f2[1]") [TVar bwx0u0]

bwpair121 :: (Dependent,Either Term Literal)
bwpair121 = (bwxdep121,Left bwxt121)

bwpair122 :: (Dependent,Either Term Literal)
bwpair122 = (bwxdep122,Left bwxt122)

bwxres12 = update_graph_all (set_all_solutions bwxfs12 [bwpair121,bwpair122]) [bwpair121,bwpair122] []

-- Example 13
bwxmt131 :: Metaterm
bwxmt131 = MTermR u1 (MTermT (read "f1[2](x0,x3)"))

bwxmt132 :: Metaterm
bwxmt132 = MTermR u1 (MTermT (read "x1"))

bwxmt133 :: Metaterm
bwxmt133 = MTermF (read "f1[2]") [MTermR u1 (MTermR u0 (MTermT (read "x2"))),MTermR u1 (MTermT (read "X0"))]

bwxc131 :: Constraint
bwxc131 = Tcstr bwxmt132 bwxmt131

bwxc132 :: Constraint
bwxc132 = Tcstr bwxmt132 bwxmt133

bwxcs13 = [bwxc131,bwxc132]

(bwxrmvs13,(bwxrinst13,bwxscs13)) = all_simpl_cstr bwmetavars (idinst,bwxcs13)

bwxg13 = build_graph_from_constraints bwxscs13

bwxfs13 :: FullSolution
bwxfs13 = (bwxrmvs13,[],(bwxrinst13,[]),bwxg13)

bwxdep131 :: Dependent
bwxdep131 = (DRec u1 (DVar x0))

bwxt131 :: Term
bwxt131 = TVar bwx0u1

bwxdep132 :: Dependent
bwxdep132 = (DRec u1 (DVar x3))

bwxt132 :: Term
bwxt132 = TFun (read "f2[1]") [TVar bwx0u1]

bwpair131 :: (Dependent,Either Term Literal)
bwpair131 = (bwxdep131,Left bwxt131)

bwpair132 :: (Dependent,Either Term Literal)
bwpair132 = (bwxdep132,Left bwxt132)

bwxres13 = update_graph_all (set_all_solutions bwxfs13 [bwpair131,bwpair132]) [bwpair131,bwpair132] []

-- Example 14
bwxmt141 :: Metaterm
bwxmt141 = MTermR u0 (MTermT (read "f1[2](x0,x3)"))

bwxmt142 :: Metaterm
bwxmt142 = MTermR u0 (MTermT (read "x1"))

bwxmt143 :: Metaterm
bwxmt143 = MTermR u0 (MTermT (read "f1[2](x2,x4)"))

bwxc141 :: Constraint
bwxc141 = Tcstr bwxmt142 bwxmt141

bwxc142 :: Constraint
bwxc142 = Tcstr bwxmt142 bwxmt143

bwxcs14 = [bwxc141,bwxc142]

(bwxrmvs14,(bwxrinst14,bwxscs14)) = all_simpl_cstr bwmetavars (idinst,bwxcs14)

bwxg14 = build_graph_from_constraints bwxscs14

bwxfs14 :: FullSolution
bwxfs14 = (bwxrmvs14,[],(bwxrinst14,[]),bwxg14)

bwxdep141 :: Dependent
bwxdep141 = (DRec u0 (DVar x0))

bwxt141 :: Term
bwxt141 = TVar bwx0u0

bwxdep142 :: Dependent
bwxdep142 = (DRec u0 (DVar x3))

bwxt142 :: Term
bwxt142 = TFun (read "f2[1]") [TVar bwx0u0]

bwxdep143 :: Dependent
bwxdep143 = (DRec u0 (DVar x2))

bwxt143 :: Term
bwxt143 = TVar bwx0u0

bwpair141 :: (Dependent,Either Term Literal)
bwpair141 = (bwxdep141,Left bwxt141)

bwpair142 :: (Dependent,Either Term Literal)
bwpair142 = (bwxdep142,Left bwxt142)

bwpair143 :: (Dependent,Either Term Literal)
bwpair143 = (bwxdep143,Left bwxt143)

bwxres14 = update_graph_all (set_all_solutions bwxfs14 [bwpair143,bwpair142,bwpair141]) [bwpair143,bwpair142,bwpair141] []

-- Example 15
bwxmt151 :: Metaterm
bwxmt151 = MTermR u0 (MTermT (read "f1[2](x0,x3)"))

bwxmt152 :: Metaterm
bwxmt152 = MTermR u0 (MTermT (read "x1"))

bwxmt153 :: Metaterm
bwxmt153 = MTermR u0 (MTermT (read "f1[2](x2,x4)"))

bwxc151 :: Constraint
bwxc151 = Tcstr bwxmt152 bwxmt151

bwxc152 :: Constraint
bwxc152 = Tcstr bwxmt152 bwxmt153

bwxcs15 = [bwxc151,bwxc152]

(bwxrmvs15,(bwxrinst15,bwxscs15)) = all_simpl_cstr bwmetavars (idinst,bwxcs15)

bwxg15 = build_graph_from_constraints bwxscs15

bwxfs15 :: FullSolution
bwxfs15 = (bwxrmvs15,[],(bwxrinst15,[]),bwxg15)

bwxdep151 :: Dependent
bwxdep151 = (DRec u0 (DVar x0))

bwxt151 :: Term
bwxt151 = TVar bwx0u0

bwxdep152 :: Dependent
bwxdep152 = (DRec u0 (DVar x3))

bwxt152 :: Term
bwxt152 = TFun (read "f2[1]") [TVar bwx0u0]

bwxdep153 :: Dependent
bwxdep153 = (DRec u0 (DVar x2))

bwxt153 :: Term
bwxt153 = TFun (read "f2[1]") [TVar bwx0u0]

bwpair151 :: (Dependent,Either Term Literal)
bwpair151 = (bwxdep151,Left bwxt151)

bwpair152 :: (Dependent,Either Term Literal)
bwpair152 = (bwxdep152,Left bwxt152)

bwpair153 :: (Dependent,Either Term Literal)
bwpair153 = (bwxdep153,Left bwxt153)

bwxres15 = update_graph_all (set_all_solutions bwxfs15 [bwpair153,bwpair152,bwpair151]) [bwpair153,bwpair152,bwpair151] []



-- Testing graph factorization
fac_n_base_vars :: Int
fac_n_base_vars = 5

-- Variables
--x0 :: Variable
--x0 = Var 0

--x1 :: Variable
--x1 = Var 1

--x2 :: Variable
--x2 = Var 2

--x3 :: Variable
--x3 = Var 3

--x4 :: Variable
--x4 = Var 4

-- Metavariables
facmetavars = []

-- Unifiers
--u0 :: Unifier
--u0 = U 0

-- Derived variables
facx0u0 :: Variable
facx0u0 = get_image_var bw_n_base_vars u0 x0

facx1u0 :: Variable
facx1u0 = get_image_var bw_n_base_vars u0 x1

-- Example 1
facmt1_1 :: Metaterm
facmt1_1 = MTermR u0 (MTermT (read "f1[1](x1)"))

facmt1_2 :: Metaterm
facmt1_2 = MTermR u0 (MTermT (read "x0"))

facc1_1 :: Constraint
facc1_1 = Tcstr facmt1_1 facmt1_2

faccs1 = [facc1_1]

(facrmvs1,(facrinst1,facscs1)) = all_simpl_cstr facmetavars (idinst,faccs1)

facg1 = build_graph_from_constraints facscs1

facfs1 :: FullSolution
facfs1 = (facrmvs1,[],(facrinst1,[]),facg1)

facleaf1 :: Dependent
facleaf1 = DRec u0 (DVar x0)

(facres1,facvals1) = factorize_dgraph facfs1 facleaf1

-- Example 2
facmt2_1 :: Metaterm
facmt2_1 = MTermR u0 (MTermT (read "f1[1](f2[1](x1))"))

facmt2_2 :: Metaterm
facmt2_2 = MTermR u0 (MTermT (read "x0"))

facc2_1 :: Constraint
facc2_1 = Tcstr facmt2_1 facmt2_2

faccs2 = [facc2_1]

(facrmvs2,(facrinst2,facscs2)) = all_simpl_cstr facmetavars (idinst,faccs2)

facg2 = build_graph_from_constraints facscs2

facfs2 :: FullSolution
facfs2 = (facrmvs2,[],(facrinst2,[]),facg2)

facleaf2 :: Dependent
facleaf2 = DRec u0 (DVar x0)

(facres2,facvals2) = factorize_dgraph facfs2 facleaf2

-- Example 3
facmt3_1 :: Metaterm
facmt3_1 = MTermR u0 (MTermT (read "f1[2](x1,x2)"))

facmt3_2 :: Metaterm
facmt3_2 = MTermR u0 (MTermT (read "x0"))

facc3_1 :: Constraint
facc3_1 = Tcstr facmt3_1 facmt3_2

faccs3 = [facc3_1]

(facrmvs3,(facrinst3,facscs3)) = all_simpl_cstr facmetavars (idinst,faccs3)

facg3 = build_graph_from_constraints facscs3

facfs3 :: FullSolution
facfs3 = (facrmvs3,[],(facrinst3,[]),facg3)

facleaf3 :: Dependent
facleaf3 = DRec u0 (DVar x0)

(facres3,facvals3) = factorize_dgraph facfs3 facleaf3

-- Example 4
facmt4_1 :: Metaterm
facmt4_1 = MTermR u0 (MTermT (read "f1[2](x1,f2[1](x2))"))

facmt4_2 :: Metaterm
facmt4_2 = MTermR u0 (MTermT (read "x0"))

facc4_1 :: Constraint
facc4_1 = Tcstr facmt4_1 facmt4_2

faccs4 = [facc4_1]

(facrmvs4,(facrinst4,facscs4)) = all_simpl_cstr facmetavars (idinst,faccs4)

facg4 = build_graph_from_constraints facscs4

facfs4 :: FullSolution
facfs4 = (facrmvs4,[],(facrinst4,[]),facg4)

facleaf4 :: Dependent
facleaf4 = DRec u0 (DVar x0)

(facres4,facvals4) = factorize_dgraph facfs4 facleaf4

-- Example 5
facmt5_1 :: Metaterm
facmt5_1 = MTermR u0 (MTermT (read "f1[2](x1,x2)"))

facmt5_2 :: Metaterm
facmt5_2 = MTermR u0 (MTermT (read "x0"))

facmt5_3 :: Metaterm
facmt5_3 = MTermR u0 (MTermT (read "f2[1](x3)"))

facmt5_4 :: Metaterm
facmt5_4 = MTermR u0 (MTermT (read "x2"))

facc5_1 :: Constraint
facc5_1 = Tcstr facmt5_1 facmt5_2

facc5_2 :: Constraint
facc5_2 = Tcstr facmt5_3 facmt5_4

faccs5 = [facc5_1,facc5_2]

(facrmvs5,(facrinst5,facscs5)) = all_simpl_cstr facmetavars (idinst,faccs5)

facg5 = build_graph_from_constraints facscs5

facfs5 :: FullSolution
facfs5 = (facrmvs5,[],(facrinst5,[]),facg5)

facleaf5 :: Dependent
facleaf5 = DRec u0 (DVar x0)

(facres5,facvals5) = factorize_dgraph facfs5 facleaf5

-- Example 6
facmt6_1 :: Metaterm
facmt6_1 = MTermR u0 (MTermT (read "f1[1](x1)"))

facmt6_2 :: Metaterm
facmt6_2 = MTermR u0 (MTermT (read "x0"))

facmt6_3 :: Metaterm
facmt6_3 = MTermR u0 (MTermT (read "f1[1](x2)"))

facc6_1 :: Constraint
facc6_1 = Tcstr facmt6_1 facmt6_2

facc6_2 :: Constraint
facc6_2 = Tcstr facmt6_3 facmt6_2

faccs6 = [facc6_1,facc6_2]

(facrmvs6,(facrinst6,facscs6)) = all_simpl_cstr facmetavars (idinst,faccs6)

facg6 = build_graph_from_constraints facscs6

facfs6 :: FullSolution
facfs6 = (facrmvs6,[],(facrinst6,[]),facg6)

facleaf6 :: Dependent
facleaf6 = DRec u0 (DVar x0)

(facres6,facvals6) = factorize_dgraph facfs6 facleaf6

-- Example 7
facmt7_1 :: Metaterm
facmt7_1 = MTermR u0 (MTermT (read "f1[1](x1)"))

facmt7_2 :: Metaterm
facmt7_2 = MTermR u0 (MTermT (read "x0"))

facmt7_3 :: Metaterm
facmt7_3 = MTermR u0 (MTermT (read "f1[1](f2[1](x2))"))

facc7_1 :: Constraint
facc7_1 = Tcstr facmt7_1 facmt7_2

facc7_2 :: Constraint
facc7_2 = Tcstr facmt7_3 facmt7_2

faccs7 = [facc7_1,facc7_2]

(facrmvs7,(facrinst7,facscs7)) = all_simpl_cstr facmetavars (idinst,faccs7)

facg7 = build_graph_from_constraints facscs7

facfs7 :: FullSolution
facfs7 = (facrmvs7,[],(facrinst7,[]),facg7)

facleaf7 :: Dependent
facleaf7 = DRec u0 (DVar x0)

(facres7,facvals7) = factorize_dgraph facfs7 facleaf7

-- Example 8
facmt8_1 :: Metaterm
facmt8_1 = MTermR u0 (MTermT (read "f1[2](x1,x2)"))

facmt8_2 :: Metaterm
facmt8_2 = MTermR u0 (MTermT (read "x0"))

facmt8_3 :: Metaterm
facmt8_3 = MTermR u0 (MTermT (read "f1[2](x2,x3)"))

facc8_1 :: Constraint
facc8_1 = Tcstr facmt8_1 facmt8_2

facc8_2 :: Constraint
facc8_2 = Tcstr facmt8_3 facmt8_2

faccs8 = [facc8_1,facc8_2]

(facrmvs8,(facrinst8,facscs8)) = all_simpl_cstr facmetavars (idinst,faccs8)

facg8 = build_graph_from_constraints facscs8

facfs8 :: FullSolution
facfs8 = (facrmvs8,[],(facrinst8,[]),facg8)

facleaf8 :: Dependent
facleaf8 = DRec u0 (DVar x0)

(facres8,facvals8) = factorize_dgraph facfs8 facleaf8

-- Example 9
facmt9_1 :: Metaterm
facmt9_1 = MTermR u0 (MTermT (read "f1[2](x1,x2)"))

facmt9_2 :: Metaterm
facmt9_2 = MTermR u0 (MTermT (read "x0"))

facmt9_3 :: Metaterm
facmt9_3 = MTermR u0 (MTermT (read "f1[2](x2,x3)"))

facmt9_4 :: Metaterm
facmt9_4 = MTermR u0 (MTermT (read "f1[2](x3,x1)"))

facc9_1 :: Constraint
facc9_1 = Tcstr facmt9_1 facmt9_2

facc9_2 :: Constraint
facc9_2 = Tcstr facmt9_3 facmt9_2

facc9_3 :: Constraint
facc9_3 = Tcstr facmt9_4 facmt9_2

faccs9 = [facc9_1,facc9_2,facc9_3]

(facrmvs9,(facrinst9,facscs9)) = all_simpl_cstr facmetavars (idinst,faccs9)

facg9 = build_graph_from_constraints facscs9

facfs9 :: FullSolution
facfs9 = (facrmvs9,[],(facrinst9,[]),facg9)

facleaf9 :: Dependent
facleaf9 = DRec u0 (DVar x0)

(facres9,facvals9) = factorize_dgraph facfs9 facleaf9

-- Example 10
facmt10_1 :: Metaterm
facmt10_1 = MTermR u0 (MTermT (read "f1[1](x1)"))

facmt10_2 :: Metaterm
facmt10_2 = MTermR u0 (MTermT (read "x0"))

facmt10_3 :: Metaterm
facmt10_3 = MTermR u0 (MTermT (read "f2[1](x2)"))

facc10_1 :: Constraint
facc10_1 = Tcstr facmt10_1 facmt10_2

facc10_2 :: Constraint
facc10_2 = Tcstr facmt10_3 facmt10_2

faccs10 = [facc10_1,facc10_2]

(facrmvs10,(facrinst10,facscs10)) = all_simpl_cstr facmetavars (idinst,faccs10)

facg10 = build_graph_from_constraints facscs10

facfs10 :: FullSolution
facfs10 = (facrmvs10,[],(facrinst10,[]),facg10)

facleaf10 :: Dependent
facleaf10 = DRec u0 (DVar x0)

(facres10,facvals10) = factorize_dgraph facfs10 facleaf10

-- Example 11
facmt11_1 :: Metaterm
facmt11_1 = MTermR u0 (MTermT (read "f1[1](x1)"))

facmt11_2 :: Metaterm
facmt11_2 = MTermR u0 (MTermT (read "x0"))

facmt11_3 :: Metaterm
facmt11_3 = MTermR u0 (MTermT (read "f1[1](x2)"))

facmt11_4 :: Metaterm
facmt11_4 = MTermR u0 (MTermT (read "f2[1](x3)"))

facc11_1 :: Constraint
facc11_1 = Tcstr facmt11_1 facmt11_2

facc11_2 :: Constraint
facc11_2 = Tcstr facmt11_3 facmt11_2

facc11_3 :: Constraint
facc11_3 = Tcstr facmt11_4 facmt11_2

faccs11 = [facc11_1,facc11_2,facc11_3]

(facrmvs11,(facrinst11,facscs11)) = all_simpl_cstr facmetavars (idinst,faccs11)

facg11 = build_graph_from_constraints facscs11

facfs11 :: FullSolution
facfs11 = (facrmvs11,[],(facrinst11,[]),facg11)

facleaf11 :: Dependent
facleaf11 = DRec u0 (DVar x0)

(facres11,facvals11) = factorize_dgraph facfs11 facleaf11

-- Example 12
facmt12_1 :: Metaterm
facmt12_1 = MTermR u0 (MTermT (read "f1[1](x1)"))

facmt12_2 :: Metaterm
facmt12_2 = MTermR u0 (MTermT (read "x0"))

facmt12_3 :: Metaterm
facmt12_3 = MTermR u0 (MTermT (read "f2[1](x2)"))

facmt12_4 :: Metaterm
facmt12_4 = MTermR u0 (MTermT (read "x1"))

facmt12_5 :: Metaterm
facmt12_5 = MTermR u0 (MTermT (read "f1[1](f3[1](x3))"))

facc12_1 :: Constraint
facc12_1 = Tcstr facmt12_1 facmt12_2

facc12_2 :: Constraint
facc12_2 = Tcstr facmt12_3 facmt12_4

facc12_3 :: Constraint
facc12_3 = Tcstr facmt12_5 facmt12_2

faccs12 = [facc12_1,facc12_2,facc12_3]

(facrmvs12,(facrinst12,facscs12)) = all_simpl_cstr facmetavars (idinst,faccs12)

facg12 = build_graph_from_constraints facscs12

facfs12 :: FullSolution
facfs12 = (facrmvs12,[],(facrinst12,[]),facg12)

facleaf12 :: Dependent
facleaf12 = DRec u0 (DVar x0)

(facres12,facvals12) = factorize_dgraph facfs12 facleaf12

-- Example 13
facmt13_1 :: Metaterm
facmt13_1 = MTermR u0 (MTermT (read "f1[2](x1,f2[1](x2))"))

facmt13_2 :: Metaterm
facmt13_2 = MTermR u0 (MTermT (read "x0"))

facmt13_3 :: Metaterm
facmt13_3 = MTermR u0 (MTermT (read "f1[2](x3,f3[1](x4))"))

facc13_1 :: Constraint
facc13_1 = Tcstr facmt13_1 facmt13_2

facc13_2 :: Constraint
facc13_2 = Tcstr facmt13_3 facmt13_2

faccs13 = [facc13_1,facc13_2]

(facrmvs13,(facrinst13,facscs13)) = all_simpl_cstr facmetavars (idinst,faccs13)

facg13 = build_graph_from_constraints facscs13

facfs13 :: FullSolution
facfs13 = (facrmvs13,[],(facrinst13,[]),facg13)

facleaf13 :: Dependent
facleaf13 = DRec u0 (DVar x0)

(facres13,facvals13) = factorize_dgraph facfs13 facleaf13

-- Example 14
facmt14_1 :: Metaterm
facmt14_1 = MTermR u0 (MTermT (read "f1[2](x1,f2[1](x2))"))

facmt14_2 :: Metaterm
facmt14_2 = MTermR u0 (MTermT (read "x0"))

facmt14_3 :: Metaterm
facmt14_3 = MTermR u0 (MTermT (read "f1[2](f3[1](x3),x4)"))

facc14_1 :: Constraint
facc14_1 = Tcstr facmt14_1 facmt14_2

facc14_2 :: Constraint
facc14_2 = Tcstr facmt14_3 facmt14_2

faccs14 = [facc14_1,facc14_2]

(facrmvs14,(facrinst14,facscs14)) = all_simpl_cstr facmetavars (idinst,faccs14)

facg14 = build_graph_from_constraints facscs14

facfs14 :: FullSolution
facfs14 = (facrmvs14,[],(facrinst14,[]),facg14)

facleaf14 :: Dependent
facleaf14 = DRec u0 (DVar x0)

(facres14,facvals14) = factorize_dgraph facfs14 facleaf14

-- Example 15
facmt15_1 :: Metaterm
facmt15_1 = MTermR u0 (MTermT (read "f1[2](x1,x4)"))

facmt15_2 :: Metaterm
facmt15_2 = MTermR u0 (MTermT (read "x0"))

facmt15_3 :: Metaterm
facmt15_3 = MTermR u0 (MTermT (read "f1[2](x2,x3)"))

facc15_1 :: Constraint
facc15_1 = Tcstr facmt15_1 facmt15_2

facc15_2 :: Constraint
facc15_2 = Tcstr facmt15_3 facmt15_2

faccs15 = [facc15_1,facc15_2]

(facrmvs15,(facrinst15,facscs15)) = all_simpl_cstr facmetavars (idinst,faccs15)

facg15 = build_graph_from_constraints facscs15

facfs15_pre :: FullSolution
facfs15_pre = (facrmvs15,[],(facrinst15,[]),facg15)

facvdep15_1 :: Dependent
facvdep15_1 = DRec u0 (DVar (read "x4"))

facvval15_1 :: Term
facvval15_1 = TVar facx0u0

facpair15_1 :: (Dependent,Either Term Literal)
facpair15_1 = (facvdep15_1,Left facvval15_1)

facfs15 = update_graph_all (set_all_solutions facfs15_pre [facpair15_1]) [facpair15_1] []

facleaf15 :: Dependent
facleaf15 = DRec u0 (DVar x0)

(facres15,facvals15) = factorize_dgraph facfs15 facleaf15

facres15_pos = update_graph_all facres15 facvals15 []

-- Example 16
facmt16_1 :: Metaterm
facmt16_1 = MTermR u0 (MTermT (read "f1[2](x1,x4)"))

facmt16_2 :: Metaterm
facmt16_2 = MTermR u0 (MTermT (read "x0"))

facmt16_3 :: Metaterm
facmt16_3 = MTermR u0 (MTermT (read "f1[2](x2,x3)"))

facmt16_4 :: Metaterm
facmt16_4 = MTermR u0 (MTermT (read "f1[2](x2,x1)"))

facc16_1 :: Constraint
facc16_1 = Tcstr facmt16_1 facmt16_2

facc16_2 :: Constraint
facc16_2 = Tcstr facmt16_3 facmt16_2

facc16_3 :: Constraint
facc16_3 = Tcstr facmt16_4 facmt16_2

faccs16 = [facc16_1,facc16_2,facc16_3]

(facrmvs16,(facrinst16,facscs16)) = all_simpl_cstr facmetavars (idinst,faccs16)

facg16 = build_graph_from_constraints facscs16

facfs16_pre :: FullSolution
facfs16_pre = (facrmvs16,[],(facrinst16,[]),facg16)

facvdep16_1 :: Dependent
facvdep16_1 = DRec u0 (DVar (read "x4"))

facvval16_1 :: Term
facvval16_1 = TVar facx0u0

facpair16_1 :: (Dependent,Either Term Literal)
facpair16_1 = (facvdep16_1,Left facvval16_1)

facvdep16_2 :: Dependent
facvdep16_2 = DRec u0 (DVar (read "x3"))

facvval16_2 :: Term
facvval16_2 = TVar facx0u0

facpair16_2 :: (Dependent,Either Term Literal)
facpair16_2 = (facvdep16_2,Left facvval16_2)

facfs16 = update_graph_all (set_all_solutions facfs16_pre [facpair16_1,facpair16_2]) [facpair16_1,facpair16_2] []

facleaf16 :: Dependent
facleaf16 = DRec u0 (DVar x0)

(facres16,facvals16) = factorize_dgraph facfs16 facleaf16

facres16_pos = update_graph_all facres16 facvals16 []

-- Example 17
facmt17_1 :: Metaterm
facmt17_1 = MTermR u0 (MTermT (read "f1[2](x1,x4)"))

facmt17_2 :: Metaterm
facmt17_2 = MTermR u0 (MTermT (read "x0"))

facmt17_3 :: Metaterm
facmt17_3 = MTermR u0 (MTermT (read "f1[2](x2,x3)"))

facc17_1 :: Constraint
facc17_1 = Tcstr facmt17_1 facmt17_2

facc17_2 :: Constraint
facc17_2 = Tcstr facmt17_3 facmt17_2

faccs17 = [facc17_1,facc17_2]

(facrmvs17,(facrinst17,facscs17)) = all_simpl_cstr facmetavars (idinst,faccs17)

facg17 = build_graph_from_constraints facscs17

facfs17_pre :: FullSolution
facfs17_pre = (facrmvs17,[],(facrinst17,[]),facg17)

facvdep17_1 :: Dependent
facvdep17_1 = DRec u0 (DVar (read "x4"))

facvval17_1 :: Term
facvval17_1 = TVar facx0u0

facpair17_1 :: (Dependent,Either Term Literal)
facpair17_1 = (facvdep17_1,Left facvval17_1)

facvdep17_2 :: Dependent
facvdep17_2 = DRec u0 (DVar (read "x3"))

facvval17_2 :: Term
facvval17_2 = TVar facx1u0

facpair17_2 :: (Dependent,Either Term Literal)
facpair17_2 = (facvdep17_2,Left facvval17_2)

facfs17 = update_graph_all (set_all_solutions facfs17_pre [facpair17_1,facpair17_2]) [facpair17_1,facpair17_2] []

facleaf17 :: Dependent
facleaf17 = DRec u0 (DVar x0)

(facres17,facvals17) = factorize_dgraph facfs17 facleaf17

-- Example 18
facmt18_1 :: Metaterm
facmt18_1 = MTermR u0 (MTermT (read "f1[2](x1,f2[1](x4))"))

facmt18_2 :: Metaterm
facmt18_2 = MTermR u0 (MTermT (read "x0"))

facmt18_3 :: Metaterm
facmt18_3 = MTermR u0 (MTermT (read "f1[2](x2,f2[1](x3))"))

facc18_1 :: Constraint
facc18_1 = Tcstr facmt18_1 facmt18_2

facc18_2 :: Constraint
facc18_2 = Tcstr facmt18_3 facmt18_2

faccs18 = [facc18_1,facc18_2]

(facrmvs18,(facrinst18,facscs18)) = all_simpl_cstr facmetavars (idinst,faccs18)

facg18 = build_graph_from_constraints facscs18

facfs18_pre :: FullSolution
facfs18_pre = (facrmvs18,[],(facrinst18,[]),facg18)

facvdep18_1 :: Dependent
facvdep18_1 = DRec u0 (DVar (read "x4"))

facvval18_1 :: Term
facvval18_1 = TVar facx0u0

facpair18_1 :: (Dependent,Either Term Literal)
facpair18_1 = (facvdep18_1,Left facvval18_1)

facfs18 = update_graph_all (set_all_solutions facfs18_pre [facpair18_1]) [facpair18_1] []

facleaf18 :: Dependent
facleaf18 = DRec u0 (DVar x0)

(facres18,facvals18) = factorize_dgraph facfs18 facleaf18

facres18_pos = update_graph_all facres18 facvals18 []

-- Example 19
facmt19_1 :: Metaterm
facmt19_1 = MTermR u0 (MTermT (read "f1[2](x1,f2[1](x4))"))

facmt19_2 :: Metaterm
facmt19_2 = MTermR u0 (MTermT (read "x0"))

facmt19_3 :: Metaterm
facmt19_3 = MTermR u0 (MTermT (read "f1[2](x2,x3)"))

facc19_1 :: Constraint
facc19_1 = Tcstr facmt19_1 facmt19_2

facc19_2 :: Constraint
facc19_2 = Tcstr facmt19_3 facmt19_2

faccs19 = [facc19_1,facc19_2]

(facrmvs19,(facrinst19,facscs19)) = all_simpl_cstr facmetavars (idinst,faccs19)

facg19 = build_graph_from_constraints facscs19

facfs19_pre :: FullSolution
facfs19_pre = (facrmvs19,[],(facrinst19,[]),facg19)

facvdep19_1 :: Dependent
facvdep19_1 = DRec u0 (DVar (read "x4"))

facvval19_1 :: Term
facvval19_1 = TVar facx0u0

facpair19_1 :: (Dependent,Either Term Literal)
facpair19_1 = (facvdep19_1,Left facvval19_1)

facfs19 = update_graph_all (set_all_solutions facfs19_pre [facpair19_1]) [facpair19_1] []

facleaf19 :: Dependent
facleaf19 = DRec u0 (DVar x0)

(facres19,facvals19) = factorize_dgraph facfs19 facleaf19

facres19_pos = update_graph_all facres19 facvals19 []

-- Example 19.1
facmt19_1_1 :: Metaterm
facmt19_1_1 = MTermR u0 (MTermT (read "f1[2](x1,x4)"))

facmt19_1_2 :: Metaterm
facmt19_1_2 = MTermR u0 (MTermT (read "x0"))

facmt19_1_3 :: Metaterm
facmt19_1_3 = MTermR u0 (MTermT (read "f1[2](x2,x3)"))

facc19_1_1 :: Constraint
facc19_1_1 = Tcstr facmt19_1_1 facmt19_1_2

facc19_1_2 :: Constraint
facc19_1_2 = Tcstr facmt19_1_3 facmt19_1_2

faccs19_1 = [facc19_1_1,facc19_1_2]

(facrmvs19_1,(facrinst19_1,facscs19_1)) = all_simpl_cstr facmetavars (idinst,faccs19_1)

facg19_1 = build_graph_from_constraints facscs19_1

facfs19_1_pre :: FullSolution
facfs19_1_pre = (facrmvs19_1,[],(facrinst19_1,[]),facg19_1)

facvdep19_1_1 :: Dependent
facvdep19_1_1 = DRec u0 (DVar (read "x4"))

facvval19_1_1 :: Term
facvval19_1_1 = TFun (read "f2[1]") [TVar facx0u0]

facpair19_1_1 :: (Dependent,Either Term Literal)
facpair19_1_1 = (facvdep19_1_1,Left facvval19_1_1)

facfs19_1 = update_graph_all (set_all_solutions facfs19_1_pre [facpair19_1_1]) [facpair19_1_1] []

facleaf19_1 :: Dependent
facleaf19_1 = DRec u0 (DVar x0)

(facres19_1,facvals19_1) = factorize_dgraph facfs19_1 facleaf19_1

facres19_1_pos = update_graph_all facres19_1 facvals19_1 []

-- Example 20
facmt20_1 :: Metaterm
facmt20_1 = MTermR u0 (MTermT (read "f1[2](x1,f2[1](x4))"))

facmt20_2 :: Metaterm
facmt20_2 = MTermR u0 (MTermT (read "x0"))

facmt20_3 :: Metaterm
facmt20_3 = MTermR u0 (MTermT (read "f1[2](x2,x3)"))

facc20_1 :: Constraint
facc20_1 = Tcstr facmt20_1 facmt20_2

facc20_2 :: Constraint
facc20_2 = Tcstr facmt20_3 facmt20_2

faccs20 = [facc20_1,facc20_2]

(facrmvs20,(facrinst20,facscs20)) = all_simpl_cstr facmetavars (idinst,faccs20)

facg20 = build_graph_from_constraints facscs20

facfs20_pre :: FullSolution
facfs20_pre = (facrmvs20,[],(facrinst20,[]),facg20)

facvdep20_1 :: Dependent
facvdep20_1 = DRec u0 (DVar (read "x4"))

facvval20_1 :: Term
facvval20_1 = TVar facx0u0

facpair20_1 :: (Dependent,Either Term Literal)
facpair20_1 = (facvdep20_1,Left facvval20_1)

facvdep20_2 :: Dependent
facvdep20_2 = DRec u0 (DVar (read "x3"))

facvval20_2 :: Term
facvval20_2 = TFun (read "f2[1]") [TVar facx1u0]

facpair20_2 :: (Dependent,Either Term Literal)
facpair20_2 = (facvdep20_2,Left facvval20_2)

facfs20 = update_graph_all (set_all_solutions facfs20_pre [facpair20_1,facpair20_2]) [facpair20_1,facpair20_2] []

facleaf20 :: Dependent
facleaf20 = DRec u0 (DVar x0)

(facres20,facvals20) = factorize_dgraph facfs20 facleaf20

facres20_pos = update_graph_all facres20 facvals20 []

-- Example 20.1
facmt20_1_1 :: Metaterm
facmt20_1_1 = MTermR u0 (MTermT (read "f1[2](x1,f2[1](x4))"))

facmt20_1_2 :: Metaterm
facmt20_1_2 = MTermR u0 (MTermT (read "x0"))

facmt20_1_3 :: Metaterm
facmt20_1_3 = MTermR u0 (MTermT (read "f1[2](x2,x3)"))

facc20_1_1 :: Constraint
facc20_1_1 = Tcstr facmt20_1_1 facmt20_1_2

facc20_1_2 :: Constraint
facc20_1_2 = Tcstr facmt20_1_3 facmt20_1_2

faccs20_1 = [facc20_1_1,facc20_1_2]

(facrmvs20_1,(facrinst20_1,facscs20_1)) = all_simpl_cstr facmetavars (idinst,faccs20_1)

facg20_1 = build_graph_from_constraints facscs20_1

facfs20_1_pre :: FullSolution
facfs20_1_pre = (facrmvs20_1,[],(facrinst20_1,[]),facg20_1)

facvdep20_1_1 :: Dependent
facvdep20_1_1 = DRec u0 (DVar (read "x4"))

facvval20_1_1 :: Term
facvval20_1_1 = TVar facx0u0

facpair20_1_1 :: (Dependent,Either Term Literal)
facpair20_1_1 = (facvdep20_1_1,Left facvval20_1_1)

facvdep20_1_2 :: Dependent
facvdep20_1_2 = DRec u0 (DVar (read "x3"))

facvval20_1_2 :: Term
facvval20_1_2 = TFun (read "f2[1]") [TVar facx0u0]

facpair20_1_2 :: (Dependent,Either Term Literal)
facpair20_1_2 = (facvdep20_1_2,Left facvval20_1_2)

facfs20_1 = update_graph_all (set_all_solutions facfs20_1_pre [facpair20_1_1,facpair20_1_2]) [facpair20_1_1,facpair20_1_2] []

facleaf20_1 :: Dependent
facleaf20_1 = DRec u0 (DVar x0)

(facres20_1,facvals20_1) = factorize_dgraph facfs20_1 facleaf20_1

facres20_1_pos = update_graph_all facres20_1 facvals20_1 []

-- Example 21
facmt21_1 :: Metaterm
facmt21_1 = MTermR u0 (MTermT (read "f1[2](x1,f2[1](x4))"))

facmt21_2 :: Metaterm
facmt21_2 = MTermR u0 (MTermT (read "x0"))

facmt21_3 :: Metaterm
facmt21_3 = MTermR u0 (MTermT (read "f1[2](x2,x3)"))

facc21_1 :: Constraint
facc21_1 = Tcstr facmt21_1 facmt21_2

facc21_2 :: Constraint
facc21_2 = Tcstr facmt21_3 facmt21_2

faccs21 = [facc21_1,facc21_2]

(facrmvs21,(facrinst21,facscs21)) = all_simpl_cstr facmetavars (idinst,faccs21)

facg21 = build_graph_from_constraints facscs21

facfs21_pre :: FullSolution
facfs21_pre = (facrmvs21,[],(facrinst21,[]),facg21)

facvdep21_1 :: Dependent
facvdep21_1 = DRec u0 (DVar (read "x4"))

facvval21_1 :: Term
facvval21_1 = TVar facx0u0

facpair21_1 :: (Dependent,Either Term Literal)
facpair21_1 = (facvdep21_1,Left facvval21_1)

facvdep21_2 :: Dependent
facvdep21_2 = DRec u0 (DVar (read "x3"))

facvval21_2 :: Term
facvval21_2 = TVar facx0u0

facpair21_2 :: (Dependent,Either Term Literal)
facpair21_2 = (facvdep21_2,Left facvval21_2)

facfs21 = update_graph_all (set_all_solutions facfs21_pre [facpair21_1,facpair21_2]) [facpair21_1,facpair21_2] []

facleaf21 :: Dependent
facleaf21 = DRec u0 (DVar x0)

(facres21,facvals21) = factorize_dgraph facfs21 facleaf21




-- show_all_cferrs :: [ConstraintFormErrors] -> IO ()
-- verify_all_unifier_constraints_wellformed :: Signature -> [Metavariable] -> [Unifier] -> [Constraint] -> [ConstraintFormErrors]


-- Testing enumeration/propagation
infinity :: Int
infinity = 99999999999999999

show_nth_sol :: Enumeration (h,FullSolution) -> Int -> IO ()
show_nth_sol en i = show_full_soln ((enum_up_to_h i en) !! i)

show_all_sols :: Enumeration (h,FullSolution) -> IO ()
show_all_sols en = foldr (>>) (putStr "") (map (\pair -> (putStr ("Graph solution #" ++ (show (fst pair)) ++ ":\n")) >> (show_full_soln (snd pair))) (zip [0..infinity] (enum_up_to_h infinity en)))

show_nth_inst :: [Metavariable] -> [Unifier] -> Enumeration (h,Maybe ([UnifierDescription],Instantiation)) -> Int -> IO ()
show_nth_inst mvs us en i = show_one_inst mvs us ((enum_up_to_h i en) !! i)

show_one_inst :: [Metavariable] -> [Unifier] -> Maybe ([UnifierDescription],Instantiation) -> IO ()
show_one_inst mvs us Nothing = putStr "Unsatisiable.\n"
show_one_inst mvs us (Just (uds,inst)) = putStr ((show_inst inst mvs) ++ "\nwith\n" ++ (show_unifs us uds))

show_all_insts :: [Metavariable] -> [Unifier] -> Enumeration (h,Maybe ([UnifierDescription],Instantiation)) -> IO ()
show_all_insts mvs us en = foldr (>>) (putStr "") (map (\pair -> (putStr ("Solution #" ++ (show (fst pair)) ++ ":\n")) >> (show_one_inst mvs us (snd pair))) (zip [0..infinity] (enum_up_to_h infinity en)))

-- We use an empty unifier description list as an indicator for an unsatisfiable set of constraints.
show_unifs :: [Unifier] -> [UnifierDescription] -> String
show_unifs [] [] = ""
show_unifs (u:us) (ud:uds) = (show u) ++ ": " ++ (show ud) ++ "\n" ++ (show_unifs us uds)
-- Just for debugging
show_unifs [] (ud:uds) = "(Unknown unifier): " ++ (show ud) ++ "\n" ++ (show_unifs [] uds)
--show_unifs (u:us) [] = (show u) ++ ": []\n" ++ (show_unifs us [])
show_unifs (u:us) [] = "Unsatisfiable.\n"

eprop_n_base_vars :: Int
eprop_n_base_vars = 5

-- Variables
--x0 :: Variable
--x0 = Var 0

--x1 :: Variable
--x1 = Var 1

--x2 :: Variable
--x2 = Var 2

-- x3 :: Variable
-- x3 = Var 3

-- x4 :: Variable
-- x4 = Var 4

-- Metavariables

-- Metavariables
-- mx0 :: Metavariable
-- mx0 = Metavar 0

-- mx1 :: Metavariable
-- mx1 = Metavar 1

mx2 :: Metavariable
mx2 = Metavar 2

epropmetavars = [mx0,mx1,mx2]

-- Unifiers
--u0 :: Unifier
--u0 = U 0

--u1 :: Unifier
--u1 = U 1

u2 :: Unifier
u2 = U 2

epropus = [u0,u1,u2]

-- Derived variables
epropx0u0 :: Variable
epropx0u0 = get_image_var eprop_n_base_vars u0 x0

epropx1u0 :: Variable
epropx1u0 = get_image_var eprop_n_base_vars u0 x1

epropx2u0 :: Variable
epropx2u0 = get_image_var eprop_n_base_vars u0 x2

epropsig :: Signature
epropsig = ([read "p1[2]",read "p2[1]"],[read "f1[2]",read "f2[2]",read "f3[1]",read "f4[1]"],eprop_n_base_vars)

-- Example 1
epropmt1_1 :: Metaterm
epropmt1_1 = MTermR u0 (MTermT (read "f3[1](x1)"))

epropmt1_2 :: Metaterm
epropmt1_2 = MTermR u0 (MTermT (read "x0"))

epropc1_1 :: Constraint
epropc1_1 = Tcstr epropmt1_1 epropmt1_2

epropcs1 = [epropc1_1]

(eproprmvs1,(eproprinst1,epropscs1)) = all_simpl_cstr epropmetavars (idinst,epropcs1)

epropg1 = build_graph_from_constraints epropscs1

epropfs1 :: FullSolution
epropfs1 = (eproprmvs1,[],(eproprinst1,[]),epropg1)

epropres1 :: Enumeration (_,FullSolution)
epropres1 = enumerate_and_propagate_all epropsig epropfs1

eproperrs1 :: [ConstraintFormErrors]
eproperrs1 = verify_all_unifier_constraints_wellformed epropsig epropmetavars epropus epropcs1

epropinst1 :: Enumeration (_,Maybe ([UnifierDescription],Instantiation))
epropinst1 = solve_unifier_constraints epropsig epropmetavars epropcs1 epropus

-- Example 2
epropmt2_1 :: Metaterm
epropmt2_1 = MTermR u0 (MTermT (read "f1[2](x1,x2)"))

epropmt2_2 :: Metaterm
epropmt2_2 = MTermR u0 (MTermT (read "x0"))

epropc2_1 :: Constraint
epropc2_1 = Tcstr epropmt2_1 epropmt2_2

epropcs2 = [epropc2_1]

(eproprmvs2,(eproprinst2,epropscs2)) = all_simpl_cstr epropmetavars (idinst,epropcs2)

epropg2 = build_graph_from_constraints epropscs2

epropfs2 :: FullSolution
epropfs2 = (eproprmvs2,[],(eproprinst2,[]),epropg2)

epropres2 :: Enumeration (_,FullSolution)
epropres2 = enumerate_and_propagate_all epropsig epropfs2

eproperrs2 :: [ConstraintFormErrors]
eproperrs2 = verify_all_unifier_constraints_wellformed epropsig epropmetavars epropus epropcs2

epropinst2 :: Enumeration (_,Maybe ([UnifierDescription],Instantiation))
epropinst2 = solve_unifier_constraints epropsig epropmetavars epropcs2 epropus

-- Example 3
epropmt3_1 :: Metaterm
epropmt3_1 = MTermR u0 (MTermT (read "f3[1](x1)"))

epropmt3_2 :: Metaterm
epropmt3_2 = MTermR u0 (MTermT (read "x0"))

epropmt3_3 :: Metaterm
epropmt3_3 = MTermR u0 (MTermT (read "f4[1](x2)"))

epropmt3_4 :: Metaterm
epropmt3_4 = MTermR u0 (MTermT (read "x1"))

epropc3_1 :: Constraint
epropc3_1 = Tcstr epropmt3_1 epropmt3_2

epropc3_2 :: Constraint
epropc3_2 = Tcstr epropmt3_3 epropmt3_4

epropcs3 = [epropc3_1,epropc3_2]

(eproprmvs3,(eproprinst3,epropscs3)) = all_simpl_cstr epropmetavars (idinst,epropcs3)

epropg3 = build_graph_from_constraints epropscs3

epropfs3 :: FullSolution
epropfs3 = (eproprmvs3,[],(eproprinst3,[]),epropg3)

epropres3 :: Enumeration (_,FullSolution)
epropres3 = enumerate_and_propagate_all epropsig epropfs3

eproperrs3 :: [ConstraintFormErrors]
eproperrs3 = verify_all_unifier_constraints_wellformed epropsig epropmetavars epropus epropcs3

epropinst3 :: Enumeration (_,Maybe ([UnifierDescription],Instantiation))
epropinst3 = solve_unifier_constraints epropsig epropmetavars epropcs3 epropus

-- Example 4
epropmt4_1 :: Metaterm
epropmt4_1 = MTermR u0 (MTermT (read "f1[2](x1,x2)"))

epropmt4_2 :: Metaterm
epropmt4_2 = MTermR u0 (MTermT (read "x0"))

epropmt4_3 :: Metaterm
epropmt4_3 = MTermR u1 (MTermR u0 (MTermT (read "x0")))

epropmt4_4 :: Metaterm
epropmt4_4 = MTermR u1 (MTermT (read "x1"))

epropc4_1 :: Constraint
epropc4_1 = Tcstr epropmt4_1 epropmt4_2

epropc4_2 :: Constraint
epropc4_2 = Tcstr epropmt4_3 epropmt4_4

epropcs4 = [epropc4_1,epropc4_2]

(eproprmvs4,(eproprinst4,epropscs4)) = all_simpl_cstr epropmetavars (idinst,epropcs4)

epropg4 = build_graph_from_constraints epropscs4

epropfs4 :: FullSolution
epropfs4 = (eproprmvs4,[],(eproprinst4,[]),epropg4)

epropres4 :: Enumeration (_,FullSolution)
epropres4 = enumerate_and_propagate_all epropsig epropfs4

eproperrs4 :: [ConstraintFormErrors]
eproperrs4 = verify_all_unifier_constraints_wellformed epropsig epropmetavars epropus epropcs4

epropinst4 :: Enumeration (_,Maybe ([UnifierDescription],Instantiation))
epropinst4 = solve_unifier_constraints epropsig epropmetavars epropcs4 epropus

-- Example 5
epropmt5_1 :: Metaterm
epropmt5_1 = MTermR u0 (MTermT (read "f1[2](x1,x2)"))

epropmt5_2 :: Metaterm
epropmt5_2 = MTermR u0 (MTermT (read "x0"))

epropmt5_3 :: Metaterm
epropmt5_3 = MTermR u1 (MTermR u0 (MTermT (read "x0")))

epropmt5_4 :: Metaterm
epropmt5_4 = MTermR u1 (MTermR u0 (MTermT (read "x1")))

epropc5_1 :: Constraint
epropc5_1 = Tcstr epropmt5_1 epropmt5_2

epropc5_2 :: Constraint
epropc5_2 = Tcstr epropmt5_3 epropmt5_4

epropcs5 = [epropc5_1,epropc5_2]

eproperrs5 :: [ConstraintFormErrors]
eproperrs5 = verify_all_unifier_constraints_wellformed epropsig epropmetavars epropus epropcs5

epropinst5 :: Enumeration (_,Maybe ([UnifierDescription],Instantiation))
epropinst5 = solve_unifier_constraints epropsig epropmetavars epropcs5 epropus

-- Example 6
epropmt6_1 :: Metaterm
epropmt6_1 = MTermR u0 (MTermT (read "f1[2](x1,x2)"))

epropmt6_2 :: Metaterm
epropmt6_2 = MTermR u0 (MTermT (read "x0"))

epropmt6_3 :: Metaterm
epropmt6_3 = MTermR u1 (MTermR u0 (MTermT (read "x0")))

epropmt6_4 :: Metaterm
epropmt6_4 = MTermR u1 (MTermT (read "f2[2](x1,x2)"))

epropc6_1 :: Constraint
epropc6_1 = Tcstr epropmt6_1 epropmt6_2

epropc6_2 :: Constraint
epropc6_2 = Tcstr epropmt6_3 epropmt6_4

epropcs6 = [epropc6_1,epropc6_2]

(eproprmvs6,(eproprinst6,epropscs6)) = all_simpl_cstr epropmetavars (idinst,epropcs6)

epropg6 = build_graph_from_constraints epropscs6

epropfs6 :: FullSolution
epropfs6 = (eproprmvs6,[],(eproprinst6,[]),epropg6)

epropres6 :: Enumeration (_,FullSolution)
epropres6 = enumerate_and_propagate_all epropsig epropfs6

eproperrs6 :: [ConstraintFormErrors]
eproperrs6 = verify_all_unifier_constraints_wellformed epropsig epropmetavars epropus epropcs6

epropinst6 :: Enumeration (_,Maybe ([UnifierDescription],Instantiation))
epropinst6 = solve_unifier_constraints epropsig epropmetavars epropcs6 epropus

-- Example 7
epropmt7_1 :: Metaterm
epropmt7_1 = MTermR u0 (MTermT (read "f1[2](x1,x2)"))

epropmt7_2 :: Metaterm
epropmt7_2 = MTermR u0 (MTermT (read "x0"))

epropmt7_3 :: Metaterm
epropmt7_3 = MTermR u1 (MTermR u0 (MTermT (read "x0")))

epropmt7_4 :: Metaterm
epropmt7_4 = MTermR u1 (MTermR u0 (MTermT (read "x3")))

epropc7_1 :: Constraint
epropc7_1 = Tcstr epropmt7_1 epropmt7_2

epropc7_2 :: Constraint
epropc7_2 = Tcstr epropmt7_3 epropmt7_4

epropcs7 = [epropc7_1,epropc7_2]

eproperrs7 :: [ConstraintFormErrors]
eproperrs7 = verify_all_unifier_constraints_wellformed epropsig epropmetavars epropus epropcs7

epropinst7 :: Enumeration (_,Maybe ([UnifierDescription],Instantiation))
epropinst7 = solve_unifier_constraints epropsig epropmetavars epropcs7 epropus

-- Example 8
epropmt8_1 :: Metaterm
epropmt8_1 = MTermR u0 (MTermT (read "f1[2](x1,x2)"))

epropmt8_2 :: Metaterm
epropmt8_2 = MTermR u0 (MTermT (read "x0"))

epropml8_3 :: Metaliteral
epropml8_3 = MLitR u1 (MLitL (read "p1[2](x3,x3)"))

epropml8_4 :: Metaliteral
epropml8_4 = MLitR u1 (MLitR u0 (MLitL (read "p1[2](x0,x3)")))

epropmt8_5 :: Metaterm
epropmt8_5 = MTermR u2 (MTermR u0 (MTermT (read "x0")))

epropmt8_6 :: Metaterm
epropmt8_6 = MTermR u2 (MTermR u1 (MTermT (read "x3")))

epropc8_1 :: Constraint
epropc8_1 = Tcstr epropmt8_1 epropmt8_2

epropc8_2 :: Constraint
epropc8_2 = Lcstr epropml8_3 epropml8_4

epropc8_3 :: Constraint
epropc8_3 = Tcstr epropmt8_5 epropmt8_6

epropcs8 = [epropc8_1,epropc8_2,epropc8_3]

(eproprmvs8,(eproprinst8,epropscs8)) = all_simpl_cstr epropmetavars (idinst,epropcs8)

epropg8 = build_graph_from_constraints epropscs8

epropfs8 :: FullSolution
epropfs8 = (eproprmvs8,[],(eproprinst8,[]),epropg8)

epropres8 :: Enumeration (_,FullSolution)
epropres8 = enumerate_and_propagate_all epropsig epropfs8

eproperrs8 :: [ConstraintFormErrors]
eproperrs8 = verify_all_unifier_constraints_wellformed epropsig epropmetavars epropus epropcs8

epropinst8 :: Enumeration (_,Maybe ([UnifierDescription],Instantiation))
epropinst8 = solve_unifier_constraints epropsig epropmetavars epropcs8 epropus

-- Example 9
epropmt9_1 :: Metaterm
epropmt9_1 = MTermR u0 (MTermT (read "f1[2](x1,x2)"))

epropmt9_2 :: Metaterm
epropmt9_2 = MTermR u0 (MTermT (read "x0"))

epropml9_3 :: Metaliteral
epropml9_3 = MLitR u1 (MLitL (read "p1[2](x3,x3)"))

epropml9_4 :: Metaliteral
epropml9_4 = MLitR u1 (MLitR u0 (MLitL (read "p1[2](x0,x3)")))

epropmt9_5 :: Metaterm
epropmt9_5 = MTermR u2 (MTermR u0 (MTermT (read "f1[2](x2,x1)")))

epropmt9_6 :: Metaterm
epropmt9_6 = MTermR u2 (MTermR u1 (MTermT (read "x3")))

epropc9_1 :: Constraint
epropc9_1 = Tcstr epropmt9_1 epropmt9_2

epropc9_2 :: Constraint
epropc9_2 = Lcstr epropml9_3 epropml9_4

epropc9_3 :: Constraint
epropc9_3 = Tcstr epropmt9_5 epropmt9_6

epropcs9 = [epropc9_1,epropc9_2,epropc9_3]

(eproprmvs9,(eproprinst9,epropscs9)) = all_simpl_cstr epropmetavars (idinst,epropcs9)

epropg9 = build_graph_from_constraints epropscs9

epropfs9 :: FullSolution
epropfs9 = (eproprmvs9,[],(eproprinst9,[]),epropg9)

epropres9 :: Enumeration (_,FullSolution)
epropres9 = enumerate_and_propagate_all epropsig epropfs9

eproperrs9 :: [ConstraintFormErrors]
eproperrs9 = verify_all_unifier_constraints_wellformed epropsig epropmetavars epropus epropcs9

epropinst9 :: Enumeration (_,Maybe ([UnifierDescription],Instantiation))
epropinst9 = solve_unifier_constraints epropsig epropmetavars epropcs9 epropus

-- Example 10
epropmt10_1 :: Metaterm
epropmt10_1 = MTermR u0 (MTermT (read "f1[2](x1,x2)"))

epropmt10_2 :: Metaterm
epropmt10_2 = MTermR u0 (MTermT (read "x0"))

epropml10_3 :: Metaliteral
epropml10_3 = MLitR u1 (MLitL (read "p1[2](x3,x3)"))

epropml10_4 :: Metaliteral
epropml10_4 = MLitR u1 (MLitR u0 (MLitL (read "p1[2](x0,x3)")))

epropmt10_5 :: Metaterm
epropmt10_5 = MTermR u2 (MTermR u0 (MTermT (read "f3[1](x0)")))

epropmt10_6 :: Metaterm
epropmt10_6 = MTermR u2 (MTermR u1 (MTermT (read "x3")))

epropc10_1 :: Constraint
epropc10_1 = Tcstr epropmt10_1 epropmt10_2

epropc10_2 :: Constraint
epropc10_2 = Lcstr epropml10_3 epropml10_4

epropc10_3 :: Constraint
epropc10_3 = Tcstr epropmt10_5 epropmt10_6

epropcs10 = [epropc10_1,epropc10_2,epropc10_3]

(eproprmvs10,(eproprinst10,epropscs10)) = all_simpl_cstr epropmetavars (idinst,epropcs10)

epropg10 = build_graph_from_constraints epropscs10

epropfs10 :: FullSolution
epropfs10 = (eproprmvs10,[],(eproprinst10,[]),epropg10)

epropres10 :: Enumeration (_,FullSolution)
epropres10 = enumerate_and_propagate_all epropsig epropfs10

eproperrs10 :: [ConstraintFormErrors]
eproperrs10 = verify_all_unifier_constraints_wellformed epropsig epropmetavars epropus epropcs10

epropinst10 :: Enumeration (_,Maybe ([UnifierDescription],Instantiation))
epropinst10 = solve_unifier_constraints epropsig epropmetavars epropcs10 epropus

-- Example 11
epropmt11_1 :: Metaterm
epropmt11_1 = MTermR u0 (MTermT (read "f1[2](x1,x2)"))

epropmt11_2 :: Metaterm
epropmt11_2 = MTermR u0 (MTermT (read "x0"))

epropml11_3 :: Metaliteral
epropml11_3 = MLitR u1 (MLitL (read "p1[2](x3,x3)"))

epropml11_4 :: Metaliteral
epropml11_4 = MLitR u1 (MLitR u0 (MLitL (read "p1[2](x0,x2)")))

epropmt11_5 :: Metaterm
epropmt11_5 = MTermR u2 (MTermR u0 (MTermT (read "x0")))

epropmt11_6 :: Metaterm
epropmt11_6 = MTermR u2 (MTermR u1 (MTermT (read "x3")))

epropc11_1 :: Constraint
epropc11_1 = Tcstr epropmt11_1 epropmt11_2

epropc11_2 :: Constraint
epropc11_2 = Lcstr epropml11_3 epropml11_4

epropc11_3 :: Constraint
epropc11_3 = Tcstr epropmt11_5 epropmt11_6

epropcs11 = [epropc11_1,epropc11_2,epropc11_3]

eproperrs11 :: [ConstraintFormErrors]
eproperrs11 = verify_all_unifier_constraints_wellformed epropsig epropmetavars epropus epropcs11

epropinst11 :: Enumeration (_,Maybe ([UnifierDescription],Instantiation))
epropinst11 = solve_unifier_constraints epropsig epropmetavars epropcs11 epropus

-- Example 12
epropmt12_1 :: Metaterm
epropmt12_1 = MTermR u0 (MTermT (read "f1[2](x1,x2)"))

epropmt12_2 :: Metaterm
epropmt12_2 = MTermR u0 (MTermT (read "x0"))

epropml12_3 :: Metaliteral
epropml12_3 = MLitR u1 (MLitL (read "p2[1](f3[1](x1))"))

epropml12_4 :: Metaliteral
epropml12_4 = MLitR u1 (MLitR u0 (MLitL (read "p2[1](x0)")))

epropc12_1 :: Constraint
epropc12_1 = Tcstr epropmt12_1 epropmt12_2

epropc12_2 :: Constraint
epropc12_2 = Lcstr epropml12_3 epropml12_4

epropcs12 = [epropc12_1,epropc12_2]

eproperrs12 :: [ConstraintFormErrors]
eproperrs12 = verify_all_unifier_constraints_wellformed epropsig epropmetavars epropus epropcs12

epropinst12 :: Enumeration (_,Maybe ([UnifierDescription],Instantiation))
epropinst12 = solve_unifier_constraints epropsig epropmetavars epropcs12 epropus

-- Example 13

epropmt13_1 :: Metaterm
epropmt13_1 = MTermR u0 (MTermT (read "f1[2](x1,x2)"))

epropmt13_2 :: Metaterm
epropmt13_2 = MTermR u0 (MTermT (read "x0"))

epropml13_3 :: Metaliteral
epropml13_3 = MLitR u1 (MLitL (read "p2[1](f3[1](x1))"))

epropml13_4 :: Metaliteral
epropml13_4 = MLitR u1 (MLitL (read "p2[1](x0)"))

epropc13_1 :: Constraint
epropc13_1 = Tcstr epropmt13_1 epropmt13_2

epropc13_2 :: Constraint
epropc13_2 = Lcstr epropml13_3 epropml13_4

epropcs13 = [epropc13_1,epropc13_2]

eproperrs13 :: [ConstraintFormErrors]
eproperrs13 = verify_all_unifier_constraints_wellformed epropsig epropmetavars epropus epropcs13

epropinst13 :: Enumeration (_,Maybe ([UnifierDescription],Instantiation))
epropinst13 = solve_unifier_constraints epropsig epropmetavars epropcs13 epropus

-- Example 14

epropmt14_1 :: Metaterm
epropmt14_1 = MTermR u0 (MTermT (read "x1"))

epropmt14_2 :: Metaterm
epropmt14_2 = MTermR u0 (MTermT (read "x0"))

epropmt14_3 :: Metaterm
epropmt14_3 = MTermR u1 (MTermR u0 (MTermT (read "x0")))

epropmt14_4 :: Metaterm
epropmt14_4 = MTermR u1 (MTermT (read "f3[1](x2)"))

epropc14_1 :: Constraint
epropc14_1 = Tcstr epropmt14_1 epropmt14_2

epropc14_2 :: Constraint
epropc14_2 = Tcstr epropmt14_3 epropmt14_4

epropcs14 = [epropc14_1,epropc14_2]

eproperrs14 :: [ConstraintFormErrors]
eproperrs14 = verify_all_unifier_constraints_wellformed epropsig epropmetavars epropus epropcs14

epropinst14 :: Enumeration (_,Maybe ([UnifierDescription],Instantiation))
epropinst14 = solve_unifier_constraints epropsig epropmetavars epropcs14 epropus

-- Example 15
epropmt15_1 :: Metaterm
epropmt15_1 = MTermR u0 (MTermT (read "f3[1](x1)"))

epropmt15_2 :: Metaterm
epropmt15_2 = MTermR u0 (MTermT (read "X0"))

epropc15_1 :: Constraint
epropc15_1 = Tcstr epropmt15_1 epropmt15_2

epropcs15 = [epropc15_1]

eproperrs15 :: [ConstraintFormErrors]
eproperrs15 = verify_all_unifier_constraints_wellformed epropsig epropmetavars epropus epropcs15

(eproprmvs15,(eproprinst15,epropscs15)) = all_simpl_cstr epropmetavars (idinst,epropcs15)

epropg15 = build_graph_from_constraints epropscs15

epropfs15 :: FullSolution
epropfs15 = (eproprmvs15,[],(eproprinst15,[]),epropg15)

epropres15 :: Enumeration (_,FullSolution)
epropres15 = enumerate_and_propagate_all epropsig epropfs15

epropinst15 :: Enumeration (_,Maybe ([UnifierDescription],Instantiation))
epropinst15 = solve_unifier_constraints epropsig epropmetavars epropcs15 epropus

-- Example 16
epropmt16_1 :: Metaterm
epropmt16_1 = MTermR u0 (MTermT (read "x1"))

epropmt16_2 :: Metaterm
epropmt16_2 = MTermR u0 (MTermT (read "f3[1](X0)"))

epropc16_1 :: Constraint
epropc16_1 = Tcstr epropmt16_1 epropmt16_2

epropcs16 = [epropc16_1]

eproperrs16 :: [ConstraintFormErrors]
eproperrs16 = verify_all_unifier_constraints_wellformed epropsig epropmetavars epropus epropcs16

(eproprmvs16,(eproprinst16,epropscs16)) = all_simpl_cstr epropmetavars (idinst,epropcs16)

epropg16 = build_graph_from_constraints epropscs16

epropfs16 :: FullSolution
epropfs16 = (eproprmvs16,[],(eproprinst16,[]),epropg16)

epropres16 :: Enumeration (_,FullSolution)
epropres16 = enumerate_and_propagate_all epropsig epropfs16

epropinst16 :: Enumeration (_,Maybe ([UnifierDescription],Instantiation))
epropinst16 = solve_unifier_constraints epropsig epropmetavars epropcs16 epropus

-- Example 17
epropmt17_1 :: Metaterm
epropmt17_1 = MTermR u0 (MTermT (read "x0"))

epropmt17_2 :: Metaterm
epropmt17_2 = MTermR u0 (MTermT (read "f1[2](x1,x2)"))

epropmt17_3 :: Metaterm
epropmt17_3 = MTermR u1 (MTermT (read "X0"))

epropmt17_4 :: Metaterm
epropmt17_4 = MTermR u1 (MTermR u0 (MTermT (read "x0")))

epropc17_1 :: Constraint
epropc17_1 = Tcstr epropmt17_1 epropmt17_2

epropc17_2 :: Constraint
epropc17_2 = Tcstr epropmt17_3 epropmt17_4

epropcs17 = [epropc17_1,epropc17_2]

eproperrs17 :: [ConstraintFormErrors]
eproperrs17 = verify_all_unifier_constraints_wellformed epropsig epropmetavars epropus epropcs17

(eproprmvs17,(eproprinst17,epropscs17)) = all_simpl_cstr epropmetavars (idinst,epropcs17)

epropg17 = build_graph_from_constraints epropscs17

epropfs17 :: FullSolution
epropfs17 = (eproprmvs17,[],(eproprinst17,[]),epropg17)

epropres17 :: Enumeration (_,FullSolution)
epropres17 = enumerate_and_propagate_all epropsig epropfs17

epropinst17 :: Enumeration (_,Maybe ([UnifierDescription],Instantiation))
epropinst17 = solve_unifier_constraints epropsig epropmetavars epropcs17 epropus

-- Example 18
epropmt18_1 :: Metaterm
epropmt18_1 = MTermR u0 (MTermT (read "x0"))

epropmt18_2 :: Metaterm
epropmt18_2 = MTermR u0 (MTermT (read "f1[2](x1,x2)"))

epropmt18_3 :: Metaterm
epropmt18_3 = MTermR u1 (MTermR u0 (MTermT (read "X0")))

epropmt18_4 :: Metaterm
epropmt18_4 = MTermR u1 (MTermT (read "x0"))

epropc18_1 :: Constraint
epropc18_1 = Tcstr epropmt18_1 epropmt18_2

epropc18_2 :: Constraint
epropc18_2 = Tcstr epropmt18_3 epropmt18_4

epropcs18 = [epropc18_1,epropc18_2]

eproperrs18 :: [ConstraintFormErrors]
eproperrs18 = verify_all_unifier_constraints_wellformed epropsig epropmetavars epropus epropcs18

(eproprmvs18,(eproprinst18,epropscs18)) = all_simpl_cstr epropmetavars (idinst,epropcs18)

epropg18 = build_graph_from_constraints epropscs18

epropfs18 :: FullSolution
epropfs18 = (eproprmvs18,[],(eproprinst18,[]),epropg18)

epropres18 :: Enumeration (_,FullSolution)
epropres18 = enumerate_and_propagate_all epropsig epropfs18

epropinst18 :: Enumeration (_,Maybe ([UnifierDescription],Instantiation))
epropinst18 = solve_unifier_constraints epropsig epropmetavars epropcs18 epropus

-- Example 19
epropmt19_1 :: Metaterm
epropmt19_1 = MTermR u0 (MTermT (read "x0"))

epropmt19_2 :: Metaterm
epropmt19_2 = MTermR u0 (MTermT (read "f1[2](x1,x2)"))

epropmt19_3 :: Metaterm
epropmt19_3 = MTermR u1 (MTermR u0 (MTermT (read "X0")))

epropmt19_4 :: Metaterm
epropmt19_4 = MTermR u1 (MTermR u0 (MTermT (read "x0")))

epropc19_1 :: Constraint
epropc19_1 = Tcstr epropmt19_1 epropmt19_2

epropc19_2 :: Constraint
epropc19_2 = Tcstr epropmt19_3 epropmt19_4

epropcs19 = [epropc19_1,epropc19_2]

eproperrs19 :: [ConstraintFormErrors]
eproperrs19 = verify_all_unifier_constraints_wellformed epropsig epropmetavars epropus epropcs19

epropinst19 :: Enumeration (_,Maybe ([UnifierDescription],Instantiation))
epropinst19 = solve_unifier_constraints epropsig epropmetavars epropcs19 epropus

-- Example 20
epropmt20_1 :: Metaterm
epropmt20_1 = MTermR u0 (MTermT (read "x1"))

epropmt20_2 :: Metaterm
epropmt20_2 = MTermR u0 (MTermT (read "f3[1](X0)"))

epropmt20_3 :: Metaterm
epropmt20_3 = MTermR u1 (MTermR u0 (MTermT (read "x1")))

epropmt20_4 :: Metaterm
epropmt20_4 = MTermR u1 (MTermT (read "f3[1](X1)"))

epropc20_1 :: Constraint
epropc20_1 = Tcstr epropmt20_1 epropmt20_2

epropc20_2 :: Constraint
epropc20_2 = Tcstr epropmt20_3 epropmt20_4

epropcs20 = [epropc20_1,epropc20_2]

eproperrs20 :: [ConstraintFormErrors]
eproperrs20 = verify_all_unifier_constraints_wellformed epropsig epropmetavars epropus epropcs20

epropinst20 :: Enumeration (_,Maybe ([UnifierDescription],Instantiation))
epropinst20 = solve_unifier_constraints epropsig epropmetavars epropcs20 epropus

-- Example 21
epropmt21_1 :: Metaterm
epropmt21_1 = MTermR u0 (MTermT (read "X0"))

epropmt21_2 :: Metaterm
epropmt21_2 = MTermR u0 (MTermT (read "f3[1](x1)"))

epropmt21_3 :: Metaterm
epropmt21_3 = MTermR u1 (MTermR u0 (MTermT (read "X1")))

epropmt21_4 :: Metaterm
epropmt21_4 = MTermR u1 (MTermT (read "f3[1](x1)"))

epropc21_1 :: Constraint
epropc21_1 = Tcstr epropmt21_1 epropmt21_2

epropc21_2 :: Constraint
epropc21_2 = Tcstr epropmt21_3 epropmt21_4

epropcs21 = [epropc21_1,epropc21_2]

eproperrs21 :: [ConstraintFormErrors]
eproperrs21 = verify_all_unifier_constraints_wellformed epropsig epropmetavars epropus epropcs21

(eproprmvs21,(eproprinst21,epropscs21)) = all_simpl_cstr epropmetavars (idinst,epropcs21)

epropg21 = build_graph_from_constraints epropscs21

epropfs21 :: FullSolution
epropfs21 = (eproprmvs21,[],(eproprinst21,[]),epropg21)

epropres21 :: Enumeration (_,FullSolution)
epropres21 = enumerate_and_propagate_all epropsig epropfs21

epropinst21 :: Enumeration (_,Maybe ([UnifierDescription],Instantiation))
epropinst21 = solve_unifier_constraints epropsig epropmetavars epropcs21 epropus


epropcs21t = [Tcstr (MTermR u1 (MTermT (read "x1"))) (MTermR u1 (MTermF (read "f1[2]") [MTermT (read "x6"),MTermF (read "f1[2]") [MTermT (read "x6"),MTermT (read "x7")]]))]

(eproprmvs21t,(eproprinst21t,epropscs21t)) = all_simpl_cstr epropmetavars (idinst,epropcs21t)

epropg21t = build_graph_from_constraints epropscs21t

epropfs21t :: FullSolution
epropfs21t = set_all_solutions (eproprmvs21t,[],(eproprinst21t,[]),epropg21t) [(DMetaT mx0,Left (read "f1[2](x1,x0)")),(DRec u0 (DVar x1),Left (read "x6")),(DRec u0 (DVar x2),Left (read "x7")),(DRec u0 (DVar x0),Left (read "f1[2](x6,x7)"))]

epropres21t :: Enumeration (_,FullSolution)
epropres21t = enumerate_and_propagate_all epropsig epropfs21t


-- Example 22
epropml22_1 :: Metaliteral
epropml22_1 = MLitR u0 (MLitL (read "X0"))

epropml22_2 :: Metaliteral
epropml22_2 = MLitR u0 (MLitL (read "X1"))

epropml22_3 :: Metaliteral
epropml22_3 = MLitR u1 (MLitL (read "X0"))

epropml22_4 :: Metaliteral
epropml22_4 = MLitR u1 (MLitR u0 (MLitL (read "p1[2](x0,x1)")))

epropml22_5 :: Metaliteral
epropml22_5 = MLitR u2 (MLitR u1 (MLitL (read "X1")))

epropml22_6 :: Metaliteral
epropml22_6 = MLitR u2 (MLitL (read "p1[2](x2,x2)"))

epropc22_1 :: Constraint
epropc22_1 = Lcstr epropml22_1 epropml22_2

epropc22_2 :: Constraint
epropc22_2 = Lcstr epropml22_3 epropml22_4

epropc22_3 :: Constraint
epropc22_3 = Lcstr epropml22_5 epropml22_6

epropcs22 = [epropc22_1,epropc22_2,epropc22_3]

eproperrs22 :: [ConstraintFormErrors]
eproperrs22 = verify_all_unifier_constraints_wellformed epropsig epropmetavars epropus epropcs22

(eproprmvs22,(eproprinst22,epropscs22)) = all_simpl_cstr epropmetavars (idinst,epropcs22)

epropg22 = build_graph_from_constraints epropscs22

epropfs22 :: FullSolution
epropfs22 = (eproprmvs22,[],(eproprinst22,[]),epropg22)

epropres22 :: Enumeration (_,FullSolution)
epropres22 = enumerate_and_propagate_all epropsig epropfs22

epropinst22 :: Enumeration (_,Maybe ([UnifierDescription],Instantiation))
epropinst22 = solve_unifier_constraints epropsig epropmetavars epropcs22 epropus

-- Example 23
epropml23_1 :: Metaliteral
epropml23_1 = MLitR u0 (MLitL (read "X0"))

epropml23_2 :: Metaliteral
epropml23_2 = MLitR u0 (MLitL (read "X1"))

epropml23_3 :: Metaliteral
epropml23_3 = MLitR u1 (MLitL (read "X0"))

epropml23_4 :: Metaliteral
epropml23_4 = MLitR u1 (MLitR u0 (MLitL (read "p1[2](x0,x1)")))

epropc23_1 :: Constraint
epropc23_1 = Lcstr epropml23_1 epropml23_2

epropc23_2 :: Constraint
epropc23_2 = Lcstr epropml23_3 epropml23_4

epropcs23 = [epropc23_1,epropc23_2]

eproperrs23 :: [ConstraintFormErrors]
eproperrs23 = verify_all_unifier_constraints_wellformed epropsig epropmetavars epropus epropcs23

epropinst23 :: Enumeration (_,Maybe ([UnifierDescription],Instantiation))
epropinst23 = solve_unifier_constraints epropsig epropmetavars epropcs23 epropus

-- Example 24
epropml24_1 :: Metaliteral
epropml24_1 = MLitR u0 (MLitL (read "X0"))

epropml24_2 :: Metaliteral
epropml24_2 = MLitR u0 (MLitL (read "X1"))

epropml24_3 :: Metaliteral
epropml24_3 = MLitR u1 (MLitR u0 (MLitL (read "X0")))

epropml24_4 :: Metaliteral
epropml24_4 = MLitR u1 (MLitL (read "p1[2](x0,x1)"))

epropml24_5 :: Metaliteral
epropml24_5 = MLitR u2 (MLitR u0 (MLitL (read "X1")))

epropml24_6 :: Metaliteral
epropml24_6 = MLitR u2 (MLitL (read "p1[2](x0,x1)"))

epropc24_1 :: Constraint
epropc24_1 = Lcstr epropml24_1 epropml24_2

epropc24_2 :: Constraint
epropc24_2 = Lcstr epropml24_3 epropml24_4

epropc24_3 :: Constraint
epropc24_3 = Lcstr epropml24_5 epropml24_6

epropcs24 = [epropc24_1,epropc24_2,epropc24_3]

eproperrs24 :: [ConstraintFormErrors]
eproperrs24 = verify_all_unifier_constraints_wellformed epropsig epropmetavars epropus epropcs24

epropinst24 :: Enumeration (_,Maybe ([UnifierDescription],Instantiation))
epropinst24 = solve_unifier_constraints epropsig epropmetavars epropcs24 epropus

-- Example 25
epropml25_1 :: Metaliteral
epropml25_1 = MLitR u0 (MLitL (read "X0"))

epropml25_2 :: Metaliteral
epropml25_2 = MLitR u0 (MLitL (read "X1"))

epropml25_3 :: Metaliteral
epropml25_3 = MLitR u1 (MLitR u0 (MLitL (read "X0")))

epropml25_4 :: Metaliteral
epropml25_4 = MLitR u1 (MLitL (read "p1[2](x0,x1)"))

epropml25_5 :: Metaliteral
epropml25_5 = MLitR u2 (MLitR u0 (MLitL (read "X1")))

epropml25_6 :: Metaliteral
epropml25_6 = MLitR u2 (MLitL (read "p1[2](x1,x0)"))

epropc25_1 :: Constraint
epropc25_1 = Lcstr epropml25_1 epropml25_2

epropc25_2 :: Constraint
epropc25_2 = Lcstr epropml25_3 epropml25_4

epropc25_3 :: Constraint
epropc25_3 = Lcstr epropml25_5 epropml25_6

epropcs25 = [epropc25_1,epropc25_2,epropc25_3]

eproperrs25 :: [ConstraintFormErrors]
eproperrs25 = verify_all_unifier_constraints_wellformed epropsig epropmetavars epropus epropcs25

epropinst25 :: Enumeration (_,Maybe ([UnifierDescription],Instantiation))
epropinst25 = solve_unifier_constraints epropsig epropmetavars epropcs25 epropus

-- Example 26
epropml26_1 :: Metaliteral
epropml26_1 = MLitR u0 (MLitL (read "X0"))

epropml26_2 :: Metaliteral
epropml26_2 = MLitR u0 (MLitL (read "X1"))

epropml26_3 :: Metaliteral
epropml26_3 = MLitR u1 (MLitL (read "X0"))

epropml26_4 :: Metaliteral
epropml26_4 = MLitR u1 (MLitL (read "p1[2](x0,x1)"))

epropml26_5 :: Metaliteral
epropml26_5 = MLitR u2 (MLitL (read "X1"))

epropml26_6 :: Metaliteral
epropml26_6 = MLitR u2 (MLitL (read "p1[2](x0,x1)"))

epropc26_1 :: Constraint
epropc26_1 = Lcstr epropml26_1 epropml26_2

epropc26_2 :: Constraint
epropc26_2 = Lcstr epropml26_3 epropml26_4

epropc26_3 :: Constraint
epropc26_3 = Lcstr epropml26_5 epropml26_6

epropcs26 = [epropc26_1,epropc26_2,epropc26_3]

eproperrs26 :: [ConstraintFormErrors]
eproperrs26 = verify_all_unifier_constraints_wellformed epropsig epropmetavars epropus epropcs26

(eproprmvs26,(eproprinst26,epropscs26)) = all_simpl_cstr epropmetavars (idinst,epropcs26)

epropg26 = build_graph_from_constraints epropscs26

epropfs26 :: FullSolution
epropfs26 = (eproprmvs26,[],(eproprinst26,[]),epropg26)

epropres26 :: Enumeration (_,FullSolution)
epropres26 = enumerate_and_propagate_all epropsig epropfs26

epropinst26 :: Enumeration (_,Maybe ([UnifierDescription],Instantiation))
epropinst26 = solve_unifier_constraints epropsig epropmetavars epropcs26 epropus
