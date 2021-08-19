{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PartialTypeSignatures #-}
module Constraints where


-- Important note. Literals here actually are atoms (no negation). Bad wording...
import Data.Maybe
import qualified Data.Set as Set
import qualified Data.HashMap as Map
import qualified Data.List as List
--import qualified Data.Fix as Fix
import Data.Functor
import Data.Either

data Variable = Var Int deriving Eq
instance Show Variable where
	show (Var x) = "x" ++ (show x)
instance Read Variable where
	readsPrec _ ('x':xs) = (let r = (head (reads xs))
				in [(Var (fst r),(snd r))])

data Metavariable = Metavar Int deriving Eq
instance Show Metavariable where
	show (Metavar x) = "X" ++ (show x)
instance Read Metavariable where
	readsPrec _ ('X':xs) = (let r = (head (reads xs))
				in [(Metavar (fst r),(snd r))])

-- Fun constructor takes an int indicating the index of the function (f1, f2, f3...) and the arity of it.
data Function = Fun Int Int deriving Eq
instance Show Function where
	show (Fun x y) = "f" ++ (show x) ++ "[" ++ (show y) ++ "]"
read_arity :: String -> (Int,String)
read_arity ('[':xs) = (let r = (head (reads xs))
			in ((fst r),(tail (snd r))))

instance Read Function where 
	readsPrec _ ('f':xs) = (let r = (head (reads xs))
				in (let r2 = (read_arity (snd r))
					in [(Fun (fst r) (fst r2),(snd r2))]))									

arity :: Function -> Int
arity (Fun _ x) = x

data Term = TVar Variable | TMeta Metavariable | TFun Function [Term] deriving Eq
instance Show Term where
	show (TVar x) = show x
	show (TMeta x) = show x
	show (TFun x []) = (show x) ++ "()"
	show (TFun x (y:ys)) = (show x) ++ "(" ++ (foldl (\x -> \y -> x ++ "," ++ (show y)) (show y) ys) ++ ")"

read_term_list :: String -> ([Term],String)
read_term_list ('(':xs) = read_term_list xs
read_term_list (')':xs) = ([],xs)
read_term_list (',':xs) = read_term_list xs
read_term_list x = (let r = (head (reads x)::(Term,String))
			in (let r2 = read_term_list (snd r)
				in ((fst r):(fst r2),(snd r2))))

instance Read Term where
	readsPrec _ ('x':xs) = (let r = (head (reads ('x':xs))::(Variable,String))
				in [(TVar (fst r),(snd r))])
	readsPrec _ ('X':xs) = (let r = (head (reads ('X':xs))::(Metavariable,String))
				in [(TMeta (fst r),(snd r))])
	readsPrec _ ('f':xs) = (let r = (head (reads ('f':xs))::(Function,String))
				in (let r2 = read_term_list (snd r)
					in [(TFun (fst r) (fst r2),(snd r2))]))

data Predicate = Pred Int Int deriving Eq
instance Show Predicate where
	show (Pred x y) = "p" ++ (show x) ++ "[" ++ (show y) ++ "]"
instance Read Predicate where
	readsPrec _ ('p':xs) = (let r = (head (reads xs))
				in (let r2 = (read_arity (snd r))
					in [(Pred (fst r) (fst r2),(snd r2))]))									

pred_arity :: Predicate -> Int
pred_arity (Pred _ x) = x

data Literal = Lit Predicate [Term] | LitM Metavariable deriving Eq
instance Show Literal where
	show (Lit x []) = (show x) ++ "()"
	show (Lit x (y:ys)) = (show x) ++ "(" ++ (foldl (\x -> \y -> x ++ "," ++ (show y)) (show y) ys) ++ ")"
	show (LitM x) = (show x)
instance Read Literal where
	readsPrec _ ('p':xs) = (let r = (head (reads ('p':xs))::(Predicate,String))
				in (let r2 = read_term_list (snd r)
					in [(Lit (fst r) (fst r2),(snd r2))]))
	readsPrec _ ('X':xs) = (let r = (head (reads ('X':xs))::(Metavariable,String))
				in [(LitM (fst r),(snd r))])

-- The order of unifiers IS important, as it affects the algorithm
data Unifier = U Int | IdU deriving Eq
instance Show Unifier where
	show (U x) = "u" ++ (show x)
	show IdU = "id"
instance Read Unifier where
	readsPrec _ ('u':xs) = (let r = (head (reads xs))
				in [(U (fst r),(snd r))])
	readsPrec _ ('i':'d':xs) = [(IdU,xs)]

data Metaterm = MTermT Term | MTermR Unifier Metaterm | MTermF Function [Metaterm] deriving Eq
instance Show Metaterm where
	show (MTermT t) = (show t)
	show (MTermR u mt) = (show u) ++ " " ++ (show mt)
	show (MTermF f []) = (show f) ++ "()"
	show (MTermF f (t:ts)) = (show f) ++ "(" ++ (foldl (\x -> \y -> x ++ "," ++ (show y)) (show t) ts) ++ ")"

read_metaterm_list :: String -> ([Metaterm],String)
read_metaterm_list ('(':xs) = read_metaterm_list xs
read_metaterm_list (')':xs) = ([],xs)
read_metaterm_list (',':xs) = read_metaterm_list xs
read_metaterm_list x = (let r = (head (reads x)::(Metaterm,String))
			in (let r2 = read_metaterm_list (snd r)
				in ((fst r):(fst r2),(snd r2))))
	

-- We assume spaces between unifiers
instance Read Metaterm where
	readsPrec _ ('u':xs) = (let r = (head (reads ('u':xs)))
				in (let r2 = (head (reads (tail (snd r))))
					in [(MTermR (fst r) (fst r2),(snd r2))]))
	readsPrec _ ('f':xs) = (let r = (head (reads ('f':xs)))
				in (let r2 = read_metaterm_list (snd r)
					in [(MTermF (fst r) (fst r2),(snd r2))]))
	readsPrec _ xs = (let r = (head (reads xs))
				in [(MTermT (fst r),(snd r))])

data Metaliteral = MLitL Literal | MLitR Unifier Metaliteral | MLitP Predicate [Metaterm] deriving Eq

instance Show Metaliteral where
	show (MLitL l) = (show l)
	show (MLitR u ml) = (show u) ++ " " ++ (show ml)
	show (MLitP p []) = (show p) ++ "()"
	show (MLitP p (t:ts)) = (show p) ++ "(" ++ (foldl (\x -> \y -> x ++ "," ++ (show y)) (show t) ts) ++ ")"

instance Read Metaliteral where
	readsPrec _ ('u':xs) = (let r = (head (reads ('u':xs)))
				in (let r2 = (head (reads (tail (snd r))))
					in [(MLitR (fst r) (fst r2),(snd r2))]))
	readsPrec _ ('p':xs) = (let r = (head (reads ('p':xs)))
				in (let r2 = read_metaterm_list (snd r)
					in [(MLitP (fst r) (fst r2),(snd r2))]))
	readsPrec _ xs = (let r = (head (reads xs))
				in [(MLitL (fst r),(snd r))])


prepend_metaliteral :: [Unifier] -> Metaliteral -> Metaliteral
prepend_metaliteral [] ml = ml
prepend_metaliteral (u:us) ml = MLitR u (prepend_metaliteral us ml)

-- When a metaterm/metaliteral has no unifiers, we can un-lift it.
unlift_mterm :: Metaterm -> Term
unlift_mterm (MTermT t) = t
unlift_mterm (MTermF f mts) = TFun f (map unlift_mterm mts)

unlift_mlit :: Metaliteral -> Literal
unlift_mlit (MLitL l) = l
unlift_mlit (MLitP p mts) = Lit p (map unlift_mterm mts)

-- Normalize metaterms and metaliterals by making them of the form "u ml", using the identity if necessary.
-- Notice that these functions are *not* recursive.
norm_mterm :: Metaterm -> Metaterm
norm_mterm (MTermT t) = MTermR IdU (MTermT t)
norm_mterm (MTermF f l) = MTermR IdU (MTermF f l)
norm_mterm (MTermR u mt) = MTermR u mt

norm_mlit :: Metaliteral -> Metaliteral
norm_mlit (MLitL l) = MLitR IdU (MLitL l)
norm_mlit (MLitP p l) = MLitR IdU (MLitP p l)
norm_mlit (MLitR u ml) = MLitR u ml

-- Simplify meta literals by pushing unifiers inwards if possible
simpl_mterm :: Metaterm -> Metaterm
simpl_mterm (MTermR u (MTermT (TFun f ts))) = MTermF f (map (\t -> simpl_mterm (MTermR u (MTermT t))) ts)
simpl_mterm (MTermR u (MTermF f ts)) = MTermF f (map (\mt -> simpl_mterm (MTermR u mt)) ts)
simpl_mterm (MTermR u (MTermR v mt)) = simpl_mterm_norec (MTermR u (simpl_mterm (MTermR v mt)))
simpl_mterm x = x

simpl_mterm_norec :: Metaterm -> Metaterm
simpl_mterm_norec (MTermR u (MTermR v mt)) = MTermR u (MTermR v mt)
simpl_mterm_norec x = simpl_mterm x

simpl_mlit :: Metaliteral -> Metaliteral
simpl_mlit (MLitR u (MLitL (Lit p ts))) = MLitP p (map (\t -> simpl_mterm (MTermR u (MTermT t))) ts)
simpl_mlit (MLitR u (MLitP p ts)) = MLitP p (map (\mt -> simpl_mterm (MTermR u mt)) ts)
simpl_mlit (MLitR u (MLitR v ml)) = simpl_mlit_norec (MLitR u (simpl_mlit (MLitR v ml))) 
simpl_mlit x = x

simpl_mlit_norec :: Metaliteral -> Metaliteral
simpl_mlit_norec (MLitR u (MLitR v ml)) = MLitR u (MLitR v ml)
simpl_mlit_norec x = simpl_mlit x

-- Remove id unifiers
delid_mterm :: Metaterm -> Metaterm
delid_mterm (MTermT t) = MTermT t
delid_mterm (MTermR IdU mt) = mt
delid_mterm (MTermR u mt) = MTermR u (delid_mterm mt)
delid_mterm (MTermF f l) = MTermF f (map delid_mterm l)

delid_mlit :: Metaliteral -> Metaliteral
delid_mlit (MLitL l) = MLitL l
delid_mlit (MLitR IdU ml) = ml
delid_mlit (MLitR u ml) = MLitR u (delid_mlit ml)
delid_mlit (MLitP p l) = MLitP p (map delid_mterm l)

-- All simplifications on metaliterals and metaterms together
all_simpl_mterm :: Metaterm -> Metaterm
all_simpl_mterm mt = delid_mterm (simpl_mterm (norm_mterm mt))

all_simpl_mlit :: Metaliteral -> Metaliteral
all_simpl_mlit ml = delid_mlit (simpl_mlit (norm_mlit ml))


-- Introduce instantiations and meta-variable mappings
-- Keep in mind that Literal and Term may contain meta-variables, so this includes partial instantiations.

--type LitInstantiation = (Metavariable -> Literal)
--type TermInstantiation = (Metavariable -> Term)
type LitInstantiation = [(Metavariable,Literal)]
type TermInstantiation = [(Metavariable,Term)]

fun_from_litinst :: LitInstantiation -> Metavariable -> Literal
fun_from_litinst [] mv = LitM mv
fun_from_litinst ((mv1,l):mvs) mv2 | mv1 == mv2 = l
fun_from_litinst ((mv1,l):mvs) mv2 = fun_from_litinst mvs mv2

fun_from_terminst :: TermInstantiation -> Metavariable -> Term
fun_from_terminst [] mv = TMeta mv
fun_from_terminst ((mv1,t):mvs) mv2 | mv1 == mv2 = t
fun_from_terminst ((mv1,t):mvs) mv2 = fun_from_terminst mvs mv2

-- Identity instantiations
idinst_lit :: LitInstantiation
idinst_lit = []
--idinst_lit mv = LitM mv
idinst_term :: TermInstantiation
--idinst_term mv = TMeta mv
idinst_term = []
idinst :: Instantiation
idinst = (idinst_lit, idinst_term)

list_contained_no_order :: Eq t => [t] -> [t] -> Bool
list_contained_no_order [] _ = True
list_contained_no_order (x:xs) l = (elem x l) && (list_contained_no_order xs l)

list_eq_no_order :: Eq t => [t] -> [t] -> Bool
list_eq_no_order l1 l2 = (list_contained_no_order l1 l2) && (list_contained_no_order l2 l1)

eq_litinst :: LitInstantiation -> LitInstantiation -> Bool
eq_litinst = list_eq_no_order

eq_terminst :: TermInstantiation -> TermInstantiation -> Bool
eq_terminst = list_eq_no_order

type Instantiation = (LitInstantiation,TermInstantiation)

eq_inst :: Instantiation -> Instantiation -> Bool
eq_inst (li1,ti1) (li2,ti2) = (eq_litinst li1 li2) && (eq_terminst ti1 ti2)

eq_inst_mvs :: [Metavariable] -> Instantiation -> Instantiation -> Bool
eq_inst_mvs [] _ _ = True
eq_inst_mvs (mv:mvs) i1 i2 = ((apply_inst i1 mv) == (apply_inst i2 mv)) && (eq_inst_mvs mvs i1 i2)

has_inst_value :: Instantiation -> Metavariable -> Bool
--has_inst_value i mv = (((fst i) mv /= (LitM mv)) || ((snd i) mv /= (TMeta mv)))
has_inst_value (li,ti) mv = (has_inst_value_lit li mv) || (has_inst_value_term ti mv)

has_inst_value_lit :: LitInstantiation -> Metavariable -> Bool
has_inst_value_lit [] mv = False
has_inst_value_lit ((mv1,(LitM mv2)):mvs) mv3 | mv1 == mv2 = has_inst_value_lit mvs mv3
has_inst_value_lit ((mv1,l):mvs) mv2 | mv1 == mv2 = True
has_inst_value_lit ((mv1,l):mvs) mv2 = has_inst_value_lit mvs mv2

has_inst_value_term :: TermInstantiation -> Metavariable -> Bool
has_inst_value_term [] mv = False
has_inst_value_term ((mv1,(TMeta mv2)):mvs) mv3 | mv1 == mv2 = has_inst_value_term mvs mv3
has_inst_value_term ((mv1,t):mvs) mv2 | mv1 == mv2 = True
has_inst_value_term ((mv1,t):mvs) mv2 = has_inst_value_term mvs mv2

show_inst_mv :: Instantiation -> Metavariable -> String
show_inst_mv i mv | (fun_from_litinst (fst i) mv /= (LitM mv)) = (show mv) ++ " -> " ++ (show (fun_from_litinst (fst i) mv))
show_inst_mv i mv | (fun_from_terminst (snd i) mv /= (TMeta mv)) = (show mv) ++ " -> " ++ (show (fun_from_terminst (snd i) mv))
show_inst_mv i mv = (show mv) ++ " -> " ++ (show mv)

show_inst :: Instantiation -> [Metavariable] -> String
show_inst i [] = "{}"
show_inst i (x:xs) = "{" ++ (foldl (\s -> \mv -> s ++ "," ++ (show_inst_mv i mv)) (show_inst_mv i x) xs) ++ "}"
--show_inst (li,ti) _ = case mvs of {[] -> "{}"; (x:xs) -> "{" ++ (foldl (\s -> \mv -> s ++ "," ++ (show_inst_mv (li,ti) mv)) (show_inst_mv (li,ti) x) xs) ++ "}"} where mvs = (map fst li) ++ (map fst ti)


apply_inst :: Instantiation -> Metavariable -> Maybe (Either Term Literal)
apply_inst (li,ti) mv | lv /= (LitM mv) = Just (Right lv) where lv = fun_from_litinst li mv
apply_inst (li,ti) mv | tv /= (TMeta mv) = Just (Left tv) where tv = fun_from_terminst ti mv
apply_inst (li,ti) mv = Nothing

contains_variable :: Variable -> Maybe (Either Term Literal) -> Bool
contains_variable _ Nothing = False
contains_variable x (Just (Left t)) = contains_variable_t x t
contains_variable x (Just (Right l)) = contains_variable_l x l

contains_variable_t :: Variable -> Term -> Bool
contains_variable_t y (TVar x) | x == y = True
contains_variable_t y (TVar x) = False
contains_variable_t y (TMeta _) = False
contains_variable_t y (TFun f ts) = any (contains_variable_t y) ts

contains_variable_l :: Variable -> Literal -> Bool
contains_variable_l y (LitM _) = False
contains_variable_l y (Lit p ts) = any (contains_variable_t y) ts


apply_inst_term :: Instantiation -> Term -> Term
apply_inst_term i (TVar v) = TVar v
apply_inst_term i (TMeta mv) = fun_from_terminst (snd i) mv
apply_inst_term i (TFun f l) = TFun f (map (apply_inst_term i) l)

apply_inst_lit :: Instantiation -> Literal -> Literal
apply_inst_lit i (LitM mv) = fun_from_litinst (fst i) mv
apply_inst_lit i (Lit p l) = Lit p (map (apply_inst_term i) l)

apply_inst_mterm :: Instantiation -> Metaterm -> Metaterm
apply_inst_mterm i (MTermT t) = MTermT (apply_inst_term i t)
apply_inst_mterm i (MTermR u mt) = MTermR u (apply_inst_mterm i mt)
apply_inst_mterm i (MTermF f l) = MTermF f (map (apply_inst_mterm i) l)

apply_inst_mlit :: Instantiation -> Metaliteral -> Metaliteral
apply_inst_mlit i (MLitL l) = MLitL (apply_inst_lit i l)
apply_inst_mlit i (MLitR u ml) = MLitR u (apply_inst_mlit i ml)
apply_inst_mlit i (MLitP p l) = MLitP p (map (apply_inst_mterm i) l)

clean_dups_inst :: Instantiation -> Instantiation
clean_dups_inst (li,ti) = (clean_dups_inst_lit [] li,clean_dups_inst_term [] ti)

clean_dups_inst_lit :: [(Metavariable,Literal)] -> LitInstantiation -> LitInstantiation
clean_dups_inst_lit mvs [] = []
clean_dups_inst_lit mvs ((mv,l):ls) | elem (mv,l) mvs = clean_dups_inst_lit mvs ls
clean_dups_inst_lit mvs ((mv1,(LitM mv2)):ls) | mv1 == mv2 = clean_dups_inst_lit mvs ls
clean_dups_inst_lit mvs ((mv,l):ls) = (mv,l):(clean_dups_inst_lit ((mv,l):mvs) ls)

clean_dups_inst_term :: [(Metavariable,Term)] -> TermInstantiation -> TermInstantiation
clean_dups_inst_term mvs [] = []
clean_dups_inst_term mvs ((mv,t):ts) | elem (mv,t) mvs = clean_dups_inst_term mvs ts
clean_dups_inst_term mvs ((mv1,(TMeta mv2)):ts) | mv1 == mv2 = clean_dups_inst_term mvs ts
clean_dups_inst_term mvs ((mv,t):ts) = (mv,t):(clean_dups_inst_term ((mv,t):mvs) ts)

-- As usual, read from right to left. The first instantiation applied is the second parameter.
compose_inst :: Instantiation -> Instantiation -> Instantiation
--compose_inst i j = (\mv -> apply_inst_lit i ((fst j) mv), \mv -> apply_inst_term i ((snd j) mv))
compose_inst i (lj,tj) = clean_dups_inst (compose_inst_lit i lj,compose_inst_term i tj)

compose_inst_lit :: Instantiation -> LitInstantiation -> LitInstantiation
compose_inst_lit (li,ti) [] = li
compose_inst_lit i ((mv,l):mvs) = ((mv,apply_inst_lit i l):(compose_inst_lit i mvs))

compose_inst_term :: Instantiation -> TermInstantiation -> TermInstantiation
compose_inst_term (li,ti) [] = ti
compose_inst_term i ((mv,t):mvs) = ((mv,apply_inst_term i t):(compose_inst_term i mvs)) 

compose_insts :: [Instantiation] -> Instantiation
compose_insts l = foldr compose_inst (idinst_lit,idinst_term) l

build_inst :: Metavariable -> Either Term Literal -> Instantiation
--build_inst mv (Left t) = (idinst_lit,(\mx -> if (mx == mv) then t else (TMeta mx)))
build_inst mv (Left t) = (idinst_lit,[(mv,t)])
--build_inst mv (Right l) = (\mx -> if (mx == mv) then l else (LitM mx),idinst_term)
build_inst mv (Right l) = ([(mv,l)],idinst_term)

build_inst_from_list :: [(Metavariable,Either Term Literal)] -> Instantiation
build_inst_from_list [] = (idinst_lit,idinst_term)
build_inst_from_list ((mv,Left t):mvs) = (prevli,((mv,t):prevti)) where (prevli,prevti) = build_inst_from_list mvs
build_inst_from_list ((mv,Right l):mvs) = (((mv,l):prevli),prevti) where (prevli,prevti) = build_inst_from_list mvs

set_instantiation_fs :: FullSolution -> Metavariable -> Either Term Literal -> FullSolution
set_instantiation_fs (mvs,eqs,(inst,cs),(g,sol,ueqs)) mv v = (mvs,eqs,(compose_inst (build_inst mv v) inst,cs),(g,sol,ueqs))
--set_instantiation_fs (mvs,eqs,((li,ti),cs),(g,sol,ueqs)) mv (Left t) = (mvs,eqs,((li,(mv,t):ti),cs),(g,sol,ueqs))
--set_instantiation_fs (mvs,eqs,((li,ti),cs),(g,sol,ueqs)) mv (Right l) = (mvs,eqs,(((mv,l):li,ti),cs),(g,sol,ueqs))

set_instantiation :: Instantiation -> Metavariable -> Either Term Literal -> Instantiation
set_instantiation inst mv v = compose_inst (build_inst mv v) inst
--set_instantiation (li,ti) mv (Left t) = (li,(mv,t):ti)
--set_instantiation (li,ti) mv (Right l) = ((mv,l):li,ti)

-- Make the instantiation single, if possible, by performing unification at the meta-level.
most_instantiated_all :: Instantiation -> Maybe Instantiation
most_instantiated_all inst = if (any (isNothing . snd) results) then Nothing else (Just (build_inst_from_list (map (\(mv,v) -> (mv,fromJust v)) results))) where sorted = all_insts_permv inst; results = map (\(mv,vs) -> (mv,most_instantiated_all_permv vs)) sorted

all_insts_permv :: Instantiation -> [(Metavariable, [Either Term Literal])]
all_insts_permv (li,ti) = all_insts_permv_rec li ti

all_insts_permv_rec :: LitInstantiation -> TermInstantiation -> [(Metavariable, [Either Term Literal])]
all_insts_permv_rec [] [] = []
all_insts_permv_rec [] ((mv,t):ts) = ((mv,(Left t):prev_mv):prev) where (prev,prev_mv) = all_insts_permv_rec_findprev (all_insts_permv_rec [] ts) mv
all_insts_permv_rec ((mv,l):ls) ti = ((mv,(Right l):prev_mv):prev) where (prev,prev_mv) = all_insts_permv_rec_findprev (all_insts_permv_rec ls ti) mv

all_insts_permv_rec_findprev :: [(Metavariable, [Either Term Literal])] -> Metavariable -> ([(Metavariable, [Either Term Literal])],[Either Term Literal])
all_insts_permv_rec_findprev [] _ = ([],[])
all_insts_permv_rec_findprev ((mv1,l):mvs) mv2 | mv1 == mv2 = (mvs,l)
all_insts_permv_rec_findprev ((mv1,l):mvs) mv2 = ((mv1,l):prev,prev_mv) where (prev,prev_mv) = all_insts_permv_rec_findprev mvs mv2

most_instantiated_all_permv :: [Either Term Literal] -> Maybe (Either Term Literal)
-- This case should never happen. Leave it unexpressed to signal the bad bug.
-- Another option would be to use the plain meta-variable as the initial value, but while more elegant, it is a lot less efficient and more bug-prone.
--most_instantiated_all_permv [] = Nothing
most_instantiated_all_permv (x:xs) = foldr most_instantiated_mbs (Just x) (map Just xs)

most_instantiated_mbs :: Maybe (Either Term Literal) -> Maybe (Either Term Literal) -> Maybe (Either Term Literal)
most_instantiated_mbs x y = demaybize (maybe_apply_2 most_instantiated x y)
-- most_instantiated :: Either Term Literal -> Either Term Literal -> Maybe (Either Term Literal)

data Constraint = Tcstr Metaterm Metaterm | Lcstr Metaliteral Metaliteral | Unsatisfiable deriving Eq
instance Show Constraint where
	show (Tcstr mt1 mt2) = (show mt1) ++ " = " ++ (show mt2)
	show (Lcstr ml1 ml2) = (show ml1) ++ " = " ++ (show ml2)
	show Unsatisfiable = "Unsatisfiable"

-- This is the type of a solution. 
-- We initially build a solution by providing no instantiation and a set of constraints. Then, we look for a *set of* solutions which, disjunctively joined, is equivalent; and such that none of them have constraints.
type UnifSolution = (Instantiation,[Constraint])
show_soln :: UnifSolution -> [Metavariable] -> String
show_soln (i,cs) l = (show_inst i l) ++ " || " ++ (show cs)

-- Sometimes we have a dependent like uC, where u is a unifier and C a meta-variable, and we wish to enumerate over it.
-- Instead of enumerating over u, we create a new meta-variable B = uC, and enumerate over B, and then calculate C as C = u-1 B (which involves enumeration).
-- In a full solution, we save these as meta-variable equations, in a very strict format, always of the form B = uC, for some meta-variables B and C and unifier u.
-- From this we can calculate the "level" of a meta-variable, and therefore what it can be instantiated to, and also build the final instantiation for C once we have an
-- instantiation for B.

data MetavariableEquation = MetaEq Metavariable Unifier Metavariable

instance Show MetavariableEquation where
	show (MetaEq mv1 u mv2) = (show mv1) ++ " = " ++ (show u) ++ " " ++ (show mv2)

show_mveqs :: [MetavariableEquation] -> String
show_mveqs [] = ""
show_mveqs (eq:eqs) = (show eq) ++ ", " ++ (show_mveqs eqs)

type FullSolution = ([Metavariable],[MetavariableEquation],UnifSolution,PartiallySolvedDGraph)
--instance Show FullSolution where
--	show (mvs,soln,(g,gsol)) = (show_soln soln mvs) ++ "\n" ++ (show  g)
full_soln_str :: FullSolution -> String
full_soln_str (mvs,eqs,soln,(g,gsol,ueqs)) = (show_soln soln mvs) ++ "\nwhere... \n" ++ (show_mveqs eqs) ++ "\n" ++ "Dependency graph: \n" ++ (show g) ++ "\nwhere... \n" ++ (show ueqs) ++ "\nand... \n" ++ (show_dgsol gsol) ++ "\n"

show_full_soln :: FullSolution -> IO ()
show_full_soln fs = putStr (full_soln_str fs)

apply_inst_fs :: FullSolution -> Metavariable -> Either Term Literal
apply_inst_fs (_,_,(i,_),_) mv = case (apply_inst i mv) of {Just x -> x; Nothing -> Left (TMeta mv)}

-- Simplify constraints
simpl_sides_cstr :: Constraint -> Constraint
simpl_sides_cstr Unsatisfiable = Unsatisfiable
simpl_sides_cstr (Lcstr ml1 ml2) = Lcstr (all_simpl_mlit ml1) (all_simpl_mlit ml2)
simpl_sides_cstr (Tcstr mt1 mt2) = Tcstr (all_simpl_mterm mt1) (all_simpl_mterm mt2)

apply_inst_cstr :: Instantiation -> Constraint -> Constraint
apply_inst_cstr i Unsatisfiable = Unsatisfiable
apply_inst_cstr i (Lcstr ml1 ml2) = Lcstr (apply_inst_mlit i ml1) (apply_inst_mlit i ml2)
apply_inst_cstr i (Tcstr mt1 mt2) = Tcstr (apply_inst_mterm i mt1) (apply_inst_mterm i mt2)

-- Helper functions to verify if a meta-literal or a meta-term correspond to u X for a (possibly composition of) unifier(s) u and a meta-variable X
is_metavar_lit :: Metaliteral -> Maybe (Metavariable, [Unifier])
is_metavar_lit (MLitP _ _) = Nothing
is_metavar_lit (MLitL (LitM x)) = Just (x, [])
is_metavar_lit (MLitL (Lit _ _)) = Nothing
is_metavar_lit (MLitR u ml) = case (is_metavar_lit ml) of {Nothing -> Nothing; Just (mv, l) -> Just (mv, u:l)}

is_metavar_term :: Metaterm -> Maybe (Metavariable, [Unifier])
is_metavar_term (MTermF _ _) = Nothing
is_metavar_term (MTermT (TMeta x)) = Just (x, [])
is_metavar_term (MTermT (TVar _)) = Nothing
is_metavar_term (MTermT (TFun _ _)) = Nothing
is_metavar_term (MTermR u mt) = case (is_metavar_term mt) of {Nothing -> Nothing; Just(mv, l) -> Just (mv, u:l)}

is_predicate_lit :: Metaliteral -> Maybe Predicate
is_predicate_lit (MLitP p _) = Just p
is_predicate_lit (MLitL (LitM _)) = Nothing
is_predicate_lit (MLitL (Lit p _)) = Just p
is_predicate_lit (MLitR u ml) = is_predicate_lit ml

-- IMPORTANT: Need to reverse the output unifiers of is_metavar_lit and is_metavar_term to apply this function properly.
build_metaliteral :: [Unifier] -> Metaliteral -> Metaliteral
build_metaliteral [] ml = ml
build_metaliteral (u:us) ml = build_metaliteral us (MLitR u ml)

build_metaterm :: [Unifier] -> Metaterm -> Metaterm
build_metaterm [] mt = mt
build_metaterm (u:us) mt = build_metaterm us (MTermR u mt)

new_metavar :: [Metavariable] -> Metavariable
new_metavar [] = Metavar 1
new_metavar ((Metavar n):xs) = if (m > n) then Metavar m else Metavar (n + 1) where m = case (new_metavar xs) of {Metavar x -> x}

new_metavars :: [Metavariable] -> [a] -> [Metavariable]
new_metavars l [] = []
new_metavars l (_:xs) = (mv:(new_metavars (mv:l) xs)) where mv = new_metavar l

add_metavars :: [Metavariable] -> [a] -> ([Metavariable],[Metavariable])
add_metavars l1 l2 = (l1++r,r) where r = new_metavars l1 l2

get_metavars_term :: Term -> [Metavariable]
get_metavars_term (TVar _) = []
get_metavars_term (TFun _ ts) = foldr List.union [] (map get_metavars_term ts)
get_metavars_term (TMeta mv) = [mv]

get_metavars_lit :: Literal -> [Metavariable]
get_metavars_lit (Lit _ ts) = foldr List.union [] (map get_metavars_term ts)
get_metavars_lit (LitM mv) = [mv]

get_metavars_mterm :: Metaterm -> [Metavariable]
get_metavars_mterm (MTermT t) = get_metavars_term t
get_metavars_mterm (MTermF f mts) = foldr List.union [] (map get_metavars_mterm mts)
get_metavars_mterm (MTermR u mt) = get_metavars_mterm mt

get_metavars_mlit :: Metaliteral -> [Metavariable]
get_metavars_mlit (MLitL l) = get_metavars_lit l
get_metavars_mlit (MLitP p mts) = foldr List.union [] (map get_metavars_mterm mts)
get_metavars_mlit (MLitR u ml) = get_metavars_mlit ml


-- We use numbers instead of using lists all along because while we need to consider having lots of variables, in practice most of them will not be used
-- (don't need to calculate all previous variables to calculate the next one).
-- This implies, however, that the variables are used adequately: Use 0...n-1 for the base level, n...2n-1 for the next level, 2n...4n-1 for the next level, etc.

-- First parameter is number of base variables.
get_first_image_varnum :: Int -> Int -> Int
get_first_image_varnum n m | m < n = m+n
get_first_image_varnum n m = get_first_image_varnum (2*n) m 

get_num_vars :: Int -> Int -> Int
get_num_vars n 0 = n
get_num_vars n i = 2*(get_num_vars n (i-1))

-- First parameter is number of base variables. Second parameter is unifier.
get_image_varnum :: Int -> Int -> Int -> Int
get_image_varnum n u m = (get_num_vars n u) + m

get_preimage_varnum :: Int -> Int -> Int -> Int
get_preimage_varnum n u m = m - (get_num_vars n u)

-- This is basically a logarithm.
get_base_level_varnum :: Int -> Int -> Int
get_base_level_varnum n m | m < n = 0
get_base_level_varnum n m = (get_base_level_varnum (2*n) m)+1

-- Base variables, level, variable.
is_in_domain_num :: Int -> Int -> Int -> Bool
is_in_domain_num n u m = (get_base_level_varnum n m) <= u

is_in_range_num :: Int -> Int -> Int -> Bool
is_in_range_num n u m = b <= u+1 && b > u where b = get_base_level_varnum n m

get_domain_vars :: Int -> Unifier -> [Variable]
get_domain_vars n (U l) = map (\x -> Var x) [0..m-1] where m = get_num_vars n l

get_range_vars :: Int -> Unifier -> [Variable]
get_range_vars n (U l) = map (\x -> Var x) [m..(2*m)-1] where m = get_num_vars n l

is_in_domain :: Int -> Unifier -> Variable -> Bool
is_in_domain n (U u) (Var m) = is_in_domain_num n u m

is_in_range :: Int -> Unifier -> Variable -> Bool
is_in_range n (U u) (Var m) = is_in_range_num n u m

-- First parameter is number of base variables. Second parameter is unifier.
get_image_var :: Int -> Unifier -> Variable -> Variable
get_image_var n (U u) (Var m) = Var (get_image_varnum n u m)

get_preimage_var :: Int -> Unifier -> Variable -> Variable
get_preimage_var n (U u) (Var m) = Var (get_preimage_varnum n u m)



-- In this function we assume that we have already simplified terms and literals. This should mean that any meta-literal or meta-term of the form MLitL should correspond to a meta-variable,
-- and any of the form MTermT should correspond to a meta-variable or an object-level variable.
-- The simplification functions for literals and terms ensure this.
-- It returns a set of new constraints and an instantiation to compose with the previously existing one.
-- The boolean indicates whether new constraints were generated.
simpl_cstr :: [Metavariable] -> Constraint -> (Bool, [Metavariable], (Instantiation, [Constraint]))
simpl_cstr mvs (Lcstr (MLitP p mt1) (MLitP q mt2)) | p == q = (True, mvs, (idinst, (map (\pair -> Tcstr (fst pair) (snd pair)) (zip mt1 mt2))))
simpl_cstr mvs (Lcstr (MLitP p mt1) (MLitP q mt2)) = (True, mvs, (idinst, [Unsatisfiable]))
simpl_cstr mvs (Lcstr (MLitP p mt) ml) | isJust (mmv) = 	(True, total_mvs, (
								(
									([(Metavar m,Lit p (map TMeta new_mvs))],
									idinst_term),
								(map (\pair -> Tcstr (fst pair) (snd pair)) (zip (map (\mv -> build_metaterm us (MTermT (TMeta mv))) new_mvs) mt))) 
							)) where mmv = is_metavar_lit ml ; m = case mmv of {Just (Metavar x,_) -> x} ; us = case mmv of {Just (_,x) -> reverse x} ; new_mvs = new_metavars mvs mt; total_mvs = mvs ++ new_mvs
simpl_cstr mvs (Lcstr ml (MLitP p mt)) = simpl_cstr mvs (Lcstr (MLitP p mt) ml)
simpl_cstr mvs (Tcstr (MTermF f mt1) (MTermF g mt2)) | f == g = (True, mvs, (idinst, (map (\pair -> Tcstr (fst pair) (snd pair)) (zip mt1 mt2))))
simpl_cstr mvs (Tcstr (MTermF f mt1) (MTermF g mt2)) = (True, mvs, (idinst, [Unsatisfiable]))
simpl_cstr mvs x = (False, mvs, (idinst, [x]))

all_simpl_cstr :: [Metavariable] -> UnifSolution -> ([Metavariable],UnifSolution)
all_simpl_cstr mvs (i,cs) = case (all_simpl_cstr_rec mvs i (map (\c -> (True,simpl_sides_cstr c)) cs)) of (rmvs,ri,rcs) -> (rmvs,(ri,(map snd rcs)))

all_simpl_cstr_rec :: [Metavariable] -> Instantiation -> [(Bool,Constraint)] -> ([Metavariable],Instantiation,[(Bool,Constraint)])
all_simpl_cstr_rec mvs i cs = case (all_simpl_cstr_step mvs i cs) of {(True,rmvs,ri,rcs) -> all_simpl_cstr_rec rmvs ri rcs ; (False,rmvs,ri,rcs) -> (rmvs,ri,rcs)}

-- Receives a set of used meta-variables, an instantiation, and constraints marked whether they should be simplified or they have already been simplified, and returns an equivalent set after one
-- simplification, plus a boolean indicating whether more steps are necessary.
all_simpl_cstr_step :: [Metavariable] -> Instantiation -> [(Bool,Constraint)] -> (Bool,[Metavariable],Instantiation,[(Bool,Constraint)])
all_simpl_cstr_step mvs i [] = (False,mvs,i,[])
all_simpl_cstr_step mvs i ((True,Unsatisfiable):_) = (False,mvs,i,[(False,Unsatisfiable)])
all_simpl_cstr_step mvs i ((True,c):cs) = case (simpl_cstr mvs c) of (bool, total_mvs, (j, new_cs)) -> (True,total_mvs, compose_inst j i, (map (all_simpl_cstr_step_helper j) cs) ++ (map (\c -> (bool,simpl_sides_cstr c)) new_cs))
all_simpl_cstr_step mvs i ((False,c):cs) = case (all_simpl_cstr_step mvs i cs) of (r,rmvs,ri,rcs) -> (r,rmvs, ri, (False,c):rcs)

all_simpl_cstr_step_helper :: Instantiation -> (Bool,Constraint) -> (Bool,Constraint)
all_simpl_cstr_step_helper j (b,c) = (b || (c /= nc),nc) where nc = simpl_sides_cstr (apply_inst_cstr j c)

-- Dependency graphs

type Substitution = (Variable -> Term)
apply_subst :: Substitution -> Term -> Term
apply_subst s (TVar v) = s v
apply_subst s (TFun f l) = TFun f (map (apply_subst s) l)
apply_subst s (TMeta m) = TMeta m

apply_subst_lit :: Substitution -> Literal -> Literal
apply_subst_lit s (Lit p ts) = Lit p (map (apply_subst s) ts)
apply_subst_lit s (LitM m) = LitM m

apply_subst_tlit :: Substitution -> Either Term Literal -> Either Term Literal
apply_subst_tlit s (Left t) = Left (apply_subst s t)
apply_subst_tlit s (Right l) = Right (apply_subst_lit s l)

new_var :: [Variable] -> Variable
new_var [] = Var 1
new_var ((Var n):xs) = if (m > n) then Var m else Var (n + 1) where m = case (new_var xs) of {Var x -> x}

new_vars :: [Variable] -> [a] -> [Variable]
new_vars l [] = []
new_vars l (_:xs) = (v:(new_vars (v:l) xs)) where v = new_var l

add_vars :: [Variable] -> [a] -> ([Variable],[Variable])
add_vars l1 l2 = (l1++r,r) where r = new_vars l1 l2

-- Lists should have the same length, and the variable should be in the first list.
get_next_level_var :: [Variable] -> [Variable] -> Variable -> Variable
get_next_level_var (v1:r1) (v2:r2) v | v1 == v = v2
get_next_level_var (v1:r1) (v2:r2) v = get_next_level_var r1 r2 v

-- Creates new variables for the next level, and gives the default mapping between them.
next_level_vars :: [Variable] -> (Variable -> Variable)
next_level_vars l v = get_next_level_var l (new_vars l l) v

data UnifierValue = UV Variable Term deriving Eq
instance Show UnifierValue where
	show (UV v t) = (show v) ++ " -> " ++ (show t)

type UnifierDescription = [UnifierValue]

eq_unifier :: UnifierDescription -> UnifierDescription -> Bool
eq_unifier = list_eq_no_order

-- We avoid duplicates here, as this should not be called too often.
-- It is the dumb way to check duplicates, with no hashes, but "hey man, I'm too tired for this".
vars_in_unif_desc :: UnifierDescription -> [Variable]
vars_in_unif_desc [] = []
vars_in_unif_desc ((UV v _):ud) = if (elem v rec) then rec else (v:rec) where rec = vars_in_unif_desc ud

-- This is a performance monster, that is why we leave it commented. DO NOT USE IT!

--complete_unif_description :: [Variable] -> (Variable -> Variable) -> UnifierDescription -> UnifierDescription
--complete_unif_description vs f ud = foldl (\lud -> \lv -> complete_unif_description_helper lv (f lv) lud) ud vs

--complete_unif_description_helper :: Variable -> Variable -> UnifierDescription -> UnifierDescription
--complete_unif_description_helper v fv [] = [UV v (TVar fv)]
--complete_unif_description_helper v1 _ ((UV v2 (TVar fv)):ud) | v1 == v2 = ((UV v2 (TVar fv)):ud)
--complete_unif_description_helper v1 fv (udh:ud) = udh:(complete_unif_description_helper v1 fv ud)


-- Receives a set of variables for the substitution, the canonical new variables for those, and a set of unifier values,
-- and returns a substitution.
obtain_substitution :: Int -> Unifier ->  UnifierDescription -> Substitution
obtain_substitution nvars u [] v = TVar (get_image_var nvars u v)
obtain_substitution nvars u ((UV v1 t):uvs) v2 | v1 == v2 = t
obtain_substitution nvars u ((UV v1 t):uvs) v2 | v1 /= v2 = obtain_substitution nvars u uvs v2


-- This is under the last unifier. If there are any remaining unifiers, we throw a non-exhaustive exception, to flag this up.
apply_subst_mterm :: Substitution -> Metaterm -> Metaterm
apply_subst_mterm subst (MTermT t) = MTermT (apply_subst subst t)
apply_subst_mterm subst (MTermF f mts) = MTermF f (map (apply_subst_mterm subst) mts)
--apply_subst_mterm subst (MTermR u mt) = MTermR u mt

apply_subst_mlit :: Substitution -> Metaliteral -> Metaliteral
apply_subst_mlit subst (MLitL l) = MLitL (apply_subst_lit subst l)
apply_subst_mlit subst (MLitP p mts) = MLitP p (map (apply_subst_mterm subst) mts)
--apply_subst_mlit subst (MLitR u ml) = MLitR u ml

-- The substitutions need to be applied in order, the first unifier first. This is essential.
apply_substitution_mterm :: Int -> Unifier -> UnifierDescription -> Metaterm -> Metaterm
apply_substitution_mterm nvars u ud (MTermT t) = MTermT t
apply_substitution_mterm nvars u ud (MTermF f mts) = MTermF f (map (apply_substitution_mterm nvars u ud) mts)
apply_substitution_mterm nvars u ud (MTermR v mt) | u == v = apply_subst_mterm (obtain_substitution nvars u ud) mt
apply_substitution_mterm nvars u ud (MTermR v mt) = MTermR v (apply_substitution_mterm nvars u ud mt)

apply_substitution_mlit :: Int -> Unifier -> UnifierDescription -> Metaliteral -> Metaliteral
apply_substitution_mlit nvars u ud (MLitL l) = MLitL l
apply_substitution_mlit nvars u ud (MLitP p mts) = MLitP p (map (apply_substitution_mterm nvars u ud) mts)
apply_substitution_mlit nvars u ud (MLitR v ml) | u == v = apply_subst_mlit (obtain_substitution nvars u ud) ml
apply_substitution_mlit nvars u ud (MLitR v ml) = MLitR v (apply_substitution_mlit nvars u ud ml)

data Dependent = DVar Variable | DMetaT Metavariable | DMetaL Metavariable | DRec Unifier Dependent deriving Eq
metaterm_from_depnode :: Dependent -> Metaterm
metaterm_from_depnode (DVar x) = (MTermT (TVar x))
metaterm_from_depnode (DMetaT x) = (MTermT (TMeta x))
metaterm_from_depnode (DRec u n) = (MTermR u (metaterm_from_depnode n))

-- This only works if the metaterm is in normal form (and therefore has all functions outside)
depnode_from_metaterm :: Metaterm -> Maybe Dependent
depnode_from_metaterm (MTermT (TVar x)) = Just (DVar x)
depnode_from_metaterm (MTermT (TMeta mx)) = Just (DMetaT mx)
depnode_from_metaterm (MTermT _) = Nothing
depnode_from_metaterm (MTermF _ _) = Nothing
depnode_from_metaterm (MTermR u mt) = maybe_apply (\d -> DRec u d) (depnode_from_metaterm mt)

metalit_from_depnode :: Dependent -> Metaliteral
-- Purposely not defined for variables.
metalit_from_depnode (DMetaL x) = (MLitL (LitM x))
metalit_from_depnode (DRec u n) = (MLitR u (metalit_from_depnode n))

depnode_from_metalit :: Metaliteral -> Maybe Dependent
depnode_from_metalit (MLitL (LitM mx)) = Just (DMetaL mx)
depnode_from_metalit (MLitL _) = Nothing
depnode_from_metalit (MLitP _ _) = Nothing
depnode_from_metalit (MLitR u ml) = maybe_apply (\d -> DRec u d) (depnode_from_metalit ml)

-- Only defined when the dependent has no unifiers
term_from_dependent :: Dependent -> Term
term_from_dependent (DVar v) = TVar v
term_from_dependent (DMetaT mv) = TMeta mv

lit_from_dependent :: Dependent -> Literal
lit_from_dependent (DMetaL mv) = LitM mv

has_unifier :: Dependent -> Bool
has_unifier (DVar _) = False
has_unifier (DMetaT _) = False
has_unifier (DMetaL _) = False
has_unifier (DRec _ _) = True

get_unifier_dependent :: Dependent -> Unifier
get_unifier_dependent (DRec u _) = u

get_inner_dependent :: Dependent -> Dependent
-- Only defined when it is a recursive dependent, obviously.
get_inner_dependent (DRec _ d) = d

instance Show Dependent where
	show (DVar x) = show x
	show (DMetaT mt) = show mt
	show (DMetaL ml) = show ml
	show (DRec u d) = (show u) ++ " " ++ (show d)

instance Ord Dependent where
	(DVar _) <= (DMetaT _) = True
	(DVar _) <= (DMetaL _) = True
	(DVar _) <= (DRec _ _) = True
	(DVar (Var i)) <= (DVar (Var j)) = i <= j
	(DMetaT _) <= (DRec _ _) = True
	(DMetaT _) <= (DVar _) = False
	(DMetaT _) <= (DMetaL _) = True	
	(DMetaT (Metavar i)) <= (DMetaT (Metavar j)) = i <= j
	(DMetaL _) <= (DRec _ _) = True
	(DMetaL _) <= (DVar _) = False	
	(DMetaL _) <= (DMetaT _) = False
	(DMetaL (Metavar i)) <= (DMetaL (Metavar j)) = i <= j
	(DRec _ _) <= (DVar _) = False
	(DRec _ _) <= (DMetaT _) = False
	(DRec _ _) <= (DMetaL _) = False
	(DRec (U i) d1) <= (DRec (U j) d2) | i == j = d1 <= d2
	(DRec (U i) d1) <= (DRec (U j) d2) = i <= j

--data HorizontalDependency = THDep ([Term] -> Term) | LTHDep ([Term] -> Literal) | LHDep (Literal -> Literal)
data TermDependencyInput = TInDependent | TInFixed Term | TInRec TermHorizontalDependency
data LitDependencyInput = LInDependent | LInFixed Literal
data TermHorizontalDependency = FApp Function [TermDependencyInput]
data LitTermHorizontalDependency = PApp Predicate [TermDependencyInput]
data LitHorizontalDependency = LEq LitDependencyInput

data HorizontalDependency = THDep TermHorizontalDependency | LTHDep LitTermHorizontalDependency | LHDep LitHorizontalDependency

instance Show TermHorizontalDependency where
	show (FApp f ins) = (show f) ++ "(" ++ recstr ++ ")" where recstr = show_tins_free ins

show_tins_free :: [TermDependencyInput] -> String
show_tins_free [] = ""
show_tins_free (TInDependent:ins) = "*" ++ ", " ++ recstr where recstr = show_tins_free ins
show_tins_free ((TInFixed t):ins) = (show t) ++ ", " ++ recstr where recstr = show_tins_free ins
show_tins_free ((TInRec rec):ins) = recstr1 ++ ", " ++ recstr2 where recstr1 = show rec; recstr2 = show_tins_free ins

show_tins :: [Dependent] -> [TermDependencyInput] -> (String,[Dependent])
show_tins ds [] = ("",ds)
show_tins (d:ds) (TInDependent:ins) = ((show d) ++ ", " ++ recstr,recdeps) where (recstr,recdeps) = show_tins ds ins
show_tins ds ((TInFixed t):ins) = ((show t) ++ "(fix)" ++ ", " ++ recstr,recdeps) where (recstr,recdeps) = show_tins ds ins
show_tins ds ((TInRec rec):ins) = (recstr1 ++ ", " ++ recstr2,recdeps2) where (recstr1,recdeps1) = show_thdep ds rec; (recstr2,recdeps2) = show_tins recdeps1 ins
	
show_thdep :: [Dependent] -> TermHorizontalDependency -> (String,[Dependent])
show_thdep ds (FApp f ins) = ((show f) ++ "(" ++ recstr ++ ")",recdeps) where (recstr,recdeps) = show_tins ds ins

show_lthdep :: [Dependent] -> LitTermHorizontalDependency -> (String,[Dependent])
show_lthdep ds (PApp p ins) = ((show p) ++ "(" ++ recstr ++ ")",recdeps) where (recstr,recdeps) = show_tins ds ins

show_lhdep :: [Dependent] -> LitHorizontalDependency -> (String,[Dependent])
show_lhdep (d:ds) (LEq LInDependent) = ((show d),ds)
show_lhdep ds (LEq (LInFixed l)) = ((show l) ++ "(fix)",ds)

show_hdep :: [Dependent] -> HorizontalDependency -> String
show_hdep ds (THDep x) = fst (show_thdep ds x)
show_hdep ds (LTHDep x) = fst (show_lthdep ds x)
show_hdep ds (LHDep x) = fst (show_lhdep ds x)

-- Purposely not defined when it does not make sense
apply_thdep :: HorizontalDependency -> [Term] -> Term
apply_thdep (THDep (FApp f ins)) ts = TFun f res where (res,_) = apply_thdep_helper ins ts

-- To be able to do it recursively, we output the list of remaining terms. In the outer-most call, this must be an empty list. In any case, there must be at least enough terms in the list
-- to keep going.
-- The first list is the actual result, and the second is the remaining unused terms.
apply_thdep_helper :: [TermDependencyInput] -> [Term] -> ([Term],[Term])
apply_thdep_helper [] [] = ([],[])
--apply_thdep_helper ((TInDependent):ins) [] = bootstrap ([],[])
apply_thdep_helper ((TInDependent):ins) (t:ts) = ((t:rec),rem) where (rec,rem) = apply_thdep_helper ins ts
apply_thdep_helper ((TInFixed t):ins) ts = ((t:rec),rem) where (rec,rem) = apply_thdep_helper ins ts
apply_thdep_helper ((TInRec (FApp f rins)):ins) ts = (((TFun f inner):outer),rem) where (inner,inner_rem) = apply_thdep_helper rins ts; (outer,rem) = apply_thdep_helper ins inner_rem

apply_lthdep :: HorizontalDependency -> [Term] -> Literal
apply_lthdep (LTHDep (PApp p ins)) ts = Lit p res where (res,_) = apply_thdep_helper ins ts

apply_lhdep :: HorizontalDependency -> Literal -> Literal
apply_lhdep (LHDep (LEq LInDependent)) l = l
apply_lhdep (LHDep (LEq (LInFixed l))) _ = l

apply_hdep :: HorizontalDependency -> Either [Term] Literal -> Either Term Literal
apply_hdep (THDep x) (Left ts) = Left (apply_thdep (THDep x) ts)
apply_hdep (LTHDep x) (Left ts) = Right (apply_lthdep (LTHDep x) ts)
apply_hdep (LHDep x) (Right l) = Right (apply_lhdep (LHDep x) l)

data VerticalDependency = TVDep (Term -> Metaterm) | LVDep (Literal -> Metaliteral)
apply_tvdep :: VerticalDependency -> Term -> Metaterm
apply_tvdep (TVDep f) = f

apply_lvdep :: VerticalDependency -> Literal -> Metaliteral
apply_lvdep (LVDep f) = f

apply_vdep :: VerticalDependency -> Either Term Literal -> Either Metaterm Metaliteral
apply_vdep (TVDep f) (Left t) = Left (apply_tvdep (TVDep f) t)
apply_vdep (LVDep f) (Right l) = Right (apply_lvdep (LVDep f) l)

-- The term parameter is the final value of the term on which the last-level unifier is applied. For example, on v u X, the term should be the value of u X, once the instantiation and u are known.
data PossibleHorizontalDependency = PTHDep ([Term] -> Term -> [HorizontalDependency]) | PLTHDep ([Term] -> Literal -> [HorizontalDependency]) | PLHDep (Literal -> Literal -> [HorizontalDependency])

-- Retrievable set (can extract elements)
type RSet t = Map.Map t t

rset_insert_helper :: Ord t => t -> (Maybe t) -> (Maybe t)
rset_insert_helper x Nothing = Just x
rset_insert_helper x (Just y) = Just y

rset_insert :: Ord t => t -> RSet t -> RSet t
rset_insert x s = Map.alter (rset_insert_helper x) x s

rset_replace :: Ord t => t -> t -> RSet t -> RSet t
rset_replace o n s = Map.adjust (\x -> n) o s

rset_contains :: Ord t => t -> RSet t -> Bool
rset_contains n s = isJust (Map.lookup n s)

rset_remove :: Ord t => t -> RSet t -> RSet t
rset_remove x s = Map.delete x s

rset_from_list :: Ord t => [t] -> RSet t
rset_from_list l = Map.fromList (map (\x -> (x,x)) l)

list_from_rset :: Ord t => RSet t -> [t]
list_from_rset s = map fst (Map.toList s)

-- DNode value outgoing_edges (horizontal, possible, vertical) incoming_edges (h, p, v)
data DependencyNode = DNode Dependent [HDependencyEdge] [PHDependencyEdge] [VDependencyEdge] [HDependencyEdge] [PHDependencyEdge] [VDependencyEdge]
get_dependent :: DependencyNode -> Dependent
get_dependent (DNode d _ _ _ _ _ _) = d
instance Eq DependencyNode where
	(DNode d1 _ _ _ _ _ _) == (DNode d2 _ _ _ _ _ _) = d1 == d2
instance Ord DependencyNode where
	(DNode d1 _ _ _ _ _ _) <= (DNode d2 _ _ _ _ _ _) = d1 <= d2 
instance Show DependencyNode where
	show (DNode dep d1 d2 d3 d4 d5 d6) = "Node: " ++ (show dep) ++ "\n" ++ 
						"\tDepends on: \n" ++ (concat (map (\e -> "\t\tHorizontal[" ++ (show e) ++ "]\n")
										d4)) ++
									(concat (map (\e -> "\t\tVertical[" ++
											(show (get_vsource e)) ++
											"]\n")
											d6)) ++
									(concat (map (\e -> "\t\tPossible horizontal[" ++
											(concat (map (\n ->
													(show n) ++
													",")
												(get_phsources e))) ++
											"]\n")
										d5)) ++
						"\tThings that depend on it: \n" ++ (concat (map (\e -> "\t\tHorizontal[" ++ (show e) ++ "]\n")
													d1)) ++
											(concat (map (\e -> "\t\tVertical[" ++
													(show (get_vtarget e)) ++
													"]\n")
													d3)) ++
											(concat (map (\e -> "\t\tPossible horizontal[" ++
													(show (get_phtarget e)) ++
													"]\n")
													d2))

get_outgoing_hdeps :: DependencyNode -> [HDependencyEdge]
get_outgoing_hdeps (DNode _ x _ _ _ _ _) = x

get_incoming_hdeps :: DependencyNode -> [HDependencyEdge]
get_incoming_hdeps (DNode _ _ _ _ x _ _) = x

get_outgoing_vdeps :: DependencyNode -> [VDependencyEdge]
get_outgoing_vdeps (DNode _ _ _ x _ _ _) = x

get_incoming_vdeps :: DependencyNode -> [VDependencyEdge]
get_incoming_vdeps (DNode _ _ _ _ _ _ x) = x
						
data EqDependencyClass = EqDep (RSet Dependent) Dependent
instance Show EqDependencyClass where
	show (EqDep s rep) = "Equivalence class: " ++ (show (Map.elems s)) ++ ", represented by: " ++ (show rep) ++ "\n"

instance Eq EqDependencyClass where
	(EqDep _ r1) == (EqDep _ r2) = r1 == r2

eqdep_set :: EqDependencyClass -> RSet Dependent
eqdep_set (EqDep s _) = s

eqdep_elems :: EqDependencyClass -> [Dependent]
eqdep_elems (EqDep s _) = Map.elems s

eqdep_rep :: EqDependencyClass -> Dependent
eqdep_rep (EqDep _ rep) = rep

new_eqdep :: Dependent -> EqDependencyClass
new_eqdep d = EqDep (rset_insert d Map.empty) d

-- HDEdge dependency sources target
data HDependencyEdge = HDEdge HorizontalDependency [Dependent] Dependent
get_hsources :: HDependencyEdge -> [Dependent]
get_hsources (HDEdge _ s _) = s

get_htarget :: HDependencyEdge -> Dependent
get_htarget (HDEdge _ _ t) = t

instance Eq HDependencyEdge where
	HDEdge _ s1 t1 == HDEdge _ s2 t2 = (s1 == s2 && t1 == t2)

instance Show HDependencyEdge where
	show (HDEdge dep ss t) = (show t) ++ " = " ++ (show_hdep ss dep)

data VDependencyEdge = VDEdge VerticalDependency Dependent Dependent
get_vsource :: VDependencyEdge -> Dependent
get_vsource (VDEdge _ s _) = s

get_vtarget :: VDependencyEdge -> Dependent
get_vtarget (VDEdge _ _ t) = t

instance Eq VDependencyEdge where
	VDEdge _ s1 t1 == VDEdge _ s2 t2 = (s1 == s2 && t1 == t2)

data PHDependencyEdge = PHDEdge PossibleHorizontalDependency [Dependent] Dependent
get_phsources :: PHDependencyEdge -> [Dependent]
get_phsources (PHDEdge _ s _) = s

get_phtarget :: PHDependencyEdge -> Dependent
get_phtarget (PHDEdge _ _ t) = t

cons_mb_mb :: Maybe t -> Maybe [t] -> Maybe [t]
cons_mb_mb Nothing _ = Nothing
cons_mb_mb _ Nothing = Nothing
cons_mb_mb (Just x) (Just xs) = Just (x:xs)

cons_mb_x :: Maybe t -> [t] -> Maybe [t]
cons_mb_x Nothing _ = Nothing
cons_mb_x (Just x) xs = Just (x:xs)

cons_x_mb :: t -> Maybe [t] -> Maybe [t]
cons_x_mb _ Nothing = Nothing
cons_x_mb x (Just xs) = Just (x:xs)

map_maybe :: (a -> Maybe b) -> [a] -> [b]
map_maybe f [] = []
map_maybe f (x:xs) = case fx of {Nothing -> map_maybe f xs; Just y -> (y:(map_maybe f xs))} where fx = f x

mbs_cons :: MaybePlenty t -> [t] -> [t]
mbs_cons NothingS xs = xs
mbs_cons (JustS x) xs = (x:xs)
mbs_cons PlentyS xs = xs

mb_eager :: Maybe t -> Maybe t -> Maybe t
mb_eager (Just x) _ = Just x
mb_eager Nothing (Just x) = Just x
mb_eager Nothing Nothing = Nothing

mb_lazy :: Maybe t -> Maybe t -> Maybe t
mb_lazy Nothing _ = Nothing
mb_lazy _ Nothing = Nothing
mb_lazy (Just x) (Just _) = Just x

data MaybePlenty t = NothingS | PlentyS | JustS t
instance Show t => Show (MaybePlenty t) where
	show NothingS = "Nothing"
	show PlentyS = "Plenty"
	show (JustS x) = "Just " ++ (show x)

mbplenty_combine :: MaybePlenty t -> MaybePlenty t -> MaybePlenty t
mbplenty_combine PlentyS _ = PlentyS
mbplenty_combine _ PlentyS = PlentyS
mbplenty_combine (JustS x) _ = JustS x
mbplenty_combine _ (JustS x) = JustS x
mbplenty_combine NothingS NothingS = NothingS

isPlentyS :: MaybePlenty t -> Bool
isPlentyS NothingS = False
isPlentyS (JustS _) = False
isPlentyS PlentyS = True

isNothingS :: MaybePlenty t -> Bool
isNothingS NothingS = True
isNothingS (JustS _) = False
isNothingS PlentyS = False

isJustS :: MaybePlenty t -> Bool
isJustS NothingS = False
isJustS (JustS _) = True
isJustS PlentyS = False

fold_with_update :: Eq a => (b -> a -> b) -> (b -> a -> a) -> b -> [a] -> b
fold_with_update _ _ r [] = r
fold_with_update comb upd r (x:xs) = fold_with_update comb upd rr rxs where rr = comb r x; rx = upd r x; rxs = fold_with_update_helper x rx xs

fold_with_update_helper :: Eq a => a -> a -> [a] -> [a]
fold_with_update_helper _ _ [] = []
fold_with_update_helper x rx (y:ys) | x == y = (rx:(fold_with_update_helper x rx ys))
fold_with_update_helper x rx (y:ys) = (y:(fold_with_update_helper x rx ys))


-- The graph between equivalence classes needs to be directed acyclic. A cycle would mean an occurs check. We represent it with an inductive structure over dependents,
-- where the same dependent may appear more than once, indicating the cycles (i.e. not syntactically explicit).
data DAGNode t = DAGNode t [DAGNode t]

show_dagnode :: Show t => String -> DAGNode t -> String
show_dagnode pre (DAGNode d cs) = pre ++ (show d) ++ "\n" ++ (concat (map (show_dagnode (pre ++ "\t")) cs))

dagnode_elem :: DAGNode t -> t
dagnode_elem (DAGNode d _) = d

instance Show t => Show (DAGNode t) where
	show n = show_dagnode "" n

-- The roots.
-- For convenience, we have a special case where the DAG has cycles, similar to the Maybe type.
data DAG t = DAG [DAGNode t] | Cycled

instance Show t => Show (DAG t) where
	show (DAG ns) = concat (map show ns)
	show Cycled = "Cycles in the DAG!\n"

dagroots :: DAG t -> [t]
dagroots (DAG ns) = map dagnode_elem ns
dagroots Cycled = []

empty_dag :: DAG t
empty_dag = DAG []

-- Here, we assume that it is not yet in the DAG.
-- We add it as a root.
add_dagnode :: t -> DAG t -> DAG t
add_dagnode _ Cycled = Cycled
add_dagnode x (DAG ns) = DAG ((DAGNode x []):ns)

find_new_dagnode :: Eq t => t -> DAG t -> DAGNode t
find_new_dagnode x dag = case r of {Just n -> n; Nothing -> DAGNode x []} where r = find_dagnode x dag

find_dagnode :: Eq t => t -> DAG t -> Maybe (DAGNode t)
find_dagnode x Cycled = Nothing
find_dagnode x (DAG ns) = find_dagnode_nodes x ns

find_dagnode_nodes :: Eq t => t -> [DAGNode t] -> Maybe (DAGNode t)
find_dagnode_nodes x [] = Nothing
find_dagnode_nodes x ((DAGNode y n1s):n2s) | x == y = Just (DAGNode y n1s)
find_dagnode_nodes x ((DAGNode _ n1s):n2s) = if (isJust r1) then r1 else (find_dagnode_nodes x n2s) where r1 = find_dagnode_nodes x n1s

maybe_add_dagnode :: Eq t => t -> DAG t -> DAG t
maybe_add_dagnode x dag = case (find_dagnode x dag) of {Nothing -> add_dagnode x dag; Just _ -> dag}


-- First we remove all its edges.
remove_dagnode :: Eq t => t -> DAG t -> DAG t
remove_dagnode _ Cycled = Cycled
remove_dagnode x (DAG ns) = DAG (remove_dagnode_nodes x rns) where n = find_dagnode x (DAG ns); ts = case n of {Nothing -> []; Just (DAGNode _ cs) -> map dagnode_elem cs}; rdag = foldl (\dag -> \t -> remove_dagedge x t dag) (DAG ns) ts; rns = case rdag of {DAG ns -> ns}

remove_dagnode_nodes :: Eq t => t -> [DAGNode t] -> [DAGNode t]
remove_dagnode_nodes _ [] = []
remove_dagnode_nodes x ((DAGNode y n1s):n2s) | x == y = remove_dagnode_nodes x n2s
remove_dagnode_nodes x ((DAGNode y n1s):n2s) = ((DAGNode y (remove_dagnode_nodes x n1s)):(remove_dagnode_nodes x n2s))

remove_dagroot :: Eq t => t -> DAG t -> DAG t
remove_dagroot _ Cycled = Cycled
remove_dagroot x (DAG ns) = DAG (remove_dagroot_roots x ns)

remove_dagroot_roots :: Eq t => t -> [DAGNode t] -> [DAGNode t]
remove_dagroot_roots _ [] = []
remove_dagroot_roots x ((DAGNode y n1s):n2s) | x == y = remove_dagroot_roots x n2s
remove_dagroot_roots x ((DAGNode y n1s):n2s) = ((DAGNode y n1s):(remove_dagroot_roots x n2s))

-- These functions give a very high amount of repetitions for edges, but we don't really care about the excess (and we need to have at least all the existing repetitions). 
-- However, I am worried that this might be way too inefficient, so it is a point to look at if things are slow.
find_incoming_dagedges :: Eq t => t -> DAG t -> [t]
find_incoming_dagedges x Cycled = []
find_incoming_dagedges x (DAG ns) = find_incoming_dagedges_roots x ns

find_incoming_dagedges_roots :: Eq t => t -> [DAGNode t] -> [t]
find_incoming_dagedges_roots x [] = []
find_incoming_dagedges_roots x ((DAGNode y n1s):n2s) = (find_incoming_dagedges_nodes y x n1s) ++ (find_incoming_dagedges_roots x n2s)

find_incoming_dagedges_nodes :: Eq t => t -> t -> [DAGNode t] -> [t]
find_incoming_dagedges_nodes s x [] = []
find_incoming_dagedges_nodes s x ((DAGNode y n1s):n2s) | y == x = (s:(find_incoming_dagedges_nodes s x n2s))
find_incoming_dagedges_nodes s x ((DAGNode y n1s):n2s) = (find_incoming_dagedges_nodes y x n1s) ++ (find_incoming_dagedges_nodes s x n2s)

find_outgoing_dagedges :: Eq t => t -> DAG t -> [t]
find_outgoing_dagedges x dag = case n of {Nothing -> []; Just (DAGNode _ ns) -> map (\n2 -> case n2 of {DAGNode z _ -> z}) ns} where n = find_dagnode x dag

-- The node needs to be part of the graph, otherwise it won't work properly. 
replace_dagnode :: Eq t => t -> t -> DAG t -> DAG t
replace_dagnode x y dag = remove_dagroot x (replace_dagnode_with_inedges x y (find_incoming_dagedges x dag) (replace_dagnode_with_outedges x y (find_outgoing_dagedges x dag) dag))

replace_dagnode_with_outedges :: Eq t => t -> t -> [t] -> DAG t -> DAG t
replace_dagnode_with_outedges _ _ [] dag = dag
replace_dagnode_with_outedges x y (z:zs) dag = replace_dagnode_with_outedges x y zs (remove_dagedge x z (add_dagedge y z dag))

replace_dagnode_with_inedges :: Eq t => t -> t -> [t] -> DAG t -> DAG t
replace_dagnode_with_inedges _ _ [] dag = dag
replace_dagnode_with_inedges x y (z:zs) dag = replace_dagnode_with_inedges x y zs (remove_dagedge z x (add_dagedge z y dag))


-- Here, we assume that both elements are already in the DAG.
add_dagedge :: Eq t => t -> t -> DAG t -> DAG t
add_dagedge x y dag | x == y = Cycled
add_dagedge s t dag = add_dagedge_with_node s t n dag where n = find_new_dagnode t dag

add_dagedge_with_node :: Eq t => t -> t -> DAGNode t -> DAG t -> DAG t
add_dagedge_with_node _ _ _ Cycled = Cycled
add_dagedge_with_node s t n (DAG ns) = case r of {Just ns -> DAG ns; Nothing -> Cycled} where r = add_dagedge_with_node_roots s t n ns

add_dagedge_with_node_roots :: Eq t => t -> t -> DAGNode t -> [DAGNode t] -> Maybe [DAGNode t]
add_dagedge_with_node_roots _ _ _ [] = Just []
-- If the target is a root, just completely ignore it, unless it becomes a cycle.
add_dagedge_with_node_roots s t n ((DAGNode x n1s):n2s) | t == x = mb_lazy (add_dagedge_with_node_roots s t n n2s) (add_dagedge_with_node_roots_danger s n1s)
-- If the source is a root, then we add the node
add_dagedge_with_node_roots s t n ((DAGNode x n1s):n2s) | s == x = cons_x_mb (DAGNode x (n:n1s)) (add_dagedge_with_node_roots s t n n2s)
add_dagedge_with_node_roots s t n ((DAGNode x n1s):n2s) = cons_mb_mb (dagnode_x_mb x (add_dagedge_with_node_nodes s t n n1s)) (add_dagedge_with_node_roots s t n n2s)

add_dagedge_with_node_roots_danger :: Eq t => t -> [DAGNode t] -> Maybe [DAGNode t]
add_dagedge_with_node_roots_danger s [] = Just []
-- Cycle!!!!
add_dagedge_with_node_roots_danger s ((DAGNode x n1s):n2s) | s == x = Nothing
-- We really do not need the result here, just to see if there are cycles.
add_dagedge_with_node_roots_danger s ((DAGNode x n1s):n2s) = mb_lazy (add_dagedge_with_node_roots_danger s n1s) (add_dagedge_with_node_roots_danger s n2s)

dagnode_x_mb :: t -> Maybe [DAGNode t] -> Maybe (DAGNode t)
dagnode_x_mb _ Nothing = Nothing
dagnode_x_mb n (Just ns) = Just (DAGNode n ns)

-- Chances of multiple edges between two nodes are few, so checking for repetition is more expensive than simply dealing with it. It is not a problem that edges are repeated.
-- Moreover, this allows us a simple way to keep count of the multiplicity of edges, so that when there are several, we can remove one without removing all of them.
add_dagedge_with_node_nodes :: Eq t => t -> t -> DAGNode t -> [DAGNode t] -> Maybe [DAGNode t]
add_dagedge_with_node_nodes _ _ _ [] = Just []
add_dagedge_with_node_nodes s t n ((DAGNode x n1s):n2s) | s == x = cons_x_mb (DAGNode x (n:n1s)) (add_dagedge_with_node_nodes s t n n2s)
add_dagedge_with_node_nodes s t n ((DAGNode x n1s):n2s) | t == x = cons_mb_mb (dagnode_x_mb x (add_dagedge_with_node_nodes_danger s n n1s)) (add_dagedge_with_node_nodes s t n n2s)
add_dagedge_with_node_nodes s t n ((DAGNode x n1s):n2s) = cons_mb_mb (dagnode_x_mb x (add_dagedge_with_node_nodes s t n n1s)) (add_dagedge_with_node_nodes s t n n2s)

add_dagedge_with_node_nodes_danger :: Eq t => t -> DAGNode t -> [DAGNode t] -> Maybe [DAGNode t]
add_dagedge_with_node_nodes_danger s n [] = Just []
-- Cycle!!!!
add_dagedge_with_node_nodes_danger s n ((DAGNode x n1s):n2s) | s == x = Nothing
add_dagedge_with_node_nodes_danger s n ((DAGNode x n1s):n2s) = cons_mb_mb (dagnode_x_mb x (add_dagedge_with_node_nodes_danger s n n1s)) (add_dagedge_with_node_nodes_danger s n n2s)

remove_dagedge :: Eq t => t -> t -> DAG t -> DAG t
remove_dagedge _ _ Cycled = Cycled
remove_dagedge s t (DAG ns) = DAG (mbs_cons (snd r) (fst r)) where r = remove_dagedge_nodes s t ns

-- We keep track of the node we removed, to add it as a root. If we find it again, we return Plenty.
remove_dagedge_nodes :: Eq t => t -> t -> [DAGNode t] -> ([DAGNode t],MaybePlenty (DAGNode t))
remove_dagedge_nodes s t [] = ([],NothingS)
remove_dagedge_nodes s t ((DAGNode x n1s):n2s) | s == x = (((DAGNode x (fst rx)):(fst rxs)),mbplenty_combine (snd rx) (snd rxs)) where rx = remove_dagedge_nodes_source t n1s; rxs = remove_dagedge_nodes s t n2s
remove_dagedge_nodes s t ((DAGNode x n1s):n2s) | t == x = (((DAGNode x (fst rx)):(fst rxs)),PlentyS) where rx = remove_dagedge_nodes s t n1s; rxs = remove_dagedge_nodes s t n2s
remove_dagedge_nodes s t ((DAGNode x n1s):n2s) = (((DAGNode x (fst rx)):(fst rxs)),mbplenty_combine (snd rx) (snd rxs)) where rx = remove_dagedge_nodes s t n1s; rxs = remove_dagedge_nodes s t n2s

remove_dagedge_nodes_source :: Eq t => t -> [DAGNode t] -> ([DAGNode t],MaybePlenty (DAGNode t))
remove_dagedge_nodes_source t [] = ([],NothingS)
-- Remove ONLY one, so after we found one, we change function.
remove_dagedge_nodes_source t ((DAGNode x n1s):n2s) | t == x = (n2s,mbplenty_combine (JustS (DAGNode x n1s)) rxs) where rxs = remove_dagedge_nodes_justfind t n2s
remove_dagedge_nodes_source t ((DAGNode x n1s):n2s) = (((DAGNode x n1s):(fst rxs)),mbplenty_combine rx (snd rxs)) where rx = remove_dagedge_nodes_justfind t n1s; rxs = remove_dagedge_nodes_source t n2s

remove_dagedge_nodes_justfind :: Eq t => t -> [DAGNode t] -> MaybePlenty (DAGNode t)
remove_dagedge_nodes_justfind t [] = NothingS
remove_dagedge_nodes_justfind t ((DAGNode x n1s):n2s) | t == x = PlentyS
remove_dagedge_nodes_justfind t ((DAGNode x n1s):n2s) = mbplenty_combine (remove_dagedge_nodes_justfind t n1s) (remove_dagedge_nodes_justfind t n2s)

find_all_leaves_dag :: DAG t -> [t]
find_all_leaves_dag Cycled = []
find_all_leaves_dag (DAG ns) = concat (map find_all_leaves_dag_helper ns)

find_all_leaves_dag_helper :: DAGNode t -> [t]
find_all_leaves_dag_helper (DAGNode x []) = [x]
find_all_leaves_dag_helper (DAGNode _ ns) = concat (map find_all_leaves_dag_helper ns)

type EqDepDAGNode = DAGNode Dependent
type EqDepDAG = DAG Dependent

data DependencyGraph = DGraph (RSet DependencyNode) [EqDependencyClass] EqDepDAG
nodes :: DependencyGraph -> [DependencyNode]
nodes (DGraph ns _ _) = Map.elems ns

dag :: DependencyGraph -> EqDepDAG
dag (DGraph _ _ dag) = dag

roots :: DependencyGraph -> [Dependent]
roots g = dagroots (dag g)

instance Show DependencyGraph where
	show (DGraph ns cs dag) = (concat (map show (Map.elems ns))) ++ (concat (map show cs)) ++ "Horizontal dependency DAG: \n" ++ (show dag)

unconnected_node :: Dependent -> DependencyNode
unconnected_node d = DNode d [] [] [] [] [] []

replace_once :: Eq t => t -> t -> [t] -> [t]
replace_once x y [] = []
replace_once x y (z:zs) | x == z = (y:zs)
replace_once x y (z:zs) = (z:(replace_once x y zs))

replace_all :: Eq t => t -> t -> [t] -> [t]
replace_all x y [] = []
replace_all x y (z:zs) | x == z = (y:(replace_all x y zs))
replace_all x y (z:zs) = (z:(replace_all x y zs))


add_outgoing_hdep :: HDependencyEdge -> DependencyNode -> DependencyNode
add_outgoing_hdep e (DNode dep d1 d2 d3 d4 d5 d6) = DNode dep (e:d1) d2 d3 d4 d5 d6

del_outgoing_hdep :: HDependencyEdge -> DependencyNode -> DependencyNode
del_outgoing_hdep e (DNode dep d1 d2 d3 d4 d5 d6) = DNode dep (List.delete e d1) d2 d3 d4 d5 d6

update_outgoing_hdep :: HDependencyEdge -> HDependencyEdge -> DependencyNode -> DependencyNode
update_outgoing_hdep e1 e2 (DNode dep d1 d2 d3 d4 d5 d6) = DNode dep (replace_once e1 e2 d1) d2 d3 d4 d5 d6

add_incoming_hdep :: HDependencyEdge -> DependencyNode -> DependencyNode
add_incoming_hdep e (DNode dep d1 d2 d3 d4 d5 d6) = DNode dep d1 d2 d3 (e:d4) d5 d6

del_incoming_hdep :: HDependencyEdge -> DependencyNode -> DependencyNode
del_incoming_hdep e (DNode dep d1 d2 d3 d4 d5 d6) = DNode dep d1 d2 d3 (List.delete e d4) d5 d6

update_incoming_hdep :: HDependencyEdge -> HDependencyEdge -> DependencyNode -> DependencyNode
update_incoming_hdep e1 e2 (DNode dep d1 d2 d3 d4 d5 d6) = DNode dep d1 d2 d3 (replace_once e1 e2 d4) d5 d6

add_outgoing_phdep :: PHDependencyEdge -> DependencyNode -> DependencyNode
add_outgoing_phdep e (DNode dep d1 d2 d3 d4 d5 d6) = DNode dep d1 (e:d2) d3 d4 d5 d6

add_incoming_phdep :: PHDependencyEdge -> DependencyNode -> DependencyNode
add_incoming_phdep e (DNode dep d1 d2 d3 d4 d5 d6) = DNode dep d1 d2 d3 d4 (e:d5) d6

add_outgoing_vdep :: VDependencyEdge -> DependencyNode -> DependencyNode
add_outgoing_vdep e (DNode dep d1 d2 d3 d4 d5 d6) = DNode dep d1 d2 (e:d3) d4 d5 d6

del_outgoing_vdep :: VDependencyEdge -> DependencyNode -> DependencyNode
del_outgoing_vdep e (DNode dep d1 d2 d3 d4 d5 d6) = DNode dep d1 d2 (List.delete e d3) d4 d5 d6

update_outgoing_vdep :: VDependencyEdge -> VDependencyEdge -> DependencyNode -> DependencyNode
update_outgoing_vdep e1 e2 (DNode dep d1 d2 d3 d4 d5 d6) = DNode dep d1 d2 (replace_once e1 e2 d3) d4 d5 d6

add_incoming_vdep :: VDependencyEdge -> DependencyNode -> DependencyNode
add_incoming_vdep e (DNode dep d1 d2 d3 d4 d5 d6) = DNode dep d1 d2 d3 d4 d5 (e:d6)

del_incoming_vdep :: VDependencyEdge -> DependencyNode -> DependencyNode
del_incoming_vdep e (DNode dep d1 d2 d3 d4 d5 d6) = DNode dep d1 d2 d3 d4 d5 (List.delete e d6)

update_incoming_vdep :: VDependencyEdge -> VDependencyEdge -> DependencyNode -> DependencyNode
update_incoming_vdep e1 e2 (DNode dep d1 d2 d3 d4 d5 d6) = DNode dep d1 d2 d3 d4 d5 (replace_once e1 e2 d6)

is_node :: DependencyGraph -> Dependent -> Bool
is_node (DGraph ns _ _) d = rset_contains (unconnected_node d) ns

-- If we can't find the node, raise an error.
find_node :: DependencyGraph -> Dependent -> DependencyNode
--find_node (DGraph ns _ dag) d = case (Map.lookup (unconnected_node d) ns) of {Just x -> x; Nothing -> bootstrap (DNode (DVar (read "x0")) [] [] [] [] [] [])}
find_node (DGraph ns cs dag) d = case (Map.lookup (unconnected_node d) ns) of {Just x -> x; Nothing -> unconnected_node d}

find_node_maybe :: DependencyGraph -> Dependent -> Maybe DependencyNode
find_node_maybe (DGraph ns _ _) d = Map.lookup (unconnected_node d) ns

-- Applies a function to a node in the graph.
apply_to_node :: Dependent -> (DependencyNode -> DependencyNode) -> (DependencyGraph -> DependencyGraph)
apply_to_node d f (DGraph ns cs dag) = DGraph (rset_replace n fn ns) cs dag where n = find_node (DGraph ns cs dag) d; fn = f n
--apply_to_node d f (DGraph ns cs dag) = if (isNothing nmb) then (DGraph ns cs dag) else (DGraph (rset_replace n fn ns) cs dag) where nmb = find_node_maybe (DGraph ns cs dag) d; n = find_node (DGraph ns cs dag) d; fn = f n

apply_to_dag :: (EqDepDAG -> EqDepDAG) -> DependencyGraph -> DependencyGraph
apply_to_dag f (DGraph ns cs dag) = DGraph ns cs (f dag)

empty_graph :: DependencyGraph
empty_graph = DGraph Map.empty [] empty_dag


-- These are the "primitives" to modify the graph from outside. This is where equivalence class graph quotient needs to be kept updated.

add_node :: DependencyGraph -> Dependent -> DependencyGraph
-- Check that it is not already in the graph.
add_node (DGraph ns cs dag) n | (rset_contains (unconnected_node n) ns) = DGraph ns cs dag
add_node (DGraph ns cs dag) n = DGraph (rset_insert (unconnected_node n) ns) ((new_eqdep n):cs) (add_dagnode n dag)

-- Remove the node, and ALL of its dependencies.
remove_node :: DependencyGraph -> Dependent -> DependencyGraph
remove_node g d = DGraph (rset_remove n rns) rcs rdag where n = find_node g d; (rns,rcs,rdag) = case (remove_node_eqdeps (remove_node_hvdeps g d) d) of DGraph ns cs dag -> (ns,cs,dag)
--remove_node g d = if (isNothing nmb) then g else (DGraph (rset_remove n rns) rcs rdag) where nmb = find_node_maybe g d; n = find_node g d; (rns,rcs,rdag) = case (remove_node_eqdeps (remove_node_hvdeps g d) d) of DGraph ns cs dag -> (ns,cs,dag)

-- It is assumed that one dependency is never cyclic.
add_hdep :: DependencyGraph -> HorizontalDependency -> [Dependent] -> Dependent -> DependencyGraph
add_hdep g dep ss t = apply_to_dag (\dah -> (foldl (\dag -> \s -> add_dagedge (find_eqdep_rep g s) (find_eqdep_rep g t) dag) dah ss)) (apply_to_node t (add_incoming_hdep edge) (foldl (\gg -> \s -> apply_to_node s (add_outgoing_hdep edge) gg) g ss)) where edge = HDEdge dep ss t

add_phdep :: DependencyGraph -> PossibleHorizontalDependency -> [Dependent] -> Dependent -> DependencyGraph
add_phdep g dep ss t = apply_to_node t (add_incoming_phdep edge) (foldl (\gg -> \s -> apply_to_node s (add_outgoing_phdep edge) gg) g ss) where edge = PHDEdge dep ss t

-- This is a bit ugly. We should have instead changed the representation. We know that nodes can only have one (incoming) vertical dependency, so we only add it if it does not already have it.
add_vdep :: DependencyGraph -> VerticalDependency -> Dependent -> Dependent -> DependencyGraph
add_vdep g dep s t = if (has_vdep g t) then g else (apply_to_node t (add_incoming_vdep edge) (apply_to_node s (add_outgoing_vdep edge) g)) where edge = VDEdge dep s t

update_hdep :: DependencyGraph -> HDependencyEdge -> HDependencyEdge -> DependencyGraph
update_hdep g (HDEdge dep ss t) e2 = apply_to_dag (update_dag_hdep (map (find_eqdep_rep g) ss) (map (find_eqdep_rep g) (get_hsources e2)) (find_eqdep_rep g t) (find_eqdep_rep g (get_htarget e2))) (apply_to_node t (update_incoming_hdep e1 e2) (foldl (\gg -> \s -> apply_to_node s (update_outgoing_hdep e1 e2) gg) g ss)) where e1 = HDEdge dep ss t

del_hdep_from_source :: DependencyGraph -> Dependent -> HDependencyEdge -> DependencyGraph
del_hdep_from_source g d e = apply_to_node d (del_outgoing_hdep e) g

del_all_incoming_hdeps :: DependencyGraph -> Dependent -> DependencyGraph
del_all_incoming_hdeps g d = foldl (\h -> \e -> apply_to_node d (del_incoming_hdep e) (foldl (\i -> \s -> apply_to_node s (del_outgoing_hdep e) (apply_to_dag (remove_dagedge (find_eqdep_rep i s) (find_eqdep_rep i d)) i)) h (get_hsources e))) g (get_incoming_hdeps (find_node g d))

add_eqdep :: DependencyGraph -> Dependent -> Dependent -> DependencyGraph
-- Each dependent must already be in exactly one dependency class. Find them, and merge them.
-- To avoid doing too much equality comparation, we just find first one, then the other, then add the new one.
add_eqdep (DGraph ns cs dag) d1 d2 = DGraph ns (fst sol) (maybe_replace_node (snd sol) dag) where sol = add_eqdep_1 cs d1 d2


-- Until here.

list_replace :: Eq b => b -> b -> [b] -> [b]
list_replace a b = map (\x -> if (a == x) then b else x)

-- Need to remove them from the node itself or otherwise in the DAG they will slide over to another representative.
remove_node_hvdeps :: DependencyGraph -> Dependent -> DependencyGraph
remove_node_hvdeps g d = foldl (\h -> \hdep -> remove_hdep h hdep) (foldl (\i -> \vdep -> remove_vdep i vdep) g ((get_outgoing_vdeps n) ++ (get_incoming_vdeps n))) ((get_outgoing_hdeps n) ++ (get_incoming_hdeps n)) where n = find_node g d
--remove_node_hvdeps g d = foldl (\h -> \dep -> apply_to_node (get_vsource dep) (del_outgoing_vdep dep) h) (foldl (\h -> \dep -> apply_to_node (get_vtarget dep) (del_incoming_vdep dep) h) (foldl (\h -> \dep -> foldl (\i -> \t -> apply_to_node t (del_outgoing_hdep dep) i) h (get_hsources dep)) (foldl (\h -> \dep -> foldl (\i -> \s -> apply_to_node s (del_outgoing_hdep dep) i) (apply_to_node (get_htarget dep) (del_incoming_hdep dep) h) (get_hsources dep)) g (get_outgoing_hdeps n)) (get_incoming_hdeps n)) (get_outgoing_vdeps n)) (get_incoming_vdeps n) where n = find_node g d

remove_hdep :: DependencyGraph -> HDependencyEdge -> DependencyGraph
remove_hdep g e = foldl (\j -> \s -> apply_to_dag (remove_dagedge s (get_htarget e)) j) (apply_to_node (get_htarget e) (del_incoming_hdep e) (foldl (\h -> \s -> apply_to_node s (del_outgoing_hdep e) h) g (get_hsources e))) (get_hsources e)

remove_vdep :: DependencyGraph -> VDependencyEdge -> DependencyGraph
remove_vdep g e = apply_to_node (get_vtarget e) (del_incoming_vdep e) (apply_to_node (get_vsource e) (del_outgoing_vdep e) g)

remove_node_eqdeps :: DependencyGraph -> Dependent -> DependencyGraph
remove_node_eqdeps g d = case act of {NothingS -> (DGraph ns (List.delete c cs) (remove_dagnode d dag)); JustS nd -> (DGraph ns (list_replace c (case nc of {Just x -> x}) cs) (replace_dagnode d nd (add_dagnode nd dag))); PlentyS -> (DGraph ns (list_replace c (case nc of {Just x -> x}) cs) dag)} where n = find_node g d; c = find_eqdep g d; ncres = remove_node_eqdeps_class c d; (nc,act) = ncres; (ns,cs,dag) = case g of {DGraph ns cs dag -> (ns,cs,dag)}

-- If it returns Nothing, then remove the equivalence class altogether, as it was the last element in it. If it returns Just x, then it means that it was the representative element for the class,
-- and x is the new representative element. If it returns Plenty, it means that it was not the representative element for the class, so nothing needs to be done.
remove_node_eqdeps_class :: EqDependencyClass -> Dependent -> (Maybe EqDependencyClass,MaybePlenty Dependent)
remove_node_eqdeps_class (EqDep s r) d | (r == d) && ((Map.size s) == 1) = (Nothing,NothingS)
remove_node_eqdeps_class (EqDep s r) d | (r == d) = (Just (EqDep ns nr),JustS nr) where ns = rset_remove d s; l = Map.keys ns; nr = case l of {(x:_) -> x}
remove_node_eqdeps_class (EqDep s r) d = (Just (EqDep ns r),PlentyS) where ns = rset_remove d s

has_vdep :: DependencyGraph -> Dependent -> Bool
has_vdep g d = not (null (case (find_node g d) of {DNode _ _ _ _ _ _ x -> x}))
--has_vdep g d = if (isNothing nmb) then False else (not (null (case (find_node g d) of {DNode _ _ _ _ _ _ x -> x}))) where nmb = find_node_maybe g d

-- The simple way that also works efficiently with the way that we do things (in general the new dependency will be the old one with one less source) is:
-- 	Iterate over the sources of both edges at the same time.
--	When the sources are equal, perfect, just keep going.
--	When the sources are different, we remove the edge from the old source, and keep going.
--	When there are no more sources left on either side, we add the remaining dependencies from the other side.
--	All of that, as long as the target is the same. If the target is different, just remove all old and add all new.
update_dag_hdep :: [Dependent] -> [Dependent] -> Dependent -> Dependent -> EqDepDAG -> EqDepDAG
update_dag_hdep [] [] t1 t2 dag | t1 == t2 = dag
update_dag_hdep (s:ss) [] t1 t2 dag | t1 == t2 = update_dag_hdep ss [] t1 t2 (remove_dagedge s t1 dag)
update_dag_hdep [] (s:ss) t1 t2 dag | t1 == t2 = update_dag_hdep [] ss t1 t2 (add_dagedge s t2 dag)
update_dag_hdep (s1:s1s) (s2:s2s) t1 t2 dag | t1 == t2 && s1 == s2 = update_dag_hdep s1s s2s t1 t2 dag
update_dag_hdep (s1:s1s) (s2:s2s) t1 t2 dag | t1 == t2 = update_dag_hdep s1s (s2:s2s) t1 t2 (remove_dagedge s1 t1 dag)
-- In the case where targets are different (should not be called)
update_dag_hdep [] [] t1 t2 dag = dag
update_dag_hdep (s:ss) [] t1 t2 dag = update_dag_hdep ss [] t1 t2 (remove_dagedge s t1 dag)
update_dag_hdep [] (s:ss) t1 t2 dag = update_dag_hdep [] ss t1 t2 (add_dagedge s t2 dag)
update_dag_hdep (s1:s1s) (s2:s2s) t1 t2 dag = update_dag_hdep s1s (s2:s2s) t1 t2 (remove_dagedge s1 t1 dag)


maybe_replace_node :: Maybe (Dependent, Dependent) -> EqDepDAG -> EqDepDAG
maybe_replace_node Nothing dag = dag
maybe_replace_node (Just (o,n)) dag = replace_dagnode o n dag

-- Also returns the representative elements to update (everywhere left appears, replace with right)
add_eqdep_1 :: [EqDependencyClass] -> Dependent -> Dependent -> ([EqDependencyClass],Maybe (Dependent,Dependent))
-- The particular case in which both are already in the same class is considered.
add_eqdep_1 (c:cs) d1 d2 | is_in_eqdep c d1 && is_in_eqdep c d2 = ((c:cs),Nothing)
-- d1 is in c, but d2 is not, so we can safely remove c.
add_eqdep_1 (c:cs) d1 d2 | is_in_eqdep c d1 = add_eqdep_2 cs c d2
-- d2 is in c, but d1 is not, so we can safely remove c.
add_eqdep_1 (c:cs) d1 d2 | is_in_eqdep c d2 = add_eqdep_2 cs c d1
-- Neither is in this class, we keep it then.
add_eqdep_1 (c:cs) d1 d2 = ((c:(fst sol)),(snd sol)) where sol = add_eqdep_1 cs d1 d2
-- We purposely do not consider the case when it is not in any equivalence class. This should not happen, and we want to raise an error in such case.
--add_eqdep_1 [] d1 d2 = capture_value (d1,d2) ([],Nothing)

add_eqdep_2 :: [EqDependencyClass] -> EqDependencyClass -> Dependent -> ([EqDependencyClass],Maybe (Dependent,Dependent))
-- It is in this one. We remove it, and add the union with the previous one to the remainder of the list.
add_eqdep_2 (c:cs) c1 d2 | is_in_eqdep c d2 = (((EqDep (Map.union s2 s1) rep1):cs),Just (rep2,rep1)) where s1 = case c1 of {EqDep x _ -> x}; s2 = case c of {EqDep x _ -> x}; rep1 = eqdep_rep c1; rep2 = eqdep_rep c
-- It is not in this one. We keep it and move on.
add_eqdep_2 (c:cs) c1 d2 = ((c:(fst sol)),(snd sol)) where sol = add_eqdep_2 cs c1 d2
-- We purposely do not consider the case when it is not in any equivalence class. This should not happen, and we want to raise an error in such case.

is_in_eqdep :: EqDependencyClass -> Dependent -> Bool
is_in_eqdep (EqDep s _) d = Map.member d s

find_eqdep :: DependencyGraph -> Dependent -> EqDependencyClass
find_eqdep (DGraph _ cs _) d = find_eqdep_cs cs d

find_eqdep_rep :: DependencyGraph -> Dependent -> Dependent
find_eqdep_rep g d = eqdep_rep (find_eqdep g d)

find_eqdep_cs :: [EqDependencyClass] -> Dependent -> EqDependencyClass
-- It's either on the first class...
find_eqdep_cs ((EqDep s rep):cs) d | (Map.member d s) = EqDep s rep
find_eqdep_cs ((EqDep s _):cs) d = find_eqdep_cs cs d
-- OLD: We purposely do not consider the case when it is not in any equivalence class. This should not happen, and we want to raise an error in such case.
find_eqdep_cs [] d = EqDep (Map.singleton d d) d


-- Building dependency graphs from constraints
concat_functions :: [([a] -> b)] -> [Int] -> ([a] -> [b])
concat_functions [] _ vs = []
concat_functions (f:fs) (n:ns) vs = (f (fst sides)):(concat_functions fs ns (snd sides)) where sides = splitAt n vs

-- Note that meta-literal constraints are always between two meta-variables and so both sides are dependents.
-- The outer-most unifier is assumed to have been removed from the meta-term already when passed here: This contains the inner meta-term.
-- We assume that meta-literals/terms arriving here have been simplified and so they are never of the form MTermT, MTermR, MLitL or MLitR unless they are variables or meta-variables.
--data DependencyConstraintSide = DDep Dependent | DFun [Dependent] ([Term] -> Term)
--data TermDependencyInput = TInDependent | TInFixed Term | TInRec TermHorizontalDependency
--data LitDependencyInput = LInDependent | LInFixed Literal
--data TermHorizontalDependency = FApp Function [TermDependencyInput]
--data LitTermHorizontalDependency = PApp Predicate [TermDependencyInput]
--data LitHorizontalDependency = LEq LitDependencyInput

--data HorizontalDependency = THDep TermHorizontalDependency | LTHDep LitTermHorizontalDependency | LHDep LitHorizontalDependency
data MetatermModUnif = MTermFixed Term | MTermTMU Term | MTermRMU Unifier MetatermModUnif | MTermFMU Function [MetatermModUnif]
data MetaliteralModUnif = MLitFixed Literal | MLitLMU Literal | MLitRMU Unifier MetaliteralModUnif | MLitPMU Predicate [MetatermModUnif]
data DependencyConstraintSide = DDep Dependent | DFun [Dependent] TermHorizontalDependency | DFixedT Term | DFixedL Literal

build_dependency_side_term :: MetatermModUnif -> DependencyConstraintSide
build_dependency_side_term (MTermTMU (TVar v)) = DDep (DVar v)
build_dependency_side_term (MTermTMU (TMeta mv)) = DDep (DMetaT mv)
build_dependency_side_term (MTermFMU f ts) = DFun (concat deps) (FApp f funs)
								where recs = map build_dependency_side_term ts;
									deps = map (\s -> case s of {DDep x -> [x]; DFun xs _ -> xs; DFixedT _ -> []}) recs; 
									funs = map (\s -> case s of {DDep _ -> TInDependent; DFun _ sf -> TInRec sf; DFixedT t -> TInFixed t}) recs;
									lengths = map length deps
build_dependency_side_term (MTermRMU u mt) = case (build_dependency_side_term mt) of DDep d -> DDep (DRec u d) -- If it is a function, something's not right. Similarly if it is a fixed value.
build_dependency_side_term (MTermFixed t) = DFixedT t

build_dependency_side_lit :: MetaliteralModUnif -> DependencyConstraintSide
build_dependency_side_lit (MLitLMU (LitM mv)) = DDep (DMetaL mv)
build_dependency_side_lit (MLitRMU u ml) = case (build_dependency_side_lit ml) of DDep d -> DDep (DRec u d) -- If it is a predicate, something's not right. Similarly if it is a fixed value.
build_dependency_side_lit (MLitFixed l) = DFixedL l

-- Apart from all the assumptions above, remember that they need to have the outer-most unifier. This unifier is not taken into consideration in the dependency, as it is the unifier at which level
-- the dependency is horizontal. We do this by extracting the inner meta-literals/terms with a function. However, if the term is a function, the unifiers have been pushed inwards. We solve this through
-- recursive calls
extract_inner_literal :: Metaliteral -> MetaliteralModUnif
extract_inner_literal (MLitR _ ml) = modulate_metaliteral ml
extract_inner_literal (MLitL l) = MLitFixed l
extract_inner_literal (MLitP p mts) = MLitPMU p (map extract_inner_term mts)

modulate_metaliteral :: Metaliteral -> MetaliteralModUnif
modulate_metaliteral (MLitL l) = MLitLMU l
modulate_metaliteral (MLitR u ml) = MLitRMU u (modulate_metaliteral ml)
modulate_metaliteral (MLitP p mts) = MLitPMU p (map modulate_metaterm mts)

extract_inner_term :: Metaterm -> MetatermModUnif
extract_inner_term (MTermR _ mt) = modulate_metaterm mt
extract_inner_term (MTermF f mts) = MTermFMU f (map extract_inner_term mts)
extract_inner_term (MTermT t) = MTermFixed t

modulate_metaterm :: Metaterm -> MetatermModUnif
modulate_metaterm (MTermT t) = MTermTMU t
modulate_metaterm (MTermR u mt) = MTermRMU u (modulate_metaterm mt)
modulate_metaterm (MTermF f mts) = MTermFMU f (map modulate_metaterm mts)

extract_unifier_literal :: Metaliteral -> Maybe Unifier
extract_unifier_literal (MLitR u _) = Just u
extract_unifier_literal (MLitP _ _) = Nothing
extract_unifier_literal (MLitL _) = Nothing

extract_unifier_term :: Metaterm -> Maybe Unifier
extract_unifier_term (MTermR u _) = Just u
extract_unifier_term (MTermF _ _) = Nothing
extract_unifier_term (MTermT _) = Nothing

extract_unifier_constraint :: Constraint -> Unifier
extract_unifier_constraint (Lcstr ml1 ml2) | isJust res = case res of {Just x -> x} where res = extract_unifier_literal ml1
extract_unifier_constraint (Lcstr _ ml2) = case (extract_unifier_literal ml2) of Just x -> x
extract_unifier_constraint (Tcstr mt1 mt2) | isJust res = case res of {Just x -> x} where res = extract_unifier_term mt1
extract_unifier_constraint (Tcstr _ mt2) = case (extract_unifier_term mt2) of Just x -> x

add_unifier_dependent :: Unifier -> Dependent -> Dependent
add_unifier_dependent u d = DRec u d

-- Three (possible) results: A dependency from left to right, a dependency from right to left, or directly a value.
build_dependency_constraint :: Constraint -> (Maybe (([Dependent],Dependent),HorizontalDependency),Maybe (([Dependent],Dependent),HorizontalDependency),Maybe (Dependent,Either Term Literal))
build_dependency_constraint Unsatisfiable = (Nothing, Nothing, Nothing)
-- Because literals are always relations between two meta-variables, we know that the dependency is always going to be the identity.
--build_dependency_constraint (Lcstr ml1 ml2) = (Just (([dep1],dep2),LHDep (\x -> x)),Just (([dep2],dep1),LHDep (\x -> x))) 
--							where u = extract_unifier_constraint (Lcstr ml1 ml2); s1 = build_dependency_side_lit (extract_inner_literal ml1); s2 = build_dependency_side_lit (extract_inner_literal ml2); dep1 = add_unifier_dependent u (case s1 of {DDep dep -> dep}); dep2 = add_unifier_dependent u (case s2 of {DDep dep -> dep})
build_dependency_constraint (Lcstr ml1 ml2) = (Nothing, Nothing, Nothing)
build_dependency_constraint (Tcstr mt1 mt2) = case s1 of
						{
							DDep dep1 -> case s2 of
							{
								-- Two dependents. Build a symmetric dependency with the identity (first and only term).
								--DDep dep2 -> (Just (([add_unifier_dependent u dep1],add_unifier_dependent u dep2),THDep (\ts -> (head ts))),Just (([add_unifier_dependent u dep2],add_unifier_dependent u dep1),THDep (\ts -> (head ts))));
								-- Two dependents. This is an equivalence class. Deal with this somewhere else.
								DDep dep2 -> (Nothing,Nothing,Nothing);
								-- A dependent and a function. A true dependency. Left depends on right.
								DFun dep2s f -> (Nothing,Just ((map (add_unifier_dependent u) dep2s,add_unifier_dependent u dep1),(THDep f)),Nothing);
								DFixedT t -> (Nothing,Nothing,Just (add_unifier_dependent u dep1,(Left t)))
							};
							DFun dep1s f -> case s2 of
							{
								-- A dependent and a function. A true dependency. Left depends on right.
								DDep dep2 -> (Just ((map (add_unifier_dependent u) dep1s,add_unifier_dependent u dep2),(THDep f)),Nothing,Nothing);
								-- It should not be possible that there is two functions, this means simplification is wrong. If this happens, forget about it.
								-- Similarly, if a function equals a value there is some unsatisfiability or some wrong simplification.
								-- We return no dependency and hope the unsatisfiability is caught later.
								DFun _ _ -> (Nothing,Nothing,Nothing);
								DFixedT _ -> (Nothing,Nothing,Nothing)
							};
							DFixedT t -> case s2 of
							{
								DDep dep2 -> (Nothing,Nothing,Just (add_unifier_dependent u dep2,(Left t)));
								DFixedT _ -> (Nothing,Nothing,Nothing)
							}
						}						
						where u = extract_unifier_constraint (Tcstr mt1 mt2); s1 = build_dependency_side_term (extract_inner_term mt1); s2 = build_dependency_side_term (extract_inner_term mt2)

apply_dependency_constraint_helper :: DependencyGraph -> Maybe (([Dependent],Dependent),HorizontalDependency) -> DependencyGraph
apply_dependency_constraint_helper g Nothing = g
apply_dependency_constraint_helper g (Just ((ss,t),dep)) = add_hdep (foldl add_node (add_node g t) ss) dep ss t

apply_dependency_constraint_helper_2 :: DependencyGraphSolution -> Maybe (Dependent,Either Term Literal) -> DependencyGraphSolution
apply_dependency_constraint_helper_2 sol Nothing = sol
apply_dependency_constraint_helper_2 sol (Just v) = v:sol

apply_dependency_constraint_helper_3 :: DependencyGraph -> Maybe (Dependent,Either Term Literal) -> DependencyGraph
apply_dependency_constraint_helper_3 g Nothing = g
apply_dependency_constraint_helper_3 g (Just (d,v)) = add_node g d

-- IMPORTANT: We are not really being correct here. We know that whenever this generates new values, we will recheck all dependents, so we do not return dependents for which a value has been found, merely add it to the solution.
apply_dependency_constraint :: PartiallySolvedDGraph -> Constraint -> PartiallySolvedDGraph
apply_dependency_constraint (g,sol,ueqs) c = (apply_dependency_constraint_helper (apply_dependency_constraint_helper (apply_dependency_constraint_helper_3 g val) ltr) rtl,apply_dependency_constraint_helper_2 sol val,ueqs) where (ltr,rtl,val) = build_dependency_constraint c

-- Build equivalence classes.
-- If the constraint is an equivalence, updates the equivalence classes. Otherwise, does nothing.
update_equivalence_classes :: DependencyGraph -> Constraint -> DependencyGraph
-- Because literals are always relations between two meta-variables, we know that the dependency is always going to be the identity.
update_equivalence_classes g Unsatisfiable = g
update_equivalence_classes g (Lcstr ml1 ml2) = (add_eqdep (add_node (add_node g dep1) dep2) dep1 dep2)
							where u = extract_unifier_constraint (Lcstr ml1 ml2); s1 = build_dependency_side_lit (extract_inner_literal ml1); s2 = build_dependency_side_lit (extract_inner_literal ml2); dep1 = add_unifier_dependent u (case s1 of {DDep dep -> dep}); dep2 = add_unifier_dependent u (case s2 of {DDep dep -> dep})
-- If they are terms, it is going to be an equivalence if they are both dependents.
update_equivalence_classes g (Tcstr mt1 mt2) = case s1 of
						{
							DDep dep1 -> case s2 of
							{
								DDep dep2 -> update_equivalence_classes_helper g (add_unifier_dependent u dep1) (add_unifier_dependent u dep2);
								DFun _ _ -> g;
								DFixedT _ -> g;
							};
							DFun _ _ -> g;
							DFixedT _ -> g
						}
						where u = extract_unifier_constraint (Tcstr mt1 mt2); s1 = build_dependency_side_term (extract_inner_term mt1); s2 = build_dependency_side_term (extract_inner_term mt2)
update_equivalence_classes_helper :: DependencyGraph -> Dependent -> Dependent -> DependencyGraph
update_equivalence_classes_helper g d1 d2 = add_eqdep (add_node (add_node g d1) d2) d1 d2

-- Builds a vertical dependency from the first dependent to the second one.
is_dependent_term :: Dependent -> Bool
is_dependent_term (DVar _) = True
is_dependent_term (DMetaT _) = True
is_dependent_term (DMetaL _) = False
is_dependent_term (DRec _ d) = is_dependent_term d

is_dependent_metavar :: Dependent -> Bool
is_dependent_metavar (DVar _) = False
is_dependent_metavar (DMetaT _) = True
is_dependent_metavar (DMetaL _) = True
is_dependent_metavar (DRec _ d) = is_dependent_metavar d

-- Only defined when it actually is a meta-variable.
extract_metavar_dependent :: Dependent -> Metavariable
extract_metavar_dependent (DMetaT mv) = mv
extract_metavar_dependent (DMetaL mv) = mv
extract_metavar_dependent (DRec _ d) = extract_metavar_dependent d

-- Just one unifier
is_dependent_single :: Dependent -> Bool
is_dependent_single (DVar _) = False
is_dependent_single (DMetaT _) = False
is_dependent_single (DMetaL _) = False
is_dependent_single (DRec _ (DVar _)) = True
is_dependent_single (DRec _ (DMetaT _)) = True
is_dependent_single (DRec _ (DMetaL _)) = True
is_dependent_single (DRec _ (DRec _ _)) = False

maybe_add_vertical_dependency :: DependencyGraph -> Dependent -> Maybe (Dependent,VerticalDependency) -> DependencyGraph
maybe_add_vertical_dependency g _ Nothing = g
maybe_add_vertical_dependency g d1 (Just (d2,d)) = add_vdep (add_node g d2) d d2 d1

build_vertical_dependency :: Dependent -> Maybe (Dependent,VerticalDependency)
build_vertical_dependency (DVar _) = Nothing
build_vertical_dependency (DMetaT _) = Nothing
build_vertical_dependency (DMetaL _) = Nothing
build_vertical_dependency (DRec u x) | (is_dependent_term x) = Just (x, TVDep (\t -> MTermR u (MTermT t)))
build_vertical_dependency (DRec u x) | (not (is_dependent_term x)) = Just (x, LVDep (\l -> MLitR u (MLitL l)))

calculate_vertical_dependencies :: DependencyGraph -> DependencyGraph
calculate_vertical_dependencies g = calculate_vertical_dependencies_rec g (nodes g)

calculate_vertical_dependencies_step :: DependencyGraph -> [DependencyNode] -> (DependencyGraph,[DependencyNode])
calculate_vertical_dependencies_step g (n:ns) = (g2, calculate_vertical_dependencies_step_helper g2 ns md) where md = build_vertical_dependency (get_dependent n); g2 = maybe_add_vertical_dependency g (get_dependent n) md

calculate_vertical_dependencies_step_helper :: DependencyGraph -> [DependencyNode] -> Maybe (Dependent,VerticalDependency) -> [DependencyNode]
calculate_vertical_dependencies_step_helper _ l Nothing = l
calculate_vertical_dependencies_step_helper g l (Just (d,_)) = ((find_node g d):l)
--calculate_vertical_dependencies_step_helper g l (Just (d,_)) = if (isNothing nmb) then l else ((find_node g d):l) where nmb = find_node_maybe g d
calculate_vertical_dependencies_rec :: DependencyGraph -> [DependencyNode] -> DependencyGraph
calculate_vertical_dependencies_rec g [] = g
calculate_vertical_dependencies_rec g (n:ns) = calculate_vertical_dependencies_rec rg rns where step = calculate_vertical_dependencies_step g (n:ns); rg = case step of {(x,_) -> x}; rns = case step of {(_,x) -> x}


update_graph_with_constraint :: PartiallySolvedDGraph -> Constraint -> PartiallySolvedDGraph
update_graph_with_constraint gsol c = (calculate_vertical_dependencies (update_equivalence_classes rg c),rsol,rueqs) where (rg,rsol,rueqs) = apply_dependency_constraint gsol c

-- A bit of efficiency. We only calculate the vertical dependencies once.
update_graph_with_constraints :: PartiallySolvedDGraph -> [Constraint] -> PartiallySolvedDGraph
update_graph_with_constraints gsol cs = (calculate_vertical_dependencies (foldl update_equivalence_classes rg cs),rsol,rueqs) where (rg,rsol,rueqs) = foldl apply_dependency_constraint gsol cs

update_graph_with_constraints_fsol :: FullSolution -> [Constraint] -> FullSolution
update_graph_with_constraints_fsol (mvs,mveqs,(inst,cs),gsol) ncs | (elem Unsatisfiable ncs) || (elem Unsatisfiable cs) = (mvs,mveqs,(inst,[Unsatisfiable]),gsol)
update_graph_with_constraints_fsol (mvs,mveqs,(inst,cs),gsol) ncs = (mvs,mveqs,(inst,[]),update_graph_with_constraints gsol (cs++ncs))

-- For usage from outside this module.
update_graph_with_constraints_and_propagate :: ExtendedSignature -> FullSolution -> [Constraint] -> FullSolution
update_graph_with_constraints_and_propagate sig (mvs,mveqs,(inst,ocs),(g,sol,ueqs)) cs = clean_dep_graph_fs (update_graph_all sig (mvs,mveqs,(inst,ucs),(ug,usol,uueqs)) new []) where (umvs,umveqs,(uinst,ucs),(ug,usol,uueqs)) = update_graph_with_constraints_fsol (mvs,mveqs,(inst,ocs),(g,sol,ueqs)) cs; new = maybe_sol_from_list (ug,usol,uueqs) (all_eq ug (map (get_dependent) (nodes ug)))

build_graph_from_constraints :: [Constraint] -> PartiallySolvedDGraph
build_graph_from_constraints cs = update_graph_with_constraints (empty_graph,[],[]) cs

type FreshVariables = (Unifier -> [Variable])

-----------------------------------------
-- IMPORTANT: For now, we go without possible horizontal dependencies.
-- I believe this should work without them, by encoding vertical dependencies properly, using inverse unifiers on meta-variables and updating the graph adequately.
-- But we keep the partial code in case we decide to go back to it.
-----------------------------------------

-- This function is to be run for each pair (u,v) of unifiers where u > v
-- Gives two sets: The set of existing nodes at that level corresponding to application over fresh variables, and the set of nodes that could possibly have horizontal dependencies with them.
-- NOTE: This function could possibly be made a bit more efficient if all sets are calculated at once, but it seems complicated and possibly not better.
--get_unif_phdep_class :: DependencyGraph -> FreshVariables -> Unifier -> Unifier -> ([Dependent],[Dependent])
--get_unif_phdep_class g fv u v = get_unif_phdep_class_helper fv u v (map get_dependent (nodes g))

--get_unif_phdep_class_helper :: FreshVariables -> Unifier -> Unifier -> [Dependent] -> ([Dependent],[Dependent])
--get_unif_phdep_class_helper _ _ _ [] = ([],[])
-- If it does not have a unifier, it surely is not in the class.
--get_unif_phdep_class_helper u v fv ((DVar _):ds) = get_unif_phdep_class_helper u v fv ds
--get_unif_phdep_class_helper u v fv ((DMetaT _):ds) = get_unif_phdep_class_helper u v fv ds
--get_unif_phdep_class_helper u v fv ((DMetaL _):ds) = get_unif_phdep_class_helper u v fv ds
-- If the unifier is not the one we are looking for, then it is not at this level.
--get_unif_phdep_class_helper u v fv ((DRec w x):ds) | not (u == w) = get_unif_phdep_class_helper u v fv ds
-- If it's u x where x is a variable which is NOT fresh after v, then it has no dependencies.
--get_unif_phdep_class_helper u v fv ((DRec w (DVar x)):ds) | (u == w) && (not (elem x (fv v))) = get_unif_phdep_class_helper u v fv ds
-- If it's u x where x is a variable which is fresh after v, then it is in the first set.
--get_unif_phdep_class_helper u v fv ((DRec w (DVar x)):ds) | (u == w) && (elem x (fv v)) = ((DRec w (DVar x)):(fst r),(snd r)) where r = get_unif_phdep_class_helper u v fv ds
-- If it's u X where X is a meta-variable, then it has no dependencies (of the unifier type).
--get_unif_phdep_class_helper u v fv ((DRec w (DMetaT _)):ds) | (u == w) = get_unif_phdep_class_helper u v fv ds
--get_unif_phdep_class_helper u v fv ((DRec w (DMetaL _)):ds) | (u == w) = get_unif_phdep_class_helper u v fv ds
-- If it's u v A for any meta-term\literal A, then it is in the second set.
--get_unif_phdep_class_helper u v fv ((DRec w (DRec o x)):ds) | (u == w) && (o == v) = ((fst r),(DRec v (DRec w x)):(snd r)) where r = get_unif_phdep_class_helper u vs ds
-- If it's u w A , where w != v, then it has no dependencies.
--get_unif_phdep_class_helper u v fv ((DRec w (DRec o x)):ds) | (u == w) && (not (o == v)) = get_unif_phdep_class_helper u v fv ds

--build_unif_phdep :: DependencyGraph -> FreshVariables -> Unifier -> Unifier -> [PHDependencyEdge]
--build_unif_phdep g fv u v = build_unif_phdep_helper (get_unif_phdep_class g fv u v)

--build_unif_phdep_helper :: ([Dependent],[Dependent]) -> [PHDependencyEdge]
--build_unif_phdep_helper (vs,ds) = concat (map (build_unif_phdep_helper_one vs) ds)

--build_unif_phdep_helper_one :: [Dependent] -> Dependent -> [PHDependencyEdge]
--build_unif_phdep_helper_one vs d | (is_dependent_term d) = ((build_unif_phdep_fromvars vs d):(map (build_unif_phdep_tovar d) vs))
-- TODO: Other cases

-- This is very complicated.
-- Think with an example: If arguments are [v xu, v yu] and vux; we are building an encoding of a possible horizontal dependency from v xu and v yu towards vux,
-- which says that, for example,
-- if u x is learned to be f(xu,yu,zu) (this would be the second argument of PTHDep), and 
-- then we learned that v xu = xuv, v yu = g(xuv) and v zu = xuv (this would be the argument of HDep, which is the result of PTHDep, the last argument here), THEN,
-- we know that vux would be f(xuv,g(xuv),xuv).

-- Note that zu is not part of the initial arguments: This means that this node was not present in the graph. For efficiency, we only considers nodes which have other reasons to be in the graph.

-- The way to build this in general is the following:
--	- We build a function with five arguments.
--	- We take the fourth argument, this indicates the structure of the result.
--	- We need to apply to this third fourth the substitution given as the fifth argument
--	- The variables for which this last substitution corresponds are the ones given by the third argument.
--	- The first argument indicates which nodes the dependency goes from, and the second one which node it goes to. 
--		These may possibly not include nodes not in the graph which will, eventually, affect the result. This is not relevant, those dependencies will be updated in time (via a vertical dependency).
--		The purposes of the possible dependency are two: Make it explicit that the node is not a root, and know how to locally update the graph as more information is gathered.
--	
--build_unif_phdep_fromvars :: [Dependent] -> Dependent -> PHDependencyEdge
--build_unif_phdep_fromvars vs d = PTHDep (\ts -> \t -> THDep (\fts -> ))

--build_unif_phdep_tovar :: Dependent -> Dependent -> PHDependencyEdge

--((PTHDep (\ts -> \t -> THDep (\)):(map (\v -> PTHDep (\ts -> \t -> )) vs))

-- data PossibleHorizontalDependency = PTHDep ([Term] -> Term -> [HorizontalDependency]) | PLTHDep ([Term] -> Literal -> [HorizontalDependency]) | PLHDep (Literal -> Literal -> [HorizontalDependency])
-- data HorizontalDependency = THDep ([Term] -> Term) | LTHDep ([Term] -> Literal) | LHDep (Literal -> Literal)

-------------------------------------
-- END OF POSSIBLE HORIZONTAL DEPENDENCIES DEPRECATED CODE
-------------------------------------


-- Simplify dependencies to obtain unifier values.
-- The first parameter is the term to which the unifier is applied and the second parameter the result of the unifier.
-- Purposely not defined for meta-variables.
-- When the substitution is impossible (e.g. if u f(x1,x2) = x3 or u f(x1,x2) = g(x3,x4), we return Nothing.
simpl_dep_term :: Term -> Term -> Maybe UnifierDescription
simpl_dep_term (TVar v1) t = Just [UV v1 t]
simpl_dep_term (TFun f1 t1s) (TFun f2 t2s) | f1 == f2 = maybe_concat (map (\pair -> simpl_dep_term (fst pair) (snd pair)) (zip t1s t2s))
simpl_dep_term _ _ = Nothing

simpl_dep_lit :: Literal -> Literal -> Maybe UnifierDescription
simpl_dep_lit (Lit p t1s) (Lit q t2s) | p == q = maybe_concat (map (\pair -> simpl_dep_term (fst pair) (snd pair)) (zip t1s t2s))
simpl_dep_lit _ _ = Nothing

-- Inverting a unifier
-- Variables in the domain of the unifier that do not appear in the description are indicated through the first parameter, and these are included as possible solutions wherever they could be.
-- But we assume that those variables necessarily go to their canonical variables, and therefore are only included as possible solutions in that case, and only when they have no collision with
-- the unifier description.
invert_unifier_term :: Int -> Unifier -> [Variable] -> UnifierDescription -> Term -> [(Term,UnifierDescription)]
invert_unifier_term nvars u fvs ud (TVar v) = invert_unifier_variable nvars u (filter (not . (canonic_has_collision nvars u ud)) fvs) ud v
invert_unifier_term nvars u fvs ud (TFun f ts) = invert_unifier_function nvars u (filter (not . (canonic_has_collision nvars u ud)) fvs) ud f ts
-- Meta-variable should never appear, we purposely leave this case unspecified.

invert_unifier_variable :: Int -> Unifier -> [Variable] -> UnifierDescription -> Variable -> [(Term,UnifierDescription)]
invert_unifier_variable nvars u fvs [] v | elem pre fvs = [(TVar pre,[UV pre (TVar v)])] where pre = get_preimage_var nvars u v
invert_unifier_variable nvars u fvs [] v = []
-- A variable that leads to the same variable, that's what we're looking for.
--invert_unifier_variable fvs ((UV v1 (TVar v2)):ud) v3 | v2 == v3 = ((TVar v1,[]):(invert_unifier_variable fvs ud v3))
invert_unifier_variable nvars u fvs ((UV v1 (TVar v2)):ud) v3 | v2 == v3 = ((TVar v1,[]):(invert_unifier_variable nvars u fvs ud v3))
-- A variable leading to another variable, not good.
invert_unifier_variable nvars u fvs ((UV v1 (TVar v2)):ud) v3 | v2 /= v3 = invert_unifier_variable nvars u fvs ud v3
-- A variable leading to something which is not a variable, not good.
invert_unifier_variable nvars u fvs ((UV v1 _):ud) v3 = invert_unifier_variable nvars u fvs ud v3

invert_unifier_function :: Int -> Unifier -> [Variable] -> UnifierDescription -> Function -> [Term] -> [(Term,UnifierDescription)]
invert_unifier_function nvars u fvs ud f ts = (invert_unifier_function_direct ud f ts) ++ (invert_unifier_function_rec nvars u fvs ud f ts)

-- A variable that directly generates the given term.
invert_unifier_function_direct :: UnifierDescription -> Function -> [Term] -> [(Term,UnifierDescription)]
invert_unifier_function_direct [] _ _ = []
-- NO FREE VARIABLES HERE!
--invert_unifier_function_direct (fv:fvs) [] f ts = ((TVar fv,[UV fv (TFun f ts)]):(invert_unifier_function_direct fvs [] f ts))
-- A variable that leads to the same function with exactly the same terms, that's what we're looking for.
invert_unifier_function_direct ((UV v1 (TFun f1 t1s)):ud) f2 t2s | (f1 == f2) && (t1s == t2s) = ((TVar v1,[]):(invert_unifier_function_direct ud f2 t2s))
-- A variable that leads to a different function or different terms, not good.
invert_unifier_function_direct ((UV v1 (TFun f1 t1s)):ud) f2 t2s | not ((f1 == f2) && (t1s == t2s)) = invert_unifier_function_direct ud f2 t2s
-- A variable that leads to something which is not a function, not good.
invert_unifier_function_direct ((UV v1 _):ud) f ts = invert_unifier_function_direct ud f ts

-- If we already had a function, where each subterm was sent to the new corresponding term, then that is an inverse. Gather all combinations.
invert_unifier_function_rec :: Int -> Unifier -> [Variable] -> UnifierDescription -> Function -> [Term] -> [(Term,UnifierDescription)]
invert_unifier_function_rec nvars u fvs ud f ts = filter invert_unifier_function_rec_helper (map (\tc2s -> (TFun f (map fst tc2s),concat (map snd tc2s))) (combinations (map (invert_unifier_term nvars u fvs ud) ts)))

invert_unifier_function_rec_helper :: (t,UnifierDescription) -> Bool
invert_unifier_function_rec_helper (_,ud) = is_unif_desc_consistent ud

-- It needs to be the predicate with inverse subterms
invert_unifier_literal :: Int -> Unifier -> [Variable] -> UnifierDescription -> Literal -> [(Literal,UnifierDescription)]
invert_unifier_literal nvars u fvs ud (Lit p ts) = filter invert_unifier_function_rec_helper (map (\tc2s -> (Lit p (map fst tc2s),concat (map snd tc2s))) (combinations (map (invert_unifier_term nvars u fvs ud) ts)))

-- The variable is the target variable.
canonic_has_collision :: Int -> Unifier -> UnifierDescription -> Variable -> Bool
canonic_has_collision nvars u uds v = any (\uv -> case uv of {UV _ t -> term_contains_variable t img}) uds where img = get_image_var nvars u v

term_contains_variable :: Term -> Variable -> Bool
term_contains_variable (TVar v1) v2 | v1 == v2 = True
term_contains_variable (TVar v1) v2 = False
term_contains_variable (TMeta _) v = False
term_contains_variable (TFun _ ts) v = any (\t -> term_contains_variable t v) ts

is_unif_desc_consistent :: UnifierDescription -> Bool
is_unif_desc_consistent [] = True
is_unif_desc_consistent ((UV x _):ud) = (all (\uv -> case uv of {UV y _ -> x /= y}) ud) && (is_unif_desc_consistent ud)

combinations :: [[t]] -> [[t]]
combinations [] = [[]]
combinations (xs:xss) = combinations_helper xs (combinations xss)

combinations_helper :: [t] -> [[t]] -> [[t]]
combinations_helper xs xss = concat (map (combinations_helper_2 xss) xs)

combinations_helper_2 :: [[t]] -> t -> [[t]]
combinations_helper_2 xss x = map (\xs -> (x:xs)) xss


-- There are three notions of solution here. The one we are interested in in the end is a meta-variable instantiation. 
-- But, at the same time, this involves solving the unifiers; this is the second notion of solution.
-- Finally, the dependency graph itself can be "solved" by finding out actual values for the nodes in the graph.
-- Our intention is to calculate the third one and then obtain the other two from that (possibly by having left some clues on the way).
-- A (possibly partial) solution to a dependency graph is an assignation of a term/literal to each node (dependent).
type DependencyGraphSolution = [(Dependent,Either Term Literal)]

show_dgsol :: DependencyGraphSolution -> String
show_dgsol [] = ""
show_dgsol (d:ds) = (show_single_dgsol d) ++ ", " ++ (show_dgsol ds)

show_single_dgsol :: (Dependent,Either Term Literal) -> String
show_single_dgsol (d,Left t) = (show d) ++ " = " ++ (show t)
show_single_dgsol (d,Right l) = (show d) ++ " = " ++ (show l)

apply_graph_solution :: DependencyGraphSolution -> Dependent -> Maybe (Either Term Literal)
apply_graph_solution [] _ = Nothing
apply_graph_solution ((d1,v):ds) d2 | d1 == d2 = Just v
apply_graph_solution ((d1,v):ds) d2 = apply_graph_solution ds d2

apply_graph_solution_term :: DependencyGraphSolution -> Metaterm -> Metaterm
apply_graph_solution_term sol (MTermT t) = MTermT t
apply_graph_solution_term sol (MTermF f mts) = MTermF f (map (apply_graph_solution_term sol) mts)
--apply_graph_solution_term sol (MTermR u mt) = case mb_dep of {Nothing -> MTermR u rmt; Just dep -> case (apply_graph_solution sol dep) of {Nothing -> MTermR u rmt; Just (Left t) -> MTermT t}} where rmt = apply_graph_solution_term sol mt; mb_dep = depnode_from_metaterm rmt
apply_graph_solution_term sol (MTermR u mt) = case mb_dep of {Nothing -> rmt; Just dep -> case (apply_graph_solution sol dep) of {Nothing -> rmt; Just (Left t) -> MTermT t}} where rimt = apply_graph_solution_term sol mt; rmt = (MTermR u rimt); mb_dep = depnode_from_metaterm rmt

apply_graph_solution_lit :: DependencyGraphSolution -> Metaliteral -> Metaliteral
apply_graph_solution_lit sol (MLitL l) = MLitL l
apply_graph_solution_lit sol (MLitP p mts) = MLitP p (map (apply_graph_solution_term sol) mts)
--apply_graph_solution_lit sol (MLitR u ml) = case mb_dep of {Nothing -> MLitR u rml; Just dep -> case (apply_graph_solution sol dep) of {Nothing -> MLitR u rml; Just (Right l) -> MLitL l}} where rml = apply_graph_solution_lit sol ml; mb_dep = depnode_from_metalit rml
apply_graph_solution_lit sol (MLitR u ml) = case mb_dep of {Nothing -> rml; Just dep -> case (apply_graph_solution sol dep) of {Nothing -> rml; Just (Right l) -> MLitL l}} where riml = apply_graph_solution_lit sol ml; rml = (MLitR u riml); mb_dep = depnode_from_metalit rml

apply_graph_solution_cstr :: DependencyGraphSolution -> Constraint -> Constraint
apply_graph_solution_cstr sol (Tcstr mt1 mt2) = Tcstr (apply_graph_solution_term sol mt1) (apply_graph_solution_term sol mt2)
apply_graph_solution_cstr sol (Lcstr ml1 ml2) = Lcstr (apply_graph_solution_lit sol ml1) (apply_graph_solution_lit sol ml2)

-- This version actually keeps track of the last unifier and passes it down so that if a whole term or literal can be solved within with the inner-most unifier, it does so.
apply_graph_solution_term_full :: DependencyGraphSolution -> Metaterm -> Metaterm
apply_graph_solution_term_full sol (MTermT t) = MTermT t
apply_graph_solution_term_full sol (MTermF f mts) = MTermF f (map (apply_graph_solution_term_full sol) mts)
--apply_graph_solution_term sol (MTermR u mt) = case mb_dep of {Nothing -> MTermR u rmt; Just dep -> case (apply_graph_solution sol dep) of {Nothing -> MTermR u rmt; Just (Left t) -> MTermT t}} where rmt = apply_graph_solution_term sol mt; mb_dep = depnode_from_metaterm rmt
apply_graph_solution_term_full sol (MTermR u mt) = case total of {Just t -> MTermT t; Nothing -> case mb_dep of {Nothing -> rmt; Just dep -> case (apply_graph_solution sol dep) of {Nothing -> rmt; Just (Left t) -> MTermT t}}} where total = apply_graph_solution_term_full_helper sol u mt; rimt = apply_graph_solution_term_full sol mt; rmt = (MTermR u rimt); mb_dep = depnode_from_metaterm rmt

-- This one solves it retorting to the last unifier, and only if it does not have any additional unifiers.
apply_graph_solution_term_full_helper :: DependencyGraphSolution -> Unifier -> Metaterm -> Maybe Term
apply_graph_solution_term_full_helper sol u (MTermT (TVar x)) = case (apply_graph_solution sol dep) of {Nothing -> Nothing; Just (Left t) -> Just t} where dep = (DRec u (DVar x))
apply_graph_solution_term_full_helper sol u (MTermT (TFun f ts)) = if (all isJust ress) then Just (TFun f (map fromJust ress)) else Nothing where mts = map MTermT ts; ress = map (apply_graph_solution_term_full_helper sol u) mts
apply_graph_solution_term_full_helper sol u (MTermT (TMeta m)) = Nothing
apply_graph_solution_term_full_helper sol u (MTermF f mts) = if (all isJust ress) then Just (TFun f (map fromJust ress)) else Nothing where ress = map (apply_graph_solution_term_full_helper sol u) mts
apply_graph_solution_term_full_helper sol u (MTermR _ _) = Nothing

apply_graph_solution_lit_full :: DependencyGraphSolution -> Metaliteral -> Metaliteral
apply_graph_solution_lit_full sol (MLitL l) = MLitL l
apply_graph_solution_lit_full sol (MLitP p mts) = MLitP p (map (apply_graph_solution_term_full sol) mts)
--apply_graph_solution_lit sol (MLitR u ml) = case mb_dep of {Nothing -> MLitR u rml; Just dep -> case (apply_graph_solution sol dep) of {Nothing -> MLitR u rml; Just (Right l) -> MLitL l}} where rml = apply_graph_solution_lit sol ml; mb_dep = depnode_from_metalit rml
apply_graph_solution_lit_full sol (MLitR u ml) = case total of {Just l -> MLitL l; Nothing -> case mb_dep of {Nothing -> rml; Just dep -> case (apply_graph_solution sol dep) of {Nothing -> rml; Just (Right l) -> MLitL l}}} where total = apply_graph_solution_lit_full_helper sol u ml; riml = apply_graph_solution_lit_full sol ml; rml = (MLitR u riml); mb_dep = depnode_from_metalit rml

apply_graph_solution_lit_full_helper :: DependencyGraphSolution -> Unifier -> Metaliteral -> Maybe Literal
apply_graph_solution_lit_full_helper sol u (MLitL (Lit p ts)) = if (all isJust ress) then Just (Lit p (map fromJust ress)) else Nothing where mts = map MTermT ts; ress = map (apply_graph_solution_term_full_helper sol u) mts
apply_graph_solution_lit_full_helper sol u (MLitL (LitM m)) = Nothing
apply_graph_solution_lit_full_helper sol u (MLitP p mts) = if (all isJust ress) then Just (Lit p (map fromJust ress)) else Nothing where ress = map (apply_graph_solution_term_full_helper sol u) mts
apply_graph_solution_lit_full_helper sol u (MLitR _ _) = Nothing



--empty_graph_solution :: DependencyGraph -> DependencyGraphSolution
--empty_graph_solution _ = []

--single_graph_solution :: Dependent -> (Either Term Literal) -> DependencyGraphSolution
--single_graph_solution d1 r d2 | d1 == d2 = Just r
--single_graph_solution d1 r d2 | d1 /= d2 = Nothing

-- The first one is given priority
--merge_solutions :: DependencyGraphSolution -> DependencyGraphSolution -> DependencyGraphSolution
--merge_solutions s1 s2 d = case (s1 d) of {Just x -> Just x; Nothing -> (s2 d)}

type PartiallySolvedDGraph = (DependencyGraph,DependencyGraphSolution,[UnifierEquation])

-- The algorithm is as follows:
--		- We have a graph.
--		- At each step, we choose a node to give a value to. This may be because it is a root, or because we made a choice (in which case the algorithm gives several solutions).
--		- After giving a value to the node, we update our current solution for the graph, and the mapping of meta-variables with unifiers.
--		- Furthermore, we need to update the graph, possibly changing it, and updating the solution alongside it.
--		- When all nodes have values, we found a solution, backtrack to find the instantiation and the unifier solution.

-- Update a graph when a node is given a value. Removes the node from the graph, and updates the rest of the graph accordingly, and updates the solution.
-- It returns the new dependency graph, the new solution and a list of other updates that can be made as a cascading consequence of this one.
--update_graph_from_value :: PartiallySolvedDGraph -> Dependent -> (Either Term Literal) -> (PartiallySolvedDGraph,[(Dependent,Either Term Literal)])
-- Take all dependencies going out of the node, and update through them.
--update_graph_from_value (g,sol) d v = ??? 

-- Updating the solution is done here. But it does not propagate. That's why we need to keep record of which nodes to update, so that we can propagate later on.
--do_one_update_to_graph :: (PartiallySolvedDGraph -> t -> (DependencyGraph,[Dependent])) -> (PartiallySolvedDGraph,[(Dependent,Either Term Literal)]) -> t -> (PartiallySolvedDGraph,[(Dependent,Either Term Literal)])
--do_one_update_to_graph f ((g,sol),l) x = ((fg,sol_from_list (l ++ new)),l ++ new) where fgnew = f (g,sol) x; fg = fst fgnew; pos = snd fgnew; new = maybe_sol_from_list (fg,sol) pos
thd :: (a,b,c) -> c
thd (_,_,x) = x

get_graph :: FullSolution -> DependencyGraph
get_graph (_,_,(_,_),(g,_,_)) = g

get_gsol :: FullSolution -> PartiallySolvedDGraph
get_gsol (_,_,_,gsol) = gsol

get_instantiation :: FullSolution -> Instantiation
get_instantiation (_,_,(inst,_),_) = inst

dep_in_graph :: DependencyGraph -> Dependent -> Bool
dep_in_graph g d = elem d (map get_dependent (nodes g))

clean_dep_graph_fs :: FullSolution -> FullSolution
clean_dep_graph_fs (mvs,eqs,(inst,cs),psg) = (mvs,eqs,(inst,cs),clean_dep_graph psg)

-- Removes nodes for which we have a solution from the graph, and such that all elements that vertically depend on it have a solution.
clean_dep_graph :: PartiallySolvedDGraph -> PartiallySolvedDGraph
clean_dep_graph (g,sol,ueqs) = (remove_nounif sol ueqs (clean_dep_graph_helper sol ueqs g (map fst sol)),sol,ueqs)

clean_dep_graph_helper :: DependencyGraphSolution -> [UnifierEquation] -> DependencyGraph -> [Dependent] -> DependencyGraph
clean_dep_graph_helper sol ueqs g [] = g
clean_dep_graph_helper sol ueqs g (d:ds) | not (dep_in_graph g d) = clean_dep_graph_helper sol ueqs g ds
clean_dep_graph_helper sol ueqs g (d:ds) | can_remove (g,sol,ueqs) d = clean_dep_graph_helper sol ueqs (remove_node g d) ds
clean_dep_graph_helper sol ueqs g (d:ds) = clean_dep_graph_helper sol ueqs g ds

remove_nounif :: DependencyGraphSolution -> [UnifierEquation] -> DependencyGraph -> DependencyGraph
remove_nounif sol ueqs g = remove_nounif_helper sol ueqs g (map get_dependent (nodes g))

remove_nounif_helper :: DependencyGraphSolution -> [UnifierEquation] -> DependencyGraph -> [Dependent] -> DependencyGraph
remove_nounif_helper sol ueqs g [] = g
remove_nounif_helper sol ueqs g ((DVar v):ds) | can_remove (g,sol,ueqs) (DVar v) = remove_nounif_helper sol ueqs (remove_node g (DVar v)) ds
remove_nounif_helper sol ueqs g ((DMetaT m):ds) | can_remove (g,sol,ueqs) (DMetaT m) = remove_nounif_helper sol ueqs (remove_node g (DMetaT m)) ds
remove_nounif_helper sol ueqs g ((DMetaL m):ds) | can_remove (g,sol,ueqs) (DMetaL m) = remove_nounif_helper sol ueqs (remove_node g (DMetaL m)) ds
remove_nounif_helper sol ueqs g (d:ds) = remove_nounif_helper sol ueqs g ds

can_remove :: PartiallySolvedDGraph -> Dependent -> Bool
can_remove (g,sol,ueqs) d = (is_solved sol d) && (all (can_remove (g,sol,ueqs)) others) where vdeps = get_outgoing_vdeps (find_node g d); others = map get_vtarget vdeps
--can_remove (g,sol,ueqs) d = if (isNothing nmb) then False else ((is_solved sol d) && (all (can_remove (g,sol,ueqs)) others)) where nmb = find_node_maybe g d; vdeps = get_outgoing_vdeps (find_node g d); others = map get_vtarget vdeps

is_solved :: DependencyGraphSolution -> Dependent -> Bool
is_solved sol (DVar _) = True
is_solved sol (DMetaT _) = True
is_solved sol (DMetaL _) = True
is_solved sol d = (isJust (apply_graph_solution sol d))

-- Takes the dependency graph solution and transforms it into unifier values and instantiations, and then removes the solved nodes from the graph.
-- Therefore, it assumes that no more propagation can be carried out from those solutions inside the graph.
--absorb_graph_solution :: FullSolution -> FullSolution
--absorb_graph_solution (mvs,(inst,cs),(g,sol)) = 

-- We do not do this yet, only once all the dependents in the graph have been removed.
--unifier_desc_from_graph :: PartiallySolvedDGraph -> Unifier -> UnifierDescription
--unifier_desc_from_graph (g,sol) u = unifier_desc_from_graph_helper (map get_dependent (nodes g)) u (sol g)

--unifier_desc_from_graph_helper :: [Dependent] -> Unifier -> DependencyGraphSolution -> UnifierDescription
--unifier_desc_from_graph_helper [] _ _ = []
--unifier_desc_from_graph_helper ((DRec u (DVar x)):ds) v sol | u == v = case (sol d) of {Nothing -> rec; Just (Left t) -> (UV x t):rec} where d = (DRec u (DVar x)); rec = --unifier_desc_from_graph_helper ds v sol
--unifier_desc_from_graph_helper (d:ds) v sol = unifier_desc_from_graph_helper ds v sol

-- This may add meta-variables and partial instantiations between them.
--inst_from_graph :: FullSolution -> Unifier -> Enumeration (h,FullSolution)
--inst_from_graph (mvs,(inst,cs),(g,sol)) = 

--inst_from_graph_helper :: [Dependent] -> Unifier -> FullSolution -> Enumeration (h,FullSolution)
--inst_from_graph_helper [] _ fs = single_enum (no_help fs)
--inst_from_graph_helper ((DRec u (DMetaT x)):ds) v (mv,(inst,cs),(g,sol)) | u == v = case (sol d) of {Nothing -> rec; Just (Left t) -> where d = (DRec u (DMetaT x)); rec = inst_from_graph_helper ds v (mv,(inst,cs),(g,sol))


-- Possible sources of multiforest edges in the middle of the reduction: Actual dependents, fixed values or a function or predicate applied to other pseudodependents.
-- Predicates cannot occur, so we don't consider them.
-- In theory, fixed literals also cannot occur, because they'd have to be metavariables without unifiers, but it's worth keeping around just in case our way to handle metavariables changes.
data PseudoDependent = PDDep Dependent | PDFixedT Term | PDFixedL Literal | PDRecF Function [PseudoDependent] 

instance Show PseudoDependent where
	show (PDDep dep) = show dep
	show (PDFixedT t) = show t
	show (PDFixedL l) = show l
	show (PDRecF f ds) = (show f) ++ "(" ++ (concat (map (\d -> (show d) ++ ",") ds)) ++ ")"

-- We say pseudodependents have a "head" and a "body".
-- The head is the function symbol (in theory also predicate, but that does not happen in practice) that precedes it. At most one. It could be void.
-- The body is the arguments to this head, a set of other pseudodependents.
-- The part that needs to match.
-- We should never get predicates here, really.
-- So it's either a function, or nothing.
data PseudoDependentHead = PDHeadVoid | PDHeadF Function 

isPDHeadVoid :: PseudoDependentHead -> Bool
isPDHeadVoid PDHeadVoid = True
isPDHeadVoid (PDHeadF _) = False

isPDHeadF :: PseudoDependentHead -> Bool
isPDHeadF PDHeadVoid = False
isPDHeadF (PDHeadF _) = True

-- When the head is empty, the body needs to be either a dependent or a fixed variable (or meta-variable, not in theory, but we keep this door open).
data PseudoDependentBody = PDBodyVoidD Dependent | PDBodyVoidV Variable | PDBodyVoidM Metavariable | PDBodyF [PseudoDependent] | PDBodyFixedF [Term] | PDBodySubD Dependent PseudoDependentBody

type PseudoDependentDecomposition = (PseudoDependentHead,PseudoDependentBody)

void_pddepd_decompose :: Dependent -> PseudoDependentDecomposition
void_pddepd_decompose d = (PDHeadVoid,PDBodyVoidD d)

void_pddepv_decompose :: Variable -> PseudoDependentDecomposition
void_pddepv_decompose v = (PDHeadVoid,PDBodyVoidV v)

void_pddepm_decompose :: Metavariable -> PseudoDependentDecomposition
void_pddepm_decompose mv = (PDHeadVoid,PDBodyVoidM mv)

fun_pddep_decompose :: Function -> [PseudoDependent] -> PseudoDependentDecomposition
fun_pddep_decompose f pds = (PDHeadF f,PDBodyF pds)

fun_pddepfix_decompose :: Function -> [Term] -> PseudoDependentDecomposition
fun_pddepfix_decompose f ts = (PDHeadF f,PDBodyFixedF ts)

is_pdep_fixed :: PseudoDependent -> Bool
is_pdep_fixed (PDDep _) = False
is_pdep_fixed (PDFixedT _) = True
is_pdep_fixed (PDFixedL _) = True
is_pdep_fixed (PDRecF _ pds) = all is_pdep_fixed pds

extract_fixed_term_pdep :: PseudoDependent -> Term
extract_fixed_term_pdep (PDFixedT t) = t
extract_fixed_term_pdep (PDRecF f pds) = TFun f (map extract_fixed_term_pdep pds)

decompose_pseudodep :: PseudoDependent -> PseudoDependentDecomposition
decompose_pseudodep (PDDep d) = void_pddepd_decompose d
decompose_pseudodep (PDFixedT (TVar v)) = void_pddepv_decompose v
-- Meta-variables should not appear without unifiers, in theory, but just in case...
decompose_pseudodep (PDFixedT (TMeta mv)) = void_pddepm_decompose mv
decompose_pseudodep (PDFixedT (TFun f ts)) = fun_pddepfix_decompose f ts
-- Predicates do not appear, so we ignore them
-- decompose_pseudodep (PDFixedL (Lit p ts)) = 
decompose_pseudodep (PDFixedL (LitM mv)) = void_pddepm_decompose mv
decompose_pseudodep (PDRecF f pds) | (all is_pdep_fixed pds) = fun_pddepfix_decompose f (map extract_fixed_term_pdep pds)
decompose_pseudodep (PDRecF f pds) = fun_pddep_decompose f pds

-- The difference with normal decomposition is that, if the pseudodependent is a dependent with one incoming dependency, returns the head for that incoming dependency, and a PDBodySubD body with the dependent and the body for the incoming pseudodependent.
-- Functions using this result can use this to know that there is a dependent there, but also know what the actual body of the dependent needs to look like.
decompose_pseudodep_in_graph :: DependencyGraph -> PseudoDependent -> PseudoDependentDecomposition
decompose_pseudodep_in_graph g pd =
	case (decompose_pseudodep pd) of
	{
		(PDHeadVoid,PDBodyVoidD d) -> case (get_subpdep_dependent g (PDDep d)) of {(PDDep d2) -> (PDHeadVoid,PDBodyVoidD d2); otherwise -> decompose_pseudodep_in_graph_helper d otherwise};
		otherwise -> otherwise
	}

decompose_pseudodep_in_graph_helper :: Dependent -> PseudoDependent -> PseudoDependentDecomposition
decompose_pseudodep_in_graph_helper d pd = (rechead,PDBodySubD d recbody) where (rechead,recbody) = decompose_pseudodep pd

-- A pseudodependency essentially represents a dependency which is:
--		- Not totally finished. The sources are connected to pseudodependents which may add more things to it.
--		- May have dependents in the middle. For each dependent, there is one true dependency being built, but we consider the whole thing as one to be able to proceed upwards on one go.
-- The structure represents: The dependent at the target, the last dependency, and the sources of that last dependency, which may recursively be pseudodependencies.
-- The number of pseudodependencyinputs corresponds to the number of TInDependent leaves present in the external dependency, and indicates what to replace each of those with (an actual dependent, or another dependency (a branch)).
-- Base pseudodependency just means identity dependency.
data PseudoDependency = PDependencyBase Dependent | PDependency Dependent TermHorizontalDependency [PseudoDependencyInput]

instance Show PseudoDependency where
	show (PDependencyBase d) = (show d) ++ " <- ()"
	show (PDependency d thdep pins) = (show d) ++ " <- " ++ (show thdep) ++ " || " ++ (show pins)

instance Show PseudoDependencyInput where
	show PDInTip = "*"
	show (PDInBranch dep) = (show dep)

-- The input to a single dependency within a pseudodependency can be either a pseudodependent itself (which we call a "tip"), or another single dependency (with a dependent at its tip) (which we call a "branch")
data PseudoDependencyInput = PDInTip | PDInBranch PseudoDependency

get_pdep_dependent :: PseudoDependency -> Dependent
get_pdep_dependent (PDependencyBase d) = d
get_pdep_dependent (PDependency d _ _) = d

-- Finds all leaves, and then factorizes from every and each of them.
factorize_dgraph_all :: FullSolution -> (FullSolution,[(Dependent,Either Term Literal)])
factorize_dgraph_all fs = foldl factorize_dgraph_all_helper (fs,[]) (find_all_true_leaves (get_graph fs))

-- To fold
factorize_dgraph_all_helper :: (FullSolution,[(Dependent,Either Term Literal)]) -> Dependent -> (FullSolution,[(Dependent,Either Term Literal)])
factorize_dgraph_all_helper (fs,vs) d = (rfs,vs++rvs) where (rfs,rvs) = factorize_dgraph fs d

find_all_true_leaves :: DependencyGraph -> [Dependent]
find_all_true_leaves (DGraph _ _ dag) = filter has_unifier (List.nub (find_all_leaves_dag dag))

factorize_dgraph :: FullSolution -> Dependent -> (FullSolution,[(Dependent,Either Term Literal)])
factorize_dgraph fs d = factorize_dgraph_rec fs (PDependencyBase d) [pdeps] where pdeps = pseudodeps_from_node (get_graph fs) d

-- Possibilities are:
--	- No match: Just add unsatisfiable constraint to the solution and return that.
--	- Match, but conflicting solutions: We have several actual solutions that are not equal. Just add unsatisfiable constraint to the solution and return that.
--	- Match: There might be remaining factorizations to do. When the head is a function.
--		or...
--	- Match: There may not be any remaining factorizations to do. When the head is empty.
--		In any case...
--	- Match: There may be dependents in the middle. If there are, we just add them to the dependency, and create a new incoming dependency for them. This is branching.
--		moreover...
--	- Match: If there are dependents in the middle, and there were values, we need to assign those values to those dependents.
--	- Match: Even if there were no dependents, we need to plug in these values into the dependencies. This is updating.
--
-- Note that before doing any of this, we have to factorize each single pseudodependent, so that possible incoming dependencies to dependents get filtered downwards, and factorized recursively.
factorize_dgraph_rec :: FullSolution -> PseudoDependency -> [[PseudoDependent]] -> (FullSolution,[(Dependent,Either Term Literal)])
factorize_dgraph_rec fs dep pdeps = 
	if (any isNothing matches) 
		then ((mvs,eqs,(inst,Unsatisfiable:cs),(g,sol,ueqs)),[])
		else (if (any isPlentyS sols)
			then ((mvs,eqs,(inst,Unsatisfiable:cs),(g,sol,ueqs)),[])
			else (if (any isPDHeadF heads)
				then (recsol,parcpairs++solpairs++recpairs)
				else (dump_pseudodependency_graph parcsol pdeppr,parcpairs++solpairs)))
	where ((mvs,eqs,(inst,cs),(g,sol,ueqs)),parcpairs) = just_factorize_all_single_dependents fs pdeps;
		matches = map (match_pseudodependents g) pdeps;
		dss = factorize_dgraph_rec_helper_1 matches;
		rg = factorize_add_equivalences g dss;
		eqreps = factorize_dgraph_rec_helper_2 rg dss;
		pdepbr = factorize_introduce_branches dep eqreps;
		sols = factorize_dgraph_rec_helper_4 matches;
		solpairs = factorize_dgraph_rec_helper_6 eqreps sols;
		heads = factorize_dgraph_rec_helper_3 matches;
		tris = (map (\tris -> case tris of {(h,d,v) -> replace_head_thdep h d v}) (zip3 heads eqreps sols));
		pdeppr = factorize_upd_depfun heads eqreps sols pdepbr;		
		parcsol = set_all_solutions (mvs,eqs,(inst,cs),(rg,sol,ueqs)) solpairs;
		recpds = factorize_dgraph_rec_helper_7 (factorize_remove_fixed_values_from_matching tris matches);
		(recsol,recpairs) = factorize_dgraph_rec parcsol pdeppr recpds
	

-- add_eqdep :: DependencyGraph -> Dependent -> Dependent -> DependencyGraph
-- match_pseudodependents :: [PseudoDependent] -> Maybe (PseudoDependentHead,([Dependent],[Either Term Literal],[[PseudoDependent]]))
-- set_all_solutions :: FullSolution -> [(Dependent,Either Term Literal)] -> FullSolution

-- This is an important, complicated, part.
-- When we have to match a set of pseudodependents and one of them is a dependent, we have to check that it does not have incoming dependencies.
-- If it does not, we just use the dependent, and all is fine.
-- If it does, then we have to:
--	- Factorize it.
--	- Replace it with the pseudodependent resulting from the factorization (the unique incoming dependency).
--
-- However, we need to keep in mind that it was a dependent so that we can place it in the corresponding dependency.
-- The way that we handle this is the following:
-- 	- Before matching at each step, we recursively factorize all single dependents to be matched, to make sure they only have one incoming dependency.
--	- During the matching, we replace these dependents with their incoming pseudodependent, but return the dependents themselves as part of the matching process, so that we can place them
--		in the dependency.
factorize_single_dependent :: FullSolution -> PseudoDependent -> (FullSolution,[(Dependent,Either Term Literal)],PseudoDependent)
factorize_single_dependent (mvs,eqs,(inst,cs),(g,sol,ueqs)) (PDDep d) =
	case (get_incoming_hdeps (find_node g d)) of
	{
		[] -> ((mvs,eqs,(inst,cs),(g,sol,ueqs)),[],(PDDep d));
		hdeps -> factorize_single_dependent_helper_1 (mvs,eqs,(inst,cs),(g,sol,ueqs)) d
	} 
--	if (isNothing nmb) then ((mvs,eqs,(inst,cs),(g,sol,ueqs)),[],(PDDep d)) else (case (get_incoming_hdeps (find_node g d)) of
--	{
--		[] -> ((mvs,eqs,(inst,cs),(g,sol,ueqs)),[],(PDDep d));
--		hdeps -> factorize_single_dependent_helper_1 (mvs,eqs,(inst,cs),(g,sol,ueqs)) d
--	})
--	where nmb = find_node_maybe g d
factorize_single_dependent fs otherwise = (fs,[],otherwise)

-- We need to have factorized before, so here we just get the unique incoming dependency (if there is) and return it as a pseudodependent.
get_subpdep_dependent :: DependencyGraph -> PseudoDependent -> PseudoDependent
get_subpdep_dependent g (PDDep d) =
	case (get_incoming_hdeps (find_node g d)) of
	{
		[] -> PDDep d;
		hdeps -> case (pseudodeps_from_node g d) of {[x] -> x}
	}
--	if (isNothing nmb) then (PDDep d) else (case (get_incoming_hdeps (find_node g d)) of
--	{
--		[] -> PDDep d;
--		hdeps -> case (pseudodeps_from_node g d) of {[x] -> x}
--	})
	where nmb = find_node_maybe g d
get_subpdep_dependent _ other = other

just_factorize_all_single_dependents :: FullSolution -> [[PseudoDependent]] -> (FullSolution,[(Dependent,Either Term Literal)])
just_factorize_all_single_dependents fs ls = (rfs,rvs) where (rfs,rvs,_) = factorize_all_single_dependents fs ls

factorize_all_single_dependents :: FullSolution -> [[PseudoDependent]] -> (FullSolution,[(Dependent,Either Term Literal)],[[PseudoDependent]])
factorize_all_single_dependents fs ls = foldl factorize_single_dependent_helper_2 (fs,[],[]) (reverse ls)

factorize_single_dependent_helper_1 :: FullSolution -> Dependent -> (FullSolution,[(Dependent,Either Term Literal)],PseudoDependent)
-- We know that, after factorization, the dependent ought to have a unique incoming dependency, which we use.
-- To verify that this holds, we use a case where we purposely leave non-exhaustive if the list has less or more than one element.
factorize_single_dependent_helper_1 fs d = (parc,parcvs,pdep) where (parc,parcvs) = factorize_dgraph fs d; pdeps = pseudodeps_from_node (get_graph parc) d; pdep = case pdeps of {[x] -> x}

-- To fold. Start with an empty list of lists of pseudodependents.
factorize_single_dependent_helper_2 :: (FullSolution,[(Dependent,Either Term Literal)],[[PseudoDependent]]) -> [PseudoDependent] -> (FullSolution,[(Dependent,Either Term Literal)],[[PseudoDependent]])
factorize_single_dependent_helper_2 (fs,vs,ls) pds = (resfs,vs++resvs,respds:ls) where (resfs,resvs,respds) = foldl factorize_single_dependent_helper_3 (fs,[],[]) (reverse pds)

-- To fold, at the lower level.
factorize_single_dependent_helper_3 :: (FullSolution,[(Dependent,Either Term Literal)],[PseudoDependent]) -> PseudoDependent -> (FullSolution,[(Dependent,Either Term Literal)],[PseudoDependent])
factorize_single_dependent_helper_3 (fs,vs,l) pd = (resfs,vs++resvs,respd:l) where (resfs,resvs,respd) = factorize_single_dependent fs pd

-- For each single dependency in the pseudodependency, it does the following:
--	- Removes any incoming horizontal dependencies to the target dependent.
--	- Adds a single dependency consisting on the encoded one.
dump_pseudodependency_graph :: FullSolution -> PseudoDependency -> FullSolution
dump_pseudodependency_graph fs (PDependencyBase _) = fs
dump_pseudodependency_graph (mvs,eqs,(inst,cs),(g,sol,ueqs)) (PDependency d thdep pins) = foldl dump_pseudodependency_graph_helper (mvs,eqs,(inst,cs),(redressed,sol,ueqs)) pins where naked = del_all_incoming_hdeps g d; redressed = add_hdep naked (THDep thdep) (dump_pseudodependency_graph_helper_2 pins) d

dump_pseudodependency_graph_helper :: FullSolution -> PseudoDependencyInput -> FullSolution
dump_pseudodependency_graph_helper fs PDInTip = fs
dump_pseudodependency_graph_helper fs (PDInBranch pdep) = dump_pseudodependency_graph fs pdep

-- Gets the sources of one dependency within a pseudodependency
dump_pseudodependency_graph_helper_2 :: [PseudoDependencyInput] -> [Dependent]
dump_pseudodependency_graph_helper_2 [] = []
-- This one should not really happen, though.
dump_pseudodependency_graph_helper_2 (PDInTip:pins) = dump_pseudodependency_graph_helper_2 pins
dump_pseudodependency_graph_helper_2 ((PDInBranch pdep):pins) = (get_pdep_dependent pdep):(dump_pseudodependency_graph_helper_2 pins)

--add_hdep :: DependencyGraph -> HorizontalDependency -> [Dependent] -> Dependent -> DependencyGraph

-- Extracts the classes of equivalent dependents.
factorize_dgraph_rec_helper_1 :: [Maybe (PseudoDependentHead,([Dependent],[Either Term Literal],[[PseudoDependent]]))] -> [[Dependent]]
factorize_dgraph_rec_helper_1 [] = []
-- There should be no nothings here. We first check that all heads are satisfiable. Note that we rely on lazy evaluation to avoid pattern matching here if this happens.
--factorize_dgraph_rec_helper_1 (Nothing:rs) = factorize_dgraph_rec_helper_1 rs
factorize_dgraph_rec_helper_1 ((Just (_,(x,_,_))):rs) = x:(factorize_dgraph_rec_helper_1 rs)

-- Extracts the equivalence class representer for each class of equivalent dependents, or Nothing if there are none. Must be run after making them equivalent.
factorize_dgraph_rec_helper_2 :: DependencyGraph -> [[Dependent]] -> [Maybe Dependent]
factorize_dgraph_rec_helper_2 g [] = []
factorize_dgraph_rec_helper_2 g ([]:rs) = Nothing:(factorize_dgraph_rec_helper_2 g rs)
factorize_dgraph_rec_helper_2 g ((d1:ds):rs) = (Just (find_eqdep_rep g d1)):(factorize_dgraph_rec_helper_2 g rs)

-- Extracts the heads
factorize_dgraph_rec_helper_3 :: [Maybe (PseudoDependentHead,([Dependent],[Either Term Literal],[[PseudoDependent]]))] -> [PseudoDependentHead]
factorize_dgraph_rec_helper_3 [] = []
-- There should be no nothings here. We first check that all heads are satisfiable. Note that we rely on lazy evaluation to avoid pattern matching here if this happens.
-- factorize_dgraph_rec_helper_3 (Nothing:rs) = factorize_dgraph_rec_helper_3 rs
factorize_dgraph_rec_helper_3 ((Just (h,_)):rs) = h:(factorize_dgraph_rec_helper_3 rs)

-- Nothing indicates that there is no solution.
-- Plenty indicates that there are several, incompatible, solutions.
-- Otherwise, we give the solution.
factorize_dgraph_rec_helper_4 :: [Maybe (PseudoDependentHead,([Dependent],[Either Term Literal],[[PseudoDependent]]))] -> [MaybePlenty (Either Term Literal)]
factorize_dgraph_rec_helper_4 [] = []
-- There should be no nothings here. We first check that all heads are satisfiable. Note that we rely on lazy evaluation to avoid pattern matching here if this happens.
-- factorize_dgraph_rec_helper_4 (Nothing:rs) = factorize_dgraph_rec_helper_4 rs
factorize_dgraph_rec_helper_4 ((Just (_,(_,vs,_))):rs) = (foldl factorize_dgraph_rec_helper_5 NothingS vs):(factorize_dgraph_rec_helper_4 rs)

factorize_dgraph_rec_helper_5 :: MaybePlenty (Either Term Literal) -> Either Term Literal -> MaybePlenty (Either Term Literal)
factorize_dgraph_rec_helper_5 NothingS v = JustS v
factorize_dgraph_rec_helper_5 (JustS v1) v2 | v1 == v2 = JustS v1
factorize_dgraph_rec_helper_5 (JustS v1) v2 = PlentyS
factorize_dgraph_rec_helper_5 PlentyS _ = PlentyS

factorize_dgraph_rec_helper_6 :: [Maybe Dependent] -> [MaybePlenty (Either Term Literal)] -> [(Dependent,Either Term Literal)]
factorize_dgraph_rec_helper_6 [] [] = []
factorize_dgraph_rec_helper_6 (Nothing:ds) (_:sols) = factorize_dgraph_rec_helper_6 ds sols
factorize_dgraph_rec_helper_6 (_:ds) (NothingS:sols) = factorize_dgraph_rec_helper_6 ds sols
-- There should be no plentys here, we would have given Unsatisfiable if so. We rely on lazy evaluation for this.
-- factorize_dgraph_rec_helper_6 (_:ds) (PlentyS:sols) = factorize_dgraph_rec_helper_6 ds sols
factorize_dgraph_rec_helper_6 ((Just d):ds) ((JustS v):sols) = (d,v):(factorize_dgraph_rec_helper_6 ds sols)

-- NOTE: There is a slight inefficiency here. When the head is void, we need not continue decomposing, but we need to keep the pseudodependent to keep the overall pseudodependency working.
-- This means that we decompose and match this pseudodependent against itself on all subsequent steps. This is not really a big deal, but could be avoided. We don't use time in this right now.
factorize_dgraph_rec_helper_7 :: [Maybe (PseudoDependentHead,([Dependent],[Either Term Literal],[[PseudoDependent]]))] -> [[PseudoDependent]]
factorize_dgraph_rec_helper_7 [] = []
-- There should be no nothings here. We first check that all heads are satisfiable. Note that we rely on lazy evaluation to avoid pattern matching here if this happens.
-- factorize_dgraph_rec_helper_7 (Nothing:rs) = factorize_dgraph_rec_helper_7 rs
-- Void heads should mean no pseudodependents generated (or rather, an array with just one: The same pseudodependent). We leave the case analysis non-exhaustive otherwise on purpose to flag up the error.
factorize_dgraph_rec_helper_7 ((Just (PDHeadVoid,(_,_,[[pd]]))):rs) = [pd]:(factorize_dgraph_rec_helper_7 rs)
factorize_dgraph_rec_helper_7 ((Just ((PDHeadF _),(_,_,pds))):rs) = pds ++ (factorize_dgraph_rec_helper_7 rs)

factorize_add_equivalences :: DependencyGraph -> [[Dependent]] -> DependencyGraph
factorize_add_equivalences g [] = g
factorize_add_equivalences g (d1s:dss) = factorize_add_equivalences (factorize_add_equivalences_helper g d1s) dss

factorize_add_equivalences_helper :: DependencyGraph -> [Dependent] -> DependencyGraph
factorize_add_equivalences_helper g [] = g
factorize_add_equivalences_helper g (d1:ds) = foldl (\h -> \d2 -> add_eqdep h d1 d2) g ds

factorize_introduce_branches :: PseudoDependency -> [Maybe Dependent] -> PseudoDependency
factorize_introduce_branches pd ds = fst (factorize_introduce_branches_rec pd ds)

-- The second argument is the equivalence classes representative for each matching class that we introduced, or Nothing if there is no dependent there.
factorize_introduce_branches_rec :: PseudoDependency -> [Maybe Dependent] -> (PseudoDependency,[Maybe Dependent])
factorize_introduce_branches_rec (PDependencyBase d1) (Nothing:ds) = (PDependencyBase d1,ds)
-- The following case should only happen when d1 is equal to d2 (or it is in the same dependency class). It's just a redundancy.
--factorize_introduce_branches_rec (PDependencyBase d1) ((Just d2):ds) | d1 == d2 = (PDependencyBase d1,ds)
factorize_introduce_branches_rec (PDependencyBase d1) ((Just d2):ds) = (PDependencyBase d1,ds)
factorize_introduce_branches_rec (PDependency d (FApp f ins) pins) ds = (PDependency d (FApp f ins) recpins,recrem) where (recpins,recrem,recprem) = factorize_introduce_branches_helper ins pins ds

-- The external dependency cannot change because of this. What changes is the pseudodependencyinputs. We return the list of remaining unprocessed possible dependents to replace.
factorize_introduce_branches_helper :: [TermDependencyInput] -> [PseudoDependencyInput] -> [Maybe Dependent] -> ([PseudoDependencyInput],[Maybe Dependent],[PseudoDependencyInput])
factorize_introduce_branches_helper [] pins ds = ([],ds,pins)
factorize_introduce_branches_helper (TInDependent:ins) (PDInTip:pins) (Nothing:ds) = (PDInTip:recpins,recrem,recprem) where (recpins,recrem,recprem) = factorize_introduce_branches_helper ins pins ds
factorize_introduce_branches_helper (TInDependent:ins) (PDInTip:pins) ((Just d):ds) = ((PDInBranch (PDependencyBase d)):recpins,recrem,recprem) where (recpins,recrem,recprem) = factorize_introduce_branches_helper ins pins ds
factorize_introduce_branches_helper (TInDependent:ins) ((PDInBranch pd):pins) ds = ((PDInBranch recpd1):recpins2,recrem2,recprem2) where (recpd1,recrem1) = factorize_introduce_branches_rec pd ds; (recpins2,recrem2,recprem2) = factorize_introduce_branches_helper ins pins recrem1
factorize_introduce_branches_helper ((TInFixed t):ins) pins ds = factorize_introduce_branches_helper ins pins ds
factorize_introduce_branches_helper ((TInRec (FApp f rins)):ins) pins ds = (recpins1 ++ recpins2,recrem2,recprem2) where (recpins1,recrem1,recprem1) = factorize_introduce_branches_helper rins pins ds; (recpins2,recrem2,recprem2) = factorize_introduce_branches_helper ins recprem1 recrem1

-- The key fact is: The number of heads needs to be the same as the number of elements the dependency is expecting.
-- We do not introduce branches here, this only happens when dependents are found.
-- However, we do need to take branches into account when replacing heads.
factorize_upd_depfun :: [PseudoDependentHead] -> [Maybe Dependent] -> [MaybePlenty (Either Term Literal)] -> PseudoDependency -> PseudoDependency
factorize_upd_depfun [h] _ _ (PDependencyBase d) = input_from_head d h
factorize_upd_depfun hs ds vs (PDependency d dep pdins) = replace_indeps_thpdep (PDependency d dep pdins) (map (\tris -> case tris of {(h,d,v) -> replace_head_thdep h d v}) (zip3 hs ds vs))

factorize_remove_fixed_values_from_matching :: [TermDependencyInput] -> [t] -> [t]
factorize_remove_fixed_values_from_matching [] [] = []
factorize_remove_fixed_values_from_matching ((TInFixed _):ins) (x:xs) = factorize_remove_fixed_values_from_matching ins xs
factorize_remove_fixed_values_from_matching (_:ins) (x:xs) = x:(factorize_remove_fixed_values_from_matching ins xs)

replace_head_thdep :: PseudoDependentHead -> Maybe Dependent -> MaybePlenty (Either Term Literal) -> TermDependencyInput
replace_head_thdep PDHeadVoid Nothing NothingS = TInDependent
-- Fixed value!
replace_head_thdep PDHeadVoid Nothing (JustS (Left v)) = TInFixed v
-- No plenties here!!!
--replace_head_thdep PDHeadVoid Nothing PlentyS =
-- A dependent in the middle.
replace_head_thdep PDHeadVoid (Just d) _ = TInDependent
-- Function: The recurring ones will be sorted out at the next step.
replace_head_thdep (PDHeadF f) _ _ = TInRec (default_thdep_fun f)


input_from_head :: Dependent -> PseudoDependentHead -> PseudoDependency
input_from_head d PDHeadVoid = PDependencyBase d
input_from_head d (PDHeadF f) =  (default_thpdep_fun d f)

default_thpdep_fun :: Dependent -> Function -> PseudoDependency
default_thpdep_fun d f = PDependency d (default_thdep_fun f) (replicate (arity f) PDInTip)

default_thdep_fun :: Function -> TermHorizontalDependency
default_thdep_fun f = FApp f (replicate (arity f) TInDependent)

replace_indeps_thpdep :: PseudoDependency -> [TermDependencyInput] -> PseudoDependency
replace_indeps_thpdep pd ins = fst (replace_indeps_thpdep_rec pd ins)

-- This does not introduce branches, but takes them into account. Replaces the "tips of the tips", that is, the inputs of the tip dependencies of the pseudodependency, with the given termdependencyinput. Note that while this does not introduce branches, it may need to change the number of tips!!!
replace_indeps_thpdep_rec :: PseudoDependency -> [TermDependencyInput] -> (PseudoDependency,[TermDependencyInput])
replace_indeps_thpdep_rec (PDependencyBase d) (TInDependent:ins) = (PDependencyBase d,ins)
replace_indeps_thpdep_rec (PDependencyBase d) ((TInFixed t):ins) = (PDependencyBase d,ins)
-- This is the interesting case, when the base case stops being the base case.
replace_indeps_thpdep_rec (PDependencyBase d) ((TInRec (FApp f rins)):ins) = (PDependency d (FApp f rins) (replicate (arity f) PDInTip),ins)
replace_indeps_thpdep_rec (PDependency d (FApp f rins) pins) ins = (PDependency d (FApp f recins) recpins,recrem) where (recins,recpins,recrem,recprem) = replace_indeps_thpdep_helper rins pins ins

-- First argument is the definition of the external dependency, second argument is its structure as a pseudodependency. Third argument is what to replace the tips for.
-- Result is, the updated structure of the external dependency, and the recursive pseudodependencies. The third result is the remaining unused inputs from the third argument. The fourth result is the remaining ununused pseudodependencyinputs from the second argument.
replace_indeps_thpdep_helper :: [TermDependencyInput] -> [PseudoDependencyInput] -> [TermDependencyInput] -> ([TermDependencyInput],[PseudoDependencyInput],[TermDependencyInput],[PseudoDependencyInput])
replace_indeps_thpdep_helper [] pins rs = ([],[],rs,pins)
replace_indeps_thpdep_helper (TInDependent:ins) (PDInTip:pins) (r:rs) = (r:recins,(replace_indeps_thpdep_tips_from_thpdep r) ++ recpins,recrem,recprem) where (recins,recpins,recrem,recprem) = replace_indeps_thpdep_helper ins pins rs
replace_indeps_thpdep_helper (TInDependent:ins) ((PDInBranch pd):pins) rs = (TInDependent:recins2,(PDInBranch recpd1):recpins2,recrem2,recprem2) where (recpd1,recrem1) = replace_indeps_thpdep_rec pd rs; (recins2,recpins2,recrem2,recprem2) = replace_indeps_thpdep_helper ins pins recrem1
replace_indeps_thpdep_helper ((TInFixed t):ins) pins rs = ((TInFixed t):recins,recpins,recrem,recprem) where (recins,recpins,recrem,recprem) = replace_indeps_thpdep_helper ins pins rs
replace_indeps_thpdep_helper ((TInRec (FApp f rins)):ins) pins rs = ((TInRec (FApp f recins1)):recins2,recpins1 ++ recpins2,recrem2,recprem2) where (recins1,recpins1,recrem1,recprem1) = replace_indeps_thpdep_helper rins pins rs; (recins2,recpins2,recrem2,recprem2) = replace_indeps_thpdep_helper ins recprem1 recrem1

replace_indeps_thpdep_tips_from_thpdep :: TermDependencyInput -> [PseudoDependencyInput]
replace_indeps_thpdep_tips_from_thpdep TInDependent = [PDInTip]
replace_indeps_thpdep_tips_from_thpdep (TInFixed t) = []
replace_indeps_thpdep_tips_from_thpdep (TInRec (FApp f rins)) = concat (map replace_indeps_thpdep_tips_from_thpdep rins)

--replace_indeps_thpdep_helper :: [TermDependencyInput] -> [PseudoDependencyInput] -> [TermDependencyInput] -> ([TermDependencyInput],[PseudoDependencyInput],[TermDependencyInput],[PseudoDependencyInput])
--replace_indeps_thpdep_helper [] pins rs = ([],[],rs,pins)
--replace_indeps_thpdep_helper (TInDependent:ins) (PDInTip:pins) (r:rs) = (r:recins,PDInTip:recpins,recrem,recprem) where (recins,recpins,recrem,recprem) = replace_indeps_thpdep_helper ins pins rs
--replace_indeps_thpdep_helper (TInDependent:ins) ((PDInBranch pd):pins) rs = (TInDependent:recins2,(PDInBranch recpd1):recpins2,recrem2,recprem2) where (recpd1,recrem1) = replace_indeps_thpdep_rec pd rs; (recins2,recpins2,recrem2,recprem2) = replace_indeps_thpdep_helper ins pins recrem1
--replace_indeps_thpdep_helper ((TInFixed t):ins) pins rs = ((TInFixed t):recins,recpins,recrem,recprem) where (recins,recpins,recrem,recprem) = replace_indeps_thpdep_helper ins pins rs
--replace_indeps_thpdep_helper ((TInRec (FApp f rins)):ins) pins rs = ((TInRec (FApp f recins1)):recins2,recpins1 ++ recpins2,recrem2,recprem2) where (recins1,recpins1,recrem1,recprem1) = --replace_indeps_thpdep_helper rins pins rs; (recins2,recpins2,recrem2,recprem2) = replace_indeps_thpdep_helper ins recprem1 recrem1

replace_indeps_thdep :: TermHorizontalDependency -> [TermDependencyInput] -> TermHorizontalDependency
replace_indeps_thdep (FApp f ins) rs = FApp f rins where (rins,rdeps) = replace_indeps_thdep_rec ins rs

-- First argument is previous list of inputs, second argument is what to replace dependents for. First result is resulting list of inputs, second argument is remaining non-replaced elements of second argument.
replace_indeps_thdep_rec :: [TermDependencyInput] -> [TermDependencyInput] -> ([TermDependencyInput],[TermDependencyInput])
replace_indeps_thdep_rec [] rs = ([],rs)
replace_indeps_thdep_rec (TInDependent:ins) (r1:rs) = (r1:recins,recrs) where (recins,recrs) = replace_indeps_thdep_rec ins rs
replace_indeps_thdep_rec ((TInFixed t):ins) rs = ((TInFixed t):recins,recrs) where (recins,recrs) = replace_indeps_thdep_rec ins rs
replace_indeps_thdep_rec ((TInRec (FApp f rins)):ins) rs = ((TInRec (FApp f recins1)):recins2,recrs2) where (recins1,recrs1) = replace_indeps_thdep_rec rins rs; (recins2,recrs2) = replace_indeps_thdep_rec ins recrs1

-- Old
--factorize_upd_depfun :: [PseudoDependentHead] -> Maybe TermHorizontalDependency -> Maybe TermHorizontalDependency
--factorize_upd_depfun [h] Nothing = input_from_head h
--factorize_upd_depfun hs (Just dep) = Just (replace_indeps_thdep dep (map replace_head_thdep hs))

--replace_head_thdep :: PseudoDependentHead -> TermDependencyInput
--replace_head_thdep PDHeadVoid = TInDependent
--replace_head_thdep (PDHeadF f) = TInRec (default_thdep_fun f)

--input_from_head :: PseudoDependentHead -> Maybe TermHorizontalDependency
--input_from_head PDHeadVoid = Nothing
--input_from_head (PDHeadF f) = Just (default_thdep_fun f)

--default_thdep_fun :: Function -> TermHorizontalDependency
--default_thdep_fun f = FApp f (replicate (arity f) TInDependent)

--replace_indeps_thdep :: TermHorizontalDependency -> [TermDependencyInput] -> TermHorizontalDependency
--replace_indeps_thdep (FApp f ins) rs = FApp f rins where (rins,rdeps) = replace_indeps_thdep_rec ins rs

-- First argument is previous list of inputs, second argument is what to replace dependents for. First result is resulting list of inputs, second argument is remaining non-replaced elements of second argument.
--replace_indeps_thdep_rec :: [TermDependencyInput] -> [TermDependencyInput] -> ([TermDependencyInput],[TermDependencyInput])
--replace_indeps_thdep_rec [] rs = ([],rs)
--replace_indeps_thdep_rec (TInDependent:ins) (r1:rs) = (r1:recins,recrs) where (recins,recrs) = replace_indeps_thdep_rec ins rs
--replace_indeps_thdep_rec ((TInFixed t):ins) rs = ((TInFixed t):recins,recrs) where (recins,recrs) = replace_indeps_thdep_rec ins rs
--replace_indeps_thdep_rec ((TInRec (FApp f rins)):ins) rs = ((TInRec (FApp f recins1)):recins2,recrs2) where (recins1,recrs1) = replace_indeps_thdep_rec rins rs; (recins2,recrs2) = replace_indeps_thdep_rec ins recrs1

pdep_head_arity :: PseudoDependentHead -> Int
pdep_head_arity PDHeadVoid = 1
pdep_head_arity (PDHeadF f) = arity f

list_split :: [t] -> Int -> ([t],[t])
list_split l 0 = ([],l)
list_split (x:xs) i = (x:rech,rect) where (rech,rect) = list_split xs (i-1)

--data TermDependencyInput = TInDependent | TInFixed Term | TInRec TermHorizontalDependency
--data LitDependencyInput = LInDependent | LInFixed Literal
--data TermHorizontalDependency = FApp Function [TermDependencyInput]
--data LitTermHorizontalDependency = PApp Predicate [TermDependencyInput]
--data LitHorizontalDependency = LEq LitDependencyInput

--data HorizontalDependency = THDep TermHorizontalDependency | LTHDep LitTermHorizontalDependency | LHDep LitHorizontalDependency


match_pseudodependents :: DependencyGraph -> [PseudoDependent] -> Maybe (PseudoDependentHead,([Dependent],[Either Term Literal],[[PseudoDependent]]))
match_pseudodependents g pds = match_pseudodependents_helper pds (case rhead of {Nothing -> Nothing; Just h -> Just (h,match_pseudodep_bodies h pdbodies)}) where (pdheads,pdbodies) = unzip (map (decompose_pseudodep_in_graph g) pds); rhead = match_pseudodep_heads pdheads

-- This is a little trick. When the head is void, we just put back one pseudodependent in the list of dependents to check. ANY will do, as we already matched them.
match_pseudodependents_helper :: [PseudoDependent] -> Maybe (PseudoDependentHead,([Dependent],[Either Term Literal],[[PseudoDependent]])) -> Maybe (PseudoDependentHead,([Dependent],[Either Term Literal],[[PseudoDependent]]))
match_pseudodependents_helper [] x = x
match_pseudodependents_helper _ Nothing = Nothing
-- If the head is void, the recursive pseudodeps should be empty. We leave the otherwise case non-exhaustive to flag up the error.
match_pseudodependents_helper (pd:_) (Just (PDHeadVoid,(ds,vs,[]))) = Just (PDHeadVoid,(ds,vs,[[pd]]))
match_pseudodependents_helper _ (Just (PDHeadF f,x)) = Just (PDHeadF f,x)

-- Matching a set of bodies: Those with empty heads can have either a dependent, variable or meta-variable as body
-- Here, we ignore the meta-variable case, as in the current implementation should not occur.
-- We put the dependents aside, as that means there is a node in the graph at this level.
-- Similarly, we put all fixed pseudodependents aside (variables, but also composites). If there are dependents at this level, we need to update their values, and in any case, we need to use
-- the value in the resulting dependency (after checking they are all equal).
-- Note that when we have a fixed but composite pseudodependent, we use it both to update the value of dependents at that level, and to proceed further up in the graph factorization.
-- Indeed, it may both happen that there are dependents ta that level with no dependencies that need to have their value updated, and at the same time, other values further up the graph that
-- need to be checked for this equality.
-- While at a horizontal level there is no need to propagate the value of the dependents solved in this way (as the result is going to be the one already obtained through the factorization), there
-- is a need to propagate them vertically.
-- Any non-fixed, non-dependent pseudodependents have bodies consisting of lists of dependents, which need to be equal between them. We return this as a list of lists, where each list contains pseudodependents that need to be matched.
match_pseudodep_bodies :: PseudoDependentHead -> [PseudoDependentBody] -> ([Dependent],[Either Term Literal],[[PseudoDependent]])
match_pseudodep_bodies PDHeadVoid [] = ([],[],[])
match_pseudodep_bodies (PDHeadF f) [] = ([],[],replicate (arity f) [])
match_pseudodep_bodies h ((PDBodyVoidD d):bs) = (d:rdeps,rvals,rpdeps) where (rdeps,rvals,rpdeps) = match_pseudodep_bodies h bs
match_pseudodep_bodies h ((PDBodyVoidV v):bs) = (rdeps,(Left (TVar v)):rvals,rpdeps) where (rdeps,rvals,rpdeps) = match_pseudodep_bodies h bs
match_pseudodep_bodies h ((PDBodySubD d b):bs) = (d:rdeps,rvals,rpdeps) where (rdeps,rvals,rpdeps) = match_pseudodep_bodies h (b:bs)
--match_pseudodep_bodies h ((PDBodyVoidM mv):bs) = 
match_pseudodep_bodies h ((PDBodyF pds):bs) = (rdeps,rvals,map (\pair -> case pair of {(pd,l) -> pd:l}) (zip pds rpdeps)) where (rdeps,rvals,rpdeps) = match_pseudodep_bodies h bs
match_pseudodep_bodies (PDHeadF f) ((PDBodyFixedF ts):bs) = (rdeps,(Left (TFun f ts)):rvals,map (\pair -> case pair of {(t,l) -> (PDFixedT t):l}) (zip ts rpdeps)) where (rdeps,rvals,rpdeps) = match_pseudodep_bodies (PDHeadF f) bs

--data PseudoDependentBody = PDBodyVoidD Dependent | PDBodyVoidV Variable | PBBodyVoidM Metavariable | PDBodyF [PseudoDependent] | PDBodyFixedF [Term]

match_pseudodep_heads_2 :: PseudoDependentHead -> PseudoDependentHead -> Maybe PseudoDependentHead
match_pseudodep_heads_2 PDHeadVoid PDHeadVoid = Just PDHeadVoid
match_pseudodep_heads_2 PDHeadVoid (PDHeadF f) = Just (PDHeadF f)
match_pseudodep_heads_2 (PDHeadF f) PDHeadVoid = Just (PDHeadF f)
match_pseudodep_heads_2 (PDHeadF f1) (PDHeadF f2) | f1 == f2 = Just (PDHeadF f1)
match_pseudodep_heads_2 (PDHeadF f1) (PDHeadF f2) = Nothing

match_pseudodep_heads :: [PseudoDependentHead] -> Maybe PseudoDependentHead
match_pseudodep_heads hs = foldl match_pseudodep_heads_helper (Just PDHeadVoid) hs

match_pseudodep_heads_helper :: Maybe PseudoDependentHead -> PseudoDependentHead -> Maybe PseudoDependentHead
match_pseudodep_heads_helper Nothing _ = Nothing
match_pseudodep_heads_helper (Just h1) h2 = match_pseudodep_heads_2 h1 h2

-- Incoming pseudodependents.
pseudodeps_from_node :: DependencyGraph -> Dependent -> [PseudoDependent]
pseudodeps_from_node g d = map pseudodep_from_hdep (get_incoming_hdeps (find_node g d))
--pseudodeps_from_node g d = if (isNothing nmb) then [] else (map pseudodep_from_hdep (get_incoming_hdeps (find_node g d))) where nmb = find_node_maybe g d

-- I feel so ridiculous: I just realized that lthdeps never happen because they are always simplified at the constraint level. >.<
pseudodep_from_hdep :: HDependencyEdge -> PseudoDependent
pseudodep_from_hdep (HDEdge (THDep thdep) ss _) = fst (pseudodep_from_thdep ss thdep)
--pseudodep_from_hdep HDEdge (LTHDep lthdep) ss _ = fst (pseudodep_from_lthdep ss lthdep)
pseudodep_from_hdep (HDEdge (LHDep lhdep) ss _) = fst (pseudodep_from_lhdep ss lhdep)

pseudodep_from_thdep :: [Dependent] -> TermHorizontalDependency -> (PseudoDependent,[Dependent])
pseudodep_from_thdep ds (FApp f ins) = (PDRecF f recpdeps,recdeps) where (recpdeps,recdeps) = pseudodep_from_hdepins ds ins

-- Transforms a list of term dependency inputs into a pseudo dependent, using the specified source dependents. Returns the remaining unused dependents.
pseudodep_from_hdepins :: [Dependent] -> [TermDependencyInput] -> ([PseudoDependent],[Dependent])
pseudodep_from_hdepins ds [] = ([],ds)
pseudodep_from_hdepins (d:ds) (TInDependent:ins) = (((PDDep d):recpdeps),recdeps) where (recpdeps,recdeps) = pseudodep_from_hdepins ds ins
pseudodep_from_hdepins ds ((TInFixed t):ins) = (((PDFixedT t):recpdeps),recdeps) where (recpdeps,recdeps) = pseudodep_from_hdepins ds ins
pseudodep_from_hdepins ds ((TInRec thdep):ins) = ((recpdep1:recpdeps2),recdeps2) where (recpdep1,recdeps1) = pseudodep_from_thdep ds thdep; (recpdeps2,recdeps2) = pseudodep_from_hdepins recdeps1 ins

--pseudodep_from_lthdep :: [Dependent] -> LitTermHorizontalDependency -> (PseudoDependent,[Dependent])
--pseudodep_from_lthdep ds (PApp p ins) = (PDRecP p recpdeps,recdeps) where (recpdeps,recdeps) = pseudodep_from_hdepins ds ins

pseudodep_from_lhdep :: [Dependent] -> LitHorizontalDependency -> (PseudoDependent,[Dependent])
pseudodep_from_lhdep (d:ds) (LEq LInDependent) = (PDDep d,ds)
pseudodep_from_lhdep ds (LEq (LInFixed l)) = (PDFixedL l,ds)

--data TermDependencyInput = TInDependent | TInFixed Term | TInRec TermHorizontalDependency
--data LitDependencyInput = LInDependent | LInFixed Literal
--data TermHorizontalDependency = FApp Function [TermDependencyInput]
--data LitTermHorizontalDependency = PApp Predicate [TermDependencyInput]
--data LitHorizontalDependency = LEq LitDependencyInput

--data HorizontalDependency = THDep TermHorizontalDependency | LTHDep LitTermHorizontalDependency | LHDep LitHorizontalDependency


set_solution :: FullSolution -> (Dependent,Either Term Literal) -> FullSolution
set_solution (mvs,eqs,(inst,cs),(g,sol,ueqs)) (d,v) | (sol_from_list_filter sol (d,v)) = (mvs,eqs,(inst,cs),(g,((d,v):sol),ueqs))
set_solution fs _ = fs

set_all_solutions :: FullSolution -> [(Dependent,Either Term Literal)] -> FullSolution
set_all_solutions fs dvs = foldl set_solution fs dvs

update_graph_single_maybe :: ExtendedSignature -> FullSolution -> (Dependent,Either Term Literal) -> FullSolution
update_graph_single_maybe sig fs (dep,v) = case (find_node_maybe (get_graph fs) dep) of {Nothing -> fs; (Just _) -> update_graph_all sig fs [(dep,v)] []}

-- Updates the graph as long as there is something to update that is certain (i.e. no search).
-- We have two lists, the ones that we did not consider even for horizontal updates and those that are pending updating through vertical updates.
update_graph_all :: ExtendedSignature -> FullSolution -> [(Dependent, Either Term Literal)] -> [(Dependent, Either Term Literal)] -> FullSolution
-- If there are horizontal updates to perform, perform them and call recursively. Otherwise, if there are vertical updates to perform, perform them and call recursively.
update_graph_all sig fs _ _ | is_fullsol_unsatisfiable fs = fs
update_graph_all sig fs [] [] = fs
--update_graph_all fs [] (dv:dvs) | is_node (get_graph fs) (fst dv) = update_graph_all rs rl dvs where (rs,rl) = do_one_update_to_graph update_graph_from_value_vdep (fs,[]) dv
--update_graph_all fs [] (dv:dvs) = update_graph_all rs rl dvs where (rs,rl) = do_one_update_to_graph update_graph_from_value_vdep (fs,[]) dv
--update_graph_all fs [] (dv:dvs) = do_one_update_to_graph update_graph_from_value_vdep (rs,rl) dv where (rs,rl) = update_graph_all fs [] dvs
update_graph_all sig fs [] (dv:dvs) = update_graph_all sig rrs rl dvs where (rs,rl) = do_one_update_to_graph sig update_graph_from_value_vdep fs dv; rrs = simplify_ueqs_fs rs
--update_graph_all fs [] (dv:dvs) = update_graph_all fs [] dvs
--update_graph_all fs (dh:dhs) dvs | is_node (get_graph fs) (fst dh) = update_graph_all rs (dhs ++ rl) (dh:dvs) where (rs,rl) = do_one_update_to_graph update_graph_from_value_hdep_full (fs,dhs) dh
--update_graph_all fs (dh:dhs) dvs s = update_graph_all rrs rrl [] where (rs,rl) = update_graph_all fs dhs dvs; (rrs,rrl) = do_one_update_to_graph update_graph_from_value_hdep_full (rs,rl) dh
update_graph_all sig fs (dh:dhs) dvs = update_graph_all sig rs (dhs ++ rl) (dh:dvs) where (rs,rl) = do_one_update_to_graph sig update_graph_from_value_hdep_full fs dh
--update_graph_all fs (dh:dhs) dvs = update_graph_all fs dhs dvs

--do_one_update_to_graph :: (FullSolution -> t -> (FullSolution,[Dependent])) -> (FullSolution,[(Dependent,Either Term Literal)]) -> t -> (FullSolution,[(Dependent,Either Term Literal)])
--do_one_update_to_graph f ((mvs,(inst,cs),(g,sol)),l) x = ((nmvs,usol,(fg,l ++ new)),new) where ((nmvs,usol,(fg,newsol)),pos) = f (mvs,(inst,cs),(g,sol)) x; new = maybe_sol_from_list (fg,newsol) (all_eq fg pos)

do_one_update_to_graph :: ExtendedSignature -> (FullSolution -> t -> (FullSolution,[Dependent])) -> FullSolution -> t -> (FullSolution,[(Dependent,Either Term Literal)])
do_one_update_to_graph (sig,part,sks,ls) f (mvs,eqs,(inst,cs),(g,sol,ueqs)) x = ((set_all_solutions rfs new),(filter (sol_from_list_filter sol) new)) where ((nmvs,neqs,usol,(fg,newsol,nueqs)),pos) = f (mvs,eqs,(inst,cs),(g,sol,ueqs)) x; new = maybe_sol_from_list (fg,newsol,nueqs) (all_eq fg pos); rfs_new = set_all_solutions (nmvs,neqs,usol,(fg,newsol,nueqs)) new; mb_consistent = restore_consistency_metavar_links (sig,part,sks,ls) (filter_relevant_links_dependents new ls) rfs_new; rfs = if (isJust mb_consistent) then (fromJust mb_consistent) else (mvs,eqs,(idinst,[Unsatisfiable]),(g,sol,ueqs))

filter_relevant_links_dependents :: [(Dependent,Either Term Literal)] -> [MetavariableLink] -> [MetavariableLink]
filter_relevant_links_dependents [] ls = []
filter_relevant_links_dependents ((d,_):ds) ls | is_dependent_metavar d = (filter (\(mv2,lls) -> mv2 == mv) ls) ++ (filter_relevant_links_dependents ds ls) where mv = extract_metavar_dependent d
filter_relevant_links_dependents ((d,_):ds) ls = filter_relevant_links_dependents ds ls

-- restore_consistency_metavar_links :: [MetavariableLink] -> FullSolution -> Maybe FullSolution

-- We filter REPEATED solutions. This is important to avoid infinite loops, but if we have DIFFERENT solutions for the same dependent, we keep them, to show the unsatisfiability later on.
sol_from_list_filter :: DependencyGraphSolution -> (Dependent,Either Term Literal) -> Bool
sol_from_list_filter sol (d,v) = (isNothing pv) || (case pv of {Just x -> x} /= v) where pv = apply_graph_solution sol d


all_eq :: DependencyGraph -> [Dependent] -> [Dependent]
all_eq g ds = list_from_rset (all_eq_set g ds)

all_eq_set :: DependencyGraph -> [Dependent] -> RSet Dependent
all_eq_set g ds = foldl (\s -> \e -> Map.union s (eqdep_set (find_eqdep g e))) Map.empty ds

--fgnew = thd (fst fgnewcomplete); fg = fst fgnew; pos = snd fgnewcomplete; newsol = snd fgnew; new = maybe_sol_from_list (fg,sol) pos

maybe_sol_from_list :: PartiallySolvedDGraph -> [Dependent] -> [(Dependent,Either Term Literal)]
maybe_sol_from_list (g,sol,ueqs) ds = (maybe_sol_from_list_rec (g,sol,ueqs) ds) ++ (maybe_sol_from_list_global (g,sol,ueqs) ds)

maybe_sol_from_list_global :: PartiallySolvedDGraph -> [Dependent] -> [(Dependent,Either Term Literal)]
--maybe_sol_from_list_global (g,sol,ueqs) ds = maybe_sol_from_ueqs ueqs
maybe_sol_from_list_global psg ds = []

maybe_sol_from_list_rec :: PartiallySolvedDGraph -> [Dependent] -> [(Dependent,Either Term Literal)]
maybe_sol_from_list_rec (g,sol,ueqs) [] = []
--maybe_sol_from_list_rec (g,sol,ueqs) (d:ds) | isJust (apply_graph_solution sol d) = maybe_sol_from_list_rec (g,sol,ueqs) ds
maybe_sol_from_list_rec (g,sol,ueqs) (d:ds) = rr ++ rs where r = find_all_sols_from_list (g,sol,ueqs) d; rr = map (\x -> (d,x)) r; rs = maybe_sol_from_list_rec (g,sol,ueqs) ds

-- If we find several solutions through different methods, add them all. Outside, we check for their compatibility.
find_all_sols_from_list :: PartiallySolvedDGraph -> Dependent -> [(Either Term Literal)]
find_all_sols_from_list (g,sol,ueqs) d = case r of {Nothing -> rs; Just x -> (x:rs)} where r = maybe_sol_from_graph (g,sol,ueqs) d; rs = find_all_sols_from_list_2 (g,sol,ueqs) d

find_all_sols_from_list_2 :: PartiallySolvedDGraph -> Dependent -> [(Either Term Literal)]
--find_all_sols_from_list_2 (g,sol,ueqs) d = case r of {Nothing -> rs; Just x -> (x:rs)} where r = maybe_sol_from_graph_2 (g,sol,ueqs) d; rs = find_all_sols_from_list_3 (g,sol,ueqs) d
find_all_sols_from_list_2 (g,sol,ueqs) d = case r of {Nothing -> []; Just x -> [x]} where r = maybe_sol_from_graph_2 (g,sol,ueqs) d

maybe_sol_from_graph :: PartiallySolvedDGraph -> Dependent -> Maybe (Either Term Literal)
--maybe_sol_from_graph (g,sol) (DVar v) = Just (Left (TVar v))
maybe_sol_from_graph (g,sol,ueqs) d = maybe_sol_from_graph_hdeps (g,sol,ueqs) (get_incoming_hdeps (find_node g d))
--maybe_sol_from_graph (g,sol,ueqs) d = if (isNothing nmb) then Nothing else (maybe_sol_from_graph_hdeps (g,sol,ueqs) (get_incoming_hdeps (find_node g d))) where nmb = find_node_maybe g d

-- Vertical dependencies never solve a node.
-- But equivalence classes may

maybe_sol_from_graph_2 :: PartiallySolvedDGraph -> Dependent -> Maybe (Either Term Literal)
maybe_sol_from_graph_2 (g,sol,ueqs) d = maybe_sol_from_graph_eq (g,sol,ueqs) (find_eqdep g d)

-- And unifier equations may, too.
-- NOTE: We find solutions from unifier equations here, by simplifying them, and then simplify them outside again to remove solved ones or keep simplified ones.
-- This really is doing the same work twice, but the infrastructure makes it hard to reuse these results, so for now we do it this way.

maybe_sol_from_ueqs :: [UnifierEquation] -> [(Dependent,Either Term Literal)]
maybe_sol_from_ueqs [] = []
maybe_sol_from_ueqs (ueq:ueqs) = maybe_sol_from_ueqs_helper r where r = simplify_unif_eq (simpl_side_unif_eq ueq); rs = maybe_sol_from_ueqs ueqs

maybe_sol_from_ueqs_helper :: Maybe [Either UnifierEquation (Dependent, Either Term Literal)] -> [(Dependent,Either Term Literal)]
maybe_sol_from_ueqs_helper Nothing = []
maybe_sol_from_ueqs_helper (Just l) = maybe_sol_from_ueqs_helper_2 l

maybe_sol_from_ueqs_helper_2 :: [Either UnifierEquation (Dependent, Either Term Literal)] -> [(Dependent,Either Term Literal)]
maybe_sol_from_ueqs_helper_2 [] = []
maybe_sol_from_ueqs_helper_2 ((Left x):xs) = maybe_sol_from_ueqs_helper_2 xs
maybe_sol_from_ueqs_helper_2 ((Right x):xs) = (x:(maybe_sol_from_ueqs_helper_2 xs))

maybe_sol_from_graph_hdeps :: PartiallySolvedDGraph -> [HDependencyEdge] -> Maybe (Either Term Literal)
maybe_sol_from_graph_hdeps (g,sol,ueqs) [] = Nothing
maybe_sol_from_graph_hdeps (g,sol,ueqs) (dep:deps) = case r of {Just s -> Just s; Nothing -> maybe_sol_from_graph_hdeps (g,sol,ueqs) deps} where r = maybe_sol_from_graph_hdep (g,sol,ueqs) dep

maybe_sol_from_graph_hdep :: PartiallySolvedDGraph -> HDependencyEdge -> Maybe (Either Term Literal)
-- No dependents left, that's what we're looking for. Just evaluate it.
--maybe_sol_from_graph_hdep (g,sol,ueqs) (HDEdge (THDep (FApp f ins)) [] _) | (has_indep ins) = capture_value g (Just (Left (apply_thdep (THDep (FApp f ins)) [])))
maybe_sol_from_graph_hdep (g,sol,ueqs) (HDEdge (THDep f) [] _) = Just (Left (apply_thdep (THDep f) []))
maybe_sol_from_graph_hdep (g,sol,ueqs) (HDEdge (LTHDep f) [] _) = Just (Right (apply_lthdep (LTHDep f) []))
-- For literals, give a dummy argument.
maybe_sol_from_graph_hdep (g,sol,ueqs) (HDEdge (LHDep f) [] _) = Just (Right (apply_lhdep (LHDep f) (LitM (Metavar 1))))
-- In any other case, we still can't solve it.
maybe_sol_from_graph_hdep _ _ = Nothing

has_indep :: [TermDependencyInput] -> Bool
has_indep [] = False
has_indep (TInDependent:_) = True
has_indep ((TInRec (FApp f rins)):ins) = (has_indep rins) || (has_indep ins)
has_indep (_:ins) = has_indep ins

maybe_sol_from_graph_eq :: PartiallySolvedDGraph -> EqDependencyClass -> Maybe (Either Term Literal)
maybe_sol_from_graph_eq (g,sol,ueqs) c = maybe_sol_from_graph_eq_list (g,sol,ueqs) (eqdep_elems c)

maybe_sol_from_graph_eq_list :: PartiallySolvedDGraph -> [Dependent] -> Maybe (Either Term Literal)
maybe_sol_from_graph_eq_list (g,sol,ueqs) [] = Nothing
maybe_sol_from_graph_eq_list (g,sol,ueqs) (d:ds) = case r of {Just s -> Just s; Nothing -> maybe_sol_from_graph_eq_list (g,sol,ueqs) ds} where r = apply_graph_solution sol d

--maybe_sol_from_graph_vdeps :: DependencyGraph -> [VDependencyEdge] -> Maybe (Either Term Literal)

--sol_from_list :: [(Dependent,Either Term Literal)] -> DependencyGraph -> DependencyGraphSolution
--sol_from_list [] _ _ = Nothing
--sol_from_list ((d1,r):s) g d2| (find_eqdep g d1) == (find_eqdep g d2) = Just r
--sol_from_list ((d1,r):s) g d2 = sol_from_list s g d2


partial_apply_list :: ([a] -> b) -> a -> [a] -> b
partial_apply_list f x xs = f (x:xs)

as_term :: Either Term Literal -> Term
as_term (Left x) = x

as_literal :: Either Term Literal -> Literal
as_literal (Right x) = x

-- Unifier equations here refer to situations where one side is solved and the other is not. That is, things like MT = T where MT is a meta-term and T is a term, with no unifiers.
-- These can be simplified, yielding either: 1. Other, simpler, non-simplifiable, unifier equations. 2. Solutions to dependents. 3. Unsatisfiability.
data UnifierEquation = TUEq Metaterm Term | LUEq Metaliteral Literal

instance Show UnifierEquation where
	show (TUEq mt t) = (show mt) ++ " = " ++ (show t)
	show (LUEq ml l) = (show ml) ++ " = " ++ (show l)

simpl_side_unif_eq :: UnifierEquation -> UnifierEquation
simpl_side_unif_eq (TUEq mt t) = (TUEq (all_simpl_mterm mt) t)
simpl_side_unif_eq (LUEq ml l) = (LUEq (all_simpl_mlit ml) l)

-- We assume that the meta-terms/meta-literals have been simplified so that the unifiers have been pushed inwards.
-- Result is Nothing if equation is unsatisfiable.
-- NOTE: For dependents of the form v u x, we leave the equation. We could, in theory, solve for that dependent, and then see what happens.
-- This, however, would imply certain changes in the way that we see our full solutions, and we would have to propagate backwards not only horizontally, but also vertically, so that vux = t has some effect once we know what vux is. To avoid this, we do not solve these situations, and instead leave them as equations that we come back to once we know what the inner unifier sends the variable to.
-- For meta-variables, we do use the value, and then rely on inverse unification to find instantiations for the meta-variable. This is a way of forwards non-enumerating instantiation of meta-variables, which is good!
simplify_unif_eq :: UnifierEquation -> Maybe [Either UnifierEquation (Dependent,Either Term Literal)]
-- Compatible functions: simplify.
simplify_unif_eq (TUEq (MTermF f mts) (TFun g ts)) | f == g = maybe_concat (map (\pair -> simplify_unif_eq (TUEq (fst pair) (snd pair))) (zip mts ts))
-- Incompatible functions: Unsatisfiable.
simplify_unif_eq (TUEq (MTermF f mts) (TFun g ts)) = Nothing
-- Function equals variable: Unsatisfiable.
simplify_unif_eq (TUEq (MTermF _ _) (TVar _)) = Nothing
-- Function equals meta-variable should never be produced!!!
--simplify_unif_eq (TUEq (MTermF _ _) (TMeta _)) = Nothing
-- MTermT means meta-variable or object-level variable.
-- Variable means we found a solution.
simplify_unif_eq (TUEq (MTermR u (MTermT (TVar v))) t) = Just [Right (DRec u (DVar v),Left t)]
-- Meta-variable: Solve.
simplify_unif_eq (TUEq (MTermR u (MTermT (TMeta mv))) t) = Just [Right ((DRec u (DMetaT mv)),Left t)]
-- More than one unifier: Leave as is.
simplify_unif_eq (TUEq (MTermR u mt) t) = Just [Left (TUEq (MTermR u mt) t)]
-- No unifier: Just verify that it holds, and return either unsatisfiable or no equations.
simplify_unif_eq (TUEq (MTermT t1) t2) = if (t1 == t2) then (Just []) else Nothing
-- Compatible predicates: simplify.
simplify_unif_eq (LUEq (MLitP p mts) (Lit q ts)) | p == q = maybe_concat (map (\pair -> simplify_unif_eq (TUEq (fst pair) (snd pair))) (zip mts ts))
-- Incompatible predicates: Unsatisfiable.
simplify_unif_eq (LUEq (MLitP p mts) (Lit q ts)) = Nothing
-- MLitL means meta-variable. Solve.
simplify_unif_eq (LUEq (MLitR u (MLitL (LitM mv))) l) = Just [Right ((DRec u (DMetaL mv)),Right l)]
-- More than one unifier: Leave as is.
simplify_unif_eq (LUEq (MLitR u (MLitL il)) l) = Just [Left (LUEq (MLitR u (MLitL il)) l)]
-- No unifier: Just verity that it holds, and return either unsatisfiable or no equations.
simplify_unif_eq (LUEq (MLitL l1) l2) = if (l1 == l2) then (Just []) else Nothing

maybe_concat :: [Maybe [t]] -> Maybe [t]
maybe_concat [] = Just []
maybe_concat (l:ls) = append_mb_mb l (maybe_concat ls)

append_mb_mb :: Maybe [t] -> Maybe [t] -> Maybe [t]
append_mb_mb Nothing _ = Nothing
append_mb_mb _ Nothing = Nothing
append_mb_mb (Just l1) (Just l2) = Just (l1++l2)

append_mb_x :: Maybe [t] -> [t] -> Maybe [t]
append_mb_x Nothing _ = Nothing
append_mb_x (Just l1) l2 = Just (l1++l2)

simplify_ueqs_fs :: FullSolution -> FullSolution
simplify_ueqs_fs (mvs,eqs,(inst,cs),(g,sol,ueqs)) = case r of {Nothing -> (mvs,eqs,(inst,[Unsatisfiable]),(g,sol,ueqs)); Just rueqs -> (mvs,eqs,(inst,cs),(g,sol,rueqs))} where r = simplify_ueqs_fs_helper ueqs

-- Returns Nothing if it is unsatisfiable.
simplify_ueqs_fs_helper :: [UnifierEquation] -> Maybe [UnifierEquation]
simplify_ueqs_fs_helper [] = Just []
simplify_ueqs_fs_helper (ueq:ueqs) = case r of {Nothing -> Nothing; Just rueqs -> case (simplify_ueqs_fs_helper ueqs) of {Nothing -> Nothing; Just rueqs2 -> Just ((simplify_ueqs_fs_helper_2 rueqs) ++ rueqs2)}} where r = simplify_unif_eq (simpl_side_unif_eq ueq)

simplify_ueqs_fs_helper_2 :: [Either UnifierEquation (Dependent,Either Term Literal)] -> [UnifierEquation]
simplify_ueqs_fs_helper_2 [] = []
simplify_ueqs_fs_helper_2 ((Left ueq):ueqs) = ueq:(simplify_ueqs_fs_helper_2 ueqs)
simplify_ueqs_fs_helper_2 ((Right _):ueqs) = simplify_ueqs_fs_helper_2 ueqs


update_graph_from_value_hdep_full :: FullSolution -> (Dependent,Either Term Literal) -> (FullSolution,[Dependent])
--update_graph_from_value_hdep_full (mvs,eqs,(inst,cs),(g,sol,ueqs)) x = ((mvs,eqs,(inst,cs),(rg,sol,ueqs ++ rueqs)),rl) where (rg,rl) = update_graph_from_value_hdep (g,sol,ueqs) x; rueqs = generate_unif_eqs_from_value_hdeps rg x
update_graph_from_value_hdep_full (mvs,eqs,(inst,cs),(g,sol,ueqs)) x = ((mvs,eqs,(inst,cs),(rg,sol,ueqs)),rl) where (rg,rl) = update_graph_from_value_hdep (g,sol,ueqs) x

generate_unif_eqs_from_value_hdeps :: DependencyGraph -> (Dependent,Either Term Literal) -> [UnifierEquation]
generate_unif_eqs_from_value_hdeps g (d,v) = map (generate_unif_eqs_from_value_hdep v) deps where n = find_node g d; deps = get_incoming_hdeps n
--generate_unif_eqs_from_value_hdeps g (d,v) = if (isNothing nmb) then [] else (map (generate_unif_eqs_from_value_hdep v) deps) where nmb = find_node_maybe g d; n = find_node g d; deps = get_incoming_hdeps n

generate_unif_eqs_from_value_hdep :: Either Term Literal -> HDependencyEdge -> UnifierEquation
generate_unif_eqs_from_value_hdep (Left t) (HDEdge (THDep f) ss _) = TUEq (lift_thdep (THDep f) ss) t
generate_unif_eqs_from_value_hdep (Right l) (HDEdge (LTHDep f) ss _) = LUEq (lift_lthdep (LTHDep f) ss) l
generate_unif_eqs_from_value_hdep (Right l) (HDEdge (LHDep f) s _) = LUEq (lift_lhdep (LHDep f) (head s)) l

update_graph_from_value_hdep :: PartiallySolvedDGraph -> (Dependent,Either Term Literal) -> (DependencyGraph,[Dependent])
-- Just update all horizontal dependencies going out of the node with the value.
-- We need to re-pick the dependencies each time, as it may be the same dependency more than once. So just map does not work before fold. Everything needs to be inside the fold. We implemented fold_with_update for this purpose.
update_graph_from_value_hdep (g,sol,ueqs) (d,v) = ((fold_with_update (\gg -> \sdep -> (update_hdep (del_hdep_from_source gg d sdep) sdep (update_hdep_from_value d v sdep))) (\gg -> \sdep -> update_hdep_from_value d v sdep) g deps),(d:(map get_htarget deps))) where deps = (get_outgoing_hdeps (find_node g d))
--update_graph_from_value_hdep (g,sol,ueqs) (d,v) = if (isNothing nmb) then (g,[]) else ((fold_with_update (\gg -> \sdep -> (update_hdep (del_hdep_from_source gg d sdep) sdep (update_hdep_from_value d v sdep))) (\gg -> \sdep -> update_hdep_from_value d v sdep) g deps),(d:(map get_htarget deps))) where nmb = find_node_maybe g d; deps = (get_outgoing_hdeps (find_node g d))

-- Purposely not defined for values that don't make sense.
update_hdep_from_value :: Dependent -> Either Term Literal -> HDependencyEdge -> HDependencyEdge
update_hdep_from_value d (Left vt) (HDEdge (THDep (FApp f ins)) ss t) = HDEdge (THDep (FApp f rins)) (rdeps ++ rrdeps) t where (rins,rdeps,rrdeps,rflag) = update_hdep_f_from_value d ss vt ins
update_hdep_from_value d (Left vt) (HDEdge (LTHDep (PApp p ins)) ss t) = HDEdge (LTHDep (PApp p rins)) (rdeps ++ rrdeps) t where (rins,rdeps,rrdeps,rflag) = update_hdep_f_from_value d ss vt ins
update_hdep_from_value d (Right vl) (HDEdge (LHDep (LEq LInDependent)) [s] t) | d == s = HDEdge (LHDep (LEq (LInFixed vl))) [] t

--data TermDependencyInput = TInDependent | TInFixed Term | TInRec TermHorizontalDependency
--data LitDependencyInput = LInDependent | LInFixed Literal
--data TermHorizontalDependency = FApp Function [TermDependencyInput]
--data LitTermHorizontalDependency = PApp Predicate [TermDependencyInput]
--data LitHorizontalDependency = LEq LitDependencyInput

--data HorizontalDependency = THDep TermHorizontalDependency | LTHDep LitTermHorizontalDependency | LHDep LitHorizontalDependency

-- The boolean indicates if we have already replaced the dependent. This is very useful for the recursive case.
-- The first list of dependents is the source dependents we have gone past, but not used.
-- the second is to be passed on recursive calls that happen at the top level (see doubly recursive case).
-- The resulting list of dependents is the concatenation of these two.
update_hdep_f_from_value :: Dependent -> [Dependent] -> Term -> [TermDependencyInput] -> ([TermDependencyInput],[Dependent],[Dependent],Bool)
update_hdep_f_from_value d (s:ss) v (TInDependent:ins) | d == s = ((TInFixed v):ins,[],ss,True)
update_hdep_f_from_value d (s:ss) v (TInDependent:ins) | d /= s = (TInDependent:recins,s:recdeps,recrdeps,rflag) where (recins,recdeps,recrdeps,rflag) = update_hdep_f_from_value d ss v ins
update_hdep_f_from_value d ss v [] = ([],[],ss,False)
update_hdep_f_from_value d ss v ((TInFixed ov):ins) = ((TInFixed ov):recins,recdeps,recrdeps,rflag) where (recins,recdeps,recrdeps,rflag) = update_hdep_f_from_value d ss v ins
update_hdep_f_from_value d ss v ((TInRec (FApp f rins)):ins) = if recflag1 then (((TInRec (FApp f recins1)):ins),recdeps1,recrdeps1,True) else (((TInRec (FApp f rins)):recins2),recdeps1++recdeps2,recrdeps2,recflag2) where (recins1,recdeps1,recrdeps1,recflag1) = update_hdep_f_from_value d ss v rins; (recins2,recdeps2,recrdeps2,recflag2) = update_hdep_f_from_value d recrdeps1 v ins

-- This is horrible. I hate it. What one does for efficiency. Given a dependent and a list, we traverse it. Once we find it, we remove it, partially evaluate the function and return the resulting list and the resulting function. However, in order to do this efficiently, what we do instead is that we traverse the list, looking for the dependent. Once we find it, we return the list without it, AND a function that, given another function, partially evaluates it at that position.
--update_hdep_f_from_value :: Dependent -> [Dependent] -> (([a] -> b) -> (a -> [a] -> b),[Dependent])
-- If the next source is the dependent, update it.
--update_hdep_f_from_value d (s:ss) | d == s = ((\f -> \vt -> \ts -> partial_apply_list f vt ts),ss)
-- If it is not this one, keep it and recurse.
--update_hdep_f_from_value d (s:ss) = ((\f -> \vt -> \ts -> (fst rec) (partial_apply_list f (case ts of (t:tts) -> t)) vt (case ts of (t:tts) -> tts)),(s:(snd rec))) where rec = --update_hdep_f_from_value d ss

update_graph_from_value_eqdep :: PartiallySolvedDGraph -> (Dependent,Either Term Literal) -> (DependencyGraph,[Dependent])
update_graph_from_value_eqdep (g,sol,ueqs) (d,_) = (g,eqdep_elems (find_eqdep g d))

update_graph_from_value_vdep :: FullSolution -> (Dependent,Either Term Literal) -> (FullSolution,[Dependent])
-- Calculate new constraints, remove the old dependent, apply the new constraints. This will build new horizontal dependencies AND new vertical dependencies. 
-- In theory, we would only need to re-check dependents either related to the original dependent, or those included or related to new dependents with the new generated constraints. 
-- However, calculating this set is too complicated, so we just add all dependents. We take this into account when we do update through vertical dependencies, to do this only when no more horizontal
-- dependencies can be updated and minimize recalculations.
-- IMPORTANT: We may have, for example, ux, vux, wvux and kvux. We FIRST update into wvux and kvux, then into vux; because at each update, we remove the dependent and therefore break the 
-- dependencies, so going from the bottom up is the best way to ensure we update all of them. We know that removing the one on the next level will not fuck up anything.
update_graph_from_value_vdep fs (d,(Left t)) = ((rmvs,reqs,(rinst,rcs),(rg,rsol,rueqs)),(map (get_dependent) (nodes rg))) where (rmvs,reqs,(rinst,rcs),(rg,rsol,rueqs)) = update_graph_from_value_vdep_rec fs (d,(Left (MTermT t)))
update_graph_from_value_vdep fs (d,(Right t)) = ((rmvs,reqs,(rinst,rcs),(rg,rsol,rueqs)),(map (get_dependent) (nodes rg))) where (rmvs,reqs,(rinst,rcs),(rg,rsol,rueqs)) = update_graph_from_value_vdep_rec fs (d,(Right (MLitL t)))

update_graph_from_value_vdep_rec :: FullSolution -> (Dependent,Either Metaterm Metaliteral) -> FullSolution
--update_graph_from_value_vdep_rec (mvs,(inst,cs),(g,sol)) (d,v) = update_graph_from_value_vdep_step (rmvs1,(rinst1,rcs1),(rgs1,rsol1)) (d,v) where (rmvs1,(rinst1,rcs1),(rgs1,rsol1)) = foldl (\fs -> \vdep -> update_graph_from_value_vdep_rec fs ((get_vtarget vdep),(propagate_mtl_through_vdep vdep v))) (mvs,(inst,cs),(g,sol)) (get_outgoing_vdeps (find_node g d))
update_graph_from_value_vdep_rec (mvs,eqs,(inst,cs),(g,sol,ueqs)) (d,v) = if ((elem Unsatisfiable rcs) || (elem Unsatisfiable rrcs) || (elem Unsatisfiable rrrcs)) then (mvs,eqs,(inst,[Unsatisfiable]),(g,sol,ueqs)) else (rrrrmvs,rrrreqs,(rrrrinst,rrrrcs),(rrrg,rrrsol,rrrrueqs)) where (rmvs,(rinst,rcs)) = recalculate_constraints_from_vdep_out_rec mvs (inst,cs) g d v; rrcs = map (apply_graph_solution_cstr sol) rcs; (rrrmvs,(rrrinst,rrrcs)) = all_simpl_cstr rmvs (rinst,rrcs); rg = remove_nodes_vdep_rec g d; (rrrrmvs,rrrreqs,(rrrrinst,rrrrcs),(rrrg,rrrsol,rrrueqs)) = update_graph_with_constraints_fsol (rrrmvs,eqs,(rrrinst,[]),(rg,sol,ueqs)) rrrcs; rrrrueqs = map (update_ueq_from_vdep (d,v)) rrrueqs

update_ueq_from_vdep :: (Dependent,Either Metaterm Metaliteral) -> UnifierEquation -> UnifierEquation
-- We only replace within the outermost unifier.
update_ueq_from_vdep (d,(Left mtv)) (TUEq (MTermR u mt) t) = TUEq (MTermR u (replace_mterm_mterm (all_simpl_mterm (metaterm_from_depnode d)) mtv mt)) t
update_ueq_from_vdep (d,(Left mtv)) (LUEq (MLitR u ml) l) = LUEq (MLitR u (replace_mterm_mlit (all_simpl_mterm (metaterm_from_depnode d)) mtv ml)) l
update_ueq_from_vdep (d,(Right mlv)) (LUEq (MLitR u ml) l) = LUEq (MLitR u (replace_mlit_mlit (all_simpl_mlit (metalit_from_depnode d)) mlv ml)) l

remove_nodes_vdep_rec :: DependencyGraph -> Dependent -> DependencyGraph
--remove_nodes_vdep_rec g d = add_node (remove_node (foldl (\h -> \vdep -> remove_nodes_vdep_rec h (get_vtarget vdep)) g (get_outgoing_vdeps (find_node g d))) d) d
remove_nodes_vdep_rec g d = remove_node (foldl (\h -> \vdep -> remove_nodes_vdep_rec h (get_vtarget vdep)) g (get_outgoing_vdeps (find_node g d))) d
--remove_nodes_vdep_rec g d = if (isNothing nmb) then g else (remove_node (foldl (\h -> \vdep -> remove_nodes_vdep_rec h (get_vtarget vdep)) g (get_outgoing_vdeps (find_node g d))) d) where nmb = find_node_maybe g d

propagate_mtl_through_vdep :: VDependencyEdge -> Either Metaterm Metaliteral -> Either Metaterm Metaliteral
propagate_mtl_through_vdep (VDEdge _ s t) (Left mt) = Left (replace_mterm_mterm (metaterm_from_depnode s) mt (metaterm_from_depnode t))
propagate_mtl_through_vdep (VDEdge _ s t) (Right ml) = Right (replace_mlit_mlit (metalit_from_depnode s) ml (metalit_from_depnode t))
--propagate_mtl_through_vdep (VDEdge (TVDep f) s t) (Left mt) = Left (f mt)
--propagate_mtl_through_vdep (VDEdge (LVDep f) s t) (Right ml) = Right (f ml)

--update_graph_from_value_vdep_step :: FullSolution -> (Dependent,Either Metaterm Metaliteral) -> FullSolution
--update_graph_from_value_vdep_step (mvs,(inst,cs),(g,sol)) (d,v) = (rmvs,(rinst,[]),(rg,sol)) where n = find_node g d; (rmvs,(rinst,rcs)) = foldl (\mvusol -> \vdep -> recalculate_constraints_from_vdep (fst mvusol) (snd mvusol) g vdep v) (mvs,(inst,cs)) (get_outgoing_vdeps n); rg = update_graph_with_constraints g rcs

recalculate_constraints_from_vdep_rec :: [Metavariable] -> UnifSolution -> DependencyGraph -> VDependencyEdge -> Either Metaterm Metaliteral -> ([Metavariable],UnifSolution)
recalculate_constraints_from_vdep_rec mvs (inst,cs) g (VDEdge dep s t) v = recalculate_constraints_from_vdep rmvs (rinst,rcs) g (VDEdge dep s t) v where n = find_node g t; (rmvs,(rinst,rcs)) = recalculate_constraints_from_vdep_out_rec mvs (inst,cs) g t (propagate_mtl_through_vdep (VDEdge dep s t) v)
--recalculate_constraints_from_vdep_rec mvs (inst,cs) g (VDEdge dep s t) v = if (isNothing nmb) then (mvs,(inst,cs)) else (recalculate_constraints_from_vdep rmvs (rinst,rcs) g (VDEdge dep s t) v) where nmb = find_node_maybe g t; n = find_node g t; (rmvs,(rinst,rcs)) = recalculate_constraints_from_vdep_out_rec mvs (inst,cs) g t (propagate_mtl_through_vdep (VDEdge dep s t) v)

recalculate_constraints_from_vdep_out_rec :: [Metavariable] -> UnifSolution -> DependencyGraph -> Dependent -> Either Metaterm Metaliteral -> ([Metavariable],UnifSolution)
recalculate_constraints_from_vdep_out_rec mvs (inst,cs) g d v = foldl (\mvusol -> \vdep -> recalculate_constraints_from_vdep_rec (fst mvusol) (snd mvusol) g vdep v) (mvs,(inst,cs)) (get_outgoing_vdeps (find_node g d))
--recalculate_constraints_from_vdep_out_rec mvs (inst,cs) g d v = if (isNothing nmb) then (mvs,(inst,cs)) else (foldl (\mvusol -> \vdep -> recalculate_constraints_from_vdep_rec (fst mvusol) (snd mvusol) g vdep v) (mvs,(inst,cs)) (get_outgoing_vdeps (find_node g d))) where nmb = find_node_maybe g d

recalculate_constraints_from_vdep :: [Metavariable] -> UnifSolution -> DependencyGraph -> VDependencyEdge -> Either Metaterm Metaliteral -> ([Metavariable],UnifSolution)
-- Take all horizontal dependencies on which the target of the vertical dependency is implied, and combine the solutions.
recalculate_constraints_from_vdep mvs (inst,cs) g (VDEdge _ s t) (Left mt) = recalculate_constraints_eqdep mvs1 (inst1,cs1) (Left (all_simpl_mterm (metaterm_from_depnode s))) (Left mt) g [t] where n = find_node g t; (mvs1,(inst1,cs1)) = recalculate_constraints_hdep mvs (inst,cs) (Left (all_simpl_mterm (metaterm_from_depnode s))) (Left mt) ((get_outgoing_hdeps n) ++ (get_incoming_hdeps n)) 
--recalculate_constraints_from_vdep mvs (inst,cs) g (VDEdge _ s t) (Left mt) = if (isNothing nmb) then (mvs,(inst,cs)) else (recalculate_constraints_eqdep mvs1 (inst1,cs1) (Left (all_simpl_mterm (metaterm_from_depnode s))) (Left mt) g [t]) where nmb = find_node_maybe g t; n = find_node g t; (mvs1,(inst1,cs1)) = recalculate_constraints_hdep mvs (inst,cs) (Left (all_simpl_mterm (metaterm_from_depnode s))) (Left mt) ((get_outgoing_hdeps n) ++ (get_incoming_hdeps n)) 
recalculate_constraints_from_vdep mvs (inst,cs) g (VDEdge _ s t) (Right ml) = recalculate_constraints_eqdep mvs1 (inst1,cs1) (Right (all_simpl_mlit (metalit_from_depnode s))) (Right ml) g [t] where n = find_node g t; (mvs1,(inst1,cs1)) = recalculate_constraints_hdep mvs (inst,cs) (Right (all_simpl_mlit (metalit_from_depnode s))) (Right ml) ((get_outgoing_hdeps n) ++ (get_incoming_hdeps n))
--recalculate_constraints_from_vdep mvs (inst,cs) g (VDEdge _ s t) (Right ml) = if (isNothing nmb) then (mvs,(inst,cs)) else (recalculate_constraints_eqdep mvs1 (inst1,cs1) (Right (all_simpl_mlit (metalit_from_depnode s))) (Right ml) g [t]) where nmb = find_node_maybe g t; n = find_node g t; (mvs1,(inst1,cs1)) = recalculate_constraints_hdep mvs (inst,cs) (Right (all_simpl_mlit (metalit_from_depnode s))) (Right ml) ((get_outgoing_hdeps n) ++ (get_incoming_hdeps n))  

recalculate_constraints_eqdep :: [Metavariable] -> UnifSolution -> Either Metaterm Metaliteral -> Either Metaterm Metaliteral -> DependencyGraph -> [Dependent] -> ([Metavariable],UnifSolution)
--recalculate_constraints_eqdep mvs (inst,cs) (Left mt1) (Left mt2) g ds = (mvs1,(inst1,map (replace_mterm_cstr mt1 mt2) cs1)) where (mvs1,(inst1,cs1)) = all_simpl_cstr mvs (inst,cs ++ (map_maybe (maybe_recalculate_constraint_from_eqdep g) ds))
--recalculate_constraints_eqdep mvs (inst,cs) (Right mt1) (Right mt2) g ds = (mvs1,(inst1,map (replace_mlit_cstr mt1 mt2) cs1)) where (mvs1,(inst1,cs1)) = all_simpl_cstr mvs (inst,cs ++ (map_maybe (maybe_recalculate_constraint_from_eqdep g) ds))
-- Replace first, simplify later
recalculate_constraints_eqdep mvs (inst,cs) (Left mt1) (Left mt2) g ds = all_simpl_cstr mvs (inst,map (replace_mterm_cstr mt1 mt2) (cs ++ (map_maybe (maybe_recalculate_constraint_from_eqdep g) ds)))
recalculate_constraints_eqdep mvs (inst,cs) (Right ml1) (Right ml2) g ds = all_simpl_cstr mvs (inst,map (replace_mlit_cstr ml1 ml2) (cs ++ (map_maybe (maybe_recalculate_constraint_from_eqdep g) ds)))

maybe_recalculate_constraint_from_eqdep :: DependencyGraph -> Dependent -> Maybe Constraint
maybe_recalculate_constraint_from_eqdep g d1 = case other of {Nothing -> Nothing; Just d2 -> Just (recalculate_constraint_from_eqdep d1 d2)} where other = find_other_eqdep_dep d1 (find_eqdep g d1)

find_other_eqdep_dep :: Dependent -> EqDependencyClass -> Maybe Dependent
find_other_eqdep_dep d1 (EqDep _ d2) | d1 /= d2 = Just d2
find_other_eqdep_dep d1 (EqDep s _) = find_other_eqdep_list d1 (Map.keys s)

find_other_eqdep_list :: Dependent -> [Dependent] -> Maybe Dependent
find_other_eqdep_list d1 [] = Nothing
find_other_eqdep_list d1 (d2:ds) | d1 == d2 = find_other_eqdep_list d1 ds
find_other_eqdep_list d1 (d2:ds) = Just d2


recalculate_constraint_from_eqdep :: Dependent -> Dependent -> Constraint
recalculate_constraint_from_eqdep d1 d2 | is_dependent_term d1 = Tcstr (all_simpl_mterm (metaterm_from_depnode d1)) (all_simpl_mterm (metaterm_from_depnode d2))
recalculate_constraint_from_eqdep d1 d2 = Lcstr (all_simpl_mlit (metalit_from_depnode d1)) (all_simpl_mlit (metalit_from_depnode d2))

-- We need to know the previous meta-variables and instantiation, although the constraints will likely be empty.
recalculate_constraints_hdep :: [Metavariable] -> UnifSolution -> Either Metaterm Metaliteral -> Either Metaterm Metaliteral -> [HDependencyEdge] -> ([Metavariable],UnifSolution)
--recalculate_constraints_hdep mvs (inst,cs) (Left mt1) (Left mt2) es = (mvs1,(inst1,map (replace_mterm_cstr mt1 mt2) cs1)) where (mvs1,(inst1,cs1)) = all_simpl_cstr mvs (inst,cs ++ (map rebuild_constraint_from_hdep es))
--recalculate_constraints_hdep mvs (inst,cs) (Right ml1) (Right ml2) es = (mvs1,(inst1,map (replace_mlit_cstr ml1 ml2) cs1)) where (mvs1,(inst1,cs1)) = all_simpl_cstr mvs (inst,cs ++ (map rebuild_constraint_from_hdep es))
-- Replace first, simplify later.
recalculate_constraints_hdep mvs (inst,cs) (Left mt1) (Left mt2) es = all_simpl_cstr mvs (inst,map (replace_mterm_cstr mt1 mt2) (cs ++ (map rebuild_constraint_from_hdep es)))
recalculate_constraints_hdep mvs (inst,cs) (Right ml1) (Right ml2) es = all_simpl_cstr mvs (inst,map (replace_mlit_cstr ml1 ml2) (cs ++ (map rebuild_constraint_from_hdep es)))

-- all_simpl_cstr :: [Metavariable] -> UnifSolution -> ([Metavariable],UnifSolution)

rebuild_constraint_from_hdep :: HDependencyEdge -> Constraint
rebuild_constraint_from_hdep (HDEdge (THDep dep) ss t) = Tcstr (lift_thdep (THDep dep) ss) (metaterm_from_depnode t)
rebuild_constraint_from_hdep (HDEdge (LTHDep dep) ss t) = Lcstr (lift_lthdep (LTHDep dep) ss) (metalit_from_depnode t)
rebuild_constraint_from_hdep (HDEdge (LHDep dep) ss t) = Lcstr (lift_lhdep (LHDep dep) (head ss)) (metalit_from_depnode t)


factorize_update_clean :: ExtendedSignature -> FullSolution -> FullSolution
factorize_update_clean sig fs = clean_dep_graph_fs (factorize_and_update_graph sig fs)

-- Recursively factorizes, and updates until there is nothing left to update (and so nothing to factorize).
factorize_and_update_graph :: ExtendedSignature -> FullSolution -> FullSolution
factorize_and_update_graph sig fs = if (is_fullsol_unsatisfiable rfs) then rfs else (case rdeps of {[] -> rfs; remaining -> factorize_and_update_graph sig (update_graph_all sig rfs remaining [])}) where (rfs,rdeps) = factorize_dgraph_all fs
--factorize_and_update_graph fs = if (is_fullsol_unsatisfiable rfs) then rfs else (case rdeps of {[] -> rfs; remaining -> factorize_and_update_graph (update_graph_all rfs (maybe_sol_from_list (get_gsol fs) (map get_dependent (nodes (get_graph fs)))) [])}) where (rfs,rdeps) = factorize_dgraph_all fs

is_fullsol_unsatisfiable :: FullSolution -> Bool
is_fullsol_unsatisfiable (_,_,(_,cs),_) | (elem Unsatisfiable cs) = True
is_fullsol_unsatisfiable (_,_,_,((DGraph _ _ Cycled),_,_)) = True
is_fullsol_unsatisfiable (_,_,_,(_,sol,_)) | multiple_solutions_dgraph sol = True
is_fullsol_unsatisfiable _ = False

multiple_solutions_dgraph :: DependencyGraphSolution -> Bool
--multiple_solutions_dgraph sol = any (isPlentyS . fun) (map fst sol) where fun = obtain_solution_function (\d -> NothingS) sol
multiple_solutions_dgraph sol = multiple_solutions_dgraph_helper [] sol

multiple_solutions_dgraph_helper :: [Dependent] -> DependencyGraphSolution -> Bool
multiple_solutions_dgraph_helper _ [] = False
multiple_solutions_dgraph_helper ds ((d1,v1):dvs) | elem d1 ds = True
multiple_solutions_dgraph_helper ds ((d1,v1):dvs) = multiple_solutions_dgraph_helper (d1:ds) dvs

obtain_solution_function :: (Dependent -> MaybePlenty (Either Term Literal)) -> DependencyGraphSolution -> (Dependent -> MaybePlenty (Either Term Literal))
obtain_solution_function f [] = f
obtain_solution_function f ((d1,v1):dvs) = obtain_solution_function
	(\d2 ->
		if (d1 == d2)
		then
			(case (f d2) of
			{
				NothingS -> JustS v1;
				JustS v2 -> PlentyS;
				PlentyS -> PlentyS
			})
		else
			(f d2)
	)
	dvs

-- For factorized, propagated and clean graphs. Checks if the graph has no nodes left.
is_fullsol_solved :: FullSolution -> Bool
is_fullsol_solved (_,_,_,(g,_,_)) = null (nodes g)

-- factorize_dgraph_all :: FullSolution -> (FullSolution,[(Dependent,Either Term Literal)])
-- update_graph_all :: FullSolution -> [(Dependent, Either Term Literal)] -> [(Dependent, Either Term Literal)] -> FullSolution

-- Lifting dependencies for partial evaluations or updates.

witness_variables :: [t] -> [Variable]
witness_variables l = witness_variables_rec (-1) l

witness_variables_rec :: Int -> [t] -> [Variable]
witness_variables_rec _ [] = []
witness_variables_rec i (x:xs) = ((Var i):(witness_variables_rec (i-1) xs))

replace_witness_variables_thdep :: Metaterm -> [Metaterm] -> Metaterm
replace_witness_variables_thdep mt reps = replace_witness_variables_thdep_rec mt (-1) reps

replace_witness_variables_thdep_rec :: Metaterm -> Int -> [Metaterm] -> Metaterm
replace_witness_variables_thdep_rec mt _ [] = mt
replace_witness_variables_thdep_rec mt i (rep:reps) = replace_witness_variables_thdep_rec (replace_mterm_mterm (MTermT (TVar (Var i))) rep mt) (i-1) reps

replace_witness_variables_lthdep :: Metaliteral -> [Metaterm] -> Metaliteral
replace_witness_variables_lthdep ml reps = replace_witness_variables_lthdep_rec ml (-1) reps

replace_witness_variables_lthdep_rec :: Metaliteral -> Int -> [Metaterm] -> Metaliteral
replace_witness_variables_lthdep_rec ml _ [] = ml
replace_witness_variables_lthdep_rec ml i (rep:reps) = replace_witness_variables_lthdep_rec (replace_mterm_mlit (MTermT (TVar (Var i))) rep ml) (i-1) reps

witness_metavar :: Metavariable
witness_metavar = Metavar (-1)

replace_witness_variable_lhdep :: Metaliteral -> Metaliteral -> Metaliteral
replace_witness_variable_lhdep ml rep = replace_mlit_mlit (MLitL (LitM witness_metavar)) rep ml

-- ((More less) old) way.
--data TermDependencyInput = TInDependent | TInFixed Term | TInRec TermHorizontalDependency
--data LitDependencyInput = LInDependent | LInFixed Literal
--data TermHorizontalDependency = FApp Function [TermDependencyInput]
--data LitTermHorizontalDependency = PApp Predicate [TermDependencyInput]
--data LitHorizontalDependency = LEq LitDependencyInput

--data HorizontalDependency = THDep TermHorizontalDependency | LTHDep LitTermHorizontalDependency | LHDep LitHorizontalDependency

lift_thdep :: HorizontalDependency -> [Dependent] -> Metaterm
lift_thdep (THDep dep) ds = all_simpl_mterm (fst (lift_thdep_helper dep ds))

lift_thdep_helper :: TermHorizontalDependency -> [Dependent] -> (Metaterm,[Dependent])
lift_thdep_helper (FApp f ins) ds = (MTermF f (reverse rmts),rdeps) where (rmts,rdeps) = foldl lift_thdep_helper_3 ([],ds) ins

lift_thdep_helper_2 :: TermDependencyInput -> [Dependent] -> (Metaterm,[Dependent])
lift_thdep_helper_2 TInDependent (d:ds) = (metaterm_from_depnode d,ds)
lift_thdep_helper_2 (TInFixed t) ds = (MTermT t,ds)
lift_thdep_helper_2 (TInRec rec) ds = lift_thdep_helper rec ds

-- To fold.
-- NOTE: The first result of this function needs to be reversed before using.
lift_thdep_helper_3 :: ([Metaterm],[Dependent]) -> TermDependencyInput -> ([Metaterm],[Dependent])
lift_thdep_helper_3 (mts,ds) i = (rmt:mts,rdeps) where (rmt,rdeps) = lift_thdep_helper_2 i ds

lift_lthdep :: HorizontalDependency -> [Dependent] -> Metaliteral
lift_lthdep (LTHDep dep) ds = all_simpl_mlit (fst (lift_lthdep_helper dep ds))

lift_lthdep_helper :: LitTermHorizontalDependency -> [Dependent] -> (Metaliteral,[Dependent])
lift_lthdep_helper (PApp p ins) ds = (MLitP p (reverse rmts),rdeps) where (rmts,rdeps) = foldl lift_thdep_helper_3 ([],ds) ins

lift_lhdep :: HorizontalDependency -> Dependent -> Metaliteral
lift_lhdep (LHDep (LEq LInDependent)) d = all_simpl_mlit (metalit_from_depnode d)
lift_lhdep (LHDep (LEq (LInFixed l))) _ = all_simpl_mlit (MLitL l)


-- (Less old) way.
--lift_thdep :: HorizontalDependency -> [Dependent] -> Metaterm
-- This is a bit ugly, with better formalization would not be necessary, but no time now.
-- We use negatively indexed variables as variables that we assume do not happen in normal terms, as a way to witness what the dependency does to them, and then replace them with the dependents.
--lift_thdep (THDep f) ds = replace_witness_variables_thdep mt reps where t = f (map TVar (witness_variables ds)); mt = (all_simpl_mterm (MTermT t)); reps = map metaterm_from_depnode ds

--lift_lthdep :: HorizontalDependency -> [Dependent] -> Metaliteral
--lift_lthdep (LTHDep f) ds = replace_witness_variables_lthdep ml reps where l = f (map TVar (witness_variables ds)); ml = (all_simpl_mlit (MLitL l)); reps = map metaterm_from_depnode ds

--lift_lhdep :: HorizontalDependency -> Dependent -> Metaliteral
--lift_lhdep (LHDep f) d = replace_witness_variable_lhdep ml rep where l = f (LitM witness_metavar); ml = (all_simpl_mlit (MLitL l)); rep = metalit_from_depnode d

-- Old way, made invalid assumptions about equal unifiers on all dependents.
-- If the dependency has no arguments, then the resulting meta-term is just the lifting of the resulting term.
--lift_thdep (THDep f) [] = MTermT (f [])
-- The outer-most unifier needs to be the same in all meta-terms, so we just take the first one.
--lift_thdep (THDep f) (d:ds) | not (has_unifier d) = MTermT (f (map term_from_dependent (d:ds)))
--lift_thdep dep (d:ds) = MTermR (get_unifier_dependent d) (lift_thdep dep (map get_inner_dependent (d:ds)))

--lift_lthdep :: HorizontalDependency -> [Dependent] -> Metaliteral
--lift_lthdep (LTHDep f) [] = MLitL (f [])
--lift_lthdep (LTHDep f) (d:ds) | not (has_unifier d) = MLitL (f (map term_from_dependent (d:ds)))
--lift_lthdep dep (d:ds) = MLitR (get_unifier_dependent d) (lift_lthdep dep (map get_inner_dependent (d:ds)))

--lift_lhdep :: HorizontalDependency -> Dependent -> Metaliteral
--lift_lhdep (LHDep f) d | not (has_unifier d) = MLitL (f (lit_from_dependent d))
--lift_lhdep dep d = MLitR (get_unifier_dependent d) (lift_lhdep dep (get_inner_dependent d))

-- Original, new one, where to replace.
-- We assume that it has been simplified, so functions are outer-most.
replace_mterm_mterm :: Metaterm -> Metaterm -> Metaterm -> Metaterm
replace_mterm_mterm o n x | x == o = n
replace_mterm_mterm o n (MTermR u mt) = MTermR u (replace_mterm_mterm o n mt)
replace_mterm_mterm o n (MTermF f mts) = MTermF f (map (replace_mterm_mterm o n) mts)
replace_mterm_mterm _ _ x = x

replace_mterm_mlit :: Metaterm -> Metaterm -> Metaliteral -> Metaliteral
replace_mterm_mlit o n (MLitR u ml) = MLitR u (replace_mterm_mlit o n ml)
replace_mterm_mlit o n (MLitP p mts) = MLitP p (map (replace_mterm_mterm o n) mts)
replace_mterm_mlit _ _ x = x

replace_mlit_mlit :: Metaliteral -> Metaliteral -> Metaliteral -> Metaliteral
replace_mlit_mlit o n x | x == o = n
replace_mlit_mlit o n (MLitR u ml) = MLitR u (replace_mlit_mlit o n ml)
replace_mlit_mlit _ _ x = x

replace_mterm_cstr :: Metaterm -> Metaterm -> Constraint -> Constraint
replace_mterm_cstr _ _ Unsatisfiable = Unsatisfiable
replace_mterm_cstr o n (Tcstr l r) = Tcstr (replace_mterm_mterm o n l) (replace_mterm_mterm o n r)
replace_mterm_cstr o n (Lcstr l r) = Lcstr (replace_mterm_mlit o n l) (replace_mterm_mlit o n r)

replace_mlit_cstr :: Metaliteral -> Metaliteral -> Constraint -> Constraint
replace_mlit_cstr _ _ Unsatisfiable = Unsatisfiable
replace_mlit_cstr o n (Tcstr l r) = Tcstr l r
replace_mlit_cstr o n (Lcstr l r) = Lcstr (replace_mlit_mlit o n l) (replace_mlit_mlit o n l)


rest :: [t] -> [t]
rest [] = []
rest (x:xs) = xs






-- We know, however, that there must be one first unifier with no multiple unifier dependents, so among those, we can in the worst case enumerate over meta-variables.
-- Choosing values from the dependency graph, or enumerating.
-- The rules are as follows:
--	- Possibly problematic dependents (dependents that may depend on other things but about which we do not yet know) are:
--		* Dependents containing meta-variables, of course.
--		* Dependents with more than one unifier.
--		* Dependents for which there is a dependent containing a meta-variable or a dependent with more than one unifier which may, after application, end up
--			being the same.
--	- That is, non-problematic dependents are those which contain just one unifier and a variable and for which there can be no possible incoming dependence.
--	- If a root equivalence class contains only non-problematic dependents, we can safely assign one value to them, and propagate.
--	- In other case, we know that there must be a first unifier out of those unassigned in the graph. At the level of that unifier,
--		there will necessarily be no dependents with more than one unifier.
--	- Within those cases, the "least bad" case is when there is a root class containing a dependent with just one unifier and a meta-variable.
--	- In such case, we enumerate over that meta-variable. (We choose the class with the least meta-variables to enumerate as little as possible (but this is just an heuristic which need not work always)).
--	- Original meta-variables can contain original variables. After each unifier, they can only contain image meta-variables of those unifiers. Furthermore, we can block some possibilities where that would imply an occurs check. This should help reduce the search a lot.
--	- On each enumeration, we update the graph accordingly and proceed.
--	- It is probably easier to enumerate on uC than on C, because then we can just replace the value on the graph and keep going, rather than updating the graph and thinking again what to do.
-- - In the worse case, when there are no non-problematic root classes, but also there is no root class with just one unifier and a meta-variable, we simply choose a random meta-variable and enumerate over it, updating the graph. At the very least, this converges.

-- Efficient way to encode relevant sets of variables
data VariableSet = Dom Unifier | Rg Unifier deriving (Eq, Show)

get_vars_set :: Int -> VariableSet -> [Variable]
get_vars_set n (Dom u) = get_domain_vars n u
get_vars_set n (Rg u) = get_range_vars n u

var_in_set :: Int -> VariableSet -> Variable -> Bool
var_in_set n (Dom u) v = (is_in_domain n u v)
var_in_set n (Rg u) v = (is_in_range n u v)

-- NOTE: Here we use the convention that unifiers and variables start at 0 and work regularly upwards.
-- Nothing means it is a base meta-variable (so in the domain of u0)
find_possible_vars_metavar :: [MetavariableEquation] -> Metavariable -> VariableSet
find_possible_vars_metavar [] mv = Dom (U 0)
find_possible_vars_metavar ((MetaEq tmv u smv):eqs) mv | tmv == mv = Rg u
find_possible_vars_metavar ((MetaEq tmv u smv):eqs) mv = find_possible_vars_metavar eqs mv


-- We return a list of variable sets, and any dependent consisting of a variable at one of those levels is a possibly hidden dependent.
-- The unifier parameter is the unifier at which level we want to look for possibly hidden dependents.
-- NOTE: The list may contain duplicates. Removing duplicates seems to be more effort than it is worth.
find_possibly_hidden_dependents :: FullSolution -> Unifier -> [VariableSet]
find_possibly_hidden_dependents (mvs,eqs,(inst,cs),(g,sol,ueqs)) u = find_possibly_hidden_dependents_helper eqs (map get_dependent (nodes g)) u

find_possibly_hidden_dependents_helper :: [MetavariableEquation] -> [Dependent] -> Unifier -> [VariableSet]
find_possibly_hidden_dependents_helper eqs [] u = []
-- u applied to a meta-variable: All those the meta-variable could contain.
find_possibly_hidden_dependents_helper eqs ((DRec v (DMetaT m)):ds) u | u == v = (find_possible_vars_metavar eqs m):(find_possibly_hidden_dependents_helper eqs ds u)
find_possibly_hidden_dependents_helper eqs ((DRec v (DMetaL m)):ds) u | u == v = (find_possible_vars_metavar eqs m):(find_possibly_hidden_dependents_helper eqs ds u)
-- u v SOMETHING: All those in the range of v.
find_possibly_hidden_dependents_helper eqs ((DRec v (DRec w sd)):ds) u | u == v = (Rg w):(find_possibly_hidden_dependents_helper eqs ds u)
-- Otherwise: No danger.
find_possibly_hidden_dependents_helper eqs (d:ds) u = find_possibly_hidden_dependents_helper eqs ds u

-- The possibly returned dependent is one dependent in the class which corresponds to a meta-variable. It includes the unifiers, so that we can, outside, create the new meta-variables and update the solution.
-- The integer is the number of base variables.
-- It returns Nothing if all root classes are non-valuable but none have meta-variables. In this case, we need to look for the least-depth meta-variable, pull it, and then enumerate over it. We do this outside this function.
find_best_root_class :: Int -> FullSolution -> Maybe (Dependent,Maybe Dependent)
-- There should always be at least one where all are single.
find_best_root_class n (mvs,eqs,(inst,cs),(g,sol,ueqs)) = case res of {Just (rrep,[],[]) -> Just (rrep,Nothing); Just (rrep,(h:hs),[]) -> Nothing; Just (rrep,hs,(m:ms)) -> Just (rrep,Just m); Nothing -> Nothing} where res = find_best_root_class_list n (mvs,eqs,(inst,cs),(g,sol,ueqs)) (map (find_eqdep g) (filter (\d -> not (is_solved sol d)) (roots g)))

-- Returns the representer, how many possibly hidden dependents it has and how many meta-variable dependents it has.
find_best_root_class_list :: Int -> FullSolution -> [EqDependencyClass] -> Maybe (Dependent,[Dependent],[Dependent])
-- We assume that it has at least one class, and at least one which does not contain non-single dependents
-- Or rather, if it does not, we return Nothing
find_best_root_class_list _ _ [] = Nothing
find_best_root_class_list n fs (c:[]) | has_unifier_c c && (not (has_multiple_unifs c)) = Just (eqdep_rep c,(has_hidden_deps n fs c),(has_metavars (get_graph fs) (eqdep_rep c)))
find_best_root_class_list n fs (c:[]) = Nothing
-- We try to avoid classes with hidden dependents but no meta-variables.
find_best_root_class_list n fs (c:cs) = case parc of {Nothing -> cparc; Just (prep,phid,pmv) -> (case cparc of {Nothing -> parc; Just (crep,chid,cmv) -> 
	if (null pmv) && (not (null phid)) then cparc else (
		if (null cmv) && (not (null chid)) then parc else (
			(if (length chid) + (length cmv) < (length phid) + (length pmv) then cparc else parc)))})}
	where cparc = find_best_root_class_list n fs (c:[]); parc = find_best_root_class_list n fs cs

has_hidden_deps :: Int -> FullSolution -> EqDependencyClass -> [Dependent]
has_hidden_deps n fs c | has_unifier (eqdep_rep c) = filter (is_hidden_dep n (find_possibly_hidden_dependents fs (get_unifier_dependent (eqdep_rep c)))) (eqdep_elems c)
has_hidden_deps n fs c = []

has_unifier_c :: EqDependencyClass -> Bool
has_unifier_c c = has_unifier (eqdep_rep c)

has_multiple_unifs :: EqDependencyClass -> Bool
has_multiple_unifs c = any (\d -> not (is_dependent_single d)) (eqdep_elems c)

-- This hurts. I need to include meta-variables even further down the tree, because after instantiation, they could be pulled backwards.
-- There is an alternative to this, implying partial instantiation of meta-variables, which we shall explore in the future, but I am not sure it would really get much better.
has_metavars :: DependencyGraph -> Dependent -> [Dependent]
has_metavars g d = has_metavars_rec g n where n = case (find_dagnode d (dag g)) of {Just x -> x}

has_metavars_rec :: DependencyGraph -> DAGNode Dependent -> [Dependent]
has_metavars_rec g (DAGNode d ns) = (filter is_dependent_metavar (eqdep_elems (find_eqdep g d))) ++ (concat (map (has_metavars_rec g) ns))

is_hidden_dep :: Int -> [VariableSet] -> Dependent -> Bool
is_hidden_dep n vss (DRec u (DVar v)) = any (\set -> (var_in_set n set v)) vss
-- If it is not a variable, then it is not a hidden dependent.
is_hidden_dep _ _ _ = False


-- We use an integer indicating the initial number of variables as an efficient way to describe the signature.
type Signature = ([Predicate],[Function],Int)

-- The terms that a dependent may instantiate to depend on:
--		- The signature
--		- What variable set (regarding unifiers) that dependent is at.
--		- Blocked variables that we know would imply occurs check.



-- A meta-variable partition indicates sets of meta-variables that may share added variables.
-- First integer is the number of initial (shared) variables. Then there is a list of integers, one for each partition of meta-variables, indicating how many of the following variables, in order, belong to each of the partitions.
-- For example, ([[A,B],[C]],2,[3,1]) means that there are in total six variables. The first two can appear in all meta-variables. The third to the fifth can only appear in A or B, and the 6th can only appear in C.
-- The same meta-variable may appear in more than one partition. This is necessary to deal with initial variables in the case where meta-variables have been standardized apart.
type MetavariablePartition = ([[Metavariable]],Int,[Int])

metavar_var_constraint :: MetavariablePartition -> Metavariable -> (Variable -> Bool)
metavar_var_constraint (pmvs,ninit,pns) mv = foldl (\c1 -> \c2 -> \v -> (c1 v) || (c2 v)) (\v -> case v of {Var i -> i < ninit}) (map metavar_var_constraint_helper_2 (metavar_var_constraint_helper pmvs pns ninit mv))

metavar_var_constraint_helper_2 :: (Int,Int) -> (Variable -> Bool)
metavar_var_constraint_helper_2 (nmin,nmax) (Var i) = ((i >= nmin) && (i < nmax))

-- The variables should be greater or equal to the first number and strictly less than the second.
metavar_var_constraint_helper :: [[Metavariable]] -> [Int] -> Int -> Metavariable -> [(Int,Int)]
metavar_var_constraint_helper [] [] _ _ = []
metavar_var_constraint_helper (pmv:pmvs) (n:ns) m mv | elem mv pmv = ((m,m+n):(metavar_var_constraint_helper pmvs ns (m+n) mv))
metavar_var_constraint_helper (pmv:pmvs) (n:ns) m mv = metavar_var_constraint_helper pmvs ns (m+n) mv

-- Skolem terms are created by using functions not in the signature (or in another Skolem term), and they are just regular terms.
-- The fourth element is a filter for instantiations. It is currently only used for when the signature has to be standardized apart and a meta-variable split in two, but they both are the same, except with different variables. It tells us how to update the other dependents when one meta-variable is instantiated.
type ExtendedSignature = (Signature,MetavariablePartition,[Term],[MetavariableLink])
-- type Signature = ([Predicate],[Function],Int)

get_metavar_links :: ExtendedSignature -> [MetavariableLink]
get_metavar_links (_,_,_,links) = links

type MetavariableLink = (Metavariable,[(Metavariable,Either Term Literal -> Either Term Literal)])

show_metavar_links :: Either Term Literal -> [MetavariableLink] -> String
show_metavar_links v ls = concat (map (show_metavar_link v) ls)

show_metavar_link :: Either Term Literal -> MetavariableLink -> String
show_metavar_link v (s,ls) = "From " ++ (show s)  ++ ":\n\n" ++ (concat (map (show_metavar_link_helper v s) ls))

show_metavar_link_helper :: Either Term Literal -> Metavariable -> (Metavariable,Either Term Literal -> Either Term Literal) -> String
show_metavar_link_helper v s (t,f) = "If " ++ (show s)  ++ " = " ++ (show_either_term_lit v) ++ ", then " ++ (show t) ++ " = " ++ (show_either_term_lit (f v)) ++ ".\n"

show_either_term_lit :: Either Term Literal -> String
show_either_term_lit (Left t) = (show t)
show_either_term_lit (Right l) = (show l)

-- Obtain a new Skolem term for the indicated meta-variable. It can also be used for other meta-variables but only if the variables implied make sense.
obtain_skolem_term :: ExtendedSignature -> Metavariable -> Term
obtain_skolem_term sig mv = TFun (Fun fidx (length args)) args where fidx = (find_max_function_idx sig) + 1; args = obtain_skolem_term_helper sig mv

maximum_helper :: Ord t => t -> [t] -> t
maximum_helper deflt [] = deflt
maximum_helper _ l = maximum l

find_max_function_idx :: ExtendedSignature -> Int
find_max_function_idx ((ps,fs,nvars),(pmvs,ninit,nmvs),sks,ifilt) = max maxfs maxsks where maxfs = (maximum_helper (-1) (map find_max_function_idx_helper_1 fs)); maxsks = (maximum_helper (-1) (map find_max_function_idx_helper_2 sks))

find_max_function_idx_helper_1 :: Function -> Int
find_max_function_idx_helper_1 (Fun x _) = x

find_max_function_idx_helper_2 :: Term -> Int
find_max_function_idx_helper_2 (TFun (Fun x _) _) = x

obtain_skolem_term_helper :: ExtendedSignature -> Metavariable -> [Term]
obtain_skolem_term_helper (_,(mvgs,ninit,mvvs),_,_) mv = (map (\i -> TVar (Var i)) [0..(ninit - 1)]) ++ (obtain_skolem_term_helper_2 mvgs mvvs mv ninit)

obtain_skolem_term_helper_2 :: [[Metavariable]] -> [Int] -> Metavariable -> Int -> [Term]
obtain_skolem_term_helper_2 [] [] _ _ = []
obtain_skolem_term_helper_2 (mvg:mvgs) (mvv:mvvs) mv offset | elem mv mvg = (map (\i -> TVar (Var i)) [offset..(offset+mvv-1)]) ++ (obtain_skolem_term_helper_2 mvgs mvvs mv (offset+mvv))
obtain_skolem_term_helper_2 (mvg:mvgs) (mvv:mvvs) mv offset = obtain_skolem_term_helper_2 mvgs mvvs mv (offset+mvv)



-------------------------------------------------
-- NOTE
--	All of this is very generic and beautiful, but I have run out of time and have not managed to enumerate terms using enumerations.
-- But it is not necessary really, as terms up to a certain depth are finite.
-- We can just do iterative deepening over lists, with only enumeration over depths. First ALL terms of depth 0, then ALL terms of depth 1, then ALL terms of depth 2, etc.
-------------------------------------------------
enumerate_lits_dependent :: (MetaunificationHeuristic hl ht) -> ExtendedSignature -> VariableSet -> [Variable] -> (Variable -> Bool) -> Enumeration (_,Literal)
enumerate_lits_dependent heur ((ps,fs,n),mpart,sks,ifilt) vs bans filt = diagonalize_h (\pred -> apply_enum_1_h (\terms -> Lit pred terms) (enumerate_lists (enumerate_terms_dependent_heur heur ((ps,fs,n),mpart,sks,ifilt) vs bans filt) (pred_arity pred))) (enum_from_list ps)

enumerate_terms_dependent :: ExtendedSignature -> VariableSet -> [Variable] -> (Variable -> Bool) -> Enumeration (_,Term)
enumerate_terms_dependent sig vs bans filt = Enum (((0,zeroes),tzeroes),f) (\idx -> \prev -> case prev of {(((d,l),ts),t) -> enumerate_terms_dependent_helper sig d l ts t}) where zeroes = zero_terms_dependent sig vs bans filt; f = head zeroes; tzeroes = tail zeroes; (_,_,sks,_) = sig

enumerate_terms_dependent_helper :: ExtendedSignature -> Int -> [Term] -> [Term] -> Term -> Maybe (((Int,[Term]),[Term]),Term)
enumerate_terms_dependent_helper sig d l ts t = case ts of 
	{
		[] -> case nd of {[] -> Nothing; otherwise -> enumerate_terms_dependent_helper sig (d+1) nd nd t};
		(rt:rts) -> Just (((d,l),rts),rt)
	}
	where nd = (terms_next_depth_dependent sig l)
--	where nd = if (d < 3) then (terms_next_depth_dependent sig l) else []

terms_next_depth_dependent :: ExtendedSignature -> [Term] -> [Term]
terms_next_depth_dependent ((_,fs,_),_,_,_) ts = concat (map (apply_fun_terms ts) (filter (\f -> arity f > 0) fs))

--terms_depth_dependent :: Signature -> VariableSet -> [Variable] -> Int -> [Term]
--terms_depth_dependent sig vs bans 0 = zero_terms_dependent sig vs bans
--terms_depth_dependent (ps,fs,n) vs bans i = concat (map (apply_fun_terms (terms_depth_dependent (ps,fs,n) vs bans (i-1))) (filter (\f -> arity f > 0) fs))

apply_fun_terms :: [Term] -> Function -> [Term]
apply_fun_terms ts f = map (\l -> TFun f l) (combinations (replicate (arity f) ts))

zero_terms_dependent :: ExtendedSignature -> VariableSet -> [Variable] -> (Variable -> Bool) -> [Term]
zero_terms_dependent sig vs bans filt = (map (\v -> TVar v) (vars_dependent sig vs bans filt)) ++ (map (\f -> TFun f []) (constants sig)) ++ (filter (filter_skolem_terms bans filt) sks) where (_,_,sks,_) = sig

constants :: ExtendedSignature -> [Function]
constants ((_,fs,_),_,_,_) = filter (\x -> arity x == 0) fs

vars_dependent :: ExtendedSignature -> VariableSet -> [Variable] -> (Variable -> Bool) -> [Variable]
vars_dependent ((_,_,n),_,_,_) vs bans filt = filter (\x -> (filt x) && (not (elem x bans))) (get_vars_set n vs)

filter_skolem_terms :: [Variable] -> (Variable -> Bool) -> (Term -> Bool)
filter_skolem_terms bans vfilt (TVar v) = (vfilt v) && (not (elem v bans))
filter_skolem_terms bans vfilt (TMeta _) = True
filter_skolem_terms bans vfilt (TFun f ts) = and (map (filter_skolem_terms bans vfilt) ts)


-- Given a dependent, returns the set of variables that cannot possibly occur in the instantiation of the meta-variable, as it would necessarily mean an occurs check.
-- There are other cases where certain instantiations could imply an occurs check or even a unification failure, but not others. We just try those and have confidence in detecting the 
-- impossibilities through other parts of the algorithm.
--forbidden_vars_metavar :: DependencyGraph -> Dependent -> [Variable]


--enumerate_terms_depth :: Signature -> VariableSet -> [Variable] -> Int -> Enumeration (Either _ _,Term)
--enumerate_terms_depth sig vs bans 0 = enum_hleft_h (enumerate_zero_terms_dependent sig vs bans)
--enumerate_terms_depth sig vs bans n = enum_hright_h (diagonalize_h (enumerate_terms_function (enumerate_terms_depth sig vs bans (n-1))) (enumerate_functions sig))



--enumerate_functions :: Signature -> Enumeration ([Function],Function)
--enumerate_functions (fs,_) = if (null l) then (single_enum ([],Fun (-2) 1)) else (enum_from_list l) where l = filter (\x -> arity x > 0) fs

-- Assumed that it is not a constant.
--enumerate_terms_function :: Enumeration (h1,Term) -> Function -> Enumeration (_,Term)
--enumerate_terms_function e f = apply_enum_1_h (\l -> TFun f l) (enumerate_lists e (arity f))




-- As ugly as it may be, the easiest thing is to consider constants aside when enumerating terms of zero depth.
--enumerate_zero_terms_dependent :: Signature -> VariableSet -> [Variable] -> Enumeration (_,Term)
--enumerate_zero_terms_dependent sig vs bans = concat_enums_h (apply_enum_1_h (\v -> TVar v) (enumerate_vars_dependent sig vs bans)) (apply_enum_1_h (\f -> TFun f []) (enumerate_constants sig))

-- If there are no constants, we add one. This is horrible, but it is because enumerators need to have at least one element and it is way too late to fix that.
--enumerate_constants :: Signature -> Enumeration ([Function],Function)
--enumerate_constants (fs,_) = if (null l) then (single_enum ([],Fun (-1) 0)) else (enum_from_list l) where l = filter (\x -> arity x == 0) fs

--enumerate_vars_dependent :: Signature -> VariableSet -> [Variable] -> Enumeration ([Variable],Variable)
--enumerate_vars_dependent (_,n) vs bans = enum_from_list l where l = filter (\x -> not (elem x bans)) (get_vars_set n vs)




-- Diagonalization
-- In some cases enumeration is most efficient by using the last value, in others by knowing which value we are enumerating (index). In order to enable both, we give both values.
data Enumeration t = Enum t (Int -> t -> Maybe t)

type Enumerator t = (Int -> t -> Maybe t)

single_enum :: t -> Enumeration t
single_enum x = Enum x (\idx -> \prev -> Nothing)

get_enumerator :: Enumeration t -> Enumerator t
get_enumerator (Enum _ x) = x

-- Alternate
--concat_enums :: Enumeration t -> Enumeration t -> Enumeration ((Bool,Maybe t),t)
--concat_enums (Enum e10 fe1) (Enum e20 fe2) = Enum ((False,Just e20),e10) (\idx -> \x -> case x of {((False,Just n2),c) -> Just ((True,fe1 ((quot idx 2) + 1) c),n2); ((True,Just n1),c) -> Just ((False,fe2 (quot idx 2) c),n1); ((False,Nothing),c)((,Nothing),Nothing) -> Nothing})

enum_first :: Enumeration t -> t
enum_first (Enum x _) = x

enum_first_h :: Enumeration (h,t) -> t
enum_first_h (Enum (_,x) _) = x

enum_enum :: Enumeration t -> Enumerator t
enum_enum (Enum _ x) = x

enum_up_to :: Int -> Enumeration t -> [t]
enum_up_to n (Enum t0 e) = enum_up_to_rec n e 0 t0

-- First parameter is how many left, second parameter is how many we did so far.
enum_up_to_rec :: Int -> Enumerator t -> Int -> t -> [t]
enum_up_to_rec 0 _ _ t0 = [t0]
--enum_up_to_rec n f i t0 = case ft0 of {Nothing -> [t0]; Just x -> t0:(enum_up_to_rec (n-1) f (i+1) x)} where ft0 = f i t0
enum_up_to_rec n f i t0 = t0:(case ft0 of {Nothing -> []; Just x -> enum_up_to_rec (n-1) f (i+1) x}) where ft0 = f i t0

apply_on_first :: (a -> b) -> (a,c) -> (b,c)
apply_on_first f (x,z) = (f x,z)

apply_on_first_3 :: (a -> b) -> (a,c,d) -> (b,c,d)
apply_on_first_3 f (x,y,z) = (f x,y,z)

maybe_apply :: (a -> b) -> Maybe a -> Maybe b
maybe_apply _ Nothing = Nothing
maybe_apply f (Just x) = Just (f x)

maybe_apply_2 :: (a -> b -> c) -> Maybe a -> Maybe b -> Maybe c
maybe_apply_2 _ Nothing _ = Nothing
maybe_apply_2 _ _ Nothing = Nothing
maybe_apply_2 f (Just x) (Just y) = Just (f x y)

maybe_apply_co2 :: (a -> (b,c)) -> Maybe a -> (Maybe b,Maybe c)
maybe_apply_co2 _ Nothing = (Nothing,Nothing)
maybe_apply_co2 f (Just x) = (Just y,Just z) where (y,z) = f x

demaybize :: Maybe (Maybe a) -> Maybe a
demaybize Nothing = Nothing
demaybize (Just x) = x

pair_x_mb :: a -> Maybe b -> Maybe (a,b)
pair_x_mb _ Nothing = Nothing
pair_x_mb x (Just y) = Just (x,y)

pair_mb_mb :: Maybe a -> Maybe b -> Maybe (a,b)
pair_mb_mb Nothing _ = Nothing
pair_mb_mb _ Nothing = Nothing
pair_mb_mb (Just x) (Just y) = Just (x,y)

apply_enum_1 :: (a -> b) -> Enumeration a -> Enumeration (a,b)
apply_enum_1 f (Enum a0 ea) = Enum (a0,f a0) (\idx -> \prev -> case prev of {(preva,_) -> apply_enum_1_helper f ea idx preva})

apply_enum_1_helper :: (a -> b) -> Enumerator a -> Int -> a -> Maybe (a,b)
apply_enum_1_helper f e idx preva = case epreva of {Nothing -> Nothing; Just eprevax -> Just (eprevax, f eprevax)} where epreva = e idx preva

-- fa and fb need to be inverses.
equiv_enum :: (a -> b) -> (b -> a) -> Enumeration a -> Enumeration b
equiv_enum fa fb (Enum a0 ea) = Enum (fa a0) (\idx -> \prev -> maybe_apply fa (ea idx (fb prev)))

-- The result has two parts.
-- The first one is to make it efficient. It keeps the list of a's over which we have not finished enumeration, split into two parts, the ones to the "left of the cursor" and the ones to the "right of the cursor".
-- The second one is the actual next value.
-- type Diagonalizer h1 a h2 b = ((((h1,a),[((h1,a),Enumerator (h2,b),Int,(h2,b))],[((h1,a),Enumerator (h2,b),Int,(h2,b))]),(h1,a)),h2)
type NoHelpDiagonalizer a b = ((a,[(a,Enumerator b,Int,b)],[(a,Enumerator b,Int,b)]),(a,b))
diagonalize :: (a -> Enumeration b) -> Enumeration a -> Enumeration (NoHelpDiagonalizer a b)
--diagonalize f (Enum a0 ea) = Enum ((a0,[],[(a0,enum_enum eb0,1,b0)]),(a0,b0)) (\idx -> \prev -> diagonalize_helper default_diag_breadth_control default_diag_depth_control (max_depth_cleanup_control 20000) f ea idx prev) where eb0 = (f a0); b0 = enum_first eb0
diagonalize f (Enum a0 ea) = Enum ((a0,[],[(a0,enum_enum eb0,1,b0)]),(a0,b0)) (\idx -> \prev -> diagonalize_helper default_diag_breadth_control default_diag_depth_control default_diag_cleanup_control f ea idx prev) where eb0 = (f a0); b0 = enum_first eb0

-- When a whole pass has been made, it returns a bool indicating whether the width of the search should be increased (True).
type DiagBreadthControl a b = NoHelpDiagonalizer a b -> Bool
-- After a column is enumerated, it returns a bool indicating whether it should be forgotten (False) for this pass or it should be enumerated again (True).
type DiagDepthControl a b = NoHelpDiagonalizer a b -> Bool
-- After a column is enumerated, it returns a bool indicating if it should be thrown away altogether (True).
type DiagCleanUpControl a b = NoHelpDiagonalizer a b -> Bool

default_diag_breadth_control :: DiagBreadthControl a b
default_diag_breadth_control _ = True

max_breadth_control :: Int -> DiagBreadthControl a b
max_breadth_control max ((_,columns,_),_) = (length columns) <= max

default_diag_depth_control :: DiagDepthControl a b
default_diag_depth_control _ = False

default_diag_cleanup_control :: DiagCleanUpControl a b
default_diag_cleanup_control _ = False

max_depth_cleanup_control :: Int -> DiagCleanUpControl a b
max_depth_cleanup_control max ((_,_,((_,_,idx,_):_)),_) = idx >= max

diagonalize_helper :: DiagBreadthControl a b -> DiagDepthControl a b -> DiagCleanUpControl a b -> (a -> Enumeration b) -> Enumerator a -> Int -> ((a,[(a,Enumerator b,Int,b)],[(a,Enumerator b,Int,b)]),(a,b)) -> Maybe ((a,[(a,Enumerator b,Int,b)],[(a,Enumerator b,Int,b)]),(a,b))
-- If there is a next one out of the open ones, iterate it. If it is nothing, then kill this branch and go again.
diagonalize_helper bcont dcont cucont f ea idx ((na,done,((ca,eb,cidx,cb):ps)),prev) = case nb of {Nothing -> diagonalize_helper bcont dcont cucont f ea idx ((na,done,ps),prev); Just nbb -> if again then (Just ((na,done,((ca,eb,cidx+1,nbb):ps)),(ca,nbb))) else (if cleanup then (Just ((na,done,ps),prev)) else (Just ((na,((ca,eb,cidx+1,nbb):done),ps),(ca,nbb))))} where nb = eb cidx cb; again = dcont ((na,done,((ca,eb,cidx,cb):ps)),prev); cleanup = cucont ((na,done,((ca,eb,cidx,cb):ps)),prev)
-- This was buggy, when there was only one running enumerator left, and it finished, we finished, but there could be more enumerators to diagonalize over.
-- To solve it, we now check, when there are no next ones, whether there are no done ones NOR the enumerator for a returns a new one. That truly indicates when we have finished.
-- If there is neither next nor done ones, then we are finished.
--diagonalize_helper _ _ _ ((_,[],[]),_) = Nothing
-- If there is no next one, but there are done ones, then enumerate a once, add the enumerator (if there is one) and start over.
-- Note: We reverse all the lists simply to enumerate on the same order each time, for clarity, it is not really necessary.
--diagonalize_helper f ea idx ((na,done,[]),prev) = case nna of {Nothing -> case done of {[] -> Nothing; (_:_) -> diagonalize_helper f ea idx ((na,[],done),prev)}; Just nnna -> Just ((nnna,[(nnna,enum_enum (f nnna),1,enum_first (f nnna))],reverse done),(nnna,enum_first (f nnna)))} where nna = ea idx na
diagonalize_helper bcont dcont cucont f ea idx ((na,done,[]),prev) = if increase then (case nna of {Nothing -> case done of {[] -> Nothing; (_:_) -> diagonalize_helper bcont dcont cucont f ea idx ((na,[],done),prev)}; Just nnna -> Just ((nnna,[(nnna,enum_enum (f nnna),1,enum_first (f nnna))],done),(nnna,enum_first (f nnna)))}) else (diagonalize_helper bcont dcont cucont f ea idx ((na,[],done),prev)) where nna = ea idx na; increase = bcont ((na,done,[]),prev)

enum_from_list :: [t] -> Enumeration ([t],t)
-- Not valid when the list is empty.
enum_from_list (x:xs) = (Enum (xs,x) (\idx -> \prev -> case (fst prev) of {[] -> Nothing; (x:xs) -> Just (xs,x)}))

enum_from_list_maybe :: [t] -> Enumeration ([t],Maybe t)
enum_from_list_maybe [] = Enum ([],Nothing) (\idx -> \prev -> Nothing)
enum_from_list_maybe (x:xs) = enum_maybe_h (enum_from_list (x:xs))

enum_maybe_h :: Enumeration (h1,t) -> Enumeration (h1,Maybe t)
enum_maybe_h (Enum (h0,x0) f) = Enum (h0,Just x0) (\idx -> \prev -> case prev of (_,Nothing) -> Nothing; (h,Just x) -> case (f idx (h,x)) of {Nothing -> Nothing; Just (h2,y) -> Just (h2,Just y)})

enum_nothing_h :: Enumeration ((),Maybe t)
enum_nothing_h = Enum ((),Nothing) (\idx -> \prev -> Nothing)

no_help :: Enumeration t -> Enumeration (Bool,t)
no_help (Enum t0 e) = Enum (False,t0) (\idx -> \prev -> case prev of {(_,t) -> case (e idx t) of {Nothing -> Nothing; Just x -> Just (False,x)}})

combine_help :: Enumeration (h1,(h2,t)) -> Enumeration ((h1,h2),t)
combine_help (Enum (h10,(h20,t0)) e) = Enum ((h10,h20),t0) (\idx -> \prev -> case prev of {((h1prev,h2prev),tprev) -> case (e idx (h1prev,(h2prev,tprev))) of {Nothing -> Nothing; Just (h1r,(h2r,tr)) -> Just ((h1r,h2r),tr)}})

combine_help_diagonalize :: Enumeration (h1,((h2,a),b)) -> Enumeration ((h1,h2),(a,b))
combine_help_diagonalize (Enum (h10,((h20,a0),b0)) e) = Enum ((h10,h20),(a0,b0)) (\idx -> \prev -> case prev of {((h1prev,h2prev),(aprev,bprev)) -> case (e idx (h1prev,((h2prev,aprev),bprev))) of {Nothing -> Nothing; Just (h1r,((h2r,ar),br)) -> Just ((h1r,h2r),(ar,br))}})

--concat_enums_h :: Enumeration (h1,t) -> Enumeration (h2,t) -> Enumeration (((Bool,Maybe (Either h1 h2,t)),Either h1 h2),t)
--concat_enums_h (Enum (h10,e10) fe1) (Enum (h20,e20) fe2) = Enum (((False,Just (Right h20,e20)),Left h10),e10) (\idx -> \x -> case x of {
--	(((False,Just (Right h2,n2)),Left h1),c) -> Just (((True,case (fe1 ((quot idx 2) + 1) (h1,c)) of {Nothing -> Nothing; Just (h1r,n1r) -> Just (Left h1r,n1r)}),Right h2),n2);
--	(((True,Just (Left h1,n1)),Right h2),c) -> Just (((False,case (fe2 (quot idx 2) (h2,c)) of {Nothing -> Nothing; Just (h2r,n2r) -> Just (Right h2r,n2r)}),Left h1),n1);
--	(((_,Nothing),_),_) -> Nothing})
concat_enums_h :: Enumeration (h1,t) -> Enumeration (h2,t) -> Enumeration (_,t)
concat_enums_h e1 e2 = diagonalize_h (concat_enums_h_choice e1 e2) (no_help (Enum True (\idx -> \x -> case x of {True -> Just False; False -> Nothing})))

concat_enums_h_choice :: Enumeration (h1,t) -> Enumeration (h2,t) -> Bool -> Enumeration (Either h1 h2,t)
concat_enums_h_choice e1 e2 True = equiv_enum (\x -> case x of {(h,y) -> (Left h,y)}) (\x -> case x of {(Left h,y) -> (h,y)}) e1
concat_enums_h_choice e1 e2 False = equiv_enum (\x -> case x of {(h,y) -> (Right h,y)}) (\x -> case x of {(Right h,y) -> (h,y)}) e2

enum_up_to_h :: Int -> Enumeration (h,t) -> [t]
enum_up_to_h x en = map snd (enum_up_to x en)

enum_up_to_mb_h :: Int -> Enumeration (h,Maybe t) -> [t]
enum_up_to_mb_h x en = case (enum_up_to_h x en) of {[Nothing] -> []; l -> map (\e -> case e of {Just y -> y}) l}

apply_enum_1_h :: (a -> b) -> Enumeration (h1,a) -> Enumeration ((h1,a),b)
apply_enum_1_h f en = apply_enum_1 (\pair -> f (snd pair)) en

single_list_enum_h :: Enumeration (h1,a) -> Enumeration ((h1,a),[a])
single_list_enum_h en = apply_enum_1_h (\x -> [x]) en

equiv_enum_h :: (a -> b) -> (b -> a) -> Enumeration (h,a) -> Enumeration (h,b)
equiv_enum_h fa fb (Enum (h0,a0) eah) = Enum (h0,fa a0) (\idx -> \prev -> case prev of {(h,b) -> case (eah idx (h,fb b)) of {Nothing -> Nothing; Just (hr,ar) -> Just (hr,fa ar)}})

enum_left_h :: Enumeration (h,a) -> Enumeration (h,Either a b)
enum_left_h e = equiv_enum_h (\x -> Left x) (\y -> case y of {Left x -> x}) e

enum_unleft_h :: Enumeration (h,Either a b) -> Enumeration (h,a)
enum_unleft_h e = equiv_enum_h (\x -> case x of {Left x -> x}) (\y -> Left y) e

enum_right_h :: Enumeration (h,a) -> Enumeration (h,Either b a)
enum_right_h e = equiv_enum_h (\x -> Right x) (\y -> case y of {Right x -> x}) e

enum_unright_h :: Enumeration (h,Either b a) -> Enumeration (h,a)
enum_unright_h e = equiv_enum_h (\x -> case x of {Right x -> x}) (\y -> Right y) e

-- When what could be different is the help
enum_hleft_h :: Enumeration (h,a) -> Enumeration (Either h g,a)
enum_hleft_h e = equiv_enum (\x -> case x of {(hx,ax) -> (Left hx,ax)}) (\y -> case y of {(Left hy,ay) -> (hy,ay)}) e

enum_hright_h :: Enumeration (h,a) -> Enumeration (Either g h,a)
enum_hright_h e = equiv_enum (\x -> case x of {(hx,ax) -> (Right hx,ax)}) (\y -> case y of {(Right hy,ay) -> (hy,ay)}) e

enum_filter_h :: (a -> Bool) -> Enumeration (h,a) -> Enumeration ((Int,h),a)
enum_filter_h f (Enum (h0,a0) eah) = Enum ((1,h0),a0) (enum_filter_h_rec f eah)

enum_filter_h_rec :: (a -> Bool) -> (Int -> (h,a) -> Maybe (h,a)) -> Int -> ((Int,h),a) -> Maybe ((Int,h),a)
enum_filter_h_rec f e idx ((iidx,h),a) = case eha of {Nothing -> Nothing; Just (eh,ea) -> if (f ea) then Just ((iidx+1,eh),ea) else (enum_filter_h_rec f e idx ((iidx+1,eh),ea))} where eha = e iidx (h,a)

enum_maybe_filter_h :: (a -> Bool) -> Enumeration (h,Maybe a) -> Enumeration ((Int,h),Maybe a)
enum_maybe_filter_h f (Enum (h0,Nothing) eah) = Enum a0_other (enum_maybe_filter_h_rec f eah) where a0_other = case (enum_maybe_filter_h_rec f eah 0 ((1,h0),Nothing)) of {Nothing -> ((1,h0),Nothing);Just x -> x}
enum_maybe_filter_h f (Enum (h0,Just a0) eah) = if (f a0) then Enum ((1,h0),Just a0) (enum_maybe_filter_h_rec f eah) else Enum a0_other (enum_maybe_filter_h_rec f eah) where a0_other = case (enum_maybe_filter_h_rec f eah 0 ((1,h0),Just a0)) of {Nothing -> ((1,h0),Nothing); Just x -> x}

-- In some sense, we are assuming here that the information necessary for enumeration is on the help. Otherwise, how would we distinguish different maybes?
enum_maybe_filter_h_rec :: (a -> Bool) -> (Int -> (h,Maybe a) -> Maybe (h,Maybe a)) -> Int -> ((Int,h),Maybe a) -> Maybe ((Int,h),Maybe a)
enum_maybe_filter_h_rec f e idx ((iidx,h),mba) = case eha of {Nothing -> Nothing; Just (eh,Nothing) -> enum_maybe_filter_h_rec f e idx ((iidx+1,eh),Nothing); Just (eh,Just ea) -> if (f ea) then Just ((iidx+1,eh),Just ea) else (enum_maybe_filter_h_rec f e idx ((iidx+1,eh),Just ea))} where eha = e iidx (h,mba)

enum_hleft_left_h :: Enumeration (h,a) -> Enumeration (Either h g,Either a b)
enum_hleft_left_h e = enum_hleft_h (enum_left_h e)

enum_hright_right_h :: Enumeration (h,a) -> Enumeration (Either g h,Either b a)
enum_hright_right_h e = enum_hright_h (enum_right_h e)

enum_hnil_h :: Enumeration a -> Enumeration ([h],a)
enum_hnil_h e = equiv_enum (\x -> ([],x)) (\y -> case y of {([],x) -> x}) e

enum_hcons_h :: Enumeration ((h,[h]),a) -> Enumeration ([h],a)
enum_hcons_h e = equiv_enum (\x -> case x of {((h,hs),a) -> (h:hs,a)}) (\y -> case y of {(h:hs,a) -> ((h,hs),a)}) e

type Diagonalizer h1 a h2 b = ((((h1,a),[((h1,a),Enumerator (h2,b),Int,(h2,b))],[((h1,a),Enumerator (h2,b),Int,(h2,b))]),(h1,a)),h2)

diagonalize_h :: (a -> Enumeration (h2,b)) -> Enumeration (h1,a) -> Enumeration (Diagonalizer h1 a h2 b,b)
diagonalize_h f en = combine_help (combine_help (diagonalize (\pair -> f (snd pair)) en))

diagonalize_h_uncombined :: (a -> Enumeration (h2,b)) -> Enumeration (h1,a) -> Enumeration ((((h1,a),[((h1,a),Enumerator (h2,b),Int,(h2,b))],[((h1,a),Enumerator (h2,b),Int,(h2,b))]),(h1,a)),(h2,b))
diagonalize_h_uncombined f en = combine_help (diagonalize (\pair -> f (snd pair)) en)

diagonalize_over_list_h :: [Enumeration (h1,a)] -> Enumeration (RecursiveDiagonalization (h1,a) [a],[a])
diagonalize_over_list_h es = recursively_diagonalize_h (\x -> case x of {[y] -> Left (\z -> single_list_enum_h y); (y:ys) -> Right (ys,((\w -> single_list_enum_h y),Comb (\z -> \zs -> z++zs) (\zss -> case zss of {(z:zs) -> ([z],zs)})))}) es

data RecursiveDiagonalization h1 a = BaseDiag h1 a | RecDiag ((h1,a),[((h1,a),Enumerator ((RecursiveDiagonalization h1 a),a),Int,(RecursiveDiagonalization h1 a,a))],[((h1,a),Enumerator ((RecursiveDiagonalization h1 a),a),Int,(RecursiveDiagonalization h1 a,a))]) (h1,a) (RecursiveDiagonalization h1 a)

combine_recdiag :: Enumeration (RecursiveDiagonalization h1 a) -> Enumeration (RecursiveDiagonalization h1 a,a)
combine_recdiag e = equiv_enum combine_recdiag_helper fst e

combine_recdiag_helper :: RecursiveDiagonalization h1 a -> (RecursiveDiagonalization h1 a,a)
combine_recdiag_helper (BaseDiag h x) = (BaseDiag h x,x)
combine_recdiag_helper (RecDiag stuff npa na) = (RecDiag stuff npa na,snd (combine_recdiag_helper na))

base_diag :: Enumeration (h1,r) -> Enumeration (RecursiveDiagonalization h1 r)
base_diag e = equiv_enum (\x -> case x of {(h,x) -> BaseDiag h x}) (\y -> case y of {BaseDiag h x -> (h,x)}) e

-- t is the input type, r is the result type, and p the partial type.
-- A base case computation returns a result.
-- An intermediate step returns a partial result and leaves part of the input.
data RecursiveResult t r p = Base r | Rec t p

data SingleRecursionScheme t r p = RecSch (t -> Either r (t,p)) (p -> r -> r)

-- First function says, given two parts, how to build a total. The other one is the inverse of this one. 
-- For lists, for example, this assumes that lists are built from the head, one element at a time, or something like that, so that we know where to split.
data CombinationScheme r = Comb (r -> r -> r) (r -> (r,r))

-- Given a combination scheme and a "head", gives us an equivalence between the "rests" and the "totals". This is just partial evaluation!
equiv_from_comb_1 :: CombinationScheme r -> r -> r -> r
equiv_from_comb_1 (Comb f _) = f

-- In the opposite direction
-- Ignore the head, that we assume is the same, and take the second element.
equiv_from_comb_2 :: CombinationScheme r -> r -> r -> r
equiv_from_comb_2 (Comb _ g) _ = snd . g

--equiv_from_multicomb_1 :: MultiCombinationScheme r -> r -> [r] -> r
--equiv_from_multicomb_1 (MComb f _) = f

--equiv_from_multicomb_2 :: MultiCombinationScheme r -> r -> r -> [r]
--equiv_from_multicomb_2 (MComb _ g) _ = snd . g

apply_step_result :: (t -> Either r (t,p)) -> (t -> RecursiveResult t r p)
apply_step_result f x = case (f x) of {Left res -> Base res; Right (rem,parc) -> Rec rem parc}

apply_recursion_scheme :: SingleRecursionScheme t r p -> (t -> r)
apply_recursion_scheme (RecSch f c) x = case (apply_step_result f x) of {Base r -> r; Rec rem parc -> c parc (apply_recursion_scheme (RecSch f c) rem)}

-- No partial results allowed.
-- t here is the type to recurse over. For example, a list.
-- The partial information generated in the recursive call is a function that, given a function that calculates an enumeration (which will be the recursive call),
-- an enumerated element as a partial result, and the enumerator for the partial result, diagonalizes.
-- This is internal however, and so the only thing we keep as partial information is the enumerator for the partial result.
-- t = t
-- r = [r] -> Enumeration (RecursiveDiagonalization h1 r,r) where the r enumerated should include ALL the information to enumerate (a combination), and the argument is the previously enumerated ones, so that they may affect the enumeration itself.
-- p = ([r] -> Enumeration (h1,r),CombinationScheme r) where the first parameter is the enumerator for the current diagonalization, and the second parameter is the combination of the enumeration at the current level with the enumeration at the next level, to give the total result. In most cases this combination will be constant, but it may depend on t.
-- Note that the parameter [r] are evaluated in the inverse order: The first is the inner-most enumerated one, to follow the inductive structure of conses on the front.
diagonalization_rec_scheme_h :: (t -> Either ([r] -> Enumeration (h1,r)) (t,([r] -> Enumeration (h1,r),CombinationScheme r))) -> SingleRecursionScheme t ([r] -> Enumeration (RecursiveDiagonalization h1 r,r)) ([r] -> Enumeration (h1,r),CombinationScheme r)
diagonalization_rec_scheme_h f = RecSch (diagonalization_rec_scheme_h_step f) diagonalization_rec_scheme_h_combine

diagonalization_rec_scheme_h_step :: (t -> Either ([r] -> Enumeration (h1,r)) (t,([r] -> Enumeration (h1,r),CombinationScheme r))) -> (t -> Either ([r] -> Enumeration (RecursiveDiagonalization h1 r,r)) (t,([r] -> Enumeration (h1,r),CombinationScheme r)))
diagonalization_rec_scheme_h_step f x = case (f x) of {Left e -> Left (\y -> (combine_recdiag (base_diag (e y)))); Right (rx,comb) -> Right (rx,comb)}

diagonalization_rec_scheme_h_combine :: ([r] -> Enumeration (h1,r),CombinationScheme r) -> ([r] -> Enumeration (RecursiveDiagonalization h1 r,r)) -> ([r] -> Enumeration (RecursiveDiagonalization h1 r,r))
diagonalization_rec_scheme_h_combine (pe,pcomb) r = (\xs -> equiv_enum diagonalization_rec_scheme_equiv_1 diagonalization_rec_scheme_equiv_2 (diagonalize_h_uncombined (\x -> equiv_enum_h (equiv_from_comb_1 pcomb x) (equiv_from_comb_2 pcomb x) (r (x:xs))) (pe xs)))

diagonalization_rec_scheme_equiv_1 :: ((_,(h1,r)),(RecursiveDiagonalization h1 r,r)) -> (RecursiveDiagonalization h1 r,r)
diagonalization_rec_scheme_equiv_1 ((stuff,(h,x)),(rec,y)) = (RecDiag stuff (h,x) rec,y)

diagonalization_rec_scheme_equiv_2 :: (RecursiveDiagonalization h1 r,r) -> ((_,(h1,r)),(RecursiveDiagonalization h1 r,r))
diagonalization_rec_scheme_equiv_2 (RecDiag stuff (h,x) rec,y) = ((stuff,(h,x)),(rec,y))


-- We leave the multiple recursive diagonalization things unfinished for now, and use alternatives.

--data MultiCombinationScheme r = MComb (r -> [r] -> r) (r -> (r,[r]))

--data DoublyRecursiveDiagonalization h1 r = BaseDoubRec h1 | RecDoubRec (RecursiveDiagonalization (DoublyRecursiveDiagonalization h1 r, r) [r])
--data DoublyRecursiveDiagonalization h1 r = BaseDoubRec (RecursiveDiagonalization h1 [r]) | RecDoubRec (RecursiveDiagonalization (DoublyRecursiveDiagonalization h1 r, r) [r])

--diagonalization_multirec_scheme_h_step :: (t -> Either ([r] -> Enumeration (h1,r)) ([t],([r] -> Enumeration (h1,r),MultiCombinationScheme r))) -> (t -> Either ([r] -> Enumeration ((RecursiveDiagonalization h1 r,r), [r])) ([t],([r] -> Enumeration (h1,r),MultiCombinationScheme r)))
--diagonalization_multirec_scheme_h_step f x = case (f x) of {Left e -> Left (\y -> (single_list_enum_h (combine_recdiag (base_diag (e y))))); Right (rxs,comb) -> Right (rxs,comb)}

--diagonalization_multirec_scheme_h_combine :: ([r] -> Enumeration (h1,r),MultiCombinationScheme r) -> [([r] -> Enumeration (RecursiveDiagonalization h1 r, [r]))] -> ([r] -> Enumeration (RecursiveDiagonalization h1 r, [r]))
--diagonalization_multirec_scheme_h_combine (pe,pcomb) rs = (\xs -> equiv_enum diagonalization_rec_scheme_equiv_1 diagonalization_rec_scheme_equiv_2 (diagonalize_h_uncombined (\x -> equiv_enum_h (equiv_from_multicomb_1 pcomb x) (equiv_from_multicomb_2 pcomb x) (diagonalize_over_list_h (map (\r -> r (x:xs)) rs))) (pe xs)))

--diagonalization_multirec_scheme_h_combine :: ([r] -> Enumeration (h1,r),MultiCombinationScheme r) -> [([r] -> Enumeration (DoublyRecursiveDiagonalization h1 r, [r]))] -> ([r] -> Enumeration (DoublyRecursiveDiagonalization h1 r, [r]))
--diagonalization_multirec_scheme_h_combine (pe,pcomb) rs = (\xs -> equiv_enum (equiv_doubly_rec_diag_3 . diagonalization_rec_scheme_equiv_1) (diagonalization_rec_scheme_equiv_2 . equiv_doubly_rec_diag_4) (diagonalize_h_uncombined (\x -> equiv_enum_h (equiv_from_multicomb_1 pcomb x) (equiv_from_multicomb_2 pcomb x) (equiv_enum equiv_doubly_rec_diag_1 equiv_doubly_rec_diag_2 (diagonalize_over_list_h (map (\r -> r (x:xs)) rs)))) (pe xs)))

--equiv_doubly_rec_diag_1 :: (RecursiveDiagonalization (DoublyRecursiveDiagonalization h1 r, r) [r], [r]) -> (DoublyRecursiveDiagonalization h1 r, [r])
--equiv_doubly_rec_diag_1 (rec,r) = (RecDoubRec rec,r)

--equiv_doubly_rec_diag_2 :: (DoublyRecursiveDiagonalization h1 r, [r]) -> (RecursiveDiagonalization (DoublyRecursiveDiagonalization h1 r, r) [r], [r])
--equiv_doubly_rec_diag_2 ((RecDoubRec rec),r) = (rec,r)

--equiv_doubly_rec_diag_3 :: (RecursiveDiagonalization h1 [r], [r]) -> (DoublyRecursiveDiagonalization h1 r, [r])
--equiv_doubly_rec_diag_3 (rec,r) = (BaseDoubRec rec,r)

--equiv_doubly_rec_diag_4 :: (DoublyRecursiveDiagonalization h1 r, [r]) -> (RecursiveDiagonalization h1 [r], [r])
--equiv_doubly_rec_diag_4 ((BaseDoubRec rec,r)) = (rec,r)

--data RecursiveDiagonalization h1 a = BaseDiag h1 a | RecDiag ((h1,a),[((h1,a),Enumerator ((RecursiveDiagonalization h1 a),a),Int,(RecursiveDiagonalization h1 a,a))],[((h1,a),Enumerator ((RecursiveDiagonalization h1 a),a),Int,(RecursiveDiagonalization h1 a,a))]) (h1,a) (RecursiveDiagonalization h1 a)


recursively_diagonalize_h :: (t -> Either ([r] -> Enumeration (h1,r)) (t,([r] -> Enumeration (h1,r),CombinationScheme r))) -> (t -> Enumeration (RecursiveDiagonalization h1 r,r))
recursively_diagonalize_h step x = apply_recursion_scheme (diagonalization_rec_scheme_h step) x []

enumerate_lists_step :: Enumeration (h1,t) -> Int -> Either ([[t]] -> Enumeration ((h1,t),[t])) (Int,([[t]] -> Enumeration ((h1,t),[t]),CombinationScheme [t]))
-- Previous elements don't change how we enumerate in this case.
enumerate_lists_step e 1 = Left (\x -> (single_list_enum_h e))
enumerate_lists_step e i = Right (i-1,((\x -> single_list_enum_h e),enumerate_lists_comb))

enumerate_lists_comb :: CombinationScheme [t]
enumerate_lists_comb = Comb (\ts1 -> \ts2 -> ts1++ts2) (\ts -> case ts of (t:ts) -> ([t],ts))

enumerate_lists :: Enumeration (h1,t) -> Int -> Enumeration (_,[t])
enumerate_lists e 0 = enum_hleft_h (Enum ((),[]) (\idx -> \x -> Nothing))
enumerate_lists e n = enum_hright_h (recursively_diagonalize_h (enumerate_lists_step e) n)

--data SingleRecursionScheme t r p = RecSch (t -> Either r (t,p)) (p -> r -> r)
data MultipleRecursionScheme t r p = MRecSch (t -> Either r ([t],p)) (p -> [r] -> r)

data ParallelRecursion t = SingleRec t | MultiRec [ParallelRecursion t] deriving Show

-- We start with just one t, and so must get just one result.
apply_multiple_recursion_scheme :: MultipleRecursionScheme t r p -> (t -> r)
apply_multiple_recursion_scheme sch x = case res of {SingleRec r -> r} where res = apply_recursion_scheme (convert_multiple_rec_scheme sch) (SingleRec (Right x))

convert_multiple_rec_scheme :: MultipleRecursionScheme t r p -> SingleRecursionScheme (ParallelRecursion (Either r t)) (ParallelRecursion r) (ParallelRecursion (Maybe p))
convert_multiple_rec_scheme (MRecSch step comb) = RecSch (convert_multiple_rec_scheme_step step) (convert_multiple_rec_scheme_comb comb)

convert_multiple_rec_scheme_comb :: (p -> [r] -> r) -> (ParallelRecursion (Maybe p) -> ParallelRecursion r -> ParallelRecursion r)
convert_multiple_rec_scheme_comb f (SingleRec Nothing) r = r
-- If we have a single p, then that means we can produce a single r by combining the multiple rs. The second parameter NEEDS to be multiple singles, because it came from a single recursion that split.
convert_multiple_rec_scheme_comb f (SingleRec (Just p)) (MultiRec rs) = SingleRec (f p (map (\wr -> case wr of {SingleRec r -> r}) rs))
convert_multiple_rec_scheme_comb f (MultiRec ps) (MultiRec rs) = MultiRec (map (\pair -> convert_multiple_rec_scheme_comb f (fst pair) (snd pair)) (zip ps rs))

convert_multiple_rec_scheme_step :: (t -> Either r ([t],p)) -> (ParallelRecursion (Either r t) -> Either (ParallelRecursion r) (ParallelRecursion (Either r t),ParallelRecursion (Maybe p)))
convert_multiple_rec_scheme_step f (SingleRec (Left r)) = Left (SingleRec r)
convert_multiple_rec_scheme_step f (SingleRec (Right t)) = case (f t) of {Left r -> Left (SingleRec r); Right (rs,p) -> Right (MultiRec (map (\y -> SingleRec (Right y)) rs),SingleRec (Just p))}
convert_multiple_rec_scheme_step f (MultiRec ts) = case parc of {Left rs -> Left (MultiRec rs); Right rts -> Right (convert_multiple_rec_scheme_step_helper_4 (convert_multiple_rec_scheme_step_helper_3 rts))} where parc = convert_multiple_rec_scheme_step_helper_2 (map (convert_multiple_rec_scheme_step f) ts)

convert_multiple_rec_scheme_step_helper :: Either (ParallelRecursion r) (ParallelRecursion (Either r t),ParallelRecursion (Maybe p)) -> (ParallelRecursion (Either r t),ParallelRecursion (Maybe p))
convert_multiple_rec_scheme_step_helper (Left (SingleRec r)) = (SingleRec (Left r),SingleRec Nothing)
-- We compose with fst because, due to being called on all Lefts, we know that it will return all Nothings on the p's.
convert_multiple_rec_scheme_step_helper (Left (MultiRec rs)) = (MultiRec (map (fst . convert_multiple_rec_scheme_step_helper) (map Left rs)),SingleRec Nothing)
convert_multiple_rec_scheme_step_helper (Right x) = x

convert_multiple_rec_scheme_step_helper_2 :: [Either (ParallelRecursion r) (ParallelRecursion (Either r t),ParallelRecursion (Maybe p))] -> Either [ParallelRecursion r] [(ParallelRecursion (Either r t),ParallelRecursion (Maybe p))]
convert_multiple_rec_scheme_step_helper_2 [] = Left []
convert_multiple_rec_scheme_step_helper_2 ((Left r):xs) = case (convert_multiple_rec_scheme_step_helper_2 xs) of {Left rs -> Left (r:rs); Right rts -> Right ((convert_multiple_rec_scheme_step_helper (Left r)):rts)}
convert_multiple_rec_scheme_step_helper_2 ((Right (rt,p)):xs) = Right ((rt,p):(map convert_multiple_rec_scheme_step_helper xs))

convert_multiple_rec_scheme_step_helper_3 :: [(ParallelRecursion (Either r t),ParallelRecursion (Maybe p))] -> ([ParallelRecursion (Either r t)],[ParallelRecursion (Maybe p)])
convert_multiple_rec_scheme_step_helper_3 [] = ([],[])
convert_multiple_rec_scheme_step_helper_3 ((rt,p):xs) = (rt:(fst parc),p:(snd parc)) where parc = convert_multiple_rec_scheme_step_helper_3 xs

convert_multiple_rec_scheme_step_helper_4 :: ([ParallelRecursion (Either r t)],[ParallelRecursion (Maybe p)]) -> (ParallelRecursion (Either r t),ParallelRecursion (Maybe p))
convert_multiple_rec_scheme_step_helper_4 (rts,ps) = (MultiRec rts,MultiRec ps)


-- SUPER UGLY STUFF TO GET RID OF UGLIER STUFF
ugly_simplify_help :: Enumeration (h1,t) -> Enumeration ([t],t)
ugly_simplify_help e = enum_from_list (enum_up_to_h 99999999 e)



enumerate_or_propagate_out :: (MetaunificationHeuristic hl ht) -> ExtendedSignature -> FullSolution -> Enumeration (_,FullSolution)
enumerate_or_propagate_out heur sig fs = case (enumerate_or_propagate heur sig fs) of {Left res -> enum_hleft_h (no_help (single_enum res)); Right res -> enum_hright_h res}

-- This function takes a current solution, assumed factorized and clean, calculates the best root class, and acts in consequence.
-- If the best root class requires no enumeration, then this is simply assigning the canonical variable to that class, and propagating.
-- If the best root class requires enumeration, then this implies producing an enumeration and propagating to get new solutions.
enumerate_or_propagate :: (MetaunificationHeuristic hl ht) -> ExtendedSignature -> FullSolution -> Either FullSolution (Enumeration (_,FullSolution))
enumerate_or_propagate heur sig fs = case action of
										{
											-- Choose any random meta-variable and enumerate
											Nothing -> Right (enum_hleft_h (enumerate_and_propagate_metavar heur sig fs (find_previous_dep_metavar (find_random_metavar_dep (get_graph fs)))));
											-- Just choose canonical variable and propagate. This means that all in that class, including the representative, need to be of the form "u x".
											Just ((DRec u (DVar v)),Nothing) -> Left (propagate_canonical_variable sig fs u v);
											-- Enumerate over the given meta-variable.
											-- Note: Feels like I could do something more intelligent here. I am not using the information of where that meta-variable was, and instead I am recalculating stuff again for each enumeration of the meta-variable. For now, this is good enough.
											Just (rep,Just dep) -> Right (enum_hright_h (enumerate_and_propagate_metavar heur sig fs (find_previous_dep_metavar dep)))
										}
										where ((_,_,n),_,_,_) = sig; action = find_best_root_class n fs

at_most_propagate :: ExtendedSignature -> FullSolution -> FullSolution
at_most_propagate sig fs = case action of
				{					
					Just ((DRec u (DVar v)),Nothing) -> at_most_propagate sig (propagate_canonical_variable sig fs u v);
					_ -> fs
				}
	where
	((_,_,n),_,_,_) = sig; action = find_best_root_class n fs

propagate_canonical_variable :: ExtendedSignature -> FullSolution -> Unifier -> Variable -> FullSolution
propagate_canonical_variable ((ps,ffs,n),part,sks,ls) fs u v = factorize_update_clean ((ps,ffs,n),part,sks,ls) (update_graph_all ((ps,ffs,n),part,sks,ls) (set_solution fs dv) [dv] []) where dv = ((DRec u (DVar v)),Left (TVar (get_image_var n u v)))

-- Find a random meta-variable
-- Here be where heuristics could come in. In any case, this situation is pretty bad, there's not many intelligent things to do, that's why we try to avoid it at all costs.
find_random_metavar_dep :: DependencyGraph -> Dependent
--find_random_metavar_dep g = case (filter has_unifier (filter is_dependent_metavar (map get_dependent (nodes g)))) of {[] -> capture_value g (head (filter has_unifier (filter is_dependent_metavar (map get_dependent (nodes g))))); _ -> head (filter has_unifier (filter is_dependent_metavar (map get_dependent (nodes g))))}
find_random_metavar_dep g = head (filter has_unifier (filter is_dependent_metavar (map get_dependent (nodes g))))

-- Without the outer-most unifier
find_previous_dep_metavar :: Dependent -> Dependent
find_previous_dep_metavar (DRec _ d) = d


-- Enumerate over the indicated dependent, which corresponds to a meta-var.
-- We need to:
--		- Expose the meta-variable
--		- Find out in what VariableSet the exposed meta-variable stands.
--		- Find out which variables are banned due to the topology of the graph.
--		- Enumerate possible instantiations of the meta-variable given that knowledge.
--		- For each of those, generate the corresponding solution (do this through apply_enum_1_h, of course, so that this generates a solution enumeration).
enumerate_and_propagate_metavar :: (MetaunificationHeuristic hl ht) -> ExtendedSignature -> FullSolution -> Dependent -> Enumeration (_,FullSolution)
enumerate_and_propagate_metavar heur sig fs dep | (is_dependent_term dep) = apply_enum_1_h (\fs2 -> apply_metavar_link_sig sig mv (apply_inst_fs fs2 mv) fs2) parc_fs where vs = find_variable_set dep; bans = find_banned_vars_in_instantiation (get_graph fs) dep; terms = enumerate_terms_dependent_heur heur sig vs bans (find_dep_var_constraints sig dep); parc_fs = propagate_over_metavariable_enum sig fs dep (enum_hleft_left_h terms); mv = extract_metavar_dependent dep
enumerate_and_propagate_metavar heur sig fs dep = apply_enum_1_h (\fs2 -> apply_metavar_link_sig sig mv (apply_inst_fs fs2 mv) fs2) parc_fs where vs = find_variable_set dep; bans = find_banned_vars_in_instantiation (get_graph fs) dep; lits = enumerate_lits_dependent_heur heur sig vs bans (find_dep_var_constraints sig dep); parc_fs = propagate_over_metavariable_enum sig fs dep (enum_hright_right_h lits); mv = extract_metavar_dependent dep

apply_metavar_link_sig :: ExtendedSignature -> Metavariable -> Either Term Literal -> FullSolution -> FullSolution
apply_metavar_link_sig (sig,part,sks,ifilt) mv v fs = apply_metavar_link (sig,part,sks,ifilt) ifilt mv v fs

apply_metavar_link :: ExtendedSignature -> [MetavariableLink] -> Metavariable -> Either Term Literal -> FullSolution -> FullSolution
apply_metavar_link _ [] mv v fs = fs
apply_metavar_link sig ((mv1,rs):mvls) mv2 v fs | mv1 == mv2 = do_apply_metavar_link sig (map (apply_metavar_link_apply v) rs) fs
apply_metavar_link sig ((mv1,rs):mvls) mv2 v fs = apply_metavar_link sig mvls mv2 v fs

apply_metavar_link_inst :: [MetavariableLink] -> Metavariable -> Either Term Literal -> Instantiation -> Instantiation
apply_metavar_link_inst [] mv v inst = inst
apply_metavar_link_inst ((mv1,rs):mvls) mv2 v inst | mv1 == mv2 = do_apply_metavar_link_inst (map (apply_metavar_link_apply v) rs) inst
apply_metavar_link_inst ((mv1,rs):mvls) mv2 v inst = apply_metavar_link_inst mvls mv2 v inst

do_apply_metavar_link_inst :: [(Metavariable,Either Term Literal)] -> Instantiation -> Instantiation
do_apply_metavar_link_inst rs inst = foldr do_apply_metavar_link_inst_single inst rs

do_apply_metavar_link_inst_single :: (Metavariable,Either Term Literal) -> Instantiation -> Instantiation
--do_apply_metavar_link_inst_single (mv,v) inst = compose_inst (build_inst mv v) inst
do_apply_metavar_link_inst_single (mv,(Left t)) (li,ti) = (li,(mv,t):ti)
do_apply_metavar_link_inst_single (mv,(Right l)) (li,ti) = ((mv,l):li,ti)

apply_metavar_link_apply :: Either Term Literal -> (Metavariable,Either Term Literal -> Either Term Literal) -> (Metavariable,Either Term Literal)
apply_metavar_link_apply v (mv,f) = (mv,f v)

do_apply_metavar_link :: ExtendedSignature -> [(Metavariable,Either Term Literal)] -> FullSolution -> FullSolution
do_apply_metavar_link sig rs fs = foldr (do_apply_metavar_link_single sig) fs rs

do_apply_metavar_link_single :: ExtendedSignature -> (Metavariable,Either Term Literal) -> FullSolution -> FullSolution
do_apply_metavar_link_single sig (mv,Left t) fs = propagate_over_metavariable_single sig fs (DMetaT mv) (Left t)
do_apply_metavar_link_single sig (mv,Right l) fs = propagate_over_metavariable_single sig fs (DMetaL mv) (Right l)

-- This function restores consistency between meta-variable links. Meaning, all meta-variables have their instantiations be according to their links, and more specific than they originally had. If it is not possible to restore consistency, it returns Nothing.
-- It is essentially a unification at the meta-level.
-- The process is fairly simple, but worth explaining:
--	- It goes meta-variable by meta-variable, taking its current instantiation and considering any outgoing links, calculating the corresponding values for linked meta-variables.
--	- It stores a "most specific" value for each meta-variable. When the new calculated value for a meta-variable is not equal to its most specific value, it finds a least instantiated common instantiation. If there is one, it keeps it as its value. If there is not, then consistency is not possible, and so we just return Nothing.
restore_consistency_metavar_links :: ExtendedSignature -> [MetavariableLink] -> FullSolution -> Maybe FullSolution
restore_consistency_metavar_links sig links fsol = restore_consistency_metavar_links_helper sig links (Just fsol)

restore_consistency_metavar_links_helper :: ExtendedSignature -> [MetavariableLink] -> Maybe FullSolution -> Maybe FullSolution
restore_consistency_metavar_links_helper sig _ Nothing = Nothing
restore_consistency_metavar_links_helper sig [] (Just fsol) = Just fsol
restore_consistency_metavar_links_helper sig ((smv,ls):rs) (Just fsol) = restore_consistency_metavar_links_helper sig rs (restore_consistency_metavar_links_rec sig smv ls (Just fsol))

restore_consistency_metavar_links_rec :: ExtendedSignature -> Metavariable -> [(Metavariable,Either Term Literal -> Either Term Literal)] -> Maybe FullSolution -> Maybe FullSolution
restore_consistency_metavar_links_rec _ _ _ Nothing = Nothing
restore_consistency_metavar_links_rec _ _ [] (Just fsol) = Just fsol
restore_consistency_metavar_links_rec sig smv ((tmv,f):rs) (Just fsol) = restore_consistency_metavar_links_rec sig smv rs (most_instantiated_fsol sig tmv smv f (Just fsol))

restore_consistency_metavar_links_insts :: [MetavariableLink] -> Maybe Instantiation -> Maybe Instantiation
restore_consistency_metavar_links_insts _ Nothing = Nothing
restore_consistency_metavar_links_insts [] (Just inst) = Just inst
restore_consistency_metavar_links_insts ((smv,ls):rs) (Just inst) = restore_consistency_metavar_links_insts rs (restore_consistency_metavar_links_insts_rec smv ls (Just inst))

restore_consistency_metavar_links_insts_rec :: Metavariable -> [(Metavariable,Either Term Literal -> Either Term Literal)] -> Maybe Instantiation -> Maybe Instantiation
restore_consistency_metavar_links_insts_rec _ _ Nothing = Nothing
restore_consistency_metavar_links_insts_rec _ [] (Just inst) = Just inst
restore_consistency_metavar_links_insts_rec smv ((tmv,f):rs) (Just inst) = restore_consistency_metavar_links_insts_rec smv rs (most_instantiated_inst tmv smv f (Just inst))

most_instantiated_fsol :: ExtendedSignature -> Metavariable -> Metavariable -> (Either Term Literal -> Either Term Literal) -> Maybe FullSolution -> Maybe FullSolution
most_instantiated_fsol _ _ _ _ Nothing = Nothing
--most_instantiated_fsol tmv smv f (Just fsol) = case nv of {Nothing -> Just fsol; Just (Left t1) -> case ov of {Nothing -> Just (propagate_over_metavariable_single fsol (DMetaT tmv) resv); Just (Left t2) -> case mostv of {Nothing -> Nothing; Just lt -> Just (propagate_over_metavariable_single fsol (DMetaT tmv) lt)}; Just (Right l2) -> Nothing}; Just (Right l1) -> case ov of {Nothing -> Just (propagate_over_metavariable_single fsol (DMetaL tmv) resv); Just (Left t2) -> Nothing; Just (Right l2) -> case mostv of {Nothing -> Nothing; Just lt -> Just (propagate_over_metavariable_single fsol (DMetaL tmv) lt)}}}
most_instantiated_fsol sig tmv smv f (Just fsol) = case nv of {Nothing -> Just fsol; Just (Left t1) -> case ov of {Nothing -> Just (propagate_over_metavariable_single sig fsol (DMetaT tmv) (f (Left t1))); Just (Left t2) -> case (most_instantiated (Left t2) (f (Left t1))) of {Nothing -> Nothing; Just lt -> Just (propagate_over_metavariable_single sig fsol (DMetaT tmv) lt)}; Just (Right l2) -> Nothing}; Just (Right l1) -> case ov of {Nothing -> Just (propagate_over_metavariable_single sig fsol (DMetaL tmv) (f (Right l1))); Just (Left t2) -> Nothing; Just (Right l2) -> case (most_instantiated (Right l2) (f (Right l1))) of {Nothing -> Nothing; Just lt -> Just (propagate_over_metavariable_single sig fsol (DMetaL tmv) lt)}}}  
	where 
	inst = get_instantiation fsol;
	nv = apply_inst inst smv;
	ov = apply_inst inst tmv;
--	resv = f (fromJust nv);
--	mostv = most_instantiated (fromJust ov) resv

-- propagate_over_metavariable_single :: FullSolution -> Dependent -> Either Term Literal -> FullSolution

-- A version of the function below specifically tailored to grab the values from an instantiation when restoring consistency.
-- First meta-variable is the meta-variable whose value we are updating. Second one is the meta-variable from which we are updating.
-- The function is the link between those two meta-variables (already located in the list of links).
-- It returns an instantiation which is either the original or is possibly updated to include a more updated version of the target meta-variable instantiation.
most_instantiated_inst :: Metavariable -> Metavariable -> (Either Term Literal -> Either Term Literal) -> Maybe Instantiation -> Maybe Instantiation
most_instantiated_inst _ _ _ Nothing = Nothing
--most_instantiated_inst tmv smv f (Just inst) = case nv of {Nothing -> Just inst; Just (Left t1) -> case ov of {Nothing -> Just (set_instantiation inst tmv resv); Just (Left t2) -> case mostv of {Nothing -> Nothing; Just lt -> Just (set_instantiation inst tmv lt)}; Just (Right l2) -> Nothing}; Just (Right l1) -> case ov of {Nothing -> Just (set_instantiation inst tmv resv); Just (Left t2) -> Nothing; Just (Right l2) -> case mostv of {Nothing -> Nothing; Just lt -> Just (set_instantiation inst tmv lt)}}}
most_instantiated_inst tmv smv f (Just inst) = case nv of {Nothing -> Just inst; Just (Left t1) -> case ov of {Nothing -> Just (set_instantiation inst tmv (f (Left t1))); Just (Left t2) -> case (most_instantiated (Left t2) (f (Left t1))) of {Nothing -> Nothing; Just lt -> Just (set_instantiation inst tmv lt)}; Just (Right l2) -> Nothing}; Just (Right l1) -> case ov of {Nothing -> Just (set_instantiation inst tmv (f (Right l1))); Just (Left t2) -> Nothing; Just (Right l2) -> case (most_instantiated (Right l2) (f (Right l1))) of {Nothing -> Nothing; Just lt -> Just (set_instantiation inst tmv lt)}}}  
	where 
	nv = apply_inst inst smv;
	ov = apply_inst inst tmv;
	--resv = f (fromJust nv);
	--mostv = most_instantiated (fromJust ov) resv

-- This is really just unification, where the variables are meta-variables, by the way.
-- Returns a least instantiated common instantiation of the two terms or literals, if there is one.
most_instantiated :: Either Term Literal -> Either Term Literal -> Maybe (Either Term Literal)
most_instantiated (Left t1) (Left t2) = maybe_apply Left (most_instantiated_term t1 t2)
most_instantiated (Right l1) (Right l2) = maybe_apply Right (most_instantiated_literal l1 l2)
most_instantiated _ _ = Nothing

most_instantiated_term :: Term -> Term -> Maybe Term
most_instantiated_term (TMeta _) t2 = Just t2
most_instantiated_term t1 (TMeta _) = Just t1
most_instantiated_term (TVar v1) (TVar v2) | v1 == v2 = Just (TVar v1)
most_instantiated_term (TFun f1 t1s) (TFun f2 t2s) | f1 == f2 = if (all isJust tress) then Just (TFun f1 (map fromJust tress)) else Nothing where tress = map (uncurry most_instantiated_term) (zip t1s t2s)
most_instantiated_term _ _ = Nothing

most_instantiated_literal :: Literal -> Literal -> Maybe Literal
most_instantiated_literal (LitM _) l2 = Just l2
most_instantiated_literal l1 (LitM _) = Just l1
most_instantiated_literal (Lit p1 t1s) (Lit p2 t2s) | p1 == p2 = if (all isJust tress) then Just (Lit p1 (map fromJust tress)) else Nothing where tress = map (uncurry most_instantiated_term) (zip t1s t2s)
most_instantiated_literal _ _ = Nothing


-- type MetavariableLink = (Metavariable,[Metavariable,Either Term Literal -> Either Term Literal])
-- type FullSolution = ([Metavariable],[MetavariableEquation],UnifSolution,PartiallySolvedDGraph)
-- type UnifSolution = (Instantiation,[Constraint])
-- type PartiallySolvedDGraph = (DependencyGraph,DependencyGraphSolution,[UnifierEquation])


-- So far, only direct meta-variables should be limited really, because we don't do exposing, pulling or anything like that.
-- This might need to be reviewed in the future.
find_dep_var_constraints :: ExtendedSignature -> Dependent -> (Variable -> Bool)
find_dep_var_constraints ((ps,fs,nvars),mvpart,sks,ifilt) (DMetaT mv) = metavar_var_constraint mvpart mv
find_dep_var_constraints ((ps,fs,nvars),mvpart,sks,ifilt) (DMetaL mv) = metavar_var_constraint mvpart mv
find_dep_var_constraints ((ps,fs,nvars),mvpart,sks,ifilt) _ = (\v -> True)

-- metavar_var_constraint :: MetavariablePartition -> Metavariable -> (Variable -> Bool)

find_banned_vars_in_instantiation :: DependencyGraph -> Dependent -> [Variable]
find_banned_vars_in_instantiation g d = find_banned_vars_in_instantiation_rec g d

find_banned_vars_in_instantiation_rec :: DependencyGraph -> Dependent -> [Variable]
find_banned_vars_in_instantiation_rec g d = concat (map (\sd -> (find_banned_vars_in_instantiation g sd) ++ (find_directly_banned_vars_in_instantiation sd)) (map get_htarget (get_outgoing_hdeps (find_node g d))))
--find_banned_vars_in_instantiation_rec g d = if (isNothing nmb) then [] else (concat (map (\sd -> (find_banned_vars_in_instantiation g sd) ++ (find_directly_banned_vars_in_instantiation sd)) (map get_htarget (get_outgoing_hdeps (find_node g d))))) where nmb = find_node_maybe g d

find_directly_banned_vars_in_instantiation :: Dependent -> [Variable]
find_directly_banned_vars_in_instantiation (DVar v) = [v]
find_directly_banned_vars_in_instantiation (DMetaT _) = []
find_directly_banned_vars_in_instantiation (DMetaL _) = []
find_directly_banned_vars_in_instantiation (DRec u d) = find_directly_banned_vars_in_instantiation d

find_variable_set :: Dependent -> VariableSet
find_variable_set (DMetaT _) = Dom (U 0)
find_variable_set (DMetaL _) = Dom (U 0)
find_variable_set (DRec u _) = Rg u

propagate_over_metavariable_enum :: ExtendedSignature -> FullSolution -> Dependent -> Enumeration (_,Either Term Literal) -> Enumeration (_,FullSolution)
propagate_over_metavariable_enum sig fs dep ev = apply_enum_1_h (propagate_over_metavariable_single sig fs dep) ev

propagate_over_metavariable_single :: ExtendedSignature -> FullSolution -> Dependent -> Either Term Literal -> FullSolution
propagate_over_metavariable_single sig fs dep v = factorize_update_clean sig (update_graph_single_maybe sig fs2 dv) where (fs1,mv) = expose_metavariable fs dep; dv = (dep,v); fs2 = set_solution (set_instantiation_fs fs1 mv v) dv
--propagate_over_metavariable_single fs dep v = update_graph_all (set_solution (set_instantiation_fs fs v) dv) [dv] [] where dv = (dep,v)

-- We assume that the dependent is u1 u2 ... un X for X a meta-variable. We do several things:
--		- Replace u1 u2 ... un X with u1 u2 ... un-1 Y where Y = un X, and then u1 u2 ... un-1 Y with u1 u2 ... un-2 Z where Z = un-1 Y, and so on, until we have only another meta-variable, X', and
--			add all these meta-variable equations and new meta-variables to the solution.
--		- Output the exposed meta-variable, so that we can enumerate over it.
--		- We do not replace the dependent in the graph. When we enumerate the new meta-variable, we should replace its value on the old dependent. Replacing the dependent only to replace it again afterwards would be doing unnecessary work.
expose_metavariable :: FullSolution -> Dependent -> (FullSolution,Metavariable)
expose_metavariable fs (DMetaT mv) = (fs,mv)
expose_metavariable fs (DMetaL mv) = (fs,mv)
expose_metavariable fs (DRec u d) = (((nmv:rmvs),(MetaEq nmv u rmv):reqs,(rinst,rcs),(rg,rsol,rueqs)),nmv) where ((rmvs,reqs,(rinst,rcs),(rg,rsol,rueqs)),rmv) = expose_metavariable fs d; nmv = new_metavar rmvs

-- We provide both the dependent in the graph (which has unifiers on it) and the exposed meta-variable. We assume that the provided solution already includes this exposed meta-variable and the necessary equations, but has not replaced it in the graph (because it is not necessary to do this).
-- We replace this value in the solution, by re-building the constraints it is involved in and re-calculating the graph, and also adding it to the instantiation.
propagate_metavar_value :: FullSolution -> Dependent -> Metavariable -> Either Term Literal -> FullSolution
propagate_metavar_value (mvs,eqs,(inst,cs),(g,sol,ueqs)) dep mv v = (mvs1,eqs,(rinst,[]),(rg,rsol,rueqs)) where (mvs1,(inst1,cs1)) = recalculate_constraints_from_dependent mvs (inst,cs) g dep v; (mvs2,mveqs2,(inst2,cs2),(rg,rsol,rueqs)) = update_graph_with_constraints_fsol (mvs1,eqs,(inst1,[]),((remove_node g dep),sol,ueqs)) cs1; rinst = set_instantiation inst1 mv v

recalculate_constraints_from_dependent :: [Metavariable] -> UnifSolution -> DependencyGraph -> Dependent -> Either Term Literal -> ([Metavariable],UnifSolution)
recalculate_constraints_from_dependent mvs (inst,cs) g dep (Left t) = recalculate_constraints_eqdep mvs1 (inst1,cs1) (Left (all_simpl_mterm (metaterm_from_depnode dep))) (Left (MTermT t)) g [dep] where n = find_node g dep; (mvs1,(inst1,cs1)) = recalculate_constraints_hdep mvs (inst,cs) (Left (all_simpl_mterm (metaterm_from_depnode dep))) (Left (MTermT t)) ((get_outgoing_hdeps n) ++ (get_incoming_hdeps n))
--recalculate_constraints_from_dependent mvs (inst,cs) g dep (Left t) = if (isNothing nmb) then (mvs,(inst,cs)) else (recalculate_constraints_eqdep mvs1 (inst1,cs1) (Left (all_simpl_mterm (metaterm_from_depnode dep))) (Left (MTermT t)) g [dep]) where nmb = find_node_maybe g dep; n = find_node g dep; (mvs1,(inst1,cs1)) = recalculate_constraints_hdep mvs (inst,cs) (Left (all_simpl_mterm (metaterm_from_depnode dep))) (Left (MTermT t)) ((get_outgoing_hdeps n) ++ (get_incoming_hdeps n)) 
recalculate_constraints_from_dependent mvs (inst,cs) g dep (Right l) = recalculate_constraints_eqdep mvs1 (inst1,cs1) (Right (all_simpl_mlit (metalit_from_depnode dep))) (Right (MLitL l)) g [dep] where n = find_node g dep; (mvs1,(inst1,cs1)) = recalculate_constraints_hdep mvs (inst,cs) (Right (all_simpl_mlit (metalit_from_depnode dep))) (Right (MLitL l)) ((get_outgoing_hdeps n) ++ (get_incoming_hdeps n))
--recalculate_constraints_from_dependent mvs (inst,cs) g dep (Right l) = if (isNothing nmb) then (mvs,(inst,cs)) else (recalculate_constraints_eqdep mvs1 (inst1,cs1) (Right (all_simpl_mlit (metalit_from_depnode dep))) (Right (MLitL l)) g [dep]) where nmb = find_node_maybe g dep; n = find_node g dep; (mvs1,(inst1,cs1)) = recalculate_constraints_hdep mvs (inst,cs) (Right (all_simpl_mlit (metalit_from_depnode dep))) (Right (MLitL l)) ((get_outgoing_hdeps n) ++ (get_incoming_hdeps n))  

-- t = Enumeration (_,Fullsolution)
-- r = Fullsolution
enumerate_and_propagate_all :: (MetaunificationHeuristic hl ht) -> ExtendedSignature -> FullSolution -> Enumeration (EnumPropagateAll _,FullSolution)
enumerate_and_propagate_all heur sig fs = if ((is_fullsol_solved fs) || (is_fullsol_unsatisfiable fs)) then equiv_enum enumerate_and_propagate_all_equiv_1_left enumerate_and_propagate_all_equiv_1_right (no_help (single_enum fs)) else (case parc of {Left res -> enumerate_and_propagate_all heur sig res; Right res -> equiv_enum enumerate_and_propagate_all_equiv_2_left enumerate_and_propagate_all_equiv_2_right (diagonalize_h (enumerate_and_propagate_all heur sig) res)}) where parc = enumerate_or_propagate heur sig fs

enumerate_and_propagate_all_equiv_1_left :: (Bool,FullSolution) -> (EnumPropagateAll h1,FullSolution)
enumerate_and_propagate_all_equiv_1_left (b,fs) = (EPAllNoHelp b,fs)

enumerate_and_propagate_all_equiv_1_right :: (EnumPropagateAll h1,FullSolution) -> (Bool,FullSolution)
enumerate_and_propagate_all_equiv_1_right (EPAllNoHelp b,fs) = (b,fs)

enumerate_and_propagate_all_equiv_2_left :: (_,FullSolution) -> (EnumPropagateAll h1,FullSolution)
enumerate_and_propagate_all_equiv_2_left (x,fs) = (EPAll x,fs)

enumerate_and_propagate_all_equiv_2_right :: (EnumPropagateAll h1,FullSolution) -> (_,FullSolution)
enumerate_and_propagate_all_equiv_2_right (EPAll x,fs) = (x,fs)

data EnumPropagateAll h1 = EPAllNoHelp Bool | EPAll ((((h1,FullSolution),[((h1,FullSolution),Enumerator (EnumPropagateAll h1,FullSolution),Int,(EnumPropagateAll h1,FullSolution))],[((h1,FullSolution),Enumerator (EnumPropagateAll h1,FullSolution),Int,(EnumPropagateAll h1,FullSolution))]),(h1,FullSolution)),EnumPropagateAll h1)


-- diagonalize_h :: (a -> Enumeration (h2,b)) -> Enumeration (h1,a) -> Enumeration (((((h1,a),[((h1,a),Enumerator (h2,b),Int,(h2,b))],[((h1,a),Enumerator (h2,b),Int,(h2,b))]),(h1,a)),h2),b)



-- Building final solutions from solved dependency graphs.
-- First, building an initial minimal unifier description from a dependency graph solution.
-- This is done by following the order of the unifiers, so that we can substitute previous one in new dependents.
-- Note that this leaves the dependents with meta-variables untouched. But these are solved BEFORE proceeding to the next unifier.
--unif_from_dgraph_sol :: [Unifier] -> DependencyGraphSolution -> [UnifierDescription]

-- Builds the minimal unifier description.
-- Because of how we run this function, we assume that any dependents having u as the outermost unifier necessarily do not have more inner unifiers. We leave this case non-exhaustive to flag up the error.
-- It could be, however, that the unifier description is inconsistent. To signal this, we return Nothing.
build_minimal_unif_desc :: Unifier -> [Either (Metaterm,Term) (Metaliteral,Literal)] -> Maybe UnifierDescription
build_minimal_unif_desc _ [] = Just []
build_minimal_unif_desc u ((Left (MTermR v mt,t)):vs) | (u == v) && (isNothing (is_metavar_term mt)) = append_mb_mb (simpl_dep_term (unlift_mterm mt) t) (build_minimal_unif_desc u vs)
build_minimal_unif_desc u ((Right (MLitR v ml,l)):vs) | (u == v) && (isNothing (is_metavar_lit ml)) = append_mb_mb (simpl_dep_lit (unlift_mlit ml) l) (build_minimal_unif_desc u vs)
build_minimal_unif_desc u (v:vs) = build_minimal_unif_desc u vs

translate_dgraph_sol_pairs :: DependencyGraphSolution -> [Either (Metaterm,Term) (Metaliteral,Literal)]
translate_dgraph_sol_pairs [] = []
translate_dgraph_sol_pairs ((d,Left v):ds) = (Left (metaterm_from_depnode d,v)):(translate_dgraph_sol_pairs ds)
translate_dgraph_sol_pairs ((d,Right v):ds) = (Right (metalit_from_depnode d,v)):(translate_dgraph_sol_pairs ds)

-- For meta-variables, we invert the unifiers. This may give us some more enumeration on the variables that are yet unspecified, but it gives us a unifier description, and from the inversion we obtain an instantiation, both fully specified.
invert_metavar_dependents :: MetavariablePartition -> [MetavariableEquation] -> Unifier -> [Either (Metaterm,Term) (Metaliteral,Literal)] -> UnifierDescription -> Enumeration (_,Maybe (UnifierDescription,Instantiation))
invert_metavar_dependents mvpart eqs u vs ud = recursively_diagonalize_h (invert_metavar_dependents_step mvpart eqs ud u) vs

-- t = [Either (Metaterm,Term) (Metaliteral,Literal)]
-- r = Maybe (UnifierDescription,Instantiation)
invert_metavar_dependents_step :: MetavariablePartition -> [MetavariableEquation] -> UnifierDescription -> Unifier -> [Either (Metaterm,Term) (Metaliteral,Literal)] -> Either ([Maybe (UnifierDescription,Instantiation)] -> Enumeration (_,Maybe (UnifierDescription,Instantiation))) ([Either (Metaterm,Term) (Metaliteral,Literal)],([Maybe (UnifierDescription,Instantiation)] -> Enumeration (_,Maybe (UnifierDescription,Instantiation)),CombinationScheme (Maybe (UnifierDescription,Instantiation))))
--invert_metavar_dependents_step nvars eqs ud u [] = Left (\x -> enum_hleft_h (no_help (single_enum (ud,idinst))))
invert_metavar_dependents_step mvpart eqs ud u [Left (MTermR v (MTermT (TMeta mv)),t)] | u == v = Left (\pairs -> enum_hleft_h (enum_hleft_h (enum_hleft_h (apply_enum_1_h (maybe_apply (\pair -> ((fst pair) ++ ud,snd pair))) (invert_metavar_dependent_term_maybe mvpart eqs mv t u (append_mb_x (maybe_concat (map (maybe_apply fst) pairs)) ud))))))
invert_metavar_dependents_step mvpart eqs ud u [Right (MLitR v (MLitL (LitM mv)),l)] | u == v = Left (\pairs -> enum_hleft_h (enum_hleft_h (enum_hright_h (apply_enum_1_h (maybe_apply (\pair -> ((fst pair) ++ ud,snd pair))) (invert_metavar_dependent_literal_maybe mvpart eqs mv l u (append_mb_x (maybe_concat (map (maybe_apply fst) pairs)) ud))))))
invert_metavar_dependents_step mvpart eqs ud u ((Left (MTermR v (MTermT (TMeta mv)),t)):vs) | u == v = Right (vs,
											(\pairs -> enum_hright_h (enum_hleft_h (invert_metavar_dependent_term_maybe mvpart eqs mv t u (append_mb_x (maybe_concat (map (maybe_apply fst) pairs)) ud))),
											Comb (maybe_apply_2 invert_metavar_dependents_comb) (maybe_apply_co2 invert_metavar_dependents_decomb)))
invert_metavar_dependents_step mvpart eqs ud u ((Right (MLitR v (MLitL (LitM mv)),l)):vs) | u == v = Right (vs,
											(\pairs -> enum_hright_h (enum_hright_h (invert_metavar_dependent_literal_maybe mvpart eqs mv l u (append_mb_x (maybe_concat (map (maybe_apply fst) pairs)) ud))),
											Comb (maybe_apply_2 invert_metavar_dependents_comb) (maybe_apply_co2 invert_metavar_dependents_decomb)))
invert_metavar_dependents_step mvpart eqs ud u (v:vs) = Right (vs,(\pairs -> enum_hleft_h (enum_hright_h (no_help (single_enum (Just ([],idinst))))),Comb (maybe_apply_2 invert_metavar_dependents_comb) (maybe_apply_co2 invert_metavar_dependents_decomb)))
invert_metavar_dependents_step mvpart eqs ud u [] = Left (\pairs -> enum_hleft_h (enum_hright_h (no_help (single_enum (Just (ud,idinst))))))


-- The de-composition is not relevant, because it would only be if the enumeration looked on the previous element, but we know this is not the case here. So we just decompose into the whole thing first, and nothing afterwards.
invert_metavar_dependents_comb :: (UnifierDescription,Instantiation) -> (UnifierDescription,Instantiation) -> (UnifierDescription,Instantiation)
invert_metavar_dependents_comb (ud1,inst1) (ud2,inst2) = (ud1++ud2,compose_inst inst1 inst2)

invert_metavar_dependents_decomb :: (UnifierDescription,Instantiation) -> ((UnifierDescription,Instantiation),(UnifierDescription,Instantiation))
invert_metavar_dependents_decomb (ud,inst) = ((ud,inst),([],idinst))



-- recursively_diagonalize_h :: (t -> Either ([r] -> Enumeration (h1,r)) (t,([r] -> Enumeration (h1,r),CombinationScheme r))) -> (t -> Enumeration (RecursiveDiagonalization h1 r,r))
-- data CombinationScheme r = Comb (r -> r -> r) (r -> (r,r))

invert_metavar_dependent_term_maybe :: MetavariablePartition -> [MetavariableEquation] -> Metavariable -> Term -> Unifier -> Maybe UnifierDescription -> Enumeration (_,Maybe (UnifierDescription,Instantiation))
invert_metavar_dependent_term_maybe _ _ _ _ _ Nothing = enum_hleft_h (no_help (single_enum Nothing))
invert_metavar_dependent_term_maybe mvpart eqs mv t u (Just ud) = enum_hright_h (invert_metavar_dependent_term mvpart eqs mv t u ud)

invert_metavar_dependent_term :: MetavariablePartition -> [MetavariableEquation] -> Metavariable -> Term -> Unifier -> UnifierDescription -> Enumeration (_,Maybe (UnifierDescription,Instantiation))
invert_metavar_dependent_term (pmvs,ninit,nmvs) eqs mv t u ud = apply_enum_1_h (invert_metavar_dependent_term_helper mv) einvs where vset = find_possible_vars_metavar eqs mv; bannedset = vars_in_unif_desc ud; nvars = ninit + (sum nmvs); cstr = metavar_var_constraint (pmvs,ninit,nmvs) mv; vs = filter (\v -> (cstr v) && (not (elem v bannedset))) (get_vars_set nvars vset); invs = invert_unifier_term nvars u vs ud t; einvs = enum_from_list_maybe invs

invert_metavar_dependent_term_helper :: Metavariable -> Maybe (Term,UnifierDescription) -> Maybe (UnifierDescription,Instantiation)
invert_metavar_dependent_term_helper _ Nothing = Nothing
invert_metavar_dependent_term_helper mv (Just (t,ud)) = Just (ud,build_inst mv (Left t))

invert_metavar_dependent_literal_maybe :: MetavariablePartition -> [MetavariableEquation] -> Metavariable -> Literal -> Unifier -> Maybe UnifierDescription -> Enumeration (_,Maybe (UnifierDescription,Instantiation))
invert_metavar_dependent_literal_maybe _ _ _ _ _ Nothing = enum_hleft_h (no_help (single_enum Nothing))
invert_metavar_dependent_literal_maybe mvpart eqs mv l u (Just ud) = enum_hright_h (invert_metavar_dependent_literal mvpart eqs mv l u ud)

invert_metavar_dependent_literal :: MetavariablePartition -> [MetavariableEquation] -> Metavariable -> Literal -> Unifier -> UnifierDescription -> Enumeration (_,Maybe (UnifierDescription,Instantiation))
invert_metavar_dependent_literal (pmvs,ninit,nmvs) eqs mv l u ud = apply_enum_1_h (invert_metavar_dependent_literal_helper mv) einvs where vset = find_possible_vars_metavar eqs mv; bannedset = vars_in_unif_desc ud; nvars = ninit + (sum nmvs); cstr = metavar_var_constraint (pmvs,ninit,nmvs) mv; vs = filter (\v -> (cstr v) && (not (elem v bannedset))) (get_vars_set nvars vset); invs = invert_unifier_literal nvars u vs ud l; einvs = enum_from_list_maybe invs

invert_metavar_dependent_literal_helper :: Metavariable -> Maybe (Literal,UnifierDescription) -> Maybe (UnifierDescription,Instantiation)
invert_metavar_dependent_literal_helper _ Nothing = Nothing
invert_metavar_dependent_literal_helper mv (Just (l,ud)) = Just (ud,build_inst mv (Right l))


-- invert_unifier_term :: [Variable] -> UnifierDescription -> Term -> [(Term,UnifierDescription)]
-- find_possible_vars_metavar :: [MetavariableEquation] -> Metavariable -> VariableSet
-- enumerate_terms_dependent :: Signature -> VariableSet -> [Variable] -> Enumeration (((Int,[Term]),[Term]),Term)
-- get_vars_set :: Int -> VariableSet -> [Variable]


-- Check that the unifier description is consistent.
-- is_unif_desc_consistent :: UnifierDescription -> Bool

-- From that, we update all the other dependents. Also removes any dependents on that level which have been fully specified.
-- First instantiate the meta-variables.
instantiate_all_possible_metavars :: Instantiation -> [Either (Metaterm,Term) (Metaliteral,Literal)] -> [Either (Metaterm,Term) (Metaliteral,Literal)]
instantiate_all_possible_metavars inst [] = []
instantiate_all_possible_metavars inst ((Left (mt,t)):vs) = ((Left (apply_inst_mterm inst mt,t)):(instantiate_all_possible_metavars inst vs))
instantiate_all_possible_metavars inst ((Right (ml,l)):vs) = ((Right (apply_inst_mlit inst ml,l)):(instantiate_all_possible_metavars inst vs))

-- Second remove the graph solutions that haver been already used.
clean_output_from_graph :: Unifier -> [Either (Metaterm,Term) (Metaliteral,Literal)] -> [Either (Metaterm,Term) (Metaliteral,Literal)]
clean_output_from_graph u [] = []
clean_output_from_graph u ((Left (MTermR v _,t)):vs) | u == v = clean_output_from_graph u vs
clean_output_from_graph u ((Left (mt,t)):vs) = ((Left (mt,t)):(clean_output_from_graph u vs))
clean_output_from_graph u ((Right (MLitR v _,l)):vs) | u == v = clean_output_from_graph u vs
clean_output_from_graph u ((Right (ml,l)):vs) = ((Right (ml,l)):(clean_output_from_graph u vs))

-- Third substitute unifiers on the remaining dependents.
substitute_unifier :: Int -> Unifier -> UnifierDescription -> [Either (Metaterm,Term) (Metaliteral,Literal)] -> [Either (Metaterm,Term) (Metaliteral,Literal)]
substitute_unifier nvars u ud vs = substitute_unifier_rec u (obtain_substitution nvars u ud) vs

substitute_unifier_rec :: Unifier -> Substitution -> [Either (Metaterm,Term) (Metaliteral,Literal)] -> [Either (Metaterm,Term) (Metaliteral,Literal)]
substitute_unifier_rec u s [] = []
substitute_unifier_rec u s ((Left (mt,t)):vs) = ((Left (substitute_unifier_metaterm u s mt,t)):(substitute_unifier_rec u s vs)) 
substitute_unifier_rec u s ((Right (ml,l)):vs) = ((Right (substitute_unifier_metaliteral u s ml,l)):(substitute_unifier_rec u s vs))

substitute_unifier_metaterm :: Unifier -> Substitution -> Metaterm -> Metaterm
substitute_unifier_metaterm u s (MTermR v mt) | u == v = substitute_unifier_inside_metaterm s mt
substitute_unifier_metaterm u s (MTermR v mt) | u /= v = MTermR v (substitute_unifier_metaterm u s mt)
substitute_unifier_metaterm u s (MTermT t) = (MTermT t)
substitute_unifier_metaterm u s (MTermF f mts) = MTermF f (map (substitute_unifier_metaterm u s) mts)

-- If we are here, there should be no more unifiers. We leave this case non-exhaustive to flag up the error.
substitute_unifier_inside_metaterm :: Substitution -> Metaterm -> Metaterm
substitute_unifier_inside_metaterm s (MTermT t) = MTermT (apply_subst s t)
substitute_unifier_inside_metaterm s (MTermF f mts) = MTermF f (map (substitute_unifier_inside_metaterm s) mts)

substitute_unifier_metaliteral :: Unifier -> Substitution -> Metaliteral -> Metaliteral
substitute_unifier_metaliteral u s (MLitR v ml) | u == v = substitute_unifier_inside_metaliteral s ml
substitute_unifier_metaliteral u s (MLitR v ml) | u /= v = MLitR v (substitute_unifier_metaliteral u s ml)
substitute_unifier_metaliteral u s (MLitL l) = MLitL l
substitute_unifier_metaliteral u s (MLitP p mts) = MLitP p (map (substitute_unifier_metaterm u s) mts)

-- If we are here, there should be no more unifiers. We leave this case non-exhaustive to flag up the error.
substitute_unifier_inside_metaliteral :: Substitution -> Metaliteral -> Metaliteral
substitute_unifier_inside_metaliteral s (MLitL l) = MLitL (apply_subst_lit s l)
substitute_unifier_inside_metaliteral s (MLitP p mts) = MLitP p (map (substitute_unifier_inside_metaterm s) mts)


-- simpl_dep_term :: Term -> Term -> UnifierDescription
-- simpl_dep_lit :: Literal -> Literal -> UnifierDescription
-- complete_unif_description :: [Variable] -> (Variable -> Variable) -> UnifierDescription -> UnifierDescription
-- obtain_substitution :: [Variable] -> (Variable -> Variable) -> UnifierDescription -> Substitution
-- replace_mterm_mterm :: Metaterm -> Metaterm -> Metaterm -> Metaterm


-- Finally, solve meta-variable equations to instantiate the original meta-variables.
-- At this point, unifiers have been fully specified. Moreover, we don't need to complete the unifier description, because the equation will necessarily not refer to image variables which are just
-- the result of completion. 
-- For the same reason, the inversion can no longer change the description, and so we ignore this part of the result.
-- To detect whether it is a term or literal meta-variable, we assume that only one of those two instantiations on the source meta-variable will be a non-metavariable. If this does not hold, flag up the error.
solve_metavar_eq :: Int -> (Unifier -> UnifierDescription) -> Instantiation -> MetavariableEquation -> Enumeration (_,Instantiation)
solve_metavar_eq nvars descs inst (MetaEq tmv u smv) = 
	case v of
	{
		Left t -> enum_hleft_h (apply_enum_1_h (solve_metavar_eq_single_term tmv) (apply_enum_1_h fst (enum_from_list (invert_unifier_term nvars u [] ud t))));
		Right l -> enum_hright_h (apply_enum_1_h (solve_metavar_eq_single_lit tmv) (apply_enum_1_h fst (enum_from_list (invert_unifier_literal nvars u [] ud l))))
	}
	where ud = descs u; v = get_value_metavar inst smv

get_value_metavar :: Instantiation -> Metavariable -> Either Term Literal
get_value_metavar (linst,tinst) mv = 
	case (bl,bt) of
	{
		(True,False) -> Left t;
		(False,True) -> Right l
	}
	where l = fun_from_litinst linst mv; t = fun_from_terminst tinst mv; bl = has_lit_metavar l; bt = has_term_metavar t

has_lit_metavar :: Literal -> Bool
has_lit_metavar (Lit _ ts) = any has_term_metavar ts
has_lit_metavar (LitM _) = True

has_term_metavar :: Term -> Bool
has_term_metavar (TVar _) = False
has_term_metavar (TMeta _) = True
has_term_metavar (TFun _ ts) = any has_term_metavar ts

solve_metavar_eq_single_term :: Metavariable -> Term -> Instantiation
solve_metavar_eq_single_term mv t = build_inst mv (Left t)

solve_metavar_eq_single_lit :: Metavariable -> Literal -> Instantiation
solve_metavar_eq_single_lit mv l = build_inst mv (Right l)

-- data MetavariableEquation = MetaEq Metavariable Unifier Metavariable
-- vars_in_unif_desc :: UnifierDescription -> [Variable]
-- invert_unifier_term :: [Variable] -> UnifierDescription -> Term -> [(Term,UnifierDescription)]

-- t = [MetavariableEquation]
-- r = Instantiation
solve_metavar_eqs :: Int -> (Unifier -> UnifierDescription) -> Instantiation -> [MetavariableEquation] -> Enumeration (_,Instantiation)
solve_metavar_eqs nvars descs inst eqs = recursively_diagonalize_h (solve_metavar_eqs_step nvars descs inst) eqs

solve_metavar_eqs_step :: Int -> (Unifier -> UnifierDescription) -> Instantiation -> [MetavariableEquation] -> Either ([Instantiation] -> Enumeration (_,Instantiation)) ([MetavariableEquation],([Instantiation] -> Enumeration (_,Instantiation),CombinationScheme Instantiation))
solve_metavar_eqs_step _ descs inst [] = Left (\insts -> enum_hleft_h (no_help (single_enum inst)))
solve_metavar_eqs_step nvars descs inst (eq:eqs) = Right (eqs,(\insts -> enum_hright_h (solve_metavar_eq nvars descs (compose_inst (compose_insts insts) inst) eq),Comb solve_metavar_eqs_comb solve_metavar_eqs_decomb)) 

solve_metavar_eqs_comb :: Instantiation -> Instantiation -> Instantiation
solve_metavar_eqs_comb inst1 inst2 = compose_inst inst1 inst2

-- Enumeration ultimately comes from lists, so there's no need to uncombine, we just return the instantiation on the second part, an and idinst on the first.
solve_metavar_eqs_decomb :: Instantiation -> (Instantiation,Instantiation)
solve_metavar_eqs_decomb inst = (idinst,inst)

-- recursively_diagonalize_h :: (t -> Either ([r] -> Enumeration (h1,r)) (t,([r] -> Enumeration (h1,r),CombinationScheme r))) -> (t -> Enumeration (RecursiveDiagonalization h1 r,r))
-- data CombinationScheme r = Comb (r -> r -> r) (r -> (r,r))


-- Put everything together, after solving the graph.
-- t = [Unifier]
-- r = (([UnifierDescription],Instantiation),[Either (Metaterm,Term) (Metaliteral,Literal)])
instantiation_from_dgraph_sol :: ExtendedSignature -> FullSolution -> [Unifier] -> Enumeration (_,Maybe ([UnifierDescription],Instantiation))
instantiation_from_dgraph_sol sig fs us = if (is_fullsol_unsatisfiable fs) then (enum_hleft_h (no_help (single_enum Nothing))) else (enum_hright_h (apply_enum_1_h (maybe_apply (\pair -> case pair of {(uds,inst) -> (reverse uds,inst)})) (apply_enum_1_h fst (recursively_diagonalize_h (instantiation_from_dgraph_sol_step sig fs) us))))

instantiation_from_dgraph_sol_step :: ExtendedSignature -> FullSolution -> [Unifier] -> Either ([(Maybe ([UnifierDescription],Instantiation),[Either (Metaterm,Term) (Metaliteral,Literal)])] -> Enumeration (_,(Maybe ([UnifierDescription],Instantiation),[Either (Metaterm,Term) (Metaliteral,Literal)]))) ([Unifier],([(Maybe ([UnifierDescription],Instantiation),[Either (Metaterm,Term) (Metaliteral,Literal)])] -> Enumeration (_,(Maybe ([UnifierDescription],Instantiation),[Either (Metaterm,Term) (Metaliteral,Literal)])),CombinationScheme ((Maybe ([UnifierDescription],Instantiation),[Either (Metaterm,Term) (Metaliteral,Literal)]))))
instantiation_from_dgraph_sol_step sig fs [u] = Left (\prevs -> instantiation_from_dgraph_sol_step_helper sig fs u prevs)
instantiation_from_dgraph_sol_step sig fs (u:us) = Right (us,(\prevs -> instantiation_from_dgraph_sol_step_helper sig fs u prevs,Comb instantiation_from_dgraph_sol_comb_helper_maybe instantiation_from_dgraph_sol_decomb_helper_maybe))

-- We only care about the last step to calculate the next.
instantiation_from_dgraph_sol_step_helper :: ExtendedSignature -> FullSolution -> Unifier -> [(Maybe ([UnifierDescription],Instantiation),[Either (Metaterm,Term) (Metaliteral,Literal)])] -> Enumeration (_,((Maybe ([UnifierDescription],Instantiation),[Either (Metaterm,Term) (Metaliteral,Literal)])))
instantiation_from_dgraph_sol_step_helper ((ps,fs,nvars),mvpart,sks,ifilt) (mvs,eqs,(inst,cs),(g,sol,ueqs)) u [] = if (isNothing min_ud) then (enum_hleft_h instantiation_from_dgraph_unsat_sol) else (enum_hright_h all_together)
	where curated_sol = translate_dgraph_sol_pairs sol;
		min_ud = build_minimal_unif_desc u curated_sol;
		min_ud_just = case min_ud of {Just x -> x};
		with_metavars = invert_metavar_dependents mvpart eqs u curated_sol min_ud_just;
		filtered_consistent = enum_maybe_filter_h instantiation_from_dgraph_sol_unif_filter with_metavars;
		composed_inst = apply_enum_1_h (maybe_apply (\pair -> (fst pair,compose_inst (snd pair) inst))) filtered_consistent;
		inst_clean_subst = apply_enum_1_h (instantiation_from_dgraph_sol_step_helper_2 ((ps,fs,nvars),mvpart,sks,ifilt) u curated_sol) composed_inst;
		all_together = apply_enum_1_h (instantiation_from_dgraph_sol_step_helper_3 []) inst_clean_subst
instantiation_from_dgraph_sol_step_helper ((ps,fs,nvars),mvpart,sks,ifilt) (mvs,eqs,(inst,cs),(g,sol,ueqs)) u ((Just (uds,previnst),l):_) = if (isNothing min_ud) then (enum_hleft_h instantiation_from_dgraph_unsat_sol) else (enum_hright_h all_together)
	where min_ud = build_minimal_unif_desc u l;
		min_ud_just = case min_ud of {Just x -> x};
		with_metavars = invert_metavar_dependents mvpart eqs u l min_ud_just;
		filtered_consistent = enum_maybe_filter_h instantiation_from_dgraph_sol_unif_filter with_metavars;
		composed_inst = apply_enum_1_h (maybe_apply (\pair -> (fst pair,compose_inst (snd pair) previnst))) filtered_consistent;
		inst_clean_subst = apply_enum_1_h (instantiation_from_dgraph_sol_step_helper_2 ((ps,fs,nvars),mvpart,sks,ifilt) u l) composed_inst;
		all_together = apply_enum_1_h (instantiation_from_dgraph_sol_step_helper_3 uds) inst_clean_subst
instantiation_from_dgraph_sol_step_helper ((ps,fs,nvars),mvpart,sks,ifilt) (mvs,eqs,(inst,cs),(g,sol,ueqs)) u ((Nothing,l):_) = enum_hleft_h instantiation_from_dgraph_unsat_sol

instantiation_from_dgraph_sol_unif_filter :: (UnifierDescription,Instantiation) -> Bool
instantiation_from_dgraph_sol_unif_filter (ud,inst) = is_unif_desc_consistent ud

instantiation_from_dgraph_unsat_sol :: Enumeration (_,((Maybe ([UnifierDescription],Instantiation),[Either (Metaterm,Term) (Metaliteral,Literal)])))
instantiation_from_dgraph_unsat_sol = no_help (single_enum (Nothing,[]))		

instantiation_from_dgraph_sol_step_helper_2 :: ExtendedSignature -> Unifier -> [Either (Metaterm,Term) (Metaliteral,Literal)] -> Maybe (UnifierDescription,Instantiation) -> (Maybe (UnifierDescription,Instantiation),[Either (Metaterm,Term) (Metaliteral,Literal)])
instantiation_from_dgraph_sol_step_helper_2 ((ps,fs,nvars),mvpart,sks,ifilt) u l Nothing = (Nothing,[])
instantiation_from_dgraph_sol_step_helper_2 ((ps,fs,nvars),mvpart,sks,ifilt) u l (Just (ud,inst)) = (Just (ud,inst),substitute_unifier nvars u ud (clean_output_from_graph u (instantiate_all_possible_metavars inst l)))

instantiation_from_dgraph_sol_step_helper_3 :: [UnifierDescription] -> (Maybe (UnifierDescription,Instantiation),[Either (Metaterm,Term) (Metaliteral,Literal)]) -> (Maybe ([UnifierDescription],Instantiation),[Either (Metaterm,Term) (Metaliteral,Literal)])
instantiation_from_dgraph_sol_step_helper_3 uds (Nothing,l) = (Nothing,l)
instantiation_from_dgraph_sol_step_helper_3 uds (Just (ud,inst),l) = (Just (ud:uds,inst),l)

-- type Signature = ([Predicate],[Function],Int)
-- type FullSolution = ([Metavariable],[MetavariableEquation],UnifSolution,PartiallySolvedDGraph)
-- type UnifSolution = (Instantiation,[Constraint])
-- type PartiallySolvedDGraph = (DependencyGraph,DependencyGraphSolution,[UnifierEquation])
-- translate_dgraph_sol_pairs :: DependencyGraphSolution -> [Either (Metaterm,Term) (Metaliteral,Literal)]
-- build_minimal_unif_desc :: Unifier -> [Either (Metaterm,Term) (Metaliteral,Literal)] -> UnifierDescription
-- invert_metavar_dependents :: Int -> [MetavariableEquation] -> Unifier -> [Either (Metaterm,Term) (Metaliteral,Literal)] -> UnifierDescription -> Enumeration (_,(UnifierDescription,Instantiation))
-- is_unif_desc_consistent :: UnifierDescription -> Bool
-- instantiate_all_possible_metavars :: Instantiation -> [Either (Metaterm,Term) (Metaliteral,Literal)] -> [Either (Metaterm,Term) (Metaliteral,Literal)]
-- clean_output_from_graph :: Unifier -> [Either (Metaterm,Term) (Metaliteral,Literal)] -> [Either (Metaterm,Term) (Metaliteral,Literal)]
-- substitute_unifier :: Int -> Unifier -> UnifierDescription -> [Either (Metaterm,Term) (Metaliteral,Literal)] -> [Either (Metaterm,Term) (Metaliteral,Literal)]
-- solve_metavar_eqs :: (Unifier -> UnifierDescription) -> Instantiation -> [MetavariableEquation] -> Enumeration (_,Instantiation)

-- The instantiation is passed downwards, so there's no need to re-combine it upwards: we just keep the head.
instantiation_from_dgraph_sol_comb :: ([UnifierDescription],Instantiation) -> ([UnifierDescription],Instantiation) -> ([UnifierDescription],Instantiation)
instantiation_from_dgraph_sol_comb _ x = x
--instantiation_from_dgraph_sol_comb (uds,inst1) ([ud],inst2) = (ud:uds,inst1)

-- We keep the last list, which corresponds to the first parameter, corresponding to the inner step.
instantiation_from_dgraph_sol_comb_helper :: (([UnifierDescription],Instantiation),[Either (Metaterm,Term) (Metaliteral,Literal)]) -> (([UnifierDescription],Instantiation),[Either (Metaterm,Term) (Metaliteral,Literal)]) -> (([UnifierDescription],Instantiation),[Either (Metaterm,Term) (Metaliteral,Literal)])
instantiation_from_dgraph_sol_comb_helper _ x = x
--instantiation_from_dgraph_sol_comb_helper (udinst1,l1) (udinst2,l2) = (instantiation_from_dgraph_sol_comb udinst1 udinst2,l1)

instantiation_from_dgraph_sol_comb_helper_maybe :: (Maybe ([UnifierDescription],Instantiation),[Either (Metaterm,Term) (Metaliteral,Literal)]) -> (Maybe ([UnifierDescription],Instantiation),[Either (Metaterm,Term) (Metaliteral,Literal)]) -> (Maybe ([UnifierDescription],Instantiation),[Either (Metaterm,Term) (Metaliteral,Literal)])
instantiation_from_dgraph_sol_comb_helper_maybe _ x = x


-- Once again, decombination should not be important.
instantiation_from_dgraph_sol_decomb :: ([UnifierDescription],Instantiation) -> (([UnifierDescription],Instantiation),([UnifierDescription],Instantiation))
instantiation_from_dgraph_sol_decomb (ud,inst) = (([],idinst),(ud,inst))

instantiation_from_dgraph_sol_decomb_helper :: (([UnifierDescription],Instantiation),[Either (Metaterm,Term) (Metaliteral,Literal)]) -> ((([UnifierDescription],Instantiation),[Either (Metaterm,Term) (Metaliteral,Literal)]),(([UnifierDescription],Instantiation),[Either (Metaterm,Term) (Metaliteral,Literal)]))
instantiation_from_dgraph_sol_decomb_helper (udinst,l) = ((r1,[]),(r2,l)) where (r1,r2) = instantiation_from_dgraph_sol_decomb udinst

instantiation_from_dgraph_sol_decomb_helper_maybe :: (Maybe ([UnifierDescription],Instantiation),[Either (Metaterm,Term) (Metaliteral,Literal)]) -> ((Maybe ([UnifierDescription],Instantiation),[Either (Metaterm,Term) (Metaliteral,Literal)]),(Maybe ([UnifierDescription],Instantiation),[Either (Metaterm,Term) (Metaliteral,Literal)]))
instantiation_from_dgraph_sol_decomb_helper_maybe (Nothing,l) = ((Nothing,[]),(Nothing,l))
instantiation_from_dgraph_sol_decomb_helper_maybe (Just udinst,l) = ((Just r1,[]),(Just r2,l)) where (r1,r2) = instantiation_from_dgraph_sol_decomb udinst


-- recursively_diagonalize_h :: (t -> Either ([r] -> Enumeration (h1,r)) (t,([r] -> Enumeration (h1,r),CombinationScheme r))) -> (t -> Enumeration (RecursiveDiagonalization h1 r,r))
-- data CombinationScheme r = Comb (r -> r -> r) (r -> (r,r))


-- In the end, we have all unifiers specified, all meta-variables instantiated, and so we can output the total solution.
-- THE FINAL SOLUTION, YES!!!
solve_unifier_constraints :: (MetaunificationHeuristic hl ht) -> ExtendedSignature -> [Metavariable] -> [Constraint] -> [Unifier] -> Enumeration (_,Maybe ([UnifierDescription],Instantiation))
solve_unifier_constraints heur sig mvs cs us = enum_maybe_filter_h is_solution_satisfiable (diagonalize_h (\fs -> instantiation_from_dgraph_sol sig fs us) fsols)
	where (rmvs,(rinst,rcs)) = all_simpl_cstr mvs (idinst,cs);
		(rg,rsol,rueqs) = build_graph_from_constraints rcs;
		fsols = enumerate_and_propagate_all heur sig (rmvs,[],(rinst,[]),(rg,rsol,rueqs))		

is_solution_satisfiable :: ([UnifierDescription],Instantiation) -> Bool
is_solution_satisfiable ([],_) = False
is_solution_satisfiable _ = True
		
-- instantiation_from_dgraph_sol :: Signature -> FullSolution -> [Unifier] -> Enumeration (_,([UnifierDescription],Instantiation))
-- diagonalize_h :: (a -> Enumeration (h2,b)) -> Enumeration (h1,a) -> Enumeration (((((h1,a),[((h1,a),Enumerator (h2,b),Int,(h2,b))],[((h1,a),Enumerator (h2,b),Int,(h2,b))]),(h1,a)),h2),b)
-- enum_filter_h :: (a -> Bool) -> Enumeration (h,a) -> Enumeration ((Int,h),a)


-- Verifying that a system of constraints is well formed as a meta-resolution output to be passed to meta-unification.
-- This includes:
--	- Verifying that the functions and predicates are in the signature.
--	- Verifying that the variables are in the base variables of the signature.
--	- Verifying that the meta-variables are in the list of meta-variables.
--	- Verifying that the unifiers are in the list of unifiers.
--	- Verifying that no unifier appears more than once in a meta-term or meta-literal.
--	- Verifying that the unifiers are in all cases in the correct order.
--	- Verifying that all constraints have the same outer-most unifier on both sides.
--	- Verifying that all constraints have at least one unifier.
--	- Verifying that all unifiers are on the outer-most part of all metaterms and metaliterals (this would not really be a requirement for the constraint to be valid, but all valid constraints
--		can be put in this form).
--	Note that several of these verifications do not hold for constraints generated within the algorithm, but we require them for the initial input for the algorithm.
data ConstraintFormError = FunNotInSig Function	|
				PredNotInSig Predicate |
				VarNotInSig Variable |
				MetavarNotInList Metavariable |
				UnifierNotInList Unifier |
				RepeatedUnifier Unifier	|
				IncorrectUnifierOrder Unifier Unifier |
				DistinctOuterUnifiers Unifier Unifier |
				NoOuterUnifier |
				InnerUnifierMt Metaterm | InnerUnifierMl Metaliteral

instance Show ConstraintFormError where
	show (FunNotInSig f) = "Function " ++ (show f) ++ " is not in the signature."
	show (PredNotInSig p) = "Predicate " ++ (show p) ++ " is not in the signature."
	show (VarNotInSig v) = "Variable " ++ (show v) ++ " is not in the set of base variables for the signature."
	show (MetavarNotInList mv) = "Meta-variable " ++ (show mv) ++ " is not in the input list of meta-variables."
	show (UnifierNotInList u) = "Unifier " ++ (show u) ++ " is not in the input list of unifiers."
	show (RepeatedUnifier u) = "Unifier " ++ (show u)  ++ " appears more than once."
	show (IncorrectUnifierOrder u1 u2) = "Unifiers " ++ (show u1) ++ " and " ++ (show u2) ++ " appear in the wrong order in the constraint: " ++ (show u1) ++ " should never be applied after " ++ (show u2) ++ "."
	show (DistinctOuterUnifiers u1 u2) = "The constraint has distinct outer-most unifiers on each side: " ++ (show u1) ++ " and " ++ (show u2)  ++ ". This is invalid."
	show NoOuterUnifier = "One or both of the sides of the constraint have no unifier."
	show (InnerUnifierMt mt) = "The meta-term " ++ (show mt) ++ " has unifiers inside term constructs. While this could be valid, the algorithm requires to express all constraints with all unifiers strictly out of term constructs."
	show (InnerUnifierMl ml) = "The meta-literal " ++ (show ml) ++ " has unifiers inside literal constructs. While this could be valid, the algorithm requires to express all constraints with all unifiers strictly out of literal constructs."

data ConstraintFormErrors = CFErrs Constraint [ConstraintFormError]

instance Show ConstraintFormErrors where
	show (CFErrs c errs) = "Constraint " ++ (show c) ++ ": " ++ (show_cferrs errs)

show_cferrs :: [ConstraintFormError] -> String
show_cferrs [] = "All valid.\n"
show_cferrs [err] = (show err) ++ "\n"
show_cferrs (err:errs) = "\n\n" ++ (show err) ++ "\n" ++ (show_cferrs errs)

show_all_cferrs :: [ConstraintFormErrors] -> IO ()
show_all_cferrs [] = putStr ""
show_all_cferrs (cferr:cferrs) = (putStr ((show cferr) ++ "\n")) >> (show_all_cferrs cferrs)

verify_all_unifier_constraints_wellformed :: ExtendedSignature -> [Metavariable] -> [Unifier] -> [Constraint] -> [ConstraintFormErrors]
verify_all_unifier_constraints_wellformed sig mvs us cs = map (verify_unifier_constraints_wellformed sig mvs us) cs

verify_unifier_constraints_wellformed :: ExtendedSignature -> [Metavariable] -> [Unifier] -> Constraint -> ConstraintFormErrors
verify_unifier_constraints_wellformed sig mvs us c = CFErrs c (concat [verify_funs_in_sig sig c,
								verify_preds_in_sig sig c,
								verify_vars_in_sig sig c,
								verify_mvs_in_list mvs c,
								verify_us_in_list us c,
								verify_repeated_us c,
								verify_order_us us c,
								verify_outer_us c,
								verify_us_external c])

verify_funs_in_sig :: ExtendedSignature -> Constraint -> [ConstraintFormError]
verify_funs_in_sig ((_,fs,_),_,_,_) (Tcstr mt1 mt2) = (verify_funs_in_sig_mt fs mt1) ++ (verify_funs_in_sig_mt fs mt2)
verify_funs_in_sig ((_,fs,_),_,_,_) (Lcstr ml1 ml2) = (verify_funs_in_sig_ml fs ml1) ++ (verify_funs_in_sig_ml fs ml2)

verify_funs_in_sig_mt :: [Function] -> Metaterm -> [ConstraintFormError]
verify_funs_in_sig_mt fs (MTermR _ mt) = verify_funs_in_sig_mt fs mt
verify_funs_in_sig_mt fs (MTermT t) = verify_funs_in_sig_t fs t
verify_funs_in_sig_mt fs (MTermF f mts) | elem f fs = concat (map (verify_funs_in_sig_mt fs) mts)
verify_funs_in_sig_mt fs (MTermF f mts) = (FunNotInSig f):(concat (map (verify_funs_in_sig_mt fs) mts))

verify_funs_in_sig_t :: [Function] -> Term -> [ConstraintFormError]
verify_funs_in_sig_t fs (TVar _) = []
verify_funs_in_sig_t fs (TMeta _) = []
verify_funs_in_sig_t fs (TFun f ts) | elem f fs = concat (map (verify_funs_in_sig_t fs) ts)
verify_funs_in_sig_t fs (TFun f ts) = (FunNotInSig f):(concat (map (verify_funs_in_sig_t fs) ts))

verify_funs_in_sig_ml :: [Function] -> Metaliteral -> [ConstraintFormError]
verify_funs_in_sig_ml fs (MLitR _ ml) = verify_funs_in_sig_ml fs ml
verify_funs_in_sig_ml fs (MLitL l) = verify_funs_in_sig_l fs l
verify_funs_in_sig_ml fs (MLitP p mts) = concat (map (verify_funs_in_sig_mt fs) mts)

verify_funs_in_sig_l :: [Function] -> Literal -> [ConstraintFormError]
verify_funs_in_sig_l fs (LitM _) = []
verify_funs_in_sig_l fs (Lit _ ts) = concat (map (verify_funs_in_sig_t fs) ts)

verify_preds_in_sig :: ExtendedSignature -> Constraint -> [ConstraintFormError]
verify_preds_in_sig ((ps,_,_),_,_,_) (Tcstr _ _) = []
verify_preds_in_sig ((ps,_,_),_,_,_) (Lcstr ml1 ml2) = (verify_preds_in_sig_ml ps ml1) ++ (verify_preds_in_sig_ml ps ml2)

verify_preds_in_sig_ml :: [Predicate] -> Metaliteral -> [ConstraintFormError]
verify_preds_in_sig_ml ps (MLitR _ ml) = verify_preds_in_sig_ml ps ml
verify_preds_in_sig_ml ps (MLitL l) = verify_preds_in_sig_l ps l
verify_preds_in_sig_ml ps (MLitP p _) | elem p ps = []
verify_preds_in_sig_ml ps (MLitP p _) = [PredNotInSig p]

verify_preds_in_sig_l :: [Predicate] -> Literal -> [ConstraintFormError]
verify_preds_in_sig_l ps (LitM _) = []
verify_preds_in_sig_l ps (Lit p _) | elem p ps = []
verify_preds_in_sig_l ps (Lit p _) = [PredNotInSig p]

verify_vars_in_sig :: ExtendedSignature -> Constraint -> [ConstraintFormError]
verify_vars_in_sig ((_,_,nvars),_,_,_) (Tcstr mt1 mt2) = (verify_vars_in_sig_mt nvars mt1) ++ (verify_vars_in_sig_mt nvars mt2)
verify_vars_in_sig ((_,_,nvars),_,_,_) (Lcstr ml1 ml2) = (verify_vars_in_sig_ml nvars ml1) ++ (verify_vars_in_sig_ml nvars ml2)

verify_vars_in_sig_mt :: Int -> Metaterm -> [ConstraintFormError]
verify_vars_in_sig_mt n (MTermR _ mt) = verify_vars_in_sig_mt n mt
verify_vars_in_sig_mt n (MTermT t) = verify_vars_in_sig_t n t
verify_vars_in_sig_mt n (MTermF _ mts) = concat (map (verify_vars_in_sig_mt n) mts)

verify_vars_in_sig_t :: Int -> Term -> [ConstraintFormError]
verify_vars_in_sig_t n (TVar (Var i)) | i < n = []
verify_vars_in_sig_t n (TVar (Var i)) = [VarNotInSig (Var i)]
verify_vars_in_sig_t n (TMeta _) = []
verify_vars_in_sig_t n (TFun _ ts) = concat (map (verify_vars_in_sig_t n) ts)

verify_vars_in_sig_ml :: Int -> Metaliteral -> [ConstraintFormError]
verify_vars_in_sig_ml n (MLitR _ ml) = verify_vars_in_sig_ml n ml
verify_vars_in_sig_ml n (MLitL l) = verify_vars_in_sig_l n l
verify_vars_in_sig_ml n (MLitP _ mts) = concat (map (verify_vars_in_sig_mt n) mts)

verify_vars_in_sig_l :: Int -> Literal -> [ConstraintFormError]
verify_vars_in_sig_l n (LitM _) = []
verify_vars_in_sig_l n (Lit _ ts) = concat (map (verify_vars_in_sig_t n) ts)

verify_mvs_in_list :: [Metavariable] -> Constraint -> [ConstraintFormError]
verify_mvs_in_list mvs (Tcstr mt1 mt2) = (verify_mvs_in_list_mt mvs mt1) ++ (verify_mvs_in_list_mt mvs mt2)
verify_mvs_in_list mvs (Lcstr ml1 ml2) = (verify_mvs_in_list_ml mvs ml1) ++ (verify_mvs_in_list_ml mvs ml2)

verify_mvs_in_list_mt :: [Metavariable] -> Metaterm -> [ConstraintFormError]
verify_mvs_in_list_mt mvs (MTermR _ mt) = verify_mvs_in_list_mt mvs mt
verify_mvs_in_list_mt mvs (MTermT t) = verify_mvs_in_list_t mvs t
verify_mvs_in_list_mt mvs (MTermF _ mts) = concat (map (verify_mvs_in_list_mt mvs) mts)

verify_mvs_in_list_t :: [Metavariable] -> Term -> [ConstraintFormError]
verify_mvs_in_list_t mvs (TVar _) = []
verify_mvs_in_list_t mvs (TMeta mv) | elem mv mvs = []
verify_mvs_in_list_t mvs (TMeta mv) = [MetavarNotInList mv]
verify_mvs_in_list_t mvs (TFun _ ts) = concat (map (verify_mvs_in_list_t mvs) ts)

verify_mvs_in_list_ml :: [Metavariable] -> Metaliteral -> [ConstraintFormError]
verify_mvs_in_list_ml mvs (MLitR _ ml) = verify_mvs_in_list_ml mvs ml
verify_mvs_in_list_ml mvs (MLitL l) = verify_mvs_in_list_l mvs l
verify_mvs_in_list_ml mvs (MLitP _ mts) = concat (map (verify_mvs_in_list_mt mvs) mts)

verify_mvs_in_list_l :: [Metavariable] -> Literal -> [ConstraintFormError]
verify_mvs_in_list_l mvs (LitM mv) | elem mv mvs = []
verify_mvs_in_list_l mvs (LitM mv) = [MetavarNotInList mv]
verify_mvs_in_list_l mvs (Lit _ ts) = concat (map (verify_mvs_in_list_t mvs) ts)

verify_us_in_list :: [Unifier] -> Constraint -> [ConstraintFormError]
verify_us_in_list us (Tcstr mt1 mt2) = (verify_us_in_list_mt us mt1) ++ (verify_us_in_list_mt us mt2)
verify_us_in_list us (Lcstr ml1 ml2) = (verify_us_in_list_ml us ml1) ++ (verify_us_in_list_ml us ml2)

verify_us_in_list_mt :: [Unifier] -> Metaterm -> [ConstraintFormError]
verify_us_in_list_mt us (MTermR u mt) | elem u us = verify_us_in_list_mt us mt
verify_us_in_list_mt us (MTermR u mt) = (UnifierNotInList u):(verify_us_in_list_mt us mt)
verify_us_in_list_mt us (MTermT _) = []
verify_us_in_list_mt us (MTermF _ mts) = concat (map (verify_us_in_list_mt us) mts)

verify_us_in_list_ml :: [Unifier] -> Metaliteral -> [ConstraintFormError]
verify_us_in_list_ml us (MLitR u ml) | elem u us = verify_us_in_list_ml us ml
verify_us_in_list_ml us (MLitR u ml) = (UnifierNotInList u):(verify_us_in_list_ml us ml)
verify_us_in_list_ml us (MLitL _) = []
verify_us_in_list_ml us (MLitP _ mts) = concat (map (verify_us_in_list_mt us) mts)

verify_repeated_us :: Constraint -> [ConstraintFormError]
verify_repeated_us (Tcstr mt1 mt2) = (verify_repeated_us_mt mt1) ++ (verify_repeated_us_mt mt2)
verify_repeated_us (Lcstr ml1 ml2) = (verify_repeated_us_ml ml1) ++ (verify_repeated_us_ml ml2)

verify_repeated_us_mt :: Metaterm -> [ConstraintFormError]
verify_repeated_us_mt mt = verify_repeated_us_mt_rec [] mt

verify_repeated_us_mt_rec :: [Unifier] -> Metaterm -> [ConstraintFormError]
verify_repeated_us_mt_rec pus (MTermR v mt) | elem v pus = (RepeatedUnifier v):(verify_repeated_us_mt_rec pus mt)
verify_repeated_us_mt_rec pus (MTermR v mt) = verify_repeated_us_mt_rec (v:pus) mt
verify_repeated_us_mt_rec _ (MTermT _) = []
verify_repeated_us_mt_rec _ (MTermF _ _) = []

verify_repeated_us_ml :: Metaliteral -> [ConstraintFormError]
verify_repeated_us_ml ml = verify_repeated_us_ml_rec [] ml

verify_repeated_us_ml_rec :: [Unifier] -> Metaliteral -> [ConstraintFormError]
verify_repeated_us_ml_rec pus (MLitR v ml) | elem v pus = (RepeatedUnifier v):(verify_repeated_us_ml_rec pus ml)
verify_repeated_us_ml_rec pus (MLitR v ml) = verify_repeated_us_ml_rec (v:pus) ml
verify_repeated_us_ml_rec _ (MLitL _) = []
verify_repeated_us_ml_rec _ (MLitP _ _) = []

verify_order_us :: [Unifier] -> Constraint -> [ConstraintFormError]
verify_order_us us (Tcstr mt1 mt2) = (verify_order_us_mt us mt1) ++ (verify_order_us_mt us mt2)
verify_order_us us (Lcstr ml1 ml2) = (verify_order_us_ml us ml1) ++ (verify_order_us_ml us ml2)

verify_order_us_mt :: [Unifier] -> Metaterm -> [ConstraintFormError]
verify_order_us_mt us mt = verify_order_us_mt_rec Nothing us (reverse us) mt

-- The first list is the list of valid unifiers, so that we don't output here errors having to do with incorrect unifiers.
verify_order_us_mt_rec :: Maybe Unifier -> [Unifier] -> [Unifier] -> Metaterm -> [ConstraintFormError]
verify_order_us_mt_rec _ pus (u:us) (MTermR v mt) | u == v = verify_order_us_mt_rec (Just u) pus us mt
verify_order_us_mt_rec last pus (u:us) (MTermR v mt) = verify_order_us_mt_rec last pus us (MTermR v mt)
verify_order_us_mt_rec Nothing pus [] (MTermR v mt) = [] -- This indicates an incorrect unifier, v, but not an order problem.
verify_order_us_mt_rec (Just u) pus [] (MTermR v mt) | elem v pus = [IncorrectUnifierOrder u v]
verify_order_us_mt_rec (Just u) pus [] (MTermR v mt) = [] -- This indicates an incorrect unifier, v, but not an order problem.
verify_order_us_mt_rec _ _ _ (MTermT _) = []
verify_order_us_mt_rec _ _ _ (MTermF _ _) = []

verify_order_us_ml :: [Unifier] -> Metaliteral -> [ConstraintFormError]
verify_order_us_ml us ml = verify_order_us_ml_rec Nothing us (reverse us) ml

verify_order_us_ml_rec :: Maybe Unifier -> [Unifier] -> [Unifier] -> Metaliteral -> [ConstraintFormError]
verify_order_us_ml_rec _ pus (u:us) (MLitR v ml) | u == v = verify_order_us_ml_rec (Just u) pus us ml
verify_order_us_ml_rec last pus (u:us) (MLitR v ml) = verify_order_us_ml_rec last pus us (MLitR v ml)
verify_order_us_ml_rec Nothing pus [] (MLitR v ml) = [] -- This indicates an incorrect unifier, v, but not an order problem.
verify_order_us_ml_rec (Just u) pus [] (MLitR v ml) | elem v pus = [IncorrectUnifierOrder u v]
verify_order_us_ml_rec (Just u) pus [] (MLitR v ml) = [] -- This indicates an incorrect unifier, v, but not an order problem.
verify_order_us_ml_rec _ _ _ (MLitL _) = []
verify_order_us_ml_rec _ _ _ (MLitP _ _) = []

verify_outer_us :: Constraint -> [ConstraintFormError]
verify_outer_us (Tcstr (MTermR u _) (MTermR v _)) | u == v = []
verify_outer_us (Tcstr (MTermR u _) (MTermR v _)) = [DistinctOuterUnifiers u v]
verify_outer_us (Tcstr _ _) = [NoOuterUnifier]
verify_outer_us (Lcstr (MLitR u _) (MLitR v _)) | u == v = []
verify_outer_us (Lcstr (MLitR u _) (MLitR v _)) = [DistinctOuterUnifiers u v]
verify_outer_us (Lcstr _ _) = [NoOuterUnifier]

verify_us_external :: Constraint -> [ConstraintFormError]
verify_us_external (Tcstr mt1 mt2) = (verify_us_external_mt mt1) ++ (verify_us_external_mt mt2)
verify_us_external (Lcstr ml1 ml2) = (verify_us_external_ml ml1) ++ (verify_us_external_ml ml2)

verify_us_external_mt :: Metaterm -> [ConstraintFormError]
verify_us_external_mt (MTermR _ mt) = verify_us_external_mt mt
verify_us_external_mt (MTermT _) = []
verify_us_external_mt (MTermF f mts) = if (any verify_no_us_mt mts) then [InnerUnifierMt (MTermF f mts)] else []

verify_no_us_mt :: Metaterm -> Bool
verify_no_us_mt (MTermR u mt) = True
verify_no_us_mt (MTermT _) = False
verify_no_us_mt (MTermF _ mts) = any verify_no_us_mt mts

verify_us_external_ml :: Metaliteral -> [ConstraintFormError]
verify_us_external_ml (MLitR _ ml) = verify_us_external_ml ml
verify_us_external_ml (MLitL _) = []
verify_us_external_ml (MLitP p mts) = if (any verify_no_us_mt mts) then [InnerUnifierMl (MLitP p mts)] else []


-- Heuristics for term/atom enumeration.
-- Receives the signature, the variable set on which to enumerate, a set of banned variables and an additional filter for valid variables, and returns an enumeation of the literals.
type LiteralEnumeration h = ExtendedSignature -> VariableSet -> [Variable] -> (Variable -> Bool) -> Enumeration (h,Literal)
--enumerate_lits_dependent :: (MetaunificationHeuristic hl ht) -> ExtendedSignature -> VariableSet -> [Variable] -> (Variable -> Bool) -> Enumeration (_,Literal)

-- Similarly for terms.
type TermEnumeration h = ExtendedSignature -> VariableSet -> [Variable] -> (Variable -> Bool) -> Enumeration (h,Term)
--enumerate_terms_dependent :: ExtendedSignature -> VariableSet -> [Variable] -> (Variable -> Bool) -> Enumeration (_,Term)

type MetaunificationHeuristic hl ht = (Maybe (LiteralEnumeration hl),Maybe (TermEnumeration ht))

default_metaunification_heuristic :: MetaunificationHeuristic hl ht
default_metaunification_heuristic = (Nothing,Nothing)

enumerate_lits_dependent_heur :: (MetaunificationHeuristic hl ht) -> ExtendedSignature -> VariableSet -> [Variable] -> (Variable -> Bool) -> Enumeration (_,Literal)
enumerate_lits_dependent_heur (Nothing,tenum) sig vs bans filt = enum_hleft_h (enumerate_lits_dependent (Nothing,tenum) sig vs bans filt)
enumerate_lits_dependent_heur (Just lenum,_) sig vs bans filt = enum_hright_h (lenum sig vs bans filt)

enumerate_terms_dependent_heur :: (MetaunificationHeuristic hl ht) -> ExtendedSignature -> VariableSet -> [Variable] -> (Variable -> Bool) -> Enumeration (_,Term)
enumerate_terms_dependent_heur (_,Nothing) sig vs bans filt = enum_hleft_h (enumerate_terms_dependent sig vs bans filt)
enumerate_terms_dependent_heur (_,Just tenum) sig vs bans filt = enum_hright_h (tenum sig vs bans filt)

-- To see if we run through a specific part of the code
hang_up :: t -> t
hang_up x = case (head (reverse (reverse ((Left x):(map Right [1..]))))) of {Left y -> y}

bootstrap :: t -> t
bootstrap x = x

capture_net :: t -> Bool
capture_net x = case x of {_ -> True}

capture_value :: t1 -> t2 -> t2
capture_value x y = if (capture_net x) then y else y




-- Added as not present in the library
--fromLeft :: a -> Either a b -> a
--fromLeft _ (Left x) = x
--fromLeft dflt (Right _) = dflt

--fromRight :: a -> Either b a -> a
--fromRight dflt (Left _) = dflt
--fromRight _ (Right x) = x
