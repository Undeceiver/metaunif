{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PartialTypeSignatures #-}
module Constraints where


-- Important note. Literals here actually are atoms (no negation). Bad wording...
import Data.Maybe
import qualified Data.Set as Set
import qualified Data.HashMap as Map
import qualified Data.List as List

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

data Metaliteral = MLitL Literal | MLitR Unifier Metaliteral | MLitP Predicate [Metaterm] deriving Eq
instance Show Metaliteral where
	show (MLitL l) = (show l)
	show (MLitR u ml) = (show u) ++ " " ++ (show ml)
	show (MLitP p []) = (show p) ++ "()"
	show (MLitP p (t:ts)) = (show p) ++ "(" ++ (foldl (\x -> \y -> x ++ "," ++ (show y)) (show t) ts) ++ ")"

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

type LitInstantiation = (Metavariable -> Literal)
type TermInstantiation = (Metavariable -> Term)
-- Identity instantiations
idinst_lit :: LitInstantiation
idinst_lit mv = LitM mv
idinst_term :: TermInstantiation
idinst_term mv = TMeta mv
idinst :: Instantiation
idinst = (idinst_lit, idinst_term)

type Instantiation = (LitInstantiation,TermInstantiation)

show_inst_mv :: Instantiation -> Metavariable -> String
show_inst_mv i mv | ((fst i) mv /= (LitM mv)) = (show mv) ++ " -> " ++ (show ((fst i) mv))
show_inst_mv i mv | ((snd i) mv /= (TMeta mv)) = (show mv) ++ " -> " ++ (show ((snd i) mv))
show_inst_mv i mv = (show mv) ++ " -> " ++ (show mv)

show_inst :: Instantiation -> [Metavariable] -> String
show_inst i [] = "{}"
show_inst i (x:xs) = "{" ++ (foldl (\s -> \mv -> s ++ "," ++ (show_inst_mv i mv)) (show_inst_mv i x) xs) ++ "}"

apply_inst_term :: Instantiation -> Term -> Term
apply_inst_term i (TVar v) = TVar v
apply_inst_term i (TMeta mv) = (snd i) mv
apply_inst_term i (TFun f l) = TFun f (map (apply_inst_term i) l)

apply_inst_lit :: Instantiation -> Literal -> Literal
apply_inst_lit i (LitM mv) = (fst i) mv
apply_inst_lit i (Lit p l) = Lit p (map (apply_inst_term i) l)

apply_inst_mterm :: Instantiation -> Metaterm -> Metaterm
apply_inst_mterm i (MTermT t) = MTermT (apply_inst_term i t)
apply_inst_mterm i (MTermR u mt) = MTermR u (apply_inst_mterm i mt)
apply_inst_mterm i (MTermF f l) = MTermF f (map (apply_inst_mterm i) l)

apply_inst_mlit :: Instantiation -> Metaliteral -> Metaliteral
apply_inst_mlit i (MLitL l) = MLitL (apply_inst_lit i l)
apply_inst_mlit i (MLitR u ml) = MLitR u (apply_inst_mlit i ml)
apply_inst_mlit i (MLitP p l) = MLitP p (map (apply_inst_mterm i) l)

-- As usual, read from right to left. The first instantiation applied is the second parameter.
compose_inst :: Instantiation -> Instantiation -> Instantiation
compose_inst i j = (\mv -> apply_inst_lit i ((fst j) mv), \mv -> apply_inst_term i ((snd j) mv))

compose_insts :: [Instantiation] -> Instantiation
compose_insts l = foldr compose_inst (idinst_lit,idinst_term) l

build_inst :: Metavariable -> Either Term Literal -> Instantiation
build_inst mv (Left t) = (idinst_lit,(\mx -> if (mx == mv) then t else (TMeta mx)))
build_inst mv (Right l) = (\mx -> if (mx == mv) then l else (LitM mx),idinst_term)


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
									((\mv -> case mv of {Metavar n | n == m -> Lit p (map (\mv -> TMeta mv) new_mvs); otherwise -> idinst_lit mv}),
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
all_simpl_cstr_step mvs i ((True,c):cs) = case (simpl_cstr mvs c) of (bool, total_mvs, (j, new_cs)) -> (True,total_mvs, compose_inst j i, (map (\bc -> case bc of (b,c) -> (b,(simpl_sides_cstr (apply_inst_cstr j c)))) cs) ++ (map (\c -> (bool,simpl_sides_cstr c)) new_cs))
all_simpl_cstr_step mvs i ((False,c):cs) = case (all_simpl_cstr_step mvs i cs) of (r,rmvs,ri,rcs) -> (r,rmvs, ri, (False,c):rcs)



-- Dependency graphs

-- This function is purposely not applied when meta-variables are present, raising an error.
type Substitution = (Variable -> Term)
apply_subst :: Substitution -> Term -> Term
apply_subst s (TVar v) = s v
apply_subst s (TFun f l) = TFun f (map (apply_subst s) l)

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

data UnifierValue = UV Variable Term
instance Show UnifierValue where
	show (UV v t) = (show v) ++ " -> " ++ (show t)

type UnifierDescription = [UnifierValue]

-- Receives a set of variables for the substitution, the canonical new variables for those, and a set of unifier values,
-- and returns a substitution.
obtain_substitution :: [Variable] -> (Variable -> Variable) -> UnifierDescription -> Substitution
-- By default, use new variables.
obtain_substitution l m [] = (\v -> (TVar (m v)))
obtain_substitution l m ((UV v1 t):uvs) = (\v2 -> if v2 == v1  then t else obtain_substitution l m uvs v2)

data Dependent = DVar Variable | DMetaT Metavariable | DMetaL Metavariable | DRec Unifier Dependent deriving Eq
metaterm_from_depnode :: Dependent -> Metaterm
metaterm_from_depnode (DVar x) = (MTermT (TVar x))
metaterm_from_depnode (DMetaT x) = (MTermT (TMeta x))
metaterm_from_depnode (DRec u n) = (MTermR u (metaterm_from_depnode n))

metalit_from_depnode :: Dependent -> Metaliteral
-- Purposely not defined for variables.
metalit_from_depnode (DMetaL x) = (MLitL (LitM x))
metalit_from_depnode (DRec u n) = (MLitR u (metalit_from_depnode n))

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
	show n = show (metaterm_from_depnode n)
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

-- Purposely not defined when it does not make sense
apply_thdep :: HorizontalDependency -> [Term] -> Term
apply_thdep (THDep (FApp f ins)) ts = TFun f res where (res,_) = apply_thdep_helper ins ts

-- To be able to do it recursively, we output the list of remaining terms. In the outer-most call, this must be an empty list. In any case, there must be at least enough terms in the list
-- to keep going.
-- The first list is the actual result, and the second is the remaining unused terms.
apply_thdep_helper :: [TermDependencyInput] -> [Term] -> ([Term],[Term])
apply_thdep_helper [] [] = ([],[])
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
						"\tDepends on: \n" ++ (concat (map (\e -> "\t\tHorizontal[" ++
										(concat (map (\n -> 
												(show n) ++
												",")
											(get_hsources e))) ++
										"]\n")
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
						"\tThings that depend on it: \n" ++ (concat (map (\e -> "\t\tHorizontal[" ++
													(show (get_htarget e)) ++
													"]\n")
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
find_node (DGraph ns _ _) d = case (Map.lookup (unconnected_node d) ns) of Just x -> x

-- Applies a function to a node in the graph.
apply_to_node :: Dependent -> (DependencyNode -> DependencyNode) -> (DependencyGraph -> DependencyGraph)
apply_to_node d f (DGraph ns cs dag) = DGraph (rset_replace n fn ns) cs dag where n = find_node (DGraph ns cs dag) d; fn = f n

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

add_eqdep :: DependencyGraph -> Dependent -> Dependent -> DependencyGraph
-- Each dependent must already be in exactly one dependency class. Find them, and merge them.
-- To avoid doing too much equality comparation, we just find first one, then the other, then add the new one.
add_eqdep (DGraph ns cs dag) d1 d2 = DGraph ns (fst sol) (maybe_replace_node (snd sol) dag) where sol = add_eqdep_1 cs d1 d2


-- Until here.

list_replace :: Eq b => b -> b -> [b] -> [b]
list_replace a b = map (\x -> if (a == x) then b else x)

remove_node_hvdeps :: DependencyGraph -> Dependent -> DependencyGraph
remove_node_hvdeps g d = foldl (\h -> \dep -> apply_to_node (get_vsource dep) (del_outgoing_vdep dep) h) (foldl (\h -> \dep -> apply_to_node (get_vtarget dep) (del_incoming_vdep dep) h) (foldl (\h -> \dep -> foldl (\i -> \t -> apply_to_node t (del_outgoing_hdep dep) i) h (get_hsources dep)) (foldl (\h -> \dep -> apply_to_node (get_htarget dep) (del_incoming_hdep dep) h) g (get_outgoing_hdeps n)) (get_incoming_hdeps n)) (get_outgoing_vdeps n)) (get_incoming_vdeps n) where n = find_node g d

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
-- We purposely do not consider the case when it is not in any equivalence class. This should not happen, and we want to raise an error in such case.


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
data DependencyConstraintSide = DDep Dependent | DFun [Dependent] TermHorizontalDependency

build_dependency_side_term :: Metaterm -> DependencyConstraintSide
build_dependency_side_term (MTermT (TVar v)) = DDep (DVar v)
build_dependency_side_term (MTermT (TMeta mv)) = DDep (DMetaT mv)
build_dependency_side_term (MTermF f ts) = DFun (concat deps) (\sts -> TFun f (concat_functions funs lengths sts))
								where recs = map build_dependency_side_term ts;
									deps = map (\s -> case s of {DDep x -> [x]; DFun xs _ -> xs}) recs; 
									funs = map (\s -> case s of {DDep _ -> TInDependent; DFun _ sf -> sf}) recs;
									lengths = map length deps
build_dependency_side_term (MTermR u mt) = case (build_dependency_side_term mt) of DDep d -> DDep (DRec u d) -- If it is a function, something's not right.

build_dependency_side_lit :: Metaliteral -> DependencyConstraintSide
build_dependency_side_lit (MLitL (LitM mv)) = DDep (DMetaL mv)
build_dependency_side_lit (MLitR u ml) = case (build_dependency_side_lit ml) of DDep d -> DDep (DRec u d) -- If it is a predicate, something's not right.

-- Apart from all the assumptions above, remember that they need to have the outer-most unifier. This unifier is not taken into consideration in the dependency, as it is the unifier at which level
-- the dependency is horizontal. We do this by extracting the inner meta-literals/terms with a function. However, if the term is a function, the unifiers have been pushed inwards. We solve this through
-- recursive calls
extract_inner_literal :: Metaliteral -> Metaliteral
extract_inner_literal (MLitR _ ml) = ml

extract_inner_term :: Metaterm -> Metaterm
extract_inner_term (MTermR _ mt) = mt
extract_inner_term (MTermF f mts) = (MTermF f (map extract_inner_term mts))

extract_unifier_literal :: Metaliteral -> Unifier
extract_unifier_literal (MLitR u _) = u

extract_unifier_term :: Metaterm -> Maybe Unifier
extract_unifier_term (MTermR u _) = Just u
extract_unifier_term (MTermF _ _) = Nothing

extract_unifier_constraint :: Constraint -> Unifier
extract_unifier_constraint (Lcstr ml1 _) = extract_unifier_literal ml1
extract_unifier_constraint (Tcstr mt1 mt2) | isJust res = case res of {Just x -> x} where res = extract_unifier_term mt1
extract_unifier_constraint (Tcstr _ mt2) = case (extract_unifier_term mt2) of Just x -> x

add_unifier_dependent :: Unifier -> Dependent -> Dependent
add_unifier_dependent u d = DRec u d

-- Two (possible) results: A dependency from left to right, and a dependency from right to left.
build_dependency_constraint :: Constraint -> (Maybe (([Dependent],Dependent),HorizontalDependency),Maybe (([Dependent],Dependent),HorizontalDependency))
build_dependency_constraint Unsatisfiable = (Nothing, Nothing)
-- Because literals are always relations between two meta-variables, we know that the dependency is always going to be the identity.
--build_dependency_constraint (Lcstr ml1 ml2) = (Just (([dep1],dep2),LHDep (\x -> x)),Just (([dep2],dep1),LHDep (\x -> x))) 
--							where u = extract_unifier_constraint (Lcstr ml1 ml2); s1 = build_dependency_side_lit (extract_inner_literal ml1); s2 = build_dependency_side_lit (extract_inner_literal ml2); dep1 = add_unifier_dependent u (case s1 of {DDep dep -> dep}); dep2 = add_unifier_dependent u (case s2 of {DDep dep -> dep})
build_dependency_constraint (Lcstr ml1 ml2) = (Nothing, Nothing)
build_dependency_constraint (Tcstr mt1 mt2) = case s1 of
						{
							DDep dep1 -> case s2 of
							{
								-- Two dependents. Build a symmetric dependency with the identity (first and only term).
								--DDep dep2 -> (Just (([add_unifier_dependent u dep1],add_unifier_dependent u dep2),THDep (\ts -> (head ts))),Just (([add_unifier_dependent u dep2],add_unifier_dependent u dep1),THDep (\ts -> (head ts))));
								-- Two dependents. This is an equivalence class. Deal with this somewhere else.
								DDep dep2 -> (Nothing,Nothing);
								-- A dependent and a function. A true dependency. Left depends on right.
								DFun dep2s f -> (Nothing,Just ((map (add_unifier_dependent u) dep2s,add_unifier_dependent u dep1),(THDep f)))
							};
							DFun dep1s f -> case s2 of
							{
								-- A dependent and a function. A true dependency. Left depends on right.
								DDep dep2 -> (Just ((map (add_unifier_dependent u) dep1s,add_unifier_dependent u dep2),(THDep f)),Nothing)
								-- It should not be possible that there is two functions, this means simplification is wrong. If this happens, forget about it.
							}
						}						
						where u = extract_unifier_constraint (Tcstr mt1 mt2); s1 = build_dependency_side_term (extract_inner_term mt1); s2 = build_dependency_side_term (extract_inner_term mt2)

apply_dependency_constraint_helper :: DependencyGraph -> Maybe (([Dependent],Dependent),HorizontalDependency) -> DependencyGraph
apply_dependency_constraint_helper g Nothing = g
apply_dependency_constraint_helper g (Just ((ss,t),dep)) = add_hdep (foldl add_node (add_node g t) ss) dep ss t 

apply_dependency_constraint :: DependencyGraph -> Constraint -> DependencyGraph
apply_dependency_constraint g c = apply_dependency_constraint_helper (apply_dependency_constraint_helper g ltr) rtl where cres = build_dependency_constraint c; ltr = fst cres; rtl = snd cres

-- Build equivalence classes.
-- If the constraint is an equivalence, updates the equivalence classes. Otherwise, does nothing.
update_equivalence_classes :: DependencyGraph -> Constraint -> DependencyGraph
-- Because literals are always relations between two meta-variables, we know that the dependency is always going to be the identity.
update_equivalence_classes g Unsatisfiable = g
update_equivalence_classes g (Lcstr ml1 ml2) = add_eqdep g dep1 dep2 
							where u = extract_unifier_constraint (Lcstr ml1 ml2); s1 = build_dependency_side_lit (extract_inner_literal ml1); s2 = build_dependency_side_lit (extract_inner_literal ml2); dep1 = add_unifier_dependent u (case s1 of {DDep dep -> dep}); dep2 = add_unifier_dependent u (case s2 of {DDep dep -> dep})
-- If they are terms, it is going to be an equivalence if they are both dependents.
update_equivalence_classes g (Tcstr mt1 mt2) = case s1 of
						{
							DDep dep1 -> case s2 of
							{
								DDep dep2 -> update_equivalence_classes_helper g (add_unifier_dependent u dep1) (add_unifier_dependent u dep2);
								DFun _ _ -> g
							};
							DFun _ _ -> g
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

calculate_vertical_dependencies_rec :: DependencyGraph -> [DependencyNode] -> DependencyGraph
calculate_vertical_dependencies_rec g [] = g
calculate_vertical_dependencies_rec g (n:ns) = calculate_vertical_dependencies_rec rg rns where step = calculate_vertical_dependencies_step g (n:ns); rg = case step of {(x,_) -> x}; rns = case step of {(_,x) -> x}


update_graph_with_constraint :: DependencyGraph -> Constraint -> DependencyGraph
update_graph_with_constraint g c = calculate_vertical_dependencies (update_equivalence_classes (apply_dependency_constraint g c) c)

-- A bit of efficiency. We only calculate the vertical dependencies once.
update_graph_with_constraints :: DependencyGraph -> [Constraint] -> DependencyGraph
update_graph_with_constraints g cs = calculate_vertical_dependencies (foldl update_equivalence_classes (foldl apply_dependency_constraint g cs) cs)

build_graph_from_constraints :: [Constraint] -> DependencyGraph
build_graph_from_constraints cs = update_graph_with_constraints empty_graph cs

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
-- Also purposely not defined when the substitution is impossible (i.e. if u f(x1,x2) = x3 or u f(x1,x2) = g(x3,x4). This should not happen, and we want to have an error if it does.)
simpl_dep_term :: Term -> Term -> UnifierDescription
simpl_dep_term (TVar v1) t = [UV v1 t]
simpl_dep_term (TFun f1 t1s) (TFun f2 t2s) | f1 == f2 = concat (map (\pair -> simpl_dep_term (fst pair) (snd pair)) (zip t1s t2s))

simpl_dep_lit :: Literal -> Literal -> UnifierDescription
simpl_dep_lit (Lit p t1s) (Lit q t2s) | p == q = concat (map (\pair -> simpl_dep_term (fst pair) (snd pair)) (zip t1s t2s))


-- Inverting a unifier
-- We assume that the unifier description has already been completed (so that non-described variables go to their default correspondents).
invert_unifier_term :: UnifierDescription -> Term -> [Term]
invert_unifier_term ud (TVar v) = invert_unifier_variable ud v
invert_unifier_term ud (TFun f ts) = invert_unifier_function ud f ts
-- Meta-variable should never appear, we purposely leave this case unspecified.

invert_unifier_variable :: UnifierDescription -> Variable -> [Term]
invert_unifier_variable [] _ = []
-- A variable that leads to the same variable, that's what we're looking for.
invert_unifier_variable ((UV v1 (TVar v2)):ud) v3 | v2 == v3 = ((TVar v1):(invert_unifier_variable ud v3))
-- A variable leading to another variable, not good.
invert_unifier_variable ((UV v1 (TVar v2)):ud) v3 | v2 /= v3 = invert_unifier_variable ud v3
-- A variable leading to something which is not a variable, not good.
invert_unifier_variable ((UV v1 _):ud) v3 = invert_unifier_variable ud v3

invert_unifier_function :: UnifierDescription -> Function -> [Term] -> [Term]
invert_unifier_function ud f ts = (invert_unifier_function_direct ud f ts) ++ (invert_unifier_function_rec ud f ts)

-- A variable that directly generates the given term.
invert_unifier_function_direct :: UnifierDescription -> Function -> [Term] -> [Term]
invert_unifier_function_direct [] _ _ = []
-- A variable that leads to the same function with exactly the same terms, that's what we're looking for.
invert_unifier_function_direct ((UV v1 (TFun f1 t1s)):ud) f2 t2s | (f1 == f2) && (t1s == t2s) = ((TVar v1):(invert_unifier_function_direct ud f2 t2s))
-- A variable that leads to a different function or different terms, not good.
invert_unifier_function_direct ((UV v1 (TFun f1 t1s)):ud) f2 t2s | not ((f1 == f2) && (t1s == t2s)) = invert_unifier_function_direct ud f2 t2s
-- A variable that leads to something which is not a function, not good.
invert_unifier_function_direct ((UV v1 _):ud) f ts = invert_unifier_function_direct ud f ts

-- If we already had a function, where each subterm was sent to the new corresponding term, then that is an inverse. Gather all combinations.
invert_unifier_function_rec :: UnifierDescription -> Function -> [Term] -> [Term]
invert_unifier_function_rec ud f ts = map (\t2s -> TFun f t2s) (combinations (map (invert_unifier_term ud) ts))

-- It needs to be the predicate with inverse subterms
invert_unifier_literal :: UnifierDescription -> Literal -> [Literal]
invert_unifier_literal ud (Lit p ts) = map (\t2s -> Lit p t2s) (combinations (map (invert_unifier_term ud) ts))

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


-- Removes nodes for which we have a solution from the graph, and such that all elements that vertically depend on it have a solution.
clean_dep_graph :: PartiallySolvedDGraph -> PartiallySolvedDGraph
clean_dep_graph (g,sol,ueqs) = (remove_nounif sol ueqs (clean_dep_graph_helper sol ueqs g (map fst sol)),sol,ueqs)

clean_dep_graph_helper :: DependencyGraphSolution -> [UnifierEquation] -> DependencyGraph -> [Dependent] -> DependencyGraph
clean_dep_graph_helper sol ueqs g [] = g
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

is_solved :: DependencyGraphSolution -> Dependent -> Bool
is_solved sol (DVar _) = True
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


-- Returns Nothing if the reduction shows unsatisfiabilities.
--reduce_to_tree :: DependencyGraph -> Maybe DependencyGraph

-- Given a dependent
--reduce_to_tree_back :: 


set_solution :: FullSolution -> (Dependent,Either Term Literal) -> FullSolution
set_solution (mvs,eqs,(inst,cs),(g,sol,ueqs)) (d,v) | (sol_from_list_filter sol (d,v)) = (mvs,eqs,(inst,cs),(g,((d,v):sol),ueqs))
set_solution fs _ = fs

set_all_solutions :: FullSolution -> [(Dependent,Either Term Literal)] -> FullSolution
set_all_solutions fs dvs = foldl set_solution fs dvs

-- Updates the graph as long as there is something to update that is certain (i.e. no search).
-- We have two lists, the ones that we did not consider even for horizontal updates and those that are pending updating through vertical updates.
update_graph_all :: FullSolution -> [(Dependent, Either Term Literal)] -> [(Dependent, Either Term Literal)] -> FullSolution
-- If there are horizontal updates to perform, perform them and call recursively. Otherwise, if there are vertical updates to perform, perform them and call recursively.
update_graph_all fs [] [] = fs
--update_graph_all fs [] (dv:dvs) | is_node (get_graph fs) (fst dv) = update_graph_all rs rl dvs where (rs,rl) = do_one_update_to_graph update_graph_from_value_vdep (fs,[]) dv
--update_graph_all fs [] (dv:dvs) = update_graph_all rs rl dvs where (rs,rl) = do_one_update_to_graph update_graph_from_value_vdep (fs,[]) dv
--update_graph_all fs [] (dv:dvs) = do_one_update_to_graph update_graph_from_value_vdep (rs,rl) dv where (rs,rl) = update_graph_all fs [] dvs
update_graph_all fs [] (dv:dvs) = update_graph_all rrs rl dvs where (rs,rl) = do_one_update_to_graph update_graph_from_value_vdep fs dv; rrs = simplify_ueqs_fs rs
--update_graph_all fs [] (dv:dvs) = update_graph_all fs [] dvs
--update_graph_all fs (dh:dhs) dvs | is_node (get_graph fs) (fst dh) = update_graph_all rs (dhs ++ rl) (dh:dvs) where (rs,rl) = do_one_update_to_graph update_graph_from_value_hdep_full (fs,dhs) dh
--update_graph_all fs (dh:dhs) dvs s = update_graph_all rrs rrl [] where (rs,rl) = update_graph_all fs dhs dvs; (rrs,rrl) = do_one_update_to_graph update_graph_from_value_hdep_full (rs,rl) dh
update_graph_all fs (dh:dhs) dvs = update_graph_all rs (dhs ++ rl) (dh:dvs) where (rs,rl) = do_one_update_to_graph update_graph_from_value_hdep_full fs dh
--update_graph_all fs (dh:dhs) dvs = update_graph_all fs dhs dvs

--do_one_update_to_graph :: (FullSolution -> t -> (FullSolution,[Dependent])) -> (FullSolution,[(Dependent,Either Term Literal)]) -> t -> (FullSolution,[(Dependent,Either Term Literal)])
--do_one_update_to_graph f ((mvs,(inst,cs),(g,sol)),l) x = ((nmvs,usol,(fg,l ++ new)),new) where ((nmvs,usol,(fg,newsol)),pos) = f (mvs,(inst,cs),(g,sol)) x; new = maybe_sol_from_list (fg,newsol) (all_eq fg pos)

do_one_update_to_graph :: (FullSolution -> t -> (FullSolution,[Dependent])) -> FullSolution -> t -> (FullSolution,[(Dependent,Either Term Literal)])
do_one_update_to_graph f (mvs,eqs,(inst,cs),(g,sol,ueqs)) x = ((set_all_solutions (nmvs,neqs,usol,(fg,sol,nueqs)) new),(filter (sol_from_list_filter sol) new)) where ((nmvs,neqs,usol,(fg,newsol,nueqs)),pos) = f (mvs,eqs,(inst,cs),(g,sol,ueqs)) x; new = maybe_sol_from_list (fg,newsol,nueqs) (all_eq fg pos)

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
maybe_sol_from_graph_hdep (g,sol,ueqs) (HDEdge (THDep f) [] _) = Just (Left (f []))
maybe_sol_from_graph_hdep (g,sol,ueqs) (HDEdge (LTHDep f) [] _) = Just (Right (f []))
-- For literals, give a dummy argument.
maybe_sol_from_graph_hdep (g,sol,ueqs) (HDEdge (LHDep f) [] _) = Just (Right (f (LitM (Metavar 1))))
-- In any other case, we still can't solve it.
maybe_sol_from_graph_hdep _ _ = Nothing

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

generate_unif_eqs_from_value_hdep :: Either Term Literal -> HDependencyEdge -> UnifierEquation
generate_unif_eqs_from_value_hdep (Left t) (HDEdge (THDep f) ss _) = TUEq (lift_thdep (THDep f) ss) t
generate_unif_eqs_from_value_hdep (Right l) (HDEdge (LTHDep f) ss _) = LUEq (lift_lthdep (LTHDep f) ss) l
generate_unif_eqs_from_value_hdep (Right l) (HDEdge (LHDep f) s _) = LUEq (lift_lhdep (LHDep f) (head s)) l

update_graph_from_value_hdep :: PartiallySolvedDGraph -> (Dependent,Either Term Literal) -> (DependencyGraph,[Dependent])
-- Just update all horizontal dependencies going out of the node with the value.
update_graph_from_value_hdep (g,sol,ueqs) (d,v) = ((foldl (\gg -> \sdep -> (update_hdep (del_hdep_from_source gg d sdep) sdep (update_hdep_from_value d v sdep))) g deps),(map get_htarget deps)) where deps = (get_outgoing_hdeps (find_node g d))

-- Purposely not defined for values that don't make sense.
update_hdep_from_value :: Dependent -> Either Term Literal -> HDependencyEdge -> HDependencyEdge
update_hdep_from_value d (Left vt) (HDEdge (THDep f) ss t) = HDEdge (THDep ((fst partial) f vt)) (snd partial) t where partial = update_hdep_f_from_value d ss 
update_hdep_from_value d (Left vt) (HDEdge (LTHDep f) ss t) = HDEdge (LTHDep ((fst partial) f vt)) (snd partial) t where partial = update_hdep_f_from_value d ss
update_hdep_from_value d (Right vl) (HDEdge (LHDep f) (s:[]) t) | d == s = HDEdge (LHDep (\x -> vl)) [] t

-- This is horrible. I hate it. What one does for efficiency. Given a dependent and a list, we traverse it. Once we find it, we remove it, partially evaluate the function and return the resulting list and the resulting function. However, in order to do this efficiently, what we do instead is that we traverse the list, looking for the dependent. Once we find it, we return the list without it, AND a function that, given another function, partially evaluates it at that position.
update_hdep_f_from_value :: Dependent -> [Dependent] -> (([a] -> b) -> (a -> [a] -> b),[Dependent])
-- If the next source is the dependent, update it.
update_hdep_f_from_value d (s:ss) | d == s = ((\f -> \vt -> \ts -> partial_apply_list f vt ts),ss)
-- If it is not this one, keep it and recurse.
update_hdep_f_from_value d (s:ss) = ((\f -> \vt -> \ts -> (fst rec) (partial_apply_list f (case ts of (t:tts) -> t)) vt (case ts of (t:tts) -> tts)),(s:(snd rec))) where rec = update_hdep_f_from_value d ss

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
update_graph_from_value_vdep_rec (mvs,eqs,(inst,cs),(g,sol,ueqs)) (d,v) = (rmvs,eqs,(rinst,[]),(rrg,sol,ueqs)) where (rmvs,(rinst,rcs)) = recalculate_constraints_from_vdep_out_rec mvs (inst,cs) g d v; rg = remove_nodes_vdep_rec g d; rrg = update_graph_with_constraints rg rcs; rrueqs = map (update_ueq_from_vdep (d,v)) ueqs

update_ueq_from_vdep :: (Dependent,Either Metaterm Metaliteral) -> UnifierEquation -> UnifierEquation
-- We only replace within the outermost unifier.
update_ueq_from_vdep (d,(Left mtv)) (TUEq (MTermR u mt) t) = TUEq (MTermR u (replace_mterm_mterm (all_simpl_mterm (metaterm_from_depnode d)) mtv mt)) t
update_ueq_from_vdep (d,(Left mtv)) (LUEq (MLitR u ml) l) = LUEq (MLitR u (replace_mterm_mlit (all_simpl_mterm (metaterm_from_depnode d)) mtv ml)) l
update_ueq_from_vdep (d,(Right mlv)) (LUEq (MLitR u ml) l) = LUEq (MLitR u (replace_mlit_mlit (all_simpl_mlit (metalit_from_depnode d)) mlv ml)) l

-- We remove the nodes, and add them unconnected. We never really remove nodes from the graph, but we know which nodes we have solved and which we have not.
remove_nodes_vdep_rec :: DependencyGraph -> Dependent -> DependencyGraph
remove_nodes_vdep_rec g d = add_node (remove_node (foldl (\h -> \vdep -> remove_nodes_vdep_rec h (get_vtarget vdep)) g (get_outgoing_vdeps (find_node g d))) d) d

propagate_mtl_through_vdep :: VDependencyEdge -> Either Metaterm Metaliteral -> Either Metaterm Metaliteral
propagate_mtl_through_vdep (VDEdge _ s t) (Left mt) = Left (replace_mterm_mterm (metaterm_from_depnode s) mt (metaterm_from_depnode t))
propagate_mtl_through_vdep (VDEdge _ s t) (Right ml) = Right (replace_mlit_mlit (metalit_from_depnode s) ml (metalit_from_depnode t))
--propagate_mtl_through_vdep (VDEdge (TVDep f) s t) (Left mt) = Left (f mt)
--propagate_mtl_through_vdep (VDEdge (LVDep f) s t) (Right ml) = Right (f ml)

--update_graph_from_value_vdep_step :: FullSolution -> (Dependent,Either Metaterm Metaliteral) -> FullSolution
--update_graph_from_value_vdep_step (mvs,(inst,cs),(g,sol)) (d,v) = (rmvs,(rinst,[]),(rg,sol)) where n = find_node g d; (rmvs,(rinst,rcs)) = foldl (\mvusol -> \vdep -> recalculate_constraints_from_vdep (fst mvusol) (snd mvusol) g vdep v) (mvs,(inst,cs)) (get_outgoing_vdeps n); rg = update_graph_with_constraints g rcs

recalculate_constraints_from_vdep_rec :: [Metavariable] -> UnifSolution -> DependencyGraph -> VDependencyEdge -> Either Metaterm Metaliteral -> ([Metavariable],UnifSolution)
recalculate_constraints_from_vdep_rec mvs (inst,cs) g (VDEdge dep s t) v = recalculate_constraints_from_vdep rmvs (rinst,rcs) g (VDEdge dep s t) v where n = find_node g t; (rmvs,(rinst,rcs)) = recalculate_constraints_from_vdep_out_rec mvs (inst,cs) g t (propagate_mtl_through_vdep (VDEdge dep s t) v)

recalculate_constraints_from_vdep_out_rec :: [Metavariable] -> UnifSolution -> DependencyGraph -> Dependent -> Either Metaterm Metaliteral -> ([Metavariable],UnifSolution)
recalculate_constraints_from_vdep_out_rec mvs (inst,cs) g d v = foldl (\mvusol -> \vdep -> recalculate_constraints_from_vdep_rec (fst mvusol) (snd mvusol) g vdep v) (mvs,(inst,cs)) (get_outgoing_vdeps (find_node g d))

recalculate_constraints_from_vdep :: [Metavariable] -> UnifSolution -> DependencyGraph -> VDependencyEdge -> Either Metaterm Metaliteral -> ([Metavariable],UnifSolution)
-- Take all horizontal dependencies on which the target of the vertical dependency is implied, and combine the solutions.
recalculate_constraints_from_vdep mvs (inst,cs) g (VDEdge _ s t) (Left mt) = recalculate_constraints_eqdep mvs1 (inst1,cs1) (Left (all_simpl_mterm (metaterm_from_depnode s))) (Left mt) g [t] where n = find_node g t; (mvs1,(inst1,cs1)) = recalculate_constraints_hdep mvs (inst,cs) (Left (all_simpl_mterm (metaterm_from_depnode s))) (Left mt) ((get_outgoing_hdeps n) ++ (get_incoming_hdeps n)) 
recalculate_constraints_from_vdep mvs (inst,cs) g (VDEdge _ s t) (Right ml) = recalculate_constraints_eqdep mvs1 (inst1,cs1) (Right (all_simpl_mlit (metalit_from_depnode s))) (Right ml) g [t] where n = find_node g t; (mvs1,(inst1,cs1)) = recalculate_constraints_hdep mvs (inst,cs) (Right (all_simpl_mlit (metalit_from_depnode s))) (Right ml) ((get_outgoing_hdeps n) ++ (get_incoming_hdeps n)) 

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

lift_thdep :: HorizontalDependency -> [Dependent] -> Metaterm
-- This is a bit ugly, with better formalization would not be necessary, but no time now.
-- We use negatively indexed variables as variables that we assume do not happen in normal terms, as a way to witness what the dependency does to them, and then replace them with the dependents.
lift_thdep (THDep f) ds = replace_witness_variables_thdep mt reps where t = f (map TVar (witness_variables ds)); mt = (all_simpl_mterm (MTermT t)); reps = map metaterm_from_depnode ds

lift_lthdep :: HorizontalDependency -> [Dependent] -> Metaliteral
lift_lthdep (LTHDep f) ds = replace_witness_variables_lthdep ml reps where l = f (map TVar (witness_variables ds)); ml = (all_simpl_mlit (MLitL l)); reps = map metaterm_from_depnode ds

lift_lhdep :: HorizontalDependency -> Dependent -> Metaliteral
lift_lhdep (LHDep f) d = replace_witness_variable_lhdep ml rep where l = f (LitM witness_metavar); ml = (all_simpl_mlit (MLitL l)); rep = metalit_from_depnode d

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
-- When Nothing is returned, this means that all root classes have hidden dependents, but none of them has meta-variables. This is the worst case, in which we have to enumerate over some random meta-variable.
find_best_root_class :: Int -> FullSolution -> Maybe (Dependent,Maybe Dependent)
-- There should always be at least one where all are single.
find_best_root_class n (mvs,eqs,(inst,cs),(g,sol,ueqs)) = case res of {Just (rrep,[],[]) -> Just (rrep,Nothing); Just (rrep,(h:hs),[]) -> Nothing; Just (rrep,hs,(m:ms)) -> Just (rrep,Just m)} where res = find_best_root_class_list n (mvs,eqs,(inst,cs),(g,sol,ueqs)) (map (find_eqdep g) (roots g))

-- Returns the representer, how many possibly hidden dependents it has and how many meta-variable dependents it has.
find_best_root_class_list :: Int -> FullSolution -> [EqDependencyClass] -> Maybe (Dependent,[Dependent],[Dependent])
-- We assume that it has at least one class, and at least one which does not contain non-single dependents
find_best_root_class_list n fs (c:[]) | has_unifier_c c && (not (has_multiple_unifs c)) = Just (eqdep_rep c,(has_hidden_deps n fs c),(has_metavars c))
find_best_root_class_list n fs (c:[]) = Nothing
-- We try to avoid classes with hidden dependents but no meta-variables: This forces us to choose a meta-variable to enumerate over from the whole graph, not just the roots.
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

has_metavars :: EqDependencyClass -> [Dependent]
has_metavars c = filter is_dependent_metavar (eqdep_elems c)

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




-------------------------------------------------
-- NOTE
--	All of this is very generic and beautiful, but I have run out of time and have not managed to enumerate terms using enumerations.
-- But it is not necessary really, as terms up to a certain depth are finite.
-- We can just do iterative deepening over lists, with only enumeration over depths. First ALL terms of depth 0, then ALL terms of depth 1, then ALL terms of depth 2, etc.
-------------------------------------------------
enumerate_lits_dependent :: Signature -> VariableSet -> [Variable] -> Enumeration (_,Literal)
enumerate_lits_dependent (ps,fs,n) vs bans = diagonalize_h (\pred -> apply_enum_1_h (\terms -> Lit pred terms) (enumerate_lists (enumerate_terms_dependent (ps,fs,n) vs bans) (pred_arity pred))) (enum_from_list ps)

enumerate_terms_dependent :: Signature -> VariableSet -> [Variable] -> Enumeration (((Int,[Term]),[Term]),Term)
enumerate_terms_dependent sig vs bans = Enum (((0,zeroes),tzeroes),f) (\idx -> \prev -> Just (case prev of {(((d,l),ts),t) -> enumerate_terms_dependent_helper sig d l ts t})) where zeroes = zero_terms_dependent sig vs bans; f = head zeroes; tzeroes = tail zeroes

enumerate_terms_dependent_helper :: Signature -> Int -> [Term] -> [Term] -> Term -> (((Int,[Term]),[Term]),Term)
enumerate_terms_dependent_helper sig d l ts t = case ts of 
	{
		[] -> enumerate_terms_dependent_helper sig (d+1) nd nd t;
		(rt:rts) -> (((d,l),rts),rt)
	}
	where nd = (terms_next_depth_dependent sig l)

terms_next_depth_dependent :: Signature -> [Term] -> [Term]
terms_next_depth_dependent (_,fs,_) ts = concat (map (apply_fun_terms ts) (filter (\f -> arity f > 0) fs))

terms_depth_dependent :: Signature -> VariableSet -> [Variable] -> Int -> [Term]
terms_depth_dependent sig vs bans 0 = zero_terms_dependent sig vs bans
terms_depth_dependent (ps,fs,n) vs bans i = concat (map (apply_fun_terms (terms_depth_dependent (ps,fs,n) vs bans (i-1))) (filter (\f -> arity f > 0) fs))

apply_fun_terms :: [Term] -> Function -> [Term]
apply_fun_terms ts f = map (\l -> TFun f l) (combinations (replicate (arity f) ts))

zero_terms_dependent :: Signature -> VariableSet -> [Variable] -> [Term]
zero_terms_dependent sig vs bans = (map (\v -> TVar v) (vars_dependent sig vs bans)) ++ (map (\f -> TFun f []) (constants sig))

constants :: Signature -> [Function]
constants (_,fs,_) = filter (\x -> arity x == 0) fs

vars_dependent :: Signature -> VariableSet -> [Variable] -> [Variable]
vars_dependent (_,_,n) vs bans = filter (\x -> not (elem x bans)) (get_vars_set n vs)


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

-- Alternate
--concat_enums :: Enumeration t -> Enumeration t -> Enumeration ((Bool,Maybe t),t)
--concat_enums (Enum e10 fe1) (Enum e20 fe2) = Enum ((False,Just e20),e10) (\idx -> \x -> case x of {((False,Just n2),c) -> Just ((True,fe1 ((quot idx 2) + 1) c),n2); ((True,Just n1),c) -> Just ((False,fe2 (quot idx 2) c),n1); ((False,Nothing),c)((,Nothing),Nothing) -> Nothing})

enum_first :: Enumeration t -> t
enum_first (Enum x _) = x

enum_enum :: Enumeration t -> Enumerator t
enum_enum (Enum _ x) = x

enum_up_to :: Int -> Enumeration t -> [t]
enum_up_to n (Enum t0 e) = enum_up_to_rec n e 1 t0

-- First parameter is how many left, second parameter is how many we did so far.
enum_up_to_rec :: Int -> Enumerator t -> Int -> t -> [t]
enum_up_to_rec 0 _ _ t0 = [t0]
enum_up_to_rec n f i t0 = case ft0 of {Nothing -> [t0]; Just x -> t0:(enum_up_to_rec (n-1) f (i+1) x)} where ft0 = f i t0

maybe_apply :: (a -> b) -> Maybe a -> Maybe b
maybe_apply _ Nothing = Nothing
maybe_apply f (Just x) = Just (f x)

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
diagonalize :: (a -> Enumeration b) -> Enumeration a -> Enumeration ((a,[(a,Enumerator b,Int,b)],[(a,Enumerator b,Int,b)]),(a,b))
diagonalize f (Enum a0 ea) = Enum ((a0,[],[(a0,enum_enum eb0,1,b0)]),(a0,b0)) (\idx -> \prev -> diagonalize_helper f ea idx prev) where eb0 = (f a0); b0 = enum_first eb0

diagonalize_helper :: (a -> Enumeration b) -> Enumerator a -> Int -> ((a,[(a,Enumerator b,Int,b)],[(a,Enumerator b,Int,b)]),(a,b)) -> Maybe ((a,[(a,Enumerator b,Int,b)],[(a,Enumerator b,Int,b)]),(a,b))
-- If there is a next one out of the open ones, iterate it. If it is nothing, then kill this branch and go again.
diagonalize_helper f ea idx ((na,done,((ca,eb,cidx,cb):ps)),prev) = case nb of {Nothing -> diagonalize_helper f ea idx ((na,done,ps),prev); Just nbb -> Just ((na,((ca,eb,cidx+1,nbb):done),ps),(ca,nbb))} where nb = eb cidx cb
-- This was buggy, when there was only one running enumerator left, and it finished, we finished, but there could be more enumerators to diagonalize over.
-- To solve it, we now check, when there are no next ones, whether there are no done ones NOR the enumerator for a returns a new one. That truly indicates when we have finished.
-- If there is neither next nor done ones, then we are finished.
--diagonalize_helper _ _ _ ((_,[],[]),_) = Nothing
-- If there is no next one, but there are done ones, then enumerate a once, add the enumerator (if there is one) and start over.
-- Note: We reverse all the lists simply to enumerate on the same order each time, for clarity, it is not really necessary.
diagonalize_helper f ea idx ((na,done,[]),prev) = case nna of {Nothing -> case done of {[] -> Nothing; (_:_) -> diagonalize_helper f ea idx ((na,[],done),prev)}; Just nnna -> Just ((nnna,[(nnna,enum_enum (f nnna),1,enum_first (f nnna))],reverse done),(nnna,enum_first (f nnna)))} where nna = ea idx na

enum_from_list :: [t] -> Enumeration ([t],t)
-- Not valid when the list is empty.
enum_from_list (x:xs) = (Enum (xs,x) (\idx -> \prev -> case (fst prev) of {[] -> Nothing; (x:xs) -> Just (xs,x)}))


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

enum_hleft_left_h :: Enumeration (h,a) -> Enumeration (Either h g,Either a b)
enum_hleft_left_h e = enum_hleft_h (enum_left_h e)

enum_hright_right_h :: Enumeration (h,a) -> Enumeration (Either g h,Either b a)
enum_hright_right_h e = enum_hright_h (enum_right_h e)

enum_hnil_h :: Enumeration a -> Enumeration ([h],a)
enum_hnil_h e = equiv_enum (\x -> ([],x)) (\y -> case y of {([],x) -> x}) e

enum_hcons_h :: Enumeration ((h,[h]),a) -> Enumeration ([h],a)
enum_hcons_h e = equiv_enum (\x -> case x of {((h,hs),a) -> (h:hs,a)}) (\y -> case y of {(h:hs,a) -> ((h,hs),a)}) e

diagonalize_h :: (a -> Enumeration (h2,b)) -> Enumeration (h1,a) -> Enumeration (((((h1,a),[((h1,a),Enumerator (h2,b),Int,(h2,b))],[((h1,a),Enumerator (h2,b),Int,(h2,b))]),(h1,a)),h2),b)
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



-- This function takes a current solution, calculates the best root class, and acts in consequence.
-- If the best root class requires no enumeration, then this is simply assigning the canonical variable to that class, and propagating.
-- If the best root class requires enumeration, then this implies producing an enumeration and propagating to get new solutions.
enumerate_or_propagate :: Signature -> FullSolution -> Either FullSolution (Enumeration (_,FullSolution))
enumerate_or_propagate (preds,funs,n) fs = case action of
										{
											-- Choose any random meta-variable and enumerate
											Nothing -> Right (enum_hleft_h (enumerate_and_propagate_metavar (preds,funs,n) fs (find_random_metavar_dep (get_graph fs))));
											-- Just choose canonical variable and propagate. This means that all in that class, including the representative, need to be of the form "u x".
											Just ((DRec u (DVar v)),Nothing) -> Left (propagate_canonical_variable (preds,funs,n) fs u v);
											-- Enumerate over the given meta-variable.
											-- Note: Feels like I could do something more intelligent here. I am not using the information of where that meta-variable was, and instead I am recalculating stuff again for each enumeration of the meta-variable. For now, this is good enough.
											Just (rep,Just dep) -> Right (enum_hright_h (enumerate_and_propagate_metavar (preds,funs,n) fs dep))
										}
										where action = find_best_root_class n fs

propagate_canonical_variable :: Signature -> FullSolution -> Unifier -> Variable -> FullSolution
propagate_canonical_variable (_,_,n) fs u v = (update_graph_all (set_solution fs dv) [dv] []) where dv = ((DRec u (DVar v)),Left (TVar (get_image_var n u v)))

-- Find a random meta-variable
-- Here be where heuristics could come in. In any case, this situation is pretty bad, there's not many intelligent things to do, that's why we try to avoid it at all costs.
find_random_metavar_dep :: DependencyGraph -> Dependent
find_random_metavar_dep g = head (filter has_unifier (filter is_dependent_metavar (map get_dependent (nodes g))))


-- Enumerate over the indicated dependent, which corresponds to a meta-var.
-- We need to:
--		- Expose the meta-variable -> NOPE.
--		- Find out in what VariableSet the exposed meta-variable stands. -> YUP.
--		- Find out which variables are banned due to the topology of the graph. -> YUP.
--		- Enumerate possible instantiations of the meta-variable given that knowledge. -> YUP.
--		- For each of those, generate the corresponding solution (do this through apply_enum_1_h, of course, so that this generates a solution enumeration). -> YUP.
enumerate_and_propagate_metavar :: Signature -> FullSolution -> Dependent -> Enumeration (_,FullSolution)
enumerate_and_propagate_metavar sig fs dep | (is_dependent_term dep) = propagate_over_metavariable_enum fs dep (enum_hleft_left_h terms) where vs = find_variable_set dep; bans = find_banned_vars_in_instantiation (get_graph fs) dep; terms = enumerate_terms_dependent sig vs bans
enumerate_and_propagate_metavar sig fs dep = propagate_over_metavariable_enum fs dep (enum_hright_right_h lits) where vs = find_variable_set dep; bans = find_banned_vars_in_instantiation (get_graph fs) dep; lits = enumerate_lits_dependent sig vs bans

find_banned_vars_in_instantiation :: DependencyGraph -> Dependent -> [Variable]
find_banned_vars_in_instantiation g d = find_banned_vars_in_instantiation_rec g d

find_banned_vars_in_instantiation_rec :: DependencyGraph -> Dependent -> [Variable]
find_banned_vars_in_instantiation_rec g d = concat (map (\sd -> (find_banned_vars_in_instantiation g sd) ++ (find_directly_banned_vars_in_instantiation sd)) (map get_htarget (get_outgoing_hdeps (find_node g d))))

find_directly_banned_vars_in_instantiation :: Dependent -> [Variable]
find_directly_banned_vars_in_instantiation (DVar v) = [v]
find_directly_banned_vars_in_instantiation (DMetaT _) = []
find_directly_banned_vars_in_instantiation (DMetaL _) = []
find_directly_banned_vars_in_instantiation (DRec u d) = find_directly_banned_vars_in_instantiation d

-- Assumes that it has at least one unifier.
find_variable_set :: Dependent -> VariableSet
find_variable_set (DRec u _) = Rg u

propagate_over_metavariable_enum :: FullSolution -> Dependent -> Enumeration (_,Either Term Literal) -> Enumeration (_,FullSolution)
propagate_over_metavariable_enum fs dep ev = apply_enum_1_h (propagate_over_metavariable_single fs dep) ev

propagate_over_metavariable_single :: FullSolution -> Dependent -> Either Term Literal -> FullSolution
--propagate_over_metavariable_single fs dep v = update_graph_all fs2 [dv] [] where (fs1,mv) = expose_metavariable fs dep; fs2 = propagate_metavar_value fs1 dep mv v; dv = (dep,v)
propagate_over_metavariable_single fs dep v = update_graph_all (set_solution fs dv) [dv] [] where dv = (dep,v)

-- These things below really are unnecessary, but we keep them just in case we discover we actually need them.

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
propagate_metavar_value (mvs,eqs,(inst,cs),(g,sol,ueqs)) dep mv v = (mvs1,eqs,(rinst,[]),(rg,sol,ueqs)) where (mvs1,(inst1,cs1)) = recalculate_constraints_from_dependent mvs (inst,cs) g dep v; rg = update_graph_with_constraints (remove_node g dep) cs1; rinst = compose_inst (build_inst mv v) inst1

recalculate_constraints_from_dependent :: [Metavariable] -> UnifSolution -> DependencyGraph -> Dependent -> Either Term Literal -> ([Metavariable],UnifSolution)
recalculate_constraints_from_dependent mvs (inst,cs) g dep (Left t) = recalculate_constraints_eqdep mvs1 (inst1,cs1) (Left (all_simpl_mterm (metaterm_from_depnode dep))) (Left (MTermT t)) g [dep] where n = find_node g dep; (mvs1,(inst1,cs1)) = recalculate_constraints_hdep mvs (inst,cs) (Left (all_simpl_mterm (metaterm_from_depnode dep))) (Left (MTermT t)) ((get_outgoing_hdeps n) ++ (get_incoming_hdeps n)) 
recalculate_constraints_from_dependent mvs (inst,cs) g dep (Right l) = recalculate_constraints_eqdep mvs1 (inst1,cs1) (Right (all_simpl_mlit (metalit_from_depnode dep))) (Right (MLitL l)) g [dep] where n = find_node g dep; (mvs1,(inst1,cs1)) = recalculate_constraints_hdep mvs (inst,cs) (Right (all_simpl_mlit (metalit_from_depnode dep))) (Right (MLitL l)) ((get_outgoing_hdeps n) ++ (get_incoming_hdeps n)) 





-- At some point, we have to check for unsatisfiability of constraints and for occurs checks, and fail in such cases. Need to think clearly where this should happen. Probably at each moment before
-- thinking what to do. Need to make sure that every time there is an unsatisfiability or an occurs check it is detected, too.

-- Establish and verify a limit on the number of unifiers to be applied! Integers overflow. If this is a problem, replace Int with an unbound type.
