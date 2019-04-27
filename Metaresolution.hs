{-# LANGUAGE PartialTypeSignatures #-}
module Metaresolution where

import Constraints
import Data.Maybe
import Data.List
import Data.Either

-- We made the mistake, in Constraints.hs, of calling Atoms "Literals". We call actual literals "ActualLiteral"(s) here. That is, a Literal contains no negation, and an ActualLiteral is 
-- either a negated or non-negated Literal.

data ActualLiteral = PosLit Metaliteral | NegLit Metaliteral

instance Show ActualLiteral where
	show (PosLit ml) = "+" ++ (show ml)
	show (NegLit ml) = "-" ++ (show ml)

instance Eq ActualLiteral where
	(PosLit ml1) == (PosLit ml2) = ml1 == ml2
	(NegLit ml1) == (NegLit ml2) = ml1 == ml2
	(PosLit _) == (NegLit _) = False
	(NegLit _) == (PosLit _) = False

instance Read ActualLiteral where
	readsPrec _ ('+':xs) = (let r = (head (reads xs))
				in [(PosLit (fst r),(snd r))])
	readsPrec _ ('-':xs) = (let r = (head (reads xs))
				in [(NegLit (fst r),(snd r))])
	readsPrec _ xs = []

get_atom :: ActualLiteral -> Metaliteral
get_atom (PosLit l) = l
get_atom (NegLit l) = l

flip_literal :: ActualLiteral -> ActualLiteral
flip_literal (PosLit l) = NegLit l
flip_literal (NegLit l) = PosLit l

apply_to_literal :: (Metaliteral -> Metaliteral) -> ActualLiteral -> ActualLiteral
apply_to_literal f (PosLit l) = PosLit (f l)
apply_to_literal f (NegLit l) = NegLit (f l)

-- A clause is just a list of literals, with conceptual logical disjunctions between them.
type Clause = [ActualLiteral]

-- And a CNF is just a list of clauses, with conceptual logical conjunctions between them.
-- Note that all variables appearing in the CNF are conceptually universally quantified, and existentially quantified variables have been replaced by Skolem terms. These should correspond to what is indicated in the ExtendedSignature accompannying the CNF
type CNF = [Clause]

append_clause :: CNF -> Clause -> CNF
append_clause [] cl = [cl]
append_clause (cl1:cls) cl2 = (cl1:(append_clause cls cl2))

get_metavars_actual_lit :: ActualLiteral -> [Metavariable]
get_metavars_actual_lit (PosLit l) = get_metavars_mlit l
get_metavars_actual_lit (NegLit l) = get_metavars_mlit l

get_metavars_clause :: Clause -> [Metavariable]
get_metavars_clause cl = foldr union [] (map get_metavars_actual_lit cl)

get_metavars_cnf :: CNF -> [Metavariable]
get_metavars_cnf cnf = foldr union [] (map get_metavars_clause cnf)

-- Note that transforming a formula into CNF form is performed outside this program: its assumed input are always CNFs in the adequate format.

-- In the process of solving a CNF through meta-resolution, we generate constraints, which may be dumped down into a DependencyGraph and we inductively instantiate the meta-variables.
-- We would like to work with a FullSolution, but the Instantiation as defined in Constraints.hs does NOT include logical connectives (and, or, not).
-- Therefore, we add LogicalInstantiation to deal with this, which we just apply before the one in FullSolution.
data Formula = FLit Literal | FNeg Formula | FAnd Formula Formula | FOr Formula Formula deriving Eq

instance Show Formula where
	show (FLit l) = (show l)
	show (FNeg f) = "~(" ++ (show f) ++ ")"
	show (FAnd f1 f2) = "(" ++ (show f1) ++ ") & (" ++ (show f2) ++ ")"
	show (FOr f1 f2) = "(" ++ (show f1) ++ ") | (" ++ (show f2) ++ ")"

type LogicalInstantiation = (Metavariable -> Formula)

eq_loginst :: [Metavariable] -> LogicalInstantiation -> LogicalInstantiation -> Bool
eq_loginst mvs loginst1 loginst2 = all (\mv -> (loginst1 mv) == (loginst2 mv)) mvs

show_loginst_mv :: LogicalInstantiation -> Metavariable -> String
show_loginst_mv i mv = (show mv) ++ " -> " ++ (show (i mv))

show_loginst :: LogicalInstantiation -> [Metavariable] -> String
show_loginst i [] = "{}"
show_loginst i (x:xs) = "{" ++ (foldl (\s -> \mv -> s ++ "," ++ (show_loginst_mv i mv)) (show_loginst_mv i x) xs) ++ "}\n"

-- Still not full unification, but we check that it may be just a literal in the loginst and still be compatible with the inst, if it has the same predicate.
-- Maybe some day we will be forced to do full meta-level unification here, too.
compatible_inst_loginst :: LogicalInstantiation -> Instantiation -> [Metavariable] -> Bool
compatible_inst_loginst loginst inst mvs = all (\mv -> if ((has_inst_value inst mv) && (has_loginst_value loginst mv)) then (case (loginst mv) of {FLit (Lit pl _) -> case (apply_inst inst mv) of {Just (Right (Lit pi _)) -> if (pl == pi) then True else False; _ -> False}; _ -> False}) else True) mvs

has_loginst_value :: LogicalInstantiation -> Metavariable -> Bool
has_loginst_value loginst mv = (loginst mv) /= (FLit (LitM mv))

build_loginst :: Metavariable -> Formula -> LogicalInstantiation
build_loginst mv f = (\mx -> if (mx == mv) then f else (FLit (LitM mx)))

apply_loginst_formula :: LogicalInstantiation -> Formula -> Formula
apply_loginst_formula i (FLit (LitM mv)) = i mv
apply_loginst_formula i (FLit l) = FLit l
apply_loginst_formula i (FNeg f) = FNeg (apply_loginst_formula i f)
apply_loginst_formula i (FAnd f1 f2) = FAnd (apply_loginst_formula i f1) (apply_loginst_formula i f2)
apply_loginst_formula i (FOr f1 f2) = FOr (apply_loginst_formula i f1) (apply_loginst_formula i f2)

apply_inst_formula :: Instantiation -> Formula -> Formula
apply_inst_formula i (FLit l) = (FLit (apply_inst_lit i l))
apply_inst_formula i (FNeg f) = FNeg (apply_inst_formula i f)
apply_inst_formula i (FAnd f1 f2) = FAnd (apply_inst_formula i f1) (apply_inst_formula i f2)
apply_inst_formula i (FOr f1 f2) = FOr (apply_inst_formula i f1) (apply_inst_formula i f2)


-- A CNF as a function of a meta-variable value, but syntactically rather than semantically, to know where the "holes" are.

-- To "index" the variables, we use the structure of the formula it comes from itself. This allows local indexing of the variables without having to recalculate the whole structure.
data LambdaFormulaVar = LFBaseVar | LFNegVar LambdaFormulaVar | LFLeftAndVar LambdaFormulaVar | LFRightAndVar LambdaFormulaVar | LFLeftOrVar LambdaFormulaVar | LFRightOrVar LambdaFormulaVar deriving Eq

apply_lambdaformula :: Formula -> (LambdaFormulaVar -> Formula)
apply_lambdaformula f LFBaseVar = f
apply_lambdaformula f (LFNegVar v) = case (apply_lambdaformula f v) of {FNeg g -> g}
apply_lambdaformula f (LFLeftAndVar v) = case (apply_lambdaformula f v) of {FAnd f1 f2 -> f1}
apply_lambdaformula f (LFRightAndVar v) = case (apply_lambdaformula f v) of {FAnd f1 f2 -> f2}
apply_lambdaformula f (LFLeftOrVar v) = case (apply_lambdaformula f v) of {FOr f1 f2 -> f1}
apply_lambdaformula f (LFRightOrVar v) = case (apply_lambdaformula f v) of {FOr f1 f2 -> f2}

apply_lambdaformula_lit :: Formula -> (LambdaFormulaVar -> ActualLiteral)
-- Negations may appear here because of flippings that appear when applying the resolution rule, but no ands or ors should appear here.
apply_lambdaformula_lit f v = case (apply_lambdaformula f v) of {FLit l -> PosLit (MLitL l); FNeg (FLit l) -> NegLit (MLitL l)}

data LambdaAtom = LAtomVar LambdaFormulaVar | LAtomLit Metaliteral | LAtomR Unifier LambdaAtom deriving Eq

data LambdaLiteral = LPosLit LambdaAtom | LNegLit LambdaAtom

type LambdaClause = [LambdaLiteral]

type LambdaCNF = [LambdaClause]

-- This function assumes that the LambdaCNF has absorbed the structure of the formula already, so that
-- the final results will be literals when corresponding.
apply_lambdacnf_lit :: Formula -> LambdaCNF -> CNF
apply_lambdacnf_lit f lcnf = map (apply_lambdaclause_lit f) lcnf

apply_lambdaclause_lit :: Formula -> LambdaClause -> Clause
apply_lambdaclause_lit f lcl = map (apply_lambdalit_lit f) lcl

apply_lambdalit_lit :: Formula -> LambdaLiteral -> ActualLiteral
apply_lambdalit_lit f (LPosLit a) = apply_lambdaatom_lit f a
apply_lambdalit_lit f (LNegLit a) = case (apply_lambdaatom_lit f a) of {PosLit ml -> NegLit ml; NegLit ml -> PosLit ml}

-- The potential negation here is really only used to note that "it should be negated" at the level above, it's not really a literal. In other words, this may imply double negations, that are solved at the level above.
apply_lambdaatom_lit :: Formula -> LambdaAtom -> ActualLiteral
apply_lambdaatom_lit f (LAtomVar v) = apply_lambdaformula_lit f v
apply_lambdaatom_lit _ (LAtomLit ml) = PosLit ml
apply_lambdaatom_lit f (LAtomR u at) = case (apply_lambdaatom_lit f at) of {PosLit ml -> PosLit (MLitR u ml); NegLit ml -> NegLit (MLitR u ml)}

apply_loginst_cnf :: [Metavariable] -> LogicalInstantiation -> CNF -> CNF
apply_loginst_cnf mvs i cnf = foldl (\cnf2 -> \mv -> apply_loginst_cnf_helper mv cnf2 (i mv)) cnf mvs

-- Give me a CNF and a meta-variable to replace and I'll give you a function that, given a formula to replace for that meta-variable, gives me the resulting CNF.
-- Parentheses put explicitly to illustrate this way of thinking about it.
apply_loginst_cnf_helper :: Metavariable -> CNF -> (Formula -> CNF)
apply_loginst_cnf_helper mv cnf f = apply_lambdacnf_lit f (apply_loginst_cnf_helper_2 f LFBaseVar (apply_loginst_cnf_lit mv cnf))

apply_loginst_cnf_helper_2 :: Formula -> LambdaFormulaVar -> LambdaCNF -> LambdaCNF
apply_loginst_cnf_helper_2 (FLit l) v lcnf = lcnf
apply_loginst_cnf_helper_2 (FNeg f) v lcnf = apply_loginst_cnf_helper_2 f (LFNegVar v) (apply_loginst_lcnf_flip v lcnf)
apply_loginst_cnf_helper_2 (FOr f1 f2) v lcnf = ((apply_loginst_cnf_helper_2 f1 (LFLeftOrVar v)) . (apply_loginst_cnf_helper_2 f2 (LFRightOrVar v))) (apply_loginst_lcnf_splitlit v lcnf)
apply_loginst_cnf_helper_2 (FAnd f1 f2) v lcnf = ((apply_loginst_cnf_helper_2 f1 (LFLeftAndVar v)) . (apply_loginst_cnf_helper_2 f2 (LFRightAndVar v))) (apply_loginst_lcnf_splitclause v lcnf)

apply_loginst_lcnf_splitclause :: LambdaFormulaVar -> LambdaCNF -> LambdaCNF
apply_loginst_lcnf_splitclause v lcnf = concat (map ((apply_loginst_lclause_splitclause v) . (apply_loginst_lclause_splitclause_neg v)) lcnf)

-- Positive literals, clause is split.
apply_loginst_lclause_splitclause :: LambdaFormulaVar -> LambdaClause -> [LambdaClause]
apply_loginst_lclause_splitclause v [] = [[]]
apply_loginst_lclause_splitclause v ((LPosLit (LAtomVar w)):cl) | v == w = (map left_clause (apply_loginst_lclause_splitclause v cl)) ++ (map right_clause (apply_loginst_lclause_splitclause v cl)) where left_clause = (\cl2 -> (LPosLit (LAtomVar (LFLeftAndVar w))):cl2); right_clause = (\cl2 -> (LPosLit (LAtomVar (LFRightAndVar w))):cl2)
apply_loginst_lclause_splitclause v (llit:cl) = map (\cl2 -> llit:cl2) (apply_loginst_lclause_splitclause v cl)

-- Negative literals. These are just split within the clause
apply_loginst_lclause_splitclause_neg :: LambdaFormulaVar -> LambdaClause -> LambdaClause
apply_loginst_lclause_splitclause_neg v [] = []
apply_loginst_lclause_splitclause_neg v ((LNegLit (LAtomVar w)):cl) | v == w = (LNegLit (LAtomVar (LFLeftAndVar w))):(LNegLit (LAtomVar (LFRightAndVar w))):(apply_loginst_lclause_splitclause_neg v cl)
apply_loginst_lclause_splitclause_neg v (llit:cl) = llit:(apply_loginst_lclause_splitclause_neg v cl)

apply_loginst_lcnf_splitlit :: LambdaFormulaVar -> LambdaCNF -> LambdaCNF
apply_loginst_lcnf_splitlit v lcnf = concat (map ((apply_loginst_lclause_splitlit_neg v) . (apply_loginst_lclause_splitlit v)) lcnf)

-- Negative literals, clause is split.
apply_loginst_lclause_splitlit_neg :: LambdaFormulaVar -> LambdaClause -> [LambdaClause]
apply_loginst_lclause_splitlit_neg v [] = [[]]
apply_loginst_lclause_splitlit_neg v ((LNegLit (LAtomVar w)):cl) | v == w = (map left_clause (apply_loginst_lclause_splitlit_neg v cl)) ++ (map right_clause (apply_loginst_lclause_splitlit_neg v cl)) where left_clause = (\cl2 -> (LNegLit (LAtomVar (LFLeftOrVar w))):cl2); right_clause = (\cl2 -> (LNegLit (LAtomVar (LFRightOrVar w))):cl2)
apply_loginst_lclause_splitlit_neg v (llit:cl) = map (\cl2 -> llit:cl2) (apply_loginst_lclause_splitlit_neg v cl)

-- Only positive literals dealt with here. These are just split within the clause.
apply_loginst_lclause_splitlit :: LambdaFormulaVar -> LambdaClause -> LambdaClause
apply_loginst_lclause_splitlit v [] = []
apply_loginst_lclause_splitlit v ((LPosLit (LAtomVar w)):cl) | v == w = (LPosLit (LAtomVar (LFLeftOrVar w))):(LPosLit (LAtomVar (LFRightOrVar w))):(apply_loginst_lclause_splitlit v cl)
apply_loginst_lclause_splitlit v (llit:cl) = llit:(apply_loginst_lclause_splitlit v cl)

-- Flip the variable!!!
apply_loginst_lcnf_flip :: LambdaFormulaVar -> LambdaCNF -> LambdaCNF
apply_loginst_lcnf_flip v lcnf = map (apply_loginst_lclause_flip v) lcnf

apply_loginst_lclause_flip :: LambdaFormulaVar -> LambdaClause -> LambdaClause
apply_loginst_lclause_flip v lcl = map (apply_loginst_llit_flip v) lcl

apply_loginst_llit_flip :: LambdaFormulaVar -> LambdaLiteral -> LambdaLiteral
apply_loginst_llit_flip v (LPosLit (LAtomVar w)) | v == w = LNegLit (LAtomVar (LFNegVar v))
apply_loginst_llit_flip v (LNegLit (LAtomVar w)) | v == w = LPosLit (LAtomVar (LFNegVar v))
apply_loginst_llit_flip v x = x


apply_loginst_cnf_lit :: Metavariable -> CNF -> LambdaCNF
apply_loginst_cnf_lit mv cnf = map (apply_loginst_clause_lit mv) cnf

apply_loginst_clause_lit :: Metavariable -> Clause -> LambdaClause
apply_loginst_clause_lit mv cl = map (apply_loginst_lit_lit mv) cl

apply_loginst_lit_lit :: Metavariable -> ActualLiteral -> LambdaLiteral
apply_loginst_lit_lit mv1 (PosLit ml) = LPosLit (apply_loginst_lit_atom mv1 ml)
apply_loginst_lit_lit mv1 (NegLit ml) = LNegLit (apply_loginst_lit_atom mv1 ml)

apply_loginst_lit_atom :: Metavariable -> Metaliteral -> LambdaAtom
apply_loginst_lit_atom mv1 (MLitR u ml) = LAtomR u (apply_loginst_lit_atom mv1 ml)
apply_loginst_lit_atom mv1 ml | isJust aslit && mv1 == mv2 = LAtomVar LFBaseVar where aslit = is_metavar_lit ml; (mv2,us) = fromJust aslit
apply_loginst_lit_atom mv1 ml = LAtomLit ml

set_loginst :: LogicalInstantiation -> Metavariable -> Formula -> LogicalInstantiation
set_loginst loginst mv f = compose_loginst (build_loginst mv f) loginst

compose_loginst :: LogicalInstantiation -> LogicalInstantiation -> LogicalInstantiation
compose_loginst i1 i2 mv = apply_loginst_formula i1 (i2 mv)

compose_loginst_inst :: Instantiation -> LogicalInstantiation -> LogicalInstantiation
compose_loginst_inst i li mv = apply_inst_formula i (li mv)

idloginst :: LogicalInstantiation
idloginst mv = FLit (LitM mv)


-- Checking whether two literals can be resolved. In principle this would not be necessary, we could just generate unsatisfiable constraints and then say it's unsatisfiable.
-- However, it is a lot more efficient if we do some basic checking here. Mostly, that at least one side is a meta-variable, or that if neither are, 
-- then the predicate is the same (and they are of different sign). This does not guarantee satisfiability of the unifier constraints, but it is a necessary condition.

can_resolve_literals :: ActualLiteral -> ActualLiteral -> Bool
can_resolve_literals (PosLit l) (NegLit _) | isJust (is_metavar_lit l) = True
can_resolve_literals (PosLit _) (NegLit l) | isJust (is_metavar_lit l) = True
can_resolve_literals (PosLit l) (PosLit _) | isJust (is_metavar_lit l) = True
can_resolve_literals (PosLit _) (PosLit l) | isJust (is_metavar_lit l) = True
can_resolve_literals (NegLit l) (PosLit _) | isJust (is_metavar_lit l) = True
can_resolve_literals (NegLit _) (PosLit l) | isJust (is_metavar_lit l) = True
can_resolve_literals (NegLit l) (NegLit _) | isJust (is_metavar_lit l) = True
can_resolve_literals (NegLit _) (NegLit l) | isJust (is_metavar_lit l) = True
can_resolve_literals (PosLit l1) (NegLit l2) | isJust p1 && p1 == p2 = True where p1 = is_predicate_lit l1; p2 = is_predicate_lit l2
can_resolve_literals (NegLit l1) (PosLit l2) | isJust p1 && p1 == p2 = True where p1 = is_predicate_lit l1; p2 = is_predicate_lit l2
can_resolve_literals _ _ = False


-- Receives the next unifier to use, the two literals to resolve over (assumed to have already been checked to be resolvable, and therefore we only require the Atom (Literal)), and the two clauses WITHOUT THE LITERALS. These will be used only to generate the resulting clause.
-- Returns the resulting clause and the constraints generate.
-- This function does not remove repeated clauses or literals.
apply_resolution_rule :: Unifier -> Metaliteral -> Metaliteral -> Clause -> Clause -> (Constraint,Clause)
apply_resolution_rule u ml1 ml2 c1 c2 = (Lcstr (MLitR u ml1) (MLitR u ml2), (map (apply_to_literal (MLitR u)) (c1 ++ c2)))

-- Does the flipping around if necessary, wrapping the previous function.
-- Performance "trick": We receive the logical instantiation and only compose with it when it is actually necessary.
apply_resolution_rule_lits :: [Metavariable] -> LogicalInstantiation -> Unifier -> ActualLiteral -> ActualLiteral -> Clause -> Clause -> (Constraint,Clause,LogicalInstantiation,[Metavariable],Metaliteral,Metaliteral)
apply_resolution_rule_lits mvs loginst u (PosLit ml1) (NegLit ml2) c1 c2 = (cstr,rsv,loginst,mvs,ml1,ml2) where (cstr,rsv) = apply_resolution_rule u ml1 ml2 c1 c2
-- If they are flipped then it HAS to be a meta-variable.
apply_resolution_rule_lits mvs loginst u (NegLit ml1) al2 c1 c2 = (cstr,rsv,compose_loginst (build_loginst mv (FNeg (idloginst nmv))) rloginst,nmv:rmvs,rml1,rml2) where (mv,us) = fromJust (is_metavar_lit ml1); nmv = new_metavar mvs; nml = build_metaliteral (reverse us) (MLitL (LitM nmv)); (cstr,rsv,rloginst,rmvs,rml1,rml2) = apply_resolution_rule_lits mvs loginst u (PosLit nml) al2 c1 c2
apply_resolution_rule_lits mvs loginst u (PosLit ml1) (PosLit ml2) c1 c2 = (cstr,rsv,compose_loginst (build_loginst mv (FNeg (idloginst nmv))) rloginst,nmv:rmvs,rml1,rml2) where (mv,us) = fromJust (is_metavar_lit ml2); nmv = new_metavar mvs; nml = build_metaliteral (reverse us) (MLitL (LitM nmv)); (cstr,rsv,rloginst,rmvs,rml1,rml2) = apply_resolution_rule_lits mvs loginst u (PosLit ml1) (NegLit nml) c1 c2

-- Cleaning that definitely needs to be done.

-- This also does not care about repetition.
eq_no_order_wrt :: (a -> a -> Bool) -> [a] -> [a] -> Bool
eq_no_order_wrt eq xs ys = (all (\x -> any (eq x) ys) xs) && (all (\y -> any (eq y) xs) ys)

nub_wrt :: (a -> a -> Bool) -> [a] -> [a]
nub_wrt eq [] = []
nub_wrt eq (x:xs) = (x:(nub_wrt eq (filter (\y -> not (eq x y)) xs)))

eq_clause :: Clause -> Clause -> Bool
eq_clause cl1 cl2 = eq_no_order_wrt (==) cl1 cl2

eq_cnf :: CNF -> CNF -> Bool
eq_cnf cnf1 cnf2 = eq_no_order_wrt eq_clause cnf1 cnf2

clean_deffo_clause :: Clause -> Clause
clean_deffo_clause c = remove_deffo_repeated_lits c

clean_deffo_cnf :: CNF -> CNF
clean_deffo_cnf = (remove_deffo_repeated_clauses . remove_deffo_valid_clauses . (map clean_deffo_clause))

-- Note: "deffo" stands for "definitively". This is a usual abbreviation, at least in certain subcultures.
remove_deffo_repeated_lits :: Clause -> Clause
remove_deffo_repeated_lits c = nub c

remove_deffo_repeated_clauses :: CNF -> CNF
remove_deffo_repeated_clauses cnf = nub_wrt (eq_no_order_wrt (==)) cnf

-- Valid clauses = Clauses with complementary literals
remove_deffo_valid_clauses :: CNF -> CNF
remove_deffo_valid_clauses c = filter (\x -> not (is_clause_deffo_valid x)) c

is_clause_deffo_valid :: Clause -> Bool
is_clause_deffo_valid [] = False
is_clause_deffo_valid ((PosLit l):ls) = (elem (NegLit l) ls) || (is_clause_deffo_valid ls)
is_clause_deffo_valid ((NegLit l):ls) = (elem (PosLit l) ls) || (is_clause_deffo_valid ls)


-- Make sure that meta-variables which are instantiated logically (with connectives) do not appear in meta-unification constraints. This is incompatible.
filter_incompatible_instantiations :: [MetavariableLink] -> Maybe (FullSolution,LogicalInstantiation) -> Maybe (FullSolution,LogicalInstantiation)
filter_incompatible_instantiations _ Nothing = Nothing
filter_incompatible_instantiations ls (Just ((_,_,(_,cs),_),loginst)) | or (map (\mv -> (loginst mv) /= (idloginst mv)) (transitivize_metavar_links ls (concat (map metavars_in_constraint cs)))) = Nothing
filter_incompatible_instantiations _ (Just x) = Just x

transitivize_metavar_links :: [MetavariableLink] -> [Metavariable] -> [Metavariable]
transitivize_metavar_links ls mvs = concat (map (transitivize_metavar_link ls) mvs)

transitivize_metavar_link :: [MetavariableLink] -> Metavariable -> [Metavariable]
transitivize_metavar_link [] x = [x]
transitivize_metavar_link ((mv1,rs):ls) mv2 | mv1 == mv2 = (mv1:(map fst rs)) ++ (transitivize_metavar_link ls mv2)
transitivize_metavar_link ((mv1,rs):ls) mv2 = transitivize_metavar_link ls mv2

metavars_in_constraint :: Constraint -> [Metavariable]
metavars_in_constraint (Tcstr mt1 mt2) = (metavars_in_metaterm mt1) ++ (metavars_in_metaterm mt2)
metavars_in_constraint (Lcstr ml1 ml2) = (metavars_in_metaliteral ml1) ++ (metavars_in_metaliteral ml2)
metavars_in_constraint Unsatisfiable = []

metavars_in_metaliteral :: Metaliteral -> [Metavariable]
metavars_in_metaliteral (MLitL l) = metavars_in_literal l
metavars_in_metaliteral (MLitR _ ml) = metavars_in_metaliteral ml
metavars_in_metaliteral (MLitP _ mts) = concat (map metavars_in_metaterm mts)

metavars_in_metaterm :: Metaterm -> [Metavariable]
metavars_in_metaterm (MTermT t) = metavars_in_term t
metavars_in_metaterm (MTermR _ mt) = metavars_in_metaterm mt
metavars_in_metaterm (MTermF _ mts) = concat (map metavars_in_metaterm mts)

metavars_in_literal :: Literal -> [Metavariable]
metavars_in_literal (Lit _ ts) = concat (map metavars_in_term ts)
metavars_in_literal (LitM mv) = [mv]

metavars_in_term :: Term -> [Metavariable]
metavars_in_term (TVar _) = []
metavars_in_term (TMeta mv) = [mv]
metavars_in_term (TFun _ ts) = concat (map metavars_in_term ts)

-- Can we make a resolved clause be the empty clause?
-- This depends on the two clauses it resolved, and it means that all literals in the positive clause are unifiable to the same positive literal, and that all literals in the negative clause are unifiable to the same negative literal. In this process, we can flip meta-variables as necessary (which means instantiating), and it generates a set of constraints.
force_empty_clause :: ExtendedSignature -> (FullSolution,LogicalInstantiation) -> Unifier -> Metaliteral -> Metaliteral -> Clause -> Clause -> Maybe (FullSolution,LogicalInstantiation)
force_empty_clause (_,_,_,ls) ((mvs,mveqs,(inst,cs),gsol),loginst) u ml1 ml2 cl1 cl2 = filter_incompatible_instantiations ls (foldl (combine_force_empty_clause True u ml1) (foldl (combine_force_empty_clause False u ml2) (Just ((mvs,mveqs,(inst,cs),gsol),loginst)) cl2) cl1)

-- Tries to impose the equivalence after unification to a literal, flipping the meta-variable if necessary. Returns Nothing if it is not possible, avoiding search.
-- The first parameter indicates whether it is the positive or the negative clause that we are checking.
force_empty_clause_helper :: Bool -> [Metavariable] -> Unifier -> Metaliteral -> ActualLiteral -> Maybe (Constraint,LogicalInstantiation,[Metavariable])
-- The arguments passed to can_resolve_literals are flipped because we are trying to unify within the same clause.
force_empty_clause_helper True _ _ ml1 lit2 | (not (can_resolve_literals lit2 (NegLit ml1))) = Nothing 
force_empty_clause_helper False _ _ ml1 lit2 | (not (can_resolve_literals (PosLit ml1) lit2)) = Nothing
force_empty_clause_helper True mvs u ml1 (PosLit ml2) = Just (Lcstr (MLitR u ml1) (MLitR u ml2),idloginst,mvs)
force_empty_clause_helper True mvs u ml1 (NegLit ml2) | isJust aslit = Just (Lcstr (MLitR u ml1) (MLitR u nml),build_loginst mv (FNeg (idloginst nmv)),(nmv:mvs)) where aslit = is_metavar_lit ml2; (mv,us) = fromJust aslit; nmv = new_metavar mvs; nml = build_metaliteral (reverse us) (MLitL (LitM nmv))
force_empty_clause_helper True mvs u ml1 _ = Nothing
force_empty_clause_helper False mvs u ml1 (NegLit ml2) = Just (Lcstr (MLitR u ml1) (MLitR u ml2),idloginst,mvs)
force_empty_clause_helper False mvs u ml1 (PosLit ml2) | isJust aslit = Just (Lcstr (MLitR u ml1) (MLitR u nml),build_loginst mv (FNeg (idloginst nmv)),(nmv:mvs)) where aslit = is_metavar_lit ml2; (mv,us) = fromJust aslit; nmv = new_metavar mvs; nml = build_metaliteral (reverse us) (MLitL (LitM nmv))
force_empty_clause_helper False mvs u ml1 _ = Nothing

combine_force_empty_clause :: Bool -> Unifier -> Metaliteral -> Maybe (FullSolution,LogicalInstantiation) -> ActualLiteral -> Maybe (FullSolution,LogicalInstantiation)
combine_force_empty_clause flag u ml1 Nothing al = Nothing
combine_force_empty_clause flag u ml1 (Just ((mvs,mveqs,(inst,cs),gsol),loginst)) al = combine_force_empty_clause_helper (Just ((mvs,mveqs,(inst,cs),gsol),loginst)) (force_empty_clause_helper flag mvs u ml1 al)

combine_force_empty_clause_helper :: Maybe (FullSolution,LogicalInstantiation) -> Maybe (Constraint,LogicalInstantiation,[Metavariable]) -> Maybe (FullSolution,LogicalInstantiation)
combine_force_empty_clause_helper Nothing _ = Nothing
combine_force_empty_clause_helper _ Nothing = Nothing
combine_force_empty_clause_helper (Just ((mvs,mveqs,(inst,cs),gsol),loginst)) (Just (c,nloginst,nmvs)) = Just ((nmvs,mveqs,(inst,c:cs),gsol),compose_loginst nloginst loginst)
-- This is an old version: Updates the graph at each step. We update them outside the force_empty_clause call, all at once.
--combine_force_empty_clause_helper (Just ((mvs,mveqs,(inst,cs),gsol),loginst)) (Just (c,nloginst,nmvs)) = Just ((rmvs,mveqs,(rinst,[]),update_graph_with_constraints gsol rcs),compose_loginst nloginst loginst) where (rmvs,(rinst,rcs)) = all_simpl_cstr nmvs (inst,c:cs)


-- Standardizing apart
-- This is used in the beginning for standardizing apart the whole CNF.
standardize_apart :: (ExtendedSignature,[Metavariable],CNF) -> (ExtendedSignature,[Metavariable],CNF)
standardize_apart (((ps,fs,nvars),mvpart,sks,mvlinks),mvs,cnf) = (((ps,fs,standardize_nvars nclauses nvars),standardize_metavar_partition nclauses mvs mvpart,standardize_skolem_terms nclauses nvars mvs sks,compose_metavar_links (mvlinks ++ (generate_metavar_links nvars mvs nclauses))),standardize_metavars_l nclauses mvs,standardize_cnf nvars mvs cnf) where nclauses = length cnf

-- VERY IMPORTANT NOTE: We keep this just in case, but we do NOT need to do this. Meta-unification already considers standardization of variables. Because every new clause after resolution is always
-- going to have a unifier applied to it, there is no need to standardize them apart. We only standardize apart the whole CNF ONCE at the beginning.
-- This is used after each application of the resolution rule, to standardize apart the new clause.
-- Receives the original signature and meta-variables, the current signature and meta-variables, the new clause and the index of the clause (increased by 1 each time), and returns the new signature, meta-variables and clause.
standardize_new_clause :: (ExtendedSignature,[Metavariable]) -> Int -> (ExtendedSignature,[Metavariable],Clause) -> (ExtendedSignature,[Metavariable],Clause)
standardize_new_clause (((ops,ofs,onvars),omvpart,osks,mvlinks),omvs) iclause (((ps,fs,nvars),mvpart,sks,_),mvs,cl) = 
	(((ps,fs,standardize_nvars nclauses onvars),append_mvparts mvpart (standardize_metavar_partition_nth omvs omvpart iclause),sks ++ (map (standardize_term onvars omvs iclause) osks),compose_metavar_links (mvlinks ++ (generate_metavar_links onvars omvs nclauses))),standardize_metavars_l nclauses omvs,standardize_clause onvars omvs iclause cl)
	where nclauses = (iclause + 1)

-- generate_metavar_links :: Int -> [Metavariable] -> Int -> [MetavariableLink]
-- standardize_metavar_partition :: Int -> [Metavariable] -> MetavariablePartition -> MetavariablePartition
-- standardize_nvars :: Int -> Int -> Int
-- standardize_skolem_terms :: Int -> Int -> [Metavariable] -> [Term] -> [Term]
-- standardize_cnf :: Int -> [Metavariable] -> CNF -> CNF
-- append_mvparts :: MetavariablePartition -> MetavariablePartition -> MetavariablePartition
-- standardize_metavar_partition_nth :: [Metavariable] -> MetavariablePartition -> Int -> MetavariablePartition


-- type ExtendedSignature = (Signature,MetavariablePartition,[Term],[MetavariableLink])
-- type Signature = ([Predicate],[Function],Int)
-- type MetavariablePartition = ([[Metavariable]],Int,[Int])
-- type MetavariableLink = (Metavariable,[(Metavariable,Either Term Literal -> Either Term Literal)])

-- First argument is the number of clauses. Second is original number of variables.
standardize_nvars :: Int -> Int -> Int
standardize_nvars nclauses nvars = nclauses*nvars

-- First argument is the initial number of variables. Second is the index of the clause we're in (starting at zero). Third is the index of the variable and result is the new number of the variable.
standardize_vars_n :: Int -> Int -> Int -> Int
standardize_vars_n nvars iclause ivar = (mod ivar nvars) + iclause*nvars

standardize_vars :: Int -> Int -> Variable -> Variable
standardize_vars nvars iclause (Var ivar) = Var (standardize_vars_n nvars iclause ivar)

-- First argument is the number of clauses. Second is the original metavariables.
standardize_metavars_l :: Int -> [Metavariable] -> [Metavariable]
standardize_metavars_l nclauses mvs = foldl (\mvs -> \x -> mvs ++ (new_metavars mvs x)) mvs (replicate (nclauses - 1) mvs)

-- Here we assume that meta-variables start at 0, just like variables.
standardize_metavars :: [Metavariable] -> Int -> Metavariable -> Metavariable
standardize_metavars mvs iclause (Metavar imv) = Metavar ((mod imv nmvs) + iclause*nmvs) where nmvs = length mvs

-- First argument is the number of clauses. Second is the original metavariables.
standardize_metavar_partition :: Int -> [Metavariable] -> MetavariablePartition -> MetavariablePartition
standardize_metavar_partition nclauses mvs mvpart = foldl append_mvparts ([],0,[]) mvparts where mvparts = map (standardize_metavar_partition_nth mvs mvpart) [0..(nclauses-1)]

-- Specifically defined only when the number of initial variables is 0.
append_mvparts :: MetavariablePartition -> MetavariablePartition -> MetavariablePartition
append_mvparts (pmvs1,0,pnmvs1) (pmvs2,0,pnmvs2) = (pmvs1++pmvs2,0,pnmvs1++pnmvs2)

-- First argument is the initial meta-variables, second is the original partition, third is the index of the clause.
standardize_metavar_partition_nth :: [Metavariable] -> MetavariablePartition -> Int -> MetavariablePartition
standardize_metavar_partition_nth mvs (pmvs,ninit,pnmvs) iclause = ((map (standardize_metavars mvs iclause) mvs):(map (map (standardize_metavars mvs iclause)) pmvs),0,ninit:pnmvs)

-- In all (except the first) of the following functions, the first argument is the initial number of variables, the second is the list of original meta-variables and the third is the index of the clause we're in.
standardize_cnf :: Int -> [Metavariable] -> CNF -> CNF
standardize_cnf nvars mvs cnf = map (\iclause -> standardize_clause nvars mvs iclause (cnf !! iclause)) [0..(nclauses - 1)] where nclauses = length cnf

standardize_clause :: Int -> [Metavariable] -> Int -> Clause -> Clause
standardize_clause nvars mvs iclause = map (standardize_actualliteral nvars mvs iclause)

standardize_actualliteral :: Int -> [Metavariable] -> Int -> ActualLiteral -> ActualLiteral
standardize_actualliteral nvars mvs iclause (PosLit ml) = PosLit (standardize_metaliteral nvars mvs iclause ml)
standardize_actualliteral nvars mvs iclause (NegLit ml) = NegLit (standardize_metaliteral nvars mvs iclause ml)

standardize_metaliteral :: Int -> [Metavariable] -> Int -> Metaliteral -> Metaliteral
standardize_metaliteral nvars mvs iclause (MLitL l) = MLitL (standardize_literal nvars mvs iclause l)
standardize_metaliteral nvars mvs iclause (MLitR u ml) = MLitR u ml
standardize_metaliteral nvars mvs iclause (MLitP p mts) = MLitP p (map (standardize_metaterm nvars mvs iclause) mts)

standardize_metaterm :: Int -> [Metavariable] -> Int -> Metaterm -> Metaterm
standardize_metaterm nvars mvs iclause (MTermT t) = MTermT (standardize_term nvars mvs iclause t)
standardize_metaterm nvars mvs iclause (MTermR u mt) = MTermR u mt
standardize_metaterm nvars mvs iclause (MTermF f mts) = MTermF f (map (standardize_metaterm nvars mvs iclause) mts)

standardize_literal :: Int -> [Metavariable] -> Int -> Literal -> Literal
standardize_literal nvars mvs iclause (Lit p ts) = Lit p (map (standardize_term nvars mvs iclause) ts)
standardize_literal nvars mvs iclause (LitM mv) = LitM (standardize_metavars mvs iclause mv)

standardize_term :: Int -> [Metavariable] -> Int -> Term -> Term
standardize_term nvars mvs iclause (TVar v) = TVar (standardize_vars nvars iclause v)
standardize_term nvars mvs iclause (TMeta mv) = TMeta (standardize_metavars mvs iclause mv)
standardize_term nvars mvs iclause (TFun f ts) = TFun f (map (standardize_term nvars mvs iclause) ts)

-- First argument is number of clauses, second is number of initial variables, third is the list of original meta-variables.
standardize_skolem_terms :: Int -> Int -> [Metavariable] -> [Term] -> [Term]
standardize_skolem_terms nclauses nvars mvs sks = nub terms where
	per_clause = (\iclause -> map (standardize_term nvars mvs iclause) sks);
	terms = concat (map per_clause [0..(nclauses - 1)])

-- First argument is initial number of variables, second is the list of original meta-variables, third is the number of clauses.
generate_metavar_links :: Int -> [Metavariable] -> Int -> [MetavariableLink]
generate_metavar_links nvars mvs nclauses = all_links where 
	per_source_and_target_and_mv = (\s_iclause -> \mv -> \t_iclause -> (standardize_metavars mvs t_iclause mv,generate_metavar_link nvars mvs s_iclause t_iclause));
	per_source_and_mv = (\s_iclause -> \mv -> (standardize_metavars mvs s_iclause mv,map (per_source_and_target_and_mv s_iclause mv) (filter ((/=) s_iclause) [0..(nclauses - 1)])));
	per_source = (\s_iclause -> map (per_source_and_mv s_iclause) mvs);
	all_links = concat (map per_source [0..(nclauses - 1)])

-- Calculates the transitive closure of the meta-variable links, so that transitivity need not be taken into account when using them.
-- Note: We assume that the links are compatible. There is really no easy way to check this compatibility and what we are using this for should not create incompatibilities.
compose_metavar_links :: [MetavariableLink] -> [MetavariableLink]
compose_metavar_links ls = if cont then (compose_metavar_links once) else once where (once,cont) = compose_metavar_links_once ls ls

-- The bool indicates whether any new links were generated.
-- What we do is:
--	- For each source meta-variable X, take its target meta-variables Y, and for each of those:
--	- Check its target meta-variables Z. If there is any target Z of Y that is not also a target of X, add it with the composed link.
--	- If no new targets were found at all, return false.
compose_metavar_links_once :: [MetavariableLink] -> [MetavariableLink] -> ([MetavariableLink],Bool)
compose_metavar_links_once tot [] = (tot,False)
compose_metavar_links_once tot ((mv,ls):mvs) = (combine_metavar_links r rs,rfl || rsfl) where (r,rfl) = compose_metavar_links_once_helper tot mv ls; (rs,rsfl) = compose_metavar_links_once tot mvs

compose_metavar_links_once_helper :: [MetavariableLink] -> Metavariable -> [(Metavariable,(Either Term Literal -> Either Term Literal))] -> ([MetavariableLink],Bool)
compose_metavar_links_once_helper tot smv [] = ([],False)
compose_metavar_links_once_helper tot smv ((tmv,f):ls) = (combine_metavar_links [r] rs,rfl || rsfl) where (r,rfl) = compose_metavar_links_once_helper_2 tot smv tmv f; (rs,rsfl) = compose_metavar_links_once_helper tot smv ls

compose_metavar_links_once_helper_2 :: [MetavariableLink] -> Metavariable -> Metavariable -> (Either Term Literal -> Either Term Literal) -> (MetavariableLink,Bool)
compose_metavar_links_once_helper_2 tot smv tmv f = ((smv,result),not (null result)) where (_,links) = fromMaybe (Metavar 0,[]) (find (\(mv,ls) -> mv == tmv) tot); rs = map (\(mv,g) -> (mv,g . f)) links; (_,exist) = fromMaybe (Metavar 0,[]) (find (\(mv,ls) -> mv == smv) tot); result = filter (\(mv,l) -> (mv /= smv) && (not (any (\(mv2,l2) -> mv2 == mv) exist))) rs

combine_metavar_links :: [MetavariableLink] -> [MetavariableLink] -> [MetavariableLink]
combine_metavar_links [] ls2 = ls2
combine_metavar_links ((smv,ls):ls1) ls2 = deduplicate_metavar_links [] ((combine_metavar_links_helper smv ls ls2):(combine_metavar_links ls1 ls2))

-- Keep the first always, by construction it is more general.
deduplicate_metavar_links :: [Metavariable] -> [MetavariableLink] -> [MetavariableLink]
deduplicate_metavar_links _ [] = []
deduplicate_metavar_links mvs ((smv,ls):lss) | elem smv mvs = deduplicate_metavar_links mvs lss
deduplicate_metavar_links mvs ((smv,ls):lss) = (smv,ls):(deduplicate_metavar_links (smv:mvs) lss)

combine_metavar_links_helper :: Metavariable -> [(Metavariable,Either Term Literal -> Either Term Literal)] -> [MetavariableLink] -> MetavariableLink
combine_metavar_links_helper mv ls [] = (mv,ls)
combine_metavar_links_helper mv ls ((mv2,ls2):links) | mv == mv2 = (mv,ls++ls2)
combine_metavar_links_helper mv ls ((mv2,ls2):links) = combine_metavar_links_helper mv ls links

-- First argument is initial number of variables, second is the list of original meta-variables. The third and fourth are the source and target clause respectively. It generates the function itself.
generate_metavar_link :: Int -> [Metavariable] -> Int -> Int -> Either Term Literal -> Either Term Literal
generate_metavar_link nvars mvs s_iclause t_iclause (Left t) = Left (generate_metavar_link_term nvars mvs s_iclause t_iclause t)
generate_metavar_link nvars mvs s_iclause t_iclause (Right l) = Right (generate_metavar_link_literal nvars mvs s_iclause t_iclause l)

generate_metavar_link_literal :: Int -> [Metavariable] -> Int -> Int -> Literal -> Literal
generate_metavar_link_literal nvars mvs s_iclause t_iclause (Lit p ts) = Lit p (map (generate_metavar_link_term nvars mvs s_iclause t_iclause) ts)
generate_metavar_link_literal nvars mvs s_iclause t_iclause (LitM mv) = LitM (generate_metavar_link_metavar mvs s_iclause t_iclause mv)

generate_metavar_link_term :: Int -> [Metavariable] -> Int -> Int -> Term -> Term
generate_metavar_link_term nvars mvs s_iclause t_iclause (TVar v) = TVar (generate_metavar_link_var nvars s_iclause t_iclause v)
generate_metavar_link_term nvars mvs s_iclause t_iclause (TMeta mv) = TMeta (generate_metavar_link_metavar mvs s_iclause t_iclause mv)
generate_metavar_link_term nvars mvs s_iclause t_iclause (TFun f ts) = TFun f (map (generate_metavar_link_term nvars mvs s_iclause t_iclause) ts)

generate_metavar_link_metavar :: [Metavariable] -> Int -> Int -> Metavariable -> Metavariable
generate_metavar_link_metavar mvs s_iclause t_iclause (Metavar imv) | elem (Metavar imv) mvs = Metavar (imv + (t_iclause - s_iclause)*(length mvs))
generate_metavar_link_metavar mvs s_iclause t_iclause (Metavar imv) = Metavar imv

generate_metavar_link_var :: Int -> Int -> Int -> Variable -> Variable
generate_metavar_link_var nvars s_iclause t_iclause (Var ivar) = Var (ivar + (t_iclause - s_iclause)*nvars)




-- apply_resolution_rule :: Unifier -> Metaliteral -> Metaliteral -> Clause -> Clause -> (Constraint,Clause)
-- force_empty_clause :: ExtendedSignature -> (FullSolution,LogicalInstantiation) -> Unifier -> Metaliteral -> Metaliteral -> Clause -> Clause -> Maybe (FullSolution,LogicalInstantiation)
-- is_clause_deffo_valid :: Clause -> Bool
-- can_resolve_literals :: ActualLiteral -> ActualLiteral -> Bool
-- type FullSolution = ([Metavariable],[MetavariableEquation],UnifSolution,PartiallySolvedDGraph)
-- type UnifSolution = (Instantiation,[Constraint])
-- type PartiallySolvedDGraph = (DependencyGraph,DependencyGraphSolution,[UnifierEquation])

-- An enumeration of what literals to resolve with. An heuristic of what the best order to resolve is.
-- Receives the problem context (signature, current solution), the CNF, the index of the clause and index of the literal to solve.
-- Returns the indexes of clause and literal to resolve with.
type ResolventEnumeration h = ExtendedSignature -> (FullSolution,LogicalInstantiation) -> CNF -> Int -> Int -> Maybe (Enumeration (h,(Int,Int)))

-- A choice of what literal within a clause to try to resolve first. An heuristic of what the best order to resolve is. This is not an enumeration because each time we resolve we work with the resolvent, so the list of literals keeps changing.
-- ***IMPORTANT*** This chooses the positive literal. Negative literal is chosen via ResolventEnumeration. Choosing in this order may have limitations to heuristic potential, but it can in principle be worked out via choosing the clause and the literal in the clause in the right way. At least in part.
-- Receives the problem context (signature, current solution), the CNF and the index of the clause.
-- Returns the index of the literal in the clause to resolve.
-- It returns a list only in the case that the first one does not yield any solutions. It's a list of priorities. Once an element of the list yields some solutions, the rest of the elements of the list are discarded. Those literals will be dealt with in subsequent steps of resolution.
type InClauseLiteralChoice = ExtendedSignature -> (FullSolution,LogicalInstantiation) -> CNF -> Int -> [Int]

-- By default, just work on the next one (that is positive).
default_literal_choice :: ExtendedSignature -> (FullSolution,LogicalInstantiation) -> CNF -> Int -> [Int]
--default_literal_choice _ _ cnf iclause = filter (can_be_positive_lit_idx clause) [0..((length clause)-1)] where clause = cnf !! iclause
default_literal_choice _ _ cnf iclause = [0..((length clause) - 1)] where clause = cnf !! iclause

can_be_positive_lit_idx :: Clause -> Int -> Bool
can_be_positive_lit_idx cl idx = can_be_positive_lit (cl !! idx)

can_be_positive_lit :: ActualLiteral -> Bool
can_be_positive_lit (PosLit _) = True
can_be_positive_lit (NegLit l) = isJust (is_metavar_lit l)

can_be_negative_lit :: ActualLiteral -> Bool
can_be_negative_lit (NegLit _) = True
can_be_negative_lit (PosLit l) = isJust (is_metavar_lit l)

-- Choose which clause to start with resolving.
type ClauseEnumeration h = ExtendedSignature -> CNF -> Enumeration (h,Int)

type MetaresolutionHeuristic hresenum hclauseenum = (InClauseLiteralChoice,ResolventEnumeration hresenum,ClauseEnumeration hclauseenum,Int)

get_resenum :: MetaresolutionHeuristic hresenum _ -> ResolventEnumeration hresenum
get_resenum (_,x,_,_) = x

get_litchoice :: MetaresolutionHeuristic _ _ -> InClauseLiteralChoice
get_litchoice (x,_,_,_) = x

get_clauseenum :: MetaresolutionHeuristic _ hclauseenum -> ClauseEnumeration hclauseenum
get_clauseenum (_,_,x,_) = x

get_maxproofdepth :: MetaresolutionHeuristic _ _ -> Int
get_maxproofdepth (_,_,_,x) = x

trivial_clause_enum :: ClauseEnumeration _
trivial_clause_enum sig cnf = enum_from_list [0..((length cnf) - 1)]

default_metaresolution_heuristic :: MetaresolutionHeuristic _ _
default_metaresolution_heuristic = (default_literal_choice,(\sig -> \fsloginst -> choose_complementary_literal),trivial_clause_enum,9999999)


-- Here we keep the clause (1st parameter) and literal (2nd parameter) as indexes to avoid using the same and keeping good order of what we are doing.
-- In other words, here we are concerned about the search, not the semantics.
-- Returns an enumeration of clauses and literals that can be resolved with it.
-- The fixed literal is assumed to be the positive one. That is why we need to check backwards too.
choose_complementary_literal :: CNF -> Int -> Int -> Maybe (Enumeration (_,(Int,Int)))
choose_complementary_literal cnf iclause ilit = case aslist of {[] -> Nothing; otherwise -> Just (enum_from_list aslist)} where clause = cnf !! iclause; lit = clause !! ilit; aslist = choose_complementary_literal_helper cnf clause lit 0 0 (length cnf) (case cnf of {[] -> 0; (h:_) -> (length h)}) iclause

-- The first two integers are the current index of clause and literal that we are at, the last one is the clause which we are resolving with, to avoid it.
-- The next two integers are the length of the cnf and of the current clause, to avoid recalculating it every time.
choose_complementary_literal_helper :: CNF -> Clause -> ActualLiteral -> Int -> Int -> Int -> Int -> Int -> [(Int,Int)]
choose_complementary_literal_helper cnf clause lit ccl clit lcnf lclause bcl | ccl >= lcnf = []
choose_complementary_literal_helper cnf clause lit ccl clit lcnf lclause bcl | clit >= lclause = choose_complementary_literal_helper cnf clause lit (ccl+1) 0 lcnf (length (cnf !! (ccl+1))) bcl
choose_complementary_literal_helper cnf clause lit ccl clit lcnf lclause bcl | ccl == bcl = choose_complementary_literal_helper cnf clause lit (ccl+1) 0 lcnf (length (cnf !! (ccl+1))) bcl
choose_complementary_literal_helper cnf clause lit ccl clit lcnf lclause bcl | (can_resolve_literals lit plit) = (ccl,clit):(choose_complementary_literal_helper cnf clause lit ccl (clit+1) lcnf lclause bcl) where pclause = cnf !! ccl; plit = pclause !! clit
choose_complementary_literal_helper cnf clause lit ccl clit lcnf lclause bcl = choose_complementary_literal_helper cnf clause lit ccl (clit+1) lcnf lclause bcl

-- Maybe flips the literals if they can be flipped, and returns the two possible situations after stepping in each combination, both wrapped in Maybes.
mb_flip_step_with_complementary_literal :: ExtendedSignature -> (FullSolution,LogicalInstantiation,ResolutionProof) -> CNF -> Unifier -> Int -> Int -> Int -> Int -> (Maybe (Maybe (CNF,FullSolution,LogicalInstantiation,ResolutionProof),Maybe (FullSolution,LogicalInstantiation,ResolutionProof)),Maybe (Maybe (CNF,FullSolution,LogicalInstantiation,ResolutionProof),Maybe (FullSolution,LogicalInstantiation,ResolutionProof)))
mb_flip_step_with_complementary_literal sig (fs,loginst,proof) cnf u ipclause iplit inclause inlit = (one,two) where one = if ((can_be_positive_lit (cnf !! ipclause !! iplit)) && (can_be_negative_lit (cnf !! inclause !! inlit))) then (Just (step_with_complementary_literal sig (fs,loginst,proof) cnf u ipclause iplit inclause inlit)) else Nothing; two = if ((can_be_positive_lit (cnf !! inclause !! inlit)) && (can_be_negative_lit (cnf !! ipclause !! iplit))) then (Just (step_with_complementary_literal sig (fs,loginst,proof) cnf u inclause inlit ipclause iplit)) else Nothing

-- The four integers are clause, literal, clause, literal indexes. Positive first, then negative.
-- First pair is the minimal commitment solution. Second pair is the force empty clause solution, which need not be developed deeper.
-- The first pair is Nothing if it turns out the empty clause is found through least commitment (so no more search is needed).
-- The second pair is Nothing if the empty clause cannot be possibly found.
step_with_complementary_literal :: ExtendedSignature -> (FullSolution,LogicalInstantiation,ResolutionProof) -> CNF -> Unifier -> Int -> Int -> Int -> Int -> (Maybe (CNF,FullSolution,LogicalInstantiation,ResolutionProof),Maybe (FullSolution,LogicalInstantiation,ResolutionProof))
step_with_complementary_literal sig ((mvs,mveqs,(inst,cs),(g,gsol,ueqs)),loginst,proof) cnf u ipclause iplit inclause inlit = (rescont,maybe_empty_prop)
	where
	pclause = cnf !! ipclause; plit = pclause !! iplit; patom = get_atom plit; rempclause = pclause \\ [plit];
	nclause = cnf !! inclause; nlit = nclause !! inlit; natom = get_atom nlit; remnclause = nclause \\ [nlit];
	(newcstr,newcl,rsvloginst,rsvmvs,rpa,rna) = apply_resolution_rule_lits mvs loginst u plit nlit rempclause remnclause;
	(rmvs,(rinst,rcs)) = all_simpl_cstr rsvmvs (inst,newcstr:cs);
	parcfs = (rmvs,mveqs,(rinst,rcs),(g,gsol,ueqs));
	resfs = update_graph_with_constraints_and_propagate sig (rmvs,mveqs,(rinst,[]),(g,gsol,ueqs)) rcs;
--	resfs = (rmvs,mveqs,(rinst,[]),update_graph_with_constraints (g,gsol,ueqs) rcs);
	resfsprop = at_most_propagate sig resfs;
	rescnf = clean_deffo_cnf (apply_graph_solution_cnf_fs resfsprop (append_clause cnf newcl));
	resproof = (RStep pclause nclause plit nlit newcl cnf rescnf):proof;
	rescont = case newcl of {[] -> Nothing; _ -> Just (rescnf,resfsprop,rsvloginst,resproof)};
	maybe_empty = force_empty_clause sig (parcfs,rsvloginst) u rpa rna rempclause remnclause;
	maybe_empty_proof = (RStep pclause nclause plit nlit [] cnf cnf):proof;
	maybe_empty_full = maybe_apply (\(a,b) -> (a,b,maybe_empty_proof)) maybe_empty;
	maybe_empty_graph = update_constraints_in_graph_maybe_loginst sig maybe_empty_full;
	maybe_empty_prop = maybe_apply (apply_on_first_3 (at_most_propagate sig)) maybe_empty_graph

-- Saving this one because it worked, even if slowly. Adding the ability to pour unifier values back into the CNF
--step_with_complementary_literal :: ExtendedSignature -> (FullSolution,LogicalInstantiation,ResolutionProof) -> CNF -> Unifier -> Int -> Int -> Int -> Int -> (Maybe (CNF,FullSolution,LogicalInstantiation,ResolutionProof),Maybe (FullSolution,LogicalInstantiation,ResolutionProof))
--step_with_complementary_literal sig ((mvs,mveqs,(inst,cs),(g,gsol,ueqs)),loginst,proof) cnf u ipclause iplit inclause inlit = (rescont,maybe_empty_prop)
--	where
--	pclause = cnf !! ipclause; plit = pclause !! iplit; patom = get_atom plit; rempclause = pclause \\ [plit];
--	nclause = cnf !! inclause; nlit = nclause !! inlit; natom = get_atom nlit; remnclause = nclause \\ [nlit];
--	(newcstr,newcl) = apply_resolution_rule u patom natom rempclause remnclause;
--	(rmvs,(rinst,rcs)) = all_simpl_cstr mvs (inst,newcstr:cs);
--	parcfs = (rmvs,mveqs,(rinst,rcs),(g,gsol,ueqs));
--	resfs = update_graph_with_constraints_and_propagate sig (rmvs,mveqs,(rinst,[]),(g,gsol,ueqs)) rcs;
--	resfs = (rmvs,mveqs,(rinst,[]),update_graph_with_constraints (g,gsol,ueqs) rcs);
--	resfsprop = at_most_propagate sig resfs;
--	rescnf = clean_deffo_cnf (append_clause cnf newcl);
--	resproof = (RStep pclause nclause plit nlit newcl cnf rescnf):proof;
--	rescont = case newcl of {[] -> Nothing; _ -> Just (rescnf,resfsprop,loginst,resproof)};
--	maybe_empty = force_empty_clause sig (parcfs,loginst) u patom natom rempclause remnclause;
--	maybe_empty_proof = (RStep pclause nclause plit nlit [] cnf cnf):proof;
--	maybe_empty_full = maybe_apply (\(a,b) -> (a,b,maybe_empty_proof)) maybe_empty;
--	maybe_empty_graph = update_constraints_in_graph_maybe_loginst sig maybe_empty_full;
--	maybe_empty_prop = maybe_apply (apply_on_first_3 (at_most_propagate sig)) maybe_empty_graph

apply_graph_solution_actual_lit :: DependencyGraphSolution -> ActualLiteral -> ActualLiteral
apply_graph_solution_actual_lit sol (PosLit x) = PosLit (apply_graph_solution_lit_full sol x)
apply_graph_solution_actual_lit sol (NegLit x) = NegLit (apply_graph_solution_lit_full sol x)

apply_graph_solution_clause :: DependencyGraphSolution -> Clause -> Clause
apply_graph_solution_clause sol = map (apply_graph_solution_actual_lit sol)

apply_graph_solution_cnf :: DependencyGraphSolution -> CNF -> CNF
apply_graph_solution_cnf sol = map (apply_graph_solution_clause sol)

apply_graph_solution_cnf_fs :: FullSolution -> CNF -> CNF
apply_graph_solution_cnf_fs (_,_,_,(_,sol,_)) = apply_graph_solution_cnf sol

apply_inst_actual_lit :: Instantiation -> ActualLiteral -> ActualLiteral
apply_inst_actual_lit inst (PosLit x) = PosLit (apply_inst_mlit inst x)
apply_inst_actual_lit inst (NegLit x) = NegLit (apply_inst_mlit inst x)

apply_inst_clause :: Instantiation -> Clause -> Clause
apply_inst_clause inst cl = map (apply_inst_actual_lit inst) cl

apply_inst_cnf :: Instantiation -> CNF -> CNF
apply_inst_cnf inst cnf = map (apply_inst_clause inst) cnf

apply_substitution_actual_lit :: Int -> Unifier -> UnifierDescription -> ActualLiteral -> ActualLiteral
apply_substitution_actual_lit nvars u ud (PosLit x) = PosLit (apply_substitution_mlit nvars u ud x)
apply_substitution_actual_lit nvars u ud (NegLit x) = NegLit (apply_substitution_mlit nvars u ud x)

apply_substitution_clause :: Int -> Unifier -> UnifierDescription -> Clause -> Clause
apply_substitution_clause nvars u ud cl = map (apply_substitution_actual_lit nvars u ud) cl

apply_substitution_cnf :: Int -> Unifier -> UnifierDescription -> CNF -> CNF
apply_substitution_cnf nvars u ud cnf = map (apply_substitution_clause nvars u ud) cnf

update_constraints_in_graph_maybe_loginst :: ExtendedSignature -> Maybe (FullSolution,LogicalInstantiation,ResolutionProof) -> Maybe (FullSolution,LogicalInstantiation,ResolutionProof)
update_constraints_in_graph_maybe_loginst _ Nothing = Nothing
--update_constraints_in_graph_maybe_loginst (Just ((mvs,mveqs,(inst,cs),gsol),loginst)) = Just ((rmvs,mveqs,(rinst,[]),update_graph_with_constraints gsol rcs),loginst) where (rmvs,(rinst,rcs)) = all_simpl_cstr mvs (inst,cs)
update_constraints_in_graph_maybe_loginst sig (Just ((mvs,mveqs,(inst,cs),gsol),loginst,proof)) = Just (update_graph_with_constraints_and_propagate sig (rmvs,mveqs,(rinst,[]),gsol) rcs,loginst,proof) where (rmvs,(rinst,rcs)) = all_simpl_cstr mvs (inst,cs)

-- Dealing with recursive enumeration help types again...
-- Don't look here, ugly and semantically void stuff happening.
--data ProceedWithComplementaryLiteralHelp h1 = PWCLHBase | PWCLHRec (Either () (Either () ((((h1,PWCLHa),[((h1,PWCLHa),Enumerator (PWCLHh2 h1,PWCLHb),Int,(PWCLHh2 h1,PWCLHb))],[((h1,PWCLHa),Enumerator (PWCLHh2 h1,PWCLHb),Int,(PWCLHh2 h1,PWCLHb))]),(h1,PWCLHa)),PWCLHh2 h1)))

type PWCLHTypeHelper h1 h2 = (Either () (Either () ((((h1,PWCLHa),[((h1,PWCLHa),Enumerator (PWCLHh2 h1 h2,PWCLHb),Int,(PWCLHh2 h1 h2,PWCLHb))],[((h1,PWCLHa),Enumerator (PWCLHh2 h1 h2,PWCLHb),Int,(PWCLHh2 h1 h2,PWCLHb))]),(h1,PWCLHa)),PWCLHh2 h1 h2)))
--type PWCLHTypeHelper2 h1 h2 = ((((PWCLHTypeHelper h1 h2,Int),[((PWCLHTypeHelper h1 h2,Int),Enumerator (h2,Maybe (ProceedWithComplementaryLiteralHelp h1 h2,PWCLHb)),Int,(h2,Maybe (ProceedWithComplementaryLiteralHelp h1 h2,PWCLHb)))],[((PWCLHTypeHelper h1 h2,Int),Enumerator (h2,Maybe (ProceedWithComplementaryLiteralHelp h1 h2,PWCLHb)),Int,(h2,Maybe (ProceedWithComplementaryLiteralHelp h1 h2,PWCLHb)))]),(PWCLHTypeHelper h1 h2,Int)),h2)
--type PWCLHTypeHelper2 h1 h2 = ((((h2,Int),[((h2,Int),Enumerator (PWCLHTypeHelper h1 h2,PWCLHb),Int,(PWCLHTypeHelper h1 h2,PWCLHb))],[((h2,Int),Enumerator (PWCLHTypeHelper h1 h2,PWCLHb),Int,(PWCLHTypeHelper h1 h2,PWCLHb))]),(h2,Int)),PWCLHTypeHelper h1 h2)
data PWCLHTypeHelper3 h1 h2 = PWCLHBase | PWCLHRec (PWCLHTypeHelper h1 h2)

type ProceedWithComplementaryLiteralHelp h1 h2 = Diagonalizer Bool Bool (Either (PWCLHTypeHelper3 h1 h2) (PWCLHTypeHelper3 h1 h2)) PWCLHb
-- ((((h1,a),[((h1,a),Enumerator (h2,b),Int,(h2,b))],[((h1,a),Enumerator (h2,b),Int,(h2,b))]),(h1,a)),h2)
-- diagonalize_h :: (a -> Enumeration (h2,b)) -> Enumeration (h1,a) -> Enumeration (((((h1,a),[((h1,a),Enumerator (h2,b),Int,(h2,b))],[((h1,a),Enumerator (h2,b),Int,(h2,b))]),(h1,a)),h2),b)

type PWCLHa = (Int,Int)
type PWCLHb = Maybe (Int,FullSolution,LogicalInstantiation,ResolutionProof)
type PWCLHh2 h1 h2 = ProceedWithComplementaryLiteralHelp h1 h2

-- The integer in the enumeration is the index of the last unifier applied, used when solving the dependency graph.
proceed_with_complementary_literal :: MetaresolutionHeuristic hresenum hclauseenum -> ExtendedSignature -> (FullSolution,LogicalInstantiation,ResolutionProof) -> CNF -> Unifier -> Int -> Int -> Int -> Int -> Int -> Enumeration (ProceedWithComplementaryLiteralHelp hresenum hclauseenum,Maybe (Int,FullSolution,LogicalInstantiation,ResolutionProof))
proceed_with_complementary_literal heur _ _ _ _ _ _ _ _ depth | depth > (get_maxproofdepth heur) = concat_enums_h (Enum (PWCLHBase,Nothing) (\idx -> \x -> Nothing)) (Enum (PWCLHBase,Nothing) (\idx -> \x -> Nothing))
proceed_with_complementary_literal heur sig (fs,loginst,proof) cnf (U uidx) ipclause iplit inclause inlit depth = concat_enums_h re1 re2
	where
	(maybe_one,maybe_two) = mb_flip_step_with_complementary_literal sig (fs,loginst,proof) cnf (U uidx) ipclause iplit inclause inlit;
	(maybe_cont_one,maybe_empty_one) = fromJust maybe_one;
	(nextcnf_one,nextfs_one,nextloginst_one,nextproof_one) = fromJust maybe_cont_one;
	iclause_one = (length nextcnf_one) - 1;
	tocontinue_one = proceed_with_clause_choice heur sig (nextfs_one,nextloginst_one,nextproof_one) nextcnf_one (U (uidx + 1)) iclause_one (depth+1);
	(fh_one,fx_one) = case tocontinue_one of {Enum (xfh_one,xfx_one) _ -> (xfh_one,xfx_one)};
	e1 = case maybe_empty_one of
	{
		Nothing -> case maybe_cont_one of
		{
			Nothing -> Enum (PWCLHBase,Nothing) dont_proceed_with_complementary_literal_enumerator;
			Just _ -> Enum (PWCLHBase,Nothing) (proceed_with_complementary_literal_enumerator tocontinue_one)
--			Just _ -> Enum (PWCLHRec fh_one,fx_one) (proceed_with_complementary_literal_enumerator tocontinue_one)
		};
		Just (rfs_one,rloginst_one,rproof_one) -> case maybe_cont_one of
		{
			Nothing -> Enum (PWCLHBase,Just (uidx,rfs_one,rloginst_one,rproof_one)) dont_proceed_with_complementary_literal_enumerator;
			Just _ -> Enum (PWCLHBase,Just (uidx,rfs_one,rloginst_one,rproof_one)) (proceed_with_complementary_literal_enumerator tocontinue_one)
		}
	};
	re1 = case maybe_one of {Nothing -> Enum (PWCLHBase,Nothing) (\idx -> \x -> Nothing); Just _ -> e1};
	(maybe_cont_two,maybe_empty_two) = fromJust maybe_two;
	(nextcnf_two,nextfs_two,nextloginst_two,nextproof_two) = fromJust maybe_cont_two;
	iclause_two = (length nextcnf_two) - 1;
	tocontinue_two = proceed_with_clause_choice heur sig (nextfs_two,nextloginst_two,nextproof_two) nextcnf_two (U (uidx + 1)) iclause_two (depth+1);
	(fh_two,fx_two) = case tocontinue_two of {Enum (xfh_two,xfx_two) _ -> (xfh_two,xfx_two)};
	e2 = case maybe_empty_two of
	{
		Nothing -> case maybe_cont_two of
		{
			Nothing -> Enum (PWCLHBase,Nothing) dont_proceed_with_complementary_literal_enumerator;
			Just _ -> Enum (PWCLHBase,Nothing) (proceed_with_complementary_literal_enumerator tocontinue_two)
		};
		Just (rfs_two,rloginst_two,rproof_two) -> case maybe_cont_two of
		{
			Nothing -> Enum (PWCLHBase,Just (uidx,rfs_two,rloginst_two,rproof_two)) dont_proceed_with_complementary_literal_enumerator;
			Just _ -> Enum (PWCLHBase,Just (uidx,rfs_two,rloginst_two,rproof_two)) (proceed_with_complementary_literal_enumerator tocontinue_two)
		}
	};
	re2 = case maybe_two of {Nothing -> Enum (PWCLHBase,Nothing) (\idx -> \x -> Nothing); Just _ -> e2}

dont_proceed_with_complementary_literal_enumerator :: Int -> (PWCLHTypeHelper3 h1 h2,PWCLHb) -> Maybe (PWCLHTypeHelper3 h1 h2,PWCLHb)
dont_proceed_with_complementary_literal_enumerator _ _ = Nothing


proceed_with_complementary_literal_enumerator :: Enumeration ((PWCLHTypeHelper h1 h2),PWCLHb) -> Int -> (PWCLHTypeHelper3 h1 h2,PWCLHb) -> Maybe (PWCLHTypeHelper3 h1 h2,PWCLHb)
proceed_with_complementary_literal_enumerator (Enum (fh,fx) _) idx (PWCLHBase,_) = Just (PWCLHRec fh,fx)
proceed_with_complementary_literal_enumerator (Enum _ e) idx (PWCLHRec h,x) = case maybe of {Nothing -> Nothing; Just (rh,rx) -> Just (PWCLHRec rh,rx)} where maybe = e 0 (h,x)
-- We use 0 as index to explicitly indicate that we are not using indexes. If we were, this would be more complicated (still)
-- diagonalize_h :: (a -> Enumeration (h2,b)) -> Enumeration (h1,a) -> Enumeration (((((h1,a),[((h1,a),Enumerator (h2,b),Int,(h2,b))],[((h1,a),Enumerator (h2,b),Int,(h2,b))]),(h1,a)),h2),b)

--proceed_with_literal_choice :: MetaresolutionHeuristic hresenum hclauseenum -> ExtendedSignature -> (FullSolution,LogicalInstantiation) -> CNF -> Unifier -> Int -> Int -> Enumeration (Either () ((((hresenum,PWCLHa),[((hresenum,PWCLHa),Enumerator (PWCLHh2 hresenum,PWCLHb),Int,(PWCLHh2 hresenum,PWCLHb))],[((hresenum,PWCLHa),Enumerator (PWCLHh2 hresenum,PWCLHb),Int,(PWCLHh2 hresenum,PWCLHb))]),(hresenum,PWCLHa)),PWCLHh2 hresenum),Maybe (Int,FullSolution,LogicalInstantiation))
proceed_with_literal_choice :: MetaresolutionHeuristic hresenum hclauseenum -> ExtendedSignature -> (FullSolution,LogicalInstantiation,ResolutionProof) -> CNF -> Unifier -> Int -> Int -> Int -> Enumeration (Either () ((((hresenum,PWCLHa),[((hresenum,PWCLHa),Enumerator (PWCLHh2 hresenum hclauseenum,PWCLHb),Int,(PWCLHh2 hresenum hclauseenum,PWCLHb))],[((hresenum,PWCLHa),Enumerator (PWCLHh2 hresenum hclauseenum,PWCLHb),Int,(PWCLHh2 hresenum hclauseenum,PWCLHb))]),(hresenum,PWCLHa)),PWCLHh2 hresenum hclauseenum),Maybe (Int,FullSolution,LogicalInstantiation,ResolutionProof))
proceed_with_literal_choice heur sig (fs,loginst,proof) cnf u ipclause iplit depth = case pairenum of
	{
		Nothing -> enum_hleft_h enum_nothing_h;
		Just apairenum -> enum_hright_h (diagonalize_h (\cl -> proceed_with_literal_choice_helper heur sig (fs,loginst,proof) cnf u ipclause iplit cl depth) apairenum)
	}
	where resenum = get_resenum heur; pairenum = resenum sig (fs,loginst) cnf ipclause iplit

proceed_with_literal_choice_helper :: MetaresolutionHeuristic hresenum hclauseenum -> ExtendedSignature -> (FullSolution,LogicalInstantiation,ResolutionProof) -> CNF -> Unifier -> Int -> Int -> (Int,Int) -> Int -> Enumeration (ProceedWithComplementaryLiteralHelp hresenum hclauseenum,Maybe (Int,FullSolution,LogicalInstantiation,ResolutionProof))
proceed_with_literal_choice_helper heur sig fsinst cnf u ipclause iplit (inclause,inlit) depth = proceed_with_complementary_literal heur sig fsinst cnf u ipclause iplit inclause inlit depth

proceed_with_clause_choice :: MetaresolutionHeuristic hresenum hclauseenum -> ExtendedSignature -> (FullSolution,LogicalInstantiation,ResolutionProof) -> CNF -> Unifier -> Int -> Int -> Enumeration (Either () (Either () ((((hresenum,PWCLHa),[((hresenum,PWCLHa),Enumerator (PWCLHh2 hresenum hclauseenum,PWCLHb),Int,(PWCLHh2 hresenum hclauseenum,PWCLHb))],[((hresenum,PWCLHa),Enumerator (PWCLHh2 hresenum hclauseenum,PWCLHb),Int,(PWCLHh2 hresenum hclauseenum,PWCLHb))]),(hresenum,PWCLHa)),PWCLHh2 hresenum hclauseenum)),Maybe (Int,FullSolution,LogicalInstantiation,ResolutionProof))
proceed_with_clause_choice heur sig (fs,loginst,proof) cnf u ipclause depth = proceed_with_clause_choice_helper heur sig (fs,loginst,proof) cnf u ipclause plit_priorities depth
	where litchoice = get_litchoice heur; plit_priorities = litchoice sig (fs,loginst) cnf ipclause

proceed_with_clause_choice_helper :: MetaresolutionHeuristic hresenum hclauseenum -> ExtendedSignature -> (FullSolution,LogicalInstantiation,ResolutionProof) -> CNF -> Unifier -> Int -> [Int] -> Int -> Enumeration (Either () (Either () ((((hresenum,PWCLHa),[((hresenum,PWCLHa),Enumerator (PWCLHh2 hresenum hclauseenum,PWCLHb),Int,(PWCLHh2 hresenum hclauseenum,PWCLHb))],[((hresenum,PWCLHa),Enumerator (PWCLHh2 hresenum hclauseenum,PWCLHb),Int,(PWCLHh2 hresenum hclauseenum,PWCLHb))]),(hresenum,PWCLHa)),PWCLHh2 hresenum hclauseenum)),Maybe (Int,FullSolution,LogicalInstantiation,ResolutionProof))
proceed_with_clause_choice_helper heur sig (fs,loginst,proof) cnf u ipclause [] depth = enum_hleft_h enum_nothing_h
-- Just try the first one. Nothing else.
proceed_with_clause_choice_helper heur sig (fs,loginst,proof) cnf u ipclause (iplit:_) depth = enum_hright_h (proceed_with_literal_choice heur sig (fs,loginst,proof) cnf u ipclause iplit depth)
-- A bit ugly, but not that much. We try with the first literal suggested by the heuristic. We peek the solution to see if the first element of the enumeration is Nothing. If it is, bad luck, we try with the next literal. If it is not, then nice, we can throw the rest of the literal suggestions to the bin.
--proceed_with_clause_choice_helper heur sig (fs,loginst) cnf u ipclause (iplit:iplits) = if (isNothing (head (enum_up_to_h 1 pos_enum))) then (proceed_with_clause_choice_helper heur sig (fs,loginst) cnf u ipclause iplits) else enum_hright_h pos_enum where pos_enum = proceed_with_literal_choice heur sig (fs,loginst) cnf u ipclause iplit

start_with_clause_choice :: MetaresolutionHeuristic hresenum hclauseenum -> ExtendedSignature -> [Metavariable] -> CNF -> Int -> Enumeration (_,Maybe (Int,FullSolution,LogicalInstantiation,ResolutionProof))
start_with_clause_choice heur sig mvs cnf iclause = apply_enum_1_h reverse_proof (proceed_with_clause_choice heur sig (fs,loginst,proof) cnf u iclause 0)
	where
	fs = (mvs,[],(idinst,[]),(empty_graph,[],[]));
	loginst = idloginst;
	proof = [];
	u = (U 0)

reverse_proof :: Maybe (Int,FullSolution,LogicalInstantiation,ResolutionProof) -> Maybe (Int,FullSolution,LogicalInstantiation,ResolutionProof)
reverse_proof Nothing = Nothing
reverse_proof (Just (nus,fs,loginst,proof)) = (Just (nus,fs,loginst,reverse proof))

enumerate_constraint_systems :: MetaresolutionHeuristic hresenum hclauseenum -> ExtendedSignature -> [Metavariable] -> CNF -> Enumeration (_,Maybe (ExtendedSignature,Int,FullSolution,LogicalInstantiation,ResolutionProof))
enumerate_constraint_systems heur sig mvs cnf = finalenum
	where
	(std_sig,std_mvs,std_cnf) = standardize_apart (sig,mvs,cnf);
	clauseenum = get_clauseenum heur std_sig std_cnf;
-- Maybe here I would rather go all in with a particular initial clause choice, rather than diagonalizing, but for now we do diagonalize. Many things to be thought about this later on.
	fsolenum = diagonalize_h (start_with_adapted_clause_choice heur std_sig std_mvs) (adapt_cnf_from_clause_choice std_cnf clauseenum);
	finalenum = apply_enum_1_h ((enumerate_constraint_systems_transform std_sig) . (enumerate_constraint_systems_compose_loginst_inst std_sig)) fsolenum

start_with_adapted_clause_choice :: MetaresolutionHeuristic hresenum hclauseenum -> ExtendedSignature -> [Metavariable] -> (Int -> Int,CNF,Int) -> Enumeration (_,Maybe (Int,FullSolution,LogicalInstantiation,ResolutionProof))
start_with_adapted_clause_choice heur sig mvs (ad,cnf,iclause) = start_with_clause_choice heur sig mvs cnf (ad iclause)

-- We remove the clause that we chose from the CNF, and also from next choices of clauses. This is to avoid duplication of proofs.
adapt_cnf_from_clause_choice :: CNF -> Enumeration (h,Int) -> Enumeration (h,(Int -> Int,CNF,Int))
adapt_cnf_from_clause_choice cnf (Enum (h0,i0) nexti) = Enum (h0,(id,cnf,i0)) (adapt_cnf_from_clause_choice_enum nexti)

adapt_cnf_from_clause_choice_enum :: Enumerator (h,Int) -> Enumerator (h,(Int -> Int,CNF,Int))
adapt_cnf_from_clause_choice_enum nexti idx (ph,(ad,pcnf,pi)) = case nhi of {Nothing -> Nothing; Just (nh,ni) -> Just (nh,((adapt_index_removed (ad pi)) . ad,pcnf \\ [(pcnf !! (ad pi))],ni))} where nhi = nexti idx (ph,pi)

adapt_index_removed :: Int -> Int -> Int
adapt_index_removed r i | i > r = i-1
adapt_index_removed r i | i < r = i
-- Purposely leave out the i == r case. This should be an error.

-- diagonalize_h :: (a -> Enumeration (h2,b)) -> Enumeration (h1,a) -> Enumeration (((((h1,a),[((h1,a),Enumerator (h2,b),Int,(h2,b))],[((h1,a),Enumerator (h2,b),Int,(h2,b))]),(h1,a)),h2),b)
-- apply_enum_1_h :: (a -> b) -> Enumeration (h1,a) -> Enumeration ((h1,a),b)

enumerate_constraint_systems_compose_loginst_inst :: ExtendedSignature -> Maybe (Int,FullSolution,LogicalInstantiation,ResolutionProof) -> Maybe (Int,FullSolution,LogicalInstantiation,ResolutionProof)
enumerate_constraint_systems_compose_loginst_inst _ Nothing = Nothing
enumerate_constraint_systems_compose_loginst_inst sig (Just (nus,(mvs,mveqs,(inst,cs),gsol),loginst,proof)) = case mb_loginst of {Nothing -> Nothing; Just rloginst -> Just (nus,(mvs,mveqs,(inst,cs),gsol),rloginst,proof)} where mb_loginst = restore_consistency_metavar_links_loginsts (get_metavar_links sig) (Just (compose_loginst_inst inst loginst))

enumerate_constraint_systems_transform :: ExtendedSignature -> Maybe (Int,FullSolution,LogicalInstantiation,ResolutionProof) -> Maybe (ExtendedSignature,Int,FullSolution,LogicalInstantiation,ResolutionProof)
enumerate_constraint_systems_transform _ Nothing = Nothing
enumerate_constraint_systems_transform sig (Just (nus,fs,loginst,proof)) = Just (sig,nus,fs,loginst,proof)

solve_resolution_gen_constraints :: MetaunificationHeuristic hl ht -> (ExtendedSignature,Int,FullSolution,LogicalInstantiation,ResolutionProof) -> (ExtendedSignature,Maybe LogicalInstantiation,[Unifier],ResolutionProof,FullSolution,Enumeration (_,Maybe ([UnifierDescription],Instantiation)))
solve_resolution_gen_constraints heur (sig,nus,fs,loginst,proof) = (sig,(Just loginst),us,proof,fs,enum_maybe_filter_h is_solution_satisfiable (apply_enum_1_h solve_resolution_gen_constraints_validate_insts (apply_enum_1_h (solve_resolution_gen_constraints_restore_consistency_unifs (get_metavar_links sig)) (diagonalize_h (\rfs -> case rfs of {Nothing -> enum_hleft_h empty_enum_mb_h; Just irfs -> enum_hright_h (instantiation_from_dgraph_sol sig irfs us)}) fsols_consistent))))
-- We restore consistency over logical instantiation later because we first need to apply the instantiation to the logical instantiation, or otherwise some weird shit may happen with newly generated meta-variables appearing in meta-variables that need to restore consistency (indexes becoming negative or weird, or meta-variable links not being applied properly).
--solve_resolution_gen_constraints heur (sig,nus,fs,loginst,proof) = (restore_consistency_metavar_links_loginsts (get_metavar_links sig) (Just loginst),us,proof,fs,enum_maybe_filter_h is_solution_satisfiable (apply_enum_1_h solve_resolution_gen_constraints_validate_insts (apply_enum_1_h (solve_resolution_gen_constraints_restore_consistency_unifs (get_metavar_links sig)) (diagonalize_h (\rfs -> case rfs of {Nothing -> enum_hleft_h empty_enum_mb_h; Just irfs -> enum_hright_h (instantiation_from_dgraph_sol sig irfs us)}) fsols_consistent))))
	where
	fsols = enumerate_and_propagate_all heur sig fs;
	fsols_consistent = apply_enum_1_h (restore_consistency_metavar_links sig (get_metavar_links sig)) fsols;
--	fsols_only_consistent = apply_enum_1_h fromJust_special (enum_filter_h isJust fsols_consistent);
	us = map U [0..nus]

-- I hate myself
-- Update: I hate you too.
empty_enum_mb :: Enumeration (Maybe t)
empty_enum_mb = Enum Nothing (\idx -> \x -> Nothing)

empty_enum_mb_h :: Enumeration (_,Maybe t)
empty_enum_mb_h = no_help empty_enum_mb

fromJust_special :: Maybe (Maybe t) -> Maybe t
fromJust_special (Just x) = x
fromJust_special Nothing = Nothing

solve_resolution_gen_constraints_restore_consistency_unifs :: [MetavariableLink] -> Maybe ([UnifierDescription],Instantiation) -> Maybe ([UnifierDescription],Instantiation)
solve_resolution_gen_constraints_restore_consistency_unifs _ Nothing = Nothing
solve_resolution_gen_constraints_restore_consistency_unifs links (Just (uds,inst)) = case parc of {Nothing -> Nothing; Just rinst -> Just (uds,rinst)} where parc = restore_consistency_metavar_links_insts links (Just inst)

solve_resolution_gen_constraints_validate_insts :: Maybe ([UnifierDescription],Instantiation) -> Maybe ([UnifierDescription],Instantiation)
solve_resolution_gen_constraints_validate_insts Nothing = Nothing
--solve_resolution_gen_constraints_validate_insts (Just (uds,inst)) = (Just (uds,inst))
solve_resolution_gen_constraints_validate_insts (Just (uds,inst)) = case validated of {Nothing -> Nothing; Just rinst -> Just (uds,rinst)} where validated = most_instantiated_all (clean_dups_inst inst)

-- restore_consistency_metavar_links :: [MetavariableLink] -> FullSolution -> Maybe FullSolution
-- restore_consistency_metavar_links_insts :: [MetavariableLink] -> Maybe Instantiation -> Maybe Instantiation

-- All in one: Composes instantiation with logical instantiation, but only after verifying they are compatible, and then also restores consistency through metavariable links on the logical instantiation.
-- Potentially in the future we could also restore consistency over the instantiation itself if it was necessary, and check compatibility between instantiation and logical instantiation better than simply "there's not a value in each", although I don't see how this would be possible (???)
restore_consistency_metavar_links_loginsts_inst :: [Metavariable] -> [MetavariableLink] -> Instantiation -> LogicalInstantiation -> Maybe LogicalInstantiation
restore_consistency_metavar_links_loginsts_inst mvs mvlinks inst loginst = if (compatible_inst_loginst loginst inst mvs) then (restore_consistency_metavar_links_loginsts mvlinks (Just (compose_loginst_inst inst loginst))) else Nothing

restore_consistency_metavar_links_loginsts :: [MetavariableLink] -> Maybe LogicalInstantiation -> Maybe LogicalInstantiation
restore_consistency_metavar_links_loginsts _ Nothing = Nothing
restore_consistency_metavar_links_loginsts [] (Just loginst) = Just loginst
restore_consistency_metavar_links_loginsts ((smv,ls):rs) (Just loginst) = restore_consistency_metavar_links_loginsts rs (restore_consistency_metavar_links_loginsts_rec smv ls (Just loginst))

restore_consistency_metavar_links_loginsts_rec :: Metavariable -> [(Metavariable,Either Term Literal -> Either Term Literal)] -> Maybe LogicalInstantiation -> Maybe LogicalInstantiation
restore_consistency_metavar_links_loginsts_rec _ _ Nothing = Nothing
restore_consistency_metavar_links_loginsts_rec _ [] (Just loginst) = Just loginst
restore_consistency_metavar_links_loginsts_rec smv ((tmv,f):rs) (Just loginst) = restore_consistency_metavar_links_loginsts_rec smv rs (most_instantiated_logical_inst tmv smv f (Just loginst))

most_instantiated_logical :: Formula -> Formula -> Maybe Formula
most_instantiated_logical (FLit l1) (FLit l2) = case rl of {Just (Right rrl) -> Just (FLit rrl); _ -> Nothing} where rl = most_instantiated (Right l1) (Right l2)
most_instantiated_logical (FNeg f1) (FNeg f2) = maybe_apply FNeg (most_instantiated_logical f1 f2)
most_instantiated_logical (FNeg f1) (FLit (LitM _)) = Just (FNeg f1)
most_instantiated_logical (FNeg f1) (FLit _) = Nothing
most_instantiated_logical (FLit l1) (FNeg f2) = most_instantiated_logical (FNeg f2) (FLit l1)
most_instantiated_logical (FNeg f1) _ = Nothing
most_instantiated_logical _ (FNeg f2) = Nothing
most_instantiated_logical (FAnd f11 f12) (FAnd f21 f22) = if ((isJust r1) && (isJust r2)) then (Just (FAnd (fromJust r1) (fromJust r2))) else Nothing where r1 = most_instantiated_logical f11 f21; r2 = most_instantiated_logical f12 f22
most_instantiated_logical (FAnd f11 f12) (FLit (LitM _)) = Just (FAnd f11 f12)
most_instantiated_logical (FAnd f11 f12) (FLit _) = Nothing
most_instantiated_logical (FLit l1) (FAnd f21 f22) = most_instantiated_logical (FAnd f21 f22) (FLit l1)
most_instantiated_logical (FAnd f11 f12) _ = Nothing
most_instantiated_logical _ (FAnd f21 f22) = Nothing
most_instantiated_logical (FOr f11 f12) (FOr f21 f22) = if ((isJust r1) && (isJust r2)) then (Just (FOr (fromJust r1) (fromJust r2))) else Nothing where r1 = most_instantiated_logical f11 f21; r2 = most_instantiated_logical f12 f22
most_instantiated_logical (FOr f11 f12) (FLit (LitM _)) = Just (FOr f11 f12)
most_instantiated_logical (FOr f11 f12) (FLit _) = Nothing
most_instantiated_logical (FLit l1) (FOr f21 f22) = most_instantiated_logical (FOr f21 f22) (FLit l1)
most_instantiated_logical (FOr f11 f12) _ = Nothing
most_instantiated_logical _ (FOr f11 f12) = Nothing

-- Lifts to logical instantiations.
lift_metavar_link :: (Either Term Literal -> Either Term Literal) -> (Formula -> Formula)
-- Here we assume that both are literals. If not, just use the literal as is (slightly dangerous)
lift_metavar_link f (FLit l) = FLit (fromRight l (f (Right l)))
lift_metavar_link f (FNeg sf) = FNeg (lift_metavar_link f sf)
lift_metavar_link f (FAnd sf1 sf2) = FAnd (lift_metavar_link f sf1) (lift_metavar_link f sf2)
lift_metavar_link f (FOr sf1 sf2) = FOr (lift_metavar_link f sf1) (lift_metavar_link f sf2)

apply_loginst :: LogicalInstantiation -> Metavariable -> Maybe Formula
apply_loginst loginst mv = if (r /= (FLit (LitM mv))) then (Just r) else Nothing where r = loginst mv

most_instantiated_logical_inst :: Metavariable -> Metavariable -> (Either Term Literal -> Either Term Literal) -> Maybe LogicalInstantiation -> Maybe LogicalInstantiation
most_instantiated_logical_inst _ _ _ Nothing = Nothing
most_instantiated_logical_inst tmv smv f (Just loginst) = case nv of {Nothing -> Just loginst; Just f1 -> case ov of {Nothing -> Just (set_loginst loginst tmv (lift_metavar_link f f1)); Just f2 -> case (most_instantiated_logical f2 (lift_metavar_link f f1)) of {Nothing -> Nothing; Just rf -> Just (set_loginst loginst tmv rf)}}}  
	where 
	nv = apply_loginst loginst smv;
	ov = apply_loginst loginst tmv;	

enumerate_cnf_unsat_instantiations :: MetaresolutionHeuristic hrersenum hclauseenum -> MetaunificationHeuristic hl ht -> ExtendedSignature -> [Metavariable] -> CNF -> Enumeration (_,Maybe (LogicalInstantiation,[Unifier],ResolutionProof,FullSolution,[UnifierDescription],Instantiation))
enumerate_cnf_unsat_instantiations resheur unifheur sig mvs cnf = enum_filter_h isJust sols
	where
	ecstrsys = enumerate_constraint_systems resheur sig mvs cnf;
	sols = diagonalize_h ((enumerate_cnf_unsat_instantiations_transform_2 mvs) . (maybe_apply (solve_resolution_gen_constraints unifheur))) ecstrsys

-- DEPRECATED
--enumerate_cnf_unsat_instantiations_filter :: [Metavariable] -> Maybe (LogicalInstantiation,[Unifier],ResolutionProof,FullSolution,[UnifierDescription],Instantiation) -> Bool
--enumerate_cnf_unsat_instantiations_filter _ Nothing = False
--enumerate_cnf_unsat_instantiations_filter mvs (Just (loginst,_,_,_,_,inst)) = compatible_inst_loginst loginst inst mvs

enumerate_cnf_unsat_instantiations_transform :: ExtendedSignature -> [Metavariable] -> LogicalInstantiation -> [Unifier] -> ResolutionProof -> FullSolution -> Maybe ([UnifierDescription],Instantiation) -> Maybe (LogicalInstantiation,[Unifier],ResolutionProof,FullSolution,[UnifierDescription],Instantiation)
enumerate_cnf_unsat_instantiations_transform _ _ _ _ _ _ Nothing = Nothing
-- We also take this chance here to compose logical instantiation with instantiation and restore consistency on the logical instantiation
enumerate_cnf_unsat_instantiations_transform sig mvs loginst us proof fs (Just (uds,inst)) = case mbrloginst of {Nothing -> Nothing; Just rloginst -> Just (rloginst,us,proof,fs,uds,inst)} where mbrloginst = restore_consistency_metavar_links_loginsts_inst mvs (get_metavar_links sig) inst loginst

enumerate_cnf_unsat_instantiations_transform_2 :: [Metavariable] -> Maybe (ExtendedSignature, Maybe LogicalInstantiation,[Unifier],ResolutionProof,FullSolution,Enumeration (t,Maybe ([UnifierDescription],Instantiation))) -> Enumeration (_,Maybe (LogicalInstantiation,[Unifier],ResolutionProof,FullSolution,[UnifierDescription],Instantiation))
enumerate_cnf_unsat_instantiations_transform_2 _ Nothing = enum_hleft_h enum_nothing_h
enumerate_cnf_unsat_instantiations_transform_2 _ (Just (_,Nothing,_,_,_,_)) = enum_hleft_h enum_nothing_h
enumerate_cnf_unsat_instantiations_transform_2 mvs (Just (sig,Just loginst,us,proof,fs,e)) = enum_hright_h (apply_enum_1_h (enumerate_cnf_unsat_instantiations_transform sig mvs loginst us proof fs) e)

-- DEPRECATED
--enumerate_cnf_unsat_instantiations_transform_3 :: ExtendedSignature -> Maybe (LogicalInstantiation,[Unifier],ResolutionProof,FullSolution,[UnifierDescription],Instantiation) -> Maybe (LogicalInstantiation,[Unifier],ResolutionProof,FullSolution,[UnifierDescription],Instantiation)
--enumerate_cnf_unsat_instantiations_transform_3 _ Nothing = Nothing
--enumerate_cnf_unsat_instantiations_transform_3 sig (Just (loginst,us,pr,fs,uds,inst)) = if (isJust mb_loginst) then (Just (fromJust mb_loginst,us,pr,fs,uds,inst)) else Nothing where mb_loginst = restore_consistency_metavar_links_loginsts (get_metavar_links sig) (Just (compose_loginst_inst inst loginst))


-- Filter multiple proofs with the same instantiation
-- Warning: O(n^2)
filter_repeated_insts :: [Metavariable] -> Enumeration (t,Maybe (LogicalInstantiation,[Unifier],ResolutionProof,FullSolution,[UnifierDescription],Instantiation)) -> Enumeration ((t,[Maybe (LogicalInstantiation,[Unifier],ResolutionProof,FullSolution,[UnifierDescription],Instantiation)]),Maybe (LogicalInstantiation,[Unifier],ResolutionProof,FullSolution,[UnifierDescription],Instantiation))
filter_repeated_insts mvs (Enum (hstart,xstart) en) = Enum ((hstart,[xstart]),xstart) (\idx -> filter_repeated_insts_helper mvs en idx)

filter_repeated_insts_helper :: [Metavariable] -> Enumerator (t,Maybe (LogicalInstantiation,[Unifier],ResolutionProof,FullSolution,[UnifierDescription],Instantiation)) -> Int -> ((t,[Maybe (LogicalInstantiation,[Unifier],ResolutionProof,FullSolution,[UnifierDescription],Instantiation)]),Maybe (LogicalInstantiation,[Unifier],ResolutionProof,FullSolution,[UnifierDescription],Instantiation)) -> Maybe ((t,[Maybe (LogicalInstantiation,[Unifier],ResolutionProof,FullSolution,[UnifierDescription],Instantiation)]),Maybe (LogicalInstantiation,[Unifier],ResolutionProof,FullSolution,[UnifierDescription],Instantiation))
filter_repeated_insts_helper mvs en idx ((h,prevs),x) = case mb_next of {Nothing -> Nothing; Just (hnext,xnext) -> if (any (eq_insts_sols mvs xnext) prevs) then (filter_repeated_insts_helper mvs en idx ((hnext,prevs),xnext)) else (Just ((hnext,xnext:prevs),xnext))} where mb_next = en idx (h,x)

eq_insts_sols :: [Metavariable] -> Maybe (LogicalInstantiation,[Unifier],ResolutionProof,FullSolution,[UnifierDescription],Instantiation) -> Maybe (LogicalInstantiation,[Unifier],ResolutionProof,FullSolution,[UnifierDescription],Instantiation) -> Bool
eq_insts_sols mvs Nothing Nothing = True
eq_insts_sols mvs Nothing _ = False
eq_insts_sols mvs _ Nothing = False
eq_insts_sols mvs (Just (loginst1,_,_,_,_,inst1)) (Just (loginst2,_,_,_,_,inst2)) = (eq_inst_mvs mvs inst1 inst2) && (eq_loginst mvs loginst1 loginst2)


-- A proof data type to log the actual proof.
data ResolutionStep = RStep Clause Clause ActualLiteral ActualLiteral Clause CNF CNF

show_resolution_step :: UnifierDescription -> ResolutionStep -> String
show_resolution_step ud (RStep pcl ncl plit nlit [] ocnf rcnf) = "---> Resolve positive literal " ++ (show plit) ++ " in clause " ++ (show pcl) ++ "\nwith negative literal " ++ (show nlit) ++ " in clause " ++ (show ncl) ++ "\nof CNF\n" ++ (show ocnf) ++ "\n, with unifier\n" ++ (show ud) ++ " to obtain the empty clause.\n\n"
show_resolution_step ud (RStep pcl ncl plit nlit res ocnf rcnf) = "---> Resolve positive literal " ++ (show plit) ++ " in clause " ++ (show pcl) ++ "\nwith negative literal " ++ (show nlit) ++ " in clause " ++ (show ncl) ++ "\nof CNF\n" ++ (show ocnf) ++ "\n, with unifier\n" ++ (show ud) ++ " to obtain resolvent\n" ++ (show res) ++ "\nand resulting CNF\n" ++ (show rcnf) ++ ".\n\n"

type ResolutionProof = [ResolutionStep]

show_resolution_proof :: [UnifierDescription] -> ResolutionProof -> String
show_resolution_proof [] [] = "Done."
show_resolution_proof (ud:uds) (st:sts) = (show_resolution_step ud st) ++ (show_resolution_proof uds sts)


show_unsat_instantiation :: ExtendedSignature -> [Metavariable] -> Maybe (LogicalInstantiation,[Unifier],ResolutionProof,FullSolution,[UnifierDescription],Instantiation) -> String
show_unsat_instantiation _ _ Nothing = "Unsatisfiable"
show_unsat_instantiation sig mvs (Just (loginst,us,proof,fs,uds,inst)) = (show_loginst loginst mvs) ++ "\nand\n" ++ (show_inst inst mvs) ++ "\nwith\n" ++ (show_unifs us uds) ++ "\nwith proof:\n" ++ (show_resolution_proof uds proof) ++ "\nwhere the dependency graph before finishing meta-unification looked like this:\n" ++ (full_soln_str fs) ++ "\n"

show_unifs :: [Unifier] -> [UnifierDescription] -> String
show_unifs [] [] = ""
show_unifs (u:us) (ud:uds) = (show u) ++ ": " ++ (show ud) ++ "\n" ++ (show_unifs us uds)
-- Just for debugging
show_unifs [] (ud:uds) = "(Unknown unifier): " ++ (show ud) ++ "\n" ++ (show_unifs [] uds)
--show_unifs (u:us) [] = (show u) ++ ": []\n" ++ (show_unifs us [])
show_unifs (u:us) [] = "Unsatisfiable.\n"

show_nth_unsat_instantiation :: ExtendedSignature -> [Metavariable] -> Enumeration (t,Maybe (LogicalInstantiation,[Unifier],ResolutionProof,FullSolution,[UnifierDescription],Instantiation)) -> Int -> IO ()
show_nth_unsat_instantiation sig mvs en i = putStr (show_unsat_instantiation sig mvs ((enum_up_to_h i en) !! i))

infinity :: Int
infinity = 99999999999999999

show_all_unsat_instantiations :: ExtendedSignature -> [Metavariable] -> Enumeration (t,Maybe (LogicalInstantiation,[Unifier],ResolutionProof,FullSolution,[UnifierDescription],Instantiation)) -> IO ()
show_all_unsat_instantiations sig mvs en = foldr (>>) (putStr "") (map (\pair -> (putStr ("Solution #" ++ (show (fst pair)) ++ ":\n")) >> (putStr (show_unsat_instantiation sig mvs (snd pair))) >> (putStr "\n")) (zip [0..infinity] (enum_up_to_h infinity en)))

show_n_unsat_instantiations :: ExtendedSignature -> [Metavariable] -> Enumeration (t,Maybe (LogicalInstantiation,[Unifier],ResolutionProof,FullSolution,[UnifierDescription],Instantiation)) -> Int -> IO ()
show_n_unsat_instantiations sig mvs en n = foldr (>>) (putStr "") (map (\pair -> (putStr ("Solution #" ++ (show (fst pair)) ++ ":\n")) >> (putStr (show_unsat_instantiation sig mvs (snd pair))) >> (putStr "\n")) (zip [0..n] (enum_up_to_h n en)))
