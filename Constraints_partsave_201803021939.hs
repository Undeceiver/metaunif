-- Put everything together, after solving the graph.
-- t = [Unifier] => IMPORTANT: We hand in the unifiers in the opposite order so that the inner-most, which is the first to be processed, is the first.
-- r = (([UnifierDescription],Instantiation),[Either (Metaterm,Term) (Metaliteral,Literal)])
instantiation_from_dgraph_sol :: Signature -> FullSolution -> [Unifier] -> Enumeration (_,([UnifierDescription],Instantiation))
instantiation_from_dgraph_sol sig fs us = apply_enum_1_h fst (recursively_diagonalize_h (instantiation_from_dgraph_sol_step sig fs) (reverse us))

instantiation_from_dgraph_sol_step :: Signature -> FullSolution -> [Unifier] -> Either ([(([UnifierDescription],Instantiation),[Either (Metaterm,Term) (Metaliteral,Literal)])] -> Enumeration (_,(([UnifierDescription],Instantiation),[Either (Metaterm,Term) (Metaliteral,Literal)]))) ([Unifier],([(([UnifierDescription],Instantiation),[Either (Metaterm,Term) (Metaliteral,Literal)])] -> Enumeration (_,(([UnifierDescription],Instantiation),[Either (Metaterm,Term) (Metaliteral,Literal)])),CombinationScheme ((([UnifierDescription],Instantiation),[Either (Metaterm,Term) (Metaliteral,Literal)]))))
instantiation_from_dgraph_sol_step sig (mvs,eqs,(inst,cs),(g,sol,ueqs)) [] = Left (\prevs -> enum_hleft_h (no_help (single_enum (([],inst),curated_sol)))) where curated_sol = translate_dgraph_sol_pairs sol
instantiation_from_dgraph_sol_step sig fs (u:us) = Right (us,(\prevs -> enum_hright_h (instantiation_from_dgraph_sol_step_helper sig fs u prevs),Comb instantiation_from_dgraph_sol_comb_helper instantiation_from_dgraph_sol_decomb_helper))

-- We only care about the last step to calculate the next.
instantiation_from_dgraph_sol_step_helper :: Signature -> FullSolution -> Unifier -> [(([UnifierDescription],Instantiation),[Either (Metaterm,Term) (Metaliteral,Literal)])] -> Enumeration (_,((([UnifierDescription],Instantiation),[Either (Metaterm,Term) (Metaliteral,Literal)])))
instantiation_from_dgraph_sol_step_helper (ps,fs,nvars) (mvs,eqs,(inst,cs),(g,sol,ueqs)) u (((uds,previnst),l):_) = all_together
	where min_ud = build_minimal_unif_desc u l;
		with_metavars = invert_metavar_dependents nvars eqs u l min_ud;
		filtered_consistent = enum_filter_h (\pair -> is_unif_desc_consistent (fst pair)) with_metavars;
		composed_inst = apply_enum_1_h (\pair -> (fst pair,compose_inst (snd pair) previnst)) filtered_consistent;
		inst_clean_subst = apply_enum_1_h (instantiation_from_dgraph_sol_step_helper_2 (ps,fs,nvars) u l) composed_inst;
		all_together = apply_enum_1_h (instantiation_from_dgraph_sol_step_helper_3 uds) inst_clean_subst
		

instantiation_from_dgraph_sol_step_helper_2 :: Signature -> Unifier -> [Either (Metaterm,Term) (Metaliteral,Literal)] -> (UnifierDescription,Instantiation) -> ((UnifierDescription,Instantiation),[Either (Metaterm,Term) (Metaliteral,Literal)])
instantiation_from_dgraph_sol_step_helper_2 (ps,fs,nvars) u l (ud,inst) = ((ud,inst),substitute_unifier nvars u ud (clean_output_from_graph u (instantiate_all_possible_metavars inst l)))

instantiation_from_dgraph_sol_step_helper_3 :: [UnifierDescription] -> ((UnifierDescription,Instantiation),[Either (Metaterm,Term) (Metaliteral,Literal)]) -> (([UnifierDescription],Instantiation),[Either (Metaterm,Term) (Metaliteral,Literal)])
instantiation_from_dgraph_sol_step_helper_3 uds ((ud,inst),l) = ((ud:uds,inst),l)

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

-- The idea is that at each step we work on one unifier, therefore modifying its description. Therefore, the enumeration at each step of the descriptions is just one description,
-- and thus, the combination is concatenating the lists.
-- Here we work under the assumption that the first parameter: the "piece" only has one unifier description.
-- The instantiation is passed downwards, so there's no need to re-combine it upwards: we just keep the head.
instantiation_from_dgraph_sol_comb :: ([UnifierDescription],Instantiation) -> ([UnifierDescription],Instantiation) -> ([UnifierDescription],Instantiation)
instantiation_from_dgraph_sol_comb ([ud],inst1) (uds,inst2) = (ud:uds,inst1)

-- We keep the last list, which corresponds to the first parameter, corresponding to the inner step.
instantiation_from_dgraph_sol_comb_helper :: (([UnifierDescription],Instantiation),[Either (Metaterm,Term) (Metaliteral,Literal)]) -> (([UnifierDescription],Instantiation),[Either (Metaterm,Term) (Metaliteral,Literal)]) -> (([UnifierDescription],Instantiation),[Either (Metaterm,Term) (Metaliteral,Literal)])
instantiation_from_dgraph_sol_comb_helper (udinst1,l1) (udinst2,l2) = (instantiation_from_dgraph_sol_comb udinst1 udinst2,l1)




-- Once again, decombination should not be important.
instantiation_from_dgraph_sol_decomb :: ([UnifierDescription],Instantiation) -> (([UnifierDescription],Instantiation),([UnifierDescription],Instantiation))
instantiation_from_dgraph_sol_decomb (ud,inst) = (([],idinst),(ud,inst))

instantiation_from_dgraph_sol_decomb_helper :: (([UnifierDescription],Instantiation),[Either (Metaterm,Term) (Metaliteral,Literal)]) -> ((([UnifierDescription],Instantiation),[Either (Metaterm,Term) (Metaliteral,Literal)]),(([UnifierDescription],Instantiation),[Either (Metaterm,Term) (Metaliteral,Literal)]))
instantiation_from_dgraph_sol_decomb_helper (udinst,l) = ((r1,[]),(r2,l)) where (r1,r2) = instantiation_from_dgraph_sol_decomb udinst
