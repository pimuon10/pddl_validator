theory prob_defs
imports Main PDDL_STRIPS_Checker invariant_verification
 begin
definition "dom_types = [''car'', ''vehicle'', ''person'']"
definition "dom_predicates = [(PredDecl ( Pred (''duplicate'')) ([Either([''object'']), Either([''object''])])),
 (PredDecl ( Pred (''swappable'')) ([Either([''object'']), Either([''object''])])),
 (PredDecl ( Pred (''cw'')) ([Either([''object'']), Either([''object''])])),
 (PredDecl ( Pred (''free'')) ([Either([''object''])])),
 (PredDecl ( Pred (''gone'')) ([Either([''object''])])),
 (PredDecl ( Pred (''present'')) ([Either([''object''])])),
 (PredDecl ( Pred (''normal'')) ([Either([''object''])])),
 (PredDecl ( Pred (''inverted'')) ([Either([''object''])])),
 (PredDecl ( Pred (''idle'')) ([])),
 (PredDecl ( Pred (''cutting'')) ([])),
 (PredDecl ( Pred (''have-cut'')) ([])),
 (PredDecl ( Pred (''splicing'')) ([])),
 (PredDecl ( Pred (''inverse-splicing'')) ([])),
 (PredDecl ( Pred (''finished'')) ([])),
 (PredDecl ( Pred (''cut-point-1'')) ([Either([''object''])])),
 (PredDecl ( Pred (''splice-point-1'')) ([Either([''object''])])),
 (PredDecl ( Pred (''splice-point-2'')) ([Either([''object''])])),
 (PredDecl ( Pred (''last-cut-point'')) ([Either([''object''])])),
 (PredDecl ( Pred (''s-first'')) ([Either([''object''])])),
 (PredDecl ( Pred (''s-next'')) ([Either([''object'']), Either([''object''])])),
 (PredDecl ( Pred (''s-last'')) ([Either([''object''])]))]"
definition "begin_cut = Action_Schema(''begin-cut'')
 [(Var ''?x'',Either([''object''])), (Var ''?y'',Either([''object'']))]
(BigAnd [formula.Atom (predAtm (Pred (''idle''))([])), formula.Atom (predAtm (Pred (''cw''))([Var ''?x'',Var ''?y'']))])
(Effect [formula.Atom (predAtm (Pred (''cutting''))([])), formula.Atom (predAtm (Pred (''last-cut-point''))([Var ''?x''])), formula.Atom (predAtm (Pred (''cut-point-1''))([Var ''?x''])), formula.Atom (predAtm (Pred (''s-first''))([Var ''?y''])), formula.Atom (predAtm (Pred (''s-last''))([Var ''?y'']))][formula.Atom (predAtm (Pred (''idle''))([])), formula.Atom (predAtm (Pred (''cw''))([Var ''?x'',Var ''?y'']))])"



definition "continue_cut = Action_Schema(''continue-cut'')
 [(Var ''?x'',Either([''object''])), (Var ''?y'',Either([''object'']))]
(BigAnd [formula.Atom (predAtm (Pred (''cutting''))([])), formula.Atom (predAtm (Pred (''s-last''))([Var ''?x''])), formula.Atom (predAtm (Pred (''cw''))([Var ''?x'',Var ''?y'']))])
(Effect [formula.Atom (predAtm (Pred (''s-next''))([Var ''?x'',Var ''?y''])), formula.Atom (predAtm (Pred (''s-last''))([Var ''?y'']))][formula.Atom (predAtm (Pred (''cw''))([Var ''?x'',Var ''?y''])), formula.Atom (predAtm (Pred (''s-last''))([Var ''?x'']))])"



definition "end_cut = Action_Schema(''end-cut'')
 [(Var ''?x'',Either([''object''])), (Var ''?y'',Either([''object''])), (Var ''?z'',Either([''object'']))]
(BigAnd [formula.Atom (predAtm (Pred (''cutting''))([])), formula.Atom (predAtm (Pred (''s-last''))([Var ''?x''])), formula.Atom (predAtm (Pred (''cw''))([Var ''?x'',Var ''?y''])), formula.Atom (predAtm (Pred (''cut-point-1''))([Var ''?z'']))])
(Effect [formula.Atom (predAtm (Pred (''have-cut''))([])), formula.Atom (predAtm (Pred (''cw''))([Var ''?z'',Var ''?y'']))][formula.Atom (predAtm (Pred (''cutting''))([])), formula.Atom (predAtm (Pred (''cw''))([Var ''?x'',Var ''?y''])), formula.Atom (predAtm (Pred (''cut-point-1''))([Var ''?z'']))])"



definition "begin_transpose_splice = Action_Schema(''begin-transpose-splice'')
 [(Var ''?x'',Either([''object''])), (Var ''?y'',Either([''object'']))]
(BigAnd [formula.Atom (predAtm (Pred (''have-cut''))([])), formula.Atom (predAtm (Pred (''cw''))([Var ''?x'',Var ''?y'']))])
(Effect [formula.Atom (predAtm (Pred (''splicing''))([])), formula.Atom (predAtm (Pred (''splice-point-1''))([Var ''?x''])), formula.Atom (predAtm (Pred (''splice-point-2''))([Var ''?y'']))][formula.Atom (predAtm (Pred (''have-cut''))([])), formula.Atom (predAtm (Pred (''cw''))([Var ''?x'',Var ''?y'']))])"



definition "continue_splice = Action_Schema(''continue-splice'')
 [(Var ''?x'',Either([''object''])), (Var ''?y'',Either([''object''])), (Var ''?z'',Either([''object'']))]
(BigAnd [formula.Atom (predAtm (Pred (''splicing''))([])), formula.Atom (predAtm (Pred (''s-first''))([Var ''?x''])), formula.Atom (predAtm (Pred (''s-next''))([Var ''?x'',Var ''?y''])), formula.Atom (predAtm (Pred (''splice-point-1''))([Var ''?z'']))])
(Effect [formula.Atom (predAtm (Pred (''s-first''))([Var ''?y''])), formula.Atom (predAtm (Pred (''cw''))([Var ''?z'',Var ''?x''])), formula.Atom (predAtm (Pred (''splice-point-1''))([Var ''?x'']))][formula.Atom (predAtm (Pred (''s-first''))([Var ''?x''])), formula.Atom (predAtm (Pred (''s-next''))([Var ''?x'',Var ''?y''])), formula.Atom (predAtm (Pred (''splice-point-1''))([Var ''?z'']))])"



definition "end_splice = Action_Schema(''end-splice'')
 [(Var ''?x'',Either([''object''])), (Var ''?y'',Either([''object''])), (Var ''?z'',Either([''object'']))]
(BigAnd [formula.Atom (predAtm (Pred (''splicing''))([])), formula.Atom (predAtm (Pred (''s-first''))([Var ''?x''])), formula.Atom (predAtm (Pred (''s-last''))([Var ''?x''])), formula.Atom (predAtm (Pred (''splice-point-1''))([Var ''?y''])), formula.Atom (predAtm (Pred (''splice-point-2''))([Var ''?z'']))])
(Effect [formula.Atom (predAtm (Pred (''finished''))([])), formula.Atom (predAtm (Pred (''cw''))([Var ''?y'',Var ''?x''])), formula.Atom (predAtm (Pred (''cw''))([Var ''?x'',Var ''?z'']))][formula.Atom (predAtm (Pred (''splicing''))([])), formula.Atom (predAtm (Pred (''s-first''))([Var ''?x''])), formula.Atom (predAtm (Pred (''s-last''))([Var ''?x''])), formula.Atom (predAtm (Pred (''splice-point-1''))([Var ''?y''])), formula.Atom (predAtm (Pred (''splice-point-2''))([Var ''?z'']))])"



definition "begin_transverse_splice = Action_Schema(''begin-transverse-splice'')
 [(Var ''?x'',Either([''object''])), (Var ''?y'',Either([''object'']))]
(BigAnd [formula.Atom (predAtm (Pred (''have-cut''))([])), formula.Atom (predAtm (Pred (''cw''))([Var ''?x'',Var ''?y'']))])
(Effect [formula.Atom (predAtm (Pred (''inverse-splicing''))([])), formula.Atom (predAtm (Pred (''splice-point-1''))([Var ''?x''])), formula.Atom (predAtm (Pred (''splice-point-2''))([Var ''?y'']))][formula.Atom (predAtm (Pred (''have-cut''))([])), formula.Atom (predAtm (Pred (''cw''))([Var ''?x'',Var ''?y'']))])"



definition "begin_inverse_splice = Action_Schema(''begin-inverse-splice'')
 [(Var ''?x'',Either([''object''])), (Var ''?y'',Either([''object'']))]
(BigAnd [formula.Atom (predAtm (Pred (''have-cut''))([])), formula.Atom (predAtm (Pred (''cw''))([Var ''?x'',Var ''?y''])), formula.Atom (predAtm (Pred (''last-cut-point''))([Var ''?x'']))])
(Effect [formula.Atom (predAtm (Pred (''inverse-splicing''))([])), formula.Atom (predAtm (Pred (''splice-point-1''))([Var ''?x''])), formula.Atom (predAtm (Pred (''splice-point-2''))([Var ''?y'']))][formula.Atom (predAtm (Pred (''have-cut''))([])), formula.Atom (predAtm (Pred (''cw''))([Var ''?x'',Var ''?y'']))])"



definition "begin_inverse_splice_special_case = Action_Schema(''begin-inverse-splice-special-case'')
 [(Var ''?x'',Either([''object'']))]
(BigAnd [formula.Atom (predAtm (Pred (''have-cut''))([])), formula.Atom (predAtm (Pred (''cw''))([Var ''?x'',Var ''?x''])), formula.Atom (predAtm (Pred (''last-cut-point''))([Var ''?x'']))])
(Effect [formula.Atom (predAtm (Pred (''inverse-splicing''))([])), formula.Atom (predAtm (Pred (''splice-point-1''))([Var ''?x''])), formula.Atom (predAtm (Pred (''splice-point-2''))([Var ''?x'']))][formula.Atom (predAtm (Pred (''have-cut''))([]))])"



definition "continue_inverse_splice_a = Action_Schema(''continue-inverse-splice-a'')
 [(Var ''?x'',Either([''object''])), (Var ''?y'',Either([''object''])), (Var ''?z'',Either([''object'']))]
(BigAnd [formula.Atom (predAtm (Pred (''inverse-splicing''))([])), formula.Atom (predAtm (Pred (''splice-point-1''))([Var ''?z''])), formula.Atom (predAtm (Pred (''normal''))([Var ''?x''])), formula.Atom (predAtm (Pred (''s-last''))([Var ''?x''])), formula.Atom (predAtm (Pred (''s-next''))([Var ''?y'',Var ''?x'']))])
(Effect [formula.Atom (predAtm (Pred (''s-last''))([Var ''?y''])), formula.Atom (predAtm (Pred (''inverted''))([Var ''?x''])), formula.Atom (predAtm (Pred (''cw''))([Var ''?z'',Var ''?x''])), formula.Atom (predAtm (Pred (''splice-point-1''))([Var ''?x'']))][formula.Atom (predAtm (Pred (''s-last''))([Var ''?x''])), formula.Atom (predAtm (Pred (''s-next''))([Var ''?y'',Var ''?x''])), formula.Atom (predAtm (Pred (''splice-point-1''))([Var ''?z''])), formula.Atom (predAtm (Pred (''normal''))([Var ''?x'']))])"



definition "continue_inverse_splice_b = Action_Schema(''continue-inverse-splice-b'')
 [(Var ''?x'',Either([''object''])), (Var ''?y'',Either([''object''])), (Var ''?z'',Either([''object'']))]
(BigAnd [formula.Atom (predAtm (Pred (''inverse-splicing''))([])), formula.Atom (predAtm (Pred (''splice-point-1''))([Var ''?z''])), formula.Atom (predAtm (Pred (''inverted''))([Var ''?x''])), formula.Atom (predAtm (Pred (''s-last''))([Var ''?x''])), formula.Atom (predAtm (Pred (''s-next''))([Var ''?y'',Var ''?x'']))])
(Effect [formula.Atom (predAtm (Pred (''s-last''))([Var ''?y''])), formula.Atom (predAtm (Pred (''normal''))([Var ''?x''])), formula.Atom (predAtm (Pred (''cw''))([Var ''?z'',Var ''?x''])), formula.Atom (predAtm (Pred (''splice-point-1''))([Var ''?x'']))][formula.Atom (predAtm (Pred (''s-last''))([Var ''?x''])), formula.Atom (predAtm (Pred (''s-next''))([Var ''?y'',Var ''?x''])), formula.Atom (predAtm (Pred (''inverted''))([Var ''?x''])), formula.Atom (predAtm (Pred (''splice-point-1''))([Var ''?z'']))])"



definition "end_inverse_splice_a = Action_Schema(''end-inverse-splice-a'')
 [(Var ''?x'',Either([''object''])), (Var ''?y'',Either([''object''])), (Var ''?z'',Either([''object'']))]
(BigAnd [formula.Atom (predAtm (Pred (''inverse-splicing''))([])), formula.Atom (predAtm (Pred (''normal''))([Var ''?x''])), formula.Atom (predAtm (Pred (''splice-point-1''))([Var ''?y''])), formula.Atom (predAtm (Pred (''splice-point-2''))([Var ''?z''])), formula.Atom (predAtm (Pred (''s-first''))([Var ''?x''])), formula.Atom (predAtm (Pred (''s-last''))([Var ''?x'']))])
(Effect [formula.Atom (predAtm (Pred (''finished''))([])), formula.Atom (predAtm (Pred (''cw''))([Var ''?y'',Var ''?x''])), formula.Atom (predAtm (Pred (''cw''))([Var ''?x'',Var ''?z''])), formula.Atom (predAtm (Pred (''inverted''))([Var ''?x'']))][formula.Atom (predAtm (Pred (''inverse-splicing''))([])), formula.Atom (predAtm (Pred (''splice-point-1''))([Var ''?y''])), formula.Atom (predAtm (Pred (''splice-point-2''))([Var ''?z''])), formula.Atom (predAtm (Pred (''s-first''))([Var ''?x''])), formula.Atom (predAtm (Pred (''s-last''))([Var ''?x''])), formula.Atom (predAtm (Pred (''normal''))([Var ''?x'']))])"



definition "end_inverse_splice_b = Action_Schema(''end-inverse-splice-b'')
 [(Var ''?x'',Either([''object''])), (Var ''?y'',Either([''object''])), (Var ''?z'',Either([''object'']))]
(BigAnd [formula.Atom (predAtm (Pred (''inverse-splicing''))([])), formula.Atom (predAtm (Pred (''inverted''))([Var ''?x''])), formula.Atom (predAtm (Pred (''splice-point-1''))([Var ''?y''])), formula.Atom (predAtm (Pred (''splice-point-2''))([Var ''?z''])), formula.Atom (predAtm (Pred (''s-first''))([Var ''?x''])), formula.Atom (predAtm (Pred (''s-last''))([Var ''?x'']))])
(Effect [formula.Atom (predAtm (Pred (''finished''))([])), formula.Atom (predAtm (Pred (''cw''))([Var ''?y'',Var ''?x''])), formula.Atom (predAtm (Pred (''cw''))([Var ''?x'',Var ''?z''])), formula.Atom (predAtm (Pred (''normal''))([Var ''?x'']))][formula.Atom (predAtm (Pred (''inverse-splicing''))([])), formula.Atom (predAtm (Pred (''splice-point-1''))([Var ''?y''])), formula.Atom (predAtm (Pred (''splice-point-2''))([Var ''?z''])), formula.Atom (predAtm (Pred (''s-first''))([Var ''?x''])), formula.Atom (predAtm (Pred (''s-last''))([Var ''?x''])), formula.Atom (predAtm (Pred (''inverted''))([Var ''?x'']))])"



definition "reset_1 = Action_Schema(''reset-1'')
 [(Var ''?x'',Either([''object'']))]
(BigAnd [formula.Atom (predAtm (Pred (''finished''))([])), formula.Atom (predAtm (Pred (''last-cut-point''))([Var ''?x'']))])
(Effect [formula.Atom (predAtm (Pred (''idle''))([]))][formula.Atom (predAtm (Pred (''last-cut-point''))([Var ''?x''])), formula.Atom (predAtm (Pred (''finished''))([]))])"


definition "dom_actions = [begin_cut, continue_cut, end_cut, begin_transpose_splice, continue_splice, end_splice, begin_transverse_splice, begin_inverse_splice, begin_inverse_splice_special_case, continue_inverse_splice_a, continue_inverse_splice_b, end_inverse_splice_a, end_inverse_splice_b, reset_1]"

lemma distinct_act_names:      shows "distinct (map ast_action_schema.name (dom_actions))"
  unfolding dom_types_def dom_predicates_def dom_actions_def ast_domain.wf_domain_def
begin_cut_def continue_cut_def end_cut_def begin_transpose_splice_def continue_splice_def end_splice_def begin_transverse_splice_def begin_inverse_splice_def begin_inverse_splice_special_case_def continue_inverse_splice_a_def continue_inverse_splice_b_def end_inverse_splice_a_def end_inverse_splice_b_def reset_1_def
  by (auto simp add: ast_domain.wf_predicate_decl.simps ast_domain.wf_type.simps
                      ast_domain.wf_action_schema.simps ast_domain.wf_effect.simps
                     ast_domain.wf_atom.simps ast_domain.sig_def
                    ast_domain.is_of_type_def ast_domain.of_type_def)

definition "prob_dom = Domain dom_types dom_predicates dom_actions"

definition "x_inverted = (%s. (ast_problem.holds s (BigOr [BigAnd [formula.Atom (predAtm (Pred (''normal''))([Obj ''?x''])), formula.Not (formula.Atom (predAtm (Pred (''inverted''))([Obj ''?x''])))], BigAnd [formula.Not (formula.Atom (predAtm (Pred (''normal''))([Obj ''?x'']))), formula.Atom (predAtm (Pred (''inverted''))([Obj ''?x'']))]])))"


definition "x_s_first = (%s. (ast_problem.holds s (BigOr [formula.Not (formula.Atom (predAtm (Pred (''s-first''))([Obj ''?x'']))), formula.Not (formula.Atom (predAtm (Pred (''s-first''))([Obj ''?y''])))])))"


definition "x_s_first_snd = (%s. (ast_problem.holds s (BigOr [BigOr [formula.Not (formula.Atom (predAtm (Pred (''s-first''))([Obj ''?x'']))), formula.Not (formula.Atom (predAtm (Pred (''s-first''))([Obj ''?y''])))], BigOr [formula.Not (formula.Atom (predAtm (Pred (''s-first''))([Obj ''?x'']))), formula.Not (formula.Atom (predAtm (Pred (''idle''))([])))], BigOr [formula.Not (formula.Atom (predAtm (Pred (''s-first''))([Obj ''?x'']))), formula.Not (formula.Atom (predAtm (Pred (''finished''))([])))], BigOr [formula.Not (formula.Atom (predAtm (Pred (''idle''))([]))), formula.Not (formula.Atom (predAtm (Pred (''finished''))([])))]])))"


definition "x_s_last = (%s. (ast_problem.holds s (BigOr [formula.Not (formula.Atom (predAtm (Pred (''s-last''))([Obj ''?x'']))), formula.Not (formula.Atom (predAtm (Pred (''s-last''))([Obj ''?y''])))])))"


definition "x_last_cut = (%s. (ast_problem.holds s (BigOr [formula.Not (formula.Atom (predAtm (Pred (''last-cut-point''))([Obj ''?x'']))), formula.Not (formula.Atom (predAtm (Pred (''last-cut-point''))([Obj ''?y''])))])))"


definition "x_cut_point_1 = (%s. (ast_problem.holds s (BigOr [formula.Not (formula.Atom (predAtm (Pred (''cut-point-1''))([Obj ''?x'']))), formula.Not (formula.Atom (predAtm (Pred (''cut-point-1''))([Obj ''?y''])))])))"


definition "x_splice_point_1 = (%s. (ast_problem.holds s (BigOr [formula.Not (formula.Atom (predAtm (Pred (''splice-point-1''))([Obj ''?x'']))), formula.Not (formula.Atom (predAtm (Pred (''splice-point-1''))([Obj ''?y''])))])))"


definition "x_splice_point_2 = (%s. (ast_problem.holds s (BigOr [formula.Not (formula.Atom (predAtm (Pred (''splice-point-2''))([Obj ''?x'']))), formula.Not (formula.Atom (predAtm (Pred (''splice-point-2''))([Obj ''?y''])))])))"
lemma x_inverted_invariant_begin_cut:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  begin_cut))"
  shows "ast_problem.invariant_act x_inverted (ast_domain.instantiate_action_schema  begin_cut args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_inverted s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  begin_cut args) s"
  obtain arg2 arg1 where args_2: "args = [arg2,arg1]"
    using assms
    unfolding  begin_cut_def
    apply auto
    using list_len_2 list_all2_lengthD
    by metis
  show "x_inverted(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  begin_cut args)) s)"
    using ass
    unfolding x_inverted_def  begin_cut_def
    apply(auto simp add: args_2)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_inverted_invariant_continue_cut:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  continue_cut))"
  shows "ast_problem.invariant_act x_inverted (ast_domain.instantiate_action_schema  continue_cut args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_inverted s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  continue_cut args) s"
  obtain arg2 arg1 where args_2: "args = [arg2,arg1]"
    using assms
    unfolding  continue_cut_def
    apply auto
    using list_len_2 list_all2_lengthD
    by metis
  show "x_inverted(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  continue_cut args)) s)"
    using ass
    unfolding x_inverted_def  continue_cut_def
    apply(auto simp add: args_2)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_inverted_invariant_end_cut:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  end_cut))"
  shows "ast_problem.invariant_act x_inverted (ast_domain.instantiate_action_schema  end_cut args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_inverted s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  end_cut args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  end_cut_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_inverted(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  end_cut args)) s)"
    using ass
    unfolding x_inverted_def  end_cut_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_inverted_invariant_begin_transpose_splice:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  begin_transpose_splice))"
  shows "ast_problem.invariant_act x_inverted (ast_domain.instantiate_action_schema  begin_transpose_splice args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_inverted s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  begin_transpose_splice args) s"
  obtain arg2 arg1 where args_2: "args = [arg2,arg1]"
    using assms
    unfolding  begin_transpose_splice_def
    apply auto
    using list_len_2 list_all2_lengthD
    by metis
  show "x_inverted(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  begin_transpose_splice args)) s)"
    using ass
    unfolding x_inverted_def  begin_transpose_splice_def
    apply(auto simp add: args_2)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_inverted_invariant_continue_splice:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  continue_splice))"
  shows "ast_problem.invariant_act x_inverted (ast_domain.instantiate_action_schema  continue_splice args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_inverted s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  continue_splice args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  continue_splice_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_inverted(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  continue_splice args)) s)"
    using ass
    unfolding x_inverted_def  continue_splice_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_inverted_invariant_end_splice:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  end_splice))"
  shows "ast_problem.invariant_act x_inverted (ast_domain.instantiate_action_schema  end_splice args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_inverted s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  end_splice args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  end_splice_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_inverted(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  end_splice args)) s)"
    using ass
    unfolding x_inverted_def  end_splice_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_inverted_invariant_begin_transverse_splice:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  begin_transverse_splice))"
  shows "ast_problem.invariant_act x_inverted (ast_domain.instantiate_action_schema  begin_transverse_splice args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_inverted s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  begin_transverse_splice args) s"
  obtain arg2 arg1 where args_2: "args = [arg2,arg1]"
    using assms
    unfolding  begin_transverse_splice_def
    apply auto
    using list_len_2 list_all2_lengthD
    by metis
  show "x_inverted(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  begin_transverse_splice args)) s)"
    using ass
    unfolding x_inverted_def  begin_transverse_splice_def
    apply(auto simp add: args_2)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_inverted_invariant_begin_inverse_splice:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  begin_inverse_splice))"
  shows "ast_problem.invariant_act x_inverted (ast_domain.instantiate_action_schema  begin_inverse_splice args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_inverted s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  begin_inverse_splice args) s"
  obtain arg2 arg1 where args_2: "args = [arg2,arg1]"
    using assms
    unfolding  begin_inverse_splice_def
    apply auto
    using list_len_2 list_all2_lengthD
    by metis
  show "x_inverted(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  begin_inverse_splice args)) s)"
    using ass
    unfolding x_inverted_def  begin_inverse_splice_def
    apply(auto simp add: args_2)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_inverted_invariant_begin_inverse_splice_special_case:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  begin_inverse_splice_special_case))"
  shows "ast_problem.invariant_act x_inverted (ast_domain.instantiate_action_schema  begin_inverse_splice_special_case args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_inverted s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  begin_inverse_splice_special_case args) s"
  obtain arg1 where args_1: "args = [arg1]"
    using assms
    unfolding  begin_inverse_splice_special_case_def
    apply auto
    using list_len_1 list_all2_lengthD
    by metis
  show "x_inverted(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  begin_inverse_splice_special_case args)) s)"
    using ass
    unfolding x_inverted_def  begin_inverse_splice_special_case_def
    apply(auto simp add: args_1)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_inverted_invariant_continue_inverse_splice_a:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  continue_inverse_splice_a))"
  shows "ast_problem.invariant_act x_inverted (ast_domain.instantiate_action_schema  continue_inverse_splice_a args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_inverted s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  continue_inverse_splice_a args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  continue_inverse_splice_a_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_inverted(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  continue_inverse_splice_a args)) s)"
    using ass
    unfolding x_inverted_def  continue_inverse_splice_a_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_inverted_invariant_continue_inverse_splice_b:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  continue_inverse_splice_b))"
  shows "ast_problem.invariant_act x_inverted (ast_domain.instantiate_action_schema  continue_inverse_splice_b args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_inverted s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  continue_inverse_splice_b args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  continue_inverse_splice_b_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_inverted(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  continue_inverse_splice_b args)) s)"
    using ass
    unfolding x_inverted_def  continue_inverse_splice_b_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_inverted_invariant_end_inverse_splice_a:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  end_inverse_splice_a))"
  shows "ast_problem.invariant_act x_inverted (ast_domain.instantiate_action_schema  end_inverse_splice_a args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_inverted s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  end_inverse_splice_a args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  end_inverse_splice_a_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_inverted(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  end_inverse_splice_a args)) s)"
    using ass
    unfolding x_inverted_def  end_inverse_splice_a_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_inverted_invariant_end_inverse_splice_b:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  end_inverse_splice_b))"
  shows "ast_problem.invariant_act x_inverted (ast_domain.instantiate_action_schema  end_inverse_splice_b args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_inverted s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  end_inverse_splice_b args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  end_inverse_splice_b_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_inverted(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  end_inverse_splice_b args)) s)"
    using ass
    unfolding x_inverted_def  end_inverse_splice_b_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_inverted_invariant_reset_1:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  reset_1))"
  shows "ast_problem.invariant_act x_inverted (ast_domain.instantiate_action_schema  reset_1 args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_inverted s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  reset_1 args) s"
  obtain arg1 where args_1: "args = [arg1]"
    using assms
    unfolding  reset_1_def
    apply auto
    using list_len_1 list_all2_lengthD
    by metis
  show "x_inverted(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  reset_1 args)) s)"
    using ass
    unfolding x_inverted_def  reset_1_def
    apply(auto simp add: args_1)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed
lemma x_inverted_for_prob_dom:
  assumes "PI = (Problem (prob_dom) (obj) (I) (G))"
  shows "ast_problem.invariant_wf_plan_act_seq PI x_inverted as"
  apply(rule ast_problem.invariant_for_plan_act_seq)
  apply(rule ast_problem.invariant_action_insts_imp_invariant_plan_actions[where ?Q = x_inverted])
  using ast_problem.invariant_for_plan_act_seq assms distinct_act_names
x_inverted_invariant_begin_cut x_inverted_invariant_continue_cut x_inverted_invariant_end_cut x_inverted_invariant_begin_transpose_splice x_inverted_invariant_continue_splice x_inverted_invariant_end_splice x_inverted_invariant_begin_transverse_splice x_inverted_invariant_begin_inverse_splice x_inverted_invariant_begin_inverse_splice_special_case x_inverted_invariant_continue_inverse_splice_a x_inverted_invariant_continue_inverse_splice_b x_inverted_invariant_end_inverse_splice_a x_inverted_invariant_end_inverse_splice_b x_inverted_invariant_reset_1
    unfolding prob_dom_def dom_actions_def ast_problem.action_params_match_def
begin_cut_def continue_cut_def end_cut_def begin_transpose_splice_def continue_splice_def end_splice_def begin_transverse_splice_def begin_inverse_splice_def begin_inverse_splice_special_case_def continue_inverse_splice_a_def continue_inverse_splice_b_def end_inverse_splice_a_def end_inverse_splice_b_def reset_1_def
  by auto


lemma x_s_first_invariant_begin_cut:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  begin_cut))"
  shows "ast_problem.invariant_act x_s_first (ast_domain.instantiate_action_schema  begin_cut args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_s_first s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  begin_cut args) s"
  obtain arg2 arg1 where args_2: "args = [arg2,arg1]"
    using assms
    unfolding  begin_cut_def
    apply auto
    using list_len_2 list_all2_lengthD
    by metis
  show "x_s_first(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  begin_cut args)) s)"
    using ass
    unfolding x_s_first_def  begin_cut_def
    apply(auto simp add: args_2)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_s_first_invariant_continue_cut:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  continue_cut))"
  shows "ast_problem.invariant_act x_s_first (ast_domain.instantiate_action_schema  continue_cut args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_s_first s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  continue_cut args) s"
  obtain arg2 arg1 where args_2: "args = [arg2,arg1]"
    using assms
    unfolding  continue_cut_def
    apply auto
    using list_len_2 list_all2_lengthD
    by metis
  show "x_s_first(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  continue_cut args)) s)"
    using ass
    unfolding x_s_first_def  continue_cut_def
    apply(auto simp add: args_2)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_s_first_invariant_end_cut:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  end_cut))"
  shows "ast_problem.invariant_act x_s_first (ast_domain.instantiate_action_schema  end_cut args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_s_first s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  end_cut args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  end_cut_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_s_first(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  end_cut args)) s)"
    using ass
    unfolding x_s_first_def  end_cut_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_s_first_invariant_begin_transpose_splice:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  begin_transpose_splice))"
  shows "ast_problem.invariant_act x_s_first (ast_domain.instantiate_action_schema  begin_transpose_splice args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_s_first s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  begin_transpose_splice args) s"
  obtain arg2 arg1 where args_2: "args = [arg2,arg1]"
    using assms
    unfolding  begin_transpose_splice_def
    apply auto
    using list_len_2 list_all2_lengthD
    by metis
  show "x_s_first(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  begin_transpose_splice args)) s)"
    using ass
    unfolding x_s_first_def  begin_transpose_splice_def
    apply(auto simp add: args_2)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_s_first_invariant_continue_splice:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  continue_splice))"
  shows "ast_problem.invariant_act x_s_first (ast_domain.instantiate_action_schema  continue_splice args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_s_first s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  continue_splice args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  continue_splice_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_s_first(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  continue_splice args)) s)"
    using ass
    unfolding x_s_first_def  continue_splice_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_s_first_invariant_end_splice:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  end_splice))"
  shows "ast_problem.invariant_act x_s_first (ast_domain.instantiate_action_schema  end_splice args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_s_first s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  end_splice args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  end_splice_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_s_first(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  end_splice args)) s)"
    using ass
    unfolding x_s_first_def  end_splice_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_s_first_invariant_begin_transverse_splice:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  begin_transverse_splice))"
  shows "ast_problem.invariant_act x_s_first (ast_domain.instantiate_action_schema  begin_transverse_splice args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_s_first s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  begin_transverse_splice args) s"
  obtain arg2 arg1 where args_2: "args = [arg2,arg1]"
    using assms
    unfolding  begin_transverse_splice_def
    apply auto
    using list_len_2 list_all2_lengthD
    by metis
  show "x_s_first(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  begin_transverse_splice args)) s)"
    using ass
    unfolding x_s_first_def  begin_transverse_splice_def
    apply(auto simp add: args_2)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_s_first_invariant_begin_inverse_splice:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  begin_inverse_splice))"
  shows "ast_problem.invariant_act x_s_first (ast_domain.instantiate_action_schema  begin_inverse_splice args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_s_first s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  begin_inverse_splice args) s"
  obtain arg2 arg1 where args_2: "args = [arg2,arg1]"
    using assms
    unfolding  begin_inverse_splice_def
    apply auto
    using list_len_2 list_all2_lengthD
    by metis
  show "x_s_first(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  begin_inverse_splice args)) s)"
    using ass
    unfolding x_s_first_def  begin_inverse_splice_def
    apply(auto simp add: args_2)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_s_first_invariant_begin_inverse_splice_special_case:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  begin_inverse_splice_special_case))"
  shows "ast_problem.invariant_act x_s_first (ast_domain.instantiate_action_schema  begin_inverse_splice_special_case args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_s_first s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  begin_inverse_splice_special_case args) s"
  obtain arg1 where args_1: "args = [arg1]"
    using assms
    unfolding  begin_inverse_splice_special_case_def
    apply auto
    using list_len_1 list_all2_lengthD
    by metis
  show "x_s_first(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  begin_inverse_splice_special_case args)) s)"
    using ass
    unfolding x_s_first_def  begin_inverse_splice_special_case_def
    apply(auto simp add: args_1)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_s_first_invariant_continue_inverse_splice_a:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  continue_inverse_splice_a))"
  shows "ast_problem.invariant_act x_s_first (ast_domain.instantiate_action_schema  continue_inverse_splice_a args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_s_first s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  continue_inverse_splice_a args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  continue_inverse_splice_a_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_s_first(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  continue_inverse_splice_a args)) s)"
    using ass
    unfolding x_s_first_def  continue_inverse_splice_a_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_s_first_invariant_continue_inverse_splice_b:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  continue_inverse_splice_b))"
  shows "ast_problem.invariant_act x_s_first (ast_domain.instantiate_action_schema  continue_inverse_splice_b args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_s_first s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  continue_inverse_splice_b args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  continue_inverse_splice_b_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_s_first(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  continue_inverse_splice_b args)) s)"
    using ass
    unfolding x_s_first_def  continue_inverse_splice_b_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_s_first_invariant_end_inverse_splice_a:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  end_inverse_splice_a))"
  shows "ast_problem.invariant_act x_s_first (ast_domain.instantiate_action_schema  end_inverse_splice_a args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_s_first s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  end_inverse_splice_a args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  end_inverse_splice_a_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_s_first(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  end_inverse_splice_a args)) s)"
    using ass
    unfolding x_s_first_def  end_inverse_splice_a_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_s_first_invariant_end_inverse_splice_b:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  end_inverse_splice_b))"
  shows "ast_problem.invariant_act x_s_first (ast_domain.instantiate_action_schema  end_inverse_splice_b args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_s_first s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  end_inverse_splice_b args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  end_inverse_splice_b_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_s_first(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  end_inverse_splice_b args)) s)"
    using ass
    unfolding x_s_first_def  end_inverse_splice_b_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_s_first_invariant_reset_1:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  reset_1))"
  shows "ast_problem.invariant_act x_s_first (ast_domain.instantiate_action_schema  reset_1 args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_s_first s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  reset_1 args) s"
  obtain arg1 where args_1: "args = [arg1]"
    using assms
    unfolding  reset_1_def
    apply auto
    using list_len_1 list_all2_lengthD
    by metis
  show "x_s_first(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  reset_1 args)) s)"
    using ass
    unfolding x_s_first_def  reset_1_def
    apply(auto simp add: args_1)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed
lemma x_s_first_for_prob_dom:
  assumes "PI = (Problem (prob_dom) (obj) (I) (G))"
  shows "ast_problem.invariant_wf_plan_act_seq PI x_s_first as"
  apply(rule ast_problem.invariant_for_plan_act_seq)
  apply(rule ast_problem.invariant_action_insts_imp_invariant_plan_actions[where ?Q = x_s_first])
  using ast_problem.invariant_for_plan_act_seq assms distinct_act_names
x_s_first_invariant_begin_cut x_s_first_invariant_continue_cut x_s_first_invariant_end_cut x_s_first_invariant_begin_transpose_splice x_s_first_invariant_continue_splice x_s_first_invariant_end_splice x_s_first_invariant_begin_transverse_splice x_s_first_invariant_begin_inverse_splice x_s_first_invariant_begin_inverse_splice_special_case x_s_first_invariant_continue_inverse_splice_a x_s_first_invariant_continue_inverse_splice_b x_s_first_invariant_end_inverse_splice_a x_s_first_invariant_end_inverse_splice_b x_s_first_invariant_reset_1
    unfolding prob_dom_def dom_actions_def ast_problem.action_params_match_def
begin_cut_def continue_cut_def end_cut_def begin_transpose_splice_def continue_splice_def end_splice_def begin_transverse_splice_def begin_inverse_splice_def begin_inverse_splice_special_case_def continue_inverse_splice_a_def continue_inverse_splice_b_def end_inverse_splice_a_def end_inverse_splice_b_def reset_1_def
  by auto


lemma x_s_first_snd_invariant_begin_cut:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  begin_cut))"
  shows "ast_problem.invariant_act x_s_first_snd (ast_domain.instantiate_action_schema  begin_cut args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_s_first_snd s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  begin_cut args) s"
  obtain arg2 arg1 where args_2: "args = [arg2,arg1]"
    using assms
    unfolding  begin_cut_def
    apply auto
    using list_len_2 list_all2_lengthD
    by metis
  show "x_s_first_snd(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  begin_cut args)) s)"
    using ass
    unfolding x_s_first_snd_def  begin_cut_def
    apply(auto simp add: args_2)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_s_first_snd_invariant_continue_cut:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  continue_cut))"
  shows "ast_problem.invariant_act x_s_first_snd (ast_domain.instantiate_action_schema  continue_cut args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_s_first_snd s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  continue_cut args) s"
  obtain arg2 arg1 where args_2: "args = [arg2,arg1]"
    using assms
    unfolding  continue_cut_def
    apply auto
    using list_len_2 list_all2_lengthD
    by metis
  show "x_s_first_snd(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  continue_cut args)) s)"
    using ass
    unfolding x_s_first_snd_def  continue_cut_def
    apply(auto simp add: args_2)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_s_first_snd_invariant_end_cut:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  end_cut))"
  shows "ast_problem.invariant_act x_s_first_snd (ast_domain.instantiate_action_schema  end_cut args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_s_first_snd s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  end_cut args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  end_cut_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_s_first_snd(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  end_cut args)) s)"
    using ass
    unfolding x_s_first_snd_def  end_cut_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_s_first_snd_invariant_begin_transpose_splice:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  begin_transpose_splice))"
  shows "ast_problem.invariant_act x_s_first_snd (ast_domain.instantiate_action_schema  begin_transpose_splice args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_s_first_snd s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  begin_transpose_splice args) s"
  obtain arg2 arg1 where args_2: "args = [arg2,arg1]"
    using assms
    unfolding  begin_transpose_splice_def
    apply auto
    using list_len_2 list_all2_lengthD
    by metis
  show "x_s_first_snd(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  begin_transpose_splice args)) s)"
    using ass
    unfolding x_s_first_snd_def  begin_transpose_splice_def
    apply(auto simp add: args_2)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_s_first_snd_invariant_continue_splice:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  continue_splice))"
  shows "ast_problem.invariant_act x_s_first_snd (ast_domain.instantiate_action_schema  continue_splice args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_s_first_snd s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  continue_splice args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  continue_splice_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_s_first_snd(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  continue_splice args)) s)"
    using ass
    unfolding x_s_first_snd_def  continue_splice_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_s_first_snd_invariant_end_splice:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  end_splice))"
  shows "ast_problem.invariant_act x_s_first_snd (ast_domain.instantiate_action_schema  end_splice args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_s_first_snd s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  end_splice args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  end_splice_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_s_first_snd(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  end_splice args)) s)"
    using ass
    unfolding x_s_first_snd_def  end_splice_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_s_first_snd_invariant_begin_transverse_splice:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  begin_transverse_splice))"
  shows "ast_problem.invariant_act x_s_first_snd (ast_domain.instantiate_action_schema  begin_transverse_splice args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_s_first_snd s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  begin_transverse_splice args) s"
  obtain arg2 arg1 where args_2: "args = [arg2,arg1]"
    using assms
    unfolding  begin_transverse_splice_def
    apply auto
    using list_len_2 list_all2_lengthD
    by metis
  show "x_s_first_snd(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  begin_transverse_splice args)) s)"
    using ass
    unfolding x_s_first_snd_def  begin_transverse_splice_def
    apply(auto simp add: args_2)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_s_first_snd_invariant_begin_inverse_splice:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  begin_inverse_splice))"
  shows "ast_problem.invariant_act x_s_first_snd (ast_domain.instantiate_action_schema  begin_inverse_splice args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_s_first_snd s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  begin_inverse_splice args) s"
  obtain arg2 arg1 where args_2: "args = [arg2,arg1]"
    using assms
    unfolding  begin_inverse_splice_def
    apply auto
    using list_len_2 list_all2_lengthD
    by metis
  show "x_s_first_snd(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  begin_inverse_splice args)) s)"
    using ass
    unfolding x_s_first_snd_def  begin_inverse_splice_def
    apply(auto simp add: args_2)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_s_first_snd_invariant_begin_inverse_splice_special_case:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  begin_inverse_splice_special_case))"
  shows "ast_problem.invariant_act x_s_first_snd (ast_domain.instantiate_action_schema  begin_inverse_splice_special_case args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_s_first_snd s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  begin_inverse_splice_special_case args) s"
  obtain arg1 where args_1: "args = [arg1]"
    using assms
    unfolding  begin_inverse_splice_special_case_def
    apply auto
    using list_len_1 list_all2_lengthD
    by metis
  show "x_s_first_snd(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  begin_inverse_splice_special_case args)) s)"
    using ass
    unfolding x_s_first_snd_def  begin_inverse_splice_special_case_def
    apply(auto simp add: args_1)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_s_first_snd_invariant_continue_inverse_splice_a:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  continue_inverse_splice_a))"
  shows "ast_problem.invariant_act x_s_first_snd (ast_domain.instantiate_action_schema  continue_inverse_splice_a args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_s_first_snd s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  continue_inverse_splice_a args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  continue_inverse_splice_a_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_s_first_snd(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  continue_inverse_splice_a args)) s)"
    using ass
    unfolding x_s_first_snd_def  continue_inverse_splice_a_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_s_first_snd_invariant_continue_inverse_splice_b:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  continue_inverse_splice_b))"
  shows "ast_problem.invariant_act x_s_first_snd (ast_domain.instantiate_action_schema  continue_inverse_splice_b args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_s_first_snd s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  continue_inverse_splice_b args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  continue_inverse_splice_b_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_s_first_snd(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  continue_inverse_splice_b args)) s)"
    using ass
    unfolding x_s_first_snd_def  continue_inverse_splice_b_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_s_first_snd_invariant_end_inverse_splice_a:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  end_inverse_splice_a))"
  shows "ast_problem.invariant_act x_s_first_snd (ast_domain.instantiate_action_schema  end_inverse_splice_a args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_s_first_snd s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  end_inverse_splice_a args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  end_inverse_splice_a_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_s_first_snd(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  end_inverse_splice_a args)) s)"
    using ass
    unfolding x_s_first_snd_def  end_inverse_splice_a_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_s_first_snd_invariant_end_inverse_splice_b:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  end_inverse_splice_b))"
  shows "ast_problem.invariant_act x_s_first_snd (ast_domain.instantiate_action_schema  end_inverse_splice_b args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_s_first_snd s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  end_inverse_splice_b args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  end_inverse_splice_b_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_s_first_snd(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  end_inverse_splice_b args)) s)"
    using ass
    unfolding x_s_first_snd_def  end_inverse_splice_b_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_s_first_snd_invariant_reset_1:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  reset_1))"
  shows "ast_problem.invariant_act x_s_first_snd (ast_domain.instantiate_action_schema  reset_1 args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_s_first_snd s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  reset_1 args) s"
  obtain arg1 where args_1: "args = [arg1]"
    using assms
    unfolding  reset_1_def
    apply auto
    using list_len_1 list_all2_lengthD
    by metis
  show "x_s_first_snd(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  reset_1 args)) s)"
    using ass
    unfolding x_s_first_snd_def  reset_1_def
    apply(auto simp add: args_1)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed
lemma x_s_first_snd_for_prob_dom:
  assumes "PI = (Problem (prob_dom) (obj) (I) (G))"
  shows "ast_problem.invariant_wf_plan_act_seq PI x_s_first_snd as"
  apply(rule ast_problem.invariant_for_plan_act_seq)
  apply(rule ast_problem.invariant_action_insts_imp_invariant_plan_actions[where ?Q = x_s_first_snd])
  using ast_problem.invariant_for_plan_act_seq assms distinct_act_names
x_s_first_snd_invariant_begin_cut x_s_first_snd_invariant_continue_cut x_s_first_snd_invariant_end_cut x_s_first_snd_invariant_begin_transpose_splice x_s_first_snd_invariant_continue_splice x_s_first_snd_invariant_end_splice x_s_first_snd_invariant_begin_transverse_splice x_s_first_snd_invariant_begin_inverse_splice x_s_first_snd_invariant_begin_inverse_splice_special_case x_s_first_snd_invariant_continue_inverse_splice_a x_s_first_snd_invariant_continue_inverse_splice_b x_s_first_snd_invariant_end_inverse_splice_a x_s_first_snd_invariant_end_inverse_splice_b x_s_first_snd_invariant_reset_1
    unfolding prob_dom_def dom_actions_def ast_problem.action_params_match_def
begin_cut_def continue_cut_def end_cut_def begin_transpose_splice_def continue_splice_def end_splice_def begin_transverse_splice_def begin_inverse_splice_def begin_inverse_splice_special_case_def continue_inverse_splice_a_def continue_inverse_splice_b_def end_inverse_splice_a_def end_inverse_splice_b_def reset_1_def
  by auto


lemma x_s_last_invariant_begin_cut:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  begin_cut))"
  shows "ast_problem.invariant_act x_s_last (ast_domain.instantiate_action_schema  begin_cut args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_s_last s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  begin_cut args) s"
  obtain arg2 arg1 where args_2: "args = [arg2,arg1]"
    using assms
    unfolding  begin_cut_def
    apply auto
    using list_len_2 list_all2_lengthD
    by metis
  show "x_s_last(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  begin_cut args)) s)"
    using ass
    unfolding x_s_last_def  begin_cut_def
    apply(auto simp add: args_2)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_s_last_invariant_continue_cut:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  continue_cut))"
  shows "ast_problem.invariant_act x_s_last (ast_domain.instantiate_action_schema  continue_cut args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_s_last s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  continue_cut args) s"
  obtain arg2 arg1 where args_2: "args = [arg2,arg1]"
    using assms
    unfolding  continue_cut_def
    apply auto
    using list_len_2 list_all2_lengthD
    by metis
  show "x_s_last(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  continue_cut args)) s)"
    using ass
    unfolding x_s_last_def  continue_cut_def
    apply(auto simp add: args_2)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_s_last_invariant_end_cut:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  end_cut))"
  shows "ast_problem.invariant_act x_s_last (ast_domain.instantiate_action_schema  end_cut args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_s_last s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  end_cut args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  end_cut_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_s_last(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  end_cut args)) s)"
    using ass
    unfolding x_s_last_def  end_cut_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_s_last_invariant_begin_transpose_splice:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  begin_transpose_splice))"
  shows "ast_problem.invariant_act x_s_last (ast_domain.instantiate_action_schema  begin_transpose_splice args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_s_last s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  begin_transpose_splice args) s"
  obtain arg2 arg1 where args_2: "args = [arg2,arg1]"
    using assms
    unfolding  begin_transpose_splice_def
    apply auto
    using list_len_2 list_all2_lengthD
    by metis
  show "x_s_last(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  begin_transpose_splice args)) s)"
    using ass
    unfolding x_s_last_def  begin_transpose_splice_def
    apply(auto simp add: args_2)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_s_last_invariant_continue_splice:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  continue_splice))"
  shows "ast_problem.invariant_act x_s_last (ast_domain.instantiate_action_schema  continue_splice args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_s_last s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  continue_splice args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  continue_splice_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_s_last(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  continue_splice args)) s)"
    using ass
    unfolding x_s_last_def  continue_splice_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_s_last_invariant_end_splice:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  end_splice))"
  shows "ast_problem.invariant_act x_s_last (ast_domain.instantiate_action_schema  end_splice args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_s_last s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  end_splice args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  end_splice_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_s_last(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  end_splice args)) s)"
    using ass
    unfolding x_s_last_def  end_splice_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_s_last_invariant_begin_transverse_splice:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  begin_transverse_splice))"
  shows "ast_problem.invariant_act x_s_last (ast_domain.instantiate_action_schema  begin_transverse_splice args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_s_last s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  begin_transverse_splice args) s"
  obtain arg2 arg1 where args_2: "args = [arg2,arg1]"
    using assms
    unfolding  begin_transverse_splice_def
    apply auto
    using list_len_2 list_all2_lengthD
    by metis
  show "x_s_last(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  begin_transverse_splice args)) s)"
    using ass
    unfolding x_s_last_def  begin_transverse_splice_def
    apply(auto simp add: args_2)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_s_last_invariant_begin_inverse_splice:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  begin_inverse_splice))"
  shows "ast_problem.invariant_act x_s_last (ast_domain.instantiate_action_schema  begin_inverse_splice args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_s_last s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  begin_inverse_splice args) s"
  obtain arg2 arg1 where args_2: "args = [arg2,arg1]"
    using assms
    unfolding  begin_inverse_splice_def
    apply auto
    using list_len_2 list_all2_lengthD
    by metis
  show "x_s_last(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  begin_inverse_splice args)) s)"
    using ass
    unfolding x_s_last_def  begin_inverse_splice_def
    apply(auto simp add: args_2)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_s_last_invariant_begin_inverse_splice_special_case:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  begin_inverse_splice_special_case))"
  shows "ast_problem.invariant_act x_s_last (ast_domain.instantiate_action_schema  begin_inverse_splice_special_case args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_s_last s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  begin_inverse_splice_special_case args) s"
  obtain arg1 where args_1: "args = [arg1]"
    using assms
    unfolding  begin_inverse_splice_special_case_def
    apply auto
    using list_len_1 list_all2_lengthD
    by metis
  show "x_s_last(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  begin_inverse_splice_special_case args)) s)"
    using ass
    unfolding x_s_last_def  begin_inverse_splice_special_case_def
    apply(auto simp add: args_1)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_s_last_invariant_continue_inverse_splice_a:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  continue_inverse_splice_a))"
  shows "ast_problem.invariant_act x_s_last (ast_domain.instantiate_action_schema  continue_inverse_splice_a args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_s_last s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  continue_inverse_splice_a args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  continue_inverse_splice_a_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_s_last(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  continue_inverse_splice_a args)) s)"
    using ass
    unfolding x_s_last_def  continue_inverse_splice_a_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_s_last_invariant_continue_inverse_splice_b:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  continue_inverse_splice_b))"
  shows "ast_problem.invariant_act x_s_last (ast_domain.instantiate_action_schema  continue_inverse_splice_b args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_s_last s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  continue_inverse_splice_b args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  continue_inverse_splice_b_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_s_last(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  continue_inverse_splice_b args)) s)"
    using ass
    unfolding x_s_last_def  continue_inverse_splice_b_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_s_last_invariant_end_inverse_splice_a:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  end_inverse_splice_a))"
  shows "ast_problem.invariant_act x_s_last (ast_domain.instantiate_action_schema  end_inverse_splice_a args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_s_last s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  end_inverse_splice_a args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  end_inverse_splice_a_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_s_last(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  end_inverse_splice_a args)) s)"
    using ass
    unfolding x_s_last_def  end_inverse_splice_a_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_s_last_invariant_end_inverse_splice_b:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  end_inverse_splice_b))"
  shows "ast_problem.invariant_act x_s_last (ast_domain.instantiate_action_schema  end_inverse_splice_b args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_s_last s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  end_inverse_splice_b args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  end_inverse_splice_b_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_s_last(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  end_inverse_splice_b args)) s)"
    using ass
    unfolding x_s_last_def  end_inverse_splice_b_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_s_last_invariant_reset_1:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  reset_1))"
  shows "ast_problem.invariant_act x_s_last (ast_domain.instantiate_action_schema  reset_1 args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_s_last s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  reset_1 args) s"
  obtain arg1 where args_1: "args = [arg1]"
    using assms
    unfolding  reset_1_def
    apply auto
    using list_len_1 list_all2_lengthD
    by metis
  show "x_s_last(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  reset_1 args)) s)"
    using ass
    unfolding x_s_last_def  reset_1_def
    apply(auto simp add: args_1)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed
lemma x_s_last_for_prob_dom:
  assumes "PI = (Problem (prob_dom) (obj) (I) (G))"
  shows "ast_problem.invariant_wf_plan_act_seq PI x_s_last as"
  apply(rule ast_problem.invariant_for_plan_act_seq)
  apply(rule ast_problem.invariant_action_insts_imp_invariant_plan_actions[where ?Q = x_s_last])
  using ast_problem.invariant_for_plan_act_seq assms distinct_act_names
x_s_last_invariant_begin_cut x_s_last_invariant_continue_cut x_s_last_invariant_end_cut x_s_last_invariant_begin_transpose_splice x_s_last_invariant_continue_splice x_s_last_invariant_end_splice x_s_last_invariant_begin_transverse_splice x_s_last_invariant_begin_inverse_splice x_s_last_invariant_begin_inverse_splice_special_case x_s_last_invariant_continue_inverse_splice_a x_s_last_invariant_continue_inverse_splice_b x_s_last_invariant_end_inverse_splice_a x_s_last_invariant_end_inverse_splice_b x_s_last_invariant_reset_1
    unfolding prob_dom_def dom_actions_def ast_problem.action_params_match_def
begin_cut_def continue_cut_def end_cut_def begin_transpose_splice_def continue_splice_def end_splice_def begin_transverse_splice_def begin_inverse_splice_def begin_inverse_splice_special_case_def continue_inverse_splice_a_def continue_inverse_splice_b_def end_inverse_splice_a_def end_inverse_splice_b_def reset_1_def
  by auto


lemma x_last_cut_invariant_begin_cut:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  begin_cut))"
  shows "ast_problem.invariant_act x_last_cut (ast_domain.instantiate_action_schema  begin_cut args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_last_cut s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  begin_cut args) s"
  obtain arg2 arg1 where args_2: "args = [arg2,arg1]"
    using assms
    unfolding  begin_cut_def
    apply auto
    using list_len_2 list_all2_lengthD
    by metis
  show "x_last_cut(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  begin_cut args)) s)"
    using ass
    unfolding x_last_cut_def  begin_cut_def
    apply(auto simp add: args_2)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_last_cut_invariant_continue_cut:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  continue_cut))"
  shows "ast_problem.invariant_act x_last_cut (ast_domain.instantiate_action_schema  continue_cut args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_last_cut s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  continue_cut args) s"
  obtain arg2 arg1 where args_2: "args = [arg2,arg1]"
    using assms
    unfolding  continue_cut_def
    apply auto
    using list_len_2 list_all2_lengthD
    by metis
  show "x_last_cut(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  continue_cut args)) s)"
    using ass
    unfolding x_last_cut_def  continue_cut_def
    apply(auto simp add: args_2)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_last_cut_invariant_end_cut:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  end_cut))"
  shows "ast_problem.invariant_act x_last_cut (ast_domain.instantiate_action_schema  end_cut args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_last_cut s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  end_cut args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  end_cut_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_last_cut(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  end_cut args)) s)"
    using ass
    unfolding x_last_cut_def  end_cut_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_last_cut_invariant_begin_transpose_splice:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  begin_transpose_splice))"
  shows "ast_problem.invariant_act x_last_cut (ast_domain.instantiate_action_schema  begin_transpose_splice args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_last_cut s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  begin_transpose_splice args) s"
  obtain arg2 arg1 where args_2: "args = [arg2,arg1]"
    using assms
    unfolding  begin_transpose_splice_def
    apply auto
    using list_len_2 list_all2_lengthD
    by metis
  show "x_last_cut(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  begin_transpose_splice args)) s)"
    using ass
    unfolding x_last_cut_def  begin_transpose_splice_def
    apply(auto simp add: args_2)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_last_cut_invariant_continue_splice:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  continue_splice))"
  shows "ast_problem.invariant_act x_last_cut (ast_domain.instantiate_action_schema  continue_splice args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_last_cut s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  continue_splice args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  continue_splice_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_last_cut(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  continue_splice args)) s)"
    using ass
    unfolding x_last_cut_def  continue_splice_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_last_cut_invariant_end_splice:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  end_splice))"
  shows "ast_problem.invariant_act x_last_cut (ast_domain.instantiate_action_schema  end_splice args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_last_cut s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  end_splice args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  end_splice_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_last_cut(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  end_splice args)) s)"
    using ass
    unfolding x_last_cut_def  end_splice_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_last_cut_invariant_begin_transverse_splice:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  begin_transverse_splice))"
  shows "ast_problem.invariant_act x_last_cut (ast_domain.instantiate_action_schema  begin_transverse_splice args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_last_cut s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  begin_transverse_splice args) s"
  obtain arg2 arg1 where args_2: "args = [arg2,arg1]"
    using assms
    unfolding  begin_transverse_splice_def
    apply auto
    using list_len_2 list_all2_lengthD
    by metis
  show "x_last_cut(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  begin_transverse_splice args)) s)"
    using ass
    unfolding x_last_cut_def  begin_transverse_splice_def
    apply(auto simp add: args_2)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_last_cut_invariant_begin_inverse_splice:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  begin_inverse_splice))"
  shows "ast_problem.invariant_act x_last_cut (ast_domain.instantiate_action_schema  begin_inverse_splice args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_last_cut s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  begin_inverse_splice args) s"
  obtain arg2 arg1 where args_2: "args = [arg2,arg1]"
    using assms
    unfolding  begin_inverse_splice_def
    apply auto
    using list_len_2 list_all2_lengthD
    by metis
  show "x_last_cut(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  begin_inverse_splice args)) s)"
    using ass
    unfolding x_last_cut_def  begin_inverse_splice_def
    apply(auto simp add: args_2)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_last_cut_invariant_begin_inverse_splice_special_case:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  begin_inverse_splice_special_case))"
  shows "ast_problem.invariant_act x_last_cut (ast_domain.instantiate_action_schema  begin_inverse_splice_special_case args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_last_cut s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  begin_inverse_splice_special_case args) s"
  obtain arg1 where args_1: "args = [arg1]"
    using assms
    unfolding  begin_inverse_splice_special_case_def
    apply auto
    using list_len_1 list_all2_lengthD
    by metis
  show "x_last_cut(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  begin_inverse_splice_special_case args)) s)"
    using ass
    unfolding x_last_cut_def  begin_inverse_splice_special_case_def
    apply(auto simp add: args_1)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_last_cut_invariant_continue_inverse_splice_a:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  continue_inverse_splice_a))"
  shows "ast_problem.invariant_act x_last_cut (ast_domain.instantiate_action_schema  continue_inverse_splice_a args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_last_cut s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  continue_inverse_splice_a args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  continue_inverse_splice_a_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_last_cut(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  continue_inverse_splice_a args)) s)"
    using ass
    unfolding x_last_cut_def  continue_inverse_splice_a_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_last_cut_invariant_continue_inverse_splice_b:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  continue_inverse_splice_b))"
  shows "ast_problem.invariant_act x_last_cut (ast_domain.instantiate_action_schema  continue_inverse_splice_b args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_last_cut s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  continue_inverse_splice_b args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  continue_inverse_splice_b_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_last_cut(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  continue_inverse_splice_b args)) s)"
    using ass
    unfolding x_last_cut_def  continue_inverse_splice_b_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_last_cut_invariant_end_inverse_splice_a:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  end_inverse_splice_a))"
  shows "ast_problem.invariant_act x_last_cut (ast_domain.instantiate_action_schema  end_inverse_splice_a args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_last_cut s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  end_inverse_splice_a args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  end_inverse_splice_a_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_last_cut(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  end_inverse_splice_a args)) s)"
    using ass
    unfolding x_last_cut_def  end_inverse_splice_a_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_last_cut_invariant_end_inverse_splice_b:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  end_inverse_splice_b))"
  shows "ast_problem.invariant_act x_last_cut (ast_domain.instantiate_action_schema  end_inverse_splice_b args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_last_cut s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  end_inverse_splice_b args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  end_inverse_splice_b_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_last_cut(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  end_inverse_splice_b args)) s)"
    using ass
    unfolding x_last_cut_def  end_inverse_splice_b_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_last_cut_invariant_reset_1:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  reset_1))"
  shows "ast_problem.invariant_act x_last_cut (ast_domain.instantiate_action_schema  reset_1 args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_last_cut s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  reset_1 args) s"
  obtain arg1 where args_1: "args = [arg1]"
    using assms
    unfolding  reset_1_def
    apply auto
    using list_len_1 list_all2_lengthD
    by metis
  show "x_last_cut(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  reset_1 args)) s)"
    using ass
    unfolding x_last_cut_def  reset_1_def
    apply(auto simp add: args_1)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed
lemma x_last_cut_for_prob_dom:
  assumes "PI = (Problem (prob_dom) (obj) (I) (G))"
  shows "ast_problem.invariant_wf_plan_act_seq PI x_last_cut as"
  apply(rule ast_problem.invariant_for_plan_act_seq)
  apply(rule ast_problem.invariant_action_insts_imp_invariant_plan_actions[where ?Q = x_last_cut])
  using ast_problem.invariant_for_plan_act_seq assms distinct_act_names
x_last_cut_invariant_begin_cut x_last_cut_invariant_continue_cut x_last_cut_invariant_end_cut x_last_cut_invariant_begin_transpose_splice x_last_cut_invariant_continue_splice x_last_cut_invariant_end_splice x_last_cut_invariant_begin_transverse_splice x_last_cut_invariant_begin_inverse_splice x_last_cut_invariant_begin_inverse_splice_special_case x_last_cut_invariant_continue_inverse_splice_a x_last_cut_invariant_continue_inverse_splice_b x_last_cut_invariant_end_inverse_splice_a x_last_cut_invariant_end_inverse_splice_b x_last_cut_invariant_reset_1
    unfolding prob_dom_def dom_actions_def ast_problem.action_params_match_def
begin_cut_def continue_cut_def end_cut_def begin_transpose_splice_def continue_splice_def end_splice_def begin_transverse_splice_def begin_inverse_splice_def begin_inverse_splice_special_case_def continue_inverse_splice_a_def continue_inverse_splice_b_def end_inverse_splice_a_def end_inverse_splice_b_def reset_1_def
  by auto


lemma x_cut_point_1_invariant_begin_cut:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  begin_cut))"
  shows "ast_problem.invariant_act x_cut_point_1 (ast_domain.instantiate_action_schema  begin_cut args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_cut_point_1 s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  begin_cut args) s"
  obtain arg2 arg1 where args_2: "args = [arg2,arg1]"
    using assms
    unfolding  begin_cut_def
    apply auto
    using list_len_2 list_all2_lengthD
    by metis
  show "x_cut_point_1(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  begin_cut args)) s)"
    using ass
    unfolding x_cut_point_1_def  begin_cut_def
    apply(auto simp add: args_2)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_cut_point_1_invariant_continue_cut:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  continue_cut))"
  shows "ast_problem.invariant_act x_cut_point_1 (ast_domain.instantiate_action_schema  continue_cut args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_cut_point_1 s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  continue_cut args) s"
  obtain arg2 arg1 where args_2: "args = [arg2,arg1]"
    using assms
    unfolding  continue_cut_def
    apply auto
    using list_len_2 list_all2_lengthD
    by metis
  show "x_cut_point_1(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  continue_cut args)) s)"
    using ass
    unfolding x_cut_point_1_def  continue_cut_def
    apply(auto simp add: args_2)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_cut_point_1_invariant_end_cut:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  end_cut))"
  shows "ast_problem.invariant_act x_cut_point_1 (ast_domain.instantiate_action_schema  end_cut args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_cut_point_1 s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  end_cut args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  end_cut_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_cut_point_1(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  end_cut args)) s)"
    using ass
    unfolding x_cut_point_1_def  end_cut_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_cut_point_1_invariant_begin_transpose_splice:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  begin_transpose_splice))"
  shows "ast_problem.invariant_act x_cut_point_1 (ast_domain.instantiate_action_schema  begin_transpose_splice args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_cut_point_1 s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  begin_transpose_splice args) s"
  obtain arg2 arg1 where args_2: "args = [arg2,arg1]"
    using assms
    unfolding  begin_transpose_splice_def
    apply auto
    using list_len_2 list_all2_lengthD
    by metis
  show "x_cut_point_1(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  begin_transpose_splice args)) s)"
    using ass
    unfolding x_cut_point_1_def  begin_transpose_splice_def
    apply(auto simp add: args_2)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_cut_point_1_invariant_continue_splice:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  continue_splice))"
  shows "ast_problem.invariant_act x_cut_point_1 (ast_domain.instantiate_action_schema  continue_splice args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_cut_point_1 s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  continue_splice args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  continue_splice_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_cut_point_1(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  continue_splice args)) s)"
    using ass
    unfolding x_cut_point_1_def  continue_splice_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_cut_point_1_invariant_end_splice:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  end_splice))"
  shows "ast_problem.invariant_act x_cut_point_1 (ast_domain.instantiate_action_schema  end_splice args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_cut_point_1 s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  end_splice args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  end_splice_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_cut_point_1(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  end_splice args)) s)"
    using ass
    unfolding x_cut_point_1_def  end_splice_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_cut_point_1_invariant_begin_transverse_splice:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  begin_transverse_splice))"
  shows "ast_problem.invariant_act x_cut_point_1 (ast_domain.instantiate_action_schema  begin_transverse_splice args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_cut_point_1 s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  begin_transverse_splice args) s"
  obtain arg2 arg1 where args_2: "args = [arg2,arg1]"
    using assms
    unfolding  begin_transverse_splice_def
    apply auto
    using list_len_2 list_all2_lengthD
    by metis
  show "x_cut_point_1(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  begin_transverse_splice args)) s)"
    using ass
    unfolding x_cut_point_1_def  begin_transverse_splice_def
    apply(auto simp add: args_2)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_cut_point_1_invariant_begin_inverse_splice:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  begin_inverse_splice))"
  shows "ast_problem.invariant_act x_cut_point_1 (ast_domain.instantiate_action_schema  begin_inverse_splice args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_cut_point_1 s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  begin_inverse_splice args) s"
  obtain arg2 arg1 where args_2: "args = [arg2,arg1]"
    using assms
    unfolding  begin_inverse_splice_def
    apply auto
    using list_len_2 list_all2_lengthD
    by metis
  show "x_cut_point_1(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  begin_inverse_splice args)) s)"
    using ass
    unfolding x_cut_point_1_def  begin_inverse_splice_def
    apply(auto simp add: args_2)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_cut_point_1_invariant_begin_inverse_splice_special_case:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  begin_inverse_splice_special_case))"
  shows "ast_problem.invariant_act x_cut_point_1 (ast_domain.instantiate_action_schema  begin_inverse_splice_special_case args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_cut_point_1 s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  begin_inverse_splice_special_case args) s"
  obtain arg1 where args_1: "args = [arg1]"
    using assms
    unfolding  begin_inverse_splice_special_case_def
    apply auto
    using list_len_1 list_all2_lengthD
    by metis
  show "x_cut_point_1(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  begin_inverse_splice_special_case args)) s)"
    using ass
    unfolding x_cut_point_1_def  begin_inverse_splice_special_case_def
    apply(auto simp add: args_1)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_cut_point_1_invariant_continue_inverse_splice_a:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  continue_inverse_splice_a))"
  shows "ast_problem.invariant_act x_cut_point_1 (ast_domain.instantiate_action_schema  continue_inverse_splice_a args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_cut_point_1 s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  continue_inverse_splice_a args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  continue_inverse_splice_a_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_cut_point_1(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  continue_inverse_splice_a args)) s)"
    using ass
    unfolding x_cut_point_1_def  continue_inverse_splice_a_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_cut_point_1_invariant_continue_inverse_splice_b:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  continue_inverse_splice_b))"
  shows "ast_problem.invariant_act x_cut_point_1 (ast_domain.instantiate_action_schema  continue_inverse_splice_b args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_cut_point_1 s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  continue_inverse_splice_b args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  continue_inverse_splice_b_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_cut_point_1(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  continue_inverse_splice_b args)) s)"
    using ass
    unfolding x_cut_point_1_def  continue_inverse_splice_b_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_cut_point_1_invariant_end_inverse_splice_a:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  end_inverse_splice_a))"
  shows "ast_problem.invariant_act x_cut_point_1 (ast_domain.instantiate_action_schema  end_inverse_splice_a args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_cut_point_1 s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  end_inverse_splice_a args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  end_inverse_splice_a_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_cut_point_1(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  end_inverse_splice_a args)) s)"
    using ass
    unfolding x_cut_point_1_def  end_inverse_splice_a_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_cut_point_1_invariant_end_inverse_splice_b:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  end_inverse_splice_b))"
  shows "ast_problem.invariant_act x_cut_point_1 (ast_domain.instantiate_action_schema  end_inverse_splice_b args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_cut_point_1 s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  end_inverse_splice_b args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  end_inverse_splice_b_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_cut_point_1(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  end_inverse_splice_b args)) s)"
    using ass
    unfolding x_cut_point_1_def  end_inverse_splice_b_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_cut_point_1_invariant_reset_1:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  reset_1))"
  shows "ast_problem.invariant_act x_cut_point_1 (ast_domain.instantiate_action_schema  reset_1 args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_cut_point_1 s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  reset_1 args) s"
  obtain arg1 where args_1: "args = [arg1]"
    using assms
    unfolding  reset_1_def
    apply auto
    using list_len_1 list_all2_lengthD
    by metis
  show "x_cut_point_1(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  reset_1 args)) s)"
    using ass
    unfolding x_cut_point_1_def  reset_1_def
    apply(auto simp add: args_1)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed
lemma x_cut_point_1_for_prob_dom:
  assumes "PI = (Problem (prob_dom) (obj) (I) (G))"
  shows "ast_problem.invariant_wf_plan_act_seq PI x_cut_point_1 as"
  apply(rule ast_problem.invariant_for_plan_act_seq)
  apply(rule ast_problem.invariant_action_insts_imp_invariant_plan_actions[where ?Q = x_cut_point_1])
  using ast_problem.invariant_for_plan_act_seq assms distinct_act_names
x_cut_point_1_invariant_begin_cut x_cut_point_1_invariant_continue_cut x_cut_point_1_invariant_end_cut x_cut_point_1_invariant_begin_transpose_splice x_cut_point_1_invariant_continue_splice x_cut_point_1_invariant_end_splice x_cut_point_1_invariant_begin_transverse_splice x_cut_point_1_invariant_begin_inverse_splice x_cut_point_1_invariant_begin_inverse_splice_special_case x_cut_point_1_invariant_continue_inverse_splice_a x_cut_point_1_invariant_continue_inverse_splice_b x_cut_point_1_invariant_end_inverse_splice_a x_cut_point_1_invariant_end_inverse_splice_b x_cut_point_1_invariant_reset_1
    unfolding prob_dom_def dom_actions_def ast_problem.action_params_match_def
begin_cut_def continue_cut_def end_cut_def begin_transpose_splice_def continue_splice_def end_splice_def begin_transverse_splice_def begin_inverse_splice_def begin_inverse_splice_special_case_def continue_inverse_splice_a_def continue_inverse_splice_b_def end_inverse_splice_a_def end_inverse_splice_b_def reset_1_def
  by auto


lemma x_splice_point_1_invariant_begin_cut:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  begin_cut))"
  shows "ast_problem.invariant_act x_splice_point_1 (ast_domain.instantiate_action_schema  begin_cut args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_splice_point_1 s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  begin_cut args) s"
  obtain arg2 arg1 where args_2: "args = [arg2,arg1]"
    using assms
    unfolding  begin_cut_def
    apply auto
    using list_len_2 list_all2_lengthD
    by metis
  show "x_splice_point_1(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  begin_cut args)) s)"
    using ass
    unfolding x_splice_point_1_def  begin_cut_def
    apply(auto simp add: args_2)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_splice_point_1_invariant_continue_cut:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  continue_cut))"
  shows "ast_problem.invariant_act x_splice_point_1 (ast_domain.instantiate_action_schema  continue_cut args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_splice_point_1 s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  continue_cut args) s"
  obtain arg2 arg1 where args_2: "args = [arg2,arg1]"
    using assms
    unfolding  continue_cut_def
    apply auto
    using list_len_2 list_all2_lengthD
    by metis
  show "x_splice_point_1(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  continue_cut args)) s)"
    using ass
    unfolding x_splice_point_1_def  continue_cut_def
    apply(auto simp add: args_2)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_splice_point_1_invariant_end_cut:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  end_cut))"
  shows "ast_problem.invariant_act x_splice_point_1 (ast_domain.instantiate_action_schema  end_cut args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_splice_point_1 s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  end_cut args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  end_cut_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_splice_point_1(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  end_cut args)) s)"
    using ass
    unfolding x_splice_point_1_def  end_cut_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_splice_point_1_invariant_begin_transpose_splice:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  begin_transpose_splice))"
  shows "ast_problem.invariant_act x_splice_point_1 (ast_domain.instantiate_action_schema  begin_transpose_splice args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_splice_point_1 s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  begin_transpose_splice args) s"
  obtain arg2 arg1 where args_2: "args = [arg2,arg1]"
    using assms
    unfolding  begin_transpose_splice_def
    apply auto
    using list_len_2 list_all2_lengthD
    by metis
  show "x_splice_point_1(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  begin_transpose_splice args)) s)"
    using ass
    unfolding x_splice_point_1_def  begin_transpose_splice_def
    apply(auto simp add: args_2)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_splice_point_1_invariant_continue_splice:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  continue_splice))"
  shows "ast_problem.invariant_act x_splice_point_1 (ast_domain.instantiate_action_schema  continue_splice args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_splice_point_1 s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  continue_splice args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  continue_splice_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_splice_point_1(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  continue_splice args)) s)"
    using ass
    unfolding x_splice_point_1_def  continue_splice_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_splice_point_1_invariant_end_splice:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  end_splice))"
  shows "ast_problem.invariant_act x_splice_point_1 (ast_domain.instantiate_action_schema  end_splice args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_splice_point_1 s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  end_splice args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  end_splice_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_splice_point_1(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  end_splice args)) s)"
    using ass
    unfolding x_splice_point_1_def  end_splice_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_splice_point_1_invariant_begin_transverse_splice:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  begin_transverse_splice))"
  shows "ast_problem.invariant_act x_splice_point_1 (ast_domain.instantiate_action_schema  begin_transverse_splice args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_splice_point_1 s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  begin_transverse_splice args) s"
  obtain arg2 arg1 where args_2: "args = [arg2,arg1]"
    using assms
    unfolding  begin_transverse_splice_def
    apply auto
    using list_len_2 list_all2_lengthD
    by metis
  show "x_splice_point_1(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  begin_transverse_splice args)) s)"
    using ass
    unfolding x_splice_point_1_def  begin_transverse_splice_def
    apply(auto simp add: args_2)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_splice_point_1_invariant_begin_inverse_splice:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  begin_inverse_splice))"
  shows "ast_problem.invariant_act x_splice_point_1 (ast_domain.instantiate_action_schema  begin_inverse_splice args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_splice_point_1 s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  begin_inverse_splice args) s"
  obtain arg2 arg1 where args_2: "args = [arg2,arg1]"
    using assms
    unfolding  begin_inverse_splice_def
    apply auto
    using list_len_2 list_all2_lengthD
    by metis
  show "x_splice_point_1(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  begin_inverse_splice args)) s)"
    using ass
    unfolding x_splice_point_1_def  begin_inverse_splice_def
    apply(auto simp add: args_2)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_splice_point_1_invariant_begin_inverse_splice_special_case:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  begin_inverse_splice_special_case))"
  shows "ast_problem.invariant_act x_splice_point_1 (ast_domain.instantiate_action_schema  begin_inverse_splice_special_case args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_splice_point_1 s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  begin_inverse_splice_special_case args) s"
  obtain arg1 where args_1: "args = [arg1]"
    using assms
    unfolding  begin_inverse_splice_special_case_def
    apply auto
    using list_len_1 list_all2_lengthD
    by metis
  show "x_splice_point_1(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  begin_inverse_splice_special_case args)) s)"
    using ass
    unfolding x_splice_point_1_def  begin_inverse_splice_special_case_def
    apply(auto simp add: args_1)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_splice_point_1_invariant_continue_inverse_splice_a:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  continue_inverse_splice_a))"
  shows "ast_problem.invariant_act x_splice_point_1 (ast_domain.instantiate_action_schema  continue_inverse_splice_a args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_splice_point_1 s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  continue_inverse_splice_a args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  continue_inverse_splice_a_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_splice_point_1(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  continue_inverse_splice_a args)) s)"
    using ass
    unfolding x_splice_point_1_def  continue_inverse_splice_a_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_splice_point_1_invariant_continue_inverse_splice_b:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  continue_inverse_splice_b))"
  shows "ast_problem.invariant_act x_splice_point_1 (ast_domain.instantiate_action_schema  continue_inverse_splice_b args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_splice_point_1 s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  continue_inverse_splice_b args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  continue_inverse_splice_b_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_splice_point_1(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  continue_inverse_splice_b args)) s)"
    using ass
    unfolding x_splice_point_1_def  continue_inverse_splice_b_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_splice_point_1_invariant_end_inverse_splice_a:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  end_inverse_splice_a))"
  shows "ast_problem.invariant_act x_splice_point_1 (ast_domain.instantiate_action_schema  end_inverse_splice_a args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_splice_point_1 s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  end_inverse_splice_a args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  end_inverse_splice_a_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_splice_point_1(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  end_inverse_splice_a args)) s)"
    using ass
    unfolding x_splice_point_1_def  end_inverse_splice_a_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_splice_point_1_invariant_end_inverse_splice_b:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  end_inverse_splice_b))"
  shows "ast_problem.invariant_act x_splice_point_1 (ast_domain.instantiate_action_schema  end_inverse_splice_b args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_splice_point_1 s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  end_inverse_splice_b args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  end_inverse_splice_b_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_splice_point_1(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  end_inverse_splice_b args)) s)"
    using ass
    unfolding x_splice_point_1_def  end_inverse_splice_b_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_splice_point_1_invariant_reset_1:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  reset_1))"
  shows "ast_problem.invariant_act x_splice_point_1 (ast_domain.instantiate_action_schema  reset_1 args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_splice_point_1 s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  reset_1 args) s"
  obtain arg1 where args_1: "args = [arg1]"
    using assms
    unfolding  reset_1_def
    apply auto
    using list_len_1 list_all2_lengthD
    by metis
  show "x_splice_point_1(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  reset_1 args)) s)"
    using ass
    unfolding x_splice_point_1_def  reset_1_def
    apply(auto simp add: args_1)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed
lemma x_splice_point_1_for_prob_dom:
  assumes "PI = (Problem (prob_dom) (obj) (I) (G))"
  shows "ast_problem.invariant_wf_plan_act_seq PI x_splice_point_1 as"
  apply(rule ast_problem.invariant_for_plan_act_seq)
  apply(rule ast_problem.invariant_action_insts_imp_invariant_plan_actions[where ?Q = x_splice_point_1])
  using ast_problem.invariant_for_plan_act_seq assms distinct_act_names
x_splice_point_1_invariant_begin_cut x_splice_point_1_invariant_continue_cut x_splice_point_1_invariant_end_cut x_splice_point_1_invariant_begin_transpose_splice x_splice_point_1_invariant_continue_splice x_splice_point_1_invariant_end_splice x_splice_point_1_invariant_begin_transverse_splice x_splice_point_1_invariant_begin_inverse_splice x_splice_point_1_invariant_begin_inverse_splice_special_case x_splice_point_1_invariant_continue_inverse_splice_a x_splice_point_1_invariant_continue_inverse_splice_b x_splice_point_1_invariant_end_inverse_splice_a x_splice_point_1_invariant_end_inverse_splice_b x_splice_point_1_invariant_reset_1
    unfolding prob_dom_def dom_actions_def ast_problem.action_params_match_def
begin_cut_def continue_cut_def end_cut_def begin_transpose_splice_def continue_splice_def end_splice_def begin_transverse_splice_def begin_inverse_splice_def begin_inverse_splice_special_case_def continue_inverse_splice_a_def continue_inverse_splice_b_def end_inverse_splice_a_def end_inverse_splice_b_def reset_1_def
  by auto


lemma x_splice_point_2_invariant_begin_cut:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  begin_cut))"
  shows "ast_problem.invariant_act x_splice_point_2 (ast_domain.instantiate_action_schema  begin_cut args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_splice_point_2 s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  begin_cut args) s"
  obtain arg2 arg1 where args_2: "args = [arg2,arg1]"
    using assms
    unfolding  begin_cut_def
    apply auto
    using list_len_2 list_all2_lengthD
    by metis
  show "x_splice_point_2(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  begin_cut args)) s)"
    using ass
    unfolding x_splice_point_2_def  begin_cut_def
    apply(auto simp add: args_2)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_splice_point_2_invariant_continue_cut:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  continue_cut))"
  shows "ast_problem.invariant_act x_splice_point_2 (ast_domain.instantiate_action_schema  continue_cut args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_splice_point_2 s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  continue_cut args) s"
  obtain arg2 arg1 where args_2: "args = [arg2,arg1]"
    using assms
    unfolding  continue_cut_def
    apply auto
    using list_len_2 list_all2_lengthD
    by metis
  show "x_splice_point_2(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  continue_cut args)) s)"
    using ass
    unfolding x_splice_point_2_def  continue_cut_def
    apply(auto simp add: args_2)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_splice_point_2_invariant_end_cut:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  end_cut))"
  shows "ast_problem.invariant_act x_splice_point_2 (ast_domain.instantiate_action_schema  end_cut args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_splice_point_2 s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  end_cut args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  end_cut_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_splice_point_2(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  end_cut args)) s)"
    using ass
    unfolding x_splice_point_2_def  end_cut_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_splice_point_2_invariant_begin_transpose_splice:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  begin_transpose_splice))"
  shows "ast_problem.invariant_act x_splice_point_2 (ast_domain.instantiate_action_schema  begin_transpose_splice args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_splice_point_2 s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  begin_transpose_splice args) s"
  obtain arg2 arg1 where args_2: "args = [arg2,arg1]"
    using assms
    unfolding  begin_transpose_splice_def
    apply auto
    using list_len_2 list_all2_lengthD
    by metis
  show "x_splice_point_2(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  begin_transpose_splice args)) s)"
    using ass
    unfolding x_splice_point_2_def  begin_transpose_splice_def
    apply(auto simp add: args_2)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_splice_point_2_invariant_continue_splice:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  continue_splice))"
  shows "ast_problem.invariant_act x_splice_point_2 (ast_domain.instantiate_action_schema  continue_splice args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_splice_point_2 s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  continue_splice args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  continue_splice_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_splice_point_2(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  continue_splice args)) s)"
    using ass
    unfolding x_splice_point_2_def  continue_splice_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_splice_point_2_invariant_end_splice:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  end_splice))"
  shows "ast_problem.invariant_act x_splice_point_2 (ast_domain.instantiate_action_schema  end_splice args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_splice_point_2 s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  end_splice args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  end_splice_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_splice_point_2(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  end_splice args)) s)"
    using ass
    unfolding x_splice_point_2_def  end_splice_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_splice_point_2_invariant_begin_transverse_splice:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  begin_transverse_splice))"
  shows "ast_problem.invariant_act x_splice_point_2 (ast_domain.instantiate_action_schema  begin_transverse_splice args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_splice_point_2 s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  begin_transverse_splice args) s"
  obtain arg2 arg1 where args_2: "args = [arg2,arg1]"
    using assms
    unfolding  begin_transverse_splice_def
    apply auto
    using list_len_2 list_all2_lengthD
    by metis
  show "x_splice_point_2(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  begin_transverse_splice args)) s)"
    using ass
    unfolding x_splice_point_2_def  begin_transverse_splice_def
    apply(auto simp add: args_2)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_splice_point_2_invariant_begin_inverse_splice:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  begin_inverse_splice))"
  shows "ast_problem.invariant_act x_splice_point_2 (ast_domain.instantiate_action_schema  begin_inverse_splice args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_splice_point_2 s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  begin_inverse_splice args) s"
  obtain arg2 arg1 where args_2: "args = [arg2,arg1]"
    using assms
    unfolding  begin_inverse_splice_def
    apply auto
    using list_len_2 list_all2_lengthD
    by metis
  show "x_splice_point_2(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  begin_inverse_splice args)) s)"
    using ass
    unfolding x_splice_point_2_def  begin_inverse_splice_def
    apply(auto simp add: args_2)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_splice_point_2_invariant_begin_inverse_splice_special_case:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  begin_inverse_splice_special_case))"
  shows "ast_problem.invariant_act x_splice_point_2 (ast_domain.instantiate_action_schema  begin_inverse_splice_special_case args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_splice_point_2 s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  begin_inverse_splice_special_case args) s"
  obtain arg1 where args_1: "args = [arg1]"
    using assms
    unfolding  begin_inverse_splice_special_case_def
    apply auto
    using list_len_1 list_all2_lengthD
    by metis
  show "x_splice_point_2(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  begin_inverse_splice_special_case args)) s)"
    using ass
    unfolding x_splice_point_2_def  begin_inverse_splice_special_case_def
    apply(auto simp add: args_1)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_splice_point_2_invariant_continue_inverse_splice_a:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  continue_inverse_splice_a))"
  shows "ast_problem.invariant_act x_splice_point_2 (ast_domain.instantiate_action_schema  continue_inverse_splice_a args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_splice_point_2 s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  continue_inverse_splice_a args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  continue_inverse_splice_a_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_splice_point_2(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  continue_inverse_splice_a args)) s)"
    using ass
    unfolding x_splice_point_2_def  continue_inverse_splice_a_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_splice_point_2_invariant_continue_inverse_splice_b:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  continue_inverse_splice_b))"
  shows "ast_problem.invariant_act x_splice_point_2 (ast_domain.instantiate_action_schema  continue_inverse_splice_b args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_splice_point_2 s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  continue_inverse_splice_b args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  continue_inverse_splice_b_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_splice_point_2(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  continue_inverse_splice_b args)) s)"
    using ass
    unfolding x_splice_point_2_def  continue_inverse_splice_b_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_splice_point_2_invariant_end_inverse_splice_a:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  end_inverse_splice_a))"
  shows "ast_problem.invariant_act x_splice_point_2 (ast_domain.instantiate_action_schema  end_inverse_splice_a args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_splice_point_2 s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  end_inverse_splice_a args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  end_inverse_splice_a_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_splice_point_2(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  end_inverse_splice_a args)) s)"
    using ass
    unfolding x_splice_point_2_def  end_inverse_splice_a_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_splice_point_2_invariant_end_inverse_splice_b:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  end_inverse_splice_b))"
  shows "ast_problem.invariant_act x_splice_point_2 (ast_domain.instantiate_action_schema  end_inverse_splice_b args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_splice_point_2 s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  end_inverse_splice_b args) s"
  obtain arg3 arg2 arg1 where args_3: "args = [arg3,arg2,arg1]"
    using assms
    unfolding  end_inverse_splice_b_def
    apply auto
    using list_len_3 list_all2_lengthD
    by metis
  show "x_splice_point_2(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  end_inverse_splice_b args)) s)"
    using ass
    unfolding x_splice_point_2_def  end_inverse_splice_b_def
    apply(auto simp add: args_3)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed


lemma x_splice_point_2_invariant_reset_1:
assumes "list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  reset_1))"
  shows "ast_problem.invariant_act x_splice_point_2 (ast_domain.instantiate_action_schema  reset_1 args)"
  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def
proof(safe)
  fix s assume ass: "x_splice_point_2 s" "ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  reset_1 args) s"
  obtain arg1 where args_1: "args = [arg1]"
    using assms
    unfolding  reset_1_def
    apply auto
    using list_len_1 list_all2_lengthD
    by metis
  show "x_splice_point_2(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  reset_1 args)) s)"
    using ass
    unfolding x_splice_point_2_def  reset_1_def
    apply(auto simp add: args_1)
        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)
qed
lemma x_splice_point_2_for_prob_dom:
  assumes "PI = (Problem (prob_dom) (obj) (I) (G))"
  shows "ast_problem.invariant_wf_plan_act_seq PI x_splice_point_2 as"
  apply(rule ast_problem.invariant_for_plan_act_seq)
  apply(rule ast_problem.invariant_action_insts_imp_invariant_plan_actions[where ?Q = x_splice_point_2])
  using ast_problem.invariant_for_plan_act_seq assms distinct_act_names
x_splice_point_2_invariant_begin_cut x_splice_point_2_invariant_continue_cut x_splice_point_2_invariant_end_cut x_splice_point_2_invariant_begin_transpose_splice x_splice_point_2_invariant_continue_splice x_splice_point_2_invariant_end_splice x_splice_point_2_invariant_begin_transverse_splice x_splice_point_2_invariant_begin_inverse_splice x_splice_point_2_invariant_begin_inverse_splice_special_case x_splice_point_2_invariant_continue_inverse_splice_a x_splice_point_2_invariant_continue_inverse_splice_b x_splice_point_2_invariant_end_inverse_splice_a x_splice_point_2_invariant_end_inverse_splice_b x_splice_point_2_invariant_reset_1
    unfolding prob_dom_def dom_actions_def ast_problem.action_params_match_def
begin_cut_def continue_cut_def end_cut_def begin_transpose_splice_def continue_splice_def end_splice_def begin_transverse_splice_def begin_inverse_splice_def begin_inverse_splice_special_case_def continue_inverse_splice_a_def continue_inverse_splice_b_def end_inverse_splice_a_def end_inverse_splice_b_def reset_1_def
  by auto

end
