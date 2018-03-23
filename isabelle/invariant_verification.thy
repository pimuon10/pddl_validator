section \<open>Reasoning about Invariants\<close>
theory invariant_verification
  imports PDDL_STRIPS_Semantics 
begin

(*<*)
(* Hacky internal stuff, not shown in proof document *)
lemma list_len_1: "(length l = 1) = (\<exists>a. l = [a])"
  by (cases "l", auto)

lemma list_len_2: "(length l = 2) = (\<exists>a b. l = [a, b])"
  apply auto
  apply(cases "l", auto)
proof-
  fix a list assume "length list = Suc 0" and "l = a # list"
  then show "\<exists>b. list = [b]"
    by(cases "list", auto)
qed

lemma list_len_3: "(length l = 3) = (\<exists>a b c. l = [a, b, c])"
  apply auto
  apply(cases "l", auto)
  using list_len_2 by auto

lemma list_len_4: "(length l = 4) = (\<exists>a b c d. l = [a, b, c, d])"
  apply auto
  apply(cases "l", auto)
  using list_len_3 by auto

(*>*)

context ast_domain begin
  definition "is_invariant_inst Q \<alpha> \<longleftrightarrow> 
    (\<forall>M. Q M \<and> M \<TTurnstile> precondition \<alpha>
    \<longrightarrow> Q (execute_ast_action_inst \<alpha> M))"

end

  
context ast_problem begin

text \<open>An invariant is preserved by all actions of the problem\<close>
definition "is_invariant Q \<equiv> \<forall>\<pi> M. Q M \<and> plan_action_enabled \<pi> M 
  \<longrightarrow> Q (execute_plan_action \<pi> M)"


text \<open>Shortcut for enabledness of action instance.\<close>
definition ast_action_inst_enabled :: "ast_action_inst \<Rightarrow> world_model \<Rightarrow> bool" 
  where "ast_action_inst_enabled act s \<longleftrightarrow>  s \<TTurnstile> (precondition act)"

text \<open>\<open>Q\<close> is preserved by action instance \<open>\<alpha>\<close>. \<close>
definition "invariant_act Q \<alpha> = 
  (\<forall>M. Q M \<and> ast_action_inst_enabled \<alpha> M 
    \<longrightarrow> Q (execute_ast_action_inst \<alpha> M))"

text \<open>\<open>Q\<close> is preserved by executing a sequence of action instances \<open>\<alpha>s\<close>. \<close>
definition "invariant Q \<alpha>s = 
  (\<forall>M M'. Q M \<and> ast_action_inst_path M \<alpha>s M' \<longrightarrow> Q M')"

text \<open>If all action instances in a set preserve the invariant, 
  also sequences of these instances preserve the invariant. \<close>  
lemma invariant_for_as:
  assumes "\<And>\<alpha>. \<alpha>\<in>A \<Longrightarrow> invariant_act Q \<alpha>"
  assumes "set \<alpha>s \<subseteq> A"
  shows "invariant Q \<alpha>s"
  using assms(2)
  apply (induction \<alpha>s)
  using assms(1)
  by (auto simp: invariant_def invariant_act_def ast_action_inst_enabled_def)

text \<open>Invariant wrt. a plan action. 
  Note that the invariant only needs to hold for well-formed plan actions, 
  as implicitly contained in @{const plan_action_enabled}.
  \<close>  
definition "invariant_wf_plan_act Q \<pi> 
  = (\<forall>M. Q M \<and>  plan_action_enabled \<pi> M \<longrightarrow> Q (execute_plan_action \<pi> M))"

text \<open>Invariant wrt. a sequence of well-formed plan actions. \<close>
definition "invariant_wf_plan_act_seq Q \<pi>s 
  = (\<forall>M M'. Q M \<and> plan_action_path M \<pi>s M' \<longrightarrow>  Q M')"

text \<open>An invariant wrt.\ all plan actions is preserved by paths\<close>  
lemma invariant_for_plan_act_seq:
  assumes "\<And>\<pi>. invariant_wf_plan_act Q \<pi>"
  shows "invariant_wf_plan_act_seq Q \<pi>s"
  apply (induction \<pi>s)
  using assms 
  by (auto simp: invariant_wf_plan_act_seq_def invariant_wf_plan_act_def)

text \<open>We can introduce an invariant by showing that it is invariant for 
  any possible action instance. \<close>  
lemma invariant_action_insts_imp_invariant_plan_actions:
  assumes "\<And>a args. a \<in> set (actions D) \<and> action_params_match a args 
    \<Longrightarrow> invariant_act Q (instantiate_action_schema a args)" 
  shows "invariant_wf_plan_act Q \<pi>"
  unfolding invariant_wf_plan_act_def
proof(safe) (* TODO: This proof works by unfolding and folding through 
  many different levels of definitions. Perhaps some aux-lemmas might be 
  helpful to structure this better, and avoid redundancies in similar proofs. *)  
  fix M 
  assume I0: "Q M" 
  assume EN: "plan_action_enabled \<pi> M"
  obtain n args where [simp]: "\<pi> = (PAction n args)" 
    by (cases \<pi>)
  
  from EN obtain a where
    X1: "a \<in> set (actions D)" "action_params_match a args" 
    and X2: "M \<TTurnstile> precondition (instantiate_action_schema a args)"
    and [simp]: "resolve_action_schema n = Some a"
    by (auto 
      simp: plan_action_enabled_def resolve_action_schema_def
      split: option.splits 
      dest: index_by_eq_SomeD) 
  from X1 assms have "invariant_act Q (instantiate_action_schema a args)" 
    by blast
  with I0 EN X2 show "Q (execute_plan_action \<pi> M)"
    by (auto simp: ast_action_inst_enabled_def
      invariant_act_def execute_plan_action_def 
      execute_ast_action_inst_def)
qed

end

end
