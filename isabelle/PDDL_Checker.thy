theory PDDL_Checker
imports 
  PDDL_Parser
  Error_Monad_Add
  "Containers.Containers"
begin
      
  subsection \<open>Implementation Refinements\<close>
      
  context wf_ast_domain begin    
    lemma resolve_action_wf: 
      assumes "resolve_action_schema n = Some a"
      shows "wf_action_schema a"
    proof -    
      from wf_domain have 
        X1: "distinct (map ast_action_schema.name (actions D))"
        and X2: "\<forall>a\<in>set (actions D). wf_action_schema a"
        unfolding wf_domain_def by auto
    
      show ?thesis
        using assms unfolding resolve_action_schema_def 
        by (auto simp add: index_by_eq_Some_eq[OF X1] X2)
    qed  
    
  end
      
  context ast_domain begin  
    thm of_type_def
    
    lemma rtrancl_subtype_rel_alt: "subtype_rel\<^sup>* = ({''object''} \<times> UNIV)\<^sup>="
      unfolding subtype_rel_def
      apply (auto)
      apply (meson SigmaD1 converse_rtranclE singleton_iff)
      done        
      
    lemma of_type_code: 
      "of_type oT T \<longleftrightarrow> (''object'' \<in> set (primitives T)) \<or> set (primitives oT) \<subseteq> set (primitives T)"
      unfolding of_type_def rtrancl_subtype_rel_alt
      by auto  
    
    term resolve_action_schema   
      
    definition "resolve_action_schemaE n \<equiv> 
      lift_opt (resolve_action_schema n) (ERR (shows ''No such action schema '' o shows n))"  
          
        
  end  
    
  context ast_problem begin  

    type_synonym objT = "(object, type) mapping"
    
    definition mp_objT :: "(object, type) mapping" where
      "mp_objT = Mapping.of_alist (objects P)"
        
    lemma mp_objT_correct[simp]: "Mapping.lookup mp_objT = objT"    
      unfolding mp_objT_def objT_def
      by transfer (simp add: Map_To_Mapping.map_apply_def)
    
    definition wf_fact' :: "objT \<Rightarrow> fact \<Rightarrow> bool"
      where
      "wf_fact' ot \<equiv> wf_atom (Mapping.lookup ot)"
        
    lemma wf_fact'_correct[simp]: "wf_fact' mp_objT = wf_fact"
      by (auto simp: wf_fact'_def wf_fact_def)
      

    lemma wf_problem_impl_eq:
      "wf_problem \<equiv> let mp = mp_objT in
        wf_domain
      \<and> distinct (map fst (objects P))
      \<and> (\<forall>(n,T)\<in>set (objects P). wf_type T)
      \<and> distinct (init P)
      \<and> (\<forall>f\<in>set (init P). wf_fact' mp f)
      \<and> wf_prop (Mapping.lookup mp) (goal P)
      "
      unfolding wf_problem_def
      by (simp) 
        
        
    fun wf_effect_inst_weak :: "object ast_effect \<Rightarrow> bool" where
      "wf_effect_inst_weak (Effect aes) \<longleftrightarrow> True (*distinct (map atom aes)*)" 
    
    
    lemma wf_effect_inst_weak:
      fixes a args
      defines "ai \<equiv> instantiate_action_schema a args"
      assumes A: "list_all2 is_obj_of_type args (map snd (ast_action_schema.parameters a))"
        "wf_action_schema a"
      shows "wf_effect_inst_weak (effect ai) \<longleftrightarrow> wf_effect_inst (effect ai)"  
    proof (cases a)
      case [simp]: (Action_Schema n par pre eff)
       
      {
        assume X1: "list_all2 (is_of_type objT) args (map snd par)"
          
        have "wf_atom objT (map_atom (the \<circ> map_of (zip (map fst par) args)) a)"
          if X2: "wf_atom (map_of par) a" for a :: "variable atom"
        proof (cases a)
          case [simp]: (Atom n xs)
          then show ?thesis 
            using X1 X2 A(2)
            apply (auto split: option.splits simp: Let_def)
            subgoal premises prems for Ts  
              using prems(6,1-4)
              apply (induction xs Ts rule: list_all2_induct)
              subgoal by simp  
              subgoal    
                apply (clarsimp simp: is_of_type_def in_set_conv_nth split: option.splits)
                apply (frule list_all2_lengthD[where xs=args]; simp)
                apply (subst lookup_zip_idx_eq; simp; simp?)+
                apply (drule list_all2_nthD2[where ys="map snd par"]; simp?)
                apply (auto simp: is_of_type_def split: option.splits dest: of_type_trans)
                done
              done
            done
        qed
        hence "wf_atomic_effect objT (map_ast_atomic_effect (the \<circ> map_of (zip (map fst par) args)) ae)"
          if "wf_atomic_effect (map_of par) ae"
          for ae :: "variable ast_atomic_effect"
          using X1 that by (cases ae; simp)
      }  
      then show ?thesis 
        unfolding ai_def
        using A  
        apply (simp add: Let_def)  
        apply (cases eff; auto simp: is_obj_of_type_alt)  
        done  
    qed
        
    definition en_exE :: "plan_action \<Rightarrow> state \<Rightarrow> _+state" where
      "en_exE \<equiv> \<lambda>(PAction n args) \<Rightarrow> \<lambda>s. do {
        a \<leftarrow> resolve_action_schemaE n;
        check (list_all2 is_obj_of_type args (map snd (ast_action_schema.parameters a))) (ERRS ''Parameter mismatch'');
        let ai = instantiate_action_schema a args;
        check (wf_effect_inst (effect ai)) (ERRS ''Effect not well-formed'');    
          (* TODO: Probably, we can prove that instantiation goes to valid objects only!, 
              and save the expensive check here *)
        check (holds s (precondition ai)) (ERRS ''Precondition not satisfied'');
        Error_Monad.return (apply_effect (effect ai) s)
      }"

    lemma en_exE_return_iff[return_iff]: 
      "en_exE a s = Inr s' \<longleftrightarrow> plan_action_enabled a s \<and> s' = execute_plan_action a s"
      apply (cases a)
      unfolding plan_action_enabled_def ast_action_inst_enabled_def execute_plan_action_def execute_ast_action_inst_def en_exE_def 
      by (auto 
          split: option.splits 
          simp: resolve_action_schemaE_def return_iff)
      
      
    definition "is_obj_of_type_impl mp n T = (
      case Mapping.lookup mp n of None \<Rightarrow> False | Some oT \<Rightarrow> of_type oT T
    )" 
        
    lemma is_obj_of_type_impl_correct[simp]:
      "is_obj_of_type_impl mp_objT = is_obj_of_type"
      apply (intro ext)
      apply (auto simp: is_obj_of_type_impl_def is_obj_of_type_def)  
      done
        
    definition en_exE2 :: "(object, type) mapping \<Rightarrow> plan_action \<Rightarrow> state \<Rightarrow> _+state" where
      "en_exE2 mp \<equiv> \<lambda>(PAction n args) \<Rightarrow> \<lambda>s. do {
        a \<leftarrow> resolve_action_schemaE n;
        check (list_all2 (is_obj_of_type_impl mp) args (map snd (ast_action_schema.parameters a))) (\<lambda>_. shows ''Parameter mismatch'');
        let ai = instantiate_action_schema a args;
        check (wf_effect_inst_weak (effect ai)) (ERRS ''Effect not well-formed'');    
          (* TODO: Probably, we can prove that instantiation goes to valid objects only!, 
              and save the expensive check here *)
        check (holds s (precondition ai)) (ERRS ''Precondition not satisfied'');
        Error_Monad.return (apply_effect (effect ai) s)
      }"
        
    lemma (in wf_ast_problem) wf_en_exE2_eq:
      shows "en_exE2 mp_objT pa s = en_exE pa s"
      apply (cases pa; simp add: en_exE2_def en_exE_def Let_def)
      apply (intro Error_Monad.bind_cong refl arg_cong[where f=check, THEN fun_cong])
      apply (rule wf_effect_inst_weak)
      apply (auto simp: return_iff resolve_action_schemaE_def resolve_action_wf)
      done  
      
        
    fun valid_plan_fromE :: "(object, type) mapping \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> plan \<Rightarrow> _+unit" where
      "valid_plan_fromE mp si s [] = check (holds s (goal P)) (ERRS ''Postcondition does not hold'')"
    | "valid_plan_fromE mp si s (\<pi>#\<pi>s) = do {
          s \<leftarrow> en_exE2 mp \<pi> s <+? (\<lambda>e _. shows ''at step '' o shows si o shows '': '' o e ());
          valid_plan_fromE mp (si+1) s \<pi>s
        }"

    lemma (in wf_ast_problem) valid_plan_fromE_return_iff[return_iff]:
      "valid_plan_fromE mp_objT k s \<pi>s = Inr () \<longleftrightarrow> valid_plan_from_explicit s \<pi>s"
      apply (induction mp\<equiv>mp_objT k s \<pi>s rule: valid_plan_fromE.induct)
      by (auto simp: return_iff Let_def wf_en_exE2_eq split: plan_action.split)

    lemmas valid_plan_fromE_return_iff'[return_iff] 
      = wf_ast_problem.valid_plan_fromE_return_iff[of P, OF wf_ast_problem.intro]
        
      
    lemma apply_atomic_impl_eqs:
      "apply_atomic (Add f) s = insert f s"
      "apply_atomic (Del f) s = Set.remove f s"
      by auto
      
(*      
    definition en_ex :: "plan_action \<Rightarrow> state \<rightharpoonup> state" where
      "en_ex \<equiv> \<lambda>(PAction n args) \<Rightarrow> \<lambda>s. do {
        a \<leftarrow> resolve_action_schema n;
        assert_opt (list_all2 is_obj_of_type args (map snd (ast_action_schema.parameters a)));
        let ai = instantiate_action_schema a args;
        assert_opt (wf_effect_inst (effect ai));
        assert_opt (holds s (precondition ai));
        Some (apply_effect (effect ai) s)
      }"
    
    fun valid_plan_from_impl :: "state \<Rightarrow> plan \<rightharpoonup> unit" where
      "valid_plan_from_impl s [] = assert_opt (holds s (goal P))"
    | "valid_plan_from_impl s (\<pi>#\<pi>s) = do {s \<leftarrow> en_ex \<pi> s; valid_plan_from_impl s \<pi>s}"
      
    lemma valid_plan_from_impl: 
      "valid_plan_from s \<pi>s \<longleftrightarrow> valid_plan_from_impl s \<pi>s = Some ()"
      apply (induction s \<pi>s rule: valid_plan_from.induct)
      apply (auto 
          split: Option.bind_splits plan_action.split 
          simp: en_ex_def enabled_def execute_def Let_def
          )  
      done  
*)      
      
  end  
  
  
  subsection \<open>Code Setup\<close>
  
  lemmas wf_domain_code = 
    ast_domain.sig_def 
    ast_domain.wf_type.simps
    ast_domain.wf_predicate_decl.simps
    ast_domain.wf_domain_def
    ast_domain.wf_action_schema.simps
    ast_domain.wf_effect.simps
    ast_domain.wf_prop.simps
    ast_domain.wf_atomic_effect.simps
    ast_domain.wf_atom.simps
    ast_domain.is_of_type_def
    ast_domain.of_type_code
    
  declare wf_domain_code[code]  

  lemmas wf_problem_code = 
    ast_problem.wf_problem_impl_eq
    ast_problem.wf_fact'_def
    (*ast_problem.objT_def*)
    ast_problem.is_obj_of_type_alt
    (*ast_problem.wf_object_def*)
    ast_problem.wf_fact_def
    ast_problem.wf_plan_action.simps
    ast_problem.wf_effect_inst_weak.simps
    
  declare wf_problem_code[code]  
    
  lemmas check_code =
    ast_problem.valid_plan_def
    ast_problem.valid_plan_fromE.simps
    ast_problem.en_exE2_def
    ast_problem.resolve_instantiate.simps
    ast_domain.resolve_action_schema_def
    ast_domain.resolve_action_schemaE_def
    ast_problem.I_def
    ast_domain.instantiate_action_schema.simps
    ast_domain.apply_effect.simps
    ast_problem.apply_atomic_impl_eqs
    (*ast_domain.apply_atomic.simps*)
    ast_domain.holds.simps
    ast_problem.mp_objT_def
    ast_problem.is_obj_of_type_impl_def
    
  declare check_code[code]  
    
  definition "check_plan P \<pi>s \<equiv> do {
    check (ast_problem.wf_problem P) (\<lambda>_::unit. shows ''Domain/Problem not well-formed'');
    ast_problem.valid_plan_fromE P (ast_problem.mp_objT P) 1 (ast_problem.I P) \<pi>s
  }" 
    
  lemma check_plan_return_iff[return_iff]: "check_plan P \<pi>s = Inr () 
    \<longleftrightarrow> ast_problem.wf_problem P \<and> ast_problem.valid_plan P \<pi>s"
  proof -
    interpret ast_problem P .
    show ?thesis    
      unfolding check_plan_def 
      by (auto simp: return_iff valid_plan_explicit)  
  qed      

abbreviation prep_err :: "shows \<Rightarrow> (unit \<Rightarrow> shows) \<Rightarrow> unit \<Rightarrow> shows" where
  "prep_err msg \<equiv> \<lambda>e _. msg o e ()"


  definition parse_check_dpp :: "String.literal \<Rightarrow> String.literal \<Rightarrow> String.literal \<Rightarrow> _ + unit"
    where "parse_check_dpp d p pl \<equiv> do {
      p \<leftarrow> parse_domain_and_problem d p;
      pl \<leftarrow> (parse_plan_file pl <+? prep_err (shows ''Error parsing plan: ''));
      check_plan p pl
    }"

  definition parse_check_dp :: "String.literal \<Rightarrow> String.literal \<Rightarrow> _ + unit"
    where "parse_check_dp d p \<equiv> do {
      p \<leftarrow> parse_domain_and_problem d p;
      check (ast_problem.wf_problem p) (ERRS ''Domain/Problem not well-formed'')
    }"
      

  definition parse_check_p :: "String.literal \<Rightarrow> String.literal \<Rightarrow> String.literal \<Rightarrow> _ + unit"
    where "parse_check_p d p pl \<equiv> do {
      p \<leftarrow> parse_domain_and_problem d p;
      pl \<leftarrow> parse_plan_file pl <+? prep_err (shows ''Error parsing plan: '');
      ast_problem.valid_plan_fromE p (ast_problem.mp_objT p) 1 (ast_problem.I p) pl
    }"
      
      
  (* Version using ML level strings *)    
  definition parse_check_dpp_impl 
    :: "String.literal \<Rightarrow> String.literal \<Rightarrow> String.literal \<Rightarrow> String.literal + unit"
    where
    "parse_check_dpp_impl d p pl \<equiv> parse_check_dpp d p pl <+? (\<lambda>e. String.implode (e () ''''))"

  definition parse_check_dp_impl 
    :: "String.literal \<Rightarrow> String.literal \<Rightarrow> String.literal + unit"
    where
    "parse_check_dp_impl d p \<equiv> parse_check_dp d p <+? (\<lambda>e. String.implode (e () ''''))"

  definition parse_check_p_impl 
    :: "String.literal \<Rightarrow> String.literal \<Rightarrow> String.literal \<Rightarrow> String.literal + unit"
    where
    "parse_check_p_impl d p pl \<equiv> parse_check_p d p pl <+? (\<lambda>e. String.implode (e () ''''))"
    
    
  text \<open>
    The result \<open>Inr ()\<close> is returned if and only if
      \<^item> The domain, problem, and plan can be parsed
      \<^item> The problem (and domain) is well-formed
      \<^item> The plan is a valid plan for the domain and problem
  \<close>    
  lemma parse_check_dpp_return_iff[return_iff]: 
    "parse_check_dpp ds ps pls = Inr () 
    \<longleftrightarrow> (\<exists>D P \<pi>s.
      parse_domain_file ds = Inr D
    \<and> parse_problem_file D ps = Inr P
    \<and> parse_plan_file pls = Inr \<pi>s
    \<and> ast_problem.wf_problem P 
    \<and> ast_problem.valid_plan P \<pi>s
    )" 
    unfolding parse_check_dpp_def parse_domain_and_problem_def
    by (auto simp: return_iff)
    
  theorem parse_check_dpp_impl_return_iff[return_iff]:
    "parse_check_dpp_impl ds ps pls = Inr () 
    \<longleftrightarrow> (\<exists>D P \<pi>s.
      parse_domain_file ds = Inr D
    \<and> parse_problem_file D ps = Inr P
    \<and> parse_plan_file pls = Inr \<pi>s
    \<and> ast_problem.wf_problem P 
    \<and> ast_problem.valid_plan P \<pi>s
    )" 
    unfolding parse_check_dpp_impl_def
    by (auto simp: return_iff)  

  lemma parse_check_dp_return_iff[return_iff]: 
    "parse_check_dp ds ps = Inr () 
    \<longleftrightarrow> (\<exists>D P \<pi>s.
      parse_domain_file ds = Inr D
    \<and> parse_problem_file D ps = Inr P
    \<and> ast_problem.wf_problem P 
    )" 
    unfolding parse_check_dp_def parse_domain_and_problem_def
    by (auto simp: return_iff)
    
  theorem parse_check_dp_impl_return_iff[return_iff]:
    "parse_check_dp_impl ds ps = Inr () 
    \<longleftrightarrow> (\<exists>D P \<pi>s.
      parse_domain_file ds = Inr D
    \<and> parse_problem_file D ps = Inr P
    \<and> ast_problem.wf_problem P 
    )" 
    unfolding parse_check_dp_impl_def
    apply (simp)  
    apply (subst return_iff)  
    by auto  
      
  lemma parse_check_p_return_imp: 
    "parse_check_p ds ps pls = Inr () 
    \<Longrightarrow> (\<exists>D P \<pi>s.
      parse_domain_file ds = Inr D
    \<and> parse_problem_file D ps = Inr P
    \<and> parse_plan_file pls = Inr \<pi>s
    \<and> (ast_problem.wf_problem P \<longrightarrow> ast_problem.valid_plan P \<pi>s)
    )" 
    unfolding parse_check_p_def parse_domain_and_problem_def
    by (auto simp: return_iff ast_problem.valid_plan_fromE_return_iff' ast_problem.valid_plan_explicit)
      

  (* Plan checking without wf-checking ... only used for profiling purposes. 
    This theorem, however, guarantees:
      If the checker succeeds, then the domain, problem, and plan are grammatical correct.
      Under the assumption that domain and problem are also well-formed, the plan is valid.
  *)    
  theorem parse_check_p_impl_return_imp:
    "parse_check_p_impl ds ps pls = Inr () 
    \<Longrightarrow> (\<exists>D P \<pi>s.
      parse_domain_file ds = Inr D
    \<and> parse_problem_file D ps = Inr P
    \<and> parse_plan_file pls = Inr \<pi>s
    \<and> (ast_problem.wf_problem P \<longrightarrow> ast_problem.valid_plan P \<pi>s)
    )" 
    unfolding parse_check_p_impl_def
    by (auto simp: return_iff dest: parse_check_p_return_imp)  

      
      
  (* Setup for containers framework *)    
      
  derive ceq predicate atom object
  derive ccompare predicate atom object 
  derive (rbt) set_impl atom
      
  derive (rbt) mapping_impl object   
    
      
  (* More efficient distinctness check for linear orderings. 
    TODO: Can probably be optimized even more. *)  
  fun dsorted :: "'a list \<Rightarrow> bool" where
    "dsorted [] = True"
  | "dsorted [_] = True"  
  | "dsorted (a#b#l) = (a\<noteq>b \<and> dsorted (b#l))"  
    
  lemma dsorted_correct: "sorted l \<Longrightarrow> dsorted l \<longleftrightarrow> distinct l"
    apply (induction l rule: dsorted.induct)
    apply (auto simp: sorted_Cons)
    done
    
  definition distinct_ds :: "'a::linorder list \<Rightarrow> bool" 
    where "distinct_ds l \<equiv> dsorted (quicksort l)"
    
  lemma [code_unfold]: "distinct = distinct_ds"  
    apply (intro ext)
    unfolding distinct_ds_def
    apply (auto simp: dsorted_correct)
    done  
      
      
  derive linorder predicate object atom    

  (* Setup of some reasonable code-unfold lemmas. 
    TODO: These are declared as code_abbrev in Set.thy already, but 
        seem to have no effect!
  *)  
  lemma [code_unfold]:
    "s \<union> {x} = insert x s"
    "{x} \<union> s = insert x s"
    "s - {x} = Set.remove x s"
    by auto
    
    
  export_code parse_check_dpp_impl parse_check_dp_impl parse_check_p_impl checking SML
      
(* Usage example from within Isabelle *)  
(*    
ML_val \<open>
  let
    val prefix="/home/lammich/devel/isabelle/planning/papers/pddl_validator/experiments/results/"

    fun check name = 
      (name,@{code parse_check_dpp_impl} 
        (file_to_string (prefix ^ name ^ ".dom.pddl"))
        (file_to_string (prefix ^ name ^ ".prob.pddl"))
        (file_to_string (prefix ^ name ^ ".plan")))

  in  
    (*check "IPC5_rovers_p03"*)
    check "Test2_rover_untyped_pfile07"
  end
\<close>  
*)
end
