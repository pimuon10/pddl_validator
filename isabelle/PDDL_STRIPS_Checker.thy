section \<open>Executable PDDL Checker\<close>
theory PDDL_STRIPS_Checker
imports 
  PDDL_STRIPS_Semantics

  Error_Monad_Add
  
  "~~/src/HOL/Library/Char_ord"
  "~~/src/HOL/Library/Code_Char"
  "~~/src/HOL/Library/Code_Target_Nat"
    
  "Containers.Containers"
begin
      
subsection \<open>Implementation Refinements\<close>

subsubsection \<open>Of-Type\<close>
text \<open>We exploit the flat type hierarchy to efficiently implement the 
  subtype-check\<close>
context ast_domain begin  
  
  lemma rtrancl_subtype_rel_alt: "subtype_rel\<^sup>* = ({''object''} \<times> UNIV)\<^sup>="
    unfolding subtype_rel_def
    apply (auto)
    apply (meson SigmaD1 converse_rtranclE singleton_iff)
    done        
    
  lemma of_type_code: 
    "of_type oT T \<longleftrightarrow> (
        ''object'' \<in> set (primitives T)) 
      \<or> set (primitives oT) \<subseteq> set (primitives T)"
    unfolding of_type_def rtrancl_subtype_rel_alt
    by auto  
  
end -- \<open>Context of \<open>ast_domain\<close>\<close> 

subsubsection \<open>Application of Effects\<close>

context ast_domain begin  
  text \<open>We implement the application of an effect by explicit iteration over 
    the additions and deletions\<close>
  fun apply_effect_exec 
    :: "object atom formula ast_effect \<Rightarrow> world_model \<Rightarrow> world_model" 
  where
    "apply_effect_exec (Effect adds dels) s 
      = fold (\<lambda>add s. Set.insert add s) adds 
          (fold (\<lambda>del s. Set.remove del s) dels s)"

  lemma apply_effect_exec_refine[simp]: 
    "apply_effect_exec (Effect (adds) (dels)) s 
    = apply_effect (Effect (adds) (dels)) s"
  proof(induction adds arbitrary: s)
    case Nil
    then show ?case
    proof(induction dels arbitrary: s)
      case Nil
      then show ?case by auto
    next
      case (Cons a dels)
      then show ?case 
        by (auto simp add: image_def)
    qed
  next
    case (Cons a adds)
    then show ?case
    proof(induction dels arbitrary: s)
      case Nil
      then show ?case by (auto; metis Set.insert_def sup_assoc insert_iff) 
    next
      case (Cons a dels)
      then show ?case 
        by (auto simp: Un_commute minus_set_fold union_set_fold)
    qed
  qed

  lemmas apply_effect_eq_impl_eq 
    = apply_effect_exec_refine[symmetric, unfolded apply_effect_exec.simps]
  
end -- \<open>Context of \<open>ast_domain\<close>\<close>
  
subsubsection \<open>Well-Foundedness\<close>    

context ast_problem begin  

  text \<open> We start by defining a mapping from objects to types. The container 
    framework will generate efficient, red-black tree based code for that 
    later. \<close>
    
  type_synonym objT = "(object, type) mapping"
  
  definition mp_objT :: "(object, type) mapping" where
    "mp_objT = Mapping.of_alist (objects P)"
      
  lemma mp_objT_correct[simp]: "Mapping.lookup mp_objT = objT"    
    unfolding mp_objT_def objT_def
    by transfer (simp add: Map_To_Mapping.map_apply_def)

  text \<open>We refine the typecheck to use the mapping\<close>      
    
  definition "is_obj_of_type_impl mp n T = (
    case Mapping.lookup mp n of None \<Rightarrow> False | Some oT \<Rightarrow> of_type oT T
  )" 
      
  lemma is_obj_of_type_impl_correct[simp]:
    "is_obj_of_type_impl mp_objT = is_obj_of_type"
    apply (intro ext)
    apply (auto simp: is_obj_of_type_impl_def is_obj_of_type_def)  
    done
    
  text \<open>We refine the well-formedness checks to use the mapping\<close>      
    
  definition wf_fact' :: "objT \<Rightarrow> fact \<Rightarrow> bool"
    where
    "wf_fact' ot \<equiv> wf_atom (Mapping.lookup ot)"
      
  lemma wf_fact'_correct[simp]: "wf_fact' mp_objT = wf_fact"
    by (auto simp: wf_fact'_def wf_fact_def)

  definition "wf_fmla_atom' mp f 
    = (case f of formula.Atom atm \<Rightarrow> (wf_fact' mp atm) | _ \<Rightarrow> False)"
    
  lemma wf_problem_impl_eq:
    "wf_problem \<longleftrightarrow> (let mp = mp_objT in
      wf_domain
    \<and> distinct (map fst (objects P))
    \<and> (\<forall>(n,T)\<in>set (objects P). wf_type T)
    \<and> distinct (init P)
    \<and> (\<forall>f\<in>set (init P). wf_fmla_atom' mp f)
    \<and> wf_fmla (Mapping.lookup mp) (goal P))
    "
    unfolding wf_problem_def wf_fmla_atom'_def wf_world_model_def 
    and wf_fmla_atom_alt
    apply (simp; safe)
    subgoal by (auto simp: wf_fact_def split: formula.split)
    subgoal for \<phi> by (cases \<phi>) auto
    subgoal for \<phi>
      apply (clarsimp simp: wf_fact_def split: formula.splits)
      by (cases \<phi>) auto
    done
  
    
  text \<open>Instantiating actions will yield well-founded effects. 
    Corollary of @{thm wf_instantiate_action_schema}.\<close>  
  lemma wf_effect_inst_weak:
    fixes a args
    defines "ai \<equiv> instantiate_action_schema a args"
    assumes A: "action_params_match a args"
      "wf_action_schema a"
    shows "wf_effect_inst (effect ai)"  
    using wf_instantiate_action_schema[OF A] unfolding ai_def[symmetric] 
    by (cases ai) (auto simp: wf_effect_inst_alt)
    
    
end -- \<open>Context of \<open>ast_problem\<close>\<close>


context wf_ast_domain begin    
  text \<open>Resolving an action yields a well-founded action schema.\<close>
  (* TODO: This must be implicitly proved when showing that plan execution 
    preserves wf. Try to remove this redundancy!*)
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
  
end -- \<open>Context of \<open>ast_domain\<close>\<close>
    

subsubsection \<open>Execution of Plan Actions\<close>

text \<open>We will perform two refinement steps, to summarize redundant operations\<close>

text \<open>We first lift action schema lookup into the error monad. \<close>  
context ast_domain begin  
  definition "resolve_action_schemaE n \<equiv> 
    lift_opt 
      (resolve_action_schema n) 
      (ERR (shows ''No such action schema '' o shows n))"  
end -- \<open>Context of \<open>ast_domain\<close>\<close>
  
context ast_problem begin  
  
(*TODO: change to this valuation definition to hanlde equalities nicely
definition "valuation s \<equiv> \<lambda>x. case x of (atom.Atom P ARGS) \<Rightarrow> 
                                                ((formula.Atom x) \<in> s)
                                    | (atom.Eq t1 t2) \<Rightarrow> (t1 = t2)"

primrec holds :: "'a formula set \<Rightarrow> 'a formula \<Rightarrow> bool" where
"holds s (Atom k) = ((Atom k) \<in> s)" |
"holds _ \<bottom> = False" |
"holds s (Not F) = (\<not> (holds s F))" |
"holds s (And F G) = (holds s F \<and> holds s G)" |
"holds s (Or F G) = (holds s F \<or> holds s G)" |
"holds s (Imp F G) = (holds s F \<longrightarrow> holds s G)"

  lemma holds_for_valid_formulas:
        assumes "\<forall>x\<in>s. \<exists>x'. x = formula.Atom x'"
        shows "s \<TTurnstile> F \<Longrightarrow> holds s F"
        unfolding holds_def entailment_def
        using assms
        apply (induction F; auto)
        subgoal for x apply(cases x)*)

    
  text \<open>We define a function to determine whether a formula holds in 
    a world model\<close>
  definition "holds M F \<equiv> (valuation M) \<Turnstile> F"

  text \<open>Justification of this function\<close>
  lemma holds_for_wf_fmlas:
    assumes "\<forall>x\<in>s. is_Atom x" "wf_fmla Q F"
    shows "holds s F \<longleftrightarrow> s \<TTurnstile> F"
    unfolding holds_def entailment_def valuation_def
    using assms
  proof (induction F)
    case (Atom x)
    then show ?case 
      apply auto
      by (metis formula_semantics.simps(1) is_Atom.elims(2) valuation_def)
  next
    case (Or F1 F2)
    then show ?case 
      apply simp apply (safe; clarsimp?)
      by (metis (mono_tags) is_Atom.elims(2) formula_semantics.simps(1))
  qed auto

  text \<open>The first refinement summarizes the enabledness check and the execution 
    of the action. Moreover, we implement the precondition evaluation by our
     @{const holds} function. This way, we can eliminate redundant resolving 
     and instantiation of the action.
  \<close>      
  definition en_exE :: "plan_action \<Rightarrow> world_model \<Rightarrow> _+world_model" where
    "en_exE \<equiv> \<lambda>(PAction n args) \<Rightarrow> \<lambda>s. do {
      a \<leftarrow> resolve_action_schemaE n;
      check (action_params_match a args) (ERRS ''Parameter mismatch'');
      let ai = instantiate_action_schema a args;
      check (wf_effect_inst (effect ai)) (ERRS ''Effect not well-formed'');    
      check ( holds s (precondition ai)) (ERRS ''Precondition not satisfied'');
      Error_Monad.return (apply_effect (effect ai) s)
    }"
  
  text \<open>Justification of implementation.\<close>  
  lemma (in wf_ast_problem) en_exE_return_iff: 
    assumes "\<forall>x\<in>s. is_Atom x"
    shows "en_exE a s = Inr s' 
      \<longleftrightarrow> plan_action_enabled a s \<and> s' = execute_plan_action a s"
    apply (cases a)
    using assms holds_for_wf_fmlas wf_domain
    unfolding plan_action_enabled_def execute_plan_action_def 
      and execute_ast_action_inst_def en_exE_def wf_domain_def
    apply (clarsimp 
        split: option.splits 
        simp: resolve_action_schemaE_def return_iff)
    by (metis ast_action_inst.collapse holds_for_wf_fmlas resolve_action_wf 
              wf_action_inst.simps wf_instantiate_action_schema)    
    
  text \<open>Next, we use the efficient implementation @{const is_obj_of_type_impl} 
    for the type check, and omit the well-formedness check, as effects obtained
    from instantiating well-formed action schemas are always well-formed
    (@{thm [source] wf_effect_inst_weak}).\<close>  
  abbreviation "action_params_match2 mp a args 
    \<equiv> list_all2 (is_obj_of_type_impl mp) 
        args (map snd (ast_action_schema.parameters a))"
    
  definition en_exE2 
    :: "(object, type) mapping \<Rightarrow> plan_action \<Rightarrow> world_model \<Rightarrow> _+world_model" 
  where
    "en_exE2 mp \<equiv> \<lambda>(PAction n args) \<Rightarrow> \<lambda>s. do {
      a \<leftarrow> resolve_action_schemaE n;
      check (action_params_match2 mp a args) (ERRS ''Parameter mismatch'');
      let ai = instantiate_action_schema a args;
      check (holds s (precondition ai)) (ERRS ''Precondition not satisfied'');
      Error_Monad.return (apply_effect (effect ai) s)
    }"
      
  text \<open>Justification of refinement\<close>  
  lemma (in wf_ast_problem) wf_en_exE2_eq:
    shows "en_exE2 mp_objT pa s = en_exE pa s"
    apply (cases pa; simp add: en_exE2_def en_exE_def Let_def)
    apply (auto 
      simp: return_iff resolve_action_schemaE_def resolve_action_wf 
      simp: wf_effect_inst_weak action_params_match_def
      split: error_monad_bind_split)
    done
    
  text \<open>Combination of the two refinement lemmas\<close>  
  lemma (in wf_ast_problem) en_exE2_return_iff: 
    assumes "\<forall>x\<in>s. is_Atom x"
    shows "en_exE2 mp_objT a s = Inr s' 
      \<longleftrightarrow> plan_action_enabled a s \<and> s' = execute_plan_action a s"
    unfolding wf_en_exE2_eq 
    apply (subst en_exE_return_iff)
    using assms
    by (auto)

  lemma (in wf_ast_problem) en_exE2_return_iff_compact_notation: 
    "\<lbrakk>\<forall>x\<in>s. is_Atom x\<rbrakk> \<Longrightarrow> 
      en_exE2 mp_objT a s = Inr s' 
      \<longleftrightarrow> plan_action_enabled a s \<and> s' = execute_plan_action a s"
    using en_exE2_return_iff .
    
end -- \<open>Context of \<open>ast_problem\<close>\<close>

subsubsection \<open>Checking of Plan\<close>

context ast_problem begin            
    
  text \<open>First, we combine the well-formedness check of the plan actions and 
    their execution into a single iteration.\<close>
  fun valid_plan_from1 :: "world_model \<Rightarrow> plan \<Rightarrow> bool" where
    "valid_plan_from1 s [] \<longleftrightarrow> s \<TTurnstile> (goal P)"  
  | "valid_plan_from1 s (\<pi>#\<pi>s) 
      \<longleftrightarrow> plan_action_enabled \<pi> s 
        \<and> (valid_plan_from1 (execute_plan_action \<pi> s) \<pi>s)"
    
  lemma valid_plan_from1_refine: "valid_plan_from s \<pi>s = valid_plan_from1 s \<pi>s"
  proof(induction \<pi>s arbitrary: s)
    case Nil
    then show ?case by (auto simp add: plan_action_path_def valid_plan_from_def)
  next
    case (Cons a \<pi>s)
    then show ?case 
      by (auto 
        simp: valid_plan_from_def plan_action_path_def plan_action_enabled_def 
        simp: execute_ast_action_inst_def execute_plan_action_def)
  qed      
    
  text \<open>Next, we use our efficient combined enabledness check and execution 
    function, and transfer the implementation to use the error monad: \<close>
  fun valid_plan_fromE 
    :: "(object, type) mapping \<Rightarrow> nat \<Rightarrow> world_model \<Rightarrow> plan \<Rightarrow> _+unit" 
  where
    "valid_plan_fromE mp si s [] 
      = check (holds s (goal P)) (ERRS ''Postcondition does not hold'')"
  | "valid_plan_fromE mp si s (\<pi>#\<pi>s) = do {
        s \<leftarrow> en_exE2 mp \<pi> s 
          <+? (\<lambda>e _. shows ''at step '' o shows si o shows '': '' o e ());
        valid_plan_fromE mp (si+1) s \<pi>s
      }"


  text \<open>For the refinement, we need to show that the world models only 
    contain atoms, i.e., containing only atoms is an invariant under execution
    of well-formed plan actions.\<close>    
  lemma (in wf_ast_problem) wf_actions_only_add_atoms: 
    "\<lbrakk> \<forall>x\<in>s. is_Atom x; wf_plan_action a \<rbrakk> 
      \<Longrightarrow> \<forall>x\<in>execute_plan_action a s. is_Atom x"
    using wf_problem wf_domain
    unfolding wf_problem_def wf_domain_def
    apply (cases a) 
    apply (clarsimp 
      split: option.splits 
      simp: wf_fmla_atom_alt execute_plan_action_def 
      simp: execute_ast_action_inst_def)
    subgoal for n args schema fmla
      apply (cases "effect (instantiate_action_schema schema args)"; simp)
      by (metis ast_action_inst.sel(2) ast_domain.wf_effect.simps 
            ast_domain.wf_fmla_atom_alt resolve_action_wf 
            wf_action_inst.elims(2) wf_instantiate_action_schema)
    done
      
  text \<open>Refinement lemma for our plan checking algorithm\<close>
  lemma (in wf_ast_problem) valid_plan_fromE_return_iff[return_iff]:
    assumes "\<forall>x\<in>s. is_Atom x"
    shows "valid_plan_fromE mp_objT k s \<pi>s = Inr () \<longleftrightarrow> valid_plan_from s \<pi>s"
    using assms unfolding valid_plan_from1_refine
  proof (induction mp\<equiv>mp_objT k s \<pi>s rule: valid_plan_fromE.induct)
    case (1 si s)
    then show ?case
      using wf_problem holds_for_wf_fmlas 
      by (auto 
        simp: return_iff Let_def wf_en_exE2_eq wf_problem_def
        split: plan_action.split)
  next
    case (2 si s \<pi> \<pi>s)
    then show ?case
      apply (clarsimp 
        simp: return_iff en_exE2_return_iff
        split: plan_action.split)
      by (meson ast_problem.plan_action_enabled_def wf_actions_only_add_atoms)
  qed

  lemmas valid_plan_fromE_return_iff'[return_iff] 
    = wf_ast_problem.valid_plan_fromE_return_iff[of P, OF wf_ast_problem.intro]
  
  (* TODO: This function is unused! *)  
  (*fun apply_effect_exec'' 
    :: "object atom ast_effect \<Rightarrow> world_model \<Rightarrow> world_model" 
    where
    "apply_effect_exec'' (Effect (adds) (dels)) s 
      = fold (%add s. insert add s) 
          (map formula.Atom adds) 
          (fold (%del s. Set.remove del s) (map formula.Atom dels) s)"
  *)      
      
      
end -- \<open>Context of \<open>ast_problem\<close>\<close> 

subsection \<open>Executable Plan Checker\<close>
text \<open>We obtain the main plan checker by combining the well-formedness check 
  and executability check. \<close>

definition "check_plan P \<pi>s \<equiv> do {
  check (ast_problem.wf_problem P) (ERRS ''Domain/Problem not well-formed'');
  ast_problem.valid_plan_fromE P (ast_problem.mp_objT P) 1 (ast_problem.I P) \<pi>s
}" 
 
text \<open>Correctness theorem of the plan checker: It returns @{term "Inr ()"}
  if and only if the problem is well-formed and the plan is valid.
\<close>
theorem check_plan_return_iff[return_iff]: "check_plan P \<pi>s = Inr () 
  \<longleftrightarrow> ast_problem.wf_problem P \<and> ast_problem.valid_plan P \<pi>s"
proof -
  interpret ast_problem P .
  show ?thesis    
    unfolding check_plan_def 
    apply (auto 
      simp: return_iff wf_world_model_def wf_fmla_atom_alt I_def wf_problem_def) 
    apply (metis ast_domain.wf_fmla_atom_alt ast_problem.I_def 
                ast_problem.valid_plan_def valid_plan_fromE_return_iff' 
                wf_fmla_atom.elims(2) wf_problem_def wf_world_model_def)
    by (metis (full_types) ast_domain.wf_fmla_atom_alt ast_problem.I_def 
             ast_problem.valid_plan_def ast_problem.valid_plan_fromE_return_iff'
             wf_fmla_atom.elims(2) wf_problem_def wf_world_model_def)
qed      



subsection \<open>Code Setup\<close>

text \<open>In this section, we set up the code generator to generate verified 
  code for our plan checker.\<close>

subsubsection \<open>Code Equations\<close>
text \<open>We first register the code equations for the functions of the checker.
  Note that we not necessarily register the original code equations, but also 
  optimized ones.
\<close>

lemmas wf_domain_code = 
  ast_domain.sig_def 
  ast_domain.wf_type.simps
  ast_domain.wf_predicate_decl.simps
  ast_domain.wf_domain_def
  ast_domain.wf_action_schema.simps
  ast_domain.wf_effect.simps
  ast_domain.wf_fmla.simps
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
  (*ast_problem.wf_effect_inst_weak.simps*)
  
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
  ast_domain.apply_effect_exec.simps
  (*ast_domain.apply_effect_exec'.simps*)
  ast_domain.apply_effect_eq_impl_eq
  (*ast_domain.apply_atomic.simps*)
  ast_problem.holds_def
  ast_problem.mp_objT_def
  ast_problem.is_obj_of_type_impl_def
  ast_domain.wf_fmla_atom.simps
  ast_problem.wf_fmla_atom'_def
  valuation_def
declare check_code[code]  
  
subsubsection \<open>Setup for Containers Framework\<close>    
    
derive ceq predicate atom object formula
derive ccompare predicate atom object formula
derive (rbt) set_impl atom formula
    
derive (rbt) mapping_impl object   
  
derive linorder predicate object atom "object atom formula"
    
subsubsection \<open>More Efficient Distinctness Check for Linorders\<close>
(* TODO: Can probably be optimized even more. *)
fun no_stutter :: "'a list \<Rightarrow> bool" where
  "no_stutter [] = True"
| "no_stutter [_] = True"  
| "no_stutter (a#b#l) = (a\<noteq>b \<and> no_stutter (b#l))"  
  
lemma sorted_no_stutter_eq_distinct: "sorted l \<Longrightarrow> no_stutter l \<longleftrightarrow> distinct l"
  apply (induction l rule: no_stutter.induct)
  apply (auto simp: sorted_Cons)
  done
  
definition distinct_ds :: "'a::linorder list \<Rightarrow> bool" 
  where "distinct_ds l \<equiv> no_stutter (quicksort l)"
  
lemma [code_unfold]: "distinct = distinct_ds"  
  apply (intro ext)
  unfolding distinct_ds_def
  apply (auto simp: sorted_no_stutter_eq_distinct)
  done  
    
    
  

subsubsection \<open>Code Generation\<close>
export_code 
  check_plan 
  nat_of_integer integer_of_nat Inl Inr 
  predAtm Eq predicate Pred Either Var Obj PredDecl BigAnd BigOr 
  formula.Not formula.Bot Effect ast_action_schema.Action_Schema 
  map_atom Domain Problem PAction 
  in SML
  module_name PDDL_Checker_Exported
  file "code/PDDL_STRIPS_Checker_Exported.sml"

      
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
end -- \<open>Theory\<close>
