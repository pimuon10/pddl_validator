theory PDDL_STRIPS_Semantics_Old
imports Main "Propositional_Proof_Systems.Formulas" "Propositional_Proof_Systems.Sema" begin

  definition "index_by f l \<equiv> map_of (map (\<lambda>x. (f x,x)) l)"
  
  lemma index_by_eq_Some_eq[simp]: 
    assumes "distinct (map f l)"
    shows "index_by f l n = Some x \<longleftrightarrow> (x\<in>set l \<and> f x = n)"  
    unfolding index_by_def 
    using assms  
    by (auto simp: o_def)
    
  
  type_synonym name = string
                                                                       
  datatype predicate = Pred (name: name)
  
  datatype 'val atom = predAtm (predicate: predicate) (arguments: "'val list")
                       | Eq (lhs: 'val) (rhs: 'val)
    
  datatype type = Either (primitives: "name list") (* We use singleton lists to model primitive types *)
    
  datatype 'val ast_effect = Effect (Adds: "(('val) list)") (Dels: "(('val) list)")

  datatype variable = varname: Var name
    
  datatype ast_action_schema = Action_Schema
    (name: name)
    (parameters: "(variable \<times> type) list")
    (precondition: "(variable atom) formula")
    (effect: "(variable atom) formula ast_effect")

  datatype predicate_decl = PredDecl 
    (pred: predicate) 
    (argTs: "type list")
    
  datatype ast_domain = Domain
    (types: "name list") (* Only supports flat type hierarchy *)
    (predicates: "predicate_decl list")
    (actions: "ast_action_schema list")

  datatype object = name: Obj name  
  type_synonym fact = "(object atom)"
    
  datatype ast_problem = Problem
    (domain: ast_domain)
    (objects: "(object \<times> type) list")
    (init: "fact formula list")
    (goal: "(object atom) formula")
    
  datatype plan_action = PAction
    (name: name)
    (arguments: "object list")

  type_synonym plan = "plan_action list"  
    
  (* Well-formedness *)  
  
  (*    
    Compute signature: predicate/arity
    Check that all atoms (schemas and facts) satisfy signature
    
    for action:
      Check that used parameters \<subseteq> declared parameters
      
    for init/goal: Check that facts only use declared objects  
  *)    
    
  locale ast_domain = 
    fixes D :: ast_domain
  begin    
    term atoms
    
    definition "sig \<equiv> map_of (map (\<lambda>PredDecl p n \<Rightarrow> (p,n)) (predicates D))"

    definition "subtype_rel \<equiv> {''object''}\<times>UNIV" 
      (* Every type is subtype of object. We do not restrict this to declared 
          types, as well-formedness will ensure that all types are declared. *)
      
    definition of_type :: "type \<Rightarrow> type \<Rightarrow> bool" where
      "of_type oT T \<equiv> set (primitives oT) \<subseteq> subtype_rel\<^sup>* `` set (primitives T)"
      
    context 
      fixes ty_val :: "'val \<rightharpoonup> type"  -- \<open>Value's type, or None if value is invalid\<close>
    begin
      
      definition is_of_type :: "'val \<Rightarrow> type \<Rightarrow> bool" where
        "is_of_type v T \<longleftrightarrow> (
          case ty_val v of
            Some vT \<Rightarrow> of_type vT T
          | None \<Rightarrow> False)"
      
      (*fun wf_atom :: "'val atom \<Rightarrow> bool"  where
        "wf_atom in_atom = 
          (case in_atom of
               (predAtm p vs) \<Rightarrow> (
                  case sig p of 
                  None \<Rightarrow> False
                | Some Ts \<Rightarrow> list_all2 is_of_type vs Ts)
              | (Eq v1 v2) \<Rightarrow> ty_val v1\<noteq>None \<and> ty_val v2\<noteq>None) (* TODO: We could check that types may overlap *)"*)

      fun wf_atom :: "'val atom \<Rightarrow> bool"  where
        "wf_atom in_atom = 
          (case in_atom of
               (predAtm p vs) \<Rightarrow> (
                  case sig p of 
                  None \<Rightarrow> False
                | Some Ts \<Rightarrow> list_all2 is_of_type vs Ts)
              | _ \<Rightarrow> False) (* TODO: We could check that types may overlap *)"


  fun wf_fmla :: "('val atom) formula \<Rightarrow> bool" where
        "wf_fmla (formula.Atom a) \<longleftrightarrow> wf_atom a"
      | "wf_fmla (\<phi>1 \<^bold>\<and> \<phi>2) \<longleftrightarrow> (wf_fmla \<phi>1 \<and> wf_fmla \<phi>2)"  
      | "wf_fmla (\<phi>1 \<^bold>\<or> \<phi>2) \<longleftrightarrow> (wf_fmla \<phi>1 \<and> wf_fmla \<phi>2)"  
      | "wf_fmla (\<^bold>\<not>\<bottom>) \<longleftrightarrow> True"
      | "wf_fmla _ \<longleftrightarrow> False"  

definition "wf_fmla_atom f = (case f of formula.Atom atm \<Rightarrow> (wf_atom atm)
                                           | _ \<Rightarrow> False)"

      lemma wf_fmla_atom_exists: "wf_fmla_atom f = (\<exists>atm. f = formula.Atom atm \<and> wf_atom atm)"
             by (auto simp add: wf_fmla_atom_def; cases f; auto)

      lemma wf_fmla_atom_imp_wf_fmla: "wf_fmla_atom f \<Longrightarrow> wf_fmla f"
            unfolding wf_fmla_atom_def
            by (cases f; auto)

      fun wf_effect where
        "wf_effect (Effect (adds) (dels)) \<longleftrightarrow> 
            ((\<forall>ae\<in>set adds. wf_fmla_atom ae) \<and> (\<forall>de\<in>set dels.  wf_fmla_atom de))"
    
    end
      
    fun wf_action_schema :: "ast_action_schema \<Rightarrow> bool" where   
      "wf_action_schema (Action_Schema n params pre eff) \<longleftrightarrow> (
        let
          tyv = map_of params
        in
          distinct (map fst params)
        \<and> wf_fmla tyv pre
        \<and> wf_effect tyv eff)"
      
    fun wf_type where
      "wf_type (Either Ts) \<longleftrightarrow> set Ts \<subseteq> insert ''object'' (set (types D))"
      
    fun wf_predicate_decl where 
      "wf_predicate_decl (PredDecl p Ts) \<longleftrightarrow> (\<forall>T\<in>set Ts. wf_type T)"
      
    definition wf_domain :: "bool" where
      "wf_domain \<equiv> 
        distinct (types D)
      \<and> distinct (map (predicate_decl.pred) (predicates D))
      \<and> (\<forall>p\<in>set (predicates D). wf_predicate_decl p)
      \<and> distinct (map ast_action_schema.name (actions D))
      \<and> (\<forall>a\<in>set (actions D). wf_action_schema a)
      "

  end  

  locale ast_problem = 
    fixes P :: ast_problem 
  begin  
    abbreviation "D \<equiv> ast_problem.domain P"
    sublocale ast_domain D .
    
    definition objT :: "object \<rightharpoonup> type" where
      "objT \<equiv> map_of (objects P)"
        
    definition wf_fact :: "fact \<Rightarrow> bool" where
      "wf_fact = wf_atom objT"

    definition wf_world_model where "wf_world_model M = (\<forall>f\<in>M.  wf_fmla_atom objT f)"

    definition wf_problem where
      "wf_problem \<equiv>                                      
        wf_domain
      \<and> distinct (map fst (objects P))
      \<and> (\<forall>(n,T)\<in>set (objects P). wf_type T)
      \<and> distinct (init P)
      \<and> wf_world_model (set (init P))
      \<and> wf_fmla objT (goal P)
      "

    abbreviation "notAtom fmla \<equiv> (\<forall>atm args. fmla \<noteq> (formula.Atom (atom.predAtm atm args)))"

    abbreviation "isAtom fmla \<equiv> (\<exists>atm args. fmla = (formula.Atom (atom.predAtm atm args)))"

    fun wf_effect_inst :: "object atom formula ast_effect \<Rightarrow> bool" where
      "wf_effect_inst (Effect (adds) (dels)) \<longleftrightarrow> 
          (*distinct (map atom aes) \<and>  (* No duplicate or contradictory effects allowed *)*)
          ((\<forall>ae\<in>set adds. isAtom ae) \<and> (\<forall>de\<in>set dels. isAtom de))(* Instantiated to valid objects *)" 
      
  end

  locale wf_ast_domain = ast_domain + 
    assumes wf_domain: wf_domain  
    
  locale wf_ast_problem = ast_problem P for P +
    assumes wf_problem: wf_problem
  begin
    sublocale wf_ast_domain "domain P"
      apply unfold_locales
      using wf_problem
      unfolding wf_problem_def by simp
        
  end
    
  (* Semantics *)  

  (*  To apply plan_action:   
      find action schema, instantiate, check precond, apply effect
  *)
    
  type_synonym world_model = "(fact formula) set"

  datatype ast_action_inst = Action_Inst
    (precondition: "(object atom) formula")
    (effect: "(object atom) formula ast_effect")
    
    
  context ast_domain begin
      
    definition resolve_action_schema :: "name \<rightharpoonup> ast_action_schema"
      where "resolve_action_schema n = index_by ast_action_schema.name (actions D) n"
      
    fun instantiate_action_schema :: "ast_action_schema \<Rightarrow> object list \<Rightarrow> ast_action_inst" where
      "instantiate_action_schema (Action_Schema n params pre eff) args = (let 
          inst = (the o (map_of (zip (map fst params) args)))
        in
          Action_Inst ((map_formula o map_atom) inst pre) ((map_ast_effect o map_formula o map_atom) inst eff)
        )"
                    
    (* It seems to be agreed upon that, in case of a contradictionary effect, 
      addition overrides deletion. We model this behaviour by first executing 
      the deletions, and then the additions. *)

    fun apply_effect :: "object atom formula ast_effect \<Rightarrow> world_model \<Rightarrow> world_model" where
       "apply_effect (Effect (adds) (dels)) s = (s - (set dels)) \<union> ((set adds))"

    fun apply_effect_exec' where
      "apply_effect_exec' (Effect (adds) (dels)) (s::world_model) = (formula.Atom) ` (fold (%add s. insert add s) (adds) (fold (%del s. Set.remove del s) (dels) ( the ` ((%f. case f of formula.Atom atm \<Rightarrow> Some atm | _ \<Rightarrow> None) ` s))))"


    fun apply_effect_exec :: "object atom formula ast_effect \<Rightarrow> world_model \<Rightarrow> world_model" where
      "apply_effect_exec (Effect (adds) (dels)) s = fold (%add s. insert add s) (adds) (fold (%del s. Set.remove del s) (dels) s)"

    lemma apply_effect_eq_exec[simp,symmetric]: "apply_effect (Effect (adds) (dels)) s = apply_effect_exec (Effect (adds) (dels)) s "
    proof(induction adds arbitrary: s)
      case Nil
      then show ?case
      proof(induction dels arbitrary: s)
        case Nil
        then show ?case by auto
      next
        case (Cons a dels)
        then show ?case apply (auto simp add: image_def) 
             using Diff_iff insertI1
             apply fastforce
             using Diff_iff remove_def
             apply (metis (no_types, lifting))
             using Diff_iff insertI1 
             by (metis (no_types, lifting) remove_def)
      qed
    next
      case (Cons a adds)
      then show ?case
      proof(induction dels arbitrary: s)
        case Nil
        then show ?case by (auto; metis insert_def sup_assoc insert_iff) 
      next
        case (Cons a dels)
        then show ?case by (auto; metis UnI2 Un_iff union_set_fold insert_iff union_set_fold) 
      qed
    qed

    lemma apply_effect_eq_impl_eq: "apply_effect (Effect (adds) (dels)) s = fold (%add s. insert add s) (adds) (fold (%del s. Set.remove del s) (dels) s)"
          using apply_effect_eq_exec by auto 

  end  
      

  context ast_problem begin  
    
    fun resolve_instantiate :: "plan_action \<Rightarrow> ast_action_inst" where
      "resolve_instantiate (PAction n args) = 
        instantiate_action_schema 
          (the (resolve_action_schema n))
          args"
    
    definition "is_obj_of_type n T \<equiv> case objT n of
      None \<Rightarrow> False
    | Some oT \<Rightarrow> of_type oT T"  
      
    lemma is_obj_of_type_alt: "is_obj_of_type = is_of_type objT"  
      apply (intro ext)
      unfolding is_obj_of_type_def is_of_type_def by auto
      
    fun wf_plan_action :: "plan_action \<Rightarrow> bool" where
      "wf_plan_action (PAction n args) = ( 
        case resolve_action_schema n of 
          None \<Rightarrow> False 
        | Some a \<Rightarrow> 
            list_all2 is_obj_of_type args (map snd (ast_action_schema.parameters a)) (* Objects are valid and match parameter types *)
          \<and> wf_effect_inst (effect (instantiate_action_schema a args)) (* Effect is valid *)
          )"
    (* Implementation note: This spec contains some redundancy: 
        instantiating a well formed action with valid objects will leave the 
        effect to contain valid objects.
    *)  
      
    definition ast_action_inst_enabled :: "ast_action_inst \<Rightarrow> world_model \<Rightarrow> bool" where
      "ast_action_inst_enabled act s \<longleftrightarrow>  s \<TTurnstile> (precondition act)"

    definition plan_action_enabled :: "plan_action \<Rightarrow> world_model \<Rightarrow> bool" where
      "plan_action_enabled pa s \<longleftrightarrow> wf_plan_action pa  \<and> s \<TTurnstile> precondition (resolve_instantiate pa)"

    (* Implementation note: resolve and instantiate already done inside wf_plan_action, redundancy! *)
      
    definition execute_ast_action_inst :: "ast_action_inst \<Rightarrow> world_model \<Rightarrow> world_model" where
      "execute_ast_action_inst act_inst s = apply_effect (effect act_inst) s"
                                             
    fun ast_action_inst_path :: "world_model \<Rightarrow> (ast_action_inst list) \<Rightarrow> world_model \<Rightarrow> bool" where
      "ast_action_inst_path s [] s' \<longleftrightarrow> (s = s')"
    | "ast_action_inst_path s (\<pi>#\<pi>s) s' \<longleftrightarrow> s \<TTurnstile> precondition \<pi> \<and> (ast_action_inst_path (apply_effect (effect \<pi>) s) \<pi>s s')"

    definition execute_plan_action :: "plan_action \<Rightarrow> world_model \<Rightarrow> world_model" where
      "execute_plan_action pa s = (apply_effect (effect (resolve_instantiate pa)) s)"      

    definition plan_action_path :: "world_model \<Rightarrow> (plan_action list) \<Rightarrow> world_model \<Rightarrow> bool" where
      "plan_action_path s \<pi>s s' = ((\<forall>a. a \<in> set \<pi>s \<longrightarrow> wf_plan_action a) \<and> ast_action_inst_path s (map resolve_instantiate \<pi>s) s')"

    definition valid_plan_from :: "world_model \<Rightarrow> plan \<Rightarrow> bool" where
      "valid_plan_from s \<pi>s = (\<exists>s'. plan_action_path s \<pi>s s' \<and> s' \<TTurnstile> (goal P))"

    fun valid_plan_from_explicit :: "world_model \<Rightarrow> plan \<Rightarrow> bool" where
      "valid_plan_from_explicit s [] \<longleftrightarrow> s \<TTurnstile> (goal P)"  
    | "valid_plan_from_explicit s (\<pi>#\<pi>s) \<longleftrightarrow> plan_action_enabled \<pi> s \<and> (valid_plan_from_explicit (execute_plan_action \<pi> s) \<pi>s)"

    lemma valid_plan_explicit_eq_succinct: "valid_plan_from_explicit s \<pi>s = valid_plan_from s \<pi>s"
      proof(induction \<pi>s arbitrary: s)
        case Nil
        then show ?case by (auto simp add: plan_action_path_def valid_plan_from_def)
     next
       case (Cons a \<pi>s)
       then show ?case by (auto simp add: plan_action_path_def plan_action_enabled_def execute_plan_action_def ast_action_inst_enabled_def valid_plan_from_def)
     qed

    (* Implementation note: resolve and instantiate already done inside enabledness check, redundancy! *)
      
    definition I :: "world_model" where
      "I \<equiv> set (init P)"
      
    definition valid_plan :: "plan \<Rightarrow> bool" 
      where "valid_plan \<equiv> valid_plan_from I"
    
    lemma valid_plan_explicit: "valid_plan = valid_plan_from_explicit I"
          using valid_plan_explicit_eq_succinct by (auto simp add: valid_plan_def)
  end  
    
  (*Soundness theorem for the strips semantics*)
    
  context ast_problem begin

  type_synonym action = "(object atom valuation) \<Rightarrow> (object atom valuation) option"

    definition "sound_opr (opr :: ast_action_inst) (f :: action) =
                 (\<forall>s. s \<Turnstile> (precondition opr) \<longrightarrow>
                      ((\<exists>s'. f s = (Some s') \<and>
                             (\<forall>del_atm. del_atm \<notin> set(Dels (effect opr))
                                        \<longrightarrow> isAtom del_atm
                                        \<longrightarrow> s \<Turnstile> del_atm
                                        \<longrightarrow> s' \<Turnstile> del_atm) \<and>
                             (\<forall>add_atm. add_atm \<in> set(Adds (effect opr))
                                        \<longrightarrow> s' \<Turnstile> add_atm) \<and>
                             (\<forall>s.\<forall>fmla\<in>set(Adds (effect opr)).
                                     notAtom fmla \<longrightarrow> s \<Turnstile> fmla))))"

    definition "sound_system (sys :: ast_action_inst set) (M0::world_model) (s0::object atom valuation) (F :: ast_action_inst \<Rightarrow> action) = 
                 ((\<forall>fmla\<in>M0. s0 \<Turnstile> fmla) \<and>
                  (\<forall>s.\<forall>fmla\<in>M0. notAtom fmla \<longrightarrow> s \<Turnstile> fmla) \<and>
                  (\<forall>opr\<in>sys. sound_opr opr (F opr)))"

    definition "compose_actions (f1::'a \<Rightarrow> 'a option) (f2:: 'a \<Rightarrow> 'a option)
                                   = (%x. case (f2 x) of (Some y) \<Rightarrow> f1 y
                                                         | None \<Rightarrow> None)"

    lemma compose_actions_assoc: "compose_actions f1 (compose_actions f2 f3) = compose_actions (compose_actions f1 f2) f3"
          unfolding compose_actions_def
          by (metis option.case_eq_if)

    lemma compose_Some: "compose_actions f1 Some= f1"
          unfolding compose_actions_def
          by auto

    lemma compose_Some_2: "compose_actions Some f = f"
          unfolding compose_actions_def
          proof
            fix x
            show "(case f x of None \<Rightarrow> None | Some x \<Rightarrow> Some x) = f x" 
               by (simp add: option.case_eq_if)
          qed

    lemma fold_compose: "fold (op o) acts (f1 o f2) s0 = 
                     fold (op o) acts f1 (f2 s0)"
          proof(induction acts arbitrary: s0 f1 f2)
            case Nil
            then show ?case by (simp add: compose_actions_def)
          next
            case ass: (Cons a oprs)
            then show ?case apply (simp only: fold.simps)
              by (metis comp_assoc comp_def)
          qed

    lemma fold_compose_actions: "f2 s0 = Some s1 \<Longrightarrow>
               fold compose_actions acts (compose_actions f1 f2) s0 = 
                     fold compose_actions acts f1 s1"
          proof(induction acts arbitrary: s0 s1 f1 f2)
            case Nil
            then show ?case by (simp add: compose_actions_def)
          next
            case ass: (Cons a oprs)
            then show ?case 
                 apply (auto simp add: )
              by (simp add: ast_problem.compose_actions_assoc)
          qed

    lemma effect_app_cases: "atm \<in> apply_effect (Effect (adds) (dels)) M \<Longrightarrow> (((((atm))) \<in> (set adds) \<or> (atm \<in> M) \<and> (atm) \<notin> (set dels)))"
                  by (auto simp add: image_def)

    lemma effect_app_cases_exec: "atm \<in> apply_effect_exec (Effect (adds) (dels)) M \<Longrightarrow> (((((atm))) \<in> (set adds) \<or> (atm \<in> M) \<and> (atm) \<notin> (set dels)))"
          using effect_app_cases by (simp only: apply_effect_eq_exec)

    lemma STRIPS_sema_sound: "sound_system sys M0 s0 F \<Longrightarrow> ast_action_inst_path M0 oprs M' \<Longrightarrow> set oprs \<subseteq> sys
           \<Longrightarrow> (\<exists>s'. ((fold compose_actions (map F oprs) Some) s0) = Some s' \<and> (\<forall>fmla\<in>M'. s' \<Turnstile> fmla))"
          proof(induction oprs arbitrary: s0 M0 )
            case Nil
            then show ?case by (auto simp add: compose_actions_def sound_system_def sound_opr_def) 
          next
            case ass: (Cons a oprs)
            then obtain x1 adds dels where a: "a = Action_Inst x1 (Effect adds dels)"
              using ast_action_inst.exhaust ast_effect.exhaust
              by metis
            let ?M0.1 = "execute_ast_action_inst a M0"
            obtain s1 where s1: "(F a) s0 = Some s1"
                        "(\<forall>del_atm. del_atm \<notin> set(Dels (effect a))
                                        \<longrightarrow> isAtom del_atm
                                        \<longrightarrow> s0 \<Turnstile> del_atm
                                        \<longrightarrow> s1 \<Turnstile> del_atm) \<and>
                             (\<forall>add_atm. add_atm \<in> set(Adds (effect a))
                                        \<longrightarrow> s1 \<Turnstile> add_atm) \<and> 
                             (\<forall>s.\<forall>fmla\<in>set(Adds (effect a)).
                                     notAtom fmla \<longrightarrow> s \<Turnstile> fmla)"
                   using ass(2-4)
                   unfolding sound_system_def sound_opr_def
                   apply (auto simp add: ast_action_inst_enabled_def entailment_def)
                   by blast
            let ?s0.1 = "s1"
            have "(\<forall>fmla\<in>?M0.1. s1 \<Turnstile> fmla)"
                 apply(rule ballI)
                 using ass(2) s1 effect_app_cases formula.exhaust
                 unfolding sound_system_def sound_opr_def execute_ast_action_inst_def
                 by (auto simp add: a image_def)
            moreover have "(\<forall>s.\<forall>fmla\<in>?M0.1. (\<forall>atm. fmla \<noteq> formula.Atom atm) \<longrightarrow> s \<Turnstile> fmla)"
                       using ass(2)
                       unfolding sound_system_def execute_ast_action_inst_def sound_opr_def
                       apply (auto simp add: a) 
                       by (metis a ass.prems(2) ass.prems(3) ast_action_inst.sel(2) ast_effect.sel(1) ast_problem.ast_action_inst_enabled_def ast_problem.ast_action_inst_path.simps(2) entailment_def insertI1 list.simps(15) subsetCE)
            moreover have "(\<forall>opr\<in>sys. sound_opr opr (F opr))"
                       using ass(2) unfolding sound_system_def
                       by (auto simp add:)
            ultimately have "sound_system sys ?M0.1 ?s0.1 F"
               unfolding sound_system_def
               apply auto 
               using a ass.prems(1) ast_problem.execute_ast_action_inst_def ast_problem.sound_system_def s1(2) by auto
            then obtain s' where "fold compose_actions (map F oprs) Some ?s0.1 = Some s' \<and> (\<forall>a\<in>M'. s' \<Turnstile> a)"
                       using ass unfolding sound_system_def
                       apply (auto) 
                       using ast_problem.execute_ast_action_inst_def by presburger
            moreover have "fold compose_actions (map F (a # oprs)) Some s0 = fold compose_actions (map F oprs) Some s1" using s1(1) apply (auto simp add: compose_Some) using fold_compose_actions compose_Some_2 by metis
            ultimately show ?case by auto
  qed

    (*definition "valuation s \<equiv> (\<lambda>x. (case x of (atom.Eq a b) \<Rightarrow> (a = b)  | _ \<Rightarrow> (formula.Atom x) \<in> s))"*)
    definition "valuation s \<equiv> (\<lambda>x. (formula.Atom x) \<in> s)"
    definition "holds s F \<equiv> (valuation s) \<Turnstile> F"

  end                                      
  (* Preservation of well-formedness *)  
    
  lemma lookup_zip_idx_eq:
    assumes "length params = length args"
    assumes "i<length args"  
    assumes "distinct params"  
    assumes "k = params ! i"  
    shows "map_of (zip params args) k = Some (args ! i)"
    using assms
    by (auto simp: in_set_conv_nth)  
    
  context ast_problem begin    
    (*definition wf_world_model :: "world_model \<Rightarrow> bool" where
      "wf_world_model s \<equiv> \<forall>f\<in>s. wf_fmla objT f"*)

      
    fun wf_action_inst :: "ast_action_inst \<Rightarrow> bool" where   
      "wf_action_inst (Action_Inst pre eff) \<longleftrightarrow> (
          wf_fmla objT pre
        \<and> wf_effect objT eff
        )
      "
      
    lemma is_of_type_map_ofE:
      assumes "is_of_type (map_of params) x T"  
      obtains i xT where "i<length params" "params!i = (x,xT)" "of_type xT T"
      using assms  
      unfolding is_of_type_def
      by (auto split: option.splits dest!: map_of_SomeD simp: in_set_conv_nth)  
      
  end  

  context ast_domain begin  
    lemma of_type_refl[simp, intro!]: "of_type T T"
      unfolding of_type_def by auto
        
    lemma of_type_trans[trans]: "of_type T1 T2 \<Longrightarrow> of_type T2 T3 \<Longrightarrow> of_type T1 T3"
      unfolding of_type_def  
    proof clarsimp
      fix x :: "char list"
      assume a1: "set (primitives T2) \<subseteq> subtype_rel\<^sup>* `` set (primitives T3)"
      assume a2: "set (primitives T1) \<subseteq> subtype_rel\<^sup>* `` set (primitives T2)"
      assume a3: "x \<in> set (primitives T1)"
      obtain ccs :: "char list set \<Rightarrow> (char list \<times> char list) set \<Rightarrow> char list \<Rightarrow> char list" where
        "\<forall>x0 x1 x2. (\<exists>v3. v3 \<in> x0 \<and> (v3, x2) \<in> x1) = (ccs x0 x1 x2 \<in> x0 \<and> (ccs x0 x1 x2, x2) \<in> x1)"
        by moura
      then have f4: "\<forall>cs r C. (cs \<notin> r `` C \<or> ccs C r cs \<in> C \<and> (ccs C r cs, cs) \<in> r) \<and> (cs \<in> r `` C \<or> (\<forall>csa. csa \<notin> C \<or> (csa, cs) \<notin> r))"
        by blast
      have "x \<in> subtype_rel\<^sup>* `` set (primitives T2)"
        using a3 a2 by blast
      then show "x \<in> subtype_rel\<^sup>* `` set (primitives T3)"
        using f4 a1 by (meson in_mono rtrancl_trans)
    qed  
      
      
  end  
    
  context wf_ast_problem begin
    lemma wf_I: "wf_world_model I"
      using wf_problem
      unfolding I_def wf_world_model_def wf_problem_def wf_fmla_atom_def
      apply(safe) subgoal for f 
      proof(induction f; auto)
      qed
      done

    lemma wf_apply_effect:
      assumes "wf_effect objT e"
      assumes "wf_world_model s"  
      shows "wf_world_model (apply_effect e s)"  
      using assms wf_problem 
      unfolding wf_world_model_def wf_problem_def wf_domain_def
      apply (auto split: formula.splits prod.splits)
      using ast_problem.effect_app_cases wf_fmla_atom_imp_wf_fmla
      by(metis wf_effect.elims(2) wf_fmla.simps(1))

    context 
      fixes Q f
      assumes INST: "is_of_type Q x T \<Longrightarrow> is_of_type objT (f x) T"  
    begin

      lemma wf_inst_eq_aux: "Q x = Some T \<Longrightarrow> objT (f x) \<noteq> None"
        using INST[of x T] unfolding is_of_type_def 
        by (auto split: option.splits)
          
      lemma wf_inst_atom: 
        assumes "wf_atom Q a" 
        shows "wf_atom objT (map_atom f a)"
      proof -
        have X1: "list_all2 (is_of_type objT) (map f xs) Ts" if
          "list_all2 (is_of_type Q) xs Ts" for xs Ts
          using that
          apply induction
          using INST  
          by auto  
        then show ?thesis
          using assms wf_inst_eq_aux
          by (cases a; auto split: option.splits)
      qed  
        
      lemma wf_inst_formula_atom:
        assumes "wf_fmla_atom Q a" 
        shows "wf_fmla_atom objT ((map_formula o map_atom) f a)"
        using assms wf_inst_atom by (auto simp add: wf_fmla_atom_def split: option.splits; cases a; auto)

      lemma wf_inst_effect: 
        assumes "wf_effect Q \<phi>" 
        shows "wf_effect objT ((map_ast_effect o map_formula o map_atom) f \<phi>)"
        using assms
        proof (induction \<phi>)
          case (Effect x1a x2a)
          then show ?case using wf_inst_formula_atom by auto
        qed

      (*lemma wf_inst_formula: 
        assumes "wf_fmla Q \<phi>" 
        shows "wf_fmla objT ((map_formula o map_atom) f \<phi>)"
        using assms
        apply (induction \<phi>)
        apply (auto simp: wf_inst_atom dest: wf_inst_eq_aux split: )
        subgoal for x apply(cases x; auto)
           subgoal for x1 x2 apply(cases x1; auto)
             subgoal for y apply(cases y; auto simp add: INST list.rel_map(1) list_all2_mono split: option.splits) 
             done
           done
        subgoal for x1 x2 
          using wf_inst_eq_aux by auto
        subgoal for x1 x2 y1 y2
          using wf_inst_eq_aux by auto
        done
      subgoal for \<phi> by (cases \<phi>; auto)
        done
    end*)

  lemma wf_inst_formula: 
        assumes "wf_fmla Q \<phi>" 
        shows "wf_fmla objT ((map_formula o map_atom) f \<phi>)"
        using assms
        apply (induction \<phi>)
        apply (auto simp: wf_inst_atom dest: wf_inst_eq_aux split: )
        subgoal for x apply(cases x; auto)
           subgoal for x1 x2 apply(cases x1; auto)
             subgoal for y apply(cases y; auto simp add: INST list.rel_map(1) list_all2_mono split: option.splits) 
             done
           done
        done
      subgoal for \<phi> by (cases \<phi>; auto)
        done
    end

    lemma wf_instantiate_action_schema:
      assumes "list_all2 is_obj_of_type args (map snd (ast_action_schema.parameters a))"  
      assumes "wf_action_schema a"  
      shows "wf_action_inst (instantiate_action_schema a args)"
    proof (cases a)
      case [simp]: (Action_Schema name params pre eff)
      have INST: "is_of_type objT ((the \<circ> map_of (zip (map fst params) args)) x) T"
        if "is_of_type (map_of params) x T" for x T
        using that
        apply (rule is_of_type_map_ofE)
        using assms  
        apply (clarsimp simp: Let_def)
        subgoal for i xT 
          apply (subst lookup_zip_idx_eq[where i=i]; (clarsimp simp: list_all2_lengthD)?)
          apply (frule list_all2_nthD2[where p=i]; simp?)
          apply (auto 
                  simp: is_obj_of_type_alt is_of_type_def 
                  intro: of_type_trans 
                  split: option.splits)  
          done
        done    
      show ?thesis 
        using assms(2) wf_inst_formula wf_inst_effect INST
        by (simp add: Let_def; metis comp_apply)        
    qed

    lemma wf_execute:
      assumes "plan_action_enabled \<pi> s"
      assumes "wf_world_model s"  
      shows "wf_world_model (execute_plan_action \<pi> s)"
      using assms
    proof (cases \<pi>)
      case [simp]: (PAction name args)

      from \<open>plan_action_enabled \<pi> s\<close> have "wf_plan_action \<pi>"
        unfolding plan_action_enabled_def by auto
      then obtain a where 
        "resolve_action_schema name = Some a" and
        T: "list_all2 is_obj_of_type args (map snd (ast_action_schema.parameters a))"
        by (auto split: option.splits)
          
      from wf_domain have [simp]: "distinct (map ast_action_schema.name (actions D))"
        unfolding wf_domain_def by auto
          
      from \<open>resolve_action_schema name = Some a\<close> have 
        "a \<in> set (actions D)"
        unfolding resolve_action_schema_def by auto
      with wf_domain have "wf_action_schema a"    
        unfolding wf_domain_def by auto
      hence "wf_action_inst (resolve_instantiate \<pi>)"    
        using \<open>resolve_action_schema name = Some a\<close> T
          wf_instantiate_action_schema
        by auto
      thus ?thesis
        apply (simp add: execute_plan_action_def execute_ast_action_inst_def)
        apply (rule wf_apply_effect)  
        apply (cases "resolve_instantiate \<pi>"; simp)
        by (rule \<open>wf_world_model s\<close>)
    qed

    definition "state_to_wf_world_model s = (formula.Atom ` {atm. s atm})"
    definition "wf_world_model_to_state M = (%atm. (formula.Atom atm) \<in> M)"

    lemma wm_to_state_to_wm: "s \<Turnstile> f = wf_world_model_to_state (state_to_wf_world_model s) \<Turnstile> f"
          by (auto simp add: wf_world_model_to_state_def state_to_wf_world_model_def image_def)

    lemma atom_in_wm: "s \<Turnstile> (formula.Atom atm) = ((formula.Atom atm) \<in> (state_to_wf_world_model s))"
          by (auto simp add: wf_world_model_to_state_def state_to_wf_world_model_def image_def)
    lemma atom_in_wm_2: "(wf_world_model_to_state M) \<Turnstile> (formula.Atom atm) = ((formula.Atom atm) \<in> M)"
          by (auto simp add: wf_world_model_to_state_def state_to_wf_world_model_def image_def)


    definition "pddl_opr_to_act g_opr s = (let M =  state_to_wf_world_model s in (if (s \<Turnstile> (precondition g_opr)) then Some (wf_world_model_to_state (apply_effect (effect g_opr) M)) else None))"

lemma not_dels_presreved:
  assumes "f \<notin> (set dels)" " f \<in> M" 
  shows "f \<in> apply_effect (Effect adds dels) M"
  using assms
  by auto

lemma adds_satised:
  assumes "f \<in> (set adds)"
  shows "f \<in> apply_effect (Effect adds dels) M"
  using assms
  by auto

lemma wf_fmla_atm_is_atom: "wf_fmla_atom objT f \<Longrightarrow> isAtom f"
  apply(auto simp add: wf_fmla_atom_def; cases f; auto)
  subgoal for x by(cases x; auto) 
  done

lemma wf_act_adds_are_atoms:
  assumes "wf_effect_inst effs" "ae \<in> set (Adds effs)"
  shows "isAtom ae"
  using assms
  by (cases effs; auto simp add: wf_effect.simps)

lemma wf_eff_pddl_ground_act_is_sound_opr:
      assumes "wf_effect_inst (effect g_opr)"
      shows "sound_opr g_opr (pddl_opr_to_act g_opr)"
      using assms
    proof(induction g_opr)
      case ass1: (Action_Inst x1a x2a)
      then show ?case
        unfolding sound_opr_def
        apply safe
      proof-
        fix s assume ass2: " wf_effect_inst (effect (Action_Inst x1a x2a))" "s \<Turnstile> ast_action_inst.precondition (Action_Inst x1a x2a)"
        let ?s = "wf_world_model_to_state(apply_effect x2a (state_to_wf_world_model s))"
        have "pddl_opr_to_act  (Action_Inst x1a x2a) s = Some ?s"
             using ass1 ass2
             by (cases x2a; auto simp add: pddl_opr_to_act_def image_def Let_def state_to_wf_world_model_def entailment_def wf_fmla_atom_def; cases x1a; auto)
        moreover have "del_atm \<notin> set (Dels (ast_action_inst.effect (Action_Inst x1a x2a))) \<longrightarrow> isAtom del_atm \<longrightarrow> s \<Turnstile> del_atm \<longrightarrow> ?s \<Turnstile> del_atm"
          for del_atm
          using atom_in_wm_2 not_dels_presreved atom_in_wm by (metis ast_action_inst.sel(2) ast_effect.collapse)
        moreover have "add_atm \<in> set (Adds (ast_action_inst.effect (Action_Inst x1a x2a))) \<longrightarrow> ?s \<Turnstile> add_atm" for add_atm
          using wf_act_adds_are_atoms atom_in_wm_2 adds_satised atom_in_wm ass2(1)
          by (metis ast_action_inst.sel(2) ast_effect.collapse)
        moreover have "(\<forall>s. \<forall>fmla\<in>set (Adds (ast_action_inst.effect (Action_Inst x1a x2a))). (\<forall>atm args. fmla \<noteq> formula.Atom (predAtm atm args)) \<longrightarrow> s \<Turnstile> fmla)"
          using wf_act_adds_are_atoms ass2(1)
          by fastforce
        ultimately show " \<exists>s'. pddl_opr_to_act (Action_Inst x1a x2a) s = Some s' \<and>
              (\<forall>del_atm. del_atm \<notin> set (Dels (ast_action_inst.effect (Action_Inst x1a x2a))) \<longrightarrow> (\<exists>atm args. del_atm = Atom (predAtm atm args)) \<longrightarrow> s \<Turnstile> del_atm \<longrightarrow> s' \<Turnstile> del_atm) \<and>
              (\<forall>add_atm. add_atm \<in> set (Adds (ast_action_inst.effect (Action_Inst x1a x2a))) \<longrightarrow> s' \<Turnstile> add_atm) \<and>
              (\<forall>s. \<forall>fmla\<in>set (Adds (ast_action_inst.effect (Action_Inst x1a x2a))). (\<forall>atm args. fmla \<noteq> Atom (predAtm atm args)) \<longrightarrow> s \<Turnstile> fmla)" by blast
      qed
    qed

lemma wf_eff_impt_wf_eff_inst: "wf_effect objT eff \<Longrightarrow> wf_effect_inst eff"
  apply(cases eff; auto simp add: wf_effect_inst.simps wf_fmla_atom_def)
  subgoal for adds dels ae apply (cases ae; auto)
    subgoal for atm by(cases atm; auto)
    done
  subgoal for adds dels ae apply (cases ae; auto)
    subgoal for atm by(cases atm; auto)
    done
  done

lemma wf_pddl_ground_act_is_sound_opr:
      assumes "wf_action_inst g_opr"
      shows "sound_opr g_opr (pddl_opr_to_act g_opr)"
      using wf_eff_impt_wf_eff_inst wf_eff_pddl_ground_act_is_sound_opr assms
      by (cases g_opr; auto simp add: wf_action_inst.simps)
      

    lemma wf_action_schema_sound_inst:
          assumes "list_all2 is_obj_of_type args (map snd (ast_action_schema.parameters act))" "wf_action_schema act"
          shows " sound_opr (instantiate_action_schema act args) (pddl_opr_to_act (instantiate_action_schema act args))"
      using wf_pddl_ground_act_is_sound_opr[OF wf_instantiate_action_schema[OF assms]] by blast

   lemma wf_plan_act_is_sound:
      assumes "wf_plan_action (PAction n args)"
      shows "sound_opr (instantiate_action_schema (the (resolve_action_schema n)) args) (pddl_opr_to_act (instantiate_action_schema (the (resolve_action_schema n)) args))"
      using assms
      apply (auto split: option.splits)
      using wf_action_schema_sound_inst wf_eff_pddl_ground_act_is_sound_opr by auto

   lemma wf_plan_act_is_sound':
      assumes "wf_plan_action \<pi>"
      shows "sound_opr (resolve_instantiate \<pi>) (pddl_opr_to_act (resolve_instantiate \<pi>))"
      using assms wf_plan_act_is_sound 
      by (cases \<pi>; auto )

lemma wf_world_model_has_atoms: "f\<in>M \<Longrightarrow> wf_world_model M \<Longrightarrow> isAtom f"
  using wf_fmla_atm_is_atom
  unfolding wf_world_model_def
  by auto

lemma wm_to_state_works_for_I:
  assumes "x \<in> set (init P)" shows " wf_world_model_to_state (set (init P)) \<Turnstile> x"
  using wf_world_model_has_atoms assms wf_problem
  unfolding wf_problem_def
  apply (cases x; auto simp add: wf_problem_def)
  using assms atom_in_wm_2 apply auto by force
  
lemma wf_plan_sound_system:
  assumes "\<forall>\<pi>\<in> set \<pi>s. wf_plan_action \<pi>"
  shows "sound_system (set (map resolve_instantiate \<pi>s)) (set (init P)) (wf_world_model_to_state (set (init P))) pddl_opr_to_act"
  using wm_to_state_works_for_I wf_problem wf_world_model_has_atoms 
     unfolding sound_system_def wf_problem_def
     apply auto apply blast
     using wf_plan_act_is_sound' assms by blast

lemma wf_plan_soundess_theorem:
  assumes "plan_action_path (set (init P)) \<pi>s M"
  shows "\<exists>s'. fold compose_actions (map pddl_opr_to_act (map resolve_instantiate \<pi>s)) Some (wf_world_model_to_state (set (init P))) = Some s' \<and> (\<forall>fmla\<in>M. s' \<Turnstile> fmla)"
  apply(rule STRIPS_sema_sound wf_plan_sound_system)+
  using assms 
  unfolding plan_action_path_def
  by (auto simp add: image_def)

  end

end
