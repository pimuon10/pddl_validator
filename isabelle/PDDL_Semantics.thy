theory PDDL_Semantics
imports Main begin
      
  definition "index_by f l \<equiv> map_of (map (\<lambda>x. (f x,x)) l)"
  
  lemma index_by_eq_Some_eq[simp]: 
    assumes "distinct (map f l)"
    shows "index_by f l n = Some x \<longleftrightarrow> (x\<in>set l \<and> f x = n)"  
    unfolding index_by_def 
    using assms  
    by (auto simp: o_def)
    
  
  type_synonym name = string
    
  datatype predicate = Pred (name: name)
  
  datatype 'val atom = Atom (predicate: predicate) (arguments: "'val list")
    
  datatype type = Either (primitives: "name list") (* We use singleton lists to model primitive types *)
    
  datatype 'val ast_prop =
    prop_atom "'val atom"
  | prop_eq 'val 'val
  | prop_not "'val ast_prop"
  | prop_and "'val ast_prop list"
  | prop_or "'val ast_prop list"

  datatype 'val ast_atomic_effect = is_Add: Add (atom: "'val atom") | is_Del: Del (atom: "'val atom")
  datatype 'val ast_effect = Effect (atomics: "(('val ast_atomic_effect) list)")

  datatype variable = varname: Var name
    
  datatype ast_action_schema = Action_Schema
    (name: name)
    (parameters: "(variable \<times> type) list")
    (precondition: "variable ast_prop")
    (effect: "variable ast_effect")

  datatype predicate_decl = PredDecl 
    (pred: predicate) 
    (argTs: "type list")
    
  datatype ast_domain = Domain
    (types: "name list") (* Only supports flat type hierarchy *)
    (predicates: "predicate_decl list")
    (actions: "ast_action_schema list")

  datatype object = name: Obj name  
  type_synonym fact = "object atom"
    
  datatype ast_problem = Problem
    (domain: ast_domain)
    (objects: "(object \<times> type) list")
    (init: "fact list")
    (goal: "object ast_prop")
    
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
      
      fun wf_atom :: "'val atom \<Rightarrow> bool"  where
        "wf_atom (Atom p vs) \<longleftrightarrow> (
          case sig p of 
            None \<Rightarrow> False
          | Some Ts \<Rightarrow> list_all2 is_of_type vs Ts
        )"
      
      fun wf_prop :: "'val ast_prop \<Rightarrow> bool" where
        "wf_prop (prop_atom a) \<longleftrightarrow> wf_atom a"
      | "wf_prop (prop_eq v1 v2) \<longleftrightarrow> ty_val v1\<noteq>None \<and> ty_val v2\<noteq>None" (* TODO: We could check that types may overlap *)
      | "wf_prop (prop_not \<phi>) \<longleftrightarrow> wf_prop \<phi>"  
      | "wf_prop (prop_and \<phi>s) \<longleftrightarrow> (\<forall>\<phi>\<in>set \<phi>s. wf_prop \<phi>)"  
      | "wf_prop (prop_or \<phi>s) \<longleftrightarrow> (\<exists>\<phi>\<in>set \<phi>s. wf_prop \<phi>)"  
        
      fun wf_atomic_effect where
        "wf_atomic_effect (Add a) \<longleftrightarrow> wf_atom a"
      | "wf_atomic_effect (Del a) \<longleftrightarrow> wf_atom a"
      
      fun wf_effect where
        "wf_effect (Effect aes) \<longleftrightarrow> 
            (\<forall>ae\<in>set aes. wf_atomic_effect ae)"
    
    end
      
    fun wf_action_schema :: "ast_action_schema \<Rightarrow> bool" where   
      "wf_action_schema (Action_Schema n params pre eff) \<longleftrightarrow> (
        let
          tyv = map_of params
        in
          distinct (map fst params)
        \<and> wf_prop tyv pre
        \<and> wf_effect tyv eff
        )               
      "
      
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
        
    definition wf_problem where
      "wf_problem \<equiv>                                      
        wf_domain
      \<and> distinct (map fst (objects P))
      \<and> (\<forall>(n,T)\<in>set (objects P). wf_type T)
      \<and> distinct (init P)
      \<and> (\<forall>f\<in>set (init P). wf_fact f)
      \<and> wf_prop objT (goal P)
      "

    fun wf_effect_inst :: "object ast_effect \<Rightarrow> bool" where
      "wf_effect_inst (Effect aes) \<longleftrightarrow> 
          (*distinct (map atom aes) \<and>  (* No duplicate or contradictory effects allowed *)*)
          (\<forall>ae\<in>set aes. wf_atomic_effect objT ae) (* Instantiated to valid objects *)
        " 
      
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
    
  type_synonym state = "fact set"

  datatype ast_action_inst = Action_Inst
    (precondition: "object ast_prop")
    (effect: "object ast_effect")
    
    
  context ast_domain begin
      
    definition resolve_action_schema :: "name \<rightharpoonup> ast_action_schema"
      where "resolve_action_schema n = index_by ast_action_schema.name (actions D) n"
      
    fun instantiate_action_schema :: "ast_action_schema \<Rightarrow> object list \<Rightarrow> ast_action_inst" where
      "instantiate_action_schema (Action_Schema n params pre eff) args = (let 
          inst = (the o (map_of (zip (map fst params) args)))
        in
          Action_Inst (map_ast_prop inst pre) (map_ast_effect inst eff)
        )"
      
    fun holds :: "state \<Rightarrow> object ast_prop \<Rightarrow> bool" where
      "holds s (prop_atom f) \<longleftrightarrow> f\<in>s"
    | "holds s (prop_eq x y) \<longleftrightarrow> x=y"
    | "holds s (prop_not \<phi>) \<longleftrightarrow> \<not>holds s \<phi>"  
    | "holds s (prop_and \<phi>s) \<longleftrightarrow> (\<forall>\<phi>\<in>set \<phi>s. holds s \<phi>)"
    | "holds s (prop_or \<phi>s) \<longleftrightarrow> (\<exists>\<phi>\<in>set \<phi>s. holds s \<phi>)"
      
    fun apply_atomic :: "object ast_atomic_effect \<Rightarrow> state \<Rightarrow> state" where
      "apply_atomic (Add f) s = s \<union> {f}"
    | "apply_atomic (Del f) s = s - {f}"
      
    (* It seems to be agreed upon that, in case of a contradictionary effect, 
      addition overrides deletion. We model this behaviour by first executing 
      the deletions, and then the additions. *)
    fun apply_effect :: "object ast_effect \<Rightarrow> state \<Rightarrow> state" where
      "apply_effect (Effect aes) s = (
        let 
          s = fold apply_atomic (filter is_Del aes) s;
          s = fold apply_atomic (filter is_Add aes) s
        in s)"

    (*      
    fun pos_lit_exists :: " object ast_effect \<Rightarrow> object ast_atomic_effect \<Rightarrow> bool" where (* Given a delete atomic effect, this returns false if it is added in the given action effect *)
      "pos_lit_exists (Effect (aes,cost)) (Add f) = True"
    | "pos_lit_exists (Effect (aes,cost)) (Del f) = (if ((filter (\<lambda>ae. ae = (Add f)) aes) = []) then True else False)"

    fun apply_effect :: "object ast_effect \<Rightarrow> state \<Rightarrow> state" where
      "apply_effect (Effect (aes,cost)) s = fold apply_atomic (filter (pos_lit_exists (Effect (aes,cost))) aes) s"
    *)
      
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
      

    definition ast_action_inst_enabled :: "ast_action_inst \<Rightarrow> state \<Rightarrow> bool" where
      "ast_action_inst_enabled act s \<longleftrightarrow> holds s (precondition act)"

    definition plan_action_enabled :: "plan_action \<Rightarrow> state \<Rightarrow> bool" where
      "plan_action_enabled pa s \<longleftrightarrow> wf_plan_action pa  \<and> ast_action_inst_enabled (resolve_instantiate pa) s"

    (* Implementation note: resolve and instantiate already done inside wf_plan_action, redundancy! *)
      
    definition execute_ast_action_inst :: "ast_action_inst \<Rightarrow> state \<Rightarrow> state" where
      "execute_ast_action_inst act_inst s = apply_effect (effect act_inst) s"
      
    fun ast_action_inst_path :: "state \<Rightarrow> (ast_action_inst list) \<Rightarrow> state \<Rightarrow> bool" where
      "ast_action_inst_path s [] s' \<longleftrightarrow> (s = s')"
    | "ast_action_inst_path s (\<pi>#\<pi>s) s' \<longleftrightarrow> ast_action_inst_enabled \<pi> s \<and> (ast_action_inst_path (execute_ast_action_inst \<pi> s) \<pi>s s')"

    definition execute_plan_action :: "plan_action \<Rightarrow> state \<Rightarrow> state" where
      "execute_plan_action pa s = (execute_ast_action_inst (resolve_instantiate pa) s)"
      

    fun plan_action_path :: "state \<Rightarrow> (plan_action list) \<Rightarrow> state \<Rightarrow> bool" where
      "plan_action_path s plan s' = ((\<forall>a. a \<in> set plan \<longrightarrow> wf_plan_action a) \<and> ast_action_inst_path s (map resolve_instantiate plan) s')"
(*      "path s [] s' \<longleftrightarrow> (s = s')"
    | "path s (\<pi>#\<pi>s) s' \<longleftrightarrow> ast_action_inst_enabled \<pi> s \<and> (path (execute_ast_action_inst \<pi> s) \<pi>s s')"*)


    fun valid_plan_from :: "state \<Rightarrow> plan \<Rightarrow> bool" where
      "valid_plan_from s \<pi>s = (\<exists>s'. plan_action_path s \<pi>s s' \<and> holds s' (goal P))"

    fun valid_plan_from_explicit :: "state \<Rightarrow> plan \<Rightarrow> bool" where
      "valid_plan_from_explicit s [] \<longleftrightarrow> holds s (goal P)"
    | "valid_plan_from_explicit s (\<pi>#\<pi>s) \<longleftrightarrow> plan_action_enabled \<pi> s \<and> (valid_plan_from_explicit (execute_plan_action \<pi> s) \<pi>s)"

    lemma valid_plan_explicit_eq_succinct: "valid_plan_from_explicit s \<pi>s = valid_plan_from s \<pi>s"
      proof(induction \<pi>s arbitrary: s)
        case Nil
        then show ?case by auto
     next
       case (Cons a \<pi>s)
       then show ?case by (auto simp add: plan_action_enabled_def execute_plan_action_def ast_action_inst_enabled_def)
     qed

    

    (* Implementation note: resolve and instantiate already done inside enabledness check, redundancy! *)
      
    definition I :: "state" where
      "I \<equiv> set (init P)"
      
    definition valid_plan :: "plan \<Rightarrow> bool" 
      where "valid_plan \<equiv> valid_plan_from I"
    
    lemma valid_plan_explicit: "valid_plan = valid_plan_from_explicit I"
          using valid_plan_explicit_eq_succinct by (auto simp add: valid_plan_def)
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
    definition wf_state :: "state \<Rightarrow> bool" where
      "wf_state s \<equiv> \<forall>f\<in>s. wf_fact f"

      
    fun wf_action_inst :: "ast_action_inst \<Rightarrow> bool" where   
      "wf_action_inst (Action_Inst pre eff) \<longleftrightarrow> (
          wf_prop objT pre
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
    lemma wf_I: "wf_state I"
      using wf_problem
      unfolding I_def wf_state_def wf_problem_def
      by auto  

    lemma wf_apply_atomic:   
      assumes "wf_state s"  
      assumes "wf_atomic_effect objT ae"
      shows "wf_state (apply_atomic ae s)"  
      using assms 
      apply (cases ae) 
      apply (auto simp: wf_state_def wf_fact_def)
      done  
        
    lemma wf_fold_apply_atomic:
      assumes "wf_state s"  
      assumes "\<forall>ae\<in>set aes. wf_atomic_effect objT ae"  
      shows "wf_state (fold apply_atomic aes s)"
      using assms 
      apply (induction aes arbitrary: s)
      apply (simp add: wf_state_def)  
      apply (auto intro: wf_apply_atomic)
      done  
        
    lemma wf_apply_effect:
      assumes "wf_effect objT e"
      assumes "wf_state s"  
      shows "wf_state (apply_effect e s)"  
      using assms
      by (cases e) (fastforce intro: wf_fold_apply_atomic) 

        
    context 
      fixes Q f
      assumes INST: "is_of_type Q x T \<Longrightarrow> is_of_type objT (f x) T"  
    begin
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
          using assms
          by (cases a; auto split: option.splits)  
      qed  
        
      lemma wf_inst_atomic_effect: 
        assumes "wf_atomic_effect Q ae" 
        shows "wf_atomic_effect objT (map_ast_atomic_effect f ae)"
        using assms(1)
        by (cases ae; auto simp: wf_inst_atom)  
        
      lemma wf_inst_effect: 
        assumes "wf_effect Q \<phi>" 
        shows "wf_effect objT (map_ast_effect f \<phi>)"
        using assms(1)
        by (induction \<phi>) (auto simp: wf_inst_atomic_effect)
        
      lemma wf_inst_eq_aux: "Q x = Some T \<Longrightarrow> objT (f x) \<noteq> None"
        using INST[of x T] unfolding is_of_type_def 
        by (auto split: option.splits)
          
      lemma wf_inst_prop: 
        assumes "wf_prop Q \<phi>" 
        shows "wf_prop objT (map_ast_prop f \<phi>)"
        using assms
        apply (induction \<phi>)  
        apply (auto simp: wf_inst_atom dest: wf_inst_eq_aux)
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
        using assms(2)
        apply (clarsimp simp: Let_def)
        apply rule  
        apply (erule wf_inst_prop[rotated]; auto dest: INST)  
        apply (erule wf_inst_effect[rotated]; auto dest: INST)  
        done  
        
    qed    
        
    lemma wf_execute:
      assumes "plan_action_enabled \<pi> s"
      assumes "wf_state s"  
      shows "wf_state (execute_plan_action \<pi> s)"
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
        by (rule \<open>wf_state s\<close>)
    qed

  end

end
