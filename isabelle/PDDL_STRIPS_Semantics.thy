section \<open>PDDL and STRIPS Semantics\<close>
theory PDDL_STRIPS_Semantics
imports 
  "Propositional_Proof_Systems.Formulas" 
  "Propositional_Proof_Systems.Sema" 
begin

subsection \<open>Utility Functions\<close>
definition "index_by f l \<equiv> map_of (map (\<lambda>x. (f x,x)) l)"

lemma index_by_eq_Some_eq[simp]: 
  assumes "distinct (map f l)"
  shows "index_by f l n = Some x \<longleftrightarrow> (x\<in>set l \<and> f x = n)"  
  unfolding index_by_def 
  using assms  
  by (auto simp: o_def)

lemma index_by_eq_SomeD: 
  shows "index_by f l n = Some x \<Longrightarrow> (x\<in>set l \<and> f x = n)"  
  unfolding index_by_def 
  by (auto dest: map_of_SomeD)
  
    
lemma lookup_zip_idx_eq:
  assumes "length params = length args"
  assumes "i<length args"  
  assumes "distinct params"  
  assumes "k = params ! i"  
  shows "map_of (zip params args) k = Some (args ! i)"
  using assms
  by (auto simp: in_set_conv_nth)  
  
lemma rtrancl_image_idem[simp]: "R\<^sup>* `` R\<^sup>* `` s = R\<^sup>* `` s"  
  by (metis relcomp_Image rtrancl_idemp_self_comp)
  

subsection \<open>Abstract Syntax\<close>  
  
subsubsection \<open>Generic Entities\<close>
type_synonym name = string
                                                                     
datatype predicate = Pred (name: name)

text \<open>Some of the AST entities are defined over a polymorphic \<open>'val\<close> type, 
  which gets either instantiated by variables (for domains) 
  or objects (for problems).
\<close>
  
text \<open>An atom is either a predicate with arguments, or an equality statement.\<close>
datatype 'val atom = predAtm (predicate: predicate) (arguments: "'val list")
                     | Eq (lhs: 'val) (rhs: 'val)

text \<open>A type is a list of primitive type names. 
  To model a primitive type, we use a singleton list.\<close>                         
datatype type = Either (primitives: "name list")
  
text \<open>An effect contains a list of values to be added, and a list of values 
  to be removed.\<close>
datatype 'val ast_effect = Effect (Adds: "('val) list") (Dels: "('val) list")

text \<open>Variables are identified by their names.\<close>
datatype variable = varname: Var name

subsubsection \<open>Domains\<close>

text \<open>An action schema has a name, a typed parameter list, a precondition, 
  and an effect.\<close>
datatype ast_action_schema = Action_Schema
  (name: name)
  (parameters: "(variable \<times> type) list")
  (precondition: "variable atom formula")
  (effect: "variable atom formula ast_effect")

text \<open>A predicate declaration contains the predicate's name and its 
  argument types.\<close>  
datatype predicate_decl = PredDecl 
  (pred: predicate) 
  (argTs: "type list")
  
text \<open>A domain contains the declarations of primitive types, predicates, 
  and action schemas.\<close>  
datatype ast_domain = Domain
  (types: "name list") -- \<open>Only supports flat type hierarchy\<close>
  (predicates: "predicate_decl list")
  (actions: "ast_action_schema list")

subsubsection \<open>Problems\<close>
  
text \<open>Objects are identified by their names\<close>
datatype object = name: Obj name  

text \<open>A fact is an atom over objects.\<close>
type_synonym fact = "object atom"
  
text \<open>A problem consists of a domain, a list of objects, 
  a description of the initial state, and a description of the goal state. \<close>
datatype ast_problem = Problem
  (domain: ast_domain)
  (objects: "(object \<times> type) list")
  (init: "fact formula list")
  (goal: "fact formula")
  
  
subsubsection \<open>Plans\<close>  
datatype plan_action = PAction
  (name: name)
  (arguments: "object list")

type_synonym plan = "plan_action list"  
  
subsubsection \<open>Ground Actions\<close>
text \<open>The following datatype represents an action scheme that has been 
  instantiated by replacing the arguments with concrete objects,
  also called ground action.
\<close>
datatype ast_action_inst = Action_Inst
  (precondition: "(object atom) formula")
  (effect: "(object atom) formula ast_effect")
  
subsection \<open>STRIPS Semantics\<close>

text \<open>Discriminator for atomic formulas.\<close>
fun is_Atom where 
  "is_Atom (Atom _) = True" | "is_Atom _ = False"



text \<open>The world model is a set of ground formulas\<close>
type_synonym world_model = "fact formula set"

text \<open>For this section, we fix a domain \<open>D\<close>, using Isabelle's 
  locale mechanism.\<close>
locale ast_domain = 
  fixes D :: ast_domain
begin    
  text \<open>It seems to be agreed upon that, in case of a contradictory effect, 
    addition overrides deletion. We model this behaviour by first executing 
    the deletions, and then the additions.\<close>    
  fun apply_effect 
    :: "object atom formula ast_effect \<Rightarrow> world_model \<Rightarrow> world_model" 
  where
     "apply_effect (Effect (adds) (dels)) s = (s - (set dels)) \<union> ((set adds))"

  text \<open>Execute an action instance\<close>
  definition execute_ast_action_inst 
    :: "ast_action_inst \<Rightarrow> world_model \<Rightarrow> world_model" 
  where
    "execute_ast_action_inst act_inst M = apply_effect (effect act_inst) M"    
    
  text \<open>Predicate to model that the given list of action instances is 
    executable, and transforms an initial world model \<open>M\<close> into a final 
    model \<open>M'\<close>.
    
    Note that this definition over the list structure is more convenient in HOL
    than to explicitly define an indexed sequence \<open>M\<^sub>0\<dots>M\<^sub>N\<close> of intermediate world
     models, as done in [Lif87].
  \<close>
  fun ast_action_inst_path 
    :: "world_model \<Rightarrow> (ast_action_inst list) \<Rightarrow> world_model \<Rightarrow> bool" 
  where
    "ast_action_inst_path M [] M' \<longleftrightarrow> (M = M')"
  | "ast_action_inst_path M (\<alpha>#\<alpha>s) M' \<longleftrightarrow> M \<TTurnstile> precondition \<alpha> 
    \<and> (ast_action_inst_path (execute_ast_action_inst \<alpha> M) \<alpha>s M')"

  text \<open>Function equations as presented in paper, 
    with inlined @{const execute_ast_action_inst}.\<close>
  lemma ast_action_inst_path_in_paper:  
    "ast_action_inst_path M [] M' \<longleftrightarrow> (M = M')"
    "ast_action_inst_path M (\<alpha>#\<alpha>s) M' \<longleftrightarrow> M \<TTurnstile> precondition \<alpha> 
    \<and> (ast_action_inst_path (apply_effect (effect \<alpha>) M) \<alpha>s M')"
    by (auto simp: execute_ast_action_inst_def)
  
end -- \<open>Context of \<open>ast_domain\<close>\<close>

subsubsection \<open>Soundness theorem for the STRIPS semantics\<close>
text \<open>We prove the soundness theorem according to [Lif87].\<close>

text \<open>States are modeled as valuations of our underlying predicate logic.\<close>  
type_synonym state = "object atom valuation"

context ast_domain begin
  text \<open>An action is a partial function from states to states. \<close>  
  type_synonym action = "state \<rightharpoonup> state"
  
  text \<open>The Isabelle/HOL formula @{prop \<open>f s = Some s'\<close>} means 
    that \<open>f\<close> is applicable in state \<open>s\<close>, and the result is \<open>s'\<close>. \<close>
  
  text \<open>Definition B (i)--(iv) in [Lif87]\<close>
  fun sound_opr :: "ast_action_inst \<Rightarrow> action \<Rightarrow> bool" where
    "sound_opr (Action_Inst pre (Effect add del)) f \<longleftrightarrow> 
      (\<forall>s. s \<Turnstile> pre \<longrightarrow> 
        (\<exists>s'. f s = Some s' \<and>
    (\<forall>atm. is_Atom atm \<and> atm \<notin> set del \<and> s \<Turnstile> atm \<longrightarrow> s' \<Turnstile> atm) 
  \<and> (\<forall>fmla. fmla \<in> set add \<longrightarrow> s' \<Turnstile> fmla) 
  \<and> (\<forall>fmla\<in>set add. \<not>is_Atom fmla \<longrightarrow> (\<forall>s. s \<Turnstile> fmla))
        )
      )"
      
  text \<open>Definition B (v)--(vii) in [Lif87]\<close>
  definition sound_system 
    :: "ast_action_inst set 
      \<Rightarrow> world_model 
      \<Rightarrow> object atom valuation 
      \<Rightarrow> (ast_action_inst \<Rightarrow> action) 
      \<Rightarrow> bool"
    where
    "sound_system \<Sigma> M\<^sub>0 s\<^sub>0 f \<longleftrightarrow> 
        (\<forall>fmla\<in>M\<^sub>0. s\<^sub>0 \<Turnstile> fmla) 
      \<and> (\<forall>fmla\<in>M\<^sub>0. \<not>is_Atom fmla \<longrightarrow> (\<forall>s. s \<Turnstile> fmla))
      \<and> (\<forall>\<alpha>\<in>\<Sigma>. sound_opr \<alpha> (f \<alpha>))"

  text \<open>Composing two actions\<close>    
  definition compose_action :: "action \<Rightarrow> action \<Rightarrow> action" where
    "compose_action f1 f2 x = (case f2 x of Some y \<Rightarrow> f1 y | None \<Rightarrow> None)"

  text \<open>Composing a list of actions\<close>  
  definition compose_actions :: "action list \<Rightarrow> action" where
    "compose_actions fs \<equiv> fold compose_action fs Some"

  text \<open>Composing a list of actions satisfies some natural lemmas: \<close>            
  lemma compose_actions_Nil[simp]: 
    "compose_actions [] = Some" unfolding compose_actions_def by auto
    
  lemma compose_actions_Cons[simp]:
    "f s = Some s' \<Longrightarrow> compose_actions (f#fs) s = compose_actions fs s'" 
  proof -  
    interpret monoid_add compose_action Some 
      apply unfold_locales
      unfolding compose_action_def 
      by (auto split: option.split)
    assume "f s = Some s'"  
    then show ?thesis  
      unfolding compose_actions_def
      by (simp add: compose_action_def fold_plus_sum_list_rev)
  qed
   
  lemma sound_opr_alt:  
    "sound_opr opr f = 
      (\<forall>s. s \<Turnstile> (precondition opr) \<longrightarrow> (\<exists>s'. f s = (Some s') \<and>
    (\<forall>atm. is_Atom atm \<and> atm \<notin> set(Dels (effect opr)) \<and> s \<Turnstile> atm \<longrightarrow> s' \<Turnstile> atm) 
  \<and> (\<forall>atm. atm \<in> set(Adds (effect opr)) \<longrightarrow> s' \<Turnstile> atm) 
  \<and> (\<forall>s.\<forall>fmla\<in>set(Adds (effect opr)). \<not>is_Atom fmla \<longrightarrow> s \<Turnstile> fmla)
      ))"
    by (cases "(opr,f)" rule: sound_opr.cases) auto
    
    
  text \<open>Soundness Theorem of [Lif87]. \<close>  
  theorem STRIPS_sema_sound: 
    assumes "sound_system \<Sigma> M\<^sub>0 s\<^sub>0 f" 
      -- \<open>For a sound system \<open>\<Sigma>\<close>\<close>
    assumes "set \<alpha>s \<subseteq> \<Sigma>"
      -- \<open>And a plan \<open>\<alpha>s\<close>\<close>  
    assumes "ast_action_inst_path M\<^sub>0 \<alpha>s M'" 
      -- \<open>Which is accepted by the system, yielding result \<open>M'\<close> 
          (called \<open>R(\<alpha>s)\<close> in [Lif87])\<close>
    obtains s' 
      -- \<open>We have that \<open>f(\<alpha>s)\<close> is applicable 
          in initial state, yielding state \<open>s'\<close> (called \<open>f\<^sub>\<alpha>\<^sub>s(s\<^sub>0)\<close> in [Lif87])\<close>
      where "compose_actions (map f \<alpha>s) s\<^sub>0 = Some s'" 
        -- \<open>The result world model \<open>M'\<close> is satisfied in state \<open>s'\<close>\<close>
        and "\<forall>fmla\<in>M'. s' \<Turnstile> fmla" 
  proof -  
    have "\<exists>s'. compose_actions (map f \<alpha>s) s\<^sub>0 = Some s' \<and> (\<forall>fmla\<in>M'. s' \<Turnstile> fmla)" 
      using assms
    proof(induction \<alpha>s arbitrary: s\<^sub>0 M\<^sub>0 )
      case Nil
      then show ?case by (auto simp add: compose_action_def sound_system_def) 
    next
      case ass: (Cons \<alpha> \<alpha>s)
      then obtain pre add del where a: "\<alpha> = Action_Inst pre (Effect add del)"
        using ast_action_inst.exhaust ast_effect.exhaust by metis
      let ?M\<^sub>1 = "execute_ast_action_inst \<alpha> M\<^sub>0" 
      obtain s\<^sub>1 where s1: "(f \<alpha>) s\<^sub>0 = Some s\<^sub>1"
        "(\<forall>atm. is_Atom atm \<longrightarrow> atm \<notin> set(Dels (effect \<alpha>))
                                            \<longrightarrow> s\<^sub>0 \<Turnstile> atm
                                            \<longrightarrow> s\<^sub>1 \<Turnstile> atm) \<and>
                                 (\<forall>fmla. fmla \<in> set(Adds (effect \<alpha>))
                                            \<longrightarrow> s\<^sub>1 \<Turnstile> fmla)"
        using ass(2-4)
        unfolding sound_system_def sound_opr_alt
        by (force simp: entailment_def)
        
      have "(\<forall>fmla\<in>?M\<^sub>1. s\<^sub>1 \<Turnstile> fmla)"
        apply(rule ballI)
        using ass(2) s1 formula.exhaust
        unfolding sound_system_def execute_ast_action_inst_def
        by (fastforce simp add: a image_def)
      moreover have "(\<forall>s.\<forall>fmla\<in>?M\<^sub>1. \<not>is_Atom fmla \<longrightarrow> s \<Turnstile> fmla)"
        using ass(2)
        unfolding sound_system_def execute_ast_action_inst_def 
        using a ass.prems(2) ass.prems(3) entailment_def list.set_intros(1)
        by fastforce
      moreover have "(\<forall>opr\<in>\<Sigma>. sound_opr opr (f opr))"
        using ass(2) unfolding sound_system_def
        by (auto simp add:)
      ultimately have "sound_system \<Sigma> ?M\<^sub>1 s\<^sub>1 f"
        unfolding sound_system_def
        by auto
      from ass.IH[OF this] ass.prems obtain s' where
        "compose_actions (map f \<alpha>s) s\<^sub>1 = Some s' \<and> (\<forall>a\<in>M'. s' \<Turnstile> a)"
        by auto
      thus ?case by (auto simp: s1(1))
    qed
    with that show ?thesis by blast
  qed
    
  text \<open>More compact notation of the soundness theorem.\<close>
  theorem STRIPS_sema_sound_compact_version: 
    "sound_system \<Sigma> M\<^sub>0 s\<^sub>0 f \<Longrightarrow> set \<alpha>s \<subseteq> \<Sigma> 
    \<Longrightarrow> ast_action_inst_path M\<^sub>0 \<alpha>s M'  
    \<Longrightarrow> \<exists>s'. compose_actions (map f \<alpha>s) s\<^sub>0 = Some s' 
          \<and> (\<forall>fmla\<in>M'. s' \<Turnstile> fmla)"
    using STRIPS_sema_sound by metis

end -- \<open>Context of \<open>ast_domain\<close>\<close>


subsection \<open>Well-Formedness of PDDL\<close>
  
(* Well-formedness *)  

(*    
  Compute signature: predicate/arity
  Check that all atoms (schemas and facts) satisfy signature
  
  for action:
    Check that used parameters \<subseteq> declared parameters
    
  for init/goal: Check that facts only use declared objects  
*)    
  

context ast_domain begin

  text \<open>The signature is a partial function that maps the predicates 
    of the domain to lists of argument types.\<close>
  definition sig :: "predicate \<rightharpoonup> type list" where
    "sig \<equiv> map_of (map (\<lambda>PredDecl p n \<Rightarrow> (p,n)) (predicates D))"

  text \<open>We use a flat subtype hierarchy, where every type is a subtype 
    of object, and there are no other subtype relations. 
    
    Note that we do not need to restrict this relation to declared types, 
    as we will explicitly ensure that all types used in the problem are 
    declared.
    \<close>  
  definition "subtype_rel \<equiv> {''object''}\<times>UNIV" 
    
  definition of_type :: "type \<Rightarrow> type \<Rightarrow> bool" where
    "of_type oT T \<equiv> set (primitives oT) \<subseteq> subtype_rel\<^sup>* `` set (primitives T)"
  text \<open>This checks that every primitive on the LHS is contained in or a 
    subtype of a primitive on the RHS\<close>

    
  text \<open>For the next few definitions, we fix a partial function that maps 
    a polymorphic entity type @{typ "'e"} to types. An entity can be 
    instantiated by variables or objects later.\<close>
  context 
    fixes ty_ent :: "'ent \<rightharpoonup> type"  -- \<open>Entity's type, None if invalid\<close>
  begin
    
    text \<open>Checks whether an entity has a given type\<close>
    definition is_of_type :: "'ent \<Rightarrow> type \<Rightarrow> bool" where
      "is_of_type v T \<longleftrightarrow> (
        case ty_ent v of
          Some vT \<Rightarrow> of_type vT T
        | None \<Rightarrow> False)"
    
    text \<open>Predicate-atoms are well-formed if their arguments match the 
      signature, equalities are well-formed if the arguments are valid 
      objects (have a type).
      
      TODO: We could check that types may actually overlap
    \<close>
    fun wf_atom :: "'ent atom \<Rightarrow> bool" where
      "wf_atom (predAtm p vs) \<longleftrightarrow> (
        case sig p of 
          None \<Rightarrow> False
        | Some Ts \<Rightarrow> list_all2 is_of_type vs Ts)"
    | "wf_atom (Eq _ _) = False"
    

    text \<open>A formula is well-formed if it consists of valid atoms, 
      and does not contain negations, except for the encoding \<open>\<^bold>\<not>\<bottom>\<close> of true.
    \<close>
    fun wf_fmla :: "('ent atom) formula \<Rightarrow> bool" where
      "wf_fmla (Atom a) \<longleftrightarrow> wf_atom a"
    | "wf_fmla (\<phi>1 \<^bold>\<and> \<phi>2) \<longleftrightarrow> (wf_fmla \<phi>1 \<and> wf_fmla \<phi>2)"  
    | "wf_fmla (\<phi>1 \<^bold>\<or> \<phi>2) \<longleftrightarrow> (wf_fmla \<phi>1 \<and> wf_fmla \<phi>2)"  
    | "wf_fmla (\<^bold>\<not>\<bottom>) \<longleftrightarrow> True"
    | "wf_fmla _ \<longleftrightarrow> False"  

    lemma wf_fmla_add_simps[simp]: "wf_fmla (\<^bold>\<not>\<phi>) \<longleftrightarrow> \<phi>=\<bottom>"
      by (cases \<phi>) auto

    text \<open>Special case for a well-formed atomic formula\<close>  
    fun wf_fmla_atom where
      "wf_fmla_atom (Atom a) \<longleftrightarrow> wf_atom a"  
    | "wf_fmla_atom _ \<longleftrightarrow> False"
             
    lemma wf_fmla_atom_alt: "wf_fmla_atom \<phi> \<longleftrightarrow> is_Atom \<phi> \<and> wf_fmla \<phi>"
      by (cases \<phi>) auto
    
    text \<open>An effect is well-formed if the added and removed formulas 
      are atomic\<close>
    fun wf_effect where
      "wf_effect (Effect adds dels) \<longleftrightarrow> 
          (\<forall>ae\<in>set adds. wf_fmla_atom ae) 
        \<and> (\<forall>de\<in>set dels.  wf_fmla_atom de)"
  
  end -- \<open>Context fixing \<open>ty_ent\<close>\<close>
    
  text \<open>An action schema is well-formed if the parameter names are distinct,
    and the precondition and effect is well-fromed wrt.\ the parameters.
  \<close>
  fun wf_action_schema :: "ast_action_schema \<Rightarrow> bool" where   
    "wf_action_schema (Action_Schema n params pre eff) \<longleftrightarrow> (
      let
        tyv = map_of params
      in
        distinct (map fst params)
      \<and> wf_fmla tyv pre
      \<and> wf_effect tyv eff)"
    
  text \<open>A type is well-formed if it consists only of declared primitive types,
     and the type object.\<close>
  fun wf_type where
    "wf_type (Either Ts) \<longleftrightarrow> set Ts \<subseteq> insert ''object'' (set (types D))"
    
  text \<open>A predicate is well-formed if its argument types are well-formed.\<close>  
  fun wf_predicate_decl where 
    "wf_predicate_decl (PredDecl p Ts) \<longleftrightarrow> (\<forall>T\<in>set Ts. wf_type T)"
    
  text \<open>A domain is well-formed if  
    \<^item> there are no duplicate declared primitive types, 
    \<^item> there are no duplicate declared predicate names, 
    \<^item> all declared predicates are well-formed,   
    \<^item> there are no duplicate action names,
    \<^item> and all declared actions are well-formed
    \<close>  
  definition wf_domain :: "bool" where
    "wf_domain \<equiv> 
      distinct (types D)
    \<and> distinct (map (predicate_decl.pred) (predicates D))
    \<and> (\<forall>p\<in>set (predicates D). wf_predicate_decl p)
    \<and> distinct (map ast_action_schema.name (actions D))
    \<and> (\<forall>a\<in>set (actions D). wf_action_schema a)
    "

end -- \<open>locale \<open>ast_domain\<close>\<close> 

text \<open>We fix a problem, and also include the definitions for the domain 
  of this problem.\<close>
locale ast_problem = ast_domain "domain P" 
  for P :: ast_problem 
begin  
  text \<open>We refer to the problem domain as \<open>D\<close>\<close>
  abbreviation "D \<equiv> ast_problem.domain P"
  
  definition objT :: "object \<rightharpoonup> type" where
    "objT \<equiv> map_of (objects P)"
      
  definition wf_fact :: "fact \<Rightarrow> bool" where
    "wf_fact = wf_atom objT"

  text \<open>This definition is needed for well-formedness of the initial model,
    and forward-references to the concept of world model.
  \<close>  
  definition wf_world_model where 
    "wf_world_model M = (\<forall>f\<in>M. wf_fmla_atom objT f)"

  definition wf_problem where
    "wf_problem \<equiv>                                      
      wf_domain
    \<and> distinct (map fst (objects P))
    \<and> (\<forall>(n,T)\<in>set (objects P). wf_type T)
    \<and> distinct (init P)
    \<and> wf_world_model (set (init P))
    \<and> wf_fmla objT (goal P)
    "

  fun wf_effect_inst :: "object atom formula ast_effect \<Rightarrow> bool" where
    "wf_effect_inst (Effect (adds) (dels)) 
      \<longleftrightarrow> (\<forall>a\<in>set adds \<union> set dels. wf_fmla_atom objT a)"

  lemma wf_effect_inst_alt: "wf_effect_inst eff = wf_effect objT eff"
    by (cases eff) auto
    
end -- \<open>locale \<open>ast_problem\<close>\<close>

text \<open>Locale to express a well-formed domain\<close>
locale wf_ast_domain = ast_domain + 
  assumes wf_domain: wf_domain  
  
text \<open>Locale to express a well-formed problem\<close>
locale wf_ast_problem = ast_problem P for P +
  assumes wf_problem: wf_problem
begin
  sublocale wf_ast_domain "domain P"
    apply unfold_locales
    using wf_problem
    unfolding wf_problem_def by simp
      
end -- \<open>locale \<open>wf_ast_problem\<close>\<close>
  
subsection \<open>PDDL Semantics\<close>

(* Semantics *)  

(*  To apply plan_action:   
    find action schema, instantiate, check precond, apply effect
*)
  

  
context ast_domain begin
    
  definition resolve_action_schema :: "name \<rightharpoonup> ast_action_schema" where 
    "resolve_action_schema n = index_by ast_action_schema.name (actions D) n"

  text \<open>To instantiate an action schema, we first compute a substitution from 
    parameters to objects, and then apply this substitution to the 
    precondition and effect. The substitution is applied via the \<open>map_xxx\<close> 
    functions generated by the datatype package.
    \<close>
  fun instantiate_action_schema 
    :: "ast_action_schema \<Rightarrow> object list \<Rightarrow> ast_action_inst" 
  where
    "instantiate_action_schema (Action_Schema n params pre eff) args = (let 
        psubst = (the o (map_of (zip (map fst params) args)));
        pre_inst = (map_formula o map_atom) psubst pre;
        eff_inst = (map_ast_effect o map_formula o map_atom) psubst eff
      in
        Action_Inst pre_inst eff_inst
      )"
     
end -- \<open>Context of \<open>ast_domain\<close>\<close>
    

context ast_problem begin  

  text \<open>Initial model\<close>  
  definition I :: "world_model" where
    "I \<equiv> set (init P)"


  text \<open>Resolve a plan action and instantiate the referenced action schema.\<close>
  fun resolve_instantiate :: "plan_action \<Rightarrow> ast_action_inst" where
    "resolve_instantiate (PAction n args) = 
      instantiate_action_schema 
        (the (resolve_action_schema n))
        args"
  
  text \<open>Check whether object has specified type\<close>      
  definition "is_obj_of_type n T \<equiv> case objT n of
    None \<Rightarrow> False
  | Some oT \<Rightarrow> of_type oT T"  
    
  text \<open>We can also use the generic \<open>is_of_type\<close> function.\<close>
  lemma is_obj_of_type_alt: "is_obj_of_type = is_of_type objT"  
    apply (intro ext)
    unfolding is_obj_of_type_def is_of_type_def by auto
    

  text \<open>HOL encoding of matching an action's formal parameters against an 
    argument list. 
    The parameters of the action are encoded as a list of \<open>name\<times>type\<close> pairs, 
    such that we map it to a list of types first. Then, the list 
    relator @{const list_all2} checks that arguments and types have the same 
    length, and each matching pair of argument and type 
    satisfies the predicate @{const is_obj_of_type}.
  \<close>
  definition "action_params_match a args 
    \<equiv> list_all2 is_obj_of_type args (map snd (parameters a))"
  
  text \<open>At this point, we can define well-formedness of a plan action:
    The action must refer to a declared action schema, the arguments must 
    be compatible with the formal parameters' types.
  \<close>                    
  fun wf_plan_action :: "plan_action \<Rightarrow> bool" where
    "wf_plan_action (PAction n args) = ( 
      case resolve_action_schema n of 
        None \<Rightarrow> False 
      | Some a \<Rightarrow> 
          (* Objects are valid and match parameter types *)
          action_params_match a args 
          (* Effect is valid *)
        \<and> wf_effect_inst (effect (instantiate_action_schema a args)) 
        )"
  text \<open>
    TODO: The second conjunct is redundant, as instantiating a well formed 
      action with valid objects yield a valid effect.
  \<close>      
  
    
    
  text \<open>A sequence of plan actions form a path, if they are well-formed and 
    their instantiations form a path.\<close>  
  definition plan_action_path 
    :: "world_model \<Rightarrow> (plan_action list) \<Rightarrow> world_model \<Rightarrow> bool" 
  where
    "plan_action_path M \<pi>s M' = 
        ((\<forall>\<pi> \<in> set \<pi>s. wf_plan_action \<pi>) 
      \<and> ast_action_inst_path M (map resolve_instantiate \<pi>s) M')"
    
  text \<open>A plan is valid wrt.\ a given initial model, if it forms a path to a 
    goal model \<close>
  definition valid_plan_from :: "world_model \<Rightarrow> plan \<Rightarrow> bool" where
    "valid_plan_from M \<pi>s = (\<exists>M'. plan_action_path M \<pi>s M' \<and> M' \<TTurnstile> (goal P))"
    
  (* Implementation note: resolve and instantiate already done inside 
      enabledness check, redundancy! *)
    
  text \<open>Finally, a plan is valid if it is valid wrt.\ the initial world 
    model @{const I}\<close>
  definition valid_plan :: "plan \<Rightarrow> bool" 
    where "valid_plan \<equiv> valid_plan_from I"
  
end -- \<open>Context of \<open>ast_problem\<close>\<close> 

  

subsection \<open>Preservation of Well-Formedness\<close>

subsubsection \<open>Well-Formed Action Instances\<close>
text \<open>The goal of this section is to establish that well-formedness of 
  world models is preserved by execution of well-formed plan actions.
\<close>
  
context ast_problem begin    
    
  text \<open>As plan actions are executed by first instantiating them, and then 
    executing the action instance, it is natural to define a well-formedness 
    concept for action instances.\<close>

  fun wf_action_inst :: "ast_action_inst \<Rightarrow> bool" where   
    "wf_action_inst (Action_Inst pre eff) \<longleftrightarrow> (
        wf_fmla objT pre
      \<and> wf_effect objT eff
      )
    "
    
  text \<open>We first prove that instantiating a well-formed action schema will yield 
    a well-formed action instance. 
    
    We begin with some auxiliary lemmas before the actual theorem.
  \<close>  
    
  lemma (in ast_domain) of_type_refl[simp, intro!]: "of_type T T"
    unfolding of_type_def by auto
    
  lemma (in ast_domain) of_type_trans[trans]: 
    "of_type T1 T2 \<Longrightarrow> of_type T2 T3 \<Longrightarrow> of_type T1 T3"
    unfolding of_type_def  
    by clarsimp (metis (no_types, hide_lams) 
      Image_mono contra_subsetD order_refl rtrancl_image_idem)
    
  lemma is_of_type_map_ofE:
    assumes "is_of_type (map_of params) x T"  
    obtains i xT where "i<length params" "params!i = (x,xT)" "of_type xT T"
    using assms  
    unfolding is_of_type_def
    by (auto split: option.splits dest!: map_of_SomeD simp: in_set_conv_nth)  

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
      using assms wf_inst_atom 
      by (cases a; auto)

    lemma wf_inst_effect: 
      assumes "wf_effect Q \<phi>" 
      shows "wf_effect objT ((map_ast_effect o map_formula o map_atom) f \<phi>)"
      using assms
      proof (induction \<phi>)
        case (Effect x1a x2a)
        then show ?case using wf_inst_formula_atom by auto
      qed

    lemma wf_inst_formula: 
      assumes "wf_fmla Q \<phi>" 
      shows "wf_fmla objT ((map_formula o map_atom) f \<phi>)"
      using assms
      by (induction \<phi>) (auto simp: wf_inst_atom dest: wf_inst_eq_aux)
      
  end

    
  text \<open>Instantiating a well-formed action schema with compatible arguments 
    will yield a well-formed action instance.
  \<close>  
  theorem wf_instantiate_action_schema:
    assumes "action_params_match a args"  
    assumes "wf_action_schema a"  
    shows "wf_action_inst (instantiate_action_schema a args)"
  proof (cases a)
    case [simp]: (Action_Schema name params pre eff)
    have INST: 
      "is_of_type objT ((the \<circ> map_of (zip (map fst params) args)) x) T"
      if "is_of_type (map_of params) x T" for x T
      using that
      apply (rule is_of_type_map_ofE)
      using assms  
      apply (clarsimp simp: Let_def)
      subgoal for i xT 
        unfolding action_params_match_def
        apply (subst lookup_zip_idx_eq[where i=i]; 
          (clarsimp simp: list_all2_lengthD)?)
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
end -- \<open>Context of \<open>ast_problem\<close>\<close>    
    
      
    
subsubsection \<open>Preservation\<close>
    
context ast_problem begin    
    
  text \<open>We start by defining two shorthands for enabledness and execution of 
    a plan action.\<close>

  text \<open>Shorthand for enabled plan action: It is well-formed, and the 
    precondition holds for its instance.\<close>
  definition plan_action_enabled :: "plan_action \<Rightarrow> world_model \<Rightarrow> bool" where
    "plan_action_enabled \<pi> M 
      \<longleftrightarrow> wf_plan_action \<pi> \<and> M \<TTurnstile> precondition (resolve_instantiate \<pi>)"

  text \<open>Shorthand for executing a plan action: Resolve, instantiate, and 
    apply effect\<close>
  definition execute_plan_action :: "plan_action \<Rightarrow> world_model \<Rightarrow> world_model" 
    where "execute_plan_action \<pi> M 
      = (apply_effect (effect (resolve_instantiate \<pi>)) M)"
    
  text \<open>The @{const plan_action_path} predicate can be decomposed naturally 
    using these shorthands: \<close>  
  lemma plan_action_path_Nil[simp]: "plan_action_path M [] M' \<longleftrightarrow> M'=M"  
    by (auto simp: plan_action_path_def)
    
  lemma plan_action_path_Cons[simp]:
    "plan_action_path M (\<pi>#\<pi>s) M' \<longleftrightarrow> 
      plan_action_enabled \<pi> M
    \<and> plan_action_path (execute_plan_action \<pi> M) \<pi>s M'"
    by (auto 
      simp: plan_action_path_def execute_plan_action_def 
            execute_ast_action_inst_def plan_action_enabled_def)
    
    
          
end -- \<open>Context of \<open>ast_problem\<close>\<close> 

context wf_ast_problem begin
  text \<open>The initial world model is well-formed\<close>
  lemma wf_I: "wf_world_model I"
    using wf_problem
    unfolding I_def wf_world_model_def wf_problem_def
    apply(safe) subgoal for f by (induction f) auto
    done

  text \<open>Application of a well-formed effect preserves well-formedness 
    of the model\<close>  
  lemma wf_apply_effect:
    assumes "wf_effect objT e"
    assumes "wf_world_model s"  
    shows "wf_world_model (apply_effect e s)"  
    using assms wf_problem 
    unfolding wf_world_model_def wf_problem_def wf_domain_def
    by (cases e) (auto split: formula.splits prod.splits)

  text \<open>Execution of plan actions preserves well-formedness\<close>
  theorem wf_execute:
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
      T: "action_params_match a args"
      by (auto split: option.splits)
        
    from wf_domain have 
      [simp]: "distinct (map ast_action_schema.name (actions D))"
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

  theorem wf_execute_compact_notation:
    "plan_action_enabled \<pi> s \<Longrightarrow> wf_world_model s 
    \<Longrightarrow> wf_world_model (execute_plan_action \<pi> s)"
    by (rule wf_execute)
  
  
  text \<open>Execution of a plan preserves well-formedness\<close>
  corollary wf_plan_action_path: 
    "\<lbrakk>wf_world_model M; plan_action_path M \<pi>s M'\<rbrakk> \<Longrightarrow> wf_world_model M'"
    by (induction \<pi>s arbitrary: M) (auto intro: wf_execute)
    
  
end -- \<open>Context of \<open>wf_ast_problem\<close>\<close>

  
subsection \<open>Soundness Theorem for PDDL\<close>

context wf_ast_problem begin

  text \<open>Mapping world models to states\<close>
  definition "state_to_wm s = (formula.Atom ` {atm. s atm})"
  definition "wm_to_state M = (%atm. (formula.Atom atm) \<in> M)"

  text \<open>Mapping AST action instances to actions\<close>
  definition "pddl_opr_to_act g_opr s = (
    let M = state_to_wm s in
    if (s \<Turnstile> (precondition g_opr)) then 
      Some (wm_to_state (apply_effect (effect g_opr) M)) 
    else 
      None)"
  
  lemma wm_to_state_to_wm: 
    "s \<Turnstile> f = wm_to_state (state_to_wm s) \<Turnstile> f"
    by (auto simp: wm_to_state_def 
      state_to_wm_def image_def)

  lemma atom_in_wm: 
    "s \<Turnstile> (formula.Atom atm) 
      \<longleftrightarrow> ((formula.Atom atm) \<in> (state_to_wm s))"
    by (auto simp: wm_to_state_def 
      state_to_wm_def image_def)
  lemma atom_in_wm_2: 
    "(wm_to_state M) \<Turnstile> (formula.Atom atm) 
      \<longleftrightarrow> ((formula.Atom atm) \<in> M)"
    by (auto simp: wm_to_state_def 
      state_to_wm_def image_def)


  lemma not_dels_preserved:
    assumes "f \<notin> (set dels)" " f \<in> M" 
    shows "f \<in> apply_effect (Effect adds dels) M"
    using assms
    by auto
  
  lemma adds_satisfied:
    assumes "f \<in> (set adds)"
    shows "f \<in> apply_effect (Effect adds dels) M"
    using assms
    by auto

  lemma wf_fmla_atm_is_atom: "wf_fmla_atom objT f \<Longrightarrow> is_Atom f"
    by (cases f) auto

  lemma wf_act_adds_are_atoms:
    assumes "wf_effect_inst effs" "ae \<in> set (Adds effs)"
    shows "is_Atom ae"
    using assms
    by (cases effs) (auto simp: wf_fmla_atom_alt)

  lemma wf_eff_pddl_ground_act_is_sound_opr:
    assumes "wf_effect_inst (effect g_opr)"
    shows "sound_opr g_opr (pddl_opr_to_act g_opr)"
    using assms
  proof(induction g_opr)
    case ass1: (Action_Inst x1a x2a)
    then show ?case
      unfolding sound_opr_alt
      apply safe
    proof-
      fix s 
      assume ass2: 
        "wf_effect_inst (effect (Action_Inst x1a x2a))" 
        "s \<Turnstile> precondition (Action_Inst x1a x2a)"
      let ?s = 
        "wm_to_state(apply_effect x2a (state_to_wm s))"
      have "pddl_opr_to_act  (Action_Inst x1a x2a) s = Some ?s"
        using ass1 ass2
        apply (cases x2a; simp)
        apply (cases x1a; simp)
        by (auto 
            simp: pddl_opr_to_act_def image_def Let_def 
            simp: state_to_wm_def entailment_def wf_fmla_atom_alt)
      moreover have 
        "del_atm \<notin> set (Dels (effect (Action_Inst x1a x2a))) 
          \<longrightarrow> is_Atom del_atm \<longrightarrow> s \<Turnstile> del_atm \<longrightarrow> ?s \<Turnstile> del_atm"
        for del_atm
        using atom_in_wm_2 not_dels_preserved atom_in_wm
        by (metis ast_action_inst.sel(2) is_Atom.elims(2) 
                  ast_effect.collapse)
      moreover have 
        "add_atm \<in> set (Adds (effect (Action_Inst x1a x2a))) 
            \<longrightarrow> ?s \<Turnstile> add_atm" for add_atm
        using wf_act_adds_are_atoms atom_in_wm_2 
          and adds_satisfied ass2(1)
        by (metis ast_action_inst.sel(2) ast_effect.collapse 
                  is_Atom.elims(2))
      moreover have 
        "(\<forall>s. \<forall>fmla\<in>set (Adds (effect (Action_Inst x1a x2a))). 
          \<not>is_Atom fmla \<longrightarrow> s \<Turnstile> fmla)"
        using wf_act_adds_are_atoms ass2(1)
        by fastforce
      ultimately show " \<exists>s'. pddl_opr_to_act (Action_Inst x1a x2a) s = Some s' 
        \<and> (\<forall>del_atm. 
              is_Atom del_atm 
            \<and> del_atm \<notin> set (Dels (effect (Action_Inst x1a x2a))) 
            \<and> s \<Turnstile> del_atm 
            \<longrightarrow> s' \<Turnstile> del_atm) 
        \<and> (\<forall>add_atm. 
              add_atm \<in> set (Adds (effect (Action_Inst x1a x2a))) 
            \<longrightarrow> s' \<Turnstile> add_atm) 
        \<and> (\<forall>s. \<forall>fmla\<in>set (Adds (effect (Action_Inst x1a x2a))). 
            \<not>is_Atom fmla \<longrightarrow> s \<Turnstile> fmla)" 
        by blast
    qed
  qed

  lemma wf_eff_impt_wf_eff_inst: "wf_effect objT eff \<Longrightarrow> wf_effect_inst eff"
    by (cases eff; auto simp add: wf_fmla_atom_alt)

  lemma wf_pddl_ground_act_is_sound_opr:
    assumes "wf_action_inst g_opr"
    shows "sound_opr g_opr (pddl_opr_to_act g_opr)"
    using wf_eff_impt_wf_eff_inst wf_eff_pddl_ground_act_is_sound_opr assms
    by (cases g_opr; auto)

  lemma wf_action_schema_sound_inst:
    assumes "action_params_match act args" "wf_action_schema act"
    shows "sound_opr 
      (instantiate_action_schema act args) 
      (pddl_opr_to_act (instantiate_action_schema act args))"
    using 
      wf_pddl_ground_act_is_sound_opr[
        OF wf_instantiate_action_schema[OF assms]] 
      by blast

  lemma wf_plan_act_is_sound:
    assumes "wf_plan_action (PAction n args)"
    shows "sound_opr 
      (instantiate_action_schema (the (resolve_action_schema n)) args) 
      (pddl_opr_to_act 
        (instantiate_action_schema (the (resolve_action_schema n)) args))"
    using assms
    using wf_action_schema_sound_inst wf_eff_pddl_ground_act_is_sound_opr 
    by (auto split: option.splits)
  
  lemma wf_plan_act_is_sound':
    assumes "wf_plan_action \<pi>"
    shows "sound_opr 
      (resolve_instantiate \<pi>) 
      (pddl_opr_to_act (resolve_instantiate \<pi>))"
    using assms wf_plan_act_is_sound 
    by (cases \<pi>; auto )
  
  lemma wf_world_model_has_atoms: "f\<in>M \<Longrightarrow> wf_world_model M \<Longrightarrow> is_Atom f"
    using wf_fmla_atm_is_atom
    unfolding wf_world_model_def
    by auto
  
  lemma wm_to_state_works_for_I:
    assumes "x \<in> I" 
    shows " wm_to_state I \<Turnstile> x"
    using wf_world_model_has_atoms assms wf_problem
    unfolding wf_problem_def I_def
    apply (cases x; auto simp add: wf_problem_def)
    using assms atom_in_wm_2 apply (auto simp: wm_to_state_def)
    by force+
    
  theorem wf_plan_sound_system:
    assumes "\<forall>\<pi>\<in> set \<pi>s. wf_plan_action \<pi>"
    shows "sound_system 
      (set (map resolve_instantiate \<pi>s)) 
      I 
      (wm_to_state I) 
      pddl_opr_to_act"
    using wm_to_state_works_for_I wf_problem wf_world_model_has_atoms 
    unfolding sound_system_def wf_problem_def I_def
    apply auto
    using wf_plan_act_is_sound' assms by blast

  theorem wf_plan_soundness_theorem:
    assumes "plan_action_path I \<pi>s M"
    defines "\<alpha>s \<equiv> map (pddl_opr_to_act \<circ> resolve_instantiate) \<pi>s"
    defines "s\<^sub>0 \<equiv> wm_to_state I"
    shows "\<exists>s'. compose_actions \<alpha>s s\<^sub>0 = Some s' \<and> (\<forall>\<phi>\<in>M. s' \<Turnstile> \<phi>)"
    apply (rule STRIPS_sema_sound)
    apply (rule wf_plan_sound_system)
    using assms 
    unfolding plan_action_path_def
    by (auto simp add: image_def)


end -- \<open>Context of \<open>wf_ast_problem\<close>\<close>
  

subsection \<open>Closed-World Assumption and Negation\<close>

  text \<open>A valuation extracted from the atoms of the world model\<close>
  definition valuation :: "world_model \<Rightarrow> object atom \<Rightarrow> bool"
    where "valuation M \<equiv> \<lambda>x. (Atom x \<in> M)"

  text \<open>Augment a world model by adding negated versions of all atoms 
    not contained in it.\<close>  
  definition "close_world M = M \<union> {\<^bold>\<not>(Atom atm) | atm. Atom atm \<notin> M}"
  
  lemma 
    close_world_extensive: "M \<subseteq> close_world M" and
    close_world_idem[simp]: "close_world (close_world M) = close_world M"
    by (auto simp: close_world_def)

  lemma in_close_world_conv: 
    "\<phi> \<in> close_world M \<longleftrightarrow> (\<phi>\<in>M \<or> (\<exists>atm. \<phi>=\<^bold>\<not>(Atom atm) \<and> Atom atm\<notin>M))"
    by (auto simp: close_world_def)
    
  lemma valuation_aux_1:
    fixes M :: world_model and \<phi> :: "object atom formula"
    defines "C \<equiv> close_world M"
    assumes A: "\<forall>\<phi>\<in>C. \<A> \<Turnstile> \<phi>"
    shows "\<A> = valuation M"
    using A unfolding C_def
    by (auto simp: in_close_world_conv valuation_def Ball_def intro!: ext)

  lemma valuation_aux_2: 
    assumes "\<forall>\<phi>\<in>M. is_Atom \<phi>"
    shows "(\<forall>G\<in>close_world M. valuation M \<Turnstile> G)"
    using assms
    by (force simp: in_close_world_conv valuation_def elim: is_Atom.elims) 
        
  lemma val_imp_close_world: "valuation M \<Turnstile> \<phi> \<Longrightarrow> close_world M \<TTurnstile> \<phi>"  
    unfolding entailment_def
    using valuation_aux_1
    by blast
    
  lemma close_world_imp_val: 
    "\<forall>\<phi>\<in>M. is_Atom \<phi> \<Longrightarrow> close_world M \<TTurnstile> \<phi> \<Longrightarrow> valuation M \<Turnstile> \<phi>"
    unfolding entailment_def using valuation_aux_2 by blast
    
  text \<open>Main theorem of this section: 
    If a world model \<open>M\<close> contains only atoms, its induced valuation 
    satisfies a formula \<open>\<phi>\<close> if and only if the closure of \<open>M\<close> entails \<open>\<phi>\<close>.
    
    Note that there are no syntactic restrictions on \<open>\<phi>\<close>, 
    in particular, \<open>\<phi>\<close> may contain negation.
  \<close>  
  theorem valuation_iff_close_world: 
    assumes "\<forall>\<phi>\<in>M. is_Atom \<phi>"
    shows "valuation M \<Turnstile> \<phi> \<longleftrightarrow> close_world M \<TTurnstile> \<phi>"
    using assms val_imp_close_world close_world_imp_val by blast


end -- \<open>Theory\<close>
