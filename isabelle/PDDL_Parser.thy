theory PDDL_Parser
imports
  Parser_Combinator
  PDDL_Semantics
begin    

subsection \<open>Lexical Matters\<close>  

  
definition "lx_comment \<equiv> exactly '';'' *-- repeat (tk_with_prop (op\<noteq>CHR ''\<newline>'')) --* exactly ''\<newline>''"
  
definition "lx_ws \<equiv> repeat (any char_wspace with (\<lambda>_. ()) \<parallel> lx_comment with (\<lambda>_. ()))"

abbreviation "token \<equiv> gen_token lx_ws"

(* PDDL is case insensitive, and benchmarks seem to actually exploit that!
  We convert everything to lowercase in the parser, such that we can use 
  standard equality in the semantics.
*)
abbreviation "lx_to_lower_alpha \<equiv> 
  lx_lowercase 
\<parallel> lx_uppercase with (\<lambda>c. char_of_nat ( nat_of_char c - nat_of_char CHR ''A'' + nat_of_char CHR ''a''))"
  
(* Identifiers also contain commas in some planning competition domains, we account for that here *)  
definition [consuming]: "lx_id \<equiv> 
  lx_to_lower_alpha --[op#] repeat (lx_to_lower_alpha \<parallel> lx_digit \<parallel> any ''_-,'')"
    
    
definition "tk_eoi \<equiv> token eoi"    
definition [consuming]: "tk_name \<equiv> token lx_id \<parallel> err_expecting_str ''identifier''"
definition [consuming]: "tk_cname \<equiv> token (exactly '':'' --[op@] lx_id) \<parallel> err_expecting_str '':identifier''"
definition [consuming]: "tk_vname \<equiv> token (exactly ''?'' --[op@] lx_id) \<parallel> err_expecting_str ''?identifier''" 
definition [consuming]: "tk_lparen \<equiv> token (exactly ''('')"  
definition [consuming]: "tk_rparen \<equiv> token (exactly '')'')"  
definition [consuming]: "tk_equals \<equiv> token (exactly ''='')"
definition [consuming]: "tk_dash \<equiv> token (exactly ''-'')"
  
definition [consuming]: "tk_this_name n \<equiv> do { x \<leftarrow> tk_name; if x=n then return () else err_expecting (shows ''Name '' o shows n)}"
definition [consuming]: "tk_this_cname n \<equiv> do { x \<leftarrow> tk_cname; if x=n then return () else err_expecting (shows ''CName '' o shows n)}"

abbreviation "in_paren p \<equiv> tk_lparen *-- p --* tk_rparen"
  
definition [consuming]: "parse_variable \<equiv> tk_vname with Var"  
definition [consuming]: "parse_predicate \<equiv> tk_name with Pred"
definition [consuming]: "parse_atom parse_val \<equiv> in_paren (parse_predicate -- repeat parse_val) with case_prod Atom"  
    
fun parse_prop where
  "parse_prop parse_val ::= 
    in_paren (tk_this_name ''and'' *-- repeat (parse_prop parse_val) with prop_and)
  \<parallel> in_paren (tk_equals *-- parse_val -- parse_val with case_prod prop_eq)
  \<parallel> in_paren (tk_this_name ''not'' *-- parse_prop parse_val with prop_not)
  \<parallel> (parse_atom parse_val with prop_atom)"
  
declare parse_prop.simps[simp del]
  
lemma [parser_rules]: "is_cparser (parse_prop parse_val)"
  apply (rule is_cparserI)
  apply (subst (asm) parse_prop.simps)
  apply auto
  done  

abbreviation "citem n p \<equiv> in_paren (tk_this_cname n *-- p)"
    
definition [consuming]: "parse_type \<equiv> 
    in_paren (tk_this_name ''either'' *-- repeat1 tk_name) with Either
  \<parallel> tk_name with (\<lambda>T. Either [T])"
  
definition "parse_opt_type \<equiv> optional ((Either [''object''])) (tk_dash *-- parse_type)"
    
definition "parse_typed_list px \<equiv> 
  repeat (repeat1 px -- parse_opt_type with (\<lambda>(xs,T). map (\<lambda>x. (x,T)) xs)) with concat"
    
  
definition "parse_type_decls \<equiv> optional [] (
  citem '':types'' (repeat (tk_name --* (tk_dash -- tk_this_name ''object'')? )))"
  
(*definition "parse_const_decls \<equiv> optional [] (
  citem '':constants'' (repeat (tk_name --* (tk_dash -- tk_this_name ''object'')? )))"*)
 

definition [consuming]: "parse_parameters \<equiv> tk_this_cname '':parameters'' *-- in_paren (parse_typed_list parse_variable)"
definition [consuming]: "parse_precondition \<equiv> tk_this_cname '':precondition'' *-- parse_prop parse_variable"
    
definition [consuming]: "parse_atomic_effect \<equiv> 
  in_paren (tk_this_name ''not'' *-- parse_atom parse_variable) with Del
\<parallel> parse_atom parse_variable with Add"
    

definition [consuming]: "parse_action_cost \<equiv> 
  in_paren (tk_this_name ''increase'' *-- in_paren (tk_this_name ''total-cost'') *-- repeat lx_digit)"

  
definition [consuming]: "parse_effect \<equiv> (
  tk_this_cname '':effect'' *-- (
      in_paren ( tk_this_name ''and'' *-- repeat (parse_atomic_effect))
    \<parallel> parse_atomic_effect with (\<lambda>x. [x]))
  ) with Effect"
                              
definition [consuming]: "parse_action_schema \<equiv> citem '':action'' ( 
    tk_name 
  -- optional [] parse_parameters   (* Some domains seem to omit parameters declaration if empty *)
  -- parse_precondition 
  -- parse_effect )
  with (\<lambda>(n,p,pre,e). Action_Schema n p pre e)" 
  
definition [consuming]: "parse_predicate_decl \<equiv> 
  in_paren ( tk_name -- parse_typed_list tk_vname ) with (\<lambda>(n,args). PredDecl (Pred n) (map snd args))"

definition [consuming]: "parse_predicates_decl \<equiv> citem '':predicates'' ( repeat parse_predicate_decl )"
  
definition [consuming]: "parse_domain_def \<equiv> in_paren ( tk_this_name ''domain'' *-- tk_name )"  
  
definition "parse_requirements \<equiv> 
  optional [] (citem '':requirements'' (repeat1 ( 
    tk_this_cname '':strips'' 
  \<parallel> tk_this_cname '':equality''
  \<parallel> tk_this_cname '':typing''
  \<parallel> tk_this_cname '':action-costs''
  (*\<parallel> tk_this_cname '':adl'' TODO: we need conditional effects and quantifiers!*) 
  )))"
  
definition [consuming]: "parse_domain \<equiv> in_paren ( 
     tk_this_name ''define'' 
  *-- parse_domain_def 
  *-- parse_requirements
  *-- parse_type_decls
(*  *-- parse_const_decls*)
  --  parse_predicates_decl 
  --  repeat parse_action_schema
  with (\<lambda>(types(*,consts*),preds,actions). Domain types (*consts*) preds actions)
)"
  
definition [consuming]: "parse_object \<equiv> tk_name with Obj"
definition [consuming]: "parse_fact \<equiv> parse_atom parse_object"
  
definition [consuming]: "parse_problem_def \<equiv> in_paren (tk_this_name ''problem'' *-- tk_name)"
definition [consuming]: "parse_domain_ref \<equiv> citem '':domain'' tk_name"
definition [consuming]: "parse_objects_decl \<equiv> citem '':objects'' (parse_typed_list parse_object)"  
definition [consuming]: "parse_init_spec \<equiv> citem '':init'' (repeat parse_fact)"
definition [consuming]: "parse_goal_spec \<equiv> citem '':goal'' (parse_prop parse_object)"
definition [consuming]: "parse_problem dmn \<equiv> in_paren ( do {
  tk_this_name ''define'';
  parse_problem_def;
  parse_domain_ref;
  objects \<leftarrow> optional [] parse_objects_decl; (* Some domains omit :objects if there are none *)    
  init \<leftarrow> parse_init_spec;
  goal \<leftarrow> parse_goal_spec;

  return (Problem dmn objects init goal)
})"
  
definition [consuming]: "parse_plan_action \<equiv> in_paren (tk_name -- repeat parse_object) with (\<lambda>(n,objs). PAction n objs)"
definition parse_plan :: "(_,plan) parser" where "parse_plan \<equiv> repeat parse_plan_action"
  
thm parse_plan_action_def[unfolded monad_laws]

definition "parse_domain_file \<equiv> parse_all lx_ws parse_domain"
definition "parse_problem_file dmn \<equiv> parse_all lx_ws (parse_problem dmn)"
definition "parse_plan_file \<equiv> parse_all lx_ws parse_plan"
  
definition parse_domain_and_problem :: "String.literal \<Rightarrow> String.literal \<Rightarrow> (unit \<Rightarrow> shows) + ast_problem"
  where "parse_domain_and_problem d p \<equiv> do {
  dmn \<leftarrow> parse_domain_file d <+? (\<lambda>e _. shows ''Error parsing domain: '' o e ());
  parse_problem_file dmn p <+? (\<lambda>e _. shows ''Error parsing problem: '' o e ())
}"
  
  
    
definition "test1 = parse_all lx_ws parse_effect (STR ''
  :effect (calibrated ?x)

'') <+? (\<lambda>s (_::unit). String.implode (s () ''''))"
    
ML_val \<open>
  @{code test1}

\<close>    
  
end  
  
  
