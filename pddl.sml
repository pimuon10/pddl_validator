(* This is a demo example of a simple grammar for receipts.

   Consider the following EBNF:
     sas_prob ::= version 0
*)

  fun fst (x,y) = x
  fun snd (x,y) = y


structure PDDL =
(* An implementation that uses token parser. *)
struct

  open ParserCombinators
  open CharParser
  open PDDL_Checker_Exported

  infixr 4 << >>
  infixr 3 &&
  infix  2 -- ##
  infix  2 wth suchthat return guard when
  infixr 1 || <|> ??

  structure PDDLDef :> LANGUAGE_DEF =
  struct

    type scanner = char CharParser.charParser
    val commentStart   = NONE
    val commentEnd     = NONE
    val commentLine    = SOME ";"
    val nestedComments = false

    val identLetter    = alphaNum <|> oneOf (String.explode "_-,:;=") (*Idents can be separated with " " or \n and can contain [Aa-Zz], [0-9], "-", "_"*)
    val identStart     = identLetter
    val opStart        = fail "Operators not supported" : scanner
    val opLetter       = opStart
    val reservedNames  = [":requirements", ":strips", ":equality", ":typing", ":action-costs", 
                          "define", "domain",
                          ":predicates", "either", ":functions",
                          ":types", "object",
                          ":constants",
                          ":action", ":parameters", ":precondition", ":effect", "-",
                          ":invariant", ":name", ":vars", ":set-constraint", 
                          "=", "and", "or", "not", "number", 
                          "increase", "total-cost",
                          "problem", ":domain", ":init", ":objects", ":goal", ":metric", "maximize", "minimize"]
    val reservedOpNames= []
    val caseSensitive  = false

  end

  val lineComment   =
	let fun comLine _  = newLine <|> done #"\n" <|> (anyChar >> $ comLine)
	in case PDDLDef.commentLine of
	       SOME s => string s >> $ comLine return ()
	     | NONE   => fail "Single-line comments not supported"
	end
  val mlComment      =
	case (PDDLDef.commentStart, PDDLDef.commentEnd) of
	    (SOME st, SOME ed) =>
	    let
		fun bcNest _   = try (string st) >> $contNest
		and contNest _ = try (string ed return ())
                                 <|> ($bcNest <|> (anyChar return ())) >> $contNest
		val bcU = try (string st) >> repeat (not (string ed) >> anyChar) >> string ed return ()
	    in if PDDLDef.nestedComments then $ bcNest else bcU
	    end
	  | _ => fail "Multi-line comments not supported"
  val comment        = lineComment <|> mlComment

  fun stringToString s = "''" ^ s ^ "''" 

  fun stringListToStringList ss = (String.concatWith ", ") (map stringToString ss)

  fun stringListToIsabelle ss = (map String.explode ss)


  type PDDL_VAR = string

  fun pddlVarToString v = "Var " ^ stringToString v

  fun pddlVarToIsabelle v = Var (String.explode v)

  fun pddlObjToString v = "Obj " ^ stringToString v

  fun pddlObjToIsabelle v = Obj (String.explode v)

  type PDDL_PRIM_TYPE = string

  type PDDL_TYPE = PDDL_PRIM_TYPE list

  (* fun pddlTypeToString (type_ :PDDL_TYPE) = "\n  Type is either:\n   " ^ ((String.concatWith "\n   ") type_); *)
  fun pddlTypeToString (type_ :PDDL_TYPE) = "Either([" ^ stringListToStringList type_ ^ "])";

  fun pddlTypeToIsabelle (type_ :PDDL_TYPE) = Either (stringListToIsabelle type_)

  type 'a PDDL_TYPED_LIST = (('a list) * PDDL_TYPE) list

  (* fun pddlTypedListToString (typedList :string PDDL_TYPED_LIST) = (String.concatWith "\n") (map (fn (vars, type_) => "\n" ^ ((String.concatWith "\n") vars) ^ (pddlTypeToString type_)) typedList); *)

  fun pddlTypedListVarsTypesToString (typedList :string PDDL_TYPED_LIST) =
                  "[" ^ (String.concatWith ", ") 
                           (map (fn (vars, type_) =>
                                    ((String.concatWith ", ") 
                                          (map (fn v => 
                                                   "(" ^ (pddlVarToString v) ^ "," ^
                                                         (pddlTypeToString type_) ^ ")")
                                               vars)))
                                typedList) ^ "]";

  fun pddlTypedListObjsTypesToString (typedList :string PDDL_TYPED_LIST) =
                  "[" ^ (String.concatWith ", ") 
                           (map (fn (objs, type_) =>
                                    ((String.concatWith ", ") 
                                          (map (fn obj => 
                                                   "(" ^ (pddlObjToString obj) ^ "," ^
                                                         (pddlTypeToString type_) ^ ")")
                                               objs)))
                                typedList) ^ "]";


  fun pddlTypedListVarsTypesToIsabelle (typedList :string PDDL_TYPED_LIST) =
              List.concat (map (fn (vars, type_) =>
                                    (map (fn v =>
                                           ((pddlVarToIsabelle v),
                                            (pddlTypeToIsabelle type_)))
                                       vars))
                                typedList);

  fun pddlTypedListObjsTypesToIsabelle (typedList :string PDDL_TYPED_LIST) =
              List.concat (map (fn (objs, type_) =>
                                    (map (fn obj =>
                                           ((pddlObjToIsabelle obj),
                                            (pddlTypeToIsabelle type_)))
                                       objs))
                                typedList);

  fun pddlTypedListTypesToString (typedList :string PDDL_TYPED_LIST) =
            "[" ^ (String.concatWith ", ")
                            (map (fn (vars, type_) => 
                                     ((String.concatWith ", ")
                                           (map (fn _ =>
                                                    (pddlTypeToString type_)) vars)))
                                 typedList) ^ "]";

  fun pddlTypedListTypesToIsabelle (typedList :string PDDL_TYPED_LIST) =
                            map (fn (vars, type_) => 
                                     (
                                           (map (fn _ =>
                                                    (pddlTypeToIsabelle type_)) vars)))
                                 typedList;

  (* fun extractFlatTypedList (typedList :string PDDL_TYPED_LIST) = "''" ^ (String.concatWith "'', ''") (map ((String.concatWith "'', ''") o fst) typedList) ^ "''"; *)

  fun extractFlatTypedList (typedList :string PDDL_TYPED_LIST) = (String.concatWith ", ") (map (stringListToStringList o fst) typedList);

  fun extractFlatTypedListIsabelle (typedList :string PDDL_TYPED_LIST) = List.concat (map (stringListToIsabelle o fst) typedList);

  type PDDL_TYPES_DEF = (PDDL_PRIM_TYPE PDDL_TYPED_LIST) list option
  
  fun pddlTypesDefToString (typesDefOPT :PDDL_TYPES_DEF) =
                   (* This is for debugging *)
                   (* case typesDefOPT of  *)
                   (*      SOME typesDef => *)
                   (*           ("Types in the domain:\r\n" ^ (String.concatWith "\n") (map pddlTypedListToString typesDef)) *)
                   (*    | _ => "" *)
                   case typesDefOPT of
                        SOME typesDef =>
                             ("definition \"dom_types = [" ^ (String.concatWith ", ") (map extractFlatTypedList typesDef) ^ "]\"\n")
                      | _ => "definition \"dom_types = []\"\n"

  fun pddlTypesDefToIsabelle (typesDefOPT :PDDL_TYPES_DEF) =
                   case typesDefOPT of
                        SOME typesDef =>
                             List.concat (map extractFlatTypedListIsabelle typesDef)
                      | _ => []


  (* fun pddlTypeToString (type_ :PDDL_TYPE) = "\n Either([''" ^ ((String.concatWith "'', ") type_) ^"''])"; *)
  
  type PDDL_CONSTS_DEF = (string PDDL_TYPED_LIST) list option
  
  fun pddlConstsDefToString (constsDefOPT :PDDL_CONSTS_DEF) =
                   case constsDefOPT of 
                        SOME constsDef =>
                             ("Constants in the domain:\r\n" ^ (String.concatWith "\n") (map pddlTypedListTypesToString constsDef))
                      | _ => ""

  fun pddlConstsDefToIsabelle (constsDefOPT :PDDL_CONSTS_DEF) =
                   case constsDefOPT of 
                        SOME constsDef =>
                             (map pddlTypedListTypesToIsabelle constsDef)
                      | _ => []

                      
  type PDDL_PRED = string * (PDDL_VAR PDDL_TYPED_LIST)
  
  (* fun pddlPredToString (pred_name, pred_args) = "Predicate Name: " ^ pred_name  ^ "\n Its arguments are: " ^ (pddlTypedListToString pred_args) *)

  fun pddlPredToString (pred_name, pred_args) = "PredDecl ( Pred (" ^ stringToString pred_name  ^ ")) (" ^ (pddlTypedListTypesToString pred_args) ^ ")"

  fun pddlPredToIsabelle (pred_name, pred_args) = PredDecl ((Pred(String.explode pred_name)), List.concat (pddlTypedListTypesToIsabelle pred_args))
  
  type PDDL_PRED_DEF = PDDL_PRED list option
  
  fun pddlPredDefToString pred_defOPT =
                   (* case pred_defOPT of  *)
                   (*      SOME pred_def => *)
                   (*            "Predicates are: " ^ ((String.concatWith "\n   ") (map pddlPredToString pred_def)) *)
                   (*      | _ => ""                      *)
                   case pred_defOPT of 
                        SOME pred_def =>
                              "definition \"dom_predicates = [(" ^ ((String.concatWith "),\n (") (map pddlPredToString pred_def)) ^ ")]\"\n"
                        | _ => "definition \"dom_predicates=[]\"\n"

  fun pddlPredDefToIsabelle pred_defOPT =
                   case pred_defOPT of 
                        SOME pred_def =>
                              (map pddlPredToIsabelle pred_def)
                        | _ => []
  
  type PDDL_REQUIRE_DEF = (unit list) option

  (*fun pddlReqDefToString req_def = "Requirements are: " ^ ((String.concatWith "\n   ") req_def) *)
  
  type 'a PDDL_ATOM = 'a PDDL_Checker_Exported.atom; (*string * ('a list) *)

  fun pddlEqToSrtingVar (var1, var2) = "atom.Eq (" ^ pddlVarToString var1 ^ ") ("  ^ pddlVarToString var2 ^ ")"

  fun pddlEqToIsabelleVar (var1, var2) = Eqa (pddlVarToIsabelle var1, pddlVarToIsabelle var2 )

  fun pddlEqToSrtingObj (obj1, obj2) = "atom.Eq (" ^ pddlObjToString obj1 ^ ") ("  ^ pddlObjToString obj2 ^ ")"

  fun pddlEqToIsabelleObj (obj1, obj2) = Eqa (pddlObjToIsabelle obj1, pddlObjToIsabelle obj2)

  fun pddlAtomToStringVar atm =
   case atm of PredAtm (Pred pred_name, vars_list) => 
      "predAtm (Pred (" ^ stringToString (String.implode pred_name) ^ "))([" ^ (String.concatWith "," (map pddlVarToString vars_list)) ^ "])"
              | (PDDL_Checker_Exported.Eqa eqtm) => pddlEqToSrtingVar eqtm

  fun pddlAtomToStringObj atm =
   case atm of (PredAtm (Pred pred_name, vars_list)) => 
      "predAtm (Pred (" ^ stringToString (String.implode pred_name) ^ "))([" ^ (String.concatWith "," (map pddlObjToString vars_list)) ^ "])"
              | (PDDL_Checker_Exported.Eqa eqtm) => pddlEqToSrtingObj eqtm
 
  datatype 'a PDDL_PROP = Prop_atom of  'a PDDL_ATOM |
    Prop_not of 'a PDDL_PROP | Prop_and of 'a PDDL_PROP list | Prop_or of 'a PDDL_PROP list | Fluent (*This is mainly to parse and ignore action costs*) ;

  fun pddlFormulaToASTPropStringVar phi = 
      case phi of Prop_atom(atom : string PDDL_ATOM) => ("formula.Atom (" ^ pddlAtomToStringVar atom ^ ")")
                 | Prop_not(prop: string PDDL_PROP) => ("formula.Not (" ^ pddlFormulaToASTPropStringVar prop ^ ")")
                 | Prop_and(propList: string PDDL_PROP list) => ("BigAnd [" ^ (String.concatWith ", " (List.filter (fn x => size x > 0 ) (map pddlFormulaToASTPropStringVar propList))) ^ "]")
                 | Prop_or(propList: string PDDL_PROP list) => ("BigOr [" ^ (String.concatWith ", " (List.filter (fn x => size x > 0 ) (map pddlFormulaToASTPropStringVar propList))) ^ "]")
                 | _ => ""

  fun strToVarAtom atom = map_atom (fn x => Var (String.explode x)) atom 

  fun pddlFormulaToASTPropIsabelleVar phi = 
      case phi of Prop_atom(atom : string PDDL_ATOM) =>  Atom (strToVarAtom atom)
                 | Prop_not(prop: string PDDL_PROP) =>  Not (pddlFormulaToASTPropIsabelleVar prop)
                 | Prop_and(propList: string PDDL_PROP list) => bigAnd (map pddlFormulaToASTPropIsabelleVar propList)
                 | Prop_or(propList: string PDDL_PROP list) => bigOr (map pddlFormulaToASTPropIsabelleVar propList)
                 | _ => Bot (*Fluents shall invalidate the problem*)

  fun pddlFormulaToASTPropStringObj phi = 
      case phi of Prop_atom(atom : string PDDL_ATOM) => ("formula.Atom (" ^ pddlAtomToStringObj atom ^ ")")
                 | Prop_not(prop: string PDDL_PROP) => ("formula.Not (" ^ pddlFormulaToASTPropStringObj prop ^ ")")
                 | Prop_and(propList: string PDDL_PROP list) => ("BigAnd [" ^ (String.concatWith ", " (List.filter (fn x => size x > 0 ) (map pddlFormulaToASTPropStringObj propList))) ^ "]")
                 | Prop_or(propList: string PDDL_PROP list) => ("BigOr [" ^ (String.concatWith ", " (List.filter (fn x => size x > 0 ) (map pddlFormulaToASTPropStringObj propList))) ^ "]")
                 | _ => ""

  fun strToObjAtom atom = map_atom (fn x => Obj (String.explode x)) atom

  fun pddlFormulaToASTPropIsabelleObj phi = 
      case phi of Prop_atom(atom : string PDDL_ATOM) =>  Atom (strToObjAtom atom)
                 | Prop_not(prop: string PDDL_PROP) =>  Not (pddlFormulaToASTPropIsabelleObj prop)
                 | Prop_and(propList: string PDDL_PROP list) => bigAnd (map pddlFormulaToASTPropIsabelleObj propList)
                 | Prop_or(propList: string PDDL_PROP list) => bigOr (map pddlFormulaToASTPropIsabelleObj propList)
                 | _ => Bot

  type 'a PDDL_PRE_GD = 'a PDDL_PROP option 

  fun pddlPreGDToString PreGD = 
      case PreGD of SOME (prop: string PDDL_PROP) => pddlFormulaToASTPropStringVar prop
                 | _ => ""

  fun pddlPreGDToIsabelle PreGD = 
      case PreGD of SOME (prop: string PDDL_PROP) => pddlFormulaToASTPropIsabelleVar prop
                 | _ => Not Bot (*If we have no precondition, then it is a tautology*)
  
  type C_EFFECT = string PDDL_PROP option 

  fun addEffToString atom = "(" ^ pddlAtomToStringVar atom ^ ")"

  fun delEffToString atom = "(" ^ pddlAtomToStringVar atom ^ ")"

  fun isProp_atom fmla = case fmla of Prop_atom(atom) => true | _ => false
  fun isNegProp_atom fmla = case fmla of Prop_not(Prop_atom(atom)) => true | _ => false

  fun pddlPropToASTEffString one_eff Prop = 
      case Prop of Prop_atom(atom : string PDDL_ATOM) => (if one_eff then "[" ^ (pddlFormulaToASTPropStringVar (Prop_atom (atom))) ^ "][]"
                                                                     else (pddlFormulaToASTPropStringVar (Prop_atom (atom))))
                 | Prop_not(Prop_atom (atom: string PDDL_ATOM)) => (if one_eff then "[][" ^ (pddlFormulaToASTPropStringVar (Prop_atom (atom))) ^ "]"
                                                                               else (pddlFormulaToASTPropStringVar (Prop_atom (atom))))
                 | Prop_and(propList: string PDDL_PROP list) 
                     => (("[" ^ String.concatWith ", "
                            (List.filter 
                               (fn x => size x > 0 )
                               (map (pddlPropToASTEffString false)
                                    (List.filter isProp_atom propList))) ^ "]") ^ 
                          "[" ^ String.concatWith ", "
                            (List.filter 
                               (fn x => size x > 0 )
                               (map (pddlPropToASTEffString false)
                                    (List.filter isNegProp_atom propList))) ^ "]")
                 | _ => ""

  fun pddlPropToASTEffIsabelle Prop = 
      case Prop of Prop_atom(atom : string PDDL_ATOM) => ([Atom (strToVarAtom atom)],[])
                 | Prop_not(Prop_atom (atom: string PDDL_ATOM)) => ([],[Atom (strToVarAtom atom)])
                 | Prop_and(propList: string PDDL_PROP list) 
                     => ((map (fn atm => case atm of Prop_atom(atom : string PDDL_ATOM) => Atom (strToVarAtom atom))
                                    (List.filter isProp_atom propList)),
                         (map (fn neg_atm => case neg_atm of Prop_not(Prop_atom(atom : string PDDL_ATOM)) => Atom (strToVarAtom atom)))
                                    (List.filter isNegProp_atom propList))
                 | _ => ([], [])

  fun pddlCEffectToString CEff = 
      case CEff of SOME (prop: string PDDL_PROP) => "Effect " ^ (pddlPropToASTEffString true prop)
                 | _ => "Effect [] []"

  fun pddlCEffectToIsabelle CEff = 
      case CEff of SOME (prop: string PDDL_PROP) => Effect (pddlPropToASTEffIsabelle prop)
                 | _ => Effect ([],[])
  

  type PDDL_ACTION_DEF_BODY = ((unit * (string PDDL_PRE_GD)) option) * ((unit * C_EFFECT) option)

  fun actDefBodyPreToString pre = case pre of SOME (u, pre: string PDDL_PRE_GD) => pddlPreGDToString pre
                                            | _ => ""

  fun actDefBodyPreToIsabelle pre = case pre of SOME (u, pre: string PDDL_PRE_GD) => pddlPreGDToIsabelle pre
                                            | _ => Not Bot

  fun actDefBodyEffToString eff = case eff of SOME (u, eff: C_EFFECT) => pddlCEffectToString eff
                                            | _ => ""

  fun actDefBodyEffToIsabelle eff = case eff of SOME (u, eff: C_EFFECT) => pddlCEffectToIsabelle eff
                                            | _ => Effect ([],[])

  fun pddlActDefBodyToString (pre, eff) = "(" ^ (actDefBodyPreToString pre) ^ ")\n(" ^ (actDefBodyEffToString eff) ^ ")"

  fun pddlActDefBodyToIsabelle (pre, eff) = ((actDefBodyPreToIsabelle pre), (actDefBodyEffToIsabelle eff))

  type PDDL_ACTION_SYMBOL = string

  type PDDL_ACTION = PDDL_ACTION_SYMBOL * 
                          (PDDL_VAR PDDL_TYPED_LIST *
                                     (PDDL_ACTION_DEF_BODY)) 

  fun pddlIsabelleActName actName = implode (map (fn c => if c = #"-" then #"_" else c) (explode actName))

  fun args_n n sep = case n of 0 => ""
                       | 1 => "arg" ^ Int.toString n ^ (args_n (n - 1) sep)
                       | _ => "arg" ^ Int.toString n ^ (implode [sep]) ^ (args_n (n - 1) sep)

  fun get_action_args_num args = (foldr (op +) 0 (map (length o fst) args))

  fun prove_invariant_for_action (actName, args, invariant_name) =
"lemma " ^ pddlIsabelleActName invariant_name ^ "_invariant_" ^ pddlIsabelleActName actName ^ ":\n\
  \assumes \"list_all2 (ast_problem.is_obj_of_type PI) args (map snd (parameters  " ^ pddlIsabelleActName actName ^ "))\"\n\
\  shows \"ast_problem.invariant_act " ^ pddlIsabelleActName invariant_name ^ " (ast_domain.instantiate_action_schema  " ^ pddlIsabelleActName actName ^ " args)\"\n\
\  unfolding ast_problem.invariant_act_def ast_domain.execute_ast_action_inst_def\n\
\proof(safe)\n\
\  fix s assume ass: \"" ^ pddlIsabelleActName invariant_name ^ " s\" \"ast_problem.ast_action_inst_enabled (ast_domain.instantiate_action_schema  " ^ pddlIsabelleActName actName ^ " args) s\"\n\
\  obtain " ^ args_n (get_action_args_num args) #" " ^ " where args_" ^ Int.toString (get_action_args_num args) ^ ": \"args = [" ^ args_n (get_action_args_num args) #"," ^ "]\"\n\
\    using assms\n\
\    unfolding  " ^ pddlIsabelleActName actName ^ "_def\n\
\    apply auto\n\
\    using list_len_" ^ Int.toString (get_action_args_num args) ^" list_all2_lengthD\n\
\    by metis\n\
\  show \"" ^ pddlIsabelleActName invariant_name ^ "(ast_domain.apply_effect (ast_action_inst.effect (ast_domain.instantiate_action_schema  " ^ pddlIsabelleActName actName ^ " args)) s)\"\n\
\    using ass\n\
\    unfolding " ^ pddlIsabelleActName invariant_name ^ "_def  " ^ pddlIsabelleActName actName ^ "_def\n\
\    apply(auto simp add: args_" ^ Int.toString (get_action_args_num args) ^ ")\n\
\        by (auto simp add: ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_problem.ast_action_inst_enabled_def entailment_def ast_problem.holds_def valuation_def)\n\
\qed\n"

(* \    using ast_domain.instantiate_action_schema.simps ast_domain.apply_effect.simps ast_domain.holds.simps ast_domain.apply_atomic.simps\n\ *)
(* \    by auto\n\ *)

  fun pddlActToString (actName, (args, defBody)) =
      "definition \"" ^ pddlIsabelleActName actName ^
      " = Action_Schema(''" ^ actName ^ "'')\n " ^ pddlTypedListVarsTypesToString args ^
      "\n" ^ pddlActDefBodyToString defBody ^ "\"\n\n"
 
  fun pddlActToIsabelle (actName, (args, defBody)) =
      Action_Schema(String.explode actName,
                    pddlTypedListVarsTypesToIsabelle args,
                    fst (pddlActDefBodyToIsabelle defBody),
                    snd (pddlActDefBodyToIsabelle defBody))
 
  type PDDL_ACTIONS_DEF = (PDDL_ACTION list)

  fun pddlActionsDefToString (actsDef : PDDL_ACTION list) =
                    (String.concatWith "\n\n") (map pddlActToString actsDef) ^
                    "\ndefinition \"dom_actions = [" ^ 
                       (String.concatWith ", ") (map (pddlIsabelleActName o fst) actsDef) ^
                     "]\"\n\n"

  fun pddlActionsDefToIsabelle (actsDef : PDDL_ACTION list) =
                    (map pddlActToIsabelle actsDef)

  type 'a FUN_TYPED_LIST = (('a list) * unit) list

  type ATOMIC_FUN_SKELETON = string * (PDDL_VAR PDDL_TYPED_LIST)

  type PDDL_FUNS_DEF = ATOMIC_FUN_SKELETON FUN_TYPED_LIST option

  type CONSTRAINT_BODY = string PDDL_PROP 

  type CONSTRAINT = string * (PDDL_VAR list * (CONSTRAINT_BODY))

  fun constraintToString (constraintName, (vars, constraintBody)) =
       "definition \"" ^ pddlIsabelleActName constraintName ^
       " = (%s. (ast_problem.holds s (" ^ (pddlFormulaToASTPropStringObj constraintBody) ^ ")))\"\n"

  type CONSTRAINTS_DEF = CONSTRAINT list

  fun constraintsDefToString constraints = (String.concatWith "\n\n") (map constraintToString constraints)

  type PDDL_DOM = PDDL_REQUIRE_DEF *
                      (PDDL_TYPES_DEF *
                            (PDDL_CONSTS_DEF *
                                (PDDL_PRED_DEF * 
                                    (PDDL_FUNS_DEF * 
                                          (PDDL_ACTIONS_DEF * CONSTRAINTS_DEF)))))


(* fun prove_action_names_distinct actsDef =  *)
(* "lemma distinct_act_names:\ *)
(* \      shows \"distinct (map ast_action_schema.name (dom_actions))\"\n\ *)
(* \  unfolding dom_types_def dom_predicates_def dom_actions_def ast_domain.wf_domain_def\n" ^ *)
(*                (String.concatWith " ") (map ((fn name => pddlIsabelleActName name ^ "_def") o fst) actsDef) *)
(*             (* begin_cut_def continue_cut_def end_cut_def begin_transpose_splice_def continue_splice_def end_splice_def begin_transverse_splice_def begin_inverse_splice_def begin_inverse_splice_special_case_def continue_inverse_splice_A_def continue_inverse_splice_B_def end_inverse_splice_A_def end_inverse_splice_B_def reset_1_def*) *)
(*  ^ "\n\ *)
(* \  by (auto simp add: ast_domain.wf_predicate_decl.simps ast_domain.wf_type.simps\n\ *)
(* \                      ast_domain.wf_action_schema.simps ast_domain.wf_effect.simps\n\ *)
(* \                     ast_domain.wf_atom.simps ast_domain.sig_def\n\ *)
(* \                    ast_domain.is_of_type_def ast_domain.of_type_def)\n\ *)
(* \\n\ *)
(* \definition \"prob_dom = Domain dom_types dom_predicates dom_actions\"\n\n\ *)
(* \lemma wf_prob_dom:      shows \"ast_domain.wf_domain prob_dom\"\n\ *)
(* \  unfolding dom_types_def dom_predicates_def dom_actions_def ast_domain.wf_domain_def ast_domain.wf_formula.simps prob_dom_def\n" ^ *)
(*                (String.concatWith " ") (map ((fn name => pddlIsabelleActName name ^ "_def") o fst) actsDef) ^ *)
(* "\n\ *)
(* \  by (auto simp add: ast_domain.wf_predicate_decl.simps ast_domain.wf_type.simps\n\ *)
(* \                      ast_domain.wf_action_schema.simps ast_domain.wf_effect.simps ast_domain.wf_formula.simps\n\ *)
(* \                     ast_domain.wf_atom.simps ast_domain.sig_def ast_domain.wf_formula_atom_def\n\ *)
(* \                    ast_domain.is_of_type_def ast_domain.of_type_def)\n\ *)
(* \\n" *)

fun prove_action_names_distinct actsDef = 
"lemma distinct_act_names:\
\      shows \"distinct (map ast_action_schema.name (dom_actions))\"\n\
\  unfolding dom_types_def dom_predicates_def dom_actions_def ast_domain.wf_domain_def\n" ^
               (String.concatWith " ") (map ((fn name => pddlIsabelleActName name ^ "_def") o fst) actsDef)
            (* begin_cut_def continue_cut_def end_cut_def begin_transpose_splice_def continue_splice_def end_splice_def begin_transverse_splice_def begin_inverse_splice_def begin_inverse_splice_special_case_def continue_inverse_splice_A_def continue_inverse_splice_B_def end_inverse_splice_A_def end_inverse_splice_B_def reset_1_def*)
 ^ "\n\
\  by (auto simp add: ast_domain.wf_predicate_decl.simps ast_domain.wf_type.simps\n\
\                      ast_domain.wf_action_schema.simps ast_domain.wf_effect.simps\n\
\                     ast_domain.wf_atom.simps ast_domain.sig_def\n\
\                    ast_domain.is_of_type_def ast_domain.of_type_def)\n\
\\n\
\definition \"prob_dom = Domain dom_types dom_predicates dom_actions\"\n\n"


fun prove_invariant_for_plans actions_def constraint =
"lemma " ^ pddlIsabelleActName (fst constraint) ^ "_for_prob_dom:\n\
\  assumes \"PI = (Problem (prob_dom) (obj) (I) (G))\"\n\
\  shows \"ast_problem.invariant_wf_plan_act_seq PI " ^ pddlIsabelleActName (fst constraint) ^ " as\"\n\
\  apply(rule ast_problem.invariant_for_plan_act_seq)\n\
\  apply(rule ast_problem.invariant_action_insts_imp_invariant_plan_actions[where ?Q = "^ pddlIsabelleActName (fst constraint) ^ "])\n\
\  using ast_problem.invariant_for_plan_act_seq assms distinct_act_names\n" ^
((String.concatWith " ") (map (fn (actionName, _) => (pddlIsabelleActName (fst constraint) ^ "_invariant_" ^ (pddlIsabelleActName actionName))) actions_def)) ^ "\n\
\    unfolding prob_dom_def dom_actions_def ast_problem.action_params_match_def\n" ^
((String.concatWith " ") (map (fn (actionName, _) => ((pddlIsabelleActName actionName) ^ "_def")) actions_def)) ^ "\n\
\  by auto\n"

  fun prove_invariants actions_def constraints_def = 
             (String.concatWith "\n\n")
                  (map (fn constraint =>
                          (String.concatWith "\n\n")
                            (map (fn (actName, (args, body)) =>
                                   prove_invariant_for_action(actName, args, fst constraint))
                                        actions_def) ^
                           prove_invariant_for_plans actions_def constraint) constraints_def)

  fun pddlDomToString (reqs:PDDL_REQUIRE_DEF,
                         (types_def,
                            (consts_def,
                               (pred_def,
                                   (fun_def,
                                       (actions_def,
                                          constraints_def))))))
                      = "theory prob_defs\n" ^
                        "imports Main PDDL_STRIPS_Checker invariant_verification\n begin\n" ^
                        (pddlTypesDefToString types_def) ^
                        (pddlConstsDefToString consts_def) ^
                        (pddlPredDefToString pred_def) ^
                        (pddlActionsDefToString actions_def) ^
                        prove_action_names_distinct actions_def ^
                        (constraintsDefToString constraints_def) ^
                        (prove_invariants actions_def constraints_def) ^ "\nend\n"

  fun pddlDomToIsabelle (reqs:PDDL_REQUIRE_DEF,
                         (types_def,
                            (consts_def,
                               (pred_def,
                                   (fun_def,
                                       (actions_def,
                                          constraints_def))))))
                      = Domain
                       ((pddlTypesDefToIsabelle types_def),
                        (pddlPredDefToIsabelle pred_def),
                        (pddlActionsDefToIsabelle actions_def))

  type PDDL_OBJ_DEF = string PDDL_TYPED_LIST

  fun objDefToString (objs:PDDL_OBJ_DEF) = "definition \"objs = " ^ pddlTypedListObjsTypesToString objs ^ "\"\n"

  fun objDefToIsabelle (objs:PDDL_OBJ_DEF) = pddlTypedListObjsTypesToIsabelle objs

  type PDDL_INIT_EL = string PDDL_PROP

  fun initElToString (init_el:PDDL_INIT_EL) = pddlFormulaToASTPropStringObj init_el

  fun isntFluent x = (case x of Fluent => false | _ => true)

  fun isntTautology x = (case x of Not Bot => false | _ => true)

  fun initElToIsabelle (init_el:PDDL_INIT_EL) = pddlFormulaToASTPropIsabelleObj (init_el)

  type PDDL_INIT = PDDL_INIT_EL list

  fun pddlInitToStringWithObjEqs (init:PDDL_INIT) (objs) = 
      "definition \"init_state = [" ^ String.concatWith ", " (map initElToString (List.filter isntFluent init)) ^ ", " ^
           String.concatWith ", "  (map (fn obj => "formula.Atom (" ^ (pddlEqToSrtingObj (obj, obj)) ^ ") ") objs) ^  "]\"\n"

  fun pddlInitToString (init:PDDL_INIT) (objs) = 
      "definition \"init_state = [" ^ String.concatWith ", " (map initElToString (List.filter isntFluent init)) ^  "]\"\n"

  fun pddlInitToIsabelleWithObjEqs (init:PDDL_INIT) objs = (map initElToIsabelle (List.filter isntFluent init)) @ (*I don't want fluents in the init state. This is usually an init value for the plan-cost.*)
                                                 (map (fn obj => Atom (pddlEqToIsabelleObj (obj, obj))) objs)

  fun pddlInitToIsabelle (init:PDDL_INIT) objs = (map initElToIsabelle (List.filter isntFluent init)) (*I don't want fluents in the init state. This is usually an init value for the plan-cost.*)

  type PDDL_GOAL  = string PDDL_PROP

  fun pddlGoalToString (goal:PDDL_GOAL) = "definition \"goals = " ^ pddlFormulaToASTPropStringObj goal ^ "\"\n"

  fun pddlGoalToIsabelle (goal:PDDL_GOAL) = pddlFormulaToASTPropIsabelleObj goal

  type METRIC = string option

  type PDDL_PROB = PDDL_REQUIRE_DEF * (PDDL_OBJ_DEF *(PDDL_INIT * (PDDL_GOAL * METRIC)))

  fun pddlProbToString (reqs:PDDL_REQUIRE_DEF,
                          (objs:PDDL_OBJ_DEF,
                              (init:(string PDDL_PROP list),
                                (goal_form:string PDDL_PROP,
                                   metric)))) = 
                                                            objDefToString objs ^ "\n" ^
                                                           (pddlInitToString init (List.concat (map #1 objs))) ^ "\n" ^
                                                            pddlGoalToString goal_form ^ "\n"
                                                            
  fun pddlProbToIsabelle (reqs:PDDL_REQUIRE_DEF,
                          (objs:PDDL_OBJ_DEF,
                              (init:(string PDDL_PROP list),
                                (goal_form:string PDDL_PROP,
                                   metric)))) = 
                                                    (objDefToIsabelle objs,
                                                    (pddlInitToIsabelle init (List.concat (map #1 objs))),
                                                     pddlGoalToIsabelle goal_form)

  type PDDL_PLAN_ACTION = string * (string list)

  fun planActionToString (act_name, args) = "PAction ''" ^ act_name ^ "'' [" ^ (String.concatWith ", " (map pddlObjToString args)) ^ "]\r\n"

  fun planActionToIsabelle (act_name, args) = PAction(String.explode act_name, map pddlObjToIsabelle args)

  type PDDL_PLAN = PDDL_PLAN_ACTION list

  fun planToString plan = "definition \"plan = [" ^ (String.concatWith ", " (map planActionToString plan)) ^ "]\"\n"

  fun planToIsabelle plan = map planActionToIsabelle plan

  structure RTP = TokenParser (PDDLDef)
  open RTP

  val num = (lexeme ((char #"-" || digit) && (repeat digit)) when
	      (fn (x,xs) => Int.fromString (String.implode (x::xs)))) ?? "num expression"

  val lparen = (char #"(" ) ?? "lparen"
  val rparen = (char #")" ) ?? "rparen"

  val spaces_comm = repeatSkip (space wth (fn _ => ())|| comment)

  fun in_paren p = spaces_comm >> lparen >> spaces_comm >> p << spaces_comm << rparen << spaces_comm 

  val pddl_name = identifier ?? "pddl identifier" (*First char should be a letter*)

  fun pddl_reserved wrd = (reserved wrd) ?? "resereved word"
 
  val require_key = (pddl_reserved ":strips" || pddl_reserved ":equality" ||  pddl_reserved ":typing" ||  pddl_reserved ":action-costs") ?? "require_key"
  val require_def = (in_paren(pddl_reserved ":requirements" >> repeat1 require_key)) ?? "require_def"

  val primitive_type = (pddl_name || (pddl_reserved "object") wth (fn _ => "object")) ?? "prim_type"

  val type_ = ((pddl_reserved "either" >> (repeat1 primitive_type))
               (*This only works for varialbes.
                 For types and names it will not work becuase they do not start with a
                 special character e.g. 

                 vehicle person - either object mobile
                 car - vehicle

                 There is no way to know that car is the beginning of a new typed list.*)
               || (primitive_type wth (fn tp => (tp::[])))) ?? "type"

  fun typed_list x = repeat1 (((repeat1 x) && (pddl_reserved "-" >> type_))
                              || (repeat1 x) wth (fn tlist => (tlist, ["object"]))) ?? "typed_list"

  val types_def = (in_paren(pddl_reserved ":types" >> repeat1 (typed_list pddl_name))) ?? "types def"

  val constants_def = (in_paren(pddl_reserved ":constants" >> repeat1 (typed_list pddl_name))) ?? "consts def"

  val pddl_var = (((char #"?" ) && pddl_name) wth (fn (c, str) => implode [c] ^ str)) ?? "?var_name"

  val predicate = pddl_name

  fun optional_typed_list x = (opt (typed_list x)
                                wth (fn parsed_typesOPT => (case parsed_typesOPT of (SOME parsed_types) => parsed_types
                                                                                     | _ => [])))

  val atomic_formula_skeleton = (in_paren (predicate && optional_typed_list pddl_var)) ?? "predicate"
  
  val predicates_def = (in_paren(pddl_reserved ":predicates" >> (repeat (atomic_formula_skeleton)))) ?? "predicates def"

  val function_type = pddl_reserved "number" ?? "function type"

  fun function_typed_list x =  repeat1 (((repeat1 x) && (pddl_reserved "-" >> function_type))
                                        || (repeat1 x) wth (fn tlist => (tlist, ()))) ?? "function_typed_list"

  val function_symbol = (pddl_name || pddl_reserved "total-cost" wth (fn _ => "total-cost")) ?? "function symbol"

  val atomic_function_skeleton = (in_paren ((function_symbol && optional_typed_list pddl_var)
                                            || (pddl_reserved "total-cost"
                                                  wth (fn _ => ("total-cost", [])))))
                                            (*action-cost is sometimes witout arguments*)
                                 ?? "atomic function skeleton"

  val functions_def = (in_paren(pddl_reserved ":functions" >>
                                (function_typed_list atomic_function_skeleton))) ?? "functions def"

  val function_term = in_paren(function_symbol && repeat pddl_var) wth (fn (x, _) => x) ?? "Function term" (*This is only to accommodate costs*)

  val term = (pddl_name || pddl_var (* || function_term *)) ?? "term"

  fun atomic_formula t = (in_paren(predicate && repeat t)
                             wth (fn (pred, tlist) => Prop_atom (PredAtm (Pred (String.explode pred), tlist))))
                         || in_paren((pddl_reserved "=") && t && t) 
                               wth (fn (eq, (t1, t2)) => Prop_atom (Eqa (t1, t2))) ?? "term"

  fun literal t = ((atomic_formula t) || (in_paren(pddl_reserved "not" && atomic_formula t)) wth (fn (_, t) =>  Prop_not t)) ?? "literal"

  (*TODO: The n is disgustin, there must be a way to remove it.*)

  fun GD n = (literal term ||
              in_paren(pddl_reserved "and" && (if n >= 0 then repeat1  (GD (n - 1)) else repeat1  (literal term))) wth (fn (_, gd) => Prop_and gd) ||
              in_paren(pddl_reserved "or" && (if n >= 0 then repeat1  (GD (n - 1)) else repeat1 (literal term))) wth (fn (_, gd) => Prop_or gd)) ?? "GD"

  val pre_GD = GD 3 ?? "pre GD"

  val assign_op = pddl_reserved "increase" ?? "assign_op"

  val f_head = (in_paren(function_symbol && repeat term)
                || function_symbol wth (fn s => (s, []))) ?? "assign_op"

  val f_exp = num ?? "assign_op"

  val p_effect  = ((atomic_formula term)
                    || (in_paren(pddl_reserved "not" && atomic_formula term))
                          wth (fn (_, t) =>  (Prop_not t))
                    || (in_paren(assign_op && f_head && f_exp))
                          wth (fn _ => Fluent)) ?? "p_effect"  

  val c_effect  = p_effect ?? "c_effect"  

  val effect = (c_effect || (in_paren(pddl_reserved "and" && repeat c_effect )) wth (fn (_, ceff) => (Prop_and ceff))) ?? "effect"

  fun emptyOR x = opt x

  val action_def_body = (opt (pddl_reserved ":precondition" && emptyOR pre_GD)
                         && opt (pddl_reserved ":effect" && emptyOR effect)) ?? "Action def body"

  val action_symbol = pddl_name

  val action_def = (in_paren(pddl_reserved ":action" >>
                    action_symbol
                    && (pddl_reserved ":parameters" >> (in_paren(typed_list pddl_var)))
                    && action_def_body)) ?? "action def"

  val structure_def = (action_def (*|| durative_action_def || derived_def*) )?? "struct def"

  val invariant_symbol = (pddl_reserved ":name" >> pddl_name) ?? "invariant symbol"

  val quantification = (pddl_reserved ":vars" >> in_paren(repeat pddl_var)) ?? "quantification"

  val constraints = (pddl_reserved ":set-constraint" >> pre_GD) ?? "constraint"

  val invariant_def = (in_paren(pddl_reserved ":invariant" >> spaces >>
                                 (invariant_symbol << spaces) &&
                                 (quantification << spaces) &&
                                 (constraints << spaces))) ?? "invariants def"

  val domain = in_paren(pddl_reserved "define" >> in_paren(pddl_reserved "domain" >> pddl_name)
                                                  >> (opt require_def)
                                                  && (opt types_def)
                                                  && (opt constants_def)
                                                  && (opt predicates_def)
                                                  && (opt functions_def)
                                                  && (repeat structure_def)
                                                  && (repeat invariant_def)) ?? "domain"

  val object_declar = in_paren(pddl_reserved ":objects" >> (typed_list (pddl_name)))

  val basic_fun_term = function_symbol || 
                       in_paren(function_symbol && repeat pddl_var) wth (fn (x, _) => x) ?? "basic function term"

  val init_el = (literal (pddl_name)
                 || in_paren((pddl_reserved "=") && basic_fun_term && pddl_name) 
                               wth (fn (eq, (t1, t2)) => Fluent) (*if we have x = x in the init state, it will be igonored here, and readded later in initToIsabelle*)
                 || in_paren((pddl_reserved "=") && basic_fun_term && num) 
                               wth (fn (eq, (t1, t2)) => Fluent)) ?? "init element"

  val init = in_paren(pddl_reserved ":init" >> repeat (init_el))

  val goal = in_paren(pddl_reserved ":goal" >> pre_GD)

  val optimisation = (pddl_reserved "maximize" || pddl_reserved "minimize") ?? "Optimisation"

  val metric_f_exp = function_symbol

  val metric_spec = in_paren(pddl_reserved ":metric" >> optimisation >> in_paren(metric_f_exp))

  val problem = in_paren(pddl_reserved "define" >> in_paren(pddl_reserved "problem" >> pddl_name)
                                                >> in_paren(pddl_reserved ":domain" >> pddl_name)
                                                >> (opt (require_def))
                                                  && (object_declar)
                                                  && init
                                                  && goal
                                                  && opt metric_spec) ?? "problem"

  val plan_action = in_paren(pddl_name && repeat pddl_name)
  val plan = repeat plan_action
			
end

fun readFile file =
let
    fun next_String input = (TextIO.inputAll input)
    val stream = TextIO.openIn file
in
    next_String stream
end

fun writeFile file content =                                                                                                                                                                                                               
    let val fd = TextIO.openOut file                                                                                                                                                                                                       
        val _ = TextIO.output (fd, content) handle e => (TextIO.closeOut fd; raise e)
        val _ = TextIO.closeOut fd
    in () end


val args = CommandLine.arguments()

fun parse_pddl_dom dom_file =
(CharParser.parseString PDDL.domain (readFile dom_file))

val parsedDom = parse_pddl_dom (List.nth (args,0))

val _ = case parsedDom of
          Sum.INR _ =>
             (case (Sum.outR parsedDom) of (dom: PDDL.PDDL_DOM) =>
                   writeFile "prob_defs.thy" (PDDL.pddlDomToString dom))
         | Sum.INL err =>
              (print err)

fun parse_pddl_prob prob_file =
(CharParser.parseString PDDL.problem (readFile prob_file))


val parsedProb = if length args >= 2 then parse_pddl_prob (List.nth (args,1)) else Sum.INL ""

(* val _ = case parsedProb of *)
(*           Sum.INR _ => *)
(*              (case (Sum.outR parsedProb) of (prob: PDDL.PDDL_PROB) => *)
(*                    print (PDDL.pddlProbToString prob)) *)
(*          | Sum.INL err => *)
(*               (print err) *)

fun parse_pddl_plan plan_file =
(CharParser.parseString PDDL.plan (readFile plan_file))

val parsedPlan = if length args >= 2 then parse_pddl_plan (List.nth (args,2)) else Sum.INL ""

(* val _ = case parsedPlan of *)
(*           Sum.INR _ => *)
(*              (case (Sum.outR parsedPlan) of (prob: PDDL.PDDL_PLAN) => *)
(*                    print (PDDL.planToString prob)) *)
(*          | Sum.INL err => *)
(*               (print err) *)

val _ = case parsedDom of
          Sum.INR _ =>
             (case (Sum.outR parsedDom) of (dom: PDDL.PDDL_DOM) =>
                   case parsedProb of
                    Sum.INR _ =>
                        (case (Sum.outR parsedProb) of (prob: PDDL.PDDL_PROB) =>
                              case parsedPlan of
                                   Sum.INR _ =>
                                      (case (Sum.outR parsedPlan) of (plan: PDDL.PDDL_PLAN) =>
                                                 case (PDDL_Checker_Exported.check_plan
                                                             (PDDL_Checker_Exported.Problem
                                                                     (PDDL.pddlDomToIsabelle dom,
                                                                      #1 (PDDL.pddlProbToIsabelle prob),
                                                                      #2 (PDDL.pddlProbToIsabelle prob),
                                                                      #3 (PDDL.pddlProbToIsabelle prob)))
                                                             (PDDL.planToIsabelle plan))
                                                       of PDDL_Checker_Exported.Inl _ => print ("Invalid Plan\n")
                                                         | _ => print "Valid Plan\n")
                                 | Sum.INL err =>
                                        (print err))
                  | Sum.INL err =>
                        (print err))
         | Sum.INL err =>
              (print err)

val _ = OS.Process.exit(OS.Process.success)
