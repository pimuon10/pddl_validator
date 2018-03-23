theory PDDL_Checker_Export_Code
imports PDDL_Checker
begin
  text \<open>Code export is in separate file for 
    technical reasons, as a file with export-code commands 
    cannot be imported from other projects.\<close>

  export_code 
    parse_check_dpp_impl (* Complete checker *)
    parse_check_dp_impl  (* Only well-formedness of domain and problem *)
    parse_check_p_impl   (* Only validity of plan, silently assuming well-formedness  *)
    parse_domain_file
    parse_problem_file
    parse_plan_file
    check_plan
    Inr Inl
  in SML 
    module_name PDDL_Checker_Exported
    file "code/PDDL_Checker_Exported.sml"

end
