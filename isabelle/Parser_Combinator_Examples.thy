theory Parser_Combinator_Examples
imports Parser_Combinator
begin

  subsection \<open>Parsing Simple Binary Trees\<close>
  text \<open>We parse binary trees with a really simple syntax:
    \<open>T ::= L | ( T digit T )\<close>

    To keep it simple, we do not setup any lexer, and accept only single digits.
  \<close>  
  datatype tree = Leaf | Node tree char tree   

  text \<open>The function package is used to define recursive parsers.
    You have to avoid left recursion!
    Moreover, note the \<open>::=\<close> operator, which is used instead of \<open>=\<close>!
  \<close>  
  fun parse_tree :: "(_,tree) parser" where
    "parse_tree ::= 
      exactly ''L'' with (\<lambda>_. Leaf)
    \<parallel> exactly ''('' *-- parse_tree -- lx_digit -- parse_tree --* exactly '')'' with (\<lambda>(l,x,r). Node l x r)
    "

  text \<open>The parser can be tried out with Isabelle's evaluation command\<close>  
  value "parse_all_implode_nows (parse_tree) (STR ''(L2(L3L))'')"
  text \<open>Or with the code generator. (The error messages are more readable in the output.)\<close>  
  ML_val \<open>@{code parse_all_implode_nows} @{code parse_tree} "(L2L)"\<close>  
  
  subsection \<open>The Mandatory Calculator Example\<close>
    
  subsubsection \<open>Illustration of right and left associative chaining\<close>
  context begin  
    private definition "testx \<equiv> lx_digit with (\<lambda>x. [x])"
    private definition "testf \<equiv> lx_lowercase with (\<lambda>x a b. ''(''@a@x#b@'')'')"
    value [code] "parse_all (exactly '''') (chainL1 testx testf) (STR ''1a2b3c4d5e6'')"
    value [code] "parse_all (exactly '''') (chainR1 testx testf) (STR ''1a2b3c4d5e6'')"
  end    
      
  subsubsection \<open>Calculator\<close>  
  text \<open>We start by defining a lexer\<close>  
  definition "lx_ws \<equiv> repeat (any char_wspace)"
  abbreviation "token \<equiv> gen_token lx_ws"
    
  definition [consuming]: "tk_plus = token (exactly ''+'')"  
  definition [consuming]: "tk_times \<equiv> token (exactly ''*'')"  
  definition [consuming]: "tk_minus \<equiv> token (exactly ''-'')"  
  definition [consuming]: "tk_div \<equiv> token (exactly ''/'')"  
  definition [consuming]: "tk_power \<equiv> token (exactly ''^'')"  
  definition [consuming]: "tk_lparen \<equiv> token (exactly ''('')"  
  definition [consuming]: "tk_rparen \<equiv> token (exactly '')'')"  

  abbreviation "lx_digit' \<equiv> lx_digit with (\<lambda>d. nat_of_char d - nat_of_char CHR ''0'')"
    
  text \<open>We convert the string to a number while parsing, using a parameterized parser.
    TODO: Disallow leading zeroes\<close>
  fun lx_nat_aux :: "nat \<Rightarrow> (char,nat) parser" where
    " lx_nat_aux acc ::= do { d \<leftarrow> lx_digit'; lx_nat_aux (10*acc + d) }
    \<parallel> return acc"
    
  definition [consuming]: "lx_nat \<equiv> lx_digit' \<bind> lx_nat_aux"  
  definition [consuming]: "lx_int \<equiv> exactly ''-'' *-- lx_nat with uminus o int \<parallel> lx_nat with int"
    
  definition [consuming]: "tk_int \<equiv> token lx_int"

  text \<open>In order to model left associative operators, we 
    use the @{const chainL1} combinator, inspired by parsec\<close>
    
  abbreviation "additive_op \<equiv> 
    tk_plus \<then> return op +
  \<parallel> tk_minus \<then> return op -"  
  abbreviation "multiplicative_op \<equiv> 
    tk_times \<then> return op *
  \<parallel> tk_div \<then> return op div"  
  abbreviation "power_op \<equiv> 
    tk_power \<then> return (\<lambda>a b. a^nat b)" -- \<open>Note: Negative powers are treated as \<open>x\<^sup>0\<close>\<close>
    
    
  text \<open>Mutually recursive functions just work with our parser combinators\<close>    
  fun aexp and xexp and mexp and pexp where
    "aexp ::= tk_int \<parallel> tk_lparen *-- pexp --* tk_rparen"
  | "xexp ::= chainR1 aexp power_op"
  | "mexp ::= chainL1 xexp multiplicative_op"  
  | "pexp ::= chainL1 mexp additive_op"  
    
  (* Old, right-associative version only supporting + and *   
  fun aexp and mexp and pexp where
    "aexp ::= tk_int \<parallel> tk_lparen *-- pexp --* tk_rparen"
  | "mexp ::= (aexp --* tk_times) --[op*] mexp \<parallel> aexp"  
  | "pexp ::= (mexp --* tk_plus) --[op+] pexp \<parallel> mexp"  
  *)
      
  value [code] "parse_all lx_ws (pexp) (STR ''3^3^(2-1)-1*9'')"
    
  
  subsection \<open>Basic XML\<close>
  text \<open>XML like syntax for trees with named nodes, illustrates parameterized parsers\<close>  
    
  definition [consuming]: "lx_open \<equiv> exactly ''<'' *-- repeat1 lx_alphanum --* exactly ''>''"
  definition [consuming]: "lx_close n \<equiv> exactly (''</''@n@''>'')"
  definition [consuming]: "lx_openclose \<equiv> exactly ''<'' *-- repeat1 lx_alphanum --* exactly ''/>''"
   
  datatype basic_xml = TAG string "basic_xml list"
      
  fun lx_tag and lx_body where
    "lx_tag ::= 
        do { name \<leftarrow> lx_open; body \<leftarrow> lx_body; lx_close name; return (TAG name body) }
      \<parallel> lx_openclose with (\<lambda>n. TAG n [])
    "
  | "lx_body ::= repeat lx_tag"  
    
  value [code] "parse_all lx_ws (lx_tag) (STR ''<ad><b></b><shorttag/></ad>'')"
    
    
end
