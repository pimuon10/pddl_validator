PDDL plan validator
##########

TODO FIXME OUTDATED INFO! New STRIPS checker is in ../codeBase/planning/pddlParser

To build the tool: 
    isabelle build -d . PDDL_Checker 
    cd code
    make
    
This will generate a binary file code/PDDL_Checker. 

To install it in ~/bin:
    make install

To validate a plan
    PDDL_Checker domain.pddl problem.pddl plan
    
where domain and problem must be in the PDDL strips+equality fragment, and plan
is a newline separated list of actions of the form
    action-name object1 ... objectN (1)

PDDL_Checker will output
    s VERIFIED
only if it could successfully verify that the domain and problem are well-formed, and the plan
is actually valid.
