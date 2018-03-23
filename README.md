Building the validator
======================

 Note: if you do not want to replay the verification, start at step 4 (the code generated by isabelle is included in this tar ball).

 1) Download and install [Isabelle/HOL](https://isabelle.in.tum.de)

 2) Install the Archive of Formal Proofs as indicated in [this page](https://www.isa-afp.org/using.shtml). We require version = Isabelle-2017, which, at the time of writing, is the current version.

 3) Generate sml code equivalent to the Isabelle theories by running

    cd isabelle

    ./build.sh
  note the single quotes around <code>'$AFP'</code> in build.sh! 
  This will invoke Isabelle to check all proofs and re-generate the exported code, which is written to <code> isabelle/code/PDDL_STRIPS_Checker_Exported.sml</code>

 4) Download and install [MLton](http://mlton.org/) compiler version >= 20100608.

 5) Build the generated sml code together with the pddl parser by going to the top-level directory and running

    mlton pddl.mlb

Using the validator
===================

 Given a pddl domain description file (e.g. ged3-itt_no_invariants.pddl), a pddl instance (e.g. d-1-2.pddl), and a plan file (e.g. plan), run:

    ./validate.sh ged3-itt_no_invariants.pddl d-1-2.pddl plan

 Note that the plan file has to have a plan in the IPC format, i.e. a list of action instances, each of which is as follows:

 (act_name arg1 arg2 ...)

 The validator will then give an output indicating the validation result.

Verifying invariants
====================

 Given a pddl domain description (e.g. ged3-itt_with_invariants.pddl), with invariants in a fragment of DKEL [Haslum and Scholz 2003] that only allows the standard logical connectives ("and", "or", "not"), run:

    ./generate_invariant_theories.sh ged3-itt_with_invariants.pddl

 This will generate an Isabelle theory file "prob_def.thy". Copy it to the directory ./isabelle and start Isabelle.
 
    cp prob_defs.thy ./isabelle

    isabelle jedit -d '$AFP' ./isabelle/prob_defs.thy


 This file has a bunch of Isabelle definitions and then  a validity lemma for each (action, invariant) pair. E.g. for the attached domain example ged3-itt.pddl, the file prob_defs.thy has a lemma "x_inverted_invariant_begin_cut" that indicates that the action "begin_cut" does not violate the invariant "x_inverted". Scrolling down in prob_defs.thy will stimulate Isabelle to run the proofs and highlight the lemmas that fail, indicating that the corresponding action could not be proven to conform to the invariant (in our experiments this only happened when the action violated the invariant). For instance in the "ged3-itt.pddl" example, the proof for the lemma "x_s_first_invariant_begin_cut" fails because the action "begin_cut" violates the invariant "x_s_first".

Note: after opening the generated theory file with Isabelle, it might take a few minutes for it to build all the dependencies, as well as to check all the generated proofs.

Proof document
==============
  For a quick inspection of the theories, you may use the [proof outline](isabelle/output/outline.pdf) and [proof document](isabelle/output/document.pdf) pdf files generated by Isabelle. 
  We have included them in the distribution, such that no prior checking of the proof is required.