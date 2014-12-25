* de Bruijn criterion
  - Simple core for checking proofs -- no need to verify complicated proof search algorithms... They don't matter.
  - Kernel allows extension without mucking up proofs.

* Extending Coq
  - Can be done with the OCAML source code.
  - Ltac, a DSL embedded in Coq for this purpose.

* Curry-Howard Isomorphism (Type Checking as Proofs)

* Model Checking
  - Only really works for small FSMs
  - Slow
  - Can be embedded in a proof framework as a tactic anyway
  + Automated

* Dependent Types
  - Prevent nonesense programs immediately