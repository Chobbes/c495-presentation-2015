* The task itself
  - Actually impossible
    + Have to trust the entire software stack.
      - While this is difficult this part may not actually be impossible for most tasks.
    + Have to trust the hardware.
      - Hard drive failures
      - Solar radiation
      - Everything has a probability to fail

* Why bother?
  - Necessary to do the best that we can.
  - Many situations where safety is of utmost importance
    + Aerospace
    + Automotive industry
    + Medical equipment (xray machine)
    + Military
  - Beyond that correctness can have massive costs
    + Intel floating point bugs

* What can be done?
  - Manual verification
    + Expensive
    + Error prone (exactly what we're trying to prevent)
    + Necessary due to lack of tools
  - Model checking
    + Good for small pieces of code
    + Only really works for FSMs
    + Computationally expensive, results tend not to be reusable
  - Type checking
    + Essentially free criterions of correctness (values of certain types can only behave certain ways)
    + Requires due diligence
    + Can be issues with decidability
  - Theorem Proving
    + Intimately related to type checking through C-H correspondence
    + Good reuse
    + Manual work required sometimes
    + Can be expensive
    + Provides a good framework for reasoning about code
    

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
