# Presentation

## Type System

TODO Calc. of constructions

TODO See "Axioms and Computation"

- Full universe polymorphism
    - Infinite hierarchy of cumulative types
- Implicit (i.e. inferred) type arguments
    - TODO most popular type inference is Hindley-Milner, how does Lean 4 work?
    - ```lean4
      Lst.cons {α : Type u} (a : α) (as : Lst α) : Lst α -- bracketed arguments can be inferred      
      ```
    - Override w/ `@` syntax
        - Similar to Haskell `TypeApplications` syntax (except all arguments are made explicit)
- [Proposition-types](https://leanprover.github.io/theorem_proving_in_lean4/propositions_and_proofs.html)
    - `Prop` is an alias for `Sort 0`
    - `Type u` is an alias for `Sort (u + 1)`

## [Tactics](https://leanprover.github.io/theorem_proving_in_lean4/tactics.html)

- Tactics are macros that implement proofs
- Has hygienic macro system (used to implement tactics)

## Comparison to Existing Languages


### Idris

- Emphasis on dependently-typed programming rather than theorem proving
- Has heterogeneous equality (i.e. = constructor takes arguments that are different types)
- Doesn't have universe polymorphism?

### Pie

- No new data-type definitions (i.e. new inductive data types).
- No tactic-like syntax -> requires manual (verbose) application of thms
- Few basic syntactic conveniences
    - Let bindings
    - Extremely basic type inference
        - Explicit type applications for all function applications
- No typeclasses (or symbol overloading)
- No universe polymorphism
    - Only value-type-kind (U) allowed

### Coq

### Haskell

- Utterly incomprehensible type-level machinery