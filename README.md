# Agda Formalization for Jacana: Sound Composition of Differentiation, ODE Solving, and Stochastic Processes

This is the Agda code accompanying the paper "Jacana: Sound Composition of Differentiation, ODE Solving, and Stochastic Processes".

The code is primarily meant to be typechecked to check its correctness; this can be done using the command

```
agda src/Everything.agda
```

The file `Everything.agda` also contains an overview of the different modules in the repository.

For main points of interest, see the following table.

| File                                    | Content                                    |
|-----------------------------------------|--------------------------------------------|
| src/Jacana/Syntax.agda                  | Abstract syntax                            |
| src/Jacana/Typing.agda                  | Typing relation                            |
| src/Jacana/SmallStep.agda               | Operational semantics                      |
| src/Jacana/Denotations/Model.agda       | Abstract denotational semantics            |
| src/Jacana/Denotations/Domain.agda      | Semantic domain                            |
| src/Jacana/Denotations/Denotations.agda | Instantiation of the semantics             |
| src/Jacana/Properties/Progress.agda     | Proof of progress of operational semantics |
| src/Jacana/Properties/Preservation.agda | Proof of preservation                      |
| src/Jacana/Properties/Determinism.agda  | Proof of determinism                       |

The code was developed using a bleeding-edge version of Agda 2.8, along with the 1lab library for cubical Agda.
You may need to match the commit hashes below to be able to check the proofs.

Commits:
- agda: 295c60c79cd49e880b9f07add98462f1b82d26f2
- 1lab: 02ab3a695da33e06874407e139374e1878f917a9

The proofs are based on an axiomatisation of the real numbers (in `src/Lib/Algebra/Reals.agda`) as well as an axiomatisation of regularity properties such as continuity and piecewise analyticity under analytic partitioning (PAP) (in `src/Jacana/Denotations/Regularity.agda`).
Furthermore, the denotational semantics rely on some regularity properties of operations like differentiation, which were only proven on paper (listed in `src/Jacana/Denotations/Denotations.agda`).
Similarly, the operational semantics and its soundness proof rely on abstract implementations of automatic differentiation and ODE solving (specified in `src/Jacana/SmallStep.agda`) which are assumed to be type-preserving (see `src/Jacana/Properties/Preservation.agda`).
Wherever such axiomatisations or assumptions are used, they are passed explicitly as parameters, no postulates are introduced.
Each such parameter is named using the scheme `XXXXAssumptions` (e.g., `EvalAssumptions` in `src/Jacana/SmallStep.agda`).
