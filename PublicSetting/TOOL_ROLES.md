# Tool and repository responsibility matrix

Status: 2026-10-31. This file records a division of labor for the formalization.
The roles below are deliberately non-overlapping: computation, literature
retrieval, proof search, and proof-kernel checking are different activities.

## Trusted proof core

| Resource | Assigned responsibility | Verification boundary |
|---|---|---|
| [Lean 4](https://github.com/leanprover/lean4) | Main theorem language and proof kernel for the sequential-kernel and Appendix G developments | A theorem is accepted only when the pinned Lean kernel compiles the source; generated suggestions are not proofs |
| [Mathlib4](https://github.com/leanprover-community/mathlib4) | Probability kernels, Ionescu--Tulcea trajectories, finite-prefix consistency, conditional expectation, measure theory, topology, convexity and Sion minimax | Existing lemmas supply general mathematics; the project must still prove that its concrete hypotheses match |
| [Rocq 9.2](https://github.com/rocq-prover/rocq) | Independent proof checker for the countable-ideal and RNG-obstruction modules | Classical imports and external foundation assumptions must be reported; kernel acceptance is not the same as constructive proof |
| [Gaia 2.4](https://github.com/rocq-community/gaia) | Concrete set-theoretic ordinal construction for Rocq: aleph_one := cnext omega0, countable_ordinal, and aleph_oneP | The adapter constructs the ordinal object; the project-specific game/measure schema is not yet instantiated on the Gaia carrier |

## Mathematical computation and counterexample search

| Repository | Assigned responsibility | Appropriate task here | Not a substitute for |
|---|---|---|---|
| [Macaulay2](https://github.com/Macaulay2/M2) | Commutative algebra and algebraic geometry | Gröbner-basis or polynomial-ideal calculations only if a finite strategy/payoff example develops polynomial constraints | Probability theory or a proof of an ordinal-measure theorem |
| [GAP](https://github.com/gap-system/gap) | Computational discrete algebra, especially finite groups | Enumerate finite symmetry classes, group actions, or orbit-reduced game examples if the instance has symmetry | Infinite-history measurable-process proofs |
| [SymPy](https://github.com/sympy/sympy) | Lightweight symbolic mathematics and exact expressions | Simplify finite Bellman recurrences, rational expected-payoff expressions, and hand-derived identities | A kernel-checked theorem |
| [SageMath](https://github.com/sagemath/sage) | Integrated open-source computer algebra environment | Cross-check small finite normal-form games, exact linear programs, rational polytopes and combinatorial examples; use its GAP/SymPy interfaces when convenient | An independent foundational proof; Sage includes other systems and is not itself a proof kernel |
| [cvc5](https://github.com/cvc5/cvc5) | SMT solving for first-order formulas modulo supported theories | Search for finite counterexamples to candidate inequalities, finite-state invariants, and arithmetic side conditions | Uncountability, measure-theoretic measurability, or a standalone proof of a Lean/Rocq theorem |

## Proof exposition and automated proof development

| Repository | Assigned responsibility | Appropriate task here | Guardrail |
|---|---|---|---|
| [Naproche](https://github.com/naproche/naproche) | Checking structured natural-language mathematical documents, with Isabelle/PIDE integration | Independently inspect the prose proof of the backward-induction and countable-cocountable-measure arguments | Keep the formal Lean/Rocq statement as the source of truth; natural-language checking does not replace those kernels |
| [LeanDojo-v2](https://github.com/lean-dojo/LeanDojo-v2) | Lean repository tracing, theorem retrieval, dataset construction, and AI-assisted proof search | Optional local tracing/retrieval of Mathlib declarations and proof-state examples | Proof suggestions must be replayed by Lean. The README lists GPU and external inference/API options for some agent workflows; those are excluded from the free, reproducible CI path |

## Connected research and development tools

| Tool | Role actually appropriate to this project | What its output means |
|---|---|---|
| Wolfram | Symbolic/numeric spot checks on finite examples and mathematical notation lookup | Independent computational sanity check only; no core theorem is certified by a Wolfram result |
| Context7 | Current API and version documentation, especially Lean/Mathlib and Rocq syntax | Documentation lookup; it does not establish that code compiles |
| Parallel Search | Locate and extract the source paper, relevant formal-library declarations, and primary project documentation | Source discovery; every mathematical claim still needs checking against the source or formal proof |
| Sider Scholar | Academic record lookup for the cited paper and related literature | Bibliographic and abstract evidence; not a formal proof |
| GitHub | Source inspection, versioned changes, pull-request tracking, and Actions CI | The recorded CI job is evidence only for the exact commit and exact build workflow run |

## Execution policy

1. The trusted proof path is pinned Lean/Mathlib plus Rocq/Gaia in GitHub Actions.
2. The CAS/SMT tools are optional sidecar checks. Their output can motivate lemmas or reveal counterexamples, but is never inserted as an unverified theorem.
3. Do not add every listed repository as a build dependency. That would enlarge the trusted build surface and make CI harder to reproduce without strengthening the proof.
4. No paid inference API, hosted GPU, paid CAS service, or remote deployment is required by the proof workflow. LeanDojo's optional training/inference stack is not part of CI.
5. Any future CAS/SMT result used as a proof step must be translated into a theorem statement and replayed by Lean or Rocq, or accompanied by a separately verified certificate checker.

## Directly relevant files in this repository

- Lean/SequentialKernelMinimax.lean: strategy-indexed history-dependent path kernels, finite-prefix consistency, trajectory tower property, and Sion minimax interface.
- Lean/AppendixGBackwardInduction.lean: finite-horizon public/oblivious recursion and equation (26).
- Rocq/ConcreteOmegaOne.v: Gaia-backed omega_one adapter and countable-supremum closure.
- Rocq/PRNGNoGo.v: no countable-output sampler can push forward to the countable-cocountable 0/1 law.
- RNG_COMPATIBILITY.md: exact sampler impossibility and the separate infinite-real-source consistency boundary.
