# Verification Instructions

## Lean 4

Prerequisites: Lean 4 + Lake (elaboration of Mathlib optional).

```bash
cd lean
# If using a full Mathlib project:
# lake update
lake build
```

The file `VCLearningCMI.lean` is self-contained for the combinatorial and ERM parts. Probability statements are given as axioms or `sorry` with clear interfaces so that a Mathlib `Probability` development can be substituted.

Expected: the finite-class theorems type-check and the ERM construction is accepted.

## Rocq (The Rocq Prover, formerly Coq)

Prerequisites: Rocq >= 9.0 (or Coq 8.19+ for compatibility).

```bash
cd rocq
rocq compile VCLearningCMI.v
# or
coqc VCLearningCMI.v
```

All definitions and the finite-class theorems should check. Admitted statements are clearly marked and correspond to the open analytic parts of the original problem.

## Independent Third-Party Check

1. Clone the repository at the PR / commit SHA.
2. Verify Lean and Rocq separately (they share no code).
3. Confirm that the finite-hypothesis-class CMI bound and ERM construction have no `sorry` / `Admitted` in the core statements.
4. The probability interfaces are explicit; any replacement by a full measure-theoretic library preserves the combinatorial claims.

## Relation to SolveAll / COLT 2020

This does **not** claim a full solution of the open problem. It claims:

- machine-checked foundations,
- a concrete learner,
- closure of the finite case,
- reusable interfaces for the remaining open part (general VC classes).
