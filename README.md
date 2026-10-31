# ai-open-problem-lean-rocq-2026

A research formalization repository with two tracks:
1. public partial-feedback online learning and sequential stochastic games;
2. a separate VC-learning / information-complexity exercise.

The second track does **not** prove the 2026 evaluated-CMI result discussed
below. The public-setting track contains significant Lean/Rocq infrastructure,
but it does **not** claim to have resolved the original open randomized-vs-
deterministic learnability question in every model.

## Research references

- Shao, Fang, Lin, Tao, *Partial Feedback Online Learning*, arXiv:2601.21462v3:
  https://arxiv.org/html/2601.21462v3
- Steinke and Zakynthinou, COLT 2020 VC information-complexity question:
  https://proceedings.mlr.press/v125/steinke20b.html
- Hanneke and Wang, *The optimal information complexity of VC learning*,
  arXiv:2610.10600v2: https://arxiv.org/abs/2610.10600v2

The Hanneke–Wang information-theoretic result is not encoded by this
repository. The root Lean/Rocq files prove a limited threshold-shattering
characterization only.

## Public-setting formalization: what is encoded

### Omega-one candidate

- PublicSetting/Lean/OmegaOneSeparation.lean constructs the countable-
  cocountable measurable space and 0–1 probability measure on the concrete
  Mathlib ordinal Ordinal.omega 1. It includes upper-tail/null-section
  lemmas, adaptive one-round miss nullity, fixed-witness finite-path
  containment, the finite-product probability-zero bridge, and the
  deterministic globally realizable target-family loss construction.
- PublicSetting/Rocq/OmegaOneSeparation.v independently formalizes an
  abstract countable-ideal / ordered-label counterpart, including a
  countably additive 0–1 mass and stagewise risk lemmas. It is not itself a
  concrete encoding of the full omega-one measure/game.

### Sequential processes and tower property

PublicSetting/Lean/SequentialKernelMinimax.lean uses Mathlib's
Ionescu–Tulcea trajectory kernels. For every fixed strategy pair (x,y),
strategyDependentPathMeasure accepts its own sequence of transition kernels
kappa_{x,y,n}; each transition input is the full preceding history.
The module wraps finite-prefix consistency and the condExp_traj tower
identity, and applies that tower identity separately to each strategy pair
under an integrability assumption.

The same file contains a Sion minimax interface. Compactness, convexity,
lower/upper semicontinuity, quasi-convexity/quasi-concavity, and real
extremum hypotheses are explicit inputs; they are not consequences of
kernel measurability alone.

### Appendix G

PublicSetting/Lean/AppendixGBackwardInduction.lean formalizes the
finite-horizon public/oblivious value recursion corresponding to equations
(24)–(26) of Appendix G. PairHistory stores context/acceptable-set pairs.
Its pairHistoryGloballyRealizable predicate requires one and the same
hypothesis to satisfy every pair in the history. Backward induction proves
that the public continuation value is independent of the realized
sample-label list under the paper's information structure.

The key exported theorems are:
- pairHistoryGloballyRealizable_extend_iff;
- appendixG_pairHistory_value_identity;
- appendixG_public_eq_oblivious_minimax;
- appendixG_equation_26.

The next pair-history update deliberately depends on the selected context
and acceptable set, not on the just-drawn current sample. This is the
information structure of the Appendix G / Theorem 18 public-vs-oblivious
set-valued result. It is not a theorem for a stronger adversary whose
next hidden acceptable set depends on the current fresh draw.

### Rocq omega-one object and exact RNG boundary

- PublicSetting/Rocq/ConcreteOmegaOne.v imports Gaia 2.4 and defines
  omegaOne := Ordinals1.aleph_one (cnext omega0). It proves the
  characterization by countable ordinals, closure under countable
  suprema, and non-countability of the carrier.
- PublicSetting/Rocq/PRNGNoGo.v proves that a sampler with finite or
  countably enumerable output range cannot push any source probability
  forward to the countable-cocountable 0–1 measure on omega-one. The
  push-forward gives mass one to the countable range, while the target
  gives that range mass zero.

The Gaia adapter uses Gaia's Bourbaki-style set theory, which has classical
and set-theoretic foundation assumptions; it is not presented as bare,
axiom-free constructive type theory. The generic Rocq countable-ideal game
theorems have not yet been instantiated over the Gaia carrier.

An ideal Lebesgue-real source is a different mathematical question:
a measurable push-forward from [0,1] to the countable-cocountable
omega-one law exists iff cov(N) <= aleph_1. CH suffices; models with
cov(N) > aleph_1 preclude it. This is not an ordinary finite-bit PRNG.
Details are in PublicSetting/RNG_COMPATIBILITY.md.

## What remains open in this repository

1. Instantiate the full Rocq countable-ideal / measure / game development on
   Gaia's concrete omegaOne carrier.
2. Instantiate the generic sequential kernel and Appendix G framework with
   the full public partial-feedback strategy correspondence.
3. Address product measurability of unrestricted adaptive pathwise losses.
   In the countable-cocountable omega-one sigma algebra, sectionwise nullity
   does not imply product measurability of the global error relation.
   The ordinary tower theorem cannot be applied to a nonmeasurable reward.
4. Prove the concrete strategy-space compactness and Sion regularity
   hypotheses for the chosen public game.
5. Do not claim the original Section 3.3 randomized-vs-deterministic
   learnability open question is solved until the above application theorem
   is proved in the intended model.

These are explicit mathematical/model boundaries, not hidden unfinished
proofs. The source files and CI determine which individual claims are
kernel-checked.

## Supporting repositories and tools

The additional repositories are assigned sidecar roles; they are not all
dependencies of the trusted build.

- Mathlib4 — primary Lean measure theory, probability kernels, ordinals,
  conditional expectation, convexity, and Sion library.
- Gaia 2.4 — Rocq set-theoretic ordinals and aleph_one.
- LeanDojo-v2 — theorem retrieval and proof-search assistance; all
  suggestions must be rechecked by Lean.
- Naproche — structured natural-language proof/exposition checking.
- cvc5 — finite SMT counterexample search and arithmetic side conditions.
- SageMath / SymPy / Wolfram — exact finite examples and symbolic checks.
- GAP — finite group actions and symmetry reduction when applicable.
- Macaulay2 — commutative algebra / polynomial-ideal calculations if a
  finite algebraic strategy model arises.
- Context7 — current library/API documentation.
- Parallel Search / Sider Scholar — source-paper and literature retrieval.
- GitHub Actions — pinned Lean/Rocq compilation on the exact commit.

## Reproducing the proof builds

Pinned workflow:
- Lean 4.35.0 with Mathlib 4.35.0;
- Rocq 9.2.0 with Gaia 2.4.

Lean:
~~~sh
cd PublicSetting/Lean
lake build
~~~

Rocq:
~~~sh
cd PublicSetting/Rocq
rocq compile -Q . PublicSetting PublicSetting.v
rocq compile -Q . PublicSetting PublicProtocol.v
rocq compile -Q . PublicSetting ProbabilisticBounds.v
rocq compile -Q . PublicSetting AdaptiveMoments.v
rocq compile -Q . PublicSetting OmegaOneSeparation.v
rocq compile -Q . PublicSetting PRNGNoGo.v
rocq compile -Q . PublicSetting ConcreteOmegaOne.v
~~~

The GitHub Actions workflow installs the pinned Gaia package and checks the
root Rocq/VCLearning.v file as well. A green build certifies only the
statements encoded in those exact source files.
