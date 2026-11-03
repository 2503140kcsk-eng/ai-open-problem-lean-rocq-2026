# Terminal global supremum, upper expectation, and source-model boundaries

**Status: 2026-11-03.** Formal implementation is in
`Lean/TerminalGlobalSupBridge.lean` and
`Rocq/TerminalGlobalSupBridge.v`. CI is tracked by PR #2:
https://github.com/2503140kcsk-eng/ai-open-problem-lean-rocq-2026/pull/2

This note separates the source paper's game, the upper-tail candidate
formalized in this repository, the outer/upper-integral extension, and the
ordinary path-space expectation theorem. A successful build is not a solution
of the paper's open learnability question.

## 1. Source-paper definition and quantifier order

Primary source: Shao, Fang, Lin, and Tao, *Partial Feedback Online Learning*,
arXiv:2601.21462v3 (2026-04-02):
- https://arxiv.org/abs/2601.21462
- https://arxiv.org/html/2601.21462v3

The paper's Definition 1 fixes a finite admissible sequence
`(x_t,S_t,y_t^vis)_{t=1}^T`, with
`S_t ∈ S(Y)` and `y_t^vis ∈ S_t`. For a learner A,

```
ell_T(A) = sum_t E[1{yhat_t notin S_t}]
ell_T(f) = sum_t 1{f(x_t) notin S_t}
R_A(T,H) = sup_admissible_sequences
             (ell_T(A) - inf_{f in H} ell_T(f))
R*(T,H) = inf_A R_A(T,H).
```

In the set-realizable regime there is one fixed subset
`F* ⊆ H` such that `S_t = F*(x_t)` for every t, where
`F*(x) = {f(x) : f ∈ F*}`. The same F* is used across the whole
horizon; it is not a fresh optimizer or a new target family at each round.

The equivalent public-protocol description in Section 3 has the move order:

1. adversary chooses `x_t`;
2. learner chooses its distribution `pi_t`;
3. adversary chooses/reveals `y_t^vis ∈ S_t`;
4. Nature samples `yhat_t ~ pi_t`;
5. the acceptable sets `S_{1:T}` are hidden during play and are specified
   at the end, subject to the witness constraints and the chosen realizability
   regime.

Thus the current visible witness is selected before the current draw. The
adversary can condition on previous completed public history. In the public
formulation, the learner's distribution is part of the move order before the
witness is chosen. The exact quantifiers around a terminal choice of F* and
its dependence on the completed sample path are included in the author
questions below; do not silently replace them by a roundwise choice.

The source leaves the general public randomized-versus-deterministic
learnability question open at the end of Section 3.3. Theorem 19 is an
oblivious-versus-public separation, not the same theorem. The finite-Helly /
nested-inclusion question in Section 3.2 is also different.

## 2. What the two existing Lean files actually prove

### `GlobalSupSequentialRisk.lean`

For contexts `x : Fin T → X`, visible witnesses `w`, and realized
predictions `y`, the model-specific terminal functional is

```
G(x,w,y) =
  sup { beta : X -> Label |
       forall t, beta (x t) <= w t }
    sum_t 1{ y t < beta (x t) }.
```

Here `beta : X → Label` is one global threshold function. The existing
theorem

`globalContextTerminalSupLoss_le_predictableMissCount`

proves

```
G(x,w,y) <= sum_t 1{ y t < w t }.
```

The proof is pointwise: if `y_t < beta(x_t)` and
`beta(x_t) <= w_t`, then `y_t < w_t`. It applies before taking the
supremum, so no supremum/sum interchange is used.

Equality is proved only when `t ↦ x_t` is injective. This restriction is
necessary. For a repeated context with two rounds, take
`x_0=x_1`, witnesses `w_0=2,w_1=5`, and predictions
`y_0=1,y_1=3`. One global beta must satisfy
`beta(x_0)=beta(x_1) <= 2`; hence its terminal loss is at most 1.
The stagewise envelope is 2. A different beta per round would incorrectly
turn the inequality into an equality.

The same file defines the upper integral for arbitrary nonnegative functions:

```
U_mu(f) = inf { integral g dmu |
                 g measurable and forall x, f(x) <= g(x) }.
```

It proves monotonicity, equality with the Lebesgue integral on measurable
functions, and the addition inequality when the immediate cost is measurable.
It also proves the exact upper-risk Bellman operator is bounded by the
stagewise section-risk operator, and lifts that one-step inequality through
finite-horizon backward induction.

### `ExpectedLossBridge.lean`

This is a different theorem. Its loss is a family
`loss i : Ω → ℝ` on a completed path probability space. It assumes:

- `filtration i ≤ m₀` for every index i;
- `SigmaFinite (μ.trim (filtration i))` for every i;
- `Integrable (loss i) μ` for every i in the finite summation set.

It proves

```
integral (sum_i E[loss_i | filtration_i]) dmu
  = integral (sum_i loss_i) dmu.
```

This is the finite-sum conditional-expectation identity. It does not contain
a global target-family supremum, does not prove measurability of a terminal
supremum, and does not justify
`sup_F sum_t loss_t(F) = sum_t sup_F loss_t(F)`.

### `TerminalGlobalSupBridge.lean`

This new file connects the two levels in a deliberately conditional way:

1. wraps the one-global-`beta` terminal payoff as a function of the complete
   prediction path;
2. reuses the pointwise global-supremum bound;
3. applies upper-integral monotonicity to any path measure, without requiring
   the terminal payoff to be measurable;
4. when the stagewise envelope is jointly measurable on path space, replaces
   its upper integral by its ordinary nonnegative Lebesgue integral;
5. when the terminal payoff itself is jointly measurable, proves its upper
   integral is exactly its ordinary extended expectation;
6. exposes a separate premise bounding the stagewise path expectation by a
   sequential Bellman budget.

The last premise is intentionally visible. Operator-level Bellman domination
is already in `GlobalSupSequentialRisk.lean`; this file does not fabricate
a path-law/strategy realization theorem that would identify every path
expectation with that Bellman value.

## 3. Upper integral versus ordinary expectation

For a nonnegative function `f : Ω → [0,∞]`, `U_mu(f)` is defined even if
`f` is not measurable. Ordinary expectation is not automatically defined
for such an arbitrary function.

If `f` is jointly measurable on the *complete path space*, then the
measurable function itself is an admissible majorant and monotonicity of
Lebesgue integration gives

```
U_mu(f) = integral f dmu.
```

This equality holds for the extended nonnegative integral and does not
require integrability. If a finite real-valued expectation is required,
add the relevant integrability / finite-integral assumption. In the existing
real-valued bridge, integrability is explicitly required for each round loss.
For probability measures, a measurable 0-1 indicator is bounded and hence
integrable.

The crucial premise is *joint* measurability of the path payoff, not merely
measurability of each section after the other variables are held fixed.
Measurability of each one-step miss section does not imply measurability of
the adaptive full-path error graph.

## 4. Standard-Borel majority-core obstruction

This is a model obstruction, not a blanket impossibility theorem for all
standard-Borel separations.

Let Y and Theta be standard Borel spaces, let
`M ⊆ Theta × Y` be Borel, and define
`S_theta = {y : (theta,y) ∈ M}`. Put

```
R(x,y) iff for every theta,
  (theta,y) in M -> (theta,x) in M.
```

Equivalently, x belongs to every acceptable set that contains y.
The relation R is transitive: if R(x,z) and R(z,y), then membership of y
in any S_theta implies membership of z and then x in that same S_theta.

Its complement is the projection of the Borel set

```
D = {(x,y,theta) : (theta,y) in M and (theta,x) notin M}
```

onto Y×Y. Hence not-R is analytic (Σ¹₁), while R is coanalytic (Π¹₁).
Analytic and coanalytic subsets of standard Borel spaces are universally
measurable. Therefore R is measurable in the completion of the product
probability measure mu×mu.

Suppose every incoming section has mass at least
`1-epsilon > 1/2`:

```
for every y, mu({x : R(x,y)}) >= 1-epsilon.
```

Fubini gives product mass greater than one half, so there is x₀ whose
outgoing section `{y : R(x₀,y)}` has mass greater than one half.
For any fixed y, its incoming section also has mass greater than one half.
Two sets of probability greater than one half intersect, so choose z with
R(x₀,z) and R(z,y). By transitivity R(x₀,y). Since y was arbitrary,
x₀ is related to every y and lies in every nonempty S_theta.

Thus a standard-Borel construction cannot satisfy this uniform
core-complement-risk premise with epsilon strictly below one half while
avoiding a common acceptable point. The threshold is sharp: for
Y={0,1} with uniform measure and the admissible sets {0},{1}, each core
has complement measure exactly one half and no point lies in both sets.

### Formalization boundary

- Lean's `StandardBorelCore.lean` proves the Fubini/majority/transitivity
  core only when R is measurable in the **uncompleted product sigma-algebra**.
- Descriptive set theory gives universal measurability of R, i.e. measurability
  in the completion of the product probability measure. The implication
  from a Borel relation M to that completed-product measurability is currently
  a written argument, not a theorem proved by the current Lean file. A
  further completion-aware measure-space formalization is required before
  that descriptive-set-theoretic conclusion can be fed into the current
  theorem unchanged.
- Rocq's `StandardBorelCore.v` assumes the Fubini-majority and section
  intersection principles explicitly, then proves the transitivity argument.
- Consequently, neither formal module claims a kernel-checked proof of the
  Suslin projection theorem or of the full standard-Borel-to-completion
  bridge.

The omega₁ example shows why sectionwise nullity is not enough. The strict
order relation
`E={(alpha,beta): beta<alpha}` on omega₁ has countable sections in one
direction and cocountable sections in the other. If E were measurable in
the product sigma algebra, Tonelli would force product measure to be both
zero and one. In fact, every product-measurable superset of E has product
measure one. Therefore one-step section nullity alone does not establish
ordinary pathwise expected loss.

## 5. Author confirmation requested (not yet sent)

A public institutional profile for coauthor Cong Fang lists
`fangcong@pku.edu.cn`:
https://www.ai.pku.edu.cn/en/info/1409/1827.htm

The following points should be confirmed by an author before treating any
interpretive choice as part of the paper's theorem:

1. In the public protocol, does the adversary choose the current visible
   witness after seeing the learner's distribution `pi_t`, but strictly
   before the current sample `yhat_t`?
2. In the set-realizable regime, is one subset `F* ⊆ H` chosen for all
   rounds, with each `S_t=F*(x_t)`; may this single F* be selected after
   the complete public sample path is realized, subject to all witnesses
   being accepted?
3. When the terminal hidden sets are selected as a function of the completed
   draw path, is `E[1{yhat_t notin S_t}]` intended as an ordinary expectation
   under a measurable pathwise payoff? If yes, which joint measurability
   assumption on the terminal selection / adversary is implicit?
4. Does the paper assume the label space and relevant strategy spaces are
   standard Borel, or is an arbitrary measurable space allowed throughout?
5. Is an outer expectation / upper integral an admissible extension of the
   model, or would that be a distinct definition of regret rather than the
   original Definition 1?

No author response is currently recorded. Do not cite this question list as
an endorsement or interpretation by the authors.

## 6. Tool and repository responsibilities

The division of labor is deliberately non-overlapping:

| Resource | Responsibility in this task | Verification boundary |
|---|---|---|
| GitHub + Actions | Review exact source, commit the bridge, run pinned CI, keep evidence tied to commit SHA | CI only validates the workflow's actual targets |
| Lean 4.35 + Mathlib4 | Main definition/proof for global-sup path risk, upper integral, measurability, Bellman recursion | Kernel-checked declarations; inspect `lake check` and `#print axioms` |
| Rocq 9.2 + Gaia 2.4 | Independent order-theoretic check of the one-global-function terminal bound; ordinal carrier where needed | Current new Rocq bridge is discrete/order-theoretic; not a second measure-theory development |
| Sider Scholar | Search the arXiv record and related literature | Bibliographic retrieval, not proof |
| Parallel Search | Retrieve the full paper sections and primary documentation; locate official author contact | Source extraction, not proof |
| Context7 | Check exact current Lean/Mathlib/Rocq API documentation | Documentation does not establish successful compilation |
| Wolfram | Spot-check the finite repeated-context counterexample | Computational sanity check only |
| cvc5 | Search finite-state / finite-domain variants for counterexamples | Cannot certify uncountable measure-theoretic claims |
| SymPy / SageMath | Exact finite recurrence, rational-game and combinatorial cross-checks | Not proof kernels |
| GAP | Finite symmetry/orbit enumeration if a finite game instance has group symmetry | Not useful for the ω₁ measurable-space theorem |
| Macaulay2 | Polynomial ideal / algebraic constraints only if a future finite reduction introduces them | Not a probability or descriptive-set-theory prover |
| Naproche | Check the prose proof and dependency explanation | Prose validation is not Lean/Rocq kernel verification |
| LeanDojo-v2 | Optional theorem retrieval / proof-state search with local free tooling | Any suggestion must be replayed by Lean; paid inference/GPU workflows excluded |

Do not add every starred repository as a build dependency. It would enlarge the
trusted code base without helping the measure-theoretic proof.

## 7. Axiom / warning audit policy

For Lean, run the pinned Lean 4.35.0 `lake build`, then `lake check`,
and inspect `#print axioms` for all new bridge theorems. The expected
classical dependencies (for example classical choice, propositional
extensionality, and quotient soundness) must be reported, not mislabeled as
untrusted. Any `sorryAx`, `admit`, `unsafe`, or unexpected axiom is a
release blocker. Warnings and deprecations must be scanned in the actual
workflow logs.

For Rocq, compile under the pinned Rocq 9.2 environment and inspect
`Print Assumptions` plus `Print Opaque Dependencies`. A theorem is not
"assumption-free" if an opaque proof body was unavailable to the audit;
such dependencies must be recorded as unknown. The new Rocq file prints
assumptions for its main theorem and the universal upper-bound wrapper.

CI evidence is meaningful only for the exact tested head commit. The PR
must remain draft until all new Lean/Rocq jobs and log scans complete.
