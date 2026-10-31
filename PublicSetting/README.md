# Public-setting separation in partial-feedback online learning

Status date: 2026-10-31

## Target open problem

Shao, Fang, Lin, and Tao, Partial Feedback Online Learning, arXiv:2601.21462v3, ends Section 3.3 with this open question: can randomized and deterministic learners have different learnability in the public partial-feedback setting? The paper distinguishes public from oblivious adversaries by whether the adversary can use past realized predicted labels. The current PR studies a set-realizable construction with one globally consistent target subfamily.

There is a separate question at the end of Section 3.2 about whether finite Helly number or the nested-inclusion condition is necessary for inseparability. These are different questions; the present construction targets the Section 3.3 public-setting question.

## Candidate construction: countable-cocountable omega-one space

- Label space: \(Y=\omega_1\), the first uncountable ordinal.
- Sigma algebra: all countable or cocountable subsets.
- Probability measure: zero on countable sets and one on cocountable sets.
- Admissible sets: upper tails \(S_\beta=\{y\in\omega_1:\beta\le y\}\).
- Instance space: \(X=\mathbb N\).
- Hypothesis class: \(H=Y^{\mathbb N}\), all functions from contexts to labels.

Every strict initial segment below \(w<\omega_1\) is countable. Thus each upper tail has measure one and its complement has measure zero. The measure is countably additive: in a disjoint measurable sequence, at most one member can be cocountable; if there is one, all other members are countable and the union has mass one; if there is none, the countable union is countable and every term has mass zero.

### Randomized side

The learner returns the same countable-cocountable probability measure after every public history. The visible witness \(w_t\) is fixed before the current sample. Any eventual admissible upper tail \(S_{\beta_t}\) containing it satisfies \(\beta_t\le w_t\). A mistake implies
\[
\hat y_t<\beta_t\le w_t.
\]
Hence the miss set is contained in the countable null initial segment below \(w_t\), so the one-round expected mistake is zero.

The terminal global target subfamily may be chosen after the complete prediction path. Lean proves (i) the pointwise full-path inclusion: for any threshold rule depending on the complete path, if each selected upper tail contains its fixed pre-sampling witness \(w_t\), then every path with a mistake lies in the finite union of cylinders \(\{\hat y:\hat y_t<w_t\}\); and (ii) the finite-product probability theorem `terminalPathMiss_pi_measure_zero`, using Mathlib 4.35's `Measure.pi_eval_preimage_null` and `measure_iUnion_null_iff`, showing that this entire miss event has product outer-measure zero. In addition, `constantRandomizedLearner_zero_at_every_public_history` proves the conditional one-round miss probability is zero for every public history and every visible witness selected before the current draw, even when the final threshold depends on the current sample.

### Deterministic side

The deterministic strategy receives the complete public history: previous contexts, visible labels, and realized predictions. At round \(t\), the adversary computes the current deterministic prediction \(p_t\) and reveals \(w_t=p_t+1\).

One global target subfamily is
\[
H^*=\{f:\mathbb N\to\omega_1:\forall t,\ p_t+1\le f(t)\}.
\]
It is nonempty. Its projection at context \(t\) is exactly \(S_{p_t+1}\), so the same \(H^*\) realizes all acceptable sets, contains every visible witness, and excludes every deterministic prediction. The comparator loss is zero and the deterministic learner loses exactly \(T\) rounds.

## Relation to Section 3.2 / Theorem 15

Theorem 15 (Section 3.2) gives sufficient conditions for deterministic/randomized inseparability; Corollary 16 gives a set-valued analogue. For every countable sequence \(\beta_n<\omega_1\), its supremum is still below \(\omega_1\). Therefore every countable family of upper tails has nonempty intersection; every finite subfamily does too, while the intersection of all upper tails is empty. In this family Theorem 15's condition (1), a countable decreasing subfamily with empty intersection, fails, and the Helly number is infinite.

A terminology caveat: the upper tails are pairwise nested (linearly ordered by inclusion), but no countable subfamily has empty intersection. The v3 paper does not give a separate stand-alone definition of “nested inclusion property” in the passage; this repository therefore reports the explicit condition in Theorem 15 rather than equating it with mere pairwise nestedness.

## Formal verification status

- Lean 4.35 / Mathlib 4.35: PublicSetting/Lean/OmegaOneSeparation.lean concretely constructs omega_1, the countable-cocountable measurable space, and the 0/1 probability measure via Measure.ofMeasurable. It proves the ordinal/countability facts, countable upper-tail intersection, nullity of adaptive one-round miss sets, finite-path miss-event containment in a finite union of null coordinate cylinders, and the globally realizable deterministic T-mistake construction. omegaOne_finite_horizon_separation packages the fixed-threshold randomized guarantee and the deterministic public-history lower bound for every finite horizon.
- Rocq 9.2: PublicSetting/Rocq/OmegaOneSeparation.v independently checks the 0/1 countably additive measure over a countable ideal and an abstract ordered label type, including the corresponding full-path miss-coordinate containment and deterministic global-family loss result. It is an abstract omega-one-like schema, not a concrete Rocq encoding of omega_1.

Latest code commits: Lean 4ebc89d95a6deb59bf658c2e2c26bac897701f2a and Rocq b5940c796e71800125625cbe61f5502f98902da9. Both push and pull-request CI workflows passed on the Lean code commit: runs 41160197913 and 41160201246. The documentation-complete PR head f0b7fdc755ff827aefe4f4d96e1111201bf5c68e also passed both workflows: runs 41160340096 and 41160343911. All four latest Lean/Rocq job logs were inspected; there were zero compiler errors, warning/deprecation/hint diagnostics, or sorry/admit/Admitted/Axiom/Parameter markers. The full-path containment lemma is machine-checked. The finite-product probability calculation and literal minimax inf-sup formalization remain explicit scope boundaries.

### Scope boundaries

1. The sequential transition-kernel / tower-property proof for a visible witness chosen as an arbitrary measurable function of the entire preceding random history is not encoded as one joint stochastic-process theorem. The file does prove the current-round miss probability is zero uniformly for every history and witness, and separately proves the finite-product result for any fixed witness sequence with arbitrary full-path terminal thresholds.
2. The literal minimax inf-sup operator from Appendix G is not separately declared as a Lean definition/theorem. The file formalizes the finite-horizon strategy-level witnesses and loss statements.
3. The construction uses the paper's abstract probability-measure model on the label sigma-algebra. The concrete countable-cocountable space on omega_1 is not standard Borel or countably generated, and the measure is not claimed to be sampled by a usual real-valued PRNG. No standard-Borel or PRNG implementation claim is made.
4. Rocq verifies the corresponding abstract order/ideal schema rather than a concrete ordinal omega_1.

These are formalization and model boundaries, not compiler failures.

## Roles of the supplied repositories

The supplied repositories were inspected for suitability; they are supporting references and tools, not interchangeable proof kernels.

- Mathlib4 — primary Lean library and trusted kernel environment for ordinals, measurable sets, and measure construction.
- LeanDojo-v2 — retrieval/tactic suggestion and Lean proof-development assistance; not a proof certifier.
- Naproche — checks natural-language mathematical exposition; useful for documenting the argument, not a substitute for Lean/Rocq.
- cvc5 — finite first-order/SMT models and counterexample search; it cannot prove the uncountability of omega_1.
- SageMath / SymPy / Wolfram — finite arithmetic, toy-order examples, and symbolic sanity checks.
- GAP — finite combinatorial and group-theoretic experiments; low direct relevance here.
- Macaulay2 — commutative algebra and algebraic geometry; little direct leverage on the ordinal measure argument.

## Sources

- Shao, Fang, Lin, Tao, Partial Feedback Online Learning, arXiv:2601.21462v3 (2026-04-02): https://arxiv.org/html/2601.21462v3
- MathOverflow, Inner Regularity of probability measure on totally ordered sets: https://mathoverflow.net/questions/343303/inner-regularity-of-probability-measure-on-totally-ordered-sets
- MathOverflow, Measure on omega_1: https://mathoverflow.net/questions/81143/measure-on-omega-1

## Verify

Lean: cd PublicSetting/Lean && lake build

Rocq 9.2: cd PublicSetting/Rocq && rocq compile -Q . PublicSetting PublicSetting.v


## Final documentation-head CI (2026-10-31)

The latest documentation-complete branch head is `001fa8b623e0326223658ac228f0f8f435460100`. Its push run [41163413199](https://github.com/2503140kcsk-eng/ai-open-problem-lean-rocq-2026/actions/runs/41163413199) and pull-request run [41163416315](https://github.com/2503140kcsk-eng/ai-open-problem-lean-rocq-2026/actions/runs/41163416315) both succeeded. Lean and Rocq succeeded in both runs. All four job logs were inspected; zero compiler errors, warnings, deprecation/hint messages, or unfinished-proof markers were found.
