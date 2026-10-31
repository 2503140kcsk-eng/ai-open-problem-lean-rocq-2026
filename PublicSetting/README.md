# Public-setting separation in partial-feedback online learning

Status date: 2026-10-31

## Research target

Construct a fixed set-realizable hypothesis class and a single globally consistent target subfamily for which randomized regret is sublinear while every deterministic public-history learner has linear regret, or identify the obstruction. The construction below gives a finite-horizon strategy-level separation in the paper's unrestricted measurable-space model.

Here o(T) means regret divided by T tends to zero; Ω(T) means a positive linear lower bound. A globally consistent target means that the accepted-label set at every context is the projection of the same fixed target subfamily H* of one hypothesis class H.

## Candidate construction: countable-cocountable ω₁

- Label space: Y = ω₁, the first uncountable ordinal.
- Sigma algebra: all countable or cocountable subsets of Y.
- Probability measure: zero on countable sets and one on cocountable sets.
- Admissible sets: upper tails Sβ = {y in ω₁ : β ≤ y}.
- Instance space: X = ℕ; hypothesis class: H = Y^ℕ.

Every strict initial segment below an element w of ω₁ is countable. Hence every upper tail has measure one and its complement has measure zero.

### Randomized upper bound

The randomized learner returns the same countable-cocountable probability measure after every public history. If the visible witness is w_t and the eventual acceptable set is an upper tail S_{β_t} containing w_t, then β_t ≤ w_t. A mistake implies ŷ_t < β_t ≤ w_t, so the entire miss event is contained in the null initial segment [0,w_t). This containment is pointwise and still holds when the terminal target family is chosen after the prediction path. Lean formalizes the one-round adaptive miss-set containment and the zero expected loss of every finite upper-tail sequence.

### Deterministic lower bound

The deterministic strategy interface uses public histories containing each previous context, visible label, and realized prediction. At round t, the adversary computes the learner's current prediction p_t and reveals w_t = p_t + 1. Define one global target family

H* = { f : ℕ → ω₁ | for every t, p_t + 1 ≤ f(t) }.

This family is nonempty. Its projection at context t is exactly S_{p_t+1}; therefore one fixed H* realizes every accepted set, accepts each visible witness, and excludes every deterministic prediction. The comparator loss is zero and the learner loses exactly T rounds.

## Relation to the paper's structural criterion

Theorem 15 in Section 3.2, and its set-valued analogue Corollary 16, give sufficient conditions for deterministic/randomized inseparability. For every countable sequence β_n < ω₁, its supremum is still below ω₁, so every countable family of upper tails has nonempty intersection. Every finite subfamily also has nonempty intersection, while the intersection of all upper tails is empty. Thus this family has infinite Helly number and violates Theorem 15 condition (1), which asks for a countable decreasing subfamily with empty intersection.

A terminology caveat: all upper tails are pairwise nested (linearly ordered by inclusion), but no countable subfamily has empty intersection. The v3 paper's text does not give a separate stand-alone definition of “nested inclusion property”; its formal sufficient criterion is Theorem 15(1). This repository uses that precise countable-empty-intersection criterion and does not conflate it with mere pairwise nestedness.

The open question stated at the end of Section 3.2 asks whether finite Helly number or the nested-inclusion condition is necessary for inseparability. Section 3.3 is a different topic: Theorem 17 compares oblivious and public set-valued learning; Theorem 18 separates oblivious and public partial-feedback learning. Neither is the same theorem as the omega-one randomized/deterministic construction.

## Formal verification status

- Lean 4.35 / Mathlib 4.35: PublicSetting/Lean/OmegaOneSeparation.lean concretely constructs ω₁, the countable-cocountable measurable space, and the 0/1 probability measure using Measure.ofMeasurable. The theorem omegaOne_finite_horizon_separation packages the finite-horizon strategy-level quantifiers: every upper-tail sequence admits one global zero-loss comparator and zero randomized expected loss; every deterministic public-history learner admits one global target family forcing exactly T mistakes.
- Rocq 9.2: PublicSetting/Rocq/OmegaOneSeparation.v independently formalizes the countable-ideal, 0/1 countably additive probability, finite-series semantics, and ordered-tail game lemmas under explicit omega-one-like hypotheses. It is an abstract schema, not a concrete Rocq construction of ω₁.

Both proof assistants passed on code commit 1168ded2065bc238a1f6978b5b48addfece2dee3. The corresponding GitHub Actions run is https://github.com/2503140kcsk-eng/ai-open-problem-lean-rocq-2026/actions/runs/41157208222. The Lean and Rocq job logs were inspected: no compiler errors, no Lean warning diagnostics, and no sorry/admit/Admitted/Axiom/Parameter markers.

### Limits that remain explicit

1. The Lean theorem packages the strategy-level quantifiers for every finite horizon; the literal inf-sup minimax operator from Appendix G is not separately encoded as a Lean definition/theorem.
2. The construction uses the paper's unrestricted measurable-space model. The countable-cocountable space on ω₁ is not claimed to be standard Borel, countably generated, or sampleable by an ordinary real-valued PRNG.
3. Rocq verifies an abstract counterpart, not a concrete ω₁ construction.

These are scope limits, not outstanding compiler failures. The full mathematical strategy-level candidate is machine-checked concretely in Lean and abstractly in Rocq.

## External repository roles

The supplied repositories were inspected for suitability; they were not all executed as autonomous agents. Mathlib4 is the main formal proof library and Lean kernel environment. LeanDojo-v2 is for proof retrieval and tactic assistance, not proof certification. Naproche checks natural-language mathematical documents. cvc5 is useful for finite first-order/SMT countermodels. SageMath, SymPy, and Wolfram support finite algebraic, ordinal-toy, and numerical sanity checks. GAP is useful for finite combinatorial/group models. Macaulay2 targets commutative algebra and has little direct leverage on the ω₁ measure construction. None substitutes for the Lean/Rocq kernels.

## Sources

- Shao, Fang, Lin, Tao, Partial Feedback Online Learning, arXiv:2601.21462v3 (2026-04-02): https://arxiv.org/html/2601.21462v3
- MathOverflow, Inner Regularity of probability measure on totally ordered sets: https://mathoverflow.net/questions/343303/inner-regularity-of-probability-measure-on-totally-ordered-sets
- MathOverflow, Measure on ω₁: https://mathoverflow.net/questions/81143/measure-on-omega-1

## Verify

Lean: cd PublicSetting/Lean && lake build

Rocq 9.2: cd PublicSetting/Rocq && rocq compile -Q . PublicSetting PublicSetting.v