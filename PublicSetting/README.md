# Public-setting separation in partial-feedback online learning

Status date: 2026-10-28

## Research question

For partial-feedback online learning in the public setting, does there exist one fixed hypothesis class and one globally consistent target subfamily such that:

- the randomized learner has minimax regret o(T); and
- every deterministic learner has minimax regret Ω(T),

as the horizon T tends to infinity?

Here o(T) means sublinear regret: regret divided by T tends to zero. Ω(T) means a positive constant fraction of T for all sufficiently large horizons. “Globally consistent” means that the acceptable label set at every context is induced by the same target subfamily F of a single hypothesis class H; it is not permissible to choose unrelated target hypotheses independently at each round.

## Literature status

The latest version found for this audit is Shao, Fang, Lin, and Tao, “Partial Feedback Online Learning,” arXiv:2601.21462v3 (posted 2026-04-02). The final paragraph of Section 3.3 explicitly leaves open whether randomized and deterministic learnability can separate in the public setting. Theorem 17 in Section 3.3 establishes equality between oblivious and public settings for set-valued feedback. Theorem 18 establishes a different result: randomized learnability in the oblivious partial-feedback setting need not imply learnability in the public partial-feedback setting. Neither result answers the open randomized-versus-deterministic question within the public setting.

Source: https://arxiv.org/html/2601.21462v3

A search performed on 2026-10-28 did not find a later paper resolving this exact question. This is a bounded literature check, not a proof that no result exists anywhere.

## What is formalized here

The Lean and Rocq files are independent developments. They formalize:

1. Exact asymptotic specifications for natural-number regret profiles.
2. The elementary but useful fact that one and the same nonnegative regret profile cannot be both o(T) and Ω(T).
3. A global-consistency model in which one fixed subfamily F of H induces every accepted-label set.
4. An all-horizons pathwise construction for complement-of-singleton accepted sets, and the fact that a prediction path equal to the excluded labels incurs exactly T losses over horizon T.
5. Machine-checked low-mass atom lemmas in both provers: Lean uses nonnegative rational masses with every finite prefix bounded by one; Rocq uses an integer-scaled encoding with every finite prefix bounded by denominator D. Each proves the corresponding atom-mass bound of 1/T for every positive integer horizon.

All stated lemmas are intended to be proved without placeholders. The complement-of-singleton construction is a boundary-case / adversarial-path lemma; it is **not** a randomized-versus-deterministic separation. It does not establish that any randomized learner has o(T) regret in the public protocol.

## What remains open in this repository

The main separation is **not proved** here. The operational model now records the learner's own previous sampled predictions and gives the public adversary access to all completed previous rounds, while keeping current-round sampling hidden until after the visible witness is chosen. It also enforces one global target subfamily. The remaining bridge is to define and verify probability measures, the paper's exact minimax-regret semantics, connect the discrete low-mass lemmas to conditional expected loss, and then prove a construction or impossibility theorem for every horizon T. The asymptotic profile predicate below is only a specification, not evidence that a game realizes those profiles.

No theorem named “exists separation” is declared or assumed. No axiom, sorry, or admitted step is used to pretend the open problem is solved.

## Verify

Lean (from the repository root):

    cd PublicSetting/Lean
    lake build

Rocq (from the repository root):

    cd PublicSetting/Rocq
    rocq compile -Q . PublicSetting PublicSetting.v

The GitHub Actions workflow runs both independent builds. A passing build verifies only the theorem statements actually present in these files, not the open separation claim.

## Reproducibility

The Lean subproject pins its Lean toolchain. The Rocq workflow pins a versioned official prover image. The Lean and Rocq sources do not import, generate, or trust one another.


## Omega-one candidate added on 2026-10-31

A concrete candidate has been added to the Lean project.

- Label space: Y = omega_1, the first uncountable ordinal.
- Sigma algebra: all countable or cocountable subsets of Y.
- Probability measure: zero on countable sets and one on cocountable sets.
- Admissible acceptable sets: upper tails S_beta = {y : beta <= y}.
- Instance space: natural numbers.
- Hypothesis class: all functions from natural numbers to Y.

Every initial segment below a countable ordinal is countable. Therefore every admissible upper tail has measure one.

Randomized side: use this probability measure as the learner's distribution on every round. If the visible witness is w_t, every terminal acceptable tail compatible with that witness has threshold beta_t <= w_t. A mistake implies prediction < beta_t <= w_t. Thus the error event is contained in the countable null initial segment below w_t. This remains true when the terminal target family is selected after all sampled predictions, because the containment holds pointwise for every possible terminal choice.

Deterministic side: for any deterministic prediction path p_t, choose the visible witness and tail threshold to be the successor p_t+1. One global target family F* consists of all functions f with f(t) >= p_t+1 at every coordinate. This family is nonempty and induces exactly the required upper tail at each context. It contains every visible witness while excluding the deterministic prediction, so the path incurs exactly T mistakes.

Theorem 15 (and its set-valued analogue, Corollary 16) does not cover this family. The full family of upper tails has empty intersection, but every countable subfamily has nonempty intersection by countable boundedness of omega_1, and every finite subfamily has nonempty intersection. Thus neither Theorem 15 condition (1), a countable decreasing sequence with empty intersection, nor condition (2), a finite subfamily with empty intersection, is satisfied.

Model boundary: this uses the paper's abstract model allowing arbitrary probability measures on a measurable label space. The countable-cocountable space is not claimed to be standard Borel, countably generated, or implementable by an ordinary real-valued PRNG. A stronger standard-Borel or implementable-sampling restriction requires a separate analysis.

## Current formal verification status

- Lean/OmegaOneSeparation.lean contains the concrete omega_1 label space, countable-cocountable measurable space, 0/1 probability measure through Measure.ofMeasurable, null-miss result, countable tail-intersection result, and globally realizable deterministic lower-bound construction.
- Rocq/OmegaOneSeparation.v proves the same measure and game lemmas for an abstract ordered label structure equipped with a countable ideal, countable initial segments, successors, and countable boundedness. It is an abstract theorem schema, not a concrete Rocq encoding of omega_1.
- The latest GitHub Actions runs for these new modules remain queued. No completed CI result has yet been verified. Do not treat source upload or a queued workflow as a machine-checked proof.

## Remaining tasks

1. Obtain and inspect successful Lean and Rocq 9.2 CI runs for the new modules.
2. Formalize the final wrapper connecting the roundwise zero-error lemma and deterministic pathwise lower bound to the exact public sequential minimax expression.
3. Decide whether the intended problem permits arbitrary measurable label spaces and all countably additive measures. Under that model, the candidate implies randomized regret zero and deterministic regret T. Under additional standard-Borel or implementable-sampling restrictions, this result does not automatically apply.
