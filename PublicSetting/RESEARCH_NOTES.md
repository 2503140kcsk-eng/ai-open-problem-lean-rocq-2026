# Research notes: public-setting randomized/deterministic separation

Date: 2026-10-28

## Exact question

Find either (A) a public partial-feedback online-learning game with a fixed hypothesis class H and a single global target subfamily F such that randomized minimax regret is o(T) and every deterministic learner has Ω(T) minimax regret, or (B) a theorem ruling out every such construction.

The horizon quantifier matters. A result for one finite T does not establish asymptotic learnability. The sublinear upper bound must hold for all sufficiently large horizons with ratio regret/T tending to zero; the deterministic lower bound must hold with one positive constant (possibly depending on the deterministic learner if that is the chosen quantifier convention) for all sufficiently large horizons.

## Literature audit

Primary source: Shihao Shao, Cong Fang, Zhouchen Lin, Dacheng Tao, “Partial Feedback Online Learning,” arXiv:2601.21462v3, dated 2026-04-02. Section 3.3 explicitly says the existence of a randomized/deterministic learnability separation under the public setting remains open. The same paper gives a different result: randomized learnability under the oblivious setting can fail to persist under the public setting (Theorem 18). The two statements must not be conflated.

- Paper: https://arxiv.org/abs/2601.21462
- HTML source: https://arxiv.org/html/2601.21462v3
- Related set-valued feedback paper: https://proceedings.mlr.press/v247/raman24b.html

A fresh search on 2026-10-28 did not find a later publication resolving the exact public-setting question. Search absence is not mathematical proof of open status.

## Why the global target matters

For one fixed target family F ⊆ H, the acceptable set at context x is the image {h(x) | h ∈ F}. A valid construction has to use the same F at every round. Merely selecting a different consistent hypothesis after each round is not sufficient.

The formal model in PublicSetting.lean and PublicSetting.v states this constraint. The complement-of-singleton instance uses H = ℕ^ℕ and a single family F = {h | for all t, h(t) ≠ excluded(t)}. It proves that all allowed sets are induced by this one family, and that a path equal to excluded labels loses exactly T for each horizon T.

## What has and has not been proved

Proved in source, subject to the CI actually passing:

1. An integer-scaled definition of sublinear and linear natural-valued regret.
2. A proof that one and the same regret profile cannot be both sublinear and linear.
3. Global consistency of the complement-of-singleton example for one fixed target family across all rounds.
4. An all-horizons calculation that a path matching the excluded labels incurs exactly T losses.

Not proved:

1. That the pathwise complement-of-singleton construction is an online adversary witnessing a lower bound for every deterministic policy under the exact timing rules.
2. Any o(T) regret upper bound for a randomized learner on a globally consistent target family in the public setting.
3. The requested randomized-versus-deterministic separation, or a no-go theorem.

The last two are the open mathematical core. The source intentionally contains no admitted proof, sorry, axiom, or fabricated existence theorem.

## Next mathematical step

The protocol is now modeled operationally: contexts and visible labels are chosen before the current random draw; both the learner and public adversary can inspect completed previous predictions, but neither sees hidden sets or correctness bits; and one global target family constrains all rounds. This models the information order, but it does not yet define probability measures and minimax regret at the full generality of the paper. The next mathematical step remains to define that quantitative semantics and prove either a randomized o(T) upper bound plus a deterministic Ω(T) lower bound, or an impossibility theorem. The profile predicates alone do not bridge this semantic gap.

## Construction audit: why the obvious separation example does not transfer

The classical set-valued-feedback separation of Raman, Subedi, and Tewari (PMLR 247, 2024), Section 4.1, uses `Y = ℕ`, co-singleton sets `A_y = ℕ \\ {y}`, and constant hypotheses `h_y(x)=y`. A deterministic learner can be made wrong every round by choosing `A_{p_t}` after observing its deterministic prediction (p_t); the intersection of finitely many co-singleton sets is nonempty, while a learner uniform on `[T]` has expected loss at most one in total.

That proof is not itself a public **set-realizable partial-feedback** separation: for a fixed subfamily (F^\star) of constant hypotheses, the induced set (F^\star(x)) is the same at every context. The deterministic construction needs different exclusions (p_t) across rounds. The new Lean/Rocq lemma `constant_hypothesis_complement_exclusion_is_fixed` machine-checks this obstruction: if one constant-hypothesis family induces the co-singleton `Y \\ {excluded(t)}` at every round, then `excluded` must be constant.

The opposite extreme, the full product class (H=\mathbb N^{\mathbb N}), has enough coordinate freedom to let the terminal target family avoid every realized prediction while accepting each pre-draw witness. The existing bounded-support public attack formalizes this failure of randomized learning in that submodel. Thus neither the constant class from set-valued feedback nor the full product class yields the required public separation.

A valid positive construction would need an intermediate hypothesis class: enough adaptive structure for every deterministic learner to incur linear loss, but insufficient coordinate freedom for a public adversary to tailor a globally consistent target family to a randomized path. The current literature search and formal work have not established such a class or a theorem ruling it out. This is the remaining mathematical gap, not a Lean/Rocq build failure.

## Low-mass witness obstruction for the full product class

A low-mass witness obstruction is now partly machine-checked. In `PublicSetting/Lean/PublicProtocol.lean`, `NatSubprobability` models nonnegative rational atom masses whose every finite prefix sums to at most one. Lean proves that if every atom in a prefix of length N has (T\,p_i>1), then the scaled prefix sum exceeds N, and therefore `exists_low_mass_label`: for every natural-number horizon T (in particular T≥1), some label y satisfies (T\,p_y\le1). This is the discrete atom-existence fact needed by the public adversary; the corresponding auxiliary theorem has not yet been duplicated in Rocq.

For the full product class \(H=\mathbb N^{\mathbb N}\), the independently machine-checked Lean/Rocq terminal-target construction can then be selected from the completed prediction path. Its pathwise loss equals the number of rounds with \(\hat y_t\ne y_t^{\rm vis}\); because the witness is chosen before the current sample with mass at most (1/T), the conditional expected loss on each round is at least (1-1/T\), giving expected cumulative loss at least \(T-1\). The target family remains globally consistent, and the visible-witness comparator has zero loss. The probability-measure/conditional-expectation argument is not yet a machine-checked theorem; only the atom-existence lemma in Lean and the pathwise/global-consistency construction in both provers are checked.

This reinforces the boundary diagnosis: neither the full product class nor the constant-function class is the desired separating class. A positive separation would need an intermediate hypothesis class whose global target constraint prevents the adversary from adapting the acceptable set to the sampled path, while still permitting linear deterministic lower bounds.


## Generalized terminal-target boundary result

In addition to the bounded-support special case, the Lean/Rocq protocol modules now parameterize an arbitrary realized prediction path and visible-witness path. The final exclusion at round t is the prediction whenever prediction and witness differ, and otherwise a different label. The target subfamily is one global family of functions avoiding that complete exclusion path. The proofs show all visible witnesses are accepted and the resulting pathwise loss gap equals the number of non-collision rounds. This makes the full-product attack's logic independent of any assumed support bound; it still does not give a randomized upper bound for any structurally restricted class.
