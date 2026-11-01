# Stagewise conditional-risk semantics and the Appendix G Bellman operator

**Status: formalized as a separate semantics; not claimed to solve the paper's public randomized-vs-deterministic open problem.**

## 1. Source problem and protocol

The motivating source is Shao, Fang, Lin, and Tao, *Partial Feedback Online Learning*, arXiv:2601.21462v3. The public protocol reveals a visible acceptable witness before the current draw, while the public adversary may use previously realized draws. The final evaluation still requires one global target family, not unrelated acceptable sets chosen independently at each round.

The Appendix G recursion is for the set-valued feedback comparison between public and oblivious adversaries. It should not be conflated with the distinct final question in the paper about a randomized-vs-deterministic learnability separation in the public setting.

## 2. Joint measurability criterion

Let (H, Σ_H) and (Y, Σ_Y) be measurable spaces, let R be a subset of Y × Y, and let w : H → Y be an adaptive policy. Define

    E_w = { (h,y) | (w(h),y) ∈ R }.

The map Φ(h,y) = (w(h),y) is measurable whenever w is measurable. Therefore:

- If R belongs to Σ_Y ⊗ Σ_Y, then E_w = Φ⁻¹(R) is measurable.
- For the self-policy case H = Y, if measurability is required for every measurable policy and in particular the identity policy, then R itself must be product-measurable.

Thus measurability of the policy alone is not enough. The base relation must also be product-measurable. The Lean theorem all_measurable_self_policies_iff formalizes the necessary-and-sufficient statement for this universal self-policy formulation.

The omega-one construction illustrates why this matters: individual history sections can be measurable null sets while a joint order relation on the product of countable-cocountable spaces is not product-measurable. Sectionwise nullity must not be used as a substitute for joint measurability.

## 3. Stagewise conditional-risk semantics

For each time t, let h be a public history, μ_t(h) the current draw law, w_t(h) a witness fixed before the current draw, and θ_t(h,y) a terminal threshold rule that may depend on the realized current label y.

Define the one-step error section and conditional risk by

    B_t(h) = { y | not (θ_t(h,y) ≤ y) }
    ρ_t(h) = μ_t(h)(B_t(h)).

Assume the pre-draw envelope condition

    for every h and y: θ_t(h,y) ≤ w_t(h)

and the local null-prefix condition

    μ_t(h)({y | y < w_t(h)}) = 0.

If y belongs to B_t(h), then θ_t(h,y) is not ≤ y, while θ_t(h,y) ≤ w_t(h). By linear-order trichotomy and transitivity, y < w_t(h). Thus B_t(h) is contained in the null initial segment, and ρ_t(h)=0.

For any finite history sequence (h_0, ..., h_{T-1}), define

    R_seq(T) = sum_{t<T} ρ_t(h_t).

Then R_seq(T)=0. This definition uses only one-step sections at the supplied histories; it does not construct a full-path error event. The Lean declarations are in SequentialConditionalRisk.lean; Rocq has the corresponding abstract ordered-type/countable-ideal theorem in OmegaOneSeparation.v.

This is intentionally a separate evaluation semantics. It is not automatically equal to the conventional expected cumulative loss on trajectory space. Such an identification requires a measurable stochastic process / kernel and the appropriate conditional-expectation and tower-property hypotheses.

## 4. Appendix G and the adaptive Bellman extension

The set-valued Appendix G recursion has the schematic form

    V_T(h) = 0
    V_t(h) = sup_x inf_p sup_{s ∈ Feasible(h,x,p)}
             [ r(h,x,p,s) + V_{t+1}(next(h,x,p,s)) ]

where r is the current expected one-step loss and the feasible feedback object is constrained by the same globally realizable target family.

When the next public state can depend on the current sampled label, replace the deterministic continuation term by integration against the current draw law:

    (B_t V)(h) = sup_x inf_p sup_{s ∈ Feasible(h,x,p)}
       [ ρ_t(h,x,p,s) + ∫ V(nextPublic(h,x,p,s,y)) p(dy) ].

The file formalizes both operators and proves the reduction theorem: if nextPublic is independent of y and the current draw measure has total mass one, the integral is exactly the value at the deterministic successor state. When the stage loss is the draw probability of the complement of the acceptable set, this reduces to the set-valued Appendix G operator.

This is an operator-level connection, not a blanket minimax interchange theorem. To interchange infimum and supremum using Sion, one must additionally prove nonempty convex strategy sets, compactness of the appropriate strategy set, and the required lower/upper semicontinuity and quasi-convexity/quasi-concavity conditions. Kernel measurability alone does not give those hypotheses.

## 5. Verified and unverified boundaries

Verified by the Lean 4.35 / Mathlib 4.35 CI before the latest Rocq-only extension:

- the universal self-policy product-measurability criterion;
- the omega-one one-step miss-section containment and null-risk argument;
- the finite sum of stagewise conditional risks;
- the Appendix G Bellman operator and the sample-independent-continuation reduction;
- the existing sequential-kernel, finite-prefix, tower, and Sion interface modules.

The Rocq sequential conditional-risk counterpart now also passes CI (workflow run #599). The concrete omega-one probability space is still Lean/Mathlib-specific; the Rocq development uses an abstract ordered type with countable-ideal / omega-one-like assumptions. Lean and Rocq do not share a concrete ordinal implementation: Rocq verifies the abstract order/ideal theorem.

Important model boundary: the countable-cocountable probability space on ω₁ is not asserted to be standard Borel or implementable by an ordinary real-valued PRNG. It belongs to the broad measurable-space model considered by the paper. A result under standard-Borel or algorithmic-sampling restrictions would need a separate construction or impossibility proof.

Accordingly, no claim is made here that the paper's open randomized-vs-deterministic public-setting question has been solved. What is proved is a product-measurability criterion, a distinct stagewise conditional-risk theorem, and an exact reduction from the adaptive Bellman extension to the Appendix G set-valued recursion under its sample-independent continuation condition.
