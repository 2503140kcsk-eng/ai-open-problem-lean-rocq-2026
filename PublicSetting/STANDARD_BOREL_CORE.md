# Standard-Borel core obstruction: a model-independent theorem

**Status (2026-10-31):** a complete measure-theoretic theorem and a Lean formalization target are added. The public randomized-versus-deterministic separation problem itself remains open; this note does not claim otherwise.

## 1. The result

Let (Y,B) be a standard Borel space, let μ be a probability measure on B, and let Θ be another standard Borel space. Suppose M ⊆ Θ × Y is Borel and define
S_θ = { y ∈ Y : (θ,y) ∈ M }.
For y ∈ Y, define the core section
C_y = ⋂_{θ : y ∈ S_θ} S_θ.
Thus x ∈ C_y means that every admissible set which can reveal y must also contain x.

Assume the uniform section-risk bound
  sup_y μ(Y \ C_y) ≤ ε < 1/2.
Then there exists x₀ ∈ Y such that
  for every θ, S_θ ≠ ∅ implies x₀ ∈ S_θ.
The point x₀ is a deterministic universally acceptable prediction.

The same result can be stated without Θ: put R(x,y) iff x ∈ C_y. It is a transitive relation, and the risk bound says each incoming section C_y = {x : R(x,y)} has measure at least 1 - ε > 1/2. The proof below only uses product measurability of R, transitivity, and the probability measure.

## 2. Full proof

### 2.1 The measurable relation

The complement of R is
  Rᶜ = {(x,y) : exists θ, y ∈ S_θ and x ∉ S_θ}.
The set
  D = {(x,y,θ) : (θ,y) ∈ M and (θ,x) ∉ M}
is Borel in Y × Y × Θ, and Rᶜ is its projection onto Y × Y. By the Suslin projection theorem, Rᶜ is analytic, hence R is coanalytic. Analytic and coanalytic subsets of a standard Borel space are universally measurable. In particular, R is measurable in the completion of the product probability space (Y × Y, B ⊗ B, μ ⊗ μ). Every section C_y is coanalytic as well, and is therefore measurable in the completion of μ.

Consequently Fubini/Tonelli applies to the indicator of R on the completed product space. This is the exact point at which standard Borel regularity enters. It is not legitimate to replace this step by the assertion that all sections are measurable: sectionwise measurability alone does not imply product measurability.

### 2.2 Transitivity

If x ∈ C_z and z ∈ C_y, then every admissible set S_θ containing y also contains z, and hence contains x. Therefore
  x ∈ C_z and z ∈ C_y imply x ∈ C_y.
Equivalently, R is transitive.

### 2.3 Fubini produces a large outgoing section

Write
  a(x) = μ({y : R(x,y)}),   b(y) = μ({x : R(x,y)}).
By (1), b(y) ≥ 1 - ε > 1/2 for every y. Fubini gives
  ∫ a(x) μ(dx) = ∫ b(y) μ(dy) ≥ 1 - ε > 1/2.
Therefore there is x₀ ∈ Y with a(x₀) > 1/2. Otherwise a(x) ≤ 1/2 everywhere and its integral would be at most 1/2, a contradiction.

### 2.4 Every incoming section intersects the selected outgoing section

Fix y ∈ Y. We have
  μ({z : R(x₀,z)}) > 1/2,
  μ({z : R(z,y)}) ≥ 1 - ε > 1/2.
For any two measurable subsets A,B of a probability space,
  μ(A ∩ B) ≥ μ(A) + μ(B) - 1.
Thus the two displayed sections have intersection of positive measure. Choose z in their intersection. Then R(x₀,z) and R(z,y), and transitivity yields R(x₀,y).

Since y was arbitrary, x₀ ∈ C_y for every y. If S_θ is nonempty, choose y ∈ S_θ; then x₀ ∈ C_y ⊆ S_θ. This proves the result. □

## 3. The exact scope of the Lean theorem

Lean/StandardBorelCore.lean formalizes the model-independent Fubini and transitivity core. It takes as input a product-measurable relation R, a probability measure μ, a number c₁ > 1/2, and the section-mass premise
  for every y, c₁ ≤ μ({x : R(x,y)}).
It proves
  there exists x₀ such that for every y, R(x₀,y).
The proof uses Mathlib's product-measure Fubini formulas and the finite-measure intersection identity. No ordinal, nonstandard model, or pseudorandom generator is involved.

The formal Lean file deliberately states product measurability as an explicit input. The standard-Borel bridge above supplies it by passing to the completion of μ ⊗ μ, after applying the analytic/coanalytic universal-measurability theorem. The file does not pretend that a Borel relation is automatically obtained: the core relation is generally coanalytic, not necessarily Borel.

## 4. Consequence for the proposed separation

This rules out a direct standard-Borel transplant of the ω₁ strategy that has a uniform, every-history, every-visible-witness section risk below one half, provided the terminal acceptable-set family is Borel-parametrized as above. Such a strategy would imply a deterministic label accepted by every nonempty terminal acceptable set.

It does not prove that randomized and deterministic public learners have equal minimax regret in every standard-Borel problem. In particular, it does not rule out constructions where:
- the uniform section-risk bound fails;
- the acceptable-set correspondence is not Borel/analytic in the stated sense;
- the risk guarantee is only averaged over histories rather than uniform over all histories;
- the adversary's final target family is constrained by additional pathwise conditions not captured by a single fixed relation R.

Nor does the theorem exchange sup and expectation. The order
  sup_{θ : y ∈ S_θ} ∫ 1_{x ∉ S_θ} dμ(x)
versus
  ∫ sup_{θ : y ∈ S_θ} 1_{x ∉ S_θ} dμ(x)
must remain explicit. The latter can be one even when each fixed-set expectation is zero.

## 5. Relation to the sequential kernel and minimax modules

The existing SequentialKernelMinimax.lean remains the right formalization for a jointly measurable adaptive stochastic process:
- Kernel.traj constructs the full trajectory law from arbitrary history-dependent Markov kernels;
- traj_comp_partialTraj gives finite-prefix consistency;
- condExp_traj gives the continuation-kernel conditional expectation, almost everywhere, for integrable full-path rewards;
- Sion.minimax supplies a separate inf-sup equality only after its compactness, convexity, semicontinuity, and quasi-convexity/quasi-concavity hypotheses are supplied.

The new core theorem does not bypass these hypotheses. Its role is to identify an obstruction before attempting the full-path construction: a uniformly small, universally measurable core-risk guarantee already forces a safe deterministic point.

For the public partial-feedback protocol, a full minimax regret identity still requires the single globally realizable terminal family and the correct move order. Stagewise conditional risk and conventional full-path expected loss are identified only when their measurability and tower hypotheses are proved.

## 6. Asymptotic bounds: what is and is not universal

There is no distribution-free theorem giving an o(T) randomized upper bound for every hypothesis class and every adaptive adversary. The paper itself gives regimes where minimax regret is linear. Conversely, a generic Ω(T) lower bound is not true for every class: a single universally correct hypothesis gives zero regret.

The valid general statement is conditional:
- a proved horizon-uniform estimate R*_rand(T) ≤ g(T) with g(T)/T → 0 establishes randomized learnability;
- a proved estimate R*_det(T) ≥ cT for all sufficiently large T, with fixed c > 0, establishes deterministic non-learnability.

Neither asymptotic premise follows from standard Borel structure, kernel existence, or the tower property alone. They must be obtained from additional combinatorial/complexity assumptions on the hypothesis class and the feasible globally realizable target families.

## 7. Sources

- Shao, Fang, Lin, Tao, Partial Feedback Online Learning, arXiv:2601.21462v3, especially Definition 1, Section 5.3, and Appendix G: https://arxiv.org/html/2601.21462v3
- Mathlib 4.35, product measure and Tonelli/Fubini: https://github.com/leanprover-community/mathlib4/blob/v4.35.0/Mathlib/MeasureTheory/Measure/Prod.lean
- Mathlib 4.35, Kernel.traj and Kernel.condExp_traj: https://github.com/leanprover-community/mathlib4/blob/v4.35.0/Mathlib/Probability/Kernel/IonescuTulcea/Traj.lean
- Kechris, Classical Descriptive Set Theory, analytic sets and the Suslin projection theorem.
