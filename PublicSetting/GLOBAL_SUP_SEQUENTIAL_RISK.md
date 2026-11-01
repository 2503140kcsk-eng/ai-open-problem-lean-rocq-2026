# Exact terminal global-sup reduction and sequential public-game value

**Status:** proposed formal addition to the public-setting research branch, 2026-11-01. The Lean source of record is `GlobalSupSequentialRisk.lean`; build evidence is the GitHub Actions run attached to the commit that contains this file.

## 1. Model and order of play

Let (Y=omega_1), the set of countable ordinals, with the countable-cocountable sigma algebra and probability measure
[
\mu(A)=0\quad(A\text{ countable}),\qquad
\mu(A)=1\quad(A^c\text{ countable}).
]
For each threshold (\beta\in Y), let
[
S_\beta=\{y\in Y:\beta\le y\}.
]
A round has the public information order: context (x_t), learner draw law (\pi_t), visible witness (w_t), then sample (y_t\sim\pi_t). The witness is fixed before the current draw, although future witnesses may depend on all previous realized samples.

For a finite horizon (T), an admissible global threshold vector is
[
B(w)=\{\boldsymbol\beta\in Y^T:\forall t<T,\ \beta_t\le w_t\}.
]
It determines one hypothesis family
[
F^\star_{\boldsymbol\beta}
=\{f\in Y^T:\forall t<T,\ \beta_t\le f(t)\}.
]
For every coordinate (t), the image of this *same* family is exactly (S_{\beta_t}). Indeed, every (f\in F^\star_{\boldsymbol\beta}) has (f(t)\ge\beta_t); conversely any (y\ge\beta_t) is the t-coordinate of the function taking value (y) at (t) and (\beta_s) at all other coordinates.

## 2. Exact terminal supremum theorem

The terminal loss is
[
G_T(\mathbf w,\mathbf y)
=\sup_{\boldsymbol\beta\in B(\mathbf w)}
  \sum_{t<T}\mathbf1\{y_t\notin S_{\beta_t}\}
=\sup_{\boldsymbol\beta\in B(\mathbf w)}
  \sum_{t<T}\mathbf1\{y_t<\beta_t\}.
]
Then
[
\boxed{G_T(\mathbf w,\mathbf y)
=\sum_{t<T}\mathbf1\{y_t<w_t\}.}\tag{1}
]

**Proof.** If (y_t<\beta_t\le w_t), then (y_t<w_t). Termwise, every feasible vector has loss no larger than the right-hand side of (1), so the supremum is at most that sum. Conversely, the one vector (\boldsymbol\beta=\mathbf w) is feasible, and its loss is exactly the right-hand side. Hence equality. This argument never interchanges a supremum with a sum and never selects a different global family on different rounds.

The Lean theorem `globalTailTerminalSupLoss_eq_predictableMissCount` machine-checks this identity. `globalTailFamily_projection` machine-checks that each coordinate upper tail is induced by the same function family.

## 3. Sequential conditional-risk semantics

For a public history (h), context (x), learner action (p), and pre-draw witness (w), the current slice-risk is
[
r(h,x,p,w)=\pi_p(\{y:y<w\}).
]
The section (\{y:y<w\}) is measurable and countable for every fixed (w<\omega_1), so (r(h,x,p,w)=0) when (\pi_p=\mu).

Define the finite-horizon continuation value by
[
V_0(h)=0,
]
[
V_{n+1}(h)=
\sup_x\inf_p\sup_w
\left[
\pi_p(\{y:y<w\})
+\int_Y V_n(\operatorname{Next}(h,x,p,w,y))\,\pi_p(dy)
\right].\tag{2}
]
The successor state records the entire completed public history, including the current sampled (y). The order (\sup_x\inf_p\sup_w) preserves the timing of the public protocol.

Equation (2) is an **iterated conditional-risk definition**. It does not define (V_n) by integrating the full pathwise function (G_T) over a product sigma algebra. At each node, it integrates only the current-draw section and the already-defined continuation risk. In the particular construction below, backward induction makes the continuation integrand identically zero at every node; hence it is measurable as a constant function even if the history-to-successor map is not measurable.

**Backward induction.** Suppose (V_n(h)=0) for every history (h). Choose the learner action (p_0) whose draw law is (\mu). For every context (x) and every witness (w), the bracket in (2) is
[
\mu(\{y:y<w\})+\int_Y0\,d\mu=0+0=0.
]
Thus the learner can force the upper value to zero. Since every term is nonnegative, (V_{n+1}(h)=0). The base case is immediate. Therefore
[
\boxed{V_n(h)=0\quad\text{for every finite }n\text{ and every }h.}
]
The Lean declarations `publicGlobalSupBellmanStep_eq_zero_of_policy`, `publicGlobalSupGameValue_eq_zero`, and `omegaOne_publicGlobalSupGameValue_eq_zero` machine-check this recursion and induction.

## 4. Why this avoids the product-measurability obstruction

The relation (E=\{(w,y):y<w\}\) is not measurable in the product of two countable-cocountable sigma algebras: its vertical sections are countable, while its horizontal sections are cocountable, contradicting Tonelli if it were product-measurable. Thus one cannot simply integrate the joint pathwise loss as an ordinary product-measurable random variable.

The recursion above uses a different semantic object:
- for each fixed history and pre-draw witness, the one-dimensional section (\{y:y<w\}) is measurable and null;
- the full terminal global supremum is reduced pathwise by (1);
- its sequential value is then defined by composing these one-step section-risks in the actual information order.

No sigma algebra on the space of all public histories or full paths is used in the zero-value induction. This is a sequential/iterated risk semantics, not a claim that the nonmeasurable full-path indicator has acquired an ordinary expectation.

## 5. Deterministic lower bound

For a deterministic learner, after the current context and its deterministic prediction (\hat y_t) are known, the public adversary can set
[
w_t=\operatorname{succ}(\hat y_t).
]
Then (\hat y_t<w_t) at every round. Choosing the single global threshold vector (\beta_t=w_t) makes the terminal supremum equal to (T) by (1). The existing omega-one separation development in `OmegaOneSeparation.lean` supplies the corresponding global realizability and deterministic pathwise lower-bound construction.

Thus, in this abstract measurable-space / sequential-risk model, the candidate has randomized public value (0) and deterministic worst-case terminal loss (T).

## 6. Scope and non-claims

1. This is not a theorem that every public partial-feedback game has a recursive value without regularity assumptions. General continuations still require their one-step sections to be integrable/measurable (or a separately specified upper-risk convention).
2. It does not prove that the countable-cocountable probability on (\omega_1) can be sampled by a finite-bit PRNG or pushed forward from a countable seed space. The repository's RNG no-go result explicitly rules out countable-range exact sampling.
3. It is not a standard-Borel construction. Requiring standard-Borel label spaces or ordinary implementable randomization changes the problem and is not settled by this candidate.
4. The sequential value is deliberately distinct from ordinary expectation of a full-path payoff when that payoff is nonmeasurable. The result applies under the paper's broad measurable-space abstraction only when the game value is interpreted with this iterated conditional-risk semantics.
5. Minimax interchange is not needed for the zero upper bound: one fixed learner action (p_0=\mu) is a witness to the infimum. Any broader minimax theorem still needs the compactness, convexity, and semicontinuity hypotheses recorded in `SequentialKernelMinimax.lean`.

## 7. Tool responsibilities

The existing `TOOL_ROLES.md` assigns the trusted proof to Lean/Mathlib and an independent foundational audit to Rocq/Gaia; SymPy/Sage/Wolfram/cvc5/GAP are sidecar finite-example or counterexample tools; Naproche audits prose; LeanDojo suggests Mathlib lemmas; Context7 checks current APIs; Parallel Search and Sider Scholar retrieve literature; GitHub Actions validates the exact commit. Macaulay2 has no relevant algebraic task in this theorem and is intentionally not a dependency. These tools are not all invoked as build dependencies.
