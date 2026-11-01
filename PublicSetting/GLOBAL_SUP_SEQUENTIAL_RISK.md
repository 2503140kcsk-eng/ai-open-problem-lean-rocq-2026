# Exact terminal global-sup reduction and sequential public-game value

**Date:** 2026-11-01  
**Status:** formalized in Lean 4.35 / Mathlib 4.35; CI verified together with Rocq 9.2.

## 1. Public protocol and a horizon-independent hypothesis class

Let \(Y=\omega_1\), the set of all countable ordinals, with the countable-cocountable sigma algebra and probability measure
\[
\mu(A)=
\begin{cases}
0,&A\text{ is countable},\\
1,&A^c\text{ is countable}.
\end{cases}
\]
For \(\beta\in Y\), define the acceptable upper tail
\[
S_\beta=\{y\in Y:\beta\le y\},\qquad
L_\beta=Y\setminus S_\beta=\{y:y<\beta\}.
\]
Every \(L_\beta\) is countable, measurable, and has \(\mu(L_\beta)=0\).

Fix the hypothesis domain once and for all:
\[
H=Y^{\mathbb N}.
\]
For each infinite threshold sequence \(\boldsymbol\beta\in Y^{\mathbb N}\), let
\[
F^\star_{\boldsymbol\beta}
=\{f\in H:\forall t\in\mathbb N,\ \beta_t\le f(t)\}.
\]
This is one global family of hypotheses. At context \(t\), its image is exactly \(S_{\beta_t}\):
\[
\{f(t):f\in F^\star_{\boldsymbol\beta}\}=S_{\beta_t}.
\]
The forward inclusion follows from the defining constraint. For the reverse inclusion, if \(y\ge\beta_t\), choose the single function \(f\) with \(f(t)=y\) and \(f(s)=\beta_s\) for \(s\ne t\). Thus the same family induces all the roundwise acceptable sets. The hypothesis class is not changed with the horizon.

The public order of play is: choose current context \(x_t\); learner chooses its sampling law \(p_t\); adversary reveals a witness \(w_t\) before the current draw; Nature samples \(y_t\sim p_t\); the completed sample becomes visible to the adversary in later rounds. At the end, the one global family \(F^\star\) must induce all acceptable sets and contain every revealed witness.

For a finite horizon \(T\), the feasible finite threshold vectors are
\[
B_T(\mathbf w)=
\{\boldsymbol\beta\in Y^T:\forall t<T,\ \beta_t\le w_t\}.
\]
Every such vector is the first-\(T\)-coordinate restriction of an infinite sequence in \(Y^{\mathbb N}\), and hence of one global hypothesis family.

## 2. Exact terminal supremum theorem

The terminal global loss is
\[
G_T(\mathbf w,\mathbf y)
=\sup_{\boldsymbol\beta\in B_T(\mathbf w)}
\sum_{t<T}\mathbf1\{y_t\notin S_{\beta_t}\}
=\sup_{\boldsymbol\beta\in B_T(\mathbf w)}
\sum_{t<T}\mathbf1\{y_t<\beta_t\}.
\]
The exact identity is
\[
\boxed{
G_T(\mathbf w,\mathbf y)
=\sum_{t<T}\mathbf1\{y_t<w_t\}.
}
\tag{1}
\]

**Proof.** For every feasible vector, \(y_t<\beta_t\le w_t\) implies \(y_t<w_t\), so its sum is bounded above by the right side of (1). Conversely, choose the one vector \(\boldsymbol\beta=\mathbf w\). It is feasible and attains exactly the right side. The vector is a single global choice, and its associated \(F^\star_{\boldsymbol\beta}\) is one global family in the fixed domain \(Y^{\mathbb N}\). No exchange of supremum and summation occurs, and no roundwise family is substituted for the global one.

Lean declarations:
- **globalHypothesisFamily** and **globalHypothesisFamily_projection** define one actual global target family \(F^\star_\beta\subseteq H\) for each infinite threshold sequence and prove that its coordinate image is \(S_{\beta_t}\).
- **globalHypothesisTerminalSupLoss** takes the terminal supremum directly over all feasible infinite sequences \(\beta\in Y^{\mathbb N}\), i.e. over one horizon-independent global family at a time.
- **globalHypothesisTerminalSupLoss_eq_predictableMissCount** proves identity (1) for that literal infinite-family supremum.
- **globalTailFamilyOnNat_projection** and **globalTailTerminalSupLoss_eq_predictableMissCount** provide the finite-prefix representation as an additional equivalent check.

In the paper's notation, the admissible acceptable-set family is \(\mathcal S(Y)=\{S_\beta:\beta\in Y\}\) and the collection-version-space universe is \(\tilde H=\mathcal P(H)\). Any terminally compatible \(F^\star\subseteq H\) induces a sequence of upper tails \(S_{\beta_t}\); conversely, for every feasible sequence \(\beta\) the concrete set \(F^\star_\beta\) above realizes all those tails simultaneously. Since terminal loss depends only on the coordinate images \(F^\star(t)\), optimizing over all compatible subsets \(F^\star\in\mathcal P(H)\) has exactly the same value as optimizing over the feasible global sequences \(\beta\).

## 3. Sequential conditional-risk value

A public history \(h\) contains all completed public information, including previous realized samples. Let \(\operatorname{Next}(h,x,p,w,y)\) denote the next complete history after current context \(x\), learner action \(p\), pre-draw witness \(w\), and draw \(y\). Define the stagewise section-risk
\[
r(p,w)=p(L_w)=p(\{y:y<w\}).
\]
The section \(L_w\) is measurable for every fixed \(w<\omega_1\). The witness is selected before \(y\), so this is exactly the current-round conditional error risk under identity (1).

Define the finite-horizon public value recursively:
\[
V_0(h)=0,
\]
\[
V_{n+1}(h)=
\sup_x\inf_p\sup_{w\in Y}
\left[
p(L_w)+
\int_Y V_n(\operatorname{Next}(h,x,p,w,y))\,p(dy)
\right].
\tag{2}
\]
The order \(\sup_x\inf_p\sup_w\) is the actual public protocol order: context, learner law, then visible witness, then sample. The continuation state records the draw and the full public history.

This is an **iterated sequential-risk definition**. It is not defined as an integral of a full-path payoff on the product space \(Y^T\). Its one-step risk uses only the measurable section \(L_w\) at the current public node. For the candidate below the continuation value is identically zero, making the continuation integrand a constant measurable function even if \(\operatorname{Next}\) is not measurable as a function on a global history/path space.

### Zero-value theorem

Use the same learner law \(p_0=\mu\) after every history. For every possible pre-draw witness \(w\),
\[
p_0(L_w)=\mu(L_w)=0.
\]
Induction proves \(V_n(h)=0\) for every \(n\) and every history \(h\).

- Base: \(V_0=0\) by definition.
- Inductive step: assume \(V_n\equiv0\). Under the single learner action \(p_0\), for every \(x,w\) the bracket in (2) equals
  \[
  \mu(L_w)+\int_Y0\,d\mu=0.
  \]
  Thus the learner's infimum is at most zero. All risks are nonnegative, so the value is exactly zero.

Consequently,
\[
\boxed{V_n(h)=0\quad\text{for all }n<\infty\text{ and all public histories }h.}
\]
This proof does not exchange a supremum and an integral and does not invoke Sion's theorem. A single explicit learner action gives the upper bound; nonnegativity gives the matching lower bound.

Lean declarations **publicGlobalSupBellmanStep_eq_zero_of_policy**, **publicGlobalSupGameValue_eq_zero**, and **omegaOne_publicGlobalSupGameValue_eq_zero** check the Bellman step, finite-horizon induction, and concrete \(\omega_1\) specialization.

## 4. Why full product measurability is unnecessary here

The strict order relation
\[
E=\{(w,y)\in Y\times Y:y<w\}
\]
is not measurable in the product of the two countable-cocountable sigma algebras. Its fixed-\(w\) sections in the \(y\)-coordinate are countable, while its fixed-\(y\) sections in the \(w\)-coordinate are cocountable. If \(E\) were product-measurable, Tonelli would assign its product measure both zero and one. Thus the full two-coordinate error graph cannot simply be treated as a measurable product event.

The construction avoids that invalid step:
1. The terminal supremum is first reduced pathwise by identity (1).
2. At a public node, the witness \(w\) has already been fixed before the current sample.
3. Only the one-coordinate section \(L_w\) is measured. It is measurable and null.
4. The continuation risk is recursively composed. For this strategy it is the constant zero function, so no joint measurability of the successor map is needed.

Accordingly, the proof defines and computes the public game's value in its nested, sequential conditional-risk semantics. It does **not** claim that the original full-path indicator has become an ordinary product-measurable random variable, nor does it apply the usual conditional-expectation tower theorem to that nonmeasurable indicator.

The existing **terminalPathMiss_pi_measure_zero** result in OmegaOneSeparation.lean gives an additional finite-product outer-measure containment check for a related full-path miss set. It is a separate check, not a premise of the new Bellman proof.

## 5. Deterministic lower bound and separation scope

For a deterministic learner, the current prediction \(\hat y_t\) is known before the witness is selected. The public adversary can set
\[
w_t=\operatorname{succ}(\hat y_t),
\]
so \(\hat y_t<w_t\) at every round. The one global target family with thresholds \(\beta_t=w_t\) is feasible and rejects every prediction. A member of that same family is a zero-loss comparator. Hence the deterministic learner's terminal regret is exactly \(T\).

Together with the randomized sequential value \(0\), this gives
\[
R^\star_{\rm rand}(T)=0,\qquad
R^\star_{\rm det}(T)=T
\]
for every finite \(T\), **in the stated abstract measurable-space model and with the sequential-risk interpretation of the nested public game**.

This is a candidate resolution of the randomized-versus-deterministic public-setting question in the paper's broad measurable-space framework. It is not a standard-Borel construction. The countable-cocountable probability on \(\omega_1\) cannot be sampled exactly from a finite or countably enumerable seed/output space; the repository's PRNGNoGo.v records the countable-range obstruction. Thus it does not settle a stronger version that requires standard-Borel label spaces, finite-bit PRNGs, or ordinary algorithmically implementable randomization. The distinction is substantive, not a technical footnote.

## 6. Formal verification and trusted assumptions

The new Lean module is built with Lean 4.35.0 / Mathlib 4.35.0. The checked declarations report only the standard classical Lean foundations:
- **propext**
- **Classical.choice**
- **Quot.sound**

The build log contains no **sorryAx** dependency. The PR's Rocq 9.2 / Gaia 2.4 job also succeeds, but the new global-sup/Bellman development is currently Lean-formalized; Rocq's successful run verifies its already tracked modules, not an independent port of this new module.

Current verification run:
- GitHub Actions run **41268919254**
- Lean: success
- Rocq: success
- commit: **d8fa1d8ed0ae163df56c69169d705462ad0cb340**

Reproduce the Lean build with:
~~~sh
cd PublicSetting/Lean
lake build
~~~

## 7. Tool and repository responsibilities

The repository's TOOL_ROLES.md separates the proof kernel from exploratory tools:
- **Lean 4 + Mathlib4:** trusted measure-theoretic and sequential-value proof.
- **Rocq 9.2 + Gaia 2.4:** independent checks of the existing abstract countable-ideal and ordinal foundations; the new Bellman theorem is not yet ported.
- **LeanDojo-v2:** theorem retrieval and proof-search suggestions only; generated tactics must be replayed by Lean.
- **Naproche:** structured prose-proof audit, not a replacement for the Lean kernel.
- **cvc5:** finite logical/arithmetic counterexample search.
- **SymPy / SageMath / Wolfram:** exact finite examples and sanity checks.
- **GAP:** finite group actions and symmetry experiments if a finite symmetric reduction is introduced.
- **Macaulay2:** polynomial/commutative-algebra checks only if a future finite algebraic strategy model arises; no relevant algebraic task occurs in this proof.
- **Context7:** current Mathlib API lookup.
- **Parallel Search / Sider Scholar:** source-paper and literature retrieval.
- **GitHub Actions:** pinned, reproducible build evidence for the exact commit.

These tools are complementary and are not all build dependencies. The proof does not gain rigor by adding unrelated packages to its trusted build surface.
