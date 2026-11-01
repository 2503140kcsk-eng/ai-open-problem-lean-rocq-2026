# Asymptotic regret bounds and tool responsibilities

**Date:** 2026-10-31  
**Scope warning:** the target open question is randomized-versus-deterministic learnability in the *public, set-realizable, partial-feedback* protocol. The bounds below are deliberately separated by realizability regime and adversary information.

## 1. Exact definitions

For a learner A and horizon T, the paper defines
\[
R_A(T,\mathcal H)=
\sup_{\text{admissible transcripts}}
\left(\ell_T(A)-\inf_{f\in\mathcal H}\ell_T(f)\right),
\qquad
R^\star(T,\mathcal H)=\inf_A R_A(T,\mathcal H).
\]
The transcript includes instances, hidden acceptable sets, and one visible acceptable witness per round. Randomized learner loss is expected over its sampled prediction. In the set-realizable regime, there is one fixed set of hypotheses F* such that S_t=F*(x_t) for every round.

The target public protocol's order is: adversary chooses x_t; learner publishes π_t; adversary chooses a visible witness y_t^vis in a still-feasible target set; only then is ŷ_t sampled; after the horizon the hidden sets must all be induced by one globally realizable F*. The fact that the adversary can see past realized samples is the public/oblivious distinction in §5.3 of the paper. Do not replace the globally realizable terminal family by unrelated roundwise sets.

## 2. General dimension-controlled asymptotics

The paper introduces the partial-feedback Littlestone dimension PFL_T for deterministic learners and the partial-feedback measure-shattering dimension PMS_(T,γ) for randomized learners.

### 2.1 Deterministic exact characterization

In the set-realizable regime the paper's Theorem 6 gives
\[
R^\star_{\rm det}(T,\mathcal H)=\operatorname{PFL}_T(\widetilde{\mathcal H}).
\]
Therefore
\[
R^\star_{\rm det}(T,\mathcal H)=o(T)
\quad\Longleftrightarrow\quad
\operatorname{PFL}_T(\widetilde{\mathcal H})=o(T).
\]
Also, if there are c>0 and T₀ such that
\[
\operatorname{PFL}_T(\widetilde{\mathcal H})\ge cT
\quad(T\ge T₀),
\]
then the deterministic minimax regret is Ω(T), with the same constant c.

### 2.2 Randomized two-sided bound

Theorem 13 gives a universal constant C>0 such that
\[
\sup_{\gamma\in(0,1]}
\gamma\,\operatorname{PMS}_{(T,\gamma)}(\widetilde{\mathcal H})
\le R^\star_{\rm rand}(T,\mathcal H)
\le C\inf_{\gamma\in(0,1]}
\left\{\gamma T+
\int_\gamma^1
\operatorname{PMS}_{(T,\eta)}(\widetilde{\mathcal H})\,d\eta
\right\}.
\]

The asymptotic consequences are immediate but conditional:

- **o(T) upper:** it suffices to exhibit a sequence γ_T∈(0,1] with γ_T→0 and
  \[
  \int_{\gamma_T}^1\operatorname{PMS}_{(T,\eta)}(\widetilde{\mathcal H})\,d\eta=o(T).
  \]
  Then both γ_T T=o(T) and the integral term are o(T), so the displayed upper bound is o(T).

- **Ω(T) lower:** it suffices to exhibit c>0 and a sequence γ_T∈(0,1] such that
  \[
  \gamma_T\operatorname{PMS}_{(T,\gamma_T)}(\widetilde{\mathcal H})\ge cT
  \]
  for all sufficiently large T. The displayed lower bound then gives R*_{rand}≥cT.

Neither asymptotic premise is implied by standard-Borel structure, existence of transition kernels, or the conditional-expectation tower property alone. The missing input is combinatorial: control of PFL/PMS for the particular hypothesis class and the globally feasible collection-version spaces.

## 3. Fully explicit o(T) example: finite set-realizable hypothesis classes

Let |H|=n<∞ and assume set-realizability. The paper's Theorem 2 provides a deterministic learner with
\[
R^\star_{\rm det}(T,\mathcal H)
\le B(n):=\sum_{i=1}^{\lfloor n/2\rfloor}\binom ni
\quad\text{for every }T.
\]
For every fixed n, B(n) is independent of T, hence
\[
\lim_{T\to\infty}\frac{R^\star_{\rm det}(T,\mathcal H)}T=0.
\]
Since randomized learners may use a deterministic strategy,
R*_{rand}≤R*_{det}≤B(n) in the same protocol.

### Proof idea, with the counting step made explicit

Maintain the collection version space
\[
\widetilde V_t=\{F\in\widetilde V_{t-1}:y_t^{vis}\in F(x_t)\}.
\]
A single globally realizable F* belongs to every \widetilde V_t by induction: it belongs initially, and the revealed witness lies in F*(x_t), so it survives each update.

At round t, first search for a label y that belongs to F(x_t) for every F∈\widetilde V_{t-1}. If one exists, predict it; because F* is still in the collection version space, this prediction belongs to F*(x_t)=S_t and is correct. If none exists, use a majority label among the n hypotheses.

For a round in which this fallback prediction is wrong, define the visible fiber
\[
V_t^{vis}=\{f\in H:f(x_t)=y_t^{vis}\}.
\]
The wrong fallback prediction is a majority label different from y_t^{vis}; therefore
\[
1\le |V_t^{vis}|\le\lfloor n/2\rfloor.
\]

No two mistaken fallback rounds can have the same visible fiber. Indeed, the collection version space is decreasing. The update rule is equivalently
\[
\widetilde V_t=\{F\in\widetilde V_{t-1}:F\cap V_t^{vis}\ne\varnothing\}.
\]
If t<t' and V_t^{vis}=V_{t'}^{vis}, every F surviving to time t' intersects V_t^{vis}=V_{t'}^{vis}. Thus every surviving F contains a hypothesis predicting y_{t'}^{vis} at x_{t'}, so y_{t'}^{vis} is in every F(x_{t'}). The learner's search phase would therefore have succeeded at t', and that round could not be a mistaken fallback round.

Thus each mistake injects into a distinct nonempty subset of H of size at most floor(n/2). There are exactly B(n) such subsets. This proves the mistake bound, and in set-realizability regret equals learner mistakes because the comparator's loss is zero.

This is a genuine horizon-uniform upper bound, not an asymptotic heuristic.

## 4. Fully explicit Ω(T) example: two hypotheses, but only existence-realizability

The paper's Theorem 20 proves that randomization alone does not guarantee sublinear regret once set-realizability is weakened to existence-realizability. The example has
\[
X=\{1,\ldots,T\},\quad Y=\{0,1\},\quad
H=\{f_0\equiv0,f_1\equiv1\},\quad
\mathcal S(Y)=\mathcal P(Y).
\]

At round t let p_t=π_t(1). The adversary reveals a least-probable label: it reveals 1 when p_t≤1/2 and 0 when p_t>1/2. The choice is made after π_t is published but before the current random draw; it does not inspect any realized sampled prediction.

Let q be the number of rounds with π_t(0)≥1/2 (ties included). Choose one fixed comparator index for the entire horizon:
- If q≥T/2, choose k=1.
- If q<T/2, choose k=0.

Now define the hidden acceptable sets after the strategy sequence is determined:
- On every round where the learner assigns probability at least 1/2 to label 1−k, set S_t={k}.
- On all other rounds set S_t={0,1}.

This is feasible: whenever S_t={k}, the visible label is k, because the adversary revealed a least-probable label; and whenever S_t={0,1}, either visible label is allowed. The same fixed hypothesis f_k belongs to every S_t, so this is existence-realizable. Its comparator loss is zero.

If q≥T/2, then k=1 and at least q rounds have π_t(0)≥1/2; on each such round S_t={1}, so expected learner loss π_t(0)≥1/2. If q<T/2, then k=0 and more than T/2 rounds have π_t(0)<1/2, hence π_t(1)>1/2; on each of those rounds S_t={0}, and expected loss is π_t(1)>1/2. In either case,
\[
\ell_T(A)-\ell_T(f_k)\ge\frac12\cdot\frac T2=\frac T4.
\]
Consequently
\[
R^\star_{\rm rand}(T,H)\ge T/4=\Omega(T).
\]

This lower-bound strategy ignores past sampled predictions, so it is also valid when the public adversary is allowed to see those predictions (it simply chooses not to use that extra information).

**Critical limitation:** the construction is only existence-realizable, not set-realizable. The final sets S_t are sometimes {k} and sometimes {0,1}; there is no fixed F*⊆{f₀,f₁} with S_t=F*(x_t) for all t. Hence this example does not solve the PR's set-realizable public randomized-versus-deterministic open problem. It proves that no universal randomized o(T) theorem is possible across all realizability regimes, even with two hypotheses.

## 5. Context-aware global supremum and sequential outer-risk candidate

The paper's §5.3 asks whether randomized and deterministic learners can differ in learnability in the public set-realizable setting. The omega-one construction chooses the measurable label space \(Y=\omega_1\), the admissible set family \(\mathcal S(Y)=\{S_\beta:\beta\in Y\}\) of upper tails, context space \(X=\mathbb N\), and hypothesis class \(H=Y^X\).

For one global threshold function \(\beta:X\to Y\), the same set
\[
F^\star_\beta=\{f\in Y^X:\forall x\in X,\ \beta(x)\le f(x)\}
\]
induces \(F^\star_\beta(x)=S_{\beta(x)}\) at every context. For an arbitrary context sequence \(x_t\), pre-draw witnesses \(w_t\), and predictions \(y_t\), the actual terminal global supremum is
\[
G_T(\mathbf x,\mathbf w,\mathbf y)=
\sup_{\beta:X\to Y:\ \beta(x_t)\le w_t}
\sum_{t<T}\mathbf1\{y_t<\beta(x_t)\}.
\]
The correct general theorem is
\[
G_T(\mathbf x,\mathbf w,\mathbf y)
\le\sum_{t<T}\mathbf1\{y_t<w_t\}.
\]
This may be strict when contexts repeat, because one global \(F^\star\) must use the same acceptable set at every occurrence of a context. If the context sequence is injective, a single global threshold function can set \(\beta(x_t)=w_t\) for every round, and equality holds. Lean checks these two statements as **globalContextTerminalSupLoss_le_predictableMissCount** and **globalContextTerminalSupLoss_eq_predictableMissCount_of_injective**. The earlier infinite-index equality is only the fresh-context special case \(x_t=t\).

### Exact sequential outer-risk recursion

For an arbitrary nonnegative (possibly nonmeasurable) continuation \(f:Y\to[0,\infty]\), define the upper integral / outer expectation
\[
U_p(f)=\inf\left\{\int g\,dp:
g\text{ measurable and }f\le g\text{ pointwise}\right\}.
\]
The Lean implementation proves monotonicity, agreement with the ordinary nonnegative Lebesgue integral on measurable functions, and
\[
U_p(f+g)\le U_p(f)+\int g\,dp
\]
for each measurable nonnegative immediate cost \(g\).

Let \(e_w(y)=\mathbf1\{y<w\}\) be the measurable current-round error section. The exact one-step outer-risk operator is
\[
\mathcal B^+V(h)=
\sup_x\inf_p\sup_w
U_p\!\left(e_w+
V(\operatorname{Next}(h,x,p,w,\cdot))\right).
\]
It respects the public protocol order: context, learner draw law, pre-draw witness, then sample. Its upper-integral addition inequality bounds it by the stagewise envelope
\[
\sup_x\inf_p\sup_w
\left[p(\{y:y<w\})+
U_p(V(\operatorname{Next}(h,x,p,w,\cdot)))\right].
\]
The Lean theorem **publicGlobalSupOuterBellmanStep_le_stagewise** formalizes the one-step bound, and **publicGlobalSupOuterGameValue_le_stagewiseGameValue** lifts it by finite-horizon induction to every public history. The corresponding monotonicity lemmas are also kernel-checked. This upper-integral formulation is crucial: it does not silently use the lower integral for a nonmeasurable continuation and does not apply the ordinary conditional-expectation tower to a nonmeasurable full-path payoff.

Use the fixed learner law \(p=\mu\), the countable-cocountable probability on \(Y=\omega_1\). For every pre-draw witness \(w\), the section \(L_w=\{y:y<w\}\) is countable, measurable, and null. The continuation at the zero-risk induction step is the constant zero function, so its upper integral is also zero. Backward induction therefore gives exact outer-risk value zero at every finite horizon and every public history. The pathwise terminal-sup inequality above transfers this stagewise upper bound to the terminal global regret in the explicitly defined sequential outer-risk semantics.

For the deterministic lower bound, the adversary uses fresh contexts \(x_t=t\) and witnesses \(w_t=\operatorname{succ}(\hat y_t)\). One global threshold function realizes all the upper tails and rejects every deterministic prediction, giving exactly \(T\) mistakes and zero comparator loss. Thus the selected nonstandard measurable-space sequential-risk instance has randomized outer-risk upper value \(0\) and deterministic worst-case loss \(T\).

### Scope boundary

This is a candidate separation under the explicitly defined iterated outer-risk semantics. The full terminal payoff need not be a product-measurable random variable; the result does not establish an ordinary full-path expectation for every unrestricted adaptive adversary. It is not a standard-Borel construction and does not yield a finite-bit or countable-range sampler for the countable-cocountable law. Standard-Borel / conventional full-path-expectation versions remain separate.

The final code head is **d88c9495f64afacde4b5bff92b636c9250cd8229**. GitHub Actions run [41273293794](https://github.com/2503140kcsk-eng/ai-open-problem-lean-rocq-2026/actions/runs/41273293794) completed successfully for Lean 4.35 / Mathlib 4.35 and Rocq 9.2 / Gaia 2.4. The exact outer-risk Bellman development is Lean-formalized; the Rocq job independently checks the existing ordinal and countable-ideal foundations rather than a Rocq port of the new Bellman module.

## 6. Tool and repository responsibilities

The tools are deliberately assigned non-overlapping jobs. A tool's output is never counted as a theorem proof unless it is accepted by a proof assistant's kernel.

| Resource | Assigned task | Boundary |
|---|---|---|
| Mathlib4 | Trusted Lean formalization of probability kernels, product measures, Ionescu–Tulcea, conditional expectation, Fubini, Sion | The application-specific assumptions must still be proved |
| GitHub Actions | Reproducible pinned Lean 4.35 / Mathlib 4.35 and Rocq 9.2 builds on the exact commit | A green workflow certifies only the tracked targets at that SHA |
| LeanDojo-v2 | Search theorem declarations, trace imports and proof states, propose tactic/proof search | Not a proof checker; optional model inference may require a GPU or external API |
| cvc5 | Finite arithmetic, first-order constraints, small countermodels and consistency checks | Not a measure-theory prover |
| SymPy | Exact symbolic simplification and algebraic sanity checks for finite payoff formulas | Not a proof of measurable or asymptotic claims |
| SageMath | Finite combinatorics, exact matrix games, finite tree enumeration and exploratory bounds | Computational evidence only |
| Wolfram | Independent exact calculations and finite examples; e.g. verify fixed-set risk 0 versus post-sample adaptive risk 1 | Not a substitute for the Lean/Rocq kernel |
| GAP | Group actions, finite symmetry reduction, orbit/counting experiments when the instance has such structure | No direct role in the ordinal / standard-Borel measure argument absent a finite symmetry group |
| Macaulay2 | Algebraic elimination only if a future strategy-space constraint is polynomial | No direct role in the current measure-theoretic proof |
| Naproche | Check natural-language mathematical exposition and document structure | Does not certify Lean propositions |
| Context7 | Retrieve current Mathlib API signatures and import paths | Documentation lookup, not proof checking |
| Parallel Search | Literature retrieval, source extraction, paper-version cross-check | Secondary research evidence, not formal verification |
| Sider Scholar | Search and compare academic sources / OpenAlex records | Literature discovery, not formal verification |

All listed repositories are publicly accessible. Their roles are complementary, not interchangeable. The workflow uses no paid theorem-proving model, hosted GPU, commercial symbolic service, or paid inference API. GitHub Actions and connector availability remain subject to their respective free-tier quotas.

## 7. Sources

- Shao, Fang, Lin, Tao, Partial Feedback Online Learning, arXiv:2601.21462v3: https://arxiv.org/html/2601.21462v3
- Mathlib 4.35, product measure and Tonelli/Fubini: https://github.com/leanprover-community/mathlib4/blob/v4.35.0/Mathlib/MeasureTheory/Measure/Prod.lean
- Mathlib 4.35, Ionescu–Tulcea trajectory kernels and condExp_traj: https://github.com/leanprover-community/mathlib4/blob/v4.35.0/Mathlib/Probability/Kernel/IonescuTulcea/Traj.lean
- Official repositories: https://github.com/Macaulay2/M2 ; https://github.com/gap-system/gap ; https://github.com/sympy/sympy ; https://github.com/sagemath/sage ; https://github.com/naproche/naproche ; https://github.com/cvc5/cvc5 ; https://github.com/lean-dojo/LeanDojo-v2 ; https://github.com/leanprover-community/mathlib4
