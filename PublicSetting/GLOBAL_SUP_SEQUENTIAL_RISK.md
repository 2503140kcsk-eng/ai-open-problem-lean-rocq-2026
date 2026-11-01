# Terminal global supremum and sequential conditional-risk recursion

**Date:** 2026-11-01  
**Formal source:** \`Lean/GlobalSupSequentialRisk.lean\`  
**Scope:** a non-standard measurable-space example under explicitly defined sequential-risk semantics; not a claim of a standard-Borel or ordinary full-path expectation construction.

## 1. The selected set-realizable problem

Let
\[
Y=\omega_1=\{\alpha:\alpha\text{ is a countable ordinal}\}
\]
with the countable-cocountable sigma algebra and probability measure
\[
\mu(A)=
\begin{cases}
0& A\text{ is countable},\\
1& Y\setminus A\text{ is countable}.
\end{cases}
\]
For each \(\beta\in Y\), put
\[
S_\beta=\{y\in Y:\beta\le y\},\qquad
L_\beta=Y\setminus S_\beta=\{y:y<\beta\}.
\]
Every \(L_\beta\) is countable, measurable, and \(\mu(L_\beta)=0\).

Choose the admissible acceptable-set family to be
\[
\mathcal S(Y)=\{S_\beta:\beta\in Y\}\subseteq\sigma(Y),
\]
and take the context space \(X=\mathbb N\), with hypothesis space \(H=Y^X\). This is a particular instance of the paper's set-realizable model, not a claim about every acceptable-set family.

For a threshold function \(\beta:X\to Y\), define the single global target family
\[
F^\star_\beta
=\{f\in H:\forall x\in X,\ \beta(x)\le f(x)\}.
\]
For every context \(x\),
\[
F^\star_\beta(x):=\{f(x):f\in F^\star_\beta\}=S_{\beta(x)}.
\]
The forward inclusion follows from the defining condition. Conversely, if \(y\ge\beta(x)\), the function equal to \(y\) at \(x\) and to \(\beta(z)\) at every \(z\ne x\) belongs to \(F^\star_\beta\). Thus one and the same subset \(F^\star_\beta\subseteq H\) induces every acceptable set. The Lean declaration \`globalContextHypothesisFamily_projection\` checks this coordinate-image statement for arbitrary context types.

## 2. The actual terminal global supremum when contexts may repeat

A public transcript of length \(T\) has contexts \(x_t\), pre-draw visible witnesses \(w_t\), and realized predictions \(y_t\). Set-realizability by one target family \(F^\star_\beta\) is exactly the constraint
\[
\beta(x_t)\le w_t\quad(t<T).
\]
The terminal comparator loss supremum is therefore
\[
G_T(\mathbf x,\mathbf w,\mathbf y)=
\sup_{\substack{\beta:X\to Y\\
                 \forall t<T,\ \beta(x_t)\le w_t}}
\sum_{t<T}\mathbf1\{y_t\notin S_{\beta(x_t)}\}
=
\sup_{\beta\text{ feasible}}
\sum_{t<T}\mathbf1\{y_t<\beta(x_t)\}.
\tag{1}
\]

The exact general statement is the **upper bound**
\[
\boxed{
G_T(\mathbf x,\mathbf w,\mathbf y)
\le \sum_{t<T}\mathbf1\{y_t<w_t\}.
}
\tag{2}
\]
Indeed, for every feasible global \(\beta\),
\[
y_t<\beta(x_t)\le w_t
\quad\Longrightarrow\quad y_t<w_t
\]
term by term. Taking the supremum preserves the bound. Lean checks this as \`globalContextTerminalSupLoss_le_predictableMissCount\`.

### When equality holds

If the contexts \(x_0,\ldots,x_{T-1}\) are pairwise distinct, one global threshold function can set \(\beta(x_t)=w_t\) for every round and be filled arbitrarily elsewhere. Then (2) is an equality:
\[
G_T(\mathbf x,\mathbf w,\mathbf y)
=\sum_{t<T}\mathbf1\{y_t<w_t\}.
\tag{3}
\]
Lean checks this in \`globalContextTerminalSupLoss_eq_predictableMissCount_of_injective\`.

**Why the distinction matters.** If a context repeats, the same global family must use the same set at both occurrences. For example, take two rounds with \(x_0=x_1\), witnesses \(w_0=2,w_1=5\), and predictions \(y_0=1,y_1=3\) (finite ordinals inside \(\omega_1\)). Feasibility requires \(\beta(x_0)=\beta(x_1)\le2\), so the terminal supremum is \(1\), whereas the independent stagewise sum is \(2\). Thus equality for arbitrary context sequences would be false. The new context-indexed theorem fixes this defect: the terminal supremum is always dominated by the stagewise envelope, and equality is asserted only for injective context sequences.

The earlier \`globalHypothesisTerminalSupLoss\` formula is the special case \(x_t=t\), i.e. the fresh-context transcript. It is not used as an equality for transcripts with repeated contexts.

## 3. Sequential outer conditional-risk recursion

The public move order at a history \(h\) is:
1. adversary chooses the context \(x\);
2. learner chooses a probability measure \(p\) on \(Y\);
3. adversary chooses the visible witness \(w\), before the current draw;
4. Nature draws \(y\sim p\), and \(y\) becomes part of the public history.

For a fixed witness \(w\), the immediate error section is
\[
L_w=\{y:y<w\}.
\]
It is measurable, countable, and \(\mu(L_w)=0\). Let
\[
e_w(y)=\mathbf1\{y<w\}.
\]

### Upper integral for a possibly nonmeasurable continuation

For an arbitrary nonnegative function \(f:Y\to[0,\infty]\), define its upper integral (outer expectation)
\[
U_p(f)=
\inf\left\{
\int g\,dp:
g\text{ measurable and } f(y)\le g(y)\ \forall y
\right\}.
\tag{4}
\]
The constant function \(+\infty\) is always an admissible majorant, so this infimum is well-defined even when \(f\) is not measurable.

The Lean development proves the properties needed for conditional-risk composition:

- **Monotonicity:** \(f\le g\) pointwise implies \(U_p(f)\le U_p(g)\).
- **Agreement with Lebesgue integration:** if \(f\) is measurable, then \(U_p(f)=\int f\,dp\).
- **Addition of a measurable immediate cost:** if \(g\) is measurable and nonnegative, then
  \[
  U_p(f+g)\le U_p(f)+\int g\,dp.
  \tag{5}
  \]
- For the fixed-witness section, \(U_p(e_w)=p(L_w)\), since \(e_w\) is measurable.

These are kernel-checked in **upperLIntegral_mono**, **upperLIntegral_eq_lintegral_of_measurable**, **upperLIntegral_add_measurable_le**, **lintegral_lowerSegmentIndicator_eq_measure**, and **upperLIntegral_lowerSegmentIndicator_eq_measure**.

Let \(\operatorname{Next}(h,x,p,w,y)\) be the next public history. The **exact one-step outer-risk operator** is
\[
\mathcal B^+V(h)=
\sup_x\inf_p\sup_{w\in Y}
U_p\!\left(
y\mapsto e_w(y)+V(\operatorname{Next}(h,x,p,w,y))
\right).
\tag{6}
\]
It preserves the public information order \(\sup_x\inf_p\sup_w\). No measurability of \(y\mapsto V(\operatorname{Next}(\cdots,y))\) is required: \(U_p\) is explicitly defined for arbitrary nonnegative functions using measurable majorants.

The formalization proves:
\[
\mathcal B^+V(h)\le
\sup_x\inf_p\sup_w
\left[p(L_w)+U_p(V\circ\operatorname{Next})\right],
\tag{7}
\]
by (5), and proves that both Bellman operators are monotone in \(V\). Thus the exact outer-risk operator is bounded by the simpler stagewise section-risk envelope without replacing an upper integral by a lower integral or using the ordinary tower property on a nonmeasurable payoff.

### Zero-value theorem

Define
\[
W_0(h)=0,\qquad W_{n+1}(h)=\mathcal B^+W_n(h).
\tag{8}
\]
Use the same learner action \(p_0=\mu\) at every public history. For every pre-draw witness \(w\),
\[
U_\mu(e_w)=\mu(L_w)=0.
\]
Induct on \(n\).

- Base: \(W_0(h)=0\).
- Step: assume \(W_n(h')=0\) for every history \(h'\). Then for each fixed \(x,w\), the continuation function is identically zero, so the exact one-step outer risk is
  \[
  U_\mu(e_w+0)=U_\mu(e_w)=\mu(L_w)=0.
  \]
  The learner can therefore force the Bellman bracket to zero for every \(x,w\). All risks are nonnegative, so \(W_{n+1}(h)=0\).

Hence
\[
\boxed{W_n(h)=0\quad\text{for every finite }n\text{ and every history }h.}
\]
Lean checks this through **publicGlobalSupOuterBellmanStep_eq_zero_of_policy**, **publicGlobalSupOuterGameValue_eq_zero**, and **omegaOne_publicGlobalSupOuterGameValue_eq_zero**.

The exact outer-risk recursion (8) is the primary sequential game-value semantics. Its stagewise envelope (the earlier **publicGlobalSupBellmanStep**) is a convenient upper bound. Neither is defined by integrating a full-path nonmeasurable reward over a product space.

## 4. Deterministic lower bound

For a deterministic learner, use fresh contexts \(x_t=t\). Once the learner's deterministic prediction \(\hat y_t\) is known, the public adversary chooses
\[
w_t=\operatorname{succ}(\hat y_t).
\]
Then \(\hat y_t<w_t\). Since the contexts are distinct, one global threshold function can satisfy \(\beta(t)=w_t\); its associated single family \(F^\star_\beta\) realizes all upper tails and rejects every learner prediction. The comparator has zero loss and the learner makes exactly \(T\) mistakes.

The existing \`deterministicLearner_global_separation_witness\` in \`OmegaOneSeparation.lean\` formalizes this global target-family witness. Therefore, in the specified instance and sequential-risk interpretation,
\[
R^\star_{\mathrm{seq,rand}}(T)=0,\qquad
R^\star_{\mathrm{det}}(T)=T.
\]
The randomized conclusion follows because (2) dominates the terminal global supremum pathwise, and the exact sequential outer-risk value (8) is zero. The deterministic conclusion uses the fresh-context lower-bound transcript.

## 5. Product-measurability obstruction and what is—and is not—proved

The relation
\[
E=\{(w,y)\in Y\times Y:y<w\}
\]
is not measurable in the product of the two countable-cocountable sigma algebras. For each fixed \(w\), the \(y\)-section is countable and has measure zero; for each fixed \(y\), the \(w\)-section is cocountable and has measure one. If \(E\) were product-measurable, Tonelli would give incompatible iterated integrals \(0\) and \(1\).

The exact recursion avoids this invalid joint-measurability step: at a public node the witness is already fixed, the immediate section \(L_w\) is measurable, and any possibly nonmeasurable continuation is assigned its upper integral via measurable majorants. Along the zero-risk learner strategy the continuation is identically zero. This is a nested outer-risk semantics, not an ordinary product-space expectation.

**Scope boundary.** This is a mathematically defined sequential conditional-risk semantics for a particular non-standard measurable-space set-realizable game. It does not construct an ordinary product-space random variable for the nonmeasurable terminal payoff, nor prove that the usual expectation of that payoff exists for every nonmeasurable adaptive adversary. Thus it is a candidate resolution in the explicitly stated sequential-risk model, not a theorem covering all standard-Borel/ordinary-expectation formulations of the paper's open question.

## 6. Exact randomization boundary

The countable-cocountable law is a valid abstract probability measure on \(Y\), and the paper's abstract action space \(\Pi(Y)\) admits such a law if no standard-Borel restriction is added.

The repository's \`PRNGNoGo.v\` proves that no sampler with countable output range (in particular, a finite-state or countable-seed terminating sampler) can have this law as its pushforward: the sampler's range is countable and has target mass zero but source pushforward mass one.

Do not overextend this result to every uncountable source. The repository's \`RNG_COMPATIBILITY.md\` records the sharper set-theoretic boundary: a measurable pushforward from Lebesgue \([0,1]\) to this law exists exactly when \(\operatorname{cov}(\mathcal N)\le\aleph_1\); CH is sufficient, while models with \(\operatorname{cov}(\mathcal N)>\aleph_1\) rule it out. This is not an executable finite-bit sampler.

## 7. Formal verification

- Main source: \`PublicSetting/Lean/GlobalSupSequentialRisk.lean\`.
- Lean: 4.35.0 / Mathlib 4.35.0.
- Rocq CI: 9.2.0 / Gaia 2.4 for the previously tracked ordinal and countable-ideal modules. The new context-indexed Bellman development itself is Lean-formalized, not independently ported to Rocq.
- New key declarations:
  - \`globalContextHypothesisFamily_projection\`
  - \`globalContextTerminalSupLoss_le_predictableMissCount\`
  - \`globalContextTerminalSupLoss_eq_predictableMissCount_of_injective\`
  - \`globalHypothesisTerminalSupLoss_eq_predictableMissCount\`
  - \`publicGlobalSupGameValue_eq_zero\`
  - \`omegaOne_publicGlobalSupGameValue_eq_zero\`

The final code head verified here is **0d6c7e9cc581db4ed9f109f766519838c9a2894d**. GitHub Actions run [41272999925](https://github.com/2503140kcsk-eng/ai-open-problem-lean-rocq-2026/actions/runs/41272999925) completed successfully: Lean 4.35 / Mathlib 4.35 and Rocq 9.2 / Gaia 2.4 jobs both succeeded. The Lean log reports no sorryAx; the new outer-risk theorems depend only on propext, Classical.choice, and Quot.sound. The new outer-risk development is Lean-formalized; the successful Rocq job independently compiles the repository's existing ordinal/countable-ideal foundations, not a second port of the new Bellman module.

## 8. Tool and repository roles

The proof kernel is Lean/Mathlib. Rocq/Gaia checks existing set-theoretic foundations independently. The other repositories are sidecar resources with narrow roles, not a larger untrusted build dependency:
- **Macaulay2:** polynomial/ideal elimination only if finite algebraic strategy constraints arise; no core role in this theorem.
- **GAP:** finite symmetry/orbit reductions for finite game instances.
- **SymPy:** exact symbolic simplification and small algebraic examples.
- **SageMath:** exact finite games, rational polyhedra, and combinatorial checks.
- **Naproche:** audit structured prose proofs; not a replacement for Lean/Rocq.
- **cvc5:** finite logical/arithmetic counterexample search; not a measure-theory prover.
- **LeanDojo-v2:** theorem retrieval and proof-search suggestions; every suggestion must be replayed by Lean.
- **Mathlib4:** trusted definitions and lemmas for ordinals, measures, integrals, and order-theoretic suprema.
- **Wolfram:** independent symbolic and finite numerical sanity checks.
- **Context7:** current Lean/Mathlib API lookup.
- **Parallel Search:** retrieve primary source papers and documentation.
- **Sider Scholar:** academic source discovery and bibliographic cross-check.
- **GitHub Actions:** reproducible builds at pinned tool versions and exact commit SHA.

The computation and research tools are evidence or search aids, never substitutes for the proof assistant kernel.
