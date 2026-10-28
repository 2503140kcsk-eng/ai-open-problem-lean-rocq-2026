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

The last two are the open mathematical core. The current tracked Lean/Rocq source modules contain no admitted proof, sorry, axiom, or fabricated existence theorem. Research gaps are recorded as prose, not encoded as proved existence claims.

## Next mathematical step

The protocol is now modeled operationally: contexts and visible labels are chosen before the current random draw; both the learner and public adversary can inspect completed previous predictions, but neither sees hidden sets or correctness bits; and one global target family constrains all rounds. This models the information order, but it does not yet define probability measures and minimax regret at the full generality of the paper. The next mathematical step remains to define that quantitative semantics and prove either a randomized o(T) upper bound plus a deterministic Ω(T) lower bound, or an impossibility theorem. The profile predicates alone do not bridge this semantic gap.

## Construction audit: why the obvious separation example does not transfer

The classical set-valued-feedback separation of Raman, Subedi, and Tewari (PMLR 247, 2024), Section 4.1, uses `Y = ℕ`, co-singleton sets `A_y = ℕ \\ {y}`, and constant hypotheses `h_y(x)=y`. A deterministic learner can be made wrong every round by choosing `A_{p_t}` after observing its deterministic prediction (p_t); the intersection of finitely many co-singleton sets is nonempty, while a learner uniform on `[T]` has expected loss at most one in total.

That proof is not itself a public **set-realizable partial-feedback** separation: for a fixed subfamily (F^\star) of constant hypotheses, the induced set (F^\star(x)) is the same at every context. The deterministic construction needs different exclusions (p_t) across rounds. The new Lean/Rocq lemma `constant_hypothesis_complement_exclusion_is_fixed` machine-checks this obstruction: if one constant-hypothesis family induces the co-singleton `Y \\ {excluded(t)}` at every round, then `excluded` must be constant.

The opposite extreme, the full product class (H=\mathbb N^{\mathbb N}), has enough coordinate freedom to let the terminal target family avoid every realized prediction while accepting each pre-draw witness. The existing bounded-support public attack formalizes this failure of randomized learning in that submodel. Thus neither the constant class from set-valued feedback nor the full product class yields the required public separation.

A valid positive construction would need an intermediate hypothesis class: enough adaptive structure for every deterministic learner to incur linear loss, but insufficient coordinate freedom for a public adversary to tailor a globally consistent target family to a randomized path. The current literature search and formal work have not established such a class or a theorem ruling it out. This is the remaining mathematical gap, not a Lean/Rocq build failure.

## Low-mass witness obstruction for the full product class

A low-mass witness obstruction is machine-checked in both proof assistants in two encodings. In `PublicSetting/Lean/PublicProtocol.lean`, `NatSubprobability` models nonnegative rational atom masses whose every finite prefix sums to at most one; Lean proves `exists_low_mass_label`, that for every positive integer horizon T some atom has mass at most 1/T. In `PublicSetting/Rocq/PublicProtocol.v`, `exists_scaled_low_mass_nat` proves the corresponding integer-scaled statement: for numerator masses whose every finite prefix sums to at most denominator D, some label y satisfies T * mass(y) <= D. For D>0 this represents a discrete mass of at most 1/T after dividing by D. These are separate machine-checked lemmas; the subsequent probabilistic/conditional-expectation argument is still not formalized.

For the full product class \(H=\mathbb N^{\mathbb N}\), the independently machine-checked Lean/Rocq terminal-target construction can then be selected from the completed prediction path. Its pathwise loss equals the number of rounds with \(\hat y_t\ne y_t^{\rm vis}\); because the witness is chosen before the current sample with mass at most (1/T), the conditional expected loss on each round is at least (1-1/T\), giving expected cumulative loss at least \(T-1\). The target family remains globally consistent, and the visible-witness comparator has zero loss. The probability-measure/conditional-expectation argument is not yet a machine-checked theorem; the discrete low-mass atom lemmas and the pathwise/global-consistency construction are checked in both provers, with different but corresponding rational/integer-scaled encodings.

This reinforces the boundary diagnosis: neither the full product class nor the constant-function class is the desired separating class. A positive separation would need an intermediate hypothesis class whose global target constraint prevents the adversary from adapting the acceptable set to the sampled path, while still permitting linear deterministic lower bounds.


## Generalized terminal-target boundary result

In addition to the bounded-support special case, the Lean/Rocq protocol modules now parameterize an arbitrary realized prediction path and visible-witness path. The final exclusion at round t is the prediction whenever prediction and witness differ, and otherwise a different label. The target subfamily is one global family of functions avoiding that complete exclusion path. The proofs show all visible witnesses are accepted and the resulting pathwise loss gap equals the number of non-collision rounds. This makes the full-product attack's logic independent of any assumed support bound; it still does not give a randomized upper bound for any structurally restricted class.


## Candidate audit: affine functions and the finite-avoidance obstruction

This is a further *negative* result from the 2026-10-28 search, not the requested separation.

Let \(\mathcal Y=\mathbb Q\), \(\mathcal X=\mathbb Q\), and
\[
\mathcal H_{\mathrm{aff}}=\{h_{a,b}:h_{a,b}(x)=ax+b,\ a,b\in\mathbb Q\}.
\]
Take distinct contexts \(x_t=t\), \(t=1,\ldots,T\). After the complete prediction path
\(p_1,\ldots,p_T\) and the pre-draw witness path \(y_1,\ldots,y_T\) are fixed, put
\[
J=\{t:p_t\ne y_t\},\qquad
F_T=\{h\in\mathcal H_{\mathrm{aff}}:\forall s\in J,\ h(s)\ne p_s\}.
\]
This is one global target subfamily for all rounds of this horizon. It is nonempty: fix any slope \(a\); only finitely many intercepts \(b=p_s-as\) are forbidden.

For every \(t\in J\), its projection is exactly
\(F_T(t)=\mathbb Q\setminus\{p_t\}\); for every \(t\notin J\), its projection is all of \(\mathbb Q\). To check the claim, fix a desired value \(z\) at context \(t\) and write a line through \((t,z)\) as
\(h(x)=a(x-t)+z\). Each constraint \(h(s)\ne p_s\), for \(s\in J\setminus\{t\}\), forbids only the one slope
\(a=(p_s-z)/(s-t)\). Finitely many constraints forbid finitely many rational slopes, so a permissible slope exists. At \(t\in J\), the one additional local constraint forbids precisely \(z=p_t\).

Consequently, every non-collision round \(p_t\ne y_t\) has prediction loss one, and every collision round has loss zero, with all witness labels accepted by the *same* \(F_T\). Because \(\mathbb Q\) is countably infinite, for any current discrete action distribution \(\pi_t\) and any \(T\ge1\), the adversary can select a witness \(y_t\) before the current draw with \(\pi_t(y_t)\le1/T\). Therefore
\[
\mathbb E[\text{loss}]=\sum_{t=1}^T\Pr[p_t\ne y_t]\ge T-1.
\]
The comparator has zero loss because every member of the nonempty \(F_T\) predicts a value in its induced acceptable set at every round.

This rules out an attractive but incorrect heuristic: *finite parameter dimension by itself does not prevent the public adversary from building a globally consistent post-hoc target family*. The affine class has only two parameters, yet the finite-avoidance extension property above lets it reproduce the full-product class's linear randomized lower bound. The proof is mathematical prose in this note and has **not** yet been encoded as a Lean/Rocq theorem.

### Necessary obstruction to test in future candidates

A candidate fails immediately if, for distinct queried contexts and each finite exclusion path \((p_s)_{s\in J}\), the family of hypotheses avoiding those exclusions still projects to \(\mathcal Y\setminus\{p_t\}\) at every excluded coordinate and to all of \(\mathcal Y\) elsewhere. A successful class must prevent this extension property while still permitting an adversary to preserve witness-realizability and exclude every deterministic learner's prediction on linearly many rounds. The affine and full-product examples do not meet that latter randomized requirement.


## New diagonal construction in the computable-learner model

Date: 2026-10-28. This is a **new restricted-model construction**, not a resolution of the unrestricted open problem. It gives a rigorous candidate satisfying the three requested properties when learners are restricted to total computable policies. The restriction is essential to the diagonal lower bound and must not be silently dropped.

### Model and hypothesis class

Let the label set be \(Y=\mathbb N\), and restrict allowed sets to co-singletons
\[
\mathcal S(Y)=\{Y\setminus\{y\}:y\in\mathbb N\}.
\]
Enumerate all total computable online policy kernels with valid discrete distributions by indices \(C\in\mathbb N\). A context \(x=(C,\eta)\) consists of a challenge-policy index and a code for a finite public transcript \(\eta\). It is selected before the learner's current draw. Write \(\pi_C(\eta,x)\) for the distribution output by policy \(C\) on that embedded transcript and context. Let \(m(C,\eta,x)\) be the least label attaining the maximum atom of that distribution. Such an atom exists for every probability distribution on countable \(\mathbb N\); tie-breaking by least label makes \(m\) unique. This mode function need not itself be computable for the mathematical definition of the class.

For \(C,m\in\mathbb N\), let \(\rho_{C,m}\) be the increasing bijection from \(\mathbb N\setminus\{C\}\) to \(\mathbb N\setminus\{m\}\). For context \(x=(C,\eta)\), abbreviate \(m_x=m(C,\eta,x)\). Define, for each \(B\in\mathbb N\), one hypothesis \(h_B:X\to\mathbb N\):
\[
h_B(x)=
\begin{cases}
m_x,&B=C,\\
\rho_{C,m_x}(B),&B\ne C.
\end{cases}
\]
For explicit arithmetic,
\[
\rho_{C,m}(B)=
\begin{cases}
B,&B<C,\ B<m,\\
B+1,&B<C,\ B\ge m,\\
B-1,&B>C,\ B\le m,\\
B,&B>C,\ B>m.
\end{cases}
\]
At every fixed context \(x\), the map \(B\mapsto h_B(x)\) is a bijection \(\mathbb N\to\mathbb N\). If \(B\ne C_x\), then \(h_B(x)\in\{B-1,B,B+1\}\) (with the obvious boundary-safe interpretation at zero).

For a single fixed index \(B^\star\), take one global target family
\[
F^\star=\{h_B:B\ne B^\star\}.
\]
Because each context's evaluation map is a bijection, its induced acceptable set is exactly
\[
F^\star(x)=\mathbb N\setminus\{h_{B^\star}(x)\}.
\]
The same \(F^\star\) is used at every round. Every hypothesis in \(F^\star\) has zero loss on every round of that instance, so the comparator loss is zero. The excluded hypothesis \(h_{B^\star}\) has loss one on every round.

### Property 1 — linear deterministic loss for every computable deterministic learner

Let a deterministic learner have code \(A\). At round \(t\), choose context \(x_t=(A,\eta_t)\), where \(\eta_t\) encodes the actual past transcript. Since \(\pi_A(\eta_t,x_t)\) is a point mass at the learner's prediction \(p_t\), its mode is \(m_{x_t}=p_t\), and hence \(h_A(x_t)=p_t\). After observing this deterministic policy, the adversary reveals any \(y_t^{vis}\ne p_t\). The one fixed family \(F^\star=\{h_B:B\ne A\}\) makes that witness acceptable and excludes the learner's prediction on every round. Therefore the realized regret is exactly \(T\).

The adversary chooses \(x_t\) before the current action; it does not need the current sampled prediction. The witness is chosen after the deterministic action as allowed by the public protocol.

### Property 2 — \(O(\log T)\) expected regret for a randomized learner

Use a single horizon-free randomized learner \(R\): at round \(t\), it draws independently and uniformly from \(\{0,\ldots,t-1\}\), ignoring context and history. Its support grows with elapsed time, so the same learner works for every finite horizon.

An arbitrary legal terminal target family must, by the required co-singleton form and the bijection \(B\mapsto h_B(x)\), omit one fixed hypothesis index \(B^\star\). Its regret is the number
\[
M_{B^\star}=\sum_{t=1}^{T}\mathbf1\{\hat y_t=h_{B^\star}(x_t)\}.
\]
It suffices to upper-bound \(\mathbb E[\max_B M_B]\), which is stronger than bounding the regret for any particular valid family.

For every fixed \(B\le T\), every time \(t\), and every prior transcript, the context \(x_t\) and therefore \(h_B(x_t)\) are fixed before the current independent uniform draw. Thus
\[
\Pr(\hat y_t=h_B(x_t)\mid\text{past})\le 1/t.
\]
Write \(H_T=\sum_{t=1}^{T}1/t\). For any \(k\le T\), iterated conditioning bounds the probability that a fixed \(B\le T\) matches on any chosen set \(I\) of \(k\) rounds by \(\prod_{t\in I}(1/t)\). A union bound over choices of \(I\) gives
\[
\Pr(M_B\ge k)\le
\sum_{|I|=k}\prod_{t\in I}\frac1t
\le \frac{H_T^k}{k!}\le(eH_T/k)^k.
\]
Union-bounding over \(T+1\) indices gives
\[
\Pr\!\left(\max_{B\le T}M_B\ge k\right)
\le (T+1)(eH_T/k)^k.
\]
Taking \(k_0=\lceil4eH_T\rceil\), the right side is at most \((T+1)4^{-k}\) for \(k\ge k_0\); summing this tail and using the trivial bound for small \(T\) yields
\[
\mathbb E[\max_{B\le T}M_B]=O(H_T)=O(\log(T+2)).
\]

For \(B>T\), if \(B\ne C_t\), the increasing-bijection formula implies \(h_B(x_t)\ge B-1\ge T\), outside the randomized learner's support \(\{0,\ldots,t-1\}\). Thus a high-index hypothesis can match the learner only at a round where \(C_t=B>T\) and the draw equals \(m_{x_t}\). Let
\[
Z=\sum_{t=1}^{T}\mathbf1\{C_t>T,\ \hat y_t=m_{x_t}\}.
\]
The context is chosen before the current draw, so each summand has conditional expectation at most \(1/t\), whence \(\mathbb E Z\le H_T=O(\log(T+2))\). Pathwise,
\[
\max_{B\in\mathbb N}M_B
\le \max_{B\le T}M_B+Z.
\]
Consequently
\[
\mathbb E[\operatorname{Regret}_T(R)]
\le \mathbb E[\max_B M_B]
=O(\log(T+2))=o(T).
\]
In particular Markov's inequality gives \(\Pr(\operatorname{Regret}_T(R)\ge\varepsilon T)=O(\log T)/(\varepsilon T)\to0\), so linear-loss paths are atypical for this learner. This proof allows the adversary to adapt contexts to the public past. It does not assume that the terminally selected index \(B^\star\) was chosen before random draws.

### Property 3 — one fixed target family at each horizon

For every admissible realized sequence, any valid global target family is \(F^\star=\{h_B:B\ne B^\star\}\) for a single index \(B^\star\); it generates all roundwise acceptable sets simultaneously. The deterministic lower uses \(B^\star=A\). The randomized upper takes a supremum over all \(B^\star\), including an index chosen after observing the entire path. No round-by-round-changing target family is used.

### Scope limitation — why this is not yet the original theorem

The diagonal lower bound requires an index \(A\) for the learner's strategy. It therefore applies to total computable deterministic learners, not to every set-theoretically possible (possibly noncomputable) deterministic strategy in the original paper's model. The randomized upper is valid for the displayed computable learner. The hypothesis class is defined using the fixed enumeration of computable policy kernels, and is independent of the horizon \(T\); only \(R_T\) depends on the horizon.

Thus this is a concrete separation for the explicitly restricted *computable-policy model*. It does **not** establish the requested separation for the unrestricted public partial-feedback model left open in Shao–Fang–Lin–Tao (arXiv:2601.21462v3, Section 5.3). That gap is substantive: an uncountable class of all noncomputable deterministic strategies cannot be substituted into this co-singleton permutation construction, because a per-context bijection into countable \(Y=\mathbb N\) forces the hypothesis index class itself to be countable.

No Lean or Rocq formalization of this new construction has yet been added; the asymptotic tail and diagonal arguments above are mathematical proofs in this research note and must be machine-checked before claiming formal verification.


## Audit: why the diagonal construction still does not cover every deterministic learner

Date: 2026-10-28. This section records an attempted unrestricted extension of the computable-policy construction. It is an obstruction to that *particular construction method*, not a theorem ruling out the original separation.

### The tempting non-injective extension

Let \(\mathcal A\) be an index set of deterministic policies. For a challenger \(A\in\mathcal A\) and context/history \(z\), let \(p_A(z)\in\mathbb N\) be its deterministic prediction. Define hypotheses with indices \(B\in\mathcal A\) by
\[
h_B(A,z)=
\begin{cases}
p_A(z),&B=A,\\
q_{A,z}(B),&B\ne A,
\end{cases}
\]
where \(q_{A,z}:\mathcal A\setminus\{A\}\to
\mathbb N\setminus\{p_A(z)\}\) is a surjection with every fibre infinite.

For any fixed \(A\), the target family \(F_A=\{h_B:B\ne A\}\) induces exactly the co-singleton \(\mathbb N\setminus\{p_A(z)\}\) at contexts whose challenger is \(A\). At contexts with challenger \(C\ne A\), removing just \(h_A\) does not remove any label from the image because every fibre of \(q_{C,z}\) is infinite and \(h_C\in F_A\); the induced label set remains all of \(\mathbb N\). Thus a deterministic learner \(A\), challenged at context \(A\) each round, can be wrong on all \(T\) rounds under one fixed \(F_A\). This repairs the local fibre collision in the earlier bijection-only construction.

For a randomized learner choosing uniformly from \(\{0,\ldots,t-1\}\), if the target index \(A\) is fixed and the challenger at round \(t\) is \(A\), then the current loss probability is at most \(1/t\), because the excluded label is the deterministic value \(p_A(z_t)\), chosen before the sample. At other challenger indices, the family \(F_A\) induces all labels and produces no loss. This is a useful local design idea.

### Why this is not yet a class for *all* deterministic policies

The definition above requires \(\mathcal A\) to index every permitted deterministic learner while also embedding \(A\) as a context coordinate visible to the learner. That self-indexing is impossible if learners are unrestricted functions and contexts themselves are drawn from the same set.

Let \(\kappa=|\mathcal X|\) be the cardinality of the instance space and let \(|\mathcal Y|\ge2\). Even the memoryless deterministic maps \(\mathcal X\to\mathcal Y\) have cardinality
\[
|\mathcal Y|^\kappa\ge2^\kappa>\kappa.
\]
Allowing dependence on finite histories does not reduce this lower bound. Therefore no context space of size \(\kappa\) can contain a distinct visible context code for every arbitrary deterministic policy over that same context space. For countable \(\mathcal X,\mathcal Y=\mathbb N\), there are already continuum-many deterministic maps, but only countably many context codes; for uncountable \(\mathcal X\), Cantor's theorem gives the analogous strict gap.

One could parameterize a narrower family such as computable or suitably coded measurable policies, but that no longer proves the required lower bound for *every* deterministic learner. If one uses Borel codes, the joint measurability of code-to-policy evaluation also needs a separate proof; it cannot simply be assumed for an unrestricted enumeration of all Borel functions.

### Current mathematical status

- The fibre-surjection formula above is a concrete repair of the *local* uniqueness/fibre issue in the diagonal construction.
- The unrestricted diagonal quantifier remains unmet because the strategy index cannot be inserted into the visible context for all set-theoretic policies by this route.
- This cardinality argument is **not** a no-go theorem for every possible hypothesis class: a successful class might diagonalize along paths without literally indexing policies in the context.
- No theorem establishing all three requested conditions in the unrestricted model, and no theorem ruling out such a class, has been obtained in this update.

Primary problem statement: Shao, Fang, Lin, Tao, *Partial Feedback Online Learning*, arXiv:2601.21462v3, Section 5.3 explicitly leaves the public-setting randomized-versus-deterministic learnability separation open. Theorem 19 there is only an oblivious-versus-public separation, not the requested result: https://arxiv.org/html/2601.21462v3
