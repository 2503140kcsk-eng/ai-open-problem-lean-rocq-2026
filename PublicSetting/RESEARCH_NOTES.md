# Research notes: public-setting randomized/deterministic separation

Date: 2026-10-28

## Exact question

Find either (A) a public partial-feedback online-learning game with a fixed hypothesis class H and a single global target subfamily F such that randomized minimax regret is o(T) and every deterministic learner has Ω(T) minimax regret, or (B) a theorem ruling out every such construction.

The horizon quantifier matters. A result for one finite T does not establish asymptotic learnability. The sublinear upper bound must hold for all sufficiently large horizons with ratio regret/T tending to zero; the deterministic lower bound must hold with one positive constant (possibly depending on the deterministic learner if that is the chosen quantifier convention) for all sufficiently large horizons.

## Literature audit

Primary source: Shihao Shao, Cong Fang, Zhouchen Lin, Dacheng Tao, “Partial Feedback Online Learning,” arXiv:2601.21462v3, dated 2026-04-02. The final paragraph of Section 3.2 asks whether finite Helly number or the nested-inclusion condition is necessary for inseparability. Section 3.3 also studies the separate distinction between oblivious and public adversaries. The same paper proves a different result, Theorem 18: randomized learnability under the oblivious setting can fail to persist under the public setting. The two statements must not be conflated.

- Paper: https://arxiv.org/abs/2601.21462
- HTML source: https://arxiv.org/html/2601.21462v3
- Related set-valued feedback paper: https://proceedings.mlr.press/v247/raman24b.html

A fresh search on 2026-10-29 did not find a later publication resolving the exact public-setting question. Search absence is not mathematical proof of open status.

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

## Formal finite-sampler moment-to-probability bridge (2026-10-29)

`Lean/AdaptiveMoments.lean` explicitly defines the sequential sampler: at a history of length n, draw uniformly from 0,...,n. Its finite future-path count is proved to satisfy `uniformFuturePathCount T 0 = factorial T`, so each complete path has mass 1/T!. For every predictable target, the unnormalized sum of `2^(number of matches)` over the full path tree is at most `(T+1) * T!`; after division by the verified path count, Lean proves the rational expectation bound `E[2^M] <= T+1`. It then defines the actual rational tail probability and proves `2^K * P(M >= K) <= T+1`. For any finite candidate list, a union-bound budget is proved in rational form in Lean; Rocq independently checks the corresponding path count, integer-scaled per-target tail bound, and finite-candidate aggregate in Rocq 9.2.

This is a fully checked moment-to-tail result for the explicit finite sampler, not a full conditional-expectation proof for arbitrary `NatSubprobability` learner distributions. It does not by itself establish the randomized o(T) upper bound for the public learning game; the adversary timing, target-family realizability, and loss-to-score reduction still have to be connected to the probability model.


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


## Re-audit: computable diagonal candidate and the exact scope of its proof

Date: 2026-10-28. **Correction to the immediately preceding audit:** the alleged singleton-target counterexample was invalid for the construction as specified. That construction fixes the admissible set family to
\[
\mathcal S(\mathbb N)=\{\mathbb N\setminus\{y\}:y\in\mathbb N\}.
\]
A target family \(F^\star=\{h_B\}\) induces a singleton label set, not a co-singleton, and is therefore *not a legal set-realizable target family* in this game. The earlier statement that this disproved the randomized upper bound is retracted.

### Validity of the randomized upper in the restricted computable-policy model

In the bijective construction, every context \(x\) has an evaluation bijection
\[
\phi_x:\mathbb N\to\mathbb N,\qquad \phi_x(B)=h_B(x).
\]
If a fixed subfamily \(F^\star\subseteq\mathcal H\) induces an admissible set at even one visited context \(x_t\), then
\[
F^\star(x_t)=\phi_{x_t}(\{B:h_B\in F^\star\})
\]
must be a co-singleton. Since \(\phi_{x_t}\) is a bijection, the hypothesis-index set must itself be a co-singleton. Thus every legal fixed target family along a nonempty transcript is of the form
\[
F^\star=\{h_B:B\ne B^\star\}
\]
for one *fixed* index \(B^\star\). The earlier union bound over \(B^\star\) is therefore applicable; it is not missing singleton or arbitrary smaller target families, because those induce inadmissible sets.

For the horizon-free learner \(R\) that samples independently and uniformly from \(\{0,\ldots,t-1\}\) at round \(t\), write \(M_B\) for the number of rounds on which its sampled label equals \(h_B(x_t)\). Conditional on the past and the current context, the match probability for every \(B\le T\) is at most \(1/t\). If \(H_T=\sum_{t=1}^T1/t\), then
\[
\Pr(M_B\ge k)\le H_T^k/k!\le(eH_T/k)^k,
\]
and a union bound over \(B\le T\) gives
\[
\mathbb E[\max_{B\le T}M_B]=O(\log(T+2)).
\]
For \(B>T\), a match is possible only on a round with challenger index \(C_t=B\), and the expected number of such exceptional matches is at most \(H_T\). Hence, for every legal terminally selected target family,
\[
\mathbb E[\operatorname{Regret}_T(R)]
\le \mathbb E[\max_B M_B]=O(\log(T+2))=o(T).
\]
The same bound and Markov's inequality imply that linear-loss paths have probability tending to zero. The adversary may choose contexts adaptively from prior realized predictions; the bound conditions on the current context before the current draw.

### Exact scope: what this does and does not establish

The construction is a valid separation **for total computable learner policies**, under the expressly co-singleton admissible set family and the stated public protocol:
- For a deterministic computable learner with index \(A\), choosing \(C_t=A\) makes \(h_A(x_t)\) its deterministic prediction. The single fixed family \(\{h_B:B\ne A\}\) then makes the allowed set a co-singleton excluding that prediction at every round, so loss is \(T\).
- For the randomized learner \(R\), the preceding argument gives expected regret \(O(\log T)\) against every legal target family.

This is **not yet the requested unrestricted theorem**. The class enumerates computable policies as challenger indices, so it does not give condition 1 for arbitrary, possibly noncomputable deterministic policies. The countability/cardinality issue described in the next section blocks a direct extension that tries to encode every strategy as a context label. It does not prove that every conceivable hypothesis-class construction is impossible.

The learner-specific construction and its full-game probability tail proof remain mathematical arguments, not yet a Lean/Rocq proof of the requested separation. Separately, the finite sequential-uniform sampler's moment-to-tail bridge is now machine-checked in `AdaptiveMoments`: the complete path count is T!, its exponential match moment is at most T+1, and each predictable target's tail probability is at most (T+1)/2^K; finite-candidate aggregation is proved as a rational bound in Lean and a cross-multiplied integer bound in Rocq. These generic sampler theorems are not yet connected to an o(T) minimax-regret theorem for the full public protocol. The unrestricted public-setting question remains explicitly open in Shao–Fang–Lin–Tao, *Partial Feedback Online Learning*, at the end of §5.2: https://arxiv.org/html/2601.21462v3.
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

For a randomized learner choosing uniformly from \(\{0,\ldots,t-1\}\), if the target index \(A\) is fixed and the challenger at round \(t\) is \(A\), then the current loss probability is at most \(1/t\), because the excluded label is the deterministic value \(p_A(z_t)\), chosen before the sample. At other challenger indices, the family \(F_A\) induces all labels and produces no loss. This is a useful local design idea, **not a randomized upper bound for the game**. The legal target family need not be \(F_A\): for example, \(F^\star=\{h_B\}\) is also legal and yields the singleton acceptable set \(S_t=\{h_B(x_t)\}\). A proof of condition 2 must bound regret uniformly over every such subfamily, not just complements of one indexed hypothesis. The singleton-family counterexample in the preceding corrected section illustrates this gap.

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

Primary problem statement: Shao, Fang, Lin, Tao, *Partial Feedback Online Learning*, arXiv:2601.21462v3. The final paragraph of Section 3.2 asks whether finite Helly number or the nested-inclusion criterion is necessary for deterministic/randomized inseparability. Theorem 18 there is only an oblivious-versus-public separation, not the requested result: https://arxiv.org/html/2601.21462v3


## Formalized quantifier boundary: what can and cannot be ruled out

Date: 2026-10-29.

The Lean and Rocq adaptive-moment modules now include two complementary results.

1. The theorem same_fixed_target_linear_lower_bound_survives_mixing proves the conditional no-go statement: if one and the same target induces loss at least c*T for every deterministic policy in the support of a randomized mixture, then the mixture's expected loss is also at least c*T. The code states the inequality after multiplying by the number of equally weighted sample outcomes, so there is no hidden division or probability axiom.
2. The theorem diagonalTarget_uniform_sum_lt_sample_count / diagonal_target_uniform_sum_lt_sample_count formalizes a finite loss-matrix counterexample to an invalid quantifier inference. With T+1 deterministic policies and T+1 targets, policy i loses T against target i and zero against every other target. Each deterministic policy therefore has worst-target loss T, yet for every fixed target the sum over all equally likely policies is at most T, strictly less than the number of policies T+1. The uniform mixture's average loss is therefore at most T/(T+1) < 1 although every deterministic policy has linear worst-target loss.

The second result is a countermodel for the quantifier logic, **not** a claim that this matrix is realizable as a legal partial-feedback online-learning game. It shows why the implication
\[
\forall A\ \exists F_A:\ \mathrm{Loss}(A,F_A,T)\ge cT
\quad\Longrightarrow\quad
\exists F\ \mathbb E_{A\sim\mu}[\mathrm{Loss}(A,F,T)]\ge cT
\]
is invalid in general. The first theorem rules out only the stronger interpretation where a single fixed target F, independent of the deterministic policy, gives the linear lower bound to every policy in the mixture support.

Consequently, neither the fixed-target mixing argument nor the cardinality obstruction to self-indexing all strategies proves that the original unrestricted public-setting separation is impossible. The cardinality obstruction is limited to that particular diagonal-construction route. Conversely, the finite matrix countermodel does not establish that a valid set-realizable hypothesis class with a randomized o(T) upper bound and Omega(T) lower bounds for all deterministic learners exists.

As of this update, Shao, Fang, Lin, and Tao's arXiv v3 (2026-04-02), Section 3.3 explicitly leaves the exact randomized-versus-deterministic learnability separation in the public setting open; it warns that the oblivious-versus-public separation is a different result. The present audit did not find a later source resolving this exact necessity question. This is evidence about the state of the literature, not a proof of impossibility.


## 2026-10-31: omega-one countable/cocountable candidate

### Candidate game

Take the label space Y to be the first uncountable ordinal omega_1. Give it the countable-cocountable sigma algebra:
Sigma = {A subset Y : A is countable or Y minus A is countable}.
Define mu(A)=0 for countable A and mu(A)=1 for cocountable A. Let the prescribed admissible family be the upper tails
S_beta = {alpha < omega_1 : beta <= alpha}, for beta < omega_1.
Let X=N and H=Y^N.

The sigma algebra is closed under complements. For a countable union, if every member is countable then the union is countable; otherwise one member is cocountable, so the complement of the union is a subset of that member's countable complement. This proves closure under countable unions.

The mass is countably additive on disjoint measurable sequences. If one member A_i is cocountable, every other disjoint member is contained in its countable complement, hence countable; the union is cocountable and exactly one summand has mass one. If there is no cocountable member, every member and their countable union are countable, so both sides are zero. Thus mu is a probability measure.

For every beta < omega_1, the initial segment [0,beta) is countable. Hence mu([0,beta))=0 and mu(S_beta)=1.

### Randomized upper bound under the paper's measurable-space model

The learner chooses mu at every round. Consider any public history and its next visible witness w_t. The terminal target subfamily may be selected after the sampled predictions, but it must be globally consistent and its acceptable set at x_t must be an admissible upper tail S_{beta_t} containing w_t. Thus beta_t <= w_t. A mistake at round t implies
prediction < beta_t <= w_t,
so every possible miss is contained in [0,w_t), which has mu-measure zero. This is a pointwise containment, so it is unaffected by how the terminal target is selected after the predictions. Conditional on every pre-round public history and witness, the expected round loss is zero. Consequently the randomized regret is zero for every finite horizon T in the paper's abstract probability-measure strategy model.

The formal lemma needed for this argument is stronger than fixing one threshold: for every function beta:Y->Y satisfying beta(y)<=w for all y, the miss set {y : not beta(y)<=y} is contained in [0,w). It therefore covers threshold selection depending on the current sampled label. Conditioning on the other sampled labels yields the same pointwise argument for a terminal family selected from the entire path.

### Deterministic lower bound with one global target

Fix an arbitrary deterministic learner and its induced prediction path p_t at contexts x_t=t. Let the adversary reveal the witness w_t=p_t+1, and let the target threshold at context t also be p_t+1. Define one target family
F* = {f:N->omega_1 : for every t, p_t+1 <= f(t)}.
This family is nonempty (take f(t)=p_t+1). Since H is the full product Y^N, its coordinate image at t is exactly S_{p_t+1}. Hence the same global F* induces all acceptable sets simultaneously. Each witness belongs to its tail, while p_t does not. The deterministic learner therefore loses exactly T rounds. Because the construction can be made against every deterministic learner, the deterministic minimax regret is T.

### Why Theorem 15 does not apply

For every countable sequence beta_n < omega_1, regularity/cofinality of omega_1 gives an upper bound beta < omega_1. The label beta then belongs to every S_{beta_n}, so the intersection is nonempty. This rules out a countable decreasing sequence of upper tails with empty intersection. Every finite family is also countable and has nonempty intersection. However the intersection over all beta < omega_1 is empty. The sufficient structural hypotheses in Theorem 15 are therefore both false for this admissible-set family.

### Model boundary and foundations

This candidate uses the paper's very general formulation in which the label space is equipped with an arbitrary sigma algebra and randomized actions may be arbitrary probability measures on that measurable space. The countable-cocountable space on omega_1 is not standard Borel and is not asserted to be realizable by an ordinary real-valued random-number generator. The result should not be generalized to standard Borel / countably generated / algorithmically samplable label spaces without a separate proof.

### Formalization status

- Lean: PublicSetting/Lean/OmegaOneSeparation.lean is a concrete Mathlib development of omega_1, the countable-cocountable sigma algebra, the probability measure via Measure.ofMeasurable, countable upper-tail intersection, adaptive miss-set nullity, and the one-global-target deterministic lower bound.
- Rocq: PublicSetting/Rocq/OmegaOneSeparation.v proves the same measure/game lemmas abstractly for an ordered label type supplied with a countable ideal, small initial segments, successor, and countable boundedness. The Rocq Stdlib project does not supply a concrete omega_1 ordinal/measure instance in this project, so this is not yet a concrete duplicate of the Lean instantiation.
- Both updated CI tracks are queued as of 2026-10-31 in GitHub Actions. Until the logs complete successfully, the sources are formalization drafts, not completed machine-checked proof artifacts.

### Next formal verification boundary

The Lean file contains a finite-horizon strategy-level theorem quantifying over all upper-tail sequences and all deterministic public-history learners. The literal inf-sup minimax operator from Appendix G is not separately declared in Lean. The remaining formal-strengthening option is to encode that operator explicitly without weakening the fixed-global-target condition or moving the visible witness after the current sample.


## 2026-10-31 verification update

The latest source commit with the exact public-history learner interface is 1168ded2065bc238a1f6978b5b48addfece2dee3. GitHub Actions run 41157208222 passed both Lean 4.35 and Rocq 9.2. Both logs were inspected; Lean contains no warning diagnostics (the string Cache.Warning:c.o is a build-artifact name, not a compiler warning) and Rocq is clean. The Lean theorem omegaOne_finite_horizon_separation formalizes the strategy-level finite-horizon bounds; Rocq remains an abstract ordered-type counterpart rather than a concrete omega_1 instantiation.

The public-history type is List (Nat × Label × Label), storing (context, visible label, realized prediction). This allows deterministic strategies to depend on the previous sampled predictions visible in the public protocol. The randomized policy is the constant countable-cocountable probability measure; the error-event argument is pointwise contained in a null initial segment, including terminal upper-tail choices compatible with the visible witness.
