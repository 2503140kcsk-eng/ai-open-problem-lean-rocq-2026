# Exact RNG compatibility: a formal no-go result

Status: added as a Rocq proof artifact; see `Rocq/PRNGNoGo.v`.

## The target measure

The omega-one candidate uses the countable-cocountable sigma algebra on the
label space (Y=\omega_1), with

[
  \mu(A)=0 \quad\text{when }A\text{ is countable},\qquad
  \mu(A)=1 \quad\text{when }Y\setminus A\text{ is countable}.
]

Every singleton, and therefore every countable subset of (Y), has measure
zero. The whole space has measure one.

## The exact obstruction

Let (S) be a seed space that can be enumerated by a surjection
(e:\mathbb N\to S), let (g:S\to Y) be any deterministic sampler, and
let (\nu) be any source probability measure on (S). The output range

[
  R_g=\{g(s):s\in S\}
]

is countable. Hence the target assigns (\mu(R_g)=0). But every source
sample is mapped into (R_g), so the pushforward assigns

[
  (g_*\nu)(R_g)=\nu(g^{-1}(R_g))=\nu(S)=1.
]

Therefore (g_*\nu\ne\mu). The proof does not depend on how the source
probabilities are distributed, only on total mass one and the countability
of the sampler's output range.

The Rocq theorem `no_enumerable_seed_sampler_realizes_target` formalizes this
mismatch for an abstract scalar type with distinct zero and one. It covers
finite-seed PRNGs and countable seed spaces. A terminating program that emits
a finite formal description also has at most countably many possible outputs,
so it cannot exactly generate this target law through such descriptions.

This is stronger than a practical limitation: the total-variation distance
from any countably-supported output law to the target is already 1, witnessed
by the countable range itself. A finite-precision approximation cannot
converge to the target in total variation.

## What remains possible

1. Keep the omega-one measure as an abstract mathematical probability space,
   without claiming an executable sampler.
2. Replace the target measurable space or the target law with a standard-Borel
   model and prove the consequences for the learning problem again. This is a
   change of mathematical model, not an implementation of the same measure.
3. Introduce an idealized oracle that directly samples from the nonstandard
   space. Such an oracle is a specification assumption, not an ordinary
   finite-seed or terminating PRNG.

## Scope and limitations

The theorem does not show that every imaginable set-theoretic map from an
uncountable probability space into (\omega_1) is impossible. It rules out
countably-supported samplers, including ordinary executable samplers with
finite or countably many finite outputs. It also does not construct
(\omega_1) inside Rocq; the existing Rocq game development still assumes an
abstract ordered label type with countable-ideal axioms. A concrete Rocq
construction of the quotient of countable well-orders remains a separate
formalization task.

## Verification

The GitHub workflow compiles this file with the repository's pinned
Rocq 9.2.0 container, after compiling `OmegaOneSeparation.v`.

## Boundary: an ideal real-valued source is a different question

The countable-range theorem above must not be overextended to arbitrary
uncountable source spaces. For a Lebesgue-uniform source
`([0,1], Leb)`, existence of a measurable map
`f : [0,1] -> omega_1` whose pushforward is exactly the countable-cocountable
0/1 measure is equivalent to

[
  \operatorname{cov}(\mathcal N) \leq \aleph_1,
]

where `cov(N)` is the least cardinality of a family of Lebesgue-null sets
covering the real line.

**Forward direction.** If `f_* Leb = mu`, then each fiber
`f^{-1}({alpha})` has Lebesgue measure zero, because every singleton in
`omega_1` is countable and hence has target measure zero. These at most
`aleph_1` fibers cover `[0,1]`, so `cov(N) <= aleph_1`.

**Reverse direction.** Suppose `[0,1]` is covered by
`aleph_1` Lebesgue-null measurable sets `N_alpha`, indexed by
`alpha < omega_1`. Replace the cover by the disjoint measurable pieces
`P_alpha = N_alpha minus union_{beta<alpha} N_beta`.
Every `alpha < omega_1` is countable, so the union removed at stage alpha
is a countable union of null sets. Thus each `P_alpha` is null, and the
pieces partition `[0,1]`. Define `f(x)=alpha` on `P_alpha`. The inverse
image of every countable subset of `omega_1` is a countable union of null
sets; hence `f` is measurable for the countable-cocountable sigma algebra
and has exactly the desired pushforward law.

Consequently CH (which gives continuum = aleph_1) is sufficient, while
set-theoretic models with `cov(N) > aleph_1` preclude such a pushforward.
Shelah's paper *Covering of the Null Ideal May Have Countable Cofinality*
shows the consistency of `cov(N)=aleph_omega`, which is one example of a
value strictly above `aleph_1`.

This is a mathematical existence criterion for a highly nonconstructive map
from an ideal continuum of exact real randomness. It is **not** an ordinary
finite-state PRNG, a finite-bit output routine, or an executable construction
of countable ordinals. The Rocq theorem in `PRNGNoGo.v` addresses the latter
countable-output setting only.

