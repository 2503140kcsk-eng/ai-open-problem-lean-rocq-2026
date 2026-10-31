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
