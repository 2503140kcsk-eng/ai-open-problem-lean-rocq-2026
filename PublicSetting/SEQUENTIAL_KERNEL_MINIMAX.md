# Sequential kernels, the tower property, and minimax: formalization boundary

Status date: 2026-10-31

This note documents the Lean module `Lean/SequentialKernelMinimax.lean`. It deliberately distinguishes the general theorem proved by the module from the stronger claim needed to close the public partial-feedback question.

## 1. The sequential probability model

For measurable state spaces `State n`, take history-dependent Markov kernels

```
κ n : Kernel (Π i : Finset.Iic n, State i) (State (n+1)).
```

The input at time `n` contains the complete history up to `n`; therefore this is not a Markov restriction on the visible state alone. A measurable map

```
initial : E × F → (Π i : Finset.Iic 0, State i)
```

encodes a pair of strategy parameters into the initial history. The definition `strategyPathKernel` composes the deterministic initial kernel with Mathlib's Ionescu–Tulcea trajectory kernel:

```
Kernel.traj κ 0 ∘ₖ Kernel.deterministic initial hinitial
```

The resulting kernel maps a strategy pair to a probability law on complete paths. The Markov property follows when every one-step transition is a Markov kernel.

Mathlib already proves finite-prefix consistency in `Kernel.traj_comp_partialTraj`; this is wrapped as `finitePrefix_consistency`.

## 2. Tower property

The exact Mathlib result is `Kernel.condExp_traj`, wrapped as `trajectory_tower`. If (a\le b), (f) is integrable on the full trajectory law, and the information up to (b) is represented by the canonical product filtration, then

[
\mathbb E[f(X_0,X_1,\ldots)\mid\mathcal F_b](x)
=
\int f(\omega)\,\mathrm{traj}(\kappa,b,x_{\le b})(d\omega)
quad\text{a.e.}
]

This is the precise finite-prefix-to-full-trajectory bridge. It is an almost-everywhere identity and requires integrability. It does not turn a nonmeasurable pathwise loss into a measurable one.

## 3. Strategy spaces

`CompactConvexStrategySpace` records the exact topological hypotheses Sion needs: a nonempty, compact, convex carrier in a real topological vector space.

For a finite game, the intended concrete strategy domain is the probability simplex over a player's finite set of pure contingent plans. A pure contingent plan specifies an action at every information history; a mixed strategy is a probability vector over these plans. This normal-form representation makes the expected payoff bilinear in the two players' mixed-strategy vectors. In finite games with perfect recall, Kuhn's theorem additionally gives outcome-equivalence between mixed and behavioral strategies. Without perfect recall, this equivalence can fail.

Important formalization boundary: the current Lean module defines the compact-convex strategy-space interface, but does not yet prove the finite-simplex instantiation or formalize the mixed/behavioral equivalence theorem. The fields should not be mistaken for that missing proof.

## 4. Minimax conclusion

`SequentialKernelGame` packages:

- the two compact convex strategy carriers;
- a history-dependent transition-kernel family and a measurable initial-state map;
- the induced full-trajectory kernel and an integrable terminal reward;
- lower semicontinuity and quasi-convexity in the minimizing player's strategy;
- upper semicontinuity and quasi-concavity in the maximizing player's strategy.

Under these hypotheses, `sequential_kernel_minimax` applies Mathlib's `Sion.minimax'` and proves

[
\inf_{x\in X}\sup_{y\in Y} J(x,y)
=
\sup_{y\in Y}\inf_{x\in X} J(x,y),
qquad
J(x,y)=\int r(\omega)\,K(x,y)(d\omega).
]

These are substantive hypotheses. Kernel measurability alone does not imply convexity, continuity, compactness, or minimax equality. For finite normal-form games, bilinearity of the expected payoff supplies the relevant quasi-convexity / quasi-concavity; the finite simplex compactness and bilinearity proofs remain a separate formalization task.

## 5. Why this does not yet close the omega-one candidate

The omega-one construction in `OmegaOneSeparation.lean` uses the countable-cocountable sigma algebra on (omega_1) and its 0/1 probability measure. Its current proofs establish fixed-witness nullity and a finite-product null-event result for a fixed vector of visible witnesses. They do not yet establish a fully measurable pathwise loss for arbitrary history-adaptive witness policies.

There is a concrete measurability obstruction to the direct full-path route proposed in this module.

Let (Omega=omega_1), let (mathcal C) be the countable-cocountable sigma algebra, and let (mu(A)=0) for countable (A), (mu(A)=1) for cocountable (A). The successor map (s(alpha)=alpha+1) is (mathcal C/mathcal C)-measurable: the preimage of a countable set is countable, and the preimage of a cocountable set is cocountable.

Consider a two-stage adaptive policy which, after observing (X_1=\alpha), reveals the witness/threshold (s(\alpha)) before the second draw (X_2). The second-round miss section is

[
M_\alpha=\{\beta:\beta<s(\alpha)\}=\{\beta:\beta\le\alpha\},
]

which is countable for each fixed (alpha<omega_1), hence (mu(M_\alpha)=0).

But the global relation

[
M=\{(\alpha,\beta):\beta\le\alpha\}
]

is not in (mathcal C\otimes\mathcal C). To see this, note that every set in (mathcal C\otimes\mathcal C) must be constant on some co-countable rectangle (A^c\times B^c): the class of sets with this property is a sigma algebra containing every measurable rectangle. The relation (M) is not constant on any such rectangle, since both (\beta\le\alpha) and (\alpha<\beta) occur with (\alpha\in A^c,\beta\in B^c), as both co-countable subsets of (omega_1) are unbounded.

Thus sectionwise nullity does not imply that the pathwise error event is product-measurable. This blocks a direct application of `trajectory_tower` to that unrestricted adaptive loss. It does **not**, by itself, refute a separately defined recursively iterated game value that evaluates each conditional section before integrating over the past; that alternative semantics would need its own formal definition and proof.

Consequently the general Lean theorem is complete under its stated measurable-payoff and Sion regularity assumptions, but it is not yet an instantiation for the unrestricted omega-one public protocol. To close that gap one must either:
1. impose joint measurability (and prove it for the allowed adaptive adversary policies), or
2. formalize a stagewise/iterated-risk semantics that does not require a jointly measurable terminal loss, and then prove its tower law directly.

One must also prove that the chosen strategy space is compact convex and that the induced payoff satisfies Sion's hypotheses. It is not valid to assume these facts merely because every local move is a probability distribution.

## 6. Tool and repository responsibilities

The tools and repositories have distinct jobs; not all are proof engines for this theorem.

| Resource | Assigned role | What it must not be treated as |
|---|---|---|
| `leanprover-community/mathlib4` | Trusted definitions and theorems for kernels, Ionescu–Tulcea, conditional expectation, and Sion | Evidence that the application-specific hypotheses are already proved |
| `lean-dojo/LeanDojo-v2` | Retrieve relevant declarations and suggest proof search steps | A proof checker; Lean's kernel remains the checker |
| `cvc5` | Discharge finite arithmetic / first-order side conditions and counterexample search | A measure-theory or Lean proof substitute |
| `sympy`, `sagemath` | Exact finite matrix calculations, symbolic payoff simplification, and numerical sanity checks | A source of general minimax proofs |
| `gap-system/gap` | Finite group symmetries or orbit reduction if a game instance has group structure | A relevant tool for arbitrary measurable kernels |
| `Macaulay2/M2` | Algebraic-geometric elimination only if strategy constraints are polynomially parameterized | A direct probability-kernel formalizer |
| `naproche` | Check structured natural-language mathematical exposition | A replacement for Lean verification |
| Wolfram | Exact small-game examples and independent numerical checks | A proof of the general theorem |
| Sider Scholar / Parallel Search | Literature retrieval and cross-checking assumptions | Formal verification |
| Context7 | Current Mathlib declaration/import lookup | A proof checker |
| GitHub Actions | Reproducible Lean/Rocq build on the pinned toolchain | Evidence beyond the job's exact commit and target |

## 7. Reproducibility

From `PublicSetting/Lean`:

```sh
lake build SequentialKernelMinimax
```

The package default build now includes `SequentialKernelMinimax`. Record the exact commit and both Lean/Rocq CI results when reporting verification.
