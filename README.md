# ai-open-problem-lean-rocq-2026

This repository contains independent, machine-checked Lean 4 and Rocq developments for two related research tracks: public-setting partial-feedback online learning, and the information-complexity question for VC learning.

## Research background

Thomas Steinke and Lydia Zakynthinou posed the information-complexity question for VC classes in COLT 2020: https://proceedings.mlr.press/v125/steinke20b.html

Steve Hanneke and Juexiao Wang's paper, *The optimal information complexity of VC learning* (arXiv:2610.10600, submitted 2026-10-06; v2 revised 2026-10-15), reports an (O(d)) evaluated-CMI/eCMI result in the realizable case using a randomized Majority-of-5 construction: https://arxiv.org/abs/2610.10600v2

That mathematical result is **not proved by this repository's source files**. The code below only checks threshold shattering lemmas; it does not encode the information-theoretic definitions, PAC guarantee, Majority-of-5 construction, or the eCMI bound.

## Files and what is verified

- `Lean/VCLearning.lean`: Lean 4 core-only definitions for Boolean concepts and natural-number thresholds, plus proofs that every singleton can be shattered and no ordered pair (a<b) can be shattered.
- `Rocq/VCLearning.v`: independent Rocq 9.2 proofs of the corresponding singleton/pair shattering facts. These files contain no `sorry`, `admit`, or `Admitted`.
- `PublicSetting/Lean/OmegaOneSeparation.lean`: concrete Mathlib 4.35 development of the countable-cocountable probability space on ω₁, with a finite-horizon randomized zero-loss upper and a deterministic public-history lower bound of exactly T using one global target family.
- `PublicSetting/Rocq/OmegaOneSeparation.v`: independent abstract Rocq 9.2 counterpart for omega-one-like ordered label structures; it does not instantiate concrete ω₁.
- The literal inf-sup minimax operator is not separately defined in Lean, and the measurable space is not standard Borel; these boundaries are documented in PublicSetting/README.md.

The threshold results are a checked pair/singleton shattering characterization, not a separately defined global `VCDim = 1` theorem or a proof of the information-complexity result.

## Verify

From the repository root, with the pinned Lean toolchain installed:

```bash
lean Lean/VCLearning.lean
```

Rocq 9.2:

```bash
rocq compile Rocq/VCLearning.v
```

Public-setting Lean proofs:

```bash
cd PublicSetting/Lean
lake build
```

Public-setting Rocq proofs:

```bash
cd PublicSetting/Rocq
rocq compile -Q . PublicSetting PublicSetting.v
rocq compile -Q . PublicSetting PublicProtocol.v
```

GitHub Actions checks all four source modules. A green build means only that the exact statements encoded in those files have been checked; it does not validate unformalized claims in the research papers.

## Tracking and sources

- Original VC information-complexity question: https://proceedings.mlr.press/v125/steinke20b.html
- Hanneke–Wang 2026 preprint: https://arxiv.org/abs/2610.10600v2
- Public-setting partial-feedback question: https://arxiv.org/html/2601.21462v3
- Related set-valued feedback work: https://proceedings.mlr.press/v247/raman24b.html

## Status

The formalization is deliberately limited and explicit about its boundaries. The omega-one strategy-level finite-horizon separation is now machine-checked in Lean and its abstract counterpart in Rocq. The eCMI (O(d)) result is not proved in this repository.


## Public partial-feedback omega-one construction

The target open question is the final paragraph of Section 3.3 of arXiv:2601.21462v3. Section 3.2 contains a different finite-Helly/nested-inclusion necessity question. The Lean module concretely formalizes the countable-cocountable probability space on omega_1, zero-mass miss sets, path-dependent terminal-threshold error containment, and deterministic global-target lower bound. Rocq proves an abstract order/ideal counterpart. The full finite-product probability and literal minimax inf-sup are not yet formalized; details and CI status are in PublicSetting/README.md.


## Final verification (2026-10-31)

The latest Lean/Rocq code commits are 4ebc89d95a6deb59bf658c2e2c26bac897701f2a and b5940c796e71800125625cbe61f5502f98902da9. The final PR documentation head f0b7fdc755ff827aefe4f4d96e1111201bf5c68e passed both Lean and Rocq CI. The exact run links and remaining formalization scope boundaries are recorded in PublicSetting/README.md.
