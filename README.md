# ai-open-problem-lean-rocq-2026

This repository contains independent, machine-checked Lean 4 and Rocq developments for two related research tracks: public-setting partial-feedback online learning, and the information-complexity question for VC learning.

## Research background

Thomas Steinke and Lydia Zakynthinou posed the information-complexity question for VC classes in COLT 2020: https://proceedings.mlr.press/v125/steinke20b.html

Steve Hanneke and Juexiao Wang's paper, *The optimal information complexity of VC learning* (arXiv:2610.10600, submitted 2026-10-06; v2 revised 2026-10-15), reports an (O(d)) evaluated-CMI/eCMI result in the realizable case using a randomized Majority-of-5 construction: https://arxiv.org/abs/2610.10600v2

That mathematical result is **not proved by this repository's source files**. The code below only checks threshold shattering lemmas; it does not encode the information-theoretic definitions, PAC guarantee, Majority-of-5 construction, or the eCMI bound.

## Files and what is verified

- `Lean/VCLearning.lean`: Lean 4 core-only definitions for Boolean concepts and natural-number thresholds, plus proofs that every singleton can be shattered and no ordered pair (a<b) can be shattered.
- `Rocq/VCLearning.v`: independent Rocq 9.2 proofs of the corresponding singleton/pair shattering facts. These files contain no `sorry`, `admit`, or `Admitted`.
- `PublicSetting/Lean/` and `PublicSetting/Rocq/`: separate formalization of information order and globally consistent targets for public partial-feedback online learning. The exact randomized-versus-deterministic separation theorem remains open in the cited paper; the repository does **not** claim to have proved it.

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

The formalization is deliberately limited and explicit about its boundaries. No theorem asserting the eCMI (O(d)) result, and no theorem asserting the public randomized/deterministic separation, is currently proved in Lean or Rocq.
