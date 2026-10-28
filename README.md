# ai-open-problem-lean-rocq-2026

Formalizations in **Lean 4** and **Rocq** of progress on an unsolved (as of early Oct 2026) / partially resolved AI/ML theory problem:

**Information Complexity of VC Learning** (Steinke & Zakynthinou, COLT 2020).

## Problem

Do VC classes of dimension *d* admit learners with information complexity (CMI or eCMI) *O(d)* that recover the optimal PAC rates from uniform convergence?

- ERMs achieve CMI *O(d log n)*.
- Proper learners have negative results for pure *O(d)* in general.
- **Progress (Hanneke & Wang, arXiv:2610.10600, 6 Oct 2026)**: Yes for *evaluated* CMI in the realizable case, via randomized Majority-of-5 of optimal base learners. eCMI = *O(d)*.

This repo provides *independently verifiable* formal skeletons so a third party can type-check the statements without trusting informal papers or this author.

## Files

- `Lean/VCLearning.lean` — Lean 4 + Mathlib: VC-dim definition, thresholds class, placeholder theorems.
- `Rocq/VCLearning.v` — Independent Rocq development of the same concepts.

## How to verify

**Lean 4** (with Mathlib):
```bash
lake build
# or open in VS Code / Cursor with Lean extension and check the file
```

**Rocq**:
```bash
coqc Rocq/VCLearning.v
```

## Tracking & documentation

- Linear issue: [PER-5](https://linear.app/personal-ai-dev/issue/PER-5/formalize-unsolved-2026-ai-problem-vc-learning-information-complexity)
- Notion page: [2026 AI Open Problem: Information Complexity of VC Learning — Lean & Rocq Formalizations](https://app.notion.com/p/40736596197c817da13be9613ff4dd38)

## Status

Skeletons committed 2026-10-28. Full machine-checked proofs of the Hanneke–Wang construction and complete CMI theory remain future work; the current artifacts already allow independent checking of the problem formalization and the classic VC-dim = 1 for thresholds.

Created in response to a request to select a realistic 2026 AI open problem solvable in principle by current models and produce dual Lean/Rocq artifacts for third-party verification, while maximally exercising free GitHub / Linear / Notion / Vercel connectors.
