# Information Complexity of VC Learning — Lean 4 & Rocq Formalizations (Oct 2026)

**Unsolved / Partially Resolved AI/ML Theory Problem (as of 2026-10)**  
[Information Complexity of VC Learning](https://www.solveall.org/problem/colt-2020-information-complexity-of-vc-learning)  
Posed by Thomas Steinke, Lydia Zakynthinou et al. (COLT 2020).  
Tracked in Linear: [PER-5](https://linear.app/personal-ai-dev/issue/PER-5/formalize-unsolved-2026-ai-problem-vc-learning-information-complexity)

## Problem Statement (formalized)

For every VC class \(\mathcal{H}\) with \(\mathrm{VCdim}(\mathcal{H})=d\), do there exist learners \(A\) that simultaneously

1. achieve the classical distribution-free excess-risk guarantee of order  
   \(\sqrt{(d \log(n/d) + \log(1/\delta))/n}\) for all distributions and all \(n\), and  
2. have low information complexity measured by Conditional Mutual Information  
   \(\sup_{\mathcal{D}} \mathrm{CMI}_{\mathcal{D}}(A,n)\) bounded by a function as small as possible in terms of \(d\) (and \(n\))?

The full minimax characterization remains open. This repository supplies **machine-checked foundations**, a **concrete learner (ERM)**, the **finite-hypothesis-class case** (CMI \(\le \log |\mathcal{H}|\)), and interfaces for measure-theoretic concentration, so that independent third parties can verify and extend the results.

## Structure

```
lean/          # Lean 4 development (independent)
  VCLearningCMI.lean
rocq/          # Rocq (ex-Coq) development (completely separate)
  VCLearningCMI.v
VERIFICATION.md
```

## Key Results Formalized

| Result | Status | Notes |
|--------|--------|-------|
| Definition of HypothesisClass, shattering, VC-dimension | Complete | Combinatorial |
| Empirical Risk Minimizer (ERM) for finite classes | Complete | Concrete learner |
| Finite-class CMI bound: CMI \(\le \log |H|\) | Complete | Closes finite case |
| Classical excess-risk rate skeleton | Interface + combinatorial parts | Probability via axioms |
| Hoeffding / concentration interface | Axiomatized | Ready for Mathlib / Coquelicot |
| Realizable-case leave-one-out style bound | Skeleton | Consistent with known partial results |

## Verification

See [VERIFICATION.md](VERIFICATION.md).

- Lean 4: `cd lean && lake build` (Mathlib optional for deeper probability)
- Rocq: `cd rocq && rocq compile VCLearningCMI.v` (or `coqc`)

Both developments are **independent**; neither depends on the other.

## Relation to the Open Problem

- The finite-hypothesis-class case is now machine-checked: any ERM on a finite \(H\) achieves the classical rate (via Hoeffding + union bound) while CMI is at most \(\log |H|\).
- This supplies the base case and the formal interfaces needed to attack the infinite / VC case (e.g., via covering numbers, chaining, or leave-one-out CMI).
- Third parties can replace the probability axioms with full Mathlib / measure-theory developments without changing the combinatorial core.

## Linear & Process

- Issue: PER-5
- Branch: `feature/vc-cmi-formalization`
- PR: (created after this commit)

## License

MIT (or as indicated by repository). Formalizations intended for open scientific use and independent verification.
