# Sources checked on 2026-10-28

1. Shao, Shihao; Fang, Cong; Lin, Zhouchen; Tao, Dacheng. “Partial Feedback Online Learning.” arXiv:2601.21462v3, dated 2026-04-02. Primary source for the public randomized-versus-deterministic learnability question at the end of Section 3.3, Theorem 15's sufficient inseparability criteria in Section 3.2, and, separately, the oblivious-versus-public comparison in Section 3.3. Theorem 17 proves equality for set-valued feedback; Theorem 18 proves the oblivious-versus-public separation for partial feedback.
   - https://arxiv.org/abs/2601.21462
   - https://arxiv.org/html/2601.21462v3

2. Raman et al. “Online Learning with Set-valued Feedback.” Proceedings of Machine Learning Research 247 (2024). Related background: deterministic and randomized learnability can differ with set-valued feedback, but this is not the same as the public partial-feedback question.
   - https://proceedings.mlr.press/v247/raman24b.html

3. Lean 4 project and theorem kernel documentation.
   - https://github.com/leanprover/lean4
   - https://lean-lang.org/doc/reference/latest/

4. Rocq Prover official project and compilation documentation.
   - https://github.com/rocq-prover/rocq
   - https://rocq-prover.org/install
   - https://rocq-prover.org/refman/practical-tools/utilities.html


5. Raman, Vinod; Subedi, Unique; Tewari, Ambuj. “Online Learning with Set-valued Feedback.” PMLR 247 (2024), Section 4.1, Theorem 3. Used to audit why the usual randomized-versus-deterministic separation does not immediately yield a public set-realizable partial-feedback separation.
   - https://proceedings.mlr.press/v247/raman24b.html
   - https://ar5iv.labs.arxiv.org/html/2306.06247

The literature search was performed through academic and web-search connectors. It is not an exhaustive proof of nonexistence of a later result.


6. MathOverflow discussion, “Inner Regularity of probability measure on totally ordered sets” (2019-10-07). The answer by Andrés E. Caicedo explicitly describes the omega-one ordered label space, the sigma algebra of countable or cocountable sets, and the 0/1 probability measure used in the present candidate.
   - https://mathoverflow.net/questions/343303/inner-regularity-of-probability-measure-on-totally-ordered-sets

7. MathOverflow discussion, “Measure on omega_1” (2011-11-17). Gives the countable-cocountable sigma algebra on omega_1 and the probability measure assigning zero to countable sets and one to cocountable sets.
   - https://mathoverflow.net/questions/81143/measure-on-omega-1

8. Mathlib 4.35.0 source files used to select exact theorem/API names for the concrete Lean formalization.
   - https://github.com/leanprover-community/mathlib4/blob/v4.35.0/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean
   - https://github.com/leanprover-community/mathlib4/blob/v4.35.0/Mathlib/Data/Set/Countable.lean
   - https://github.com/leanprover-community/mathlib4/blob/v4.35.0/Mathlib/SetTheory/Cardinal/Aleph.lean
   - https://github.com/leanprover-community/mathlib4/blob/v4.35.0/Mathlib/SetTheory/Cardinal/Regular.lean


9. The exact protocol timing and public-history distinction were rechecked against Definition 1, Table 1, and Appendix G of arXiv:2601.21462v3. The current public history includes previous realized predictions; in the deterministic construction these are recorded alongside each context and visible label.
   - https://arxiv.org/html/2601.21462v3

10. GitHub Actions run 41157208222 completed successfully for both Lean 4.35 and Rocq 9.2 on commit 1168ded2065bc238a1f6978b5b48addfece2dee3.
   - https://github.com/2503140kcsk-eng/ai-open-problem-lean-rocq-2026/actions/runs/41157208222


11. Exact locations of the two different open questions were rechecked in the complete v3 paper text: the target public-setting randomization-versus-determinism question ends Section 3.3; the finite-Helly / nested-inclusion necessity question ends Section 3.2.
   - https://arxiv.org/html/2601.21462v3


12. GitHub Actions validation for the omega-one full-path containment addition:
   - Lean source commit 4ebc89d95a6deb59bf658c2e2c26bac897701f2a: push run https://github.com/2503140kcsk-eng/ai-open-problem-lean-rocq-2026/actions/runs/41160197913; PR run https://github.com/2503140kcsk-eng/ai-open-problem-lean-rocq-2026/actions/runs/41160201246.
   - Rocq source commit b5940c796e71800125625cbe61f5502f98902da9: push run https://github.com/2503140kcsk-eng/ai-open-problem-lean-rocq-2026/actions/runs/41159597912; PR run https://github.com/2503140kcsk-eng/ai-open-problem-lean-rocq-2026/actions/runs/41159600483.
   - Final PR documentation head f0b7fdc755ff827aefe4f4d96e1111201bf5c68e: push run https://github.com/2503140kcsk-eng/ai-open-problem-lean-rocq-2026/actions/runs/41160340096; PR run https://github.com/2503140kcsk-eng/ai-open-problem-lean-rocq-2026/actions/runs/41160343911.


13. Mathlib 4.35 product-measure API used for the completed path miss probability theorem:
   - `Measure.pi_eval_preimage_null` in https://github.com/leanprover-community/mathlib4/blob/v4.35.0/Mathlib/MeasureTheory/Constructions/Pi.lean
   - `measure_iUnion_null_iff` in Mathlib's measure/outer-measure API; the finite index `Fin T` is countable.

14. New public-history and full-product verification:
   - Lean commit 930be4f94d31b7c63ed1a4547a699d7ae5a9a902: push run https://github.com/2503140kcsk-eng/ai-open-problem-lean-rocq-2026/actions/runs/41162686492; PR run https://github.com/2503140kcsk-eng/ai-open-problem-lean-rocq-2026/actions/runs/41162690428.
   - Lean commit e9e731725fa84cf9e78306013d49e7ebce072538: push run https://github.com/2503140kcsk-eng/ai-open-problem-lean-rocq-2026/actions/runs/41162960823; PR run https://github.com/2503140kcsk-eng/ai-open-problem-lean-rocq-2026/actions/runs/41162965658.
   - Across both CI tracks and both commits, all 8 Lean/Rocq jobs passed with zero error, warning, hint, deprecation, or unfinished-proof diagnostics.
