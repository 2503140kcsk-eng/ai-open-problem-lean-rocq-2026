# Sources checked on 2026-10-28

1. Shao, Shihao; Fang, Cong; Lin, Zhouchen; Tao, Dacheng. “Partial Feedback Online Learning.” arXiv:2601.21462v3, dated 2026-04-02. Primary source for the open randomized-versus-deterministic public-setting question (end of Section 5.2) and, separately, the oblivious-versus-public comparison in Section 5.3. Theorem 18 proves equality for set-valued feedback; Theorem 19 proves the oblivious-versus-public separation for partial feedback.
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
