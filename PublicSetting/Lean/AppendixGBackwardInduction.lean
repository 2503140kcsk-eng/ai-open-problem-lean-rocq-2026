module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Appendix G: finite-horizon public/oblivious backward induction

This file formalizes the finite-horizon recursion used in Appendix G of
"Partial Feedback Online Learning" (arXiv:2601.21462v3).

The admissible-set family is filtered by a prefix-realizability predicate:
at public/oblivious state h and next context x, only sets S for which
Realizable h x S holds are quantified over.  A randomized action is an
arbitrary probability measure on the label measurable space.

The public continuation stores all sampled labels in a list.  The hidden
continuation stores only the public pair-history abstraction h.  The key
induction proves that the public value is independent of the sampled-label
list because the next hidden state depends on h, x, S but not on the current
sampled label.  This is exactly the structural condition in Eq. (26).

This theorem is distinct from the omega-one counterexample for fully
history-adaptive *hidden witnesses*: here the acceptable set selected at
the current stage is constrained by the current pair-history h, not by the
sampled label from the current stage.
-/

open MeasureTheory
open scoped ENNReal

namespace PublicSetting.AppendixG

/-- A randomized learner action: a genuine probability measure on labels. -/
structure RandomizedAction (Y : Type*) [MeasurableSpace Y] where
  law : Measure Y
  isProbability : IsProbabilityMeasure law

/-- Admissible acceptable sets together with the condition that adding the
set to the pair-history preserves global realizability by a comparator.
The realizability predicate is deliberately an explicit parameter. -/
noncomputable def feasibleSets
    {H X Y : Type*}
    (admissible : Set (Set Y))
    (realizable : H → X → Set Y → Prop)
    (h : H) (x : X) : Set (Set Y) :=
  {s | s ∈ admissible ∧ realizable h x s}

/-- A public pair-history in the set-valued feedback game:
the finite list of revealed context/acceptable-set pairs. -/
abbrev PairHistory (X Y : Type*) := List (X × Set Y)

/-- Append the next context and acceptable set to a public pair-history. -/
def pairHistoryExtend {X Y : Type*}
    (h : PairHistory X Y) (x : X) (s : Set Y) : PairHistory X Y :=
  h ++ [(x, s)]

/-- One hypothesis realizes an entire pair-history if it selects a label in
each acceptable set at the corresponding context. -/
def pairHistoryGloballyRealizable {X Y : Type*}
    (hypotheses : Set (X → Y)) (h : PairHistory X Y) : Prop :=
  ∃ f, f ∈ hypotheses ∧ ∀ entry ∈ h, f entry.1 ∈ entry.2

/-- An extension is feasible exactly when the same single hypothesis realizes
the previous pair-history and the new context/acceptable-set pair. -/
def pairHistoryPrefixRealizable {X Y : Type*}
    (hypotheses : Set (X → Y))
    (h : PairHistory X Y) (x : X) (s : Set Y) : Prop :=
  pairHistoryGloballyRealizable hypotheses (pairHistoryExtend h x s)

/-- A pair-history extension is globally realizable exactly when one
hypothesis realizes the old prefix and the new acceptable-set constraint. -/
theorem pairHistoryGloballyRealizable_extend_iff
    {X Y : Type*} (hypotheses : Set (X → Y))
    (h : PairHistory X Y) (x : X) (s : Set Y) :
    pairHistoryGloballyRealizable hypotheses (pairHistoryExtend h x s) ↔
      ∃ f, f ∈ hypotheses ∧
        (∀ entry ∈ h, f entry.1 ∈ entry.2) ∧ f x ∈ s := by
  simp [pairHistoryGloballyRealizable, pairHistoryExtend, List.mem_append]

/-- The oblivious continuation value V_t(h), with t rounds remaining.
It is the exact sup_x inf_pi sup_{S admissible and prefix-realizable}
Bellman recursion from Appendix G. -/
noncomputable def obliviousValue
    {H X Y : Type*} [MeasurableSpace Y]
    (admissible : Set (Set Y))
    (realizable : H → X → Set Y → Prop)
    (next : H → X → Set Y → H) :
    ℕ → H → ℝ≥0∞
  | 0, _ => 0
  | n + 1, h =>
      ⨆ x, ⨅ p : RandomizedAction Y,
        ⨆ s : {s : Set Y // s ∈ feasibleSets admissible realizable h x},
          p.law s.1ᶜ +
            obliviousValue admissible realizable next n (next h x s.1)

/-- Public continuation value W_t(h, ys), where ys is the complete list of
sampled labels observed so far.  The current loss is integrated under the
selected randomized action; after the draw, ys is extended by the realized
sample. -/
noncomputable def publicValue
    {H X Y : Type*} [MeasurableSpace Y]
    (admissible : Set (Set Y))
    (admissible_measurable : ∀ s ∈ admissible, MeasurableSet s)
    (realizable : H → X → Set Y → Prop)
    (next : H → X → Set Y → H) :
    ℕ → H → List Y → ℝ≥0∞
  | 0, _, _ => 0
  | n + 1, h, ys =>
      ⨆ x, ⨅ p : RandomizedAction Y,
        ⨆ s : {s : Set Y // s ∈ feasibleSets admissible realizable h x},
          letI : IsProbabilityMeasure p.law := p.isProbability
          ∫⁻ y, s.1ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y +
            publicValue admissible admissible_measurable realizable next
              n (next h x s.1) (ys ++ [y]) ∂p.law

/-- Appendix G's backward-induction identity: all dependence on previously
sampled labels disappears from the continuation value, provided admissible
sets and their realizability are selected from the pair-history only. -/
theorem publicValue_eq_obliviousValue
    {H X Y : Type*} [MeasurableSpace Y]
    (admissible : Set (Set Y))
    (admissible_measurable : ∀ s ∈ admissible, MeasurableSet s)
    (realizable : H → X → Set Y → Prop)
    (next : H → X → Set Y → H) :
    ∀ n h ys,
      publicValue admissible admissible_measurable realizable next n h ys =
        obliviousValue admissible realizable next n h := by
  intro n
  induction n with
  | zero =>
      intro h ys
      rfl
  | succ n ih =>
      intro h ys
      simp only [publicValue, obliviousValue]
      apply iSup_congr
      intro x
      apply iInf_congr
      intro p
      apply iSup_congr
      intro s
      haveI : IsProbabilityMeasure p.law := p.isProbability
      have hs : MeasurableSet s.1 := admissible_measurable s.1 s.2.1
      have hfun :
          (fun y : Y =>
            s.1ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y +
              publicValue admissible admissible_measurable realizable next
                n (next h x s.1) (ys ++ [y])) =
          (fun y : Y =>
            s.1ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y +
              obliviousValue admissible realizable next n (next h x s.1)) := by
        funext y
        rw [ih (next h x s.1) (ys ++ [y])]
      rw [hfun]
      rw [lintegral_add_left'
        ((measurable_const.indicator hs.compl).aemeasurable)]
      rw [lintegral_indicator_const hs.compl (1 : ℝ≥0∞)]
      rw [lintegral_const]
      simp

/-- Theorem 18 / Appendix G specialized to the paper's actual pair-history
and set-realizability predicate. Every feasible extension must be witnessed
by one global hypothesis f in the original class, simultaneously realizing
all earlier pairs and the current pair. -/
theorem appendixG_pairHistory_value_identity
    {X Y : Type*} [MeasurableSpace Y]
    (admissible : Set (Set Y))
    (admissible_measurable : ∀ s ∈ admissible, MeasurableSet s)
    (hypotheses : Set (X → Y)) :
    ∀ n (h : PairHistory X Y) (ys : List Y),
      publicValue admissible admissible_measurable
        (pairHistoryPrefixRealizable hypotheses) pairHistoryExtend n h ys =
      obliviousValue admissible
        (pairHistoryPrefixRealizable hypotheses) pairHistoryExtend n h := by
  exact publicValue_eq_obliviousValue
    admissible admissible_measurable
    (pairHistoryPrefixRealizable hypotheses) pairHistoryExtend

/-- The public value of the original game from the empty history, i.e.
the nested supremum/infimum/expectation expression in Equation (24). -/
noncomputable def publicInitialValue
    {X Y : Type*} [MeasurableSpace Y]
    (admissible : Set (Set Y))
    (admissible_measurable : ∀ s ∈ admissible, MeasurableSet s)
    (hypotheses : Set (X → Y)) (T : ℕ) : ℝ≥0∞ :=
  publicValue admissible admissible_measurable
    (pairHistoryPrefixRealizable hypotheses) pairHistoryExtend T [] []

/-- The oblivious value of the same game, i.e. the nested minimax expression
with a single expectation over the roundwise randomized predictions in
Equation (25). -/
noncomputable def obliviousInitialValue
    {X Y : Type*} [MeasurableSpace Y]
    (admissible : Set (Set Y))
    (hypotheses : Set (X → Y)) (T : ℕ) : ℝ≥0∞ :=
  obliviousValue admissible
    (pairHistoryPrefixRealizable hypotheses) pairHistoryExtend T []

/-- Appendix G's initial minimax equality: public and oblivious set-valued
feedback games have exactly the same finite-horizon value. -/
theorem appendixG_public_eq_oblivious_minimax
    {X Y : Type*} [MeasurableSpace Y]
    (admissible : Set (Set Y))
    (admissible_measurable : ∀ s ∈ admissible, MeasurableSet s)
    (hypotheses : Set (X → Y)) (T : ℕ) :
    publicInitialValue admissible admissible_measurable hypotheses T =
      obliviousInitialValue admissible hypotheses T := by
  exact appendixG_pairHistory_value_identity
    admissible admissible_measurable hypotheses T [] []

/-- The full public continuation value includes the losses already incurred.
This is the left-hand side W_t(tau_t) of Eq. (26), with pastLoss standing
for the sum of observed indicator losses on the realized public history. -/
def publicTotalValue
    (pastLoss continuation : ℝ≥0∞) : ℝ≥0∞ :=
  pastLoss + continuation

/-- Equation (26): public minimax value equals accumulated past loss plus
the oblivious continuation value, for every possible sampled-label history. -/
theorem appendixG_equation_26
    {H X Y : Type*} [MeasurableSpace Y]
    (admissible : Set (Set Y))
    (admissible_measurable : ∀ s ∈ admissible, MeasurableSet s)
    (realizable : H → X → Set Y → Prop)
    (next : H → X → Set Y → H)
    (n : ℕ) (h : H) (ys : List Y) (pastLoss : ℝ≥0∞) :
    publicTotalValue pastLoss
      (publicValue admissible admissible_measurable realizable next n h ys) =
    pastLoss + obliviousValue admissible realizable next n h := by
  unfold publicTotalValue
  rw [publicValue_eq_obliviousValue
    admissible admissible_measurable realizable next n h ys]

end PublicSetting.AppendixG
