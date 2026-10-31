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
