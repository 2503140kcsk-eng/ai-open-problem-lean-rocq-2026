-- Machine-checked threshold shattering lemmas using Lean 4 core only.
-- The information-complexity / eCMI theorem remains an open research target and
-- is deliberately not represented as a proved theorem in this file.

namespace VCLearning

/-- A concept is a Boolean-valued classifier. -/
abbrev Concept (X : Type) := X → Bool

/-- Initial-segment threshold: x is positive precisely when x < t. -/
def thresholdConcept (t : Nat) : Concept Nat := fun x => decide (x < t)

/-- The class of all natural-number thresholds. -/
def ThresholdClass (h : Concept Nat) : Prop :=
  ∃ t : Nat, h = thresholdConcept t

/-- Every labeling of a single point is realized by some threshold. -/
def ShattersSingleton (H : Concept Nat → Prop) (a : Nat) : Prop :=
  ∀ label : Bool, ∃ h, H h ∧ h a = label

/-- A pair is shattered when all four two-bit labelings are realizable. -/
def ShattersPair (H : Concept Nat → Prop) (a b : Nat) : Prop :=
  ∀ first second : Bool, ∃ h, H h ∧ h a = first ∧ h b = second

/-- Thresholds shatter every singleton: t=a yields false, t=a+1 yields true. -/
theorem thresholds_shatter_singleton (a : Nat) :
    ShattersSingleton ThresholdClass a := by
  intro label
  cases label with
  | false =>
      refine ⟨thresholdConcept a, ⟨a, rfl⟩, ?_⟩
      simp [thresholdConcept]
  | true =>
      refine ⟨thresholdConcept (a + 1), ⟨a + 1, rfl⟩, ?_⟩
      simp [thresholdConcept]

/-- If a < b, the non-monotone labeling (false,true) cannot be realized.
Thus no two-point set is shattered by the threshold class. -/
theorem thresholds_not_shatter_pair {a b : Nat} (hab : a < b) :
    ¬ ShattersPair ThresholdClass a b := by
  intro hpair
  obtain ⟨h, hh, ha, hb⟩ := hpair false true
  obtain ⟨t, rfl⟩ := hh
  change decide (a < t) = false at ha
  change decide (b < t) = true at hb
  have ha' : ¬ a < t := of_decide_eq_false ha
  have hb' : b < t := of_decide_eq_true hb
  exact ha' (Nat.lt_trans hab hb')

/-- A precise pair/singleton characterization witnessed by the thresholds. -/
theorem threshold_class_dimension_one_pairwise :
    (∀ a, ShattersSingleton ThresholdClass a) ∧
    (∀ a b, a < b → ¬ ShattersPair ThresholdClass a b) :=
  ⟨thresholds_shatter_singleton, fun _ _ h => thresholds_not_shatter_pair h⟩

/-- Specification placeholder for the separate information-complexity research
question. This is a predicate, not a theorem asserting existence of a learner. -/
def LowECMIResearchTarget (Learner : Type) (hasLinearECMI : Learner → Prop) : Prop :=
  ∃ learner : Learner, hasLinearECMI learner

end VCLearning
