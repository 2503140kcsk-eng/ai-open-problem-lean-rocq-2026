module

import Mathlib.MeasureTheory.Measure.Prod

/-!
A model-independent measurable-relation core for the standard-Borel obstruction.

For a product-measurable transitive relation R on a probability space, if
every incoming section has mass at least c > 1/2, then some point x₀ has
R(x₀,y) for every y. The proof is a two-sided Fubini argument followed by
the fact that two sets of probability greater than one half must intersect.

In the standard-Borel application, the complement of the core relation is
the projection of a Borel set, hence analytic; the relation is coanalytic
and universally measurable. Passing to the completion of the product
probability measure supplies the measurability hypothesis used here.
-/

open MeasureTheory
open scoped ENNReal

namespace PublicSetting.StandardBorelCore

variable {α : Type*} [MeasurableSpace α]

/-- Mass of the outgoing section {y | (x,y) ∈ R}. -/
noncomputable def outgoingMass (μ : Measure α) (R : Set (α × α)) (x : α) : ℝ≥0∞ :=
  μ (Prod.mk x ⁻¹' R)

/-- Mass of the incoming section {x | (x,y) ∈ R}. -/
noncomputable def incomingMass (μ : Measure α) (R : Set (α × α)) (y : α) : ℝ≥0∞ :=
  μ ((fun x : α => (x, y)) ⁻¹' R)

/-- Section measures of a product-measurable relation are measurable
for an s-finite measure. -/
theorem measurable_outgoingMass
    (μ : Measure α) [SFinite μ] (R : Set (α × α))
    (hR : MeasurableSet R) :
    Measurable (outgoingMass μ R) := by
  exact measurable_measure_prodMk_left hR

/-- The incoming-section mass function is measurable. -/
theorem measurable_incomingMass
    (μ : Measure α) [SFinite μ] (R : Set (α × α))
    (hR : MeasurableSet R) :
    Measurable (incomingMass μ R) := by
  exact measurable_measure_prodMk_right hR

/-- If every incoming section has uniform mass at least c₁ > 1/2,
then some outgoing section has mass strictly greater than 1/2.

This is the Fubini step for a relation measurable in the product
sigma-algebra. -/
theorem exists_outgoingMass_gt_half
    (μ : Measure α) [IsProbabilityMeasure μ] [SFinite μ]
    (R : Set (α × α)) (hR : MeasurableSet R)
    {c₁ : ℝ≥0∞} (hc₁ : (1 / 2 : ℝ≥0∞) < c₁)
    (hcol : ∀ y, c₁ ≤ incomingMass μ R y) :
    ∃ x, (1 / 2 : ℝ≥0∞) < outgoingMass μ R x := by
  by_contra hnone
  push Not at hnone
  have hupper : (μ.prod μ) R ≤ (1 / 2 : ℝ≥0∞) := by
    rw [Measure.prod_apply hR]
    calc
      (∫⁻ x, μ (Prod.mk x ⁻¹' R) ∂μ)
          ≤ ∫⁻ x, (1 / 2 : ℝ≥0∞) ∂μ :=
            lintegral_mono hnone
      _ = (1 / 2 : ℝ≥0∞) := by simp [measure_univ]
  have hlower : c₁ ≤ (μ.prod μ) R := by
    rw [Measure.prod_apply_symm hR]
    calc
      c₁ = ∫⁻ y, c₁ ∂μ := by simp [measure_univ]
      _ ≤ ∫⁻ y, μ ((fun x : α => (x, y)) ⁻¹' R) ∂μ := by
        exact lintegral_mono hcol
  exact (not_lt_of_ge hupper) (lt_of_lt_of_le hc₁ hlower)

/-- Two measurable sets in a probability space, each of measure greater
than one half, have nonempty intersection. -/
theorem nonempty_inter_of_measure_gt_half
    (μ : Measure α) [IsProbabilityMeasure μ]
    (A B : Set α) (hA : (1 / 2 : ℝ≥0∞) < μ A)
    (hB : (1 / 2 : ℝ≥0∞) < μ B)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    (A ∩ B).Nonempty := by
  have hsum : (1 : ℝ≥0∞) < μ A + μ B := by
    calc
      (1 : ℝ≥0∞) = (1 / 2 : ℝ≥0∞) + (1 / 2 : ℝ≥0∞) :=
        (ENNReal.add_halves (1 : ℝ≥0∞)).symm
      _ < μ A + μ B := ENNReal.add_lt_add hA hB
  have hUnion : μ (A ∪ B) ≤ 1 := by
    calc
      μ (A ∪ B) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hInterPos : 0 < μ (A ∩ B) := by
    by_contra hnot
    have hzero : μ (A ∩ B) = 0 :=
      le_antisymm (le_of_not_gt hnot) bot_le
    have hEq : μ (A ∪ B) = μ A + μ B := by
      calc
        μ (A ∪ B) = μ (A ∪ B) + μ (A ∩ B) := by rw [hzero, add_zero]
        _ = μ A + μ B := measure_union_add_inter A hBm
    have hbad : (1 : ℝ≥0∞) < μ (A ∪ B) := by
      rw [hEq]
      exact hsum
    exact (not_lt_of_ge hUnion) hbad
  by_contra hne
  have hempty : A ∩ B = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
  have hfalse := hInterPos
  simpa [hempty] using hfalse

/-- Uniform-section core theorem: for a product-measurable transitive
relation, if every incoming section has mass at least c₁ > 1/2, then
one point is related to every point. -/
theorem exists_universal_core_point
    (μ : Measure α) [IsProbabilityMeasure μ] [SFinite μ]
    (R : Set (α × α)) (hR : MeasurableSet R)
    (htrans : ∀ x z y, (x, z) ∈ R → (z, y) ∈ R → (x, y) ∈ R)
    {c₁ : ℝ≥0∞} (hc₁ : (1 / 2 : ℝ≥0∞) < c₁)
    (hcol : ∀ y, c₁ ≤ incomingMass μ R y) :
    ∃ x₀, ∀ y, (x₀, y) ∈ R := by
  obtain ⟨x₀, hx₀⟩ :=
    exists_outgoingMass_gt_half μ R hR hc₁ hcol
  refine ⟨x₀, ?_⟩
  intro y
  let A : Set α := Prod.mk x₀ ⁻¹' R
  let B : Set α := (fun x : α => (x, y)) ⁻¹' R
  have hAm : MeasurableSet A := hR.preimage measurable_prodMk_left
  have hBm : MeasurableSet B := hR.preimage measurable_prodMk_right
  have hA : (1 / 2 : ℝ≥0∞) < μ A := by
    simpa [A, outgoingMass] using hx₀
  have hB : (1 / 2 : ℝ≥0∞) < μ B := by
    simpa [B, incomingMass] using lt_of_lt_of_le hc₁ (hcol y)
  obtain ⟨z, hzA, hzB⟩ :=
    nonempty_inter_of_measure_gt_half μ A B hA hB hAm hBm
  exact htrans x₀ z y hzA hzB

end PublicSetting.StandardBorelCore
