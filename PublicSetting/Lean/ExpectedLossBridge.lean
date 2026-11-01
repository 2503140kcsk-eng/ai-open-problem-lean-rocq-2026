module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
Finite-horizon bridge from conditional stage risks to ordinary expected loss.

The conclusion is conditional on integrability and the sigma-finiteness
premises required by Mathlib. It does not make a nonmeasurable pathwise
indicator measurable, and it does not commute a supremum over one global
terminal hypothesis family with a sum over rounds.
-/

open MeasureTheory

namespace PublicSetting.ExpectedLossBridge

theorem integral_finset_condExp_eq_integral_finset
    {Ω ι : Type*} {m₀ : MeasurableSpace Ω}
    (μ : Measure[m₀] Ω)
    (rounds : Finset ι)
    (filtration : ι → MeasurableSpace Ω)
    (hfiltration : ∀ i, filtration i ≤ m₀)
    (hσ : ∀ i, SigmaFinite (μ.trim (hfiltration i)))
    (loss : ι → Ω → ℝ)
    (hloss : ∀ i, i ∈ rounds → Integrable (loss i) μ) :
    ∫ ω, ∑ i ∈ rounds, (μ[loss i | filtration i]) ω ∂μ =
      ∫ ω, ∑ i ∈ rounds, loss i ω ∂μ := by
  calc
    ∫ ω, ∑ i ∈ rounds, (μ[loss i | filtration i]) ω ∂μ
        = ∑ i ∈ rounds, ∫ ω, (μ[loss i | filtration i]) ω ∂μ := by
          apply integral_finsetSum
          intro i hi
          haveI : SigmaFinite (μ.trim (hfiltration i)) := hσ i
          exact integrable_condExp
    _ = ∑ i ∈ rounds, ∫ ω, loss i ω ∂μ := by
          apply Finset.sum_congr rfl
          intro i hi
          haveI : SigmaFinite (μ.trim (hfiltration i)) := hσ i
          exact integral_condExp (hfiltration i)
    _ = ∫ ω, ∑ i ∈ rounds, loss i ω ∂μ := by
          symm
          apply integral_finsetSum
          exact hloss

#print axioms PublicSetting.ExpectedLossBridge.integral_finset_condExp_eq_integral_finset

end PublicSetting.ExpectedLossBridge
