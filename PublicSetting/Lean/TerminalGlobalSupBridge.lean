import GlobalSupSequentialRisk

/-!
# Terminal global supremum -> sequential upper-risk bridge

This file keeps three notions separate:

* one terminal function beta : X -> Label, fixed across the whole trace;
* the predictable stagewise miss envelope;
* ordinary path-space expectation, which is available only after joint
  measurability (and, for a finite real expectation, integrability).

The pathwise theorem below is specific to the upper-tail family already
defined in GlobalSupSequentialRisk.lean. It is not a theorem for every
set-realizable class in the source paper.
-/

open MeasureTheory
open scoped ENNReal

namespace PublicSetting.TerminalGlobalSupBridge

open PublicSetting.OmegaOne
open PublicSetting.GlobalSupSequentialRisk

/-- The actual terminal loss supremum over one globally consistent
context-indexed threshold function, viewed as a function of the complete
prediction path. Repeated contexts share one threshold. -/
noncomputable def terminalGlobalSupPathLoss
    {X : Type*} {T : ℕ}
    (context : Fin T → X) (witness : Fin T → Label) :
    (Fin T → Label) → ℝ≥0∞ :=
  fun prediction =>
    globalContextTerminalSupLoss context witness prediction

/-- The stagewise predictable envelope on a complete prediction path. -/
noncomputable def stagewisePredictablePathRisk
    {T : ℕ} (witness : Fin T → Label) :
    (Fin T → Label) → ℝ≥0∞ :=
  fun prediction => predictableMissCount witness prediction

/-- For every completed transcript, every single global hypothesis family
has loss bounded by the predictable miss count. This uses the same beta at
all rounds; no supremum/sum interchange is used. -/
theorem terminalGlobalSupPathLoss_le_stagewisePredictablePathRisk
    {X : Type*} {T : ℕ}
    (context : Fin T → X) (witness prediction : Fin T → Label) :
    terminalGlobalSupPathLoss context witness prediction ≤
      stagewisePredictablePathRisk witness prediction := by
  exact globalContextTerminalSupLoss_le_predictableMissCount
    context witness prediction

/-- Monotonicity lifts the pointwise, single-global-family comparison to
upper integrals under any path measure. No joint measurability of the
terminal global supremum is needed for this inequality. -/
theorem terminalGlobalSup_upperIntegral_le_stagewise_upperIntegral
    {X : Type*} {T : ℕ}
    (pathMeasure : Measure (Fin T → Label))
    (context : Fin T → X) (witness : Fin T → Label) :
    upperLIntegral pathMeasure (terminalGlobalSupPathLoss context witness) ≤
      upperLIntegral pathMeasure (stagewisePredictablePathRisk witness) := by
  exact upperLIntegral_mono pathMeasure
    (terminalGlobalSupPathLoss_le_stagewisePredictablePathRisk
      context witness)

/-- Once the stagewise envelope is jointly measurable on path space, its
upper integral is its ordinary nonnegative Lebesgue integral. Combining this
with the pointwise global-supremum bound gives an expected-risk bound. -/
theorem terminalGlobalSup_upperIntegral_le_stagewise_lintegral
    {X : Type*} {T : ℕ}
    (pathMeasure : Measure (Fin T → Label))
    (context : Fin T → X) (witness : Fin T → Label)
    (hstage : Measurable (stagewisePredictablePathRisk witness)) :
    upperLIntegral pathMeasure (terminalGlobalSupPathLoss context witness) ≤
      ∫⁻ prediction, stagewisePredictablePathRisk witness prediction
        ∂pathMeasure := by
  calc
    upperLIntegral pathMeasure (terminalGlobalSupPathLoss context witness)
        ≤ upperLIntegral pathMeasure
            (stagewisePredictablePathRisk witness) :=
          terminalGlobalSup_upperIntegral_le_stagewise_upperIntegral
            pathMeasure context witness
    _ = ∫⁻ prediction, stagewisePredictablePathRisk witness prediction
          ∂pathMeasure :=
        upperLIntegral_eq_lintegral_of_measurable pathMeasure
          (stagewisePredictablePathRisk witness) hstage

/-- Joint measurability of the *terminal* global-supremum payoff is the
precise premise under which its upper integral is the ordinary extended
expectation. Integrability is not needed for equality in [0,∞]; it is
needed separately when one requires a finite real-valued expectation. -/
theorem terminalGlobalSup_upperIntegral_eq_lintegral_of_jointly_measurable
    {X : Type*} {T : ℕ}
    (pathMeasure : Measure (Fin T → Label))
    (context : Fin T → X) (witness : Fin T → Label)
    (hterminal : Measurable (terminalGlobalSupPathLoss context witness)) :
    upperLIntegral pathMeasure (terminalGlobalSupPathLoss context witness) =
      ∫⁻ prediction, terminalGlobalSupPathLoss context witness prediction
        ∂pathMeasure :=
  upperLIntegral_eq_lintegral_of_measurable pathMeasure
    (terminalGlobalSupPathLoss context witness) hterminal

/-- If a separately established path-law/dynamic-programming argument bounds
the ordinary stagewise path risk by a sequential Bellman budget, the same
budget bounds the upper integral of the one-global-family terminal loss.
This theorem exposes rather than hides the required path-law-to-Bellman
premise; the operator-level Bellman domination is proved in
GlobalSupSequentialRisk.lean. -/
theorem terminalGlobalSup_upperIntegral_le_sequentialBellmanBudget
    {X : Type*} {T : ℕ}
    (pathMeasure : Measure (Fin T → Label))
    (context : Fin T → X) (witness : Fin T → Label)
    (hstage : Measurable (stagewisePredictablePathRisk witness))
    (bellmanBudget : ℝ≥0∞)
    (hbudget :
      (∫⁻ prediction, stagewisePredictablePathRisk witness prediction
        ∂pathMeasure) ≤ bellmanBudget) :
    upperLIntegral pathMeasure (terminalGlobalSupPathLoss context witness) ≤
      bellmanBudget := by
  exact (terminalGlobalSup_upperIntegral_le_stagewise_lintegral
    pathMeasure context witness hstage).trans hbudget

/-- The sequential upper-risk Bellman value is bounded by the
stagewise conditional-risk Bellman value at every finite horizon and public
history. This is the already-established backward-induction theorem from
GlobalSupSequentialRisk.lean, exposed here next to the terminal path bound.
It is a statement about the recursively defined game values, not an
unconditional identification of an arbitrary path measure with that game. -/
theorem sequentialOuterBellmanValue_le_stagewise
    {H X P : Type*}
    (draw : P → Measure Label)
    (next : H → X → P → Label → Label → H) :
    ∀ n h,
      publicGlobalSupOuterGameValue draw next n h ≤
        publicGlobalSupGameValue draw next n h :=
  publicGlobalSupOuterGameValue_le_stagewiseGameValue draw next

#print axioms terminalGlobalSupPathLoss_le_stagewisePredictablePathRisk
#print axioms terminalGlobalSup_upperIntegral_le_stagewise_upperIntegral
#print axioms terminalGlobalSup_upperIntegral_le_stagewise_lintegral
#print axioms terminalGlobalSup_upperIntegral_eq_lintegral_of_jointly_measurable
#print axioms terminalGlobalSup_upperIntegral_le_sequentialBellmanBudget
#print axioms sequentialOuterBellmanValue_le_stagewise

end PublicSetting.TerminalGlobalSupBridge
