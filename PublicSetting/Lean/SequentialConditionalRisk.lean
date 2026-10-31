import OmegaOneSeparation

open Set MeasureTheory
open scoped ENNReal
open PublicSetting.OmegaOne

-- Make the nonstandard subtype instances explicit in this extension module.
local instance : MeasurableSpace Label := countableCocountableMeasurableSpace
local instance : LE Label :=
  ⟨fun a b => (a : Ordinal) ≤ (b : Ordinal)⟩

namespace PublicSetting.SequentialConditionalRisk

/-- An error relation on labels, pulled back along an adaptive policy. -/
def adaptiveErrorGraph
    {H Y : Type*} [MeasurableSpace H] [MeasurableSpace Y]
    (R : Set (Y × Y)) (policy : H → Y) : Set (H × Y) :=
  {z | (policy z.1, z.2) ∈ R}

/-- Joint measurability follows from two separate requirements:
the policy is measurable and the base error relation is measurable in
the product sigma algebra. -/
theorem adaptiveErrorGraph_measurable
    {H Y : Type*} [MeasurableSpace H] [MeasurableSpace Y]
    (R : Set (Y × Y)) (hR : MeasurableSet R)
    (policy : H → Y) (hpolicy : Measurable policy) :
    MeasurableSet (adaptiveErrorGraph R policy) := by
  have hmap : Measurable (fun z : H × Y => (policy z.1, z.2)) := by
    exact (hpolicy.comp measurable_fst).prodMk measurable_snd
  exact hR.preimage hmap

/-- For self-policies on Y, universal measurability of every adaptive
error graph is equivalent to product measurability of the relation itself.
The reverse implication is the preceding theorem; the forward implication
uses the identity policy. -/
theorem all_measurable_self_policies_iff
    {Y : Type*} [MeasurableSpace Y] (R : Set (Y × Y)) :
    (∀ policy : Y → Y, Measurable policy →
      MeasurableSet (adaptiveErrorGraph R policy)) ↔
        MeasurableSet R := by
  constructor
  · intro hall
    have hid := hall id measurable_id
    simpa [adaptiveErrorGraph] using hid
  · intro hR policy hpolicy
    exact adaptiveErrorGraph_measurable R hR policy hpolicy

/-- The conditional risk of a one-step error section at a fixed public
history. The section is evaluated under the draw distribution at that history;
no sigma-algebra on the space of complete paths is used. -/
noncomputable def conditionalSectionRisk
    {H : Type*}
    (draw : H → Measure Label)
    (witness : H → Label)
    (threshold : H → Label → Label) : H → ℝ≥0∞ :=
  fun h => draw h (adaptiveMissSet (threshold h) (witness h))

/-- If every sample-dependent terminal threshold remains below the
pre-sampling witness, then the section error is contained in the countable
lower segment and its conditional risk is zero. -/
theorem conditionalSectionRisk_eq_zero
    {H : Type*}
    (draw : H → Measure Label)
    (witness : H → Label)
    (threshold : H → Label → Label)
    (hbound : ∀ h y, threshold h y ≤ witness h)
    (hnull : ∀ h, draw h (lowerSegment (witness h)) = 0) :
    ∀ h, conditionalSectionRisk draw witness threshold h = 0 := by
  intro h
  unfold conditionalSectionRisk
  apply MeasureTheory.Measure.mono_null
  · exact adaptiveMiss_subset_lowerSegment (threshold h) (witness h)
      (fun y => hbound h y)
  · exact hnull h

/-- The risk function is measurable whenever it is identically zero.
This does not require the joint error graph to be measurable. -/
theorem conditionalSectionRisk_measurable_of_zero
    {H : Type*} [MeasurableSpace H]
    (draw : H → Measure Label)
    (witness : H → Label)
    (threshold : H → Label → Label)
    (hzero : ∀ h, conditionalSectionRisk draw witness threshold h = 0) :
    Measurable (conditionalSectionRisk draw witness threshold) := by
  have heq :
      conditionalSectionRisk draw witness threshold =
        fun _ : H => (0 : ℝ≥0∞) := by
    funext h
    exact hzero h
  rw [heq]
  exact measurable_const

/-- A finite-horizon risk formed by adding the conditional risks at the
successive public histories. This definition intentionally does not construct
a full-path error event. -/
noncomputable def sequentialConditionalRisk
    (T : ℕ) (History : Fin T → Type*)
    (draw : ∀ t, History t → Measure Label)
    (witness : ∀ t, History t → Label)
    (threshold : ∀ t, History t → Label → Label)
    (histories : ∀ t, History t) : ℝ≥0∞ :=
  ∑ t : Fin T,
    conditionalSectionRisk (draw t) (witness t) (threshold t) (histories t)

/-- Sequential conditional-risk theorem for arbitrary history-indexed
witness and terminal-threshold policies. The only game-specific assumption
is the pre-sampling envelope condition at each history. -/
theorem sequentialConditionalRisk_eq_zero
    (T : ℕ) (History : Fin T → Type*)
    (draw : ∀ t, History t → Measure Label)
    (witness : ∀ t, History t → Label)
    (threshold : ∀ t, History t → Label → Label)
    (histories : ∀ t, History t)
    (hbound : ∀ t h y, threshold t h y ≤ witness t h)
    (hnull : ∀ t h, draw t h (lowerSegment (witness t h)) = 0) :
    sequentialConditionalRisk T History draw witness threshold histories = 0 := by
  classical
  unfold sequentialConditionalRisk
  apply Finset.sum_eq_zero
  intro t ht
  exact conditionalSectionRisk_eq_zero
    (draw t) (witness t) (threshold t)
    (fun h y => hbound t h y)
    (fun h => hnull t h)
    (histories t)

/-- Instantiation of the sequential conditional-risk theorem on the
countable-cocountable probability space over omega-one. The public witness
may be any function of the complete preceding history. -/
theorem omegaOne_sequentialConditionalRisk_eq_zero
    (T : ℕ) (History : Fin T → Type*)
    (witness : ∀ t, History t → Label)
    (threshold : ∀ t, History t → Label → Label)
    (histories : ∀ t, History t)
    (hbound : ∀ t h y, threshold t h y ≤ witness t h) :
    sequentialConditionalRisk T History
      (fun _ _ => countableCocountableMeasure)
      witness threshold histories = 0 := by
  apply sequentialConditionalRisk_eq_zero
  · exact hbound
  · intro t h
    exact lowerSegment_measure_zero (witness t h)

/-- The Appendix G Bellman step: context, learner distribution, and a
feasible set-valued feedback object are selected in the order sup-inf-sup.
stageRisk is the current expected loss and next is the next state. -/
noncomputable def appendixGBellmanStep
    {H X P S : Type*}
    (feasible : H → X → P → Set S)
    (stageRisk : H → X → P → S → ℝ≥0∞)
    (next : H → X → P → S → H)
    (V : H → ℝ≥0∞) (h : H) : ℝ≥0∞ :=
  ⨆ x, ⨅ p, ⨆ s : {s : S // s ∈ feasible h x p},
    stageRisk h x p s.1 + V (next h x p s.1)

/-- Public adaptive extension of the Appendix G Bellman step. The current
error cost is already a conditional section-risk, while the continuation
value is integrated against the current draw because the next public history
may depend on the realized sample. -/
noncomputable def adaptiveStagewiseBellmanStep
    {H X P S Y : Type*} [MeasurableSpace Y]
    (feasible : H → X → P → Set S)
    (draw : H → X → P → Measure Y)
    (stageRisk : H → X → P → S → ℝ≥0∞)
    (next : H → X → P → S → Y → H)
    (V : H → ℝ≥0∞) (h : H) : ℝ≥0∞ :=
  ⨆ x, ⨅ p, ⨆ s : {s : S // s ∈ feasible h x p},
    stageRisk h x p s.1 +
      ∫⁻ y, V (next h x p s.1 y) ∂draw h x p

/-- The adaptive Bellman step reduces exactly to the Appendix G step when
the next state does not depend on the sampled label and each draw law has
total mass one. This is the operator-level bridge behind the backward
induction in Appendix G. -/
theorem adaptiveStagewiseBellmanStep_eq_appendixG
    {H X P S Y : Type*} [MeasurableSpace Y]
    (feasible : H → X → P → Set S)
    (draw : H → X → P → Measure Y)
    (stageRisk : H → X → P → S → ℝ≥0∞)
    (next : H → X → P → S → Y → H)
    (nextG : H → X → P → S → H)
    (V : H → ℝ≥0∞) (h : H)
    (hmass : ∀ h x p, draw h x p Set.univ = 1)
    (hnext : ∀ h x p s y, next h x p s y = nextG h x p s) :
    adaptiveStagewiseBellmanStep feasible draw stageRisk next V h =
      appendixGBellmanStep feasible stageRisk nextG V h := by
  classical
  simp [adaptiveStagewiseBellmanStep, appendixGBellmanStep,
    hnext, lintegral_const, hmass]

/-- The exact set-valued specialization used in Appendix G:
the one-step error is the draw probability of the complement of the
acceptable set, and the continuation state records only the revealed
context/set pair. -/
noncomputable def appendixGSetValuedStep
    {H X P S Y : Type*} [MeasurableSpace Y]
    (feasible : H → X → P → Set S)
    (draw : H → X → P → Measure Y)
    (acceptable : H → X → S → Set Y)
    (next : H → X → P → S → H)
    (V : H → ℝ≥0∞) (h : H) : ℝ≥0∞ :=
  appendixGBellmanStep feasible
    (fun h x p s => draw h x p (acceptable h x s)ᶜ)
    next V h

/-- If the public extension suppresses the sampled label from its successor
state, its Bellman step is exactly the Appendix G set-valued operator. -/
theorem adaptiveStagewiseBellmanStep_eq_appendixGSetValued
    {H X P S Y : Type*} [MeasurableSpace Y]
    (feasible : H → X → P → Set S)
    (draw : H → X → P → Measure Y)
    (acceptable : H → X → S → Set Y)
    (next : H → X → P → S → H)
    (nextPublic : H → X → P → S → Y → H)
    (V : H → ℝ≥0∞) (h : H)
    (hmass : ∀ h x p, draw h x p Set.univ = 1)
    (hnext : ∀ h x p s y, nextPublic h x p s y = next h x p s) :
    adaptiveStagewiseBellmanStep feasible draw
      (fun h x p s => draw h x p (acceptable h x s)ᶜ)
      nextPublic V h =
      appendixGSetValuedStep feasible draw acceptable next V h := by
  simpa [appendixGSetValuedStep] using
    (adaptiveStagewiseBellmanStep_eq_appendixG
      feasible draw
      (fun h x p s => draw h x p (acceptable h x s)ᶜ)
      nextPublic next V h hmass hnext)


/-!
## Full-continuation-dependent terminal targets

The previous conditionalSectionRisk allows a terminal threshold to depend
on the current sampled label.  The following extension allows it to depend
on an arbitrary complete future continuation as well.

The key condition is pointwise: for a fixed public history, every possible
continuation target still contains that history's pre-sampling witness.
Consequently, the error section is contained in a measurable null cylinder
on the current-label coordinate.  The error section itself need not be
measurable.  Its measure is zero by monotonicity of outer measure.

This is an iterated/conditional-risk theorem.  It does not assert that the
union of all such sections over nonmeasurable history-dependent choices is
measurable in the full path sigma-algebra.
-/

/-- The terminal miss section when the final threshold may depend on both
the current label and an arbitrary future continuation. -/
def fullContinuationMissSection {Future : Type*}
    (chooseThreshold : Label → Future → Label) : Set (Label × Future) :=
  {z | ¬ chooseThreshold z.1 z.2 ≤ z.1}

/-- Every miss remains inside the null lower cylinder whenever every
continuation's selected upper tail contains the pre-draw witness. -/
theorem fullContinuationMissSection_subset_lowerCylinder
    {Future : Type*}
    (chooseThreshold : Label → Future → Label) (witness : Label)
    (hcontains : ∀ y future, chooseThreshold y future ≤ witness) :
    fullContinuationMissSection chooseThreshold ⊆
      {z : Label × Future | z.1 ∈ lowerSegment witness} := by
  rintro ⟨y, future⟩ hmiss
  change ¬ chooseThreshold y future ≤ y at hmiss
  change y ∈ lowerSegment witness
  change y < witness
  exact lt_of_lt_of_le (lt_of_not_ge hmiss) (hcontains y future)

/-- Conditional risk of a miss whose terminal threshold can inspect the
entire future continuation. -/
noncomputable def fullContinuationConditionalRisk
    {H Future : Type*} [MeasurableSpace Future]
    (jointLaw : H → Measure (Label × Future))
    (witness : H → Label)
    (threshold : H → Label → Future → Label) : H → ℝ≥0∞ :=
  fun h => jointLaw h (fullContinuationMissSection (threshold h))

/-- Full-continuation-dependent conditional risk is zero under the
pre-sampling envelope and a null lower-cylinder condition.  No joint
measurability of the terminal miss relation is required. -/
theorem fullContinuationConditionalRisk_eq_zero
    {H Future : Type*} [MeasurableSpace Future]
    (jointLaw : H → Measure (Label × Future))
    (witness : H → Label)
    (threshold : H → Label → Future → Label)
    (hcontains : ∀ h y future, threshold h y future ≤ witness h)
    (hnull : ∀ h,
      jointLaw h {z : Label × Future | z.1 ∈ lowerSegment (witness h)} = 0) :
    ∀ h, fullContinuationConditionalRisk jointLaw witness threshold h = 0 := by
  intro h
  unfold fullContinuationConditionalRisk
  apply MeasureTheory.Measure.mono_null
    (fullContinuationMissSection_subset_lowerCylinder
      (threshold h) (witness h) (fun y future => hcontains h y future))
  exact hnull h

/-- A finite-horizon collection of conditional risks, where the future
continuation type may vary with the round.  Each threshold can inspect the
complete suffix after that round, not merely the current draw. -/
noncomputable def fullFutureSequentialRisk
    (T : ℕ) (History : Fin T → Type*) (Future : Fin T → Type*)
    [∀ t, MeasurableSpace (Future t)]
    (jointLaw : ∀ t, History t → Measure (Label × Future t))
    (witness : ∀ t, History t → Label)
    (threshold : ∀ t, History t → Label → Future t → Label)
    (histories : ∀ t, History t) : ℝ≥0∞ :=
  ∑ t : Fin T,
    fullContinuationConditionalRisk (jointLaw t) (witness t) (threshold t)
      (histories t)

/-- All finite-round full-future conditional risks vanish for every
history sequence.  In particular, the bound is uniform over arbitrary
history-dependent public witness policies and terminal targets depending
on all later samples. -/
theorem fullFutureSequentialRisk_eq_zero
    (T : ℕ) (History : Fin T → Type*) (Future : Fin T → Type*)
    [∀ t, MeasurableSpace (Future t)]
    (jointLaw : ∀ t, History t → Measure (Label × Future t))
    (witness : ∀ t, History t → Label)
    (threshold : ∀ t, History t → Label → Future t → Label)
    (histories : ∀ t, History t)
    (hcontains : ∀ t h y future, threshold t h y future ≤ witness t h)
    (hnull : ∀ t h,
      jointLaw t h {z : Label × Future t | z.1 ∈ lowerSegment (witness t h)} = 0) :
    fullFutureSequentialRisk T History Future jointLaw witness threshold histories = 0 := by
  classical
  unfold fullFutureSequentialRisk
  apply Finset.sum_eq_zero
  intro t ht
  exact fullContinuationConditionalRisk_eq_zero
    (jointLaw t) (witness t) (threshold t)
    (fun h y future => hcontains t h y future)
    (fun h => hnull t h)
    (histories t)

/-- The sequential conditional-risk process is identically zero as a
function of the complete random history trace, so its integral is zero
under any probability law on those traces.  This is deliberately distinct
from integrating a potentially nonmeasurable pathwise error indicator. -/
theorem integratedFullFutureSequentialRisk_eq_zero
    (T : ℕ) (History : Fin T → Type*) (Future : Fin T → Type*)
    [∀ t, MeasurableSpace (Future t)]
    [MeasurableSpace (∀ t, History t)]
    (jointLaw : ∀ t, History t → Measure (Label × Future t))
    (witness : ∀ t, History t → Label)
    (threshold : ∀ t, History t → Label → Future t → Label)
    (traceLaw : Measure (∀ t, History t))
    (hcontains : ∀ t h y future, threshold t h y future ≤ witness t h)
    (hnull : ∀ t h,
      jointLaw t h {z : Label × Future t | z.1 ∈ lowerSegment (witness t h)} = 0) :
    ∫⁻ trace, fullFutureSequentialRisk T History Future jointLaw witness threshold
      (fun t => trace t) ∂traceLaw = 0 := by
  have hzero :
      (fun trace : ∀ t, History t =>
        fullFutureSequentialRisk T History Future jointLaw witness threshold
          (fun t => trace t)) = fun _ => (0 : ℝ≥0∞) := by
    funext trace
    exact fullFutureSequentialRisk_eq_zero
      T History Future jointLaw witness threshold
      (fun t => trace t) hcontains hnull
  rw [hzero]
  simp


end PublicSetting.SequentialConditionalRisk
