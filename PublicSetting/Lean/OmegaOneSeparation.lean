import Mathlib

/-!
# The omega-one countable/cocountable measure construction

This file formalizes the measurable-space and measure-theoretic core of a candidate
separation for Shao–Fang–Lin–Tao, Partial Feedback Online Learning
(arXiv:2601.21462v3), Section 5.2.

The label space is the set of all countable ordinals, represented by Iio (omega-one).
It carries the countable-cocountable sigma algebra and the probability measure
which assigns mass 0 to countable sets and mass 1 to cocountable sets.

The file also formalizes two crucial game-theoretic lemmas:
* every adaptive terminal upper-tail choice containing the pre-sampling witness
  can only miss on a null initial segment;
* for every deterministic prediction path, one single global target family
  induces the successive tails immediately above those predictions.

The randomized guarantee is under the paper's abstract convention that any
probability measure on the label measurable space is an admissible randomized
action. The countable-cocountable probability space is not asserted to be a
standard Borel probability space or to be implementable from a usual real-valued
PRNG. This modelling boundary is part of the theorem statement, not hidden.
-/

noncomputable section

open Set MeasureTheory
open scoped Cardinal

namespace PublicSetting.OmegaOne

/-- The label space: all ordinals strictly below the first uncountable ordinal. -/
abbrev Label := Set.Iio (Ordinal.omega 1)

theorem label_univ_not_countable : ¬ (Set.univ : Set Label).Countable := by
  intro h
  have hcnt : Countable Label := Set.countable_univ_iff.mp h
  have hcard : Cardinal.mk Label ≤ Cardinal.aleph0 :=
    Cardinal.mk_le_aleph0_iff.mpr hcnt
  have hmk : Cardinal.mk Label = Cardinal.lift (Cardinal.aleph 1) := by
    simpa [Label, Ordinal.card_omega] using
      (Cardinal.mk_Iio_ordinal (Ordinal.omega 1))
  rw [hmk, ← Cardinal.lift_aleph 0] at hcard
  have hle : Cardinal.aleph 1 ≤ Cardinal.aleph 0 :=
    (Cardinal.lift_le).mp hcard
  exact (not_le_of_gt Cardinal.aleph0_lt_aleph_one) hle

/-- Every strict initial segment below a label is countable. -/
def lowerSegment (w : Label) : Set Label := {x | x.1 < w.1}

theorem lowerSegment_countable (w : Label) : (lowerSegment w).Countable := by
  have h : (Set.Iio w.1 : Set Ordinal).Countable :=
    Cardinal.countable_Iio_of_lt_omega_one w.2
  exact h.preimage Subtype.val_injective

/-- Every countable family of upper tails has a common label. This is the
    cofinality-omega-one fact that prevents Theorem 16's nested-countable
    intersection condition from applying to this tail family. -/
theorem countableTails_intersect (thresholds : ℕ → Label) :
    ∃ w : Label, ∀ n, thresholds n ≤ w := by
  let b : Ordinal := ⨆ n, (thresholds n).1
  have hb : b < Ordinal.omega 1 := by
    apply Ordinal.iSup_lt_omega_one
    intro n
    exact (thresholds n).2
  refine ⟨⟨b, hb⟩, ?_⟩
  intro n
  change (thresholds n).1 ≤ b
  exact le_iSup (fun k => (thresholds k).1) n

/-- The countable-cocountable sigma algebra on the label space. -/
def countableCocountableMeasurableSpace : MeasurableSpace Label where
  MeasurableSet' s := s.Countable ∨ sᶜ.Countable
  measurableSet_empty := Or.inl Set.countable_empty
  measurableSet_compl := by
    intro s hs
    rcases hs with hs | hs
    · exact Or.inr (by simpa using hs)
    · exact Or.inl (by simpa using hs)
  measurableSet_iUnion := by
    classical
    intro f hf
    by_cases hsome : ∃ i, ¬ (f i).Countable
    · right
      obtain ⟨i, hi⟩ := hsome
      have hcomp : (f i)ᶜ.Countable := (hf i).resolve_left hi
      apply hcomp.mono
      intro x hx
      change x ∈ (⋃ n, f n)ᶜ at hx
      change x ∈ (f i)ᶜ
      exact fun hxi => hx (Set.mem_iUnion.mpr ⟨i, hxi⟩)
    · left
      apply Set.countable_iUnion
      intro i
      by_contra hi
      exact hsome ⟨i, hi⟩

instance : MeasurableSpace Label := countableCocountableMeasurableSpace

/-- The 0/1 mass on measurable sets: countable sets have mass zero. -/
noncomputable def countableCocountableMass
    (s : Set Label) (_hs : MeasurableSet s) : ℝ≥0∞ := by
  classical
  exact if s.Countable then 0 else 1

/-- Countable-cocountable probability measure on omega-one. -/
noncomputable def countableCocountableMeasure : Measure Label := by
  refine Measure.ofMeasurable countableCocountableMass ?_ ?_
  · simp [countableCocountableMass]
  · intro f hf hdisj
    classical
    by_cases hsome : ∃ i, ¬ (f i).Countable
    · obtain ⟨i, hi⟩ := hsome
      have hcomp : (f i)ᶜ.Countable := (hf i).resolve_left hi
      have hcompUnion : (⋃ n, f n)ᶜ.Countable := by
        apply hcomp.mono
        intro x hx
        change x ∈ (⋃ n, f n)ᶜ at hx
        change x ∈ (f i)ᶜ
        exact fun hxi => hx (Set.mem_iUnion.mpr ⟨i, hxi⟩)
      have hnotUnion : ¬ (⋃ n, f n).Countable := by
        intro hcnt
        have hwhole : (Set.univ : Set Label).Countable := by
          have hu : ((⋃ n, f n) ∪ (⋃ n, f n)ᶜ).Countable :=
            hcnt.union hcompUnion
          simpa using hu
        exact label_univ_not_countable hwhole
      have hothers : ∀ j, j ≠ i → (f j).Countable := by
        intro j hji
        have hdis : Disjoint (f i) (f j) := hdisj (Ne.symm hji)
        apply hcomp.mono
        intro x hxj
        change x ∈ (f i)ᶜ
        intro hxi
        exact (Set.disjoint_left.mp hdis) hxi hxj
      have hsum : (∑' j : ℕ, countableCocountableMass (f j) (hf j)) = 1 := by
        rw [tsum_eq_single i]
        · simp [countableCocountableMass, hi]
        · intro j hji
          simp [countableCocountableMass, hothers j hji]
      simp [countableCocountableMass, hnotUnion, hsum]
    · have hall : ∀ i, (f i).Countable := by
        intro i
        by_contra hi
        exact hsome ⟨i, hi⟩
      have hcnt : (⋃ n, f n).Countable := Set.countable_iUnion hall
      simp [countableCocountableMass, hcnt, hall]

theorem countableCocountableMeasure_apply
    (s : Set Label) (hs : MeasurableSet s) :
    countableCocountableMeasure s = countableCocountableMass s hs := by
  rw [countableCocountableMeasure, Measure.ofMeasurable_apply]

instance : IsProbabilityMeasure countableCocountableMeasure where
  measure_univ := by
    rw [countableCocountableMeasure_apply Set.univ MeasurableSet.univ]
    simp [countableCocountableMass, label_univ_not_countable]

theorem lowerSegment_measure_zero (w : Label) :
    countableCocountableMeasure (lowerSegment w) = 0 := by
  rw [countableCocountableMeasure_apply (lowerSegment w) (Or.inl (lowerSegment_countable w))]
  simp [countableCocountableMass, lowerSegment_countable]

/-- An admissible acceptable set is an upper tail. -/
def upperTail (threshold : Label) : Set Label := {y | threshold ≤ y}

theorem upperTail_compl_countable (threshold : Label) :
    (upperTail threshold)ᶜ.Countable := by
  have h := lowerSegment_countable threshold
  apply h.mono
  intro y hy
  change ¬ threshold ≤ y at hy
  change y < threshold
  exact lt_of_not_ge hy

theorem upperTail_measure_one (threshold : Label) :
    countableCocountableMeasure (upperTail threshold) = 1 := by
  have hcomp := upperTail_compl_countable threshold
  have hnot : ¬ (upperTail threshold).Countable := by
    intro hcnt
    have hu : (Set.univ : Set Label).Countable := by
      have hUnion : (upperTail threshold ∪ (upperTail threshold)ᶜ).Countable :=
        hcnt.union hcomp
      simpa using hUnion
    exact label_univ_not_countable hu
  rw [countableCocountableMeasure_apply (upperTail threshold) (Or.inr hcomp)]
  simp [countableCocountableMass, hnot]

/-- The set of predictions rejected by a tail whose threshold may depend
on the current sampled label. -/
def adaptiveMissSet (chooseThreshold : Label → Label) (witness : Label) :
    Set Label := {prediction | ¬ chooseThreshold prediction ≤ prediction}

/-- If the terminal tail must contain the already revealed witness, every
possible miss lies strictly below that fixed witness, even when the terminal
target family is selected after observing the sampled prediction. -/
theorem adaptiveMiss_subset_lowerSegment
    (chooseThreshold : Label → Label) (witness : Label)
    (hcontains : ∀ prediction, chooseThreshold prediction ≤ witness) :
    adaptiveMissSet chooseThreshold witness ⊆ lowerSegment witness := by
  intro prediction hmiss
  change ¬ chooseThreshold prediction ≤ prediction at hmiss
  change prediction < witness
  exact lt_of_lt_of_le (lt_of_not_ge hmiss) (hcontains prediction)

theorem adaptiveMiss_countable
    (chooseThreshold : Label → Label) (witness : Label)
    (hcontains : ∀ prediction, chooseThreshold prediction ≤ witness) :
    (adaptiveMissSet chooseThreshold witness).Countable := by
  apply (lowerSegment_countable witness).mono
  exact adaptiveMiss_subset_lowerSegment chooseThreshold witness hcontains

theorem adaptiveMiss_measurable
    (chooseThreshold : Label → Label) (witness : Label)
    (hcontains : ∀ prediction, chooseThreshold prediction ≤ witness) :
    MeasurableSet (adaptiveMissSet chooseThreshold witness) :=
  Or.inl (adaptiveMiss_countable chooseThreshold witness hcontains)

/-- The one-round conditional expected mistake is zero for every public
witness and every terminal adaptive tail containing that witness. -/
theorem adaptiveMiss_measure_zero
    (chooseThreshold : Label → Label) (witness : Label)
    (hcontains : ∀ prediction, chooseThreshold prediction ≤ witness) :
    countableCocountableMeasure (adaptiveMissSet chooseThreshold witness) = 0 := by
  apply MeasureTheory.Measure.mono_null
    (adaptiveMiss_subset_lowerSegment chooseThreshold witness hcontains)
  exact lowerSegment_measure_zero witness

/-- A single global target family of functions from naturals to labels. -/
def GlobalTailFamily (thresholds : ℕ → Label) (f : ℕ → Label) : Prop :=
  ∀ t, thresholds t ≤ f t

/-- The acceptable labels generated at context t by one target family. -/
def AcceptedAt (thresholds : ℕ → Label) (t : ℕ) (y : Label) : Prop :=
  ∃ f : ℕ → Label, GlobalTailFamily thresholds f ∧ f t = y

/-- One global family induces the specified upper tail at every context. -/
theorem acceptedAt_iff_upperTail
    (thresholds : ℕ → Label) (t : ℕ) (y : Label) :
    AcceptedAt thresholds t y ↔ thresholds t ≤ y := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact hf t
  · intro hy
    refine ⟨fun s => if s = t then y else thresholds s, ?_, ?_⟩
    · intro s
      by_cases hs : s = t
      · subst s
        simpa using hy
      · simp [hs]
    · simp

theorem globalTailFamily_nonempty (thresholds : ℕ → Label) :
    ∃ f : ℕ → Label, GlobalTailFamily thresholds f :=
  ⟨thresholds, fun _ => le_rfl⟩

/-- The successor of a countable ordinal is still below omega-one. -/
def succLabel (a : Label) : Label :=
  ⟨Ordinal.succ a.1, (Cardinal.isSuccLimit_omega 1).succ_lt a.2⟩

theorem lt_succLabel (a : Label) : a < succLabel a := by
  exact Ordinal.lt_succ a.1

/-- For a fixed deterministic prediction path, the adversary uses the next
ordinal as the visible witness and as the tail threshold. -/
def deterministicThresholds (prediction : ℕ → Label) : ℕ → Label :=
  fun t => succLabel (prediction t)

theorem deterministic_global_target_is_realizable
    (prediction : ℕ → Label) :
    (∃ f : ℕ → Label, GlobalTailFamily (deterministicThresholds prediction) f) ∧
    (∀ t y,
      AcceptedAt (deterministicThresholds prediction) t y ↔
        deterministicThresholds prediction t ≤ y) :=
  ⟨globalTailFamily_nonempty _, fun t y => acceptedAt_iff_upperTail _ _ _⟩

/-- Every deterministic prediction is excluded by the corresponding member
of the globally consistent tail family. -/
theorem deterministic_prediction_is_wrong
    (prediction : ℕ → Label) (t : ℕ) :
    ¬ deterministicThresholds prediction t ≤ prediction t := by
  exact not_le_of_gt (lt_succLabel (prediction t))

/-- Exact pathwise lower bound: every round is a mistake. -/
def deterministicRoundLoss (prediction : ℕ → Label) (t : ℕ) : ℕ :=
  if deterministicThresholds prediction t ≤ prediction t then 0 else 1

theorem deterministicRoundLoss_eq_one
    (prediction : ℕ → Label) (t : ℕ) :
    deterministicRoundLoss prediction t = 1 := by
  simp [deterministicRoundLoss, deterministic_prediction_is_wrong]

def deterministicTotalLoss (prediction : ℕ → Label) : ℕ → ℕ
  | 0 => 0
  | n + 1 => deterministicTotalLoss prediction n + deterministicRoundLoss prediction n

theorem deterministicTotalLoss_eq_horizon
    (prediction : ℕ → Label) (T : ℕ) :
    deterministicTotalLoss prediction T = T := by
  induction T with
  | zero => rfl
  | succ T ih =>
      simp [deterministicTotalLoss, ih, deterministicRoundLoss_eq_one]

/-- A deterministic learner as a function of its public past and current context. -/
abbrev DeterministicLearner := List (Nat × Label × Label) → Nat → Label

/-- The adversarial public trace: at context t, the learner's deterministic
prediction is known, and the witness is its ordinal successor. -/
def deterministicTrace (learner : DeterministicLearner) :
    ℕ → List (Nat × Label × Label)
  | 0 => []
  | n + 1 =>
      let history := deterministicTrace learner n
      let prediction := learner history n
      history ++ [(n, prediction, succLabel prediction)]

def deterministicPredictionPath (learner : DeterministicLearner) : ℕ → Label :=
  fun t => learner (deterministicTrace learner t) t

theorem deterministicLearner_exact_linear_loss
    (learner : DeterministicLearner) (T : ℕ) :
    deterministicTotalLoss (deterministicPredictionPath learner) T = T :=
  deterministicTotalLoss_eq_horizon _ _

end PublicSetting.OmegaOne
