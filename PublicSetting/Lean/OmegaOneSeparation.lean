module

import Mathlib

public section

/-!
# The omega-one countable/cocountable measure construction

This file formalizes the measurable-space and measure-theoretic core of a candidate
separation for Shao–Fang–Lin–Tao, Partial Feedback Online Learning
(arXiv:2601.21462v3), Section 3.3.

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
abbrev Label := Set.Iio (Ordinal.omega (1 : Ordinal.{0}) : Ordinal.{0})

theorem label_univ_not_countable : ¬ (Set.univ : Set Label).Countable := by
  intro h
  have hcount : Countable Label := Set.countable_univ_iff.mp h
  let b : Ordinal.{0} := ⨆ a : Label, (a : Ordinal.{0})
  have hb : b < Ordinal.omega (1 : Ordinal.{0}) := by
    exact @Ordinal.iSup_lt_omega_one Label hcount
      (fun a => (a : Ordinal.{0})) (fun a => a.2)
  have hbdd : BddAbove (Set.range fun a : Label => (a : Ordinal.{0})) := by
    refine ⟨Ordinal.omega (1 : Ordinal.{0}), ?_⟩
    rintro _ ⟨a, rfl⟩
    exact a.2.le
  have hbound : ∀ a : Label, (a : Ordinal.{0}) ≤ b := by
    intro a
    exact le_ciSup hbdd a
  let w : Label := ⟨Order.succ b, (Cardinal.isSuccLimit_omega (1 : Ordinal.{0})).succ_lt hb⟩
  have hw : b < (w : Ordinal) := by
    simp [w]
  exact (not_lt_of_ge (hbound w)) hw

/-- Every strict initial segment below a label is countable. -/
def lowerSegment (w : Label) : Set Label := {x | x.1 < w.1}

theorem ordinal_lt_succ (a : Ordinal) : a < Order.succ a :=
  Order.lt_succ_of_not_isMax (not_isMax a)

theorem lowerSegment_countable (w : Label) : (lowerSegment w).Countable := by
  have h : (Set.Iio w.1 : Set Ordinal).Countable :=
    Cardinal.countable_Iio_of_lt_omega_one w.2
  exact h.preimage Subtype.val_injective

/-- Every countable family of upper tails has a common label. This is the
    cofinality-omega-one fact that prevents Theorem 15's nested-countable
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
  have hbdd : BddAbove (Set.range fun k : ℕ => (thresholds k).1) := by
    refine ⟨Ordinal.omega 1, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact (thresholds k).2.le
  exact le_ciSup hbdd n

/-- The countable-cocountable sigma algebra on the label space. -/
@[instance_reducible]
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
      exact fun hxi => hx (Set.mem_iUnion.mpr ⟨i, hxi⟩)
    · left
      apply Set.countable_iUnion
      intro i
      by_contra hi
      exact hsome ⟨i, hi⟩

instance : MeasurableSpace Label := countableCocountableMeasurableSpace

/-- The 0/1 mass: countable sets have mass zero and cocountable sets mass one. -/
noncomputable def countableCocountableMass (s : Set Label) : ENNReal := by
  classical
  exact if s.Countable then 0 else 1

theorem countableCocountableMass_empty :
    countableCocountableMass (∅ : Set Label) = 0 := by
  simp [countableCocountableMass]

/-- Countable additivity of the 0/1 mass on pairwise-disjoint measurable sets. -/
theorem countableCocountableMass_iUnion
    (f : ℕ → Set Label) (hf : ∀ i, MeasurableSet (f i))
    (hdisj : Pairwise (fun i j => Disjoint (f i) (f j))) :
    countableCocountableMass (⋃ i, f i) =
      ∑' i, countableCocountableMass (f i) := by
  classical
  by_cases hsome : ∃ i, ¬ (f i).Countable
  · obtain ⟨i, hi⟩ := hsome
    have hcomp : (f i)ᶜ.Countable := (hf i).resolve_left hi
    have hcompUnion : (⋃ n, f n)ᶜ.Countable := by
      apply hcomp.mono
      intro x hx
      change x ∈ (⋃ n, f n)ᶜ at hx
      exact fun hxi => hx (Set.mem_iUnion.mpr ⟨i, hxi⟩)
    have hnotUnion : ¬ (⋃ n, f n).Countable := by
      intro hcnt
      have hwhole : (Set.univ : Set Label).Countable := by
        have hu : ((⋃ n, f n) ∪ (⋃ n, f n)ᶜ).Countable :=
          hcnt.union hcompUnion
        apply hu.mono
        intro x _
        by_cases hx : x ∈ ⋃ n, f n
        · exact Or.inl hx
        · exact Or.inr hx
      exact label_univ_not_countable hwhole
    have hothers : ∀ j, j ≠ i → (f j).Countable := by
      intro j hji
      have hdis : Disjoint (f i) (f j) := hdisj (Ne.symm hji)
      apply hcomp.mono
      intro x hxj hxi
      exact (Set.disjoint_left.mp hdis) hxi hxj
    have hsum : (∑' j : ℕ, countableCocountableMass (f j)) = 1 := by
      rw [tsum_eq_single i]
      · simp [countableCocountableMass, hi]
      · intro j hji
        simp [countableCocountableMass, hothers j hji]
    simpa [countableCocountableMass, hnotUnion] using hsum.symm
  · have hall : ∀ i, (f i).Countable := by
      intro i
      by_contra hi
      exact hsome ⟨i, hi⟩
    have hcnt : (⋃ n, f n).Countable := Set.countable_iUnion hall
    simp [countableCocountableMass, hcnt, hall]

noncomputable def countableCocountableMeasure : Measure Label :=
  Measure.ofMeasurable
    (fun s (_ : MeasurableSet s) => countableCocountableMass s)
    (by simpa using countableCocountableMass_empty)
    (by
      intro f hf hdisj
      exact countableCocountableMass_iUnion f hf hdisj)

theorem countableCocountableMeasure_apply
    (s : Set Label) (hs : MeasurableSet s) :
    countableCocountableMeasure s = countableCocountableMass s := by
  unfold countableCocountableMeasure
  exact Measure.ofMeasurable_apply s hs

instance : IsProbabilityMeasure countableCocountableMeasure where
  measure_univ := by
    rw [countableCocountableMeasure_apply Set.univ MeasurableSet.univ]
    simp [countableCocountableMass, label_univ_not_countable]

theorem lowerSegment_measure_zero (w : Label) :
    countableCocountableMeasure (lowerSegment w) = 0 := by
  rw [countableCocountableMeasure_apply (lowerSegment w)
    (Or.inl (lowerSegment_countable w))]
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

/-- Every upper tail has a null complement under the countable-cocountable
probability measure. This is the expected zero-one loss for predicting from
the fixed measure when the hidden acceptable set is that tail. -/
theorem upperTail_complement_measure_zero (threshold : Label) :
    countableCocountableMeasure ((upperTail threshold)ᶜ) = 0 := by
  rw [countableCocountableMeasure_apply _ (Or.inl (upperTail_compl_countable threshold))]
  simp [countableCocountableMass, upperTail_compl_countable]


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

/-- The intersection of all admissible upper tails is empty. -/
theorem allUpperTails_intersection_empty (y : Label) :
    ∃ threshold : Label, ¬ upperTail threshold y := by
  refine ⟨⟨Order.succ y.1, (Cardinal.isSuccLimit_omega 1).succ_lt y.2⟩, ?_⟩
  exact not_le_of_gt (ordinal_lt_succ y.1)

/-- The set of predictions rejected by a tail whose threshold may depend
on the current sampled label. -/
def adaptiveMissSet (chooseThreshold : Label → Label) (_witness : Label) :
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


/-- The full finite prediction path may determine every terminal threshold.
If each selected upper tail still contains its pre-sampling witness, then any
round with a mistake has its sampled coordinate below that fixed witness. -/
def terminalPathMissSet (T : ℕ)
    (chooseThreshold : (Fin T → Label) → Fin T → Label) :
    Set (Fin T → Label) :=
  {path | ∃ t, ¬ chooseThreshold path t ≤ path t}

/-- Even when the terminal global target family is selected after the complete
prediction path, the pathwise error event is contained in a finite union of
coordinate cylinders over the null initial segments. -/
theorem terminalPathMiss_subset_badCoordinateCylinders
    (T : ℕ) (witnesses : Fin T → Label)
    (chooseThreshold : (Fin T → Label) → Fin T → Label)
    (hcontains : ∀ path t, chooseThreshold path t ≤ witnesses t) :
    terminalPathMissSet T chooseThreshold ⊆
      ⋃ t : Fin T, {path | path t ∈ lowerSegment (witnesses t)} := by
  intro path hmiss
  rcases hmiss with ⟨t, hmiss⟩
  refine Set.mem_iUnion.2 ⟨t, ?_⟩
  change path t < witnesses t
  exact lt_of_lt_of_le (lt_of_not_ge hmiss) (hcontains path t)

/-- The finite product of the roundwise countable-cocountable laws assigns
zero probability to every path on which a path-dependent terminal target
causes a mistake, provided each target tail contains its pre-sampling
visible witness. The key inclusion is pathwise; the probability-zero step
uses the product-coordinate null-preimage theorem. -/
theorem terminalPathMiss_pi_measure_zero
    (T : ℕ) (witnesses : Fin T → Label)
    (chooseThreshold : (Fin T → Label) → Fin T → Label)
    (hcontains : ∀ path t, chooseThreshold path t ≤ witnesses t) :
    Measure.pi (fun _ : Fin T => countableCocountableMeasure)
      (terminalPathMissSet T chooseThreshold) = 0 := by
  apply MeasureTheory.Measure.mono_null
    (terminalPathMiss_subset_badCoordinateCylinders T witnesses chooseThreshold hcontains)
  rw [measure_iUnion_null_iff]
  intro t
  exact Measure.pi_eval_preimage_null
    (μ := fun _ : Fin T => countableCocountableMeasure)
    (i := t)
    (s := lowerSegment (witnesses t))
    (lowerSegment_measure_zero (witnesses t))

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

/-- A member of the global target family is a zero-loss comparator on every
finite horizon, because each of its values lies in the corresponding
acceptable tail. -/
def comparatorTotalLoss (thresholds : ℕ → Label) (f : ℕ → Label) (T : ℕ) : ℕ :=
  ∑ t ∈ Finset.range T, if thresholds t ≤ f t then 0 else 1

theorem comparatorTotalLoss_zero
    (thresholds : ℕ → Label) (f : ℕ → Label)
    (hf : GlobalTailFamily thresholds f) (T : ℕ) :
    comparatorTotalLoss thresholds f T = 0 := by
  change (∑ t ∈ Finset.range T, if thresholds t ≤ f t then 0 else 1) = 0
  apply Finset.sum_eq_zero
  intro t ht
  change ∀ t, thresholds t ≤ f t at hf
  simp [hf t]


/-- The successor of a countable ordinal is still below omega-one. -/
def succLabel (a : Label) : Label :=
  ⟨Order.succ a.1, (Cardinal.isSuccLimit_omega 1).succ_lt a.2⟩

theorem lt_succLabel (a : Label) : a < succLabel a := by
  exact ordinal_lt_succ a.1

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
  ⟨globalTailFamily_nonempty _, fun t y => acceptedAt_iff_upperTail (deterministicThresholds prediction) t y⟩

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

/-- A public round records its context, the visible label, and the realized
prediction. The latter is visible to the public adversary before the next
round. -/
abbrev PublicHistory := List (Nat × Label × Label)

/-- A deterministic learner is a function of the complete public past and
the current context. -/
abbrev DeterministicLearner := PublicHistory → Nat → Label

/-- The adversarial public trace: at context t, the learner's deterministic
prediction is known, and the witness is its ordinal successor. -/
def deterministicTrace (learner : DeterministicLearner) :
    ℕ → PublicHistory
  | 0 => []
  | n + 1 =>
      let history := deterministicTrace learner n
      let prediction := learner history n
      history ++ [(n, succLabel prediction, prediction)]

def deterministicPredictionPath (learner : DeterministicLearner) : ℕ → Label :=
  fun t => learner (deterministicTrace learner t) t

theorem deterministicLearner_exact_linear_loss
    (learner : DeterministicLearner) (T : ℕ) :
    deterministicTotalLoss (deterministicPredictionPath learner) T = T :=
  deterministicTotalLoss_eq_horizon _ _

/-- Full finite-horizon deterministic witness: one fixed global target family
realizes every revealed upper tail, the comparator incurs zero loss, and the
deterministic learner incurs one mistake per round. -/
theorem deterministicLearner_global_separation_witness
    (learner : DeterministicLearner) (T : ℕ) :
    ∃ f : ℕ → Label,
      GlobalTailFamily (deterministicThresholds (deterministicPredictionPath learner)) f ∧
      (∀ t y, AcceptedAt (deterministicThresholds (deterministicPredictionPath learner)) t y
        ↔ deterministicThresholds (deterministicPredictionPath learner) t ≤ y) ∧
      comparatorTotalLoss (deterministicThresholds (deterministicPredictionPath learner)) f T = 0 ∧
      deterministicTotalLoss (deterministicPredictionPath learner) T = T := by
  let thresholds := deterministicThresholds (deterministicPredictionPath learner)
  obtain ⟨f, hf⟩ := globalTailFamily_nonempty thresholds
  refine ⟨f, hf, ?_, comparatorTotalLoss_zero thresholds f hf T,
    deterministicLearner_exact_linear_loss learner T⟩
  intro t y
  exact acceptedAt_iff_upperTail thresholds t y

/-- The constant-measure randomized learner: it outputs the same
countable-cocountable probability measure after every public history. -/
noncomputable def constantRandomizedAction : Measure Label :=
  countableCocountableMeasure

noncomputable def constantRandomizedLearner
    (_history : PublicHistory) (_context : Nat) : Measure Label :=
  constantRandomizedAction

/-- Uniform conditional guarantee in the public protocol: at every possible
public history, for every visible label selected before the current draw, and
for every terminal upper-tail choice (even one depending on the current
sample) that still contains that visible label, the current miss probability
is zero. -/
theorem constantRandomizedLearner_zero_at_every_public_history
    (history : PublicHistory) (context : Nat)
    (chooseThreshold : Label → Label) (witness : Label)
    (hcontains : ∀ prediction, chooseThreshold prediction ≤ witness) :
    constantRandomizedLearner history context
      (adaptiveMissSet chooseThreshold witness) = 0 := by
  simpa [constantRandomizedLearner, constantRandomizedAction] using
    (adaptiveMiss_measure_zero chooseThreshold witness hcontains)

/-- The finite-horizon expected loss of this strategy on a sequence of
upper-tail acceptable sets. For an indicator loss, expectation equals the
measure of its error event. -/
noncomputable def randomizedExpectedTotalLoss (thresholds : ℕ → Label) (T : ℕ) : ENNReal :=
  ∑ t ∈ Finset.range T,
    (constantRandomizedLearner ([] : PublicHistory) t) ((upperTail (thresholds t))ᶜ)

theorem constantRandomizedLearner_zero_expected_loss
    (thresholds : ℕ → Label) (T : ℕ) :
    randomizedExpectedTotalLoss thresholds T = 0 := by
  simp [randomizedExpectedTotalLoss, constantRandomizedLearner, constantRandomizedAction,
    upperTail_complement_measure_zero]

/-- Combined finite-horizon separation statement in the paper's set-realizable
measurable-space model. Every randomized round uses the same valid probability
measure and has zero expected loss for every upper-tail sequence. Conversely,
each deterministic public strategy admits one fixed global target family that
realizes all tails and forces exactly T mistakes while the comparator has zero
loss. -/
theorem omegaOne_finite_horizon_separation (T : ℕ) :
    (∀ thresholds : ℕ → Label,
      ∃ f : ℕ → Label,
        GlobalTailFamily thresholds f ∧
        (∀ t y, AcceptedAt thresholds t y ↔ thresholds t ≤ y) ∧
        comparatorTotalLoss thresholds f T = 0 ∧
        randomizedExpectedTotalLoss thresholds T = 0) ∧
    (∀ learner : DeterministicLearner,
      ∃ f : ℕ → Label,
        GlobalTailFamily (deterministicThresholds (deterministicPredictionPath learner)) f ∧
        (∀ t y,
          AcceptedAt (deterministicThresholds (deterministicPredictionPath learner)) t y
            ↔ deterministicThresholds (deterministicPredictionPath learner) t ≤ y) ∧
        comparatorTotalLoss (deterministicThresholds (deterministicPredictionPath learner)) f T = 0 ∧
        deterministicTotalLoss (deterministicPredictionPath learner) T = T) := by
  constructor
  · intro thresholds
    obtain ⟨f, hf⟩ := globalTailFamily_nonempty thresholds
    refine ⟨f, hf, ?_, comparatorTotalLoss_zero thresholds f hf T,
      constantRandomizedLearner_zero_expected_loss thresholds T⟩
    intro t y
    exact acceptedAt_iff_upperTail thresholds t y
  · intro learner
    exact deterministicLearner_global_separation_witness learner T


end PublicSetting.OmegaOne
