import Lean

/-!
# Finite probability-tail aggregation for the public-setting candidate

This file formalizes the finite-counting part of the randomized proof:
* event-union bounds over all candidate target indices;
* factorial-scaled aggregation of per-index tail estimates;
* truncating a bounded loss at a tail event to bound its uniform expectation.

Important boundary: the conditional-uniform-draw argument that supplies each
per-index factorial tail estimate is represented by an explicit hypothesis in
the aggregation theorem below. This module does not silently assume that this
probability bridge has been proved.
-/

namespace PublicSetting.ProbabilisticBounds

/-- Number of outcomes in a finite sample list satisfying a Boolean event.
Repeated list entries represent distinct equiprobable outcomes. -/
def eventCount {Ω : Type} : List Ω → (Ω → Bool) → Nat
  | [], _ => 0
  | x :: xs, event => (if event x then 1 else 0) + eventCount xs event

theorem eventCount_false {Ω : Type} (samples : List Ω) :
    eventCount samples (fun _ => false) = 0 := by
  induction samples with
  | nil => rfl
  | cons x xs ih => simp [eventCount, ih]

/-- Boolean union of a finite list of events. -/
def eventAny {Ω : Type} : List (Ω → Bool) → Ω → Bool
  | [], _ => false
  | event :: events, x => event x || eventAny events x

/-- Sum of event counts over a finite event list. -/
def sumEventCounts {Ω : Type} (samples : List Ω) : List (Ω → Bool) → Nat
  | [] => 0
  | event :: events =>
      eventCount samples event + sumEventCounts samples events

/-- Sum of a natural-valued observable over the sample list. -/
def totalValue {Ω : Type} : List Ω → (Ω → Nat) → Nat
  | [], _ => 0
  | x :: xs, value => value x + totalValue xs value

/-- Factorial, defined here to keep the proof assistant dependencies at Lean core. -/
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

theorem factorial_pos (n : Nat) : 0 < factorial n := by
  induction n with
  | zero => simp [factorial]
  | succ n ih =>
      simp [factorial, Nat.mul_pos (Nat.succ_pos n) ih]

/-- The event that at least one event in a finite family occurs is bounded
by the sum of the individual event counts. -/
theorem eventCount_or_le {Ω : Type} (samples : List Ω)
    (p q : Ω → Bool) :
    eventCount samples (fun x => p x || q x) ≤
      eventCount samples p + eventCount samples q := by
  induction samples with
  | nil => simp [eventCount]
  | cons x xs ih =>
      have hx :
          (if p x || q x then 1 else 0) ≤
            (if p x then 1 else 0) + (if q x then 1 else 0) := by
        cases p x <;> cases q x <;> decide
      change (if p x || q x then 1 else 0) +
          eventCount xs (fun y => p y || q y) ≤
        ((if p x then 1 else 0) + eventCount xs p) +
          ((if q x then 1 else 0) + eventCount xs q)
      omega

theorem eventCount_any_le_sumEventCounts {Ω : Type}
    (samples : List Ω) (events : List (Ω → Bool)) :
    eventCount samples (eventAny events) ≤ sumEventCounts samples events := by
  induction events with
  | nil => simpa [eventAny, sumEventCounts] using eventCount_false samples
  | cons event events ih =>
      calc
        eventCount samples (eventAny (event :: events))
            = eventCount samples (fun x => event x || eventAny events x) := rfl
        _ ≤ eventCount samples event + eventCount samples (eventAny events) :=
          eventCount_or_le samples event (eventAny events)
        _ ≤ eventCount samples event + sumEventCounts samples events :=
          Nat.add_le_add_left ih _
        _ = sumEventCounts samples (event :: events) := rfl

/-- Sum the per-index factorial-scaled tail estimates. -/
theorem factorial_mul_sumEventCounts_le {Ω : Type}
    (samples : List Ω) (events : List (Ω → Bool))
    (k q : Nat)
    (eachTail : ∀ event, event ∈ events →
      factorial k * eventCount samples event ≤ q ^ k * samples.length) :
    factorial k * sumEventCounts samples events ≤
      events.length * (q ^ k * samples.length) := by
  induction events with
  | nil => simp [sumEventCounts]
  | cons event events ih =>
      have hhead := eachTail event (by simp)
      have hrest : ∀ e, e ∈ events →
          factorial k * eventCount samples e ≤ q ^ k * samples.length := by
        intro e he
        exact eachTail e (by simp [he])
      have htail := ih hrest
      change factorial k *
          (eventCount samples event + sumEventCounts samples events) ≤
        Nat.succ events.length * (q ^ k * samples.length)
      calc
        factorial k *
            (eventCount samples event + sumEventCounts samples events)
            = factorial k * eventCount samples event +
                factorial k * sumEventCounts samples events := by
                  simp [Nat.mul_add]
        _ ≤ q ^ k * samples.length +
              events.length * (q ^ k * samples.length) :=
                Nat.add_le_add hhead htail
        _ = Nat.succ events.length * (q ^ k * samples.length) := by
              rw [Nat.succ_mul]
              omega

/-- Union-bound aggregation for a finite family of index-tail events.

The explicit premise is the per-index tail estimate supplied by the stochastic
part of the proof: k! * count{M_i >= k} <= q^k * numberOfSamples.
This theorem proves the subsequent finite union bound in integer-scaled form. -/
theorem factorial_mul_union_tail_le {Ω : Type}
    (samples : List Ω) (events : List (Ω → Bool))
    (k q : Nat)
    (eachTail : ∀ event, event ∈ events →
      factorial k * eventCount samples event ≤ q ^ k * samples.length) :
    factorial k * eventCount samples (eventAny events) ≤
      events.length * (q ^ k * samples.length) := by
  have hunion := eventCount_any_le_sumEventCounts samples events
  calc
    factorial k * eventCount samples (eventAny events)
        ≤ factorial k * sumEventCounts samples events :=
          Nat.mul_le_mul_left (factorial k) hunion
    _ ≤ events.length * (q ^ k * samples.length) :=
      factorial_mul_sumEventCounts_le samples events k q eachTail

/-- If the union of index-tail events is small enough after
cross-multiplication, its contribution to the uniform probability is at most
1/T. This is the arithmetic bridge from a factorial-scaled union bound to the
expectation-truncation lemma below. -/
theorem badBudget_of_union_tail_bound {Ω : Type}
    (samples : List Ω) (events : List (Ω → Bool))
    (k q T : Nat)
    (eachTail : ∀ event, event ∈ events →
      factorial k * eventCount samples event ≤ q ^ k * samples.length)
    (arithmeticBudget : T * events.length * q ^ k ≤ factorial k) :
    T * eventCount samples (eventAny events) ≤ samples.length := by
  have hunion := factorial_mul_union_tail_le samples events k q eachTail
  have hscaled :
      factorial k * (T * eventCount samples (eventAny events)) ≤
        factorial k * samples.length := by
    calc
      factorial k * (T * eventCount samples (eventAny events))
          = T * (factorial k * eventCount samples (eventAny events)) := by
              simp [Nat.mul_assoc, Nat.mul_comm]
      _ ≤ T * (events.length * (q ^ k * samples.length)) :=
            Nat.mul_le_mul_left T hunion
      _ = (T * events.length * q ^ k) * samples.length := by
            simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ factorial k * samples.length :=
            Nat.mul_le_mul_right samples.length arithmeticBudget
  apply Nat.le_of_not_gt
  intro hlt
  have hstrict :
      factorial k * samples.length <
        factorial k * (T * eventCount samples (eventAny events)) :=
    Nat.mul_lt_mul_of_pos_left hlt (factorial_pos k)
  omega

theorem totalValue_mono {Ω : Type} (samples : List Ω)
    (f g : Ω → Nat) (pointwise : ∀ x, f x ≤ g x) :
    totalValue samples f ≤ totalValue samples g := by
  induction samples with
  | nil => simp [totalValue]
  | cons x xs ih =>
      change f x + totalValue xs f ≤ g x + totalValue xs g
      exact Nat.add_le_add (pointwise x) ih

theorem totalValue_const {Ω : Type} (samples : List Ω) (K : Nat) :
    totalValue samples (fun _ => K) = K * samples.length := by
  induction samples with
  | nil => simp [totalValue]
  | cons x xs ih =>
      simp [totalValue, ih, Nat.mul_succ, Nat.add_comm]

theorem totalValue_indicator {Ω : Type} (samples : List Ω)
    (T : Nat) (bad : Ω → Bool) :
    totalValue samples (fun x => if bad x then T else 0) =
      T * eventCount samples bad := by
  induction samples with
  | nil => simp [totalValue, eventCount]
  | cons x xs ih =>
      cases hb : bad x <;>
        simp [totalValue, eventCount, hb, ih, Nat.mul_succ, Nat.mul_add,
          Nat.add_comm]

theorem totalValue_add {Ω : Type} (samples : List Ω)
    (f g : Ω → Nat) :
    totalValue samples (fun x => f x + g x) =
      totalValue samples f + totalValue samples g := by
  induction samples with
  | nil => simp [totalValue]
  | cons x xs ih =>
      simp [totalValue, ih, Nat.add_assoc, Nat.add_left_comm]

/-- A fully checked truncation lemma for uniform finite sample spaces.

If the observable is at most K off a bad event, at most K+T everywhere, and
T times the number of bad outcomes is at most the sample-space size, then
its average is at most K+1. The statement is written without division by
cross-multiplying the uniform expectation. -/
theorem totalValue_le_threshold_plus_one {Ω : Type}
    (samples : List Ω) (loss : Ω → Nat) (bad : Ω → Bool)
    (K T : Nat)
    (pointwise : ∀ x,
      loss x ≤ K + (if bad x then T else 0))
    (badBudget : T * eventCount samples bad ≤ samples.length) :
    totalValue samples loss ≤ (K + 1) * samples.length := by
  have hmono := totalValue_mono samples loss
    (fun x => K + (if bad x then T else 0)) pointwise
  have hsum :
      totalValue samples (fun x => K + (if bad x then T else 0)) =
        K * samples.length + T * eventCount samples bad := by
    calc
      totalValue samples (fun x => K + (if bad x then T else 0))
          = totalValue samples (fun _ => K) +
              totalValue samples (fun x => if bad x then T else 0) := by
                rw [totalValue_add]
      _ = K * samples.length + T * eventCount samples bad := by
            rw [totalValue_const, totalValue_indicator]
  calc
    totalValue samples loss ≤ K * samples.length + T * eventCount samples bad := by
      simpa [hsum] using hmono
    _ ≤ K * samples.length + samples.length :=
      Nat.add_le_add_left badBudget _
    _ = (K + 1) * samples.length := by
      simp [Nat.add_mul]


/-- End-to-end finite-sample consequence of the per-index factorial tail
premise. The assumption on each event is exactly where the conditional
uniform-draw / elementary-symmetric-sum proof must be plugged in. Once it is
available, the union bound and expectation truncation are fully checked here. -/
theorem totalValue_le_from_factorial_tails {Ω : Type}
    (samples : List Ω) (events : List (Ω → Bool))
    (loss : Ω → Nat) (K T q : Nat)
    (eachTail : ∀ event, event ∈ events →
      factorial K * eventCount samples event ≤ q ^ K * samples.length)
    (arithmeticBudget : T * events.length * q ^ K ≤ factorial K)
    (pointwise : ∀ x,
      loss x ≤ K + (if eventAny events x then T else 0)) :
    totalValue samples loss ≤ (K + 1) * samples.length := by
  exact totalValue_le_threshold_plus_one samples loss (eventAny events) K T
    pointwise
    (badBudget_of_union_tail_bound samples events K q T eachTail arithmeticBudget)


/-- Monotonicity of powers of two, proved in core Lean without Mathlib. -/
theorem pow_two_mono {a b : Nat} (hab : a ≤ b) : 2 ^ a ≤ 2 ^ b := by
  have hex : ∃ d, b = a + d := by
    refine ⟨b - a, ?_⟩
    omega
  obtain ⟨d, hd⟩ := hex
  rw [hd, Nat.pow_add]
  have hp : 1 ≤ 2 ^ d := by
    clear hd
    induction d with
    | zero => simp
    | succ d ih =>
        rw [Nat.pow_succ]
        omega
  have hmul := Nat.mul_le_mul_left (2 ^ a) hp
  simpa using hmul

/-- The score-threshold event used in Markov's inequality. -/
def scoreTailEvent {Ω : Type} (K : Nat) (score : Ω → Nat) : Ω → Bool :=
  fun x => decide (K ≤ score x)

/-- Finite-sample Markov inequality in integer-scaled form.
If a score has exponential weight 2^score, then the number of samples with
score at least K, multiplied by 2^K, is at most the sum of all exponential
weights. Repeated sample entries count as distinct equiprobable outcomes. -/
theorem exponentialMoment_tail_count_le {Ω : Type}
    (samples : List Ω) (score : Ω → Nat) (K : Nat) :
    2 ^ K * eventCount samples (scoreTailEvent K score) ≤
      totalValue samples (fun x => 2 ^ score x) := by
  have hpoint : ∀ x,
      (if scoreTailEvent K score x then 2 ^ K else 0) ≤ 2 ^ score x := by
    intro x
    by_cases h : K ≤ score x
    · simp [scoreTailEvent, h]
      exact pow_two_mono h
    · simp [scoreTailEvent, h]
  have hmono := totalValue_mono samples
    (fun x => if scoreTailEvent K score x then 2 ^ K else 0)
    (fun x => 2 ^ score x) hpoint
  calc
    2 ^ K * eventCount samples (scoreTailEvent K score)
        = totalValue samples
            (fun x => if scoreTailEvent K score x then 2 ^ K else 0) := by
              symm
              exact totalValue_indicator samples (2 ^ K) (scoreTailEvent K score)
    _ ≤ totalValue samples (fun x => 2 ^ score x) := hmono

/-- Aggregate a common integer-scaled tail bound over a finite event family. -/
theorem scaled_mul_sumEventCounts_le {Ω : Type}
    (samples : List Ω) (events : List (Ω → Bool))
    (scale bound : Nat)
    (eachTail : ∀ event, event ∈ events →
      scale * eventCount samples event ≤ bound * samples.length) :
    scale * sumEventCounts samples events ≤
      events.length * (bound * samples.length) := by
  induction events with
  | nil => simp [sumEventCounts]
  | cons event events ih =>
      have hhead := eachTail event (by simp)
      have hrest : ∀ e, e ∈ events →
          scale * eventCount samples e ≤ bound * samples.length := by
        intro e he
        exact eachTail e (by simp [he])
      have htail := ih hrest
      change scale *
          (eventCount samples event + sumEventCounts samples events) ≤
        Nat.succ events.length * (bound * samples.length)
      calc
        scale *
            (eventCount samples event + sumEventCounts samples events)
            = scale * eventCount samples event +
                scale * sumEventCounts samples events := by
                  rw [Nat.mul_add]
        _ ≤ bound * samples.length +
              events.length * (bound * samples.length) :=
                Nat.add_le_add hhead htail
        _ = Nat.succ events.length * (bound * samples.length) := by
              rw [Nat.succ_mul]
              omega

/-- Union bound for finite-sample events from a common scaled tail estimate. -/
theorem scaled_mul_union_tail_le {Ω : Type}
    (samples : List Ω) (events : List (Ω → Bool))
    (scale bound : Nat)
    (eachTail : ∀ event, event ∈ events →
      scale * eventCount samples event ≤ bound * samples.length) :
    scale * eventCount samples (eventAny events) ≤
      events.length * (bound * samples.length) := by
  have hunion := eventCount_any_le_sumEventCounts samples events
  calc
    scale * eventCount samples (eventAny events)
        ≤ scale * sumEventCounts samples events :=
          Nat.mul_le_mul_left scale hunion
    _ ≤ events.length * (bound * samples.length) :=
      scaled_mul_sumEventCounts_le samples events scale bound eachTail

/-- If the union's scaled tail mass is small enough, its contribution to a
uniform finite-sample expectation is at most 1. The positivity premise keeps
the division-free argument valid for arbitrary natural-number scales. -/
theorem badBudget_of_scaled_union_tail_bound {Ω : Type}
    (samples : List Ω) (events : List (Ω → Bool))
    (scale bound T : Nat) (scalePos : 0 < scale)
    (eachTail : ∀ event, event ∈ events →
      scale * eventCount samples event ≤ bound * samples.length)
    (arithmeticBudget : T * events.length * bound ≤ scale) :
    T * eventCount samples (eventAny events) ≤ samples.length := by
  have hunion := scaled_mul_union_tail_le samples events scale bound eachTail
  have hscaled :
      scale * (T * eventCount samples (eventAny events)) ≤
        scale * samples.length := by
    calc
      scale * (T * eventCount samples (eventAny events))
          = T * (scale * eventCount samples (eventAny events)) := by
              simp [Nat.mul_left_comm]
      _ ≤ T * (events.length * (bound * samples.length)) :=
            Nat.mul_le_mul_left T hunion
      _ = (T * events.length * bound) * samples.length := by
            simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ scale * samples.length :=
            Nat.mul_le_mul_right samples.length arithmeticBudget
  apply Nat.le_of_not_gt
  intro hlt
  have hstrict :
      scale * samples.length <
        scale * (T * eventCount samples (eventAny events)) :=
    Nat.mul_lt_mul_of_pos_left hlt scalePos
  omega

/-- Every candidate score inherits a tail bound from its exponential-moment
bound. If the uniform mean of 2^score is at most C, then
2^K * count(score >= K) <= C * sample-count, without using real division. -/
theorem exponentialMoment_tail_count_le_of_bound {Ω : Type}
    (samples : List Ω) (score : Ω → Nat) (K C : Nat)
    (momentBound : totalValue samples (fun x => 2 ^ score x) ≤
      C * samples.length) :
    2 ^ K * eventCount samples (scoreTailEvent K score) ≤
      C * samples.length :=
  Nat.le_trans
    (exponentialMoment_tail_count_le samples score K) momentBound

/-- Union over all candidate score functions, each with its own exponential
moment bound. This is the formal per-candidate-tail to all-candidates bridge. -/
theorem exponentialMoment_union_tail_count_le {Ω : Type}
    (samples : List Ω) (scores : List (Ω → Nat)) (K C : Nat)
    (momentBounds : ∀ score, score ∈ scores →
      totalValue samples (fun x => 2 ^ score x) ≤ C * samples.length) :
    2 ^ K * eventCount samples
        (eventAny (scores.map (scoreTailEvent K))) ≤
      scores.length * (C * samples.length) := by
  have htail :
      2 ^ K * eventCount samples
          (eventAny (scores.map (scoreTailEvent K))) ≤
        (scores.map (scoreTailEvent K)).length * (C * samples.length) := by
    apply scaled_mul_union_tail_le samples (scores.map (scoreTailEvent K))
      (2 ^ K) C
    intro event he
    rcases List.mem_map.mp he with ⟨score, hscore, rfl⟩
    exact exponentialMoment_tail_count_le_of_bound samples score K C
      (momentBounds score hscore)
  simpa using htail

/-- From candidate-wise exponential moments, derive a logarithmic-threshold
expectation bound whenever the chosen threshold makes the union tail budget
small enough. The pointwise premise is the explicit loss-to-candidate-score
reduction that must be proved for the concrete learning protocol. -/
theorem totalValue_le_from_exponential_moments {Ω : Type}
    (samples : List Ω) (scores : List (Ω → Nat))
    (loss : Ω → Nat) (K T C : Nat)
    (momentBounds : ∀ score, score ∈ scores →
      totalValue samples (fun x => 2 ^ score x) ≤ C * samples.length)
    (arithmeticBudget : T * scores.length * C ≤ 2 ^ K)
    (pointwise : ∀ x,
      loss x ≤ K +
        (if eventAny (scores.map (scoreTailEvent K)) x then T else 0)) :
    totalValue samples loss ≤ (K + 1) * samples.length := by
  apply totalValue_le_threshold_plus_one samples loss
    (eventAny (scores.map (scoreTailEvent K))) K T pointwise
  apply badBudget_of_scaled_union_tail_bound samples
    (scores.map (scoreTailEvent K)) (2 ^ K) C T
  · exact Nat.pow_pos (by decide : 0 < 2)
  · intro event he
    rcases List.mem_map.mp he with ⟨score, hscore, rfl⟩
    exact exponentialMoment_tail_count_le_of_bound samples score K C
      (momentBounds score hscore)
  · simpa using arithmeticBudget


/-- Pointwise maximum of a finite collection of candidate scores. -/
def maximumScore {Ω : Type} : List (Ω → Nat) → Ω → Nat
  | [], _ => 0
  | score :: scores, x => max (score x) (maximumScore scores x)

/-- If no candidate score reaches K, their maximum is at most K; if some score
reaches K, the maximum is still bounded by the horizon T. This is the
loss-to-tail reduction needed to turn the union bound into expected regret. -/
theorem maximumScore_le_threshold_plus_tail {Ω : Type}
    (scores : List (Ω → Nat)) (K T : Nat)
    (scoreBound : ∀ score, score ∈ scores → ∀ x, score x ≤ T) :
    ∀ x, maximumScore scores x ≤
      K + (if eventAny (scores.map (scoreTailEvent K)) x then T else 0) := by
  induction scores with
  | nil =>
      intro x
      simp [maximumScore, eventAny]
  | cons score scores ih =>
      intro x
      have hHeadBound : score x ≤ T := scoreBound score (by simp) x
      have hRestBound : ∀ s, s ∈ scores → ∀ y, s y ≤ T := by
        intro s hs y
        exact scoreBound s (by simp [hs]) y
      have hRest := ih hRestBound x
      cases hHeadEvent : scoreTailEvent K score x with
      | true =>
          have hRestLe : maximumScore scores x ≤ K + T := by
            cases hRestEvent : eventAny (scores.map (scoreTailEvent K)) x <;>
              simp [hRestEvent] at hRest <;> omega
          simp [maximumScore, eventAny, hHeadEvent]
          exact Nat.max_le.mpr ⟨by omega, hRestLe⟩
      | false =>
          have hHeadLe : score x ≤ K := by
            have hnot : ¬ K ≤ score x := by
              have hd : decide (K ≤ score x) = false := by
                simpa [scoreTailEvent] using hHeadEvent
              exact of_decide_eq_false hd
            omega
          cases hRestEvent : eventAny (scores.map (scoreTailEvent K)) x with
          | true =>
              have hRestLe : maximumScore scores x ≤ K + T := by
                simpa [hRestEvent] using hRest
              simp [maximumScore, eventAny, hHeadEvent, hRestEvent]
              exact Nat.max_le.mpr ⟨by omega, hRestLe⟩
          | false =>
              have hRestLe : maximumScore scores x ≤ K := by
                simpa [hRestEvent] using hRest
              simp [maximumScore, eventAny, hHeadEvent, hRestEvent]
              exact Nat.max_le.mpr ⟨hHeadLe, hRestLe⟩

/-- Finite-candidate expected-regret theorem. Under a common exponential-moment
bound for every candidate and a threshold satisfying the union-tail budget,
the average maximum candidate score is at most K+1. On a concrete learning
game, the scoreBound premise is the horizon bound and each score is its
candidate-specific match count. -/
theorem totalValue_maximumScore_le_from_exponential_moments {Ω : Type}
    (samples : List Ω) (scores : List (Ω → Nat))
    (K T C : Nat)
    (momentBounds : ∀ score, score ∈ scores →
      totalValue samples (fun x => 2 ^ score x) ≤ C * samples.length)
    (arithmeticBudget : T * scores.length * C ≤ 2 ^ K)
    (scoreBound : ∀ score, score ∈ scores → ∀ x, score x ≤ T) :
    totalValue samples (maximumScore scores) ≤ (K + 1) * samples.length := by
  exact totalValue_le_from_exponential_moments samples scores
    (maximumScore scores) K T C momentBounds arithmeticBudget
    (maximumScore_le_threshold_plus_tail scores K T scoreBound)

end PublicSetting.ProbabilisticBounds
