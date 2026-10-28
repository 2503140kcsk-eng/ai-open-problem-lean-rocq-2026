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
              simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
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

end PublicSetting.ProbabilisticBounds
