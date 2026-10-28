import ProbabilisticBounds

/-!
Adaptive one-hit moment bound for finite sequential uniform draws.

A target is predictable when its label at a round depends only on the completed
history. At a history of length n, the next label is uniform on 0,...,n, so at
most one child is a match. We formalize the unnormalized sum of 2^(number of
matches) over all future draw paths.
-/

namespace PublicSetting.AdaptiveMoments

open PublicSetting.ProbabilisticBounds

def hitAt (target : Nat → List Nat → Nat)
    (history : List Nat) (draw : Nat) : Bool :=
  decide (draw = target history.length history)

theorem eventCount_zero_of_all_false {Ω : Type}
    (samples : List Ω) (event : Ω → Bool)
    (falseOnSamples : ∀ x, x ∈ samples → event x = false) :
    eventCount samples event = 0 := by
  induction samples with
  | nil => rfl
  | cons x xs ih =>
      have hx := falseOnSamples x (by simp)
      have htail : ∀ y, y ∈ xs → event y = false := by
        intro y hy
        exact falseOnSamples y (by simp [hy])
      simp [eventCount, hx, ih htail]

theorem eventCount_eq_le_one (xs : List Nat) (hxs : xs.Nodup) (target : Nat) :
    eventCount xs (fun x => decide (x = target)) ≤ 1 := by
  induction xs with
  | nil => simp [eventCount]
  | cons x xs ih =>
      rcases List.nodup_cons.mp hxs with ⟨hnotin, htailNodup⟩
      by_cases hxy : x = target
      · subst target
        have htailFalse : ∀ z, z ∈ xs → decide (z = x) = false := by
          intro z hz
          have hzx : z ≠ x := by
            intro hEq
            subst z
            exact hnotin hz
          simp [hzx]
        have hzero := eventCount_zero_of_all_false xs
          (fun z => decide (z = x)) htailFalse
        simp [eventCount, hzero]
      · have htail := ih htailNodup target
        simp [eventCount, hxy, htail]

theorem eventCount_range_eq_le_one (n target : Nat) :
    eventCount (List.range n) (fun x => decide (x = target)) ≤ 1 := by
  exact eventCount_eq_le_one (List.range n) (by simp) target

def weightedFuture (target : Nat → List Nat → Nat) : Nat → List Nat → Nat
  | 0, _ => 1
  | n + 1, history =>
      totalValue (List.range (history.length + 1)) (fun draw =>
        (if hitAt target history draw then 2 else 1) *
          weightedFuture target n (history ++ [draw]))

def weightedFutureBound : Nat → Nat → Nat
  | 0, _ => 1
  | n + 1, current => (current + 2) * weightedFutureBound n (current + 1)

theorem weightedFuture_le_bound (target : Nat → List Nat → Nat) :
    ∀ n history,
      weightedFuture target n history ≤
        weightedFutureBound n history.length := by
  intro n
  induction n with
  | zero =>
      intro history
      simp [weightedFuture, weightedFutureBound]
  | succ n ih =>
      intro history
      let b := weightedFutureBound n (history.length + 1)
      let hit := hitAt target history
      have hchild : ∀ draw,
          weightedFuture target n (history ++ [draw]) ≤ b := by
        intro draw
        have h := ih (history ++ [draw])
        simpa [b, List.length_append] using h
      have hpoint : ∀ draw,
          (if hit draw then 2 else 1) *
              weightedFuture target n (history ++ [draw]) ≤
            b + (if hit draw then b else 0) := by
        intro draw
        by_cases hh : hit draw
        · simp [hh]
          calc
            2 * weightedFuture target n (history ++ [draw]) ≤ 2 * b :=
              Nat.mul_le_mul_left 2 (hchild draw)
            _ = b + b := by omega
        · simp [hh]
          exact hchild draw
      have hsum := totalValue_mono
        (List.range (history.length + 1))
        (fun draw => (if hit draw then 2 else 1) *
          weightedFuture target n (history ++ [draw]))
        (fun draw => b + (if hit draw then b else 0)) hpoint
      have hdecomp :
          totalValue (List.range (history.length + 1))
              (fun draw => b + (if hit draw then b else 0)) =
            b * (history.length + 1) +
              b * eventCount (List.range (history.length + 1) hit) := by
        calc
          totalValue (List.range (history.length + 1))
              (fun draw => b + (if hit draw then b else 0))
              = totalValue (List.range (history.length + 1)) (fun _ => b) +
                  totalValue (List.range (history.length + 1))
                    (fun draw => if hit draw then b else 0) := by
                rw [totalValue_add]
          _ = b * (history.length + 1) +
                b * eventCount (List.range (history.length + 1) hit) := by
                rw [totalValue_const, totalValue_indicator]
      have hcount : eventCount (List.range (history.length + 1)) hit ≤ 1 := by
        simpa [hit, hitAt] using
          eventCount_range_eq_le_one (history.length + 1)
            (target history.length history)
      have hfinal :
          b * (history.length + 1) +
              b * eventCount (List.range (history.length + 1) hit) ≤
            (history.length + 2) * b := by
        calc
          b * (history.length + 1) +
              b * eventCount (List.range (history.length + 1) hit)
              ≤ b * (history.length + 1) + b :=
                Nat.add_le_add_left (Nat.mul_le_mul_left b hcount) _
          _ = (history.length + 2) * b := by
                simp [Nat.add_mul, Nat.mul_add, Nat.mul_comm,
                  Nat.mul_left_comm, Nat.mul_assoc, Nat.add_assoc,
                  Nat.add_comm, Nat.add_left_comm]
      calc
        weightedFuture target (n + 1) history
            = totalValue (List.range (history.length + 1))
                (fun draw => (if hit draw then 2 else 1) *
                  weightedFuture target n (history ++ [draw])) := rfl
        _ ≤ totalValue (List.range (history.length + 1))
              (fun draw => b + (if hit draw then b else 0)) := hsum
        _ = b * (history.length + 1) +
              b * eventCount (List.range (history.length + 1) hit) := hdecomp
        _ ≤ (history.length + 2) * b := hfinal
        _ = weightedFutureBound (n + 1) history.length := by
              simp [weightedFutureBound, b, Nat.mul_comm]

theorem factorial_succ (n : Nat) :
    factorial (n + 1) = (n + 1) * factorial n := rfl

theorem weightedFutureBound_mul_factorial (n current : Nat) :
    weightedFutureBound n current * factorial (current + 1) =
      factorial (current + n + 1) := by
  induction n with
  | zero =>
      simp [weightedFutureBound]
  | succ n ih =>
      calc
        weightedFutureBound (n + 1) current * factorial (current + 1)
            = weightedFutureBound n (current + 1) * factorial (current + 2) := by
                simp [weightedFutureBound, factorial_succ,
                  Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        _ = factorial ((current + 1) + n + 1) := ih (current + 1)
        _ = factorial (current + (n + 1) + 1) := by
              congr 1 <;> omega

theorem weightedFuture_le_factorial_succ
    (target : Nat → List Nat → Nat) (T : Nat) :
    weightedFuture target T [] ≤ factorial (T + 1) := by
  have hbound := weightedFuture_le_bound target T []
  have hfactor := weightedFutureBound_mul_factorial T 0
  have hboundEq : weightedFutureBound T 0 = factorial (T + 1) := by
    simpa using hfactor
  simpa [hboundEq] using hbound

end PublicSetting.AdaptiveMoments
