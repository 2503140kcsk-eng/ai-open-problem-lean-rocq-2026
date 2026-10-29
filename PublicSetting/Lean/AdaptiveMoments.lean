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
      · have htail := ih htailNodup
        simp [eventCount, hxy, htail]

theorem eventCount_range_eq_le_one (n target : Nat) :
    eventCount (List.range n) (fun x => decide (x = target)) ≤ 1 := by
  exact eventCount_eq_le_one (List.range n) (List.nodup_range) target

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
              b * eventCount (List.range (history.length + 1)) hit := by
        calc
          totalValue (List.range (history.length + 1))
              (fun draw => b + (if hit draw then b else 0))
              = totalValue (List.range (history.length + 1)) (fun _ => b) +
                  totalValue (List.range (history.length + 1))
                    (fun draw => if hit draw then b else 0) := by
                rw [totalValue_add]
          _ = b * (history.length + 1) +
                b * eventCount (List.range (history.length + 1)) hit := by
                rw [totalValue_const, totalValue_indicator]
                simp
      have hcount : eventCount (List.range (history.length + 1)) hit ≤ 1 := by
        change eventCount (List.range (history.length + 1))
          (fun draw => decide (draw = target history.length history)) ≤ 1
        exact eventCount_range_eq_le_one (history.length + 1)
          (target history.length history)
      have hcountMul :
          b * eventCount (List.range (history.length + 1)) hit ≤ b := by
        calc
          b * eventCount (List.range (history.length + 1)) hit
              ≤ b * 1 := Nat.mul_le_mul_left b hcount
          _ = b := by simp
      have hfinal :
          b * (history.length + 1) +
              b * eventCount (List.range (history.length + 1)) hit ≤
            (history.length + 2) * b := by
        have hidx : history.length + 2 = (history.length + 1) + 1 := by omega
        calc
          b * (history.length + 1) +
              b * eventCount (List.range (history.length + 1)) hit
              ≤ b * (history.length + 1) + b :=
                Nat.add_le_add_left hcountMul _
          _ = (history.length + 1) * b + b := by
                rw [Nat.mul_comm b (history.length + 1)]
          _ = ((history.length + 1) + 1) * b := by
                symm
                rw [Nat.add_mul]
                simp
          _ = (history.length + 2) * b := by rw [← hidx]
      calc
        weightedFuture target (n + 1) history
            = totalValue (List.range (history.length + 1))
                (fun draw => (if hit draw then 2 else 1) *
                  weightedFuture target n (history ++ [draw])) := rfl
        _ ≤ totalValue (List.range (history.length + 1))
              (fun draw => b + (if hit draw then b else 0)) := hsum
        _ = b * (history.length + 1) +
              b * eventCount (List.range (history.length + 1)) hit := hdecomp
        _ ≤ (history.length + 2) * b := hfinal
        _ = weightedFutureBound (n + 1) history.length := by
              simp [weightedFutureBound, b]

theorem factorial_succ (n : Nat) :
    factorial (n + 1) = (n + 1) * factorial n := rfl

theorem weightedFutureBound_mul_factorial (n current : Nat) :
    weightedFutureBound n current * factorial (current + 1) =
      factorial (current + n + 1) := by
  revert current
  induction n with
  | zero =>
      intro current
      simp [weightedFutureBound]
  | succ n ih =>
      intro current
      calc
        weightedFutureBound (n + 1) current * factorial (current + 1)
            = weightedFutureBound n (current + 1) * factorial (current + 2) := by
                simp [weightedFutureBound, factorial_succ,
                  Nat.mul_assoc, Nat.mul_left_comm]
        _ = factorial ((current + 1) + n + 1) := ih (current + 1)
        _ = factorial (current + (n + 1) + 1) := by
              congr 1 <;> omega

theorem weightedFuture_le_factorial_succ
    (target : Nat → List Nat → Nat) (T : Nat) :
    weightedFuture target T [] ≤ factorial (T + 1) := by
  have hbound := weightedFuture_le_bound target T []
  have hfactor := weightedFutureBound_mul_factorial T 0
  have hboundEq : weightedFutureBound T 0 = factorial (T + 1) := by
    simpa [factorial] using hfactor
  simpa [hboundEq] using hbound

/-- Cross-multiplied expectation bound: the sum of 2^(number of matches)
over the finite uniform path space is at most (T+1) times T!, the number
of paths. Dividing by T! gives E[2^M] <= T+1 without introducing rationals. -/
theorem weightedFuture_le_rounds_mul_factorial
    (target : Nat → List Nat → Nat) (T : Nat) :
    weightedFuture target T [] ≤ (T + 1) * factorial T := by
  have h := weightedFuture_le_factorial_succ target T
  rw [factorial_succ T] at h
  exact h


/-- Number of complete length-n future draw paths from a history of length
current. At a history of length j, exactly j+1 next draws are available. -/
def uniformFuturePathCount : Nat → Nat → Nat
  | 0, _ => 1
  | n + 1, current =>
      (current + 1) * uniformFuturePathCount n (current + 1)

/-- The number of future paths times the number of already-realized prefixes
is the corresponding factorial. This pins down the finite uniform sample
space without using an informal independence assumption. -/
theorem uniformFuturePathCount_mul_factorial (n current : Nat) :
    uniformFuturePathCount n current * factorial current =
      factorial (current + n) := by
  induction n generalizing current with
  | zero =>
      simp [uniformFuturePathCount]
  | succ n ih =>
      calc
        uniformFuturePathCount (n + 1) current * factorial current
            = uniformFuturePathCount n (current + 1) *
                ((current + 1) * factorial current) := by
                  simp [uniformFuturePathCount]
                  ac_rfl
        _ = uniformFuturePathCount n (current + 1) *
              factorial (current + 1) := by
                rw [factorial_succ]
        _ = factorial ((current + 1) + n) := ih (current + 1)
        _ = factorial (current + (n + 1)) := by
              congr 1 <;> omega

/-- There are exactly T! complete random paths from the empty history. -/
theorem uniformFuturePathCount_empty (T : Nat) :
    uniformFuturePathCount T 0 = factorial T := by
  have h := uniformFuturePathCount_mul_factorial T 0
  simpa [factorial] using h

/-- The existing weighted path sum is now explicitly normalized by the
cardinality of the uniform path space. Cross-multiplied form:
E[2^(number of matches)] <= T+1. The denominator is the proven path count T!,
so every complete draw sequence has mass 1/T!. -/
theorem uniformPath_exponentialMoment_bound
    (target : Nat → List Nat → Nat) (T : Nat) :
    weightedFuture target T [] ≤
      (T + 1) * uniformFuturePathCount T 0 := by
  rw [uniformFuturePathCount_empty]
  exact weightedFuture_le_rounds_mul_factorial target T



/-- Count future draw paths on which a predictable target is hit at least
threshold times. A hit consumes one unit of the remaining threshold. -/
def tailFutureCount (target : Nat → List Nat → Nat) :
    Nat → List Nat → Nat → Nat
  | 0, _, K => if K = 0 then 1 else 0
  | n + 1, history, K =>
      totalValue (List.range (history.length + 1)) (fun draw =>
        tailFutureCount target n (history ++ [draw])
          (if hitAt target history draw then K - 1 else K))

theorem totalValue_mul_left {Ω : Type} (samples : List Ω)
    (c : Nat) (f : Ω → Nat) :
    totalValue samples (fun x => c * f x) =
      c * totalValue samples f := by
  induction samples with
  | nil => simp [totalValue]
  | cons x xs ih => simp [totalValue, ih, Nat.mul_add]

/-- Recursive Markov inequality for the actual sequential uniform draw tree.
The numerator counts complete paths reaching the threshold; the weighted
future sum is the sum of 2^(hits) over the same tree. -/
theorem tailFutureCount_exponentialMoment_le
    (target : Nat → List Nat → Nat) :
    ∀ n history K,
      2 ^ K * tailFutureCount target n history K ≤
        weightedFuture target n history := by
  intro n
  induction n with
  | zero =>
      intro history K
      cases K <;> simp [tailFutureCount, weightedFuture]
  | succ n ih =>
      intro history K
      let draws := List.range (history.length + 1)
      let hit := hitAt target history
      have hpoint : ∀ draw,
          2 ^ K * tailFutureCount target n (history ++ [draw])
              (if hit draw then K - 1 else K) ≤
            (if hit draw then 2 else 1) *
              weightedFuture target n (history ++ [draw]) := by
        intro draw
        by_cases hhit : hit draw
        · cases K with
          | zero =>
              have hc := ih (history ++ [draw]) 0
              have hchild :
                  tailFutureCount target n (history ++ [draw]) 0 ≤
                    weightedFuture target n (history ++ [draw]) := by
                simpa using hc
              have hscaled :
                  tailFutureCount target n (history ++ [draw]) 0 ≤
                    2 * weightedFuture target n (history ++ [draw]) := by
                omega
              simpa [hhit] using hscaled
          | succ K =>
              have hc := ih (history ++ [draw]) K
              have hscaled :
                  2 ^ (K + 1) *
                      tailFutureCount target n (history ++ [draw]) K ≤
                    2 * weightedFuture target n (history ++ [draw]) := by
                calc
                  2 ^ (K + 1) *
                      tailFutureCount target n (history ++ [draw]) K =
                    2 * (2 ^ K *
                      tailFutureCount target n (history ++ [draw]) K) := by
                        simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm]
                  _ ≤ 2 * weightedFuture target n (history ++ [draw]) :=
                    Nat.mul_le_mul_left 2 hc
              simpa [hhit, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm,
                Nat.mul_left_comm] using hscaled
        · have hc := ih (history ++ [draw]) K
          simpa [hhit] using hc
      have hsum := totalValue_mono draws
        (fun draw => 2 ^ K *
          tailFutureCount target n (history ++ [draw])
            (if hit draw then K - 1 else K))
        (fun draw => (if hit draw then 2 else 1) *
          weightedFuture target n (history ++ [draw])) hpoint
      calc
        2 ^ K * tailFutureCount target (n + 1) history K
            = 2 ^ K * totalValue draws
                (fun draw => tailFutureCount target n (history ++ [draw])
                  (if hit draw then K - 1 else K)) := by
                    rfl
        _ = totalValue draws
              (fun draw => 2 ^ K *
                tailFutureCount target n (history ++ [draw])
                  (if hit draw then K - 1 else K)) := by
                    symm
                    exact totalValue_mul_left draws (2 ^ K)
                      (fun draw => tailFutureCount target n (history ++ [draw])
                        (if hit draw then K - 1 else K))
        _ ≤ totalValue draws
              (fun draw => (if hit draw then 2 else 1) *
                weightedFuture target n (history ++ [draw])) := hsum
        _ = weightedFuture target (n + 1) history := by
              simp [weightedFuture, draws, hit]

/-- Per-fixed-predictable-target tail numerator bound. Since the uniform path
space has T! equally likely paths, this is the integer-scaled tail-probability
bound 2^K * P(M >= K) <= T+1. -/
theorem tailFutureCount_tail_bound
    (target : Nat → List Nat → Nat) (T K : Nat) :
    2 ^ K * tailFutureCount target T [] K ≤
      (T + 1) * factorial T := by
  calc
    2 ^ K * tailFutureCount target T [] K
        ≤ weightedFuture target T [] :=
          tailFutureCount_exponentialMoment_le target T [] K
    _ ≤ (T + 1) * factorial T :=
      weightedFuture_le_rounds_mul_factorial target T



/-- Order rule for rational quotients, derived from positivity of the
denominator rather than assumed as a probability axiom. -/
theorem rat_div_le_of_le_mul {a b c : Rat}
    (hb : 0 < b) (h : a ≤ c * b) : a / b ≤ c := by
  by_contra hnot
  have hlt : c < a / b := lt_of_not_ge hnot
  have hmul : c * b < a := (Rat.lt_div_iff hb).mp hlt
  exact (not_lt_of_ge h) hmul

/-- The rational-valued expectation of the exponential match score under the
uniform distribution on complete paths. Every path has mass 1/T!, proved by
uniformFuturePathCount_empty. -/
def uniformPathExponentialMoment
    (target : Nat → List Nat → Nat) (T : Nat) : Rat :=
  (weightedFuture target T [] : Rat) /
    (uniformFuturePathCount T 0 : Rat)

/-- Exact normalized expectation bound for the concrete sequential sampler:
E[2^M] <= T+1. This theorem turns the weighted path sum into an actual rational
expectation by dividing by the verified number of equally likely paths. -/
theorem uniformPathExponentialMoment_le
    (target : Nat → List Nat → Nat) (T : Nat) :
    uniformPathExponentialMoment target T ≤ (T + 1 : Nat) := by
  unfold uniformPathExponentialMoment
  have hnat := uniformPath_exponential_moment_bound target T
  have hcast :
      (weightedFuture target T [] : Rat) ≤
        (((T + 1) * uniformFuturePathCount T 0 : Nat) : Rat) :=
    (Rat.natCast_le_natCast).2 hnat
  have hmoment :
      (weightedFuture target T [] : Rat) ≤
        (T + 1 : Rat) * (uniformFuturePathCount T 0 : Rat) := by
    simpa only [Nat.cast_mul] using hcast
  have hdenom : 0 < (uniformFuturePathCount T 0 : Rat) := by
    rw [uniformFuturePathCount_empty]
    exact Rat.natCast_pos.mpr (factorial_pos T)
  exact rat_div_le_of_le_mul hdenom hmoment



/-- Sum the per-candidate tail numerators. By the finite union bound, this is
an upper budget for the number of paths on which at least one listed target
has at least K matches. -/
def sumTailFutureCounts :
    List (Nat → List Nat → Nat) → Nat → Nat → Nat
  | [], _, _ => 0
  | target :: targets, T, K =>
      tailFutureCount target T [] K + sumTailFutureCounts targets T K

/-- Uniform tail budget over every member of any finite candidate list.
The bound is independent of target policies: the only inputs are the horizon
and the number of candidates. It is the count-space form of
P(exists candidate with M >= K) <= |candidates| (T+1) / 2^K. -/
theorem sumTailFutureCounts_bound
    (targets : List (Nat → List Nat → Nat)) (T K : Nat) :
    2 ^ K * sumTailFutureCounts targets T K ≤
      targets.length * ((T + 1) * factorial T) := by
  induction targets with
  | nil => simp [sumTailFutureCounts]
  | cons target targets ih =>
      have hhead := tailFutureCount_tail_bound target T K
      have htail := ih T K
      simp only [sumTailFutureCounts, List.length_cons]
      calc
        2 ^ K * (tailFutureCount target T [] K +
            sumTailFutureCounts targets T K)
            = 2 ^ K * tailFutureCount target T [] K +
                2 ^ K * sumTailFutureCounts targets T K := by
                  rw [Nat.mul_add]
        _ ≤ (T + 1) * factorial T +
              targets.length * ((T + 1) * factorial T) :=
                Nat.add_le_add hhead htail
        _ = Nat.succ targets.length * ((T + 1) * factorial T) := by
              rw [Nat.succ_mul]
              omega

end PublicSetting.AdaptiveMoments
