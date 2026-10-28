import Lean

namespace PublicSetting

/--
For a natural-valued regret profile r, this is an integer-scaled definition
of r(T) = o(T): for every positive rational scale a/b, eventually
b * r(T) < a * T.
-/
def IsSublinear (r : Nat → Nat) : Prop :=
  ∀ a b : Nat, 0 < a → 0 < b →
    ∃ N : Nat, ∀ T : Nat, N ≤ T → b * r T < a * T

/--
For a natural-valued regret profile r, this is an integer-scaled definition
of r(T) = Ω(T): some positive rational scale a/b lower-bounds r(T)
for all sufficiently large T.
-/
def IsLinear (r : Nat → Nat) : Prop :=
  ∃ a b N : Nat, 0 < a ∧ 0 < b ∧
    ∀ T : Nat, N ≤ T → a * T ≤ b * r T

/-- One profile cannot simultaneously have sublinear and linear growth. -/
theorem sublinear_not_linear (r : Nat → Nat) :
    ¬ (IsSublinear r ∧ IsLinear r) := by
  rintro ⟨hsub, ⟨a, b, N, ha, hb, hlin⟩⟩
  obtain ⟨N', hsub'⟩ := hsub a b ha hb
  let T := max N N'
  have hN : N ≤ T := Nat.le_max_left _ _
  have hN' : N' ≤ T := Nat.le_max_right _ _
  have hlinT := hlin T hN
  have hsubT := hsub' T hN'
  exact Nat.lt_irrefl (b * r T) (Nat.lt_of_lt_of_le hsubT hlinT)

/--
The exact growth-rate target, once regret is defined from a faithful public-game
semantics: a randomized profile is sublinear, and every deterministic learner's
profile is linear. This predicate is only a specification. No existence theorem
for a public game satisfying it is asserted here.
-/
def AsymptoticSeparationSpec
    (DeterministicLearner : Type)
    (randomizedRegret : Nat → Nat)
    (deterministicRegret : DeterministicLearner → Nat → Nat) : Prop :=
  IsSublinear randomizedRegret ∧
    ∀ learner : DeterministicLearner, IsLinear (deterministicRegret learner)

/--
One target family F is fixed for the entire infinite sequence. At each context,
the accepted labels are exactly the values attained there by members of F.
The visible label is also required to be accepted. This captures the global
consistency constraint independently of any choice of learner strategy.
-/
structure GlobalHypothesisInstance where
  H : Type
  X : Type
  Y : Type
  eval : H → X → Y
  target : H → Prop
  contexts : Nat → X
  accepted : Nat → Y → Prop
  visible : Nat → Y
  target_nonempty : ∃ h : H, target h
  accepted_exactly_target_values :
    ∀ t y, accepted t y ↔
      ∃ h : H, target h ∧ eval h (contexts t) = y
  visible_is_accepted : ∀ t, accepted t (visible t)

/--
A model with countably many labels and coordinate-wise hypotheses. The same
target predicate excludes one label per round, while every accepted set is
induced by that one global target family.
-/
def complementSingletonInstance (excluded : Nat → Nat) :
    GlobalHypothesisInstance where
  H := Nat → Nat
  X := Nat
  Y := Nat
  eval := fun h t => h t
  target := fun h => ∀ t, h t ≠ excluded t
  contexts := fun t => t
  accepted := fun t y => y ≠ excluded t
  visible := fun t => excluded t + 1
  target_nonempty := by
    refine ⟨fun t => excluded t + 1, ?_⟩
    intro t
    exact Nat.ne_of_gt (Nat.lt_succ_self (excluded t))
  accepted_exactly_target_values := by
    intro t y
    constructor
    · intro hy
      refine ⟨fun s => if s = t then y else excluded s + 1, ?_, ?_⟩
      · intro s
        by_cases hst : s = t
        · subst s
          simpa using hy
        · have hne : excluded s + 1 ≠ excluded s :=
            Nat.ne_of_gt (Nat.lt_succ_self (excluded s))
          simp [hst]
      · simp
    · rintro ⟨h, hh, rfl⟩
      exact hh t
  visible_is_accepted := by
    intro t
    exact Nat.ne_of_gt (Nat.lt_succ_self (excluded t))

/-- Loss 1 is incurred precisely when the prediction equals the excluded label. -/
def roundLoss (excluded prediction : Nat → Nat) (t : Nat) : Nat :=
  if prediction t = excluded t then 1 else 0

/-- Sum the round losses for rounds 0 through T-1, without finite-horizon shortcuts. -/
def totalLoss : Nat → (Nat → Nat) → (Nat → Nat) → Nat
  | 0, _, _ => 0
  | Nat.succ n, excluded, prediction =>
      totalLoss n excluded prediction +
        (if prediction n = excluded n then 1 else 0)

/-- For every horizon T, a path equal to the excluded labels loses exactly T. -/
theorem matched_path_loss (T : Nat) (path : Nat → Nat) :
    totalLoss T path path = T := by
  induction T with
  | zero => rfl
  | succ T ih =>
      simp [totalLoss, ih]

/--
For every exclusion sequence, complementSingletonInstance is globally
consistent and every pathwise accepted-label set is exact. This is not a
learner-separation theorem: the exclusion sequence is an input trajectory,
and no randomized-regret upper bound is established.
-/
theorem complementSingleton_is_global (excluded : Nat → Nat) :
    (∃ h : Nat → Nat, ∀ t, h t ≠ excluded t) ∧
    (∀ t y, (y ≠ excluded t) ↔
      ∃ h : Nat → Nat, (∀ s, h s ≠ excluded s) ∧ h t = y) := by
  constructor
  · exact ⟨fun t => excluded t + 1,
      fun t => Nat.ne_of_gt (Nat.lt_succ_self (excluded t))⟩
  · intro t y
    constructor
    · intro hy
      refine ⟨fun s => if s = t then y else excluded s + 1, ?_, ?_⟩
      · intro s
        by_cases hst : s = t
        · subst s
          simpa using hy
        · have hne : excluded s + 1 ≠ excluded s :=
            Nat.ne_of_gt (Nat.lt_succ_self (excluded s))
          simp [hst]
      · simp
    · rintro ⟨h, hh, rfl⟩
      exact hh t

end PublicSetting
