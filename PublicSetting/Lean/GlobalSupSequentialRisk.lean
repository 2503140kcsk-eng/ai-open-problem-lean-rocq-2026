import SequentialConditionalRisk

open Set MeasureTheory
open scoped ENNReal

namespace PublicSetting.GlobalSupSequentialRisk

open PublicSetting.OmegaOne
open PublicSetting.SequentialConditionalRisk

/-- One hypothesis family whose coordinate image at time t is the upper
tail with threshold beta t. The same function f is used at every time. -/
def globalTailFamily {T : ℕ} (beta : Fin T → Label) : Set (Fin T → Label) :=
  {f | ∀ t, beta t ≤ f t}

/-- The t-th coordinate image of one global tail family is exactly the
corresponding admissible upper tail. -/
theorem globalTailFamily_projection {T : ℕ}
    (beta : Fin T → Label) (t : Fin T) :
    Set.image (fun f : Fin T → Label => f t) (globalTailFamily beta) =
      upperTail (beta t) := by
  classical
  ext y
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact hf t
  · intro hy
    change beta t ≤ y at hy
    refine ⟨fun j => if j = t then y else beta j, ?_, ?_⟩
    · intro j
      by_cases hj : j = t
      · subst j
        simpa using hy
      · simp [hj]
    · simp


/-- A single horizon-independent hypothesis domain: functions on all
natural-number contexts. A finite vector of thresholds constrains only the
first T coordinates, leaving every later coordinate unrestricted. -/
def globalTailFamilyOnNat {T : ℕ} (beta : Fin T → Label) : Set (ℕ → Label) :=
  {f | ∀ t : Fin T, beta t ≤ f t}

/-- For the fixed class domain Y^N, each of the first T coordinate images
of one globally constrained family is exactly its prescribed upper tail. -/
theorem globalTailFamilyOnNat_projection {T : ℕ}
    (beta : Fin T → Label) (t : Fin T) :
    Set.image (fun f : ℕ → Label => f t) (globalTailFamilyOnNat beta) =
      upperTail (beta t) := by
  classical
  ext y
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact hf t
  · intro hy
    change beta t ≤ y at hy
    let base : ℕ → Label := fun n =>
      if hn : n < T then beta ⟨n, hn⟩ else ⊥
    refine ⟨Function.update base t y, ?_, ?_⟩
    · intro s
      by_cases hst : (s : ℕ) = (t : ℕ)
      · have hst' : s = t := Fin.ext hst
        subst s
        simp [base, t.isLt, hy]
      · simp [Function.update, base, s.isLt, hst]
    · simp [Function.update, base, t.isLt, hy]

/-- Terminal loss after choosing one common vector of upper-tail thresholds
subject to the visible-witness constraints. -/
noncomputable def globalTailTerminalSupLoss {T : ℕ}
    (witness prediction : Fin T → Label) : ℝ≥0∞ :=
  ⨆ beta : {beta : Fin T → Label // ∀ t, beta t ≤ witness t},
    ∑ t : Fin T,
      if prediction t < beta.1 t then (1 : ℝ≥0∞) else 0

/-- The predictable stage-loss sum induced by the witnesses fixed before
each current draw. -/
noncomputable def predictableMissCount {T : ℕ}
    (witness prediction : Fin T → Label) : ℝ≥0∞ :=
  ∑ t : Fin T,
    if prediction t < witness t then (1 : ℝ≥0∞) else 0

/-- Exact global-sup identity: the terminal supremum over a single globally
consistent hypothesis family equals the predictable miss count. No
supremum/sum interchange and no round-dependent choice of family occurs. -/
theorem globalTailTerminalSupLoss_eq_predictableMissCount {T : ℕ}
    (witness prediction : Fin T → Label) :
    globalTailTerminalSupLoss witness prediction =
      predictableMissCount witness prediction := by
  classical
  unfold globalTailTerminalSupLoss predictableMissCount
  apply le_antisymm
  · apply iSup_le
    intro beta
    apply Finset.sum_le_sum
    intro t ht
    by_cases h : prediction t < beta.1 t
    · have hw : prediction t < witness t :=
        lt_of_lt_of_le h (beta.2 t)
      simp [h, hw]
    · simp [h]
  · refine le_iSup_of_le ⟨witness, fun _ => le_rfl⟩ ?_
    rfl

/-- The sequential one-step operator for the public protocol.

Order of play is sup_x inf_p sup_w: the adversary chooses the context,
the learner chooses a draw law, and the adversary fixes its visible witness
before Nature draws y. The current conditional risk is the probability of
the measurable section {y | y < w}; the successor may depend on the draw. -/
noncomputable def publicGlobalSupBellmanStep
    {H X P : Type*}
    (draw : P → Measure Label)
    (next : H → X → P → Label → Label → H)
    (continuation : H → ℝ≥0∞)
    (h : H) : ℝ≥0∞ :=
  ⨆ x, ⨅ p, ⨆ w,
    draw p (lowerSegment w) +
      ∫⁻ y, continuation (next h x p w y) ∂draw p

/-- A single learner action whose every one-step section risk vanishes,
combined with a zero continuation, forces the public Bellman value to zero.
No measurability of next as a function of the public history is used:
for each fixed history the continuation integrand is identically zero. -/
theorem publicGlobalSupBellmanStep_eq_zero_of_policy
    {H X P : Type*}
    (draw : P → Measure Label)
    (next : H → X → P → Label → Label → H)
    (continuation : H → ℝ≥0∞)
    (p0 : P)
    (hzero : ∀ w, draw p0 (lowerSegment w) = 0)
    (hcont : ∀ h, continuation h = 0)
    (h : H) :
    publicGlobalSupBellmanStep draw next continuation h = 0 := by
  classical
  unfold publicGlobalSupBellmanStep
  apply le_antisymm
  · apply iSup_le
    intro x
    calc
      (⨅ p, ⨆ w,
          draw p (lowerSegment w) +
            ∫⁻ y, continuation (next h x p w y) ∂draw p)
        ≤
          (⨆ w,
            draw p0 (lowerSegment w) +
              ∫⁻ y, continuation (next h x p0 w y) ∂draw p0) :=
          iInf_le (fun p =>
            ⨆ w, draw p (lowerSegment w) +
              ∫⁻ y, continuation (next h x p w y) ∂draw p) p0
      _ = 0 := by
        apply le_antisymm
        · apply iSup_le
          intro w
          simp [hzero w, hcont]
        · exact bot_le
  · exact bot_le

/-- Finite-horizon public value obtained by recursively composing the
one-step conditional section risks. This is a sequential value semantics,
not an integral of a potentially nonmeasurable full-path payoff. -/
noncomputable def publicGlobalSupGameValue
    {H X P : Type*}
    (draw : P → Measure Label)
    (next : H → X → P → Label → Label → H) :
    ℕ → H → ℝ≥0∞
  | 0, _ => 0
  | n + 1, h =>
      publicGlobalSupBellmanStep draw next
        (publicGlobalSupGameValue draw next n) h

/-- Backward induction: if p0 uses a law giving zero mass to every strict
initial segment, then the recursively defined public value is zero at
every finite horizon and every public history, irrespective of how the
next public history depends on the current draw. -/
theorem publicGlobalSupGameValue_eq_zero
    {H X P : Type*}
    (draw : P → Measure Label)
    (next : H → X → P → Label → Label → H)
    (p0 : P)
    (hzero : ∀ w, draw p0 (lowerSegment w) = 0) :
    ∀ n h, publicGlobalSupGameValue draw next n h = 0 := by
  intro n
  induction n with
  | zero =>
      intro h
      rfl
  | succ n ih =>
      intro h
      simp only [publicGlobalSupGameValue]
      exact publicGlobalSupBellmanStep_eq_zero_of_policy
        draw next (publicGlobalSupGameValue draw next n)
        p0 hzero ih h

/-- Concrete omega-one instance. The learner's fixed action is the
countable-cocountable probability measure; every pre-draw witness has a
countable, hence null, strict lower segment. -/
theorem omegaOne_publicGlobalSupGameValue_eq_zero
    {H X P : Type*}
    (draw : P → Measure Label)
    (next : H → X → P → Label → Label → H)
    (p0 : P)
    (hdraw : draw p0 = countableCocountableMeasure) :
    ∀ n h, publicGlobalSupGameValue draw next n h = 0 := by
  apply publicGlobalSupGameValue_eq_zero draw next p0
  intro w
  rw [hdraw]
  exact lowerSegment_measure_zero w

#print axioms globalTailFamily_projection
#print axioms globalTailTerminalSupLoss_eq_predictableMissCount
#print axioms publicGlobalSupGameValue_eq_zero
#print axioms omegaOne_publicGlobalSupGameValue_eq_zero

end PublicSetting.GlobalSupSequentialRisk
