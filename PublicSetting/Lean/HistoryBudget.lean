import GlobalSupSequentialRisk

open Set MeasureTheory
open scoped ENNReal

namespace PublicSetting.GlobalSupSequentialRisk

/-- A uniform finite-horizon risk allowance attached to a public history.
The history argument is retained because the budget bounds the continuation
game from every public state; this particular bound is uniform in that state. -/
def hbudget {H : Type*} (epsilon : ℝ≥0∞) (n : ℕ) (_history : H) : ℝ≥0∞ :=
  (n : ℝ≥0∞) * epsilon

/-- A constant is an admissible measurable majorant for itself. On a
probability space its upper integral is therefore at most that constant. -/
theorem upperLIntegral_const_le
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (c : ℝ≥0∞)
    (hprob : μ Set.univ = 1) :
    upperLIntegral μ (fun _ : α => c) ≤ c := by
  classical
  unfold upperLIntegral
  simpa [hprob] using
    (iInf_le
      (fun g : {g : α → ℝ≥0∞ // Measurable g ∧
        ∀ x, (fun _ : α => c) x ≤ g x} => ∫⁻ x, g.1 x ∂μ)
      ⟨fun _ => c, measurable_const, fun _ => le_rfl⟩)

/-- If one fixed learner action is a probability law and every possible
pre-draw public witness has section-risk at most epsilon, then the stagewise
public-game value is at most n * epsilon from every public history.

This theorem is an upper-risk extension. It does not identify a nonmeasurable
terminal supremum with the ordinary expectation in the original paper. -/
theorem publicGlobalSupGameValue_le_hbudget
    {H X P : Type*}
    (draw : P → Measure Label)
    (next : H → X → P → Label → Label → H)
    (p0 : P) (epsilon : ℝ≥0∞)
    (hprob : draw p0 Set.univ = 1)
    (hsection : ∀ w, draw p0 (lowerSegment w) ≤ epsilon) :
    ∀ n h, publicGlobalSupGameValue draw next n h ≤ hbudget epsilon n h := by
  intro n
  induction n with
  | zero =>
      intro h
      simp [publicGlobalSupGameValue, hbudget]
  | succ n ih =>
      intro h
      change
        publicGlobalSupBellmanStep draw next
          (publicGlobalSupGameValue draw next n) h ≤
          ((n + 1 : ℕ) : ℝ≥0∞) * epsilon
      unfold publicGlobalSupBellmanStep
      apply iSup_le
      intro x
      refine le_trans (iInf_le _ p0) ?_
      apply iSup_le
      intro w
      have hcontinuation : ∀ y,
          publicGlobalSupGameValue draw next n
            (next h x p0 w y) ≤ (n : ℝ≥0∞) * epsilon := by
        intro y
        exact ih (next h x p0 w y)
      have hfuture :
          upperLIntegral (draw p0)
            (fun y => publicGlobalSupGameValue draw next n
              (next h x p0 w y)) ≤ (n : ℝ≥0∞) * epsilon := by
        calc
          upperLIntegral (draw p0)
              (fun y => publicGlobalSupGameValue draw next n
                (next h x p0 w y))
              ≤ upperLIntegral (draw p0)
                  (fun _ => (n : ℝ≥0∞) * epsilon) :=
                upperLIntegral_mono (draw p0) hcontinuation
          _ ≤ (n : ℝ≥0∞) * epsilon :=
                upperLIntegral_const_le (draw p0)
                  ((n : ℝ≥0∞) * epsilon) hprob
      calc
        draw p0 (lowerSegment w) +
            upperLIntegral (draw p0)
              (fun y => publicGlobalSupGameValue draw next n
                (next h x p0 w y))
            ≤ epsilon + (n : ℝ≥0∞) * epsilon :=
              add_le_add (hsection w) hfuture
        _ = ((n + 1 : ℕ) : ℝ≥0∞) * epsilon := by
          calc
            epsilon + (n : ℝ≥0∞) * epsilon
                = 1 * epsilon + (n : ℝ≥0∞) * epsilon := by simp
            _ = (1 + (n : ℝ≥0∞)) * epsilon := by rw [← add_mul]
            _ = ((n + 1 : ℕ) : ℝ≥0∞) * epsilon := by
              congr 1
              rw [Nat.cast_succ]
              exact add_comm (1 : ℝ≥0∞) (n : ℝ≥0∞)
        _ = hbudget epsilon (n + 1) h := rfl

/-- The exact sequential upper-integral game is dominated by the stagewise
value, so it inherits the same explicit history budget. -/
theorem publicGlobalSupOuterGameValue_le_hbudget
    {H X P : Type*}
    (draw : P → Measure Label)
    (next : H → X → P → Label → Label → H)
    (p0 : P) (epsilon : ℝ≥0∞)
    (hprob : draw p0 Set.univ = 1)
    (hsection : ∀ w, draw p0 (lowerSegment w) ≤ epsilon) :
    ∀ n h,
      publicGlobalSupOuterGameValue draw next n h ≤ hbudget epsilon n h := by
  intro n h
  exact le_trans
    (publicGlobalSupOuterGameValue_le_stagewiseGameValue draw next n h)
    (publicGlobalSupGameValue_le_hbudget
      draw next p0 epsilon hprob hsection n h)

end PublicSetting.GlobalSupSequentialRisk
