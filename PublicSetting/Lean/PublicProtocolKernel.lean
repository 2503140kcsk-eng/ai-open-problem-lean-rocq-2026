import PublicProtocol
import SequentialKernelMinimax

/-!
# Measurable stochastic semantics for the public protocol

This module connects the concrete information order in PublicProtocol.lean
to Mathlib's Markov-kernel and Ionescu--Tulcea path-space construction.

At each history h the order is:
  adversary chooses context;
  learner chooses an action/distribution;
  adversary chooses the visible witness using h, context and action;
  Nature samples from the action's probability kernel;
  the completed round is appended to the history.

The witness has no argument for the current sample.  The next transition
kernel is allowed to inspect the complete accumulated history, so this is
not a Markov-in-the-last-observation restriction.

A pathwise loss is admitted only with an explicit product-measurability
hypothesis.  This is essential: the omega-one sectionwise-risk results do
not imply that an unrestricted full-path error event is measurable.
-/

open MeasureTheory
open scoped ProbabilityTheory

namespace PublicSetting.ProtocolKernel

open PublicSetting.Protocol
open PublicSetting.SequentialKernelMinimax

universe u v w

abbrev History (X : Type u) (D : Type v) (Y : Type w) :=
  List (PublicRound X D Y)

/-- The current context is chosen from the completed public history. -/
def currentContext {X : Type u} {D : Type v} [MeasurableSpace D] {Y : Type w}
    (A : Adversary X D Y) (h : History X D Y) : X :=
  A.chooseContext h

/-- The learner's current randomized action can depend on its complete
observation history, including its own previously sampled predictions. -/
def currentPolicy {X : Type u} {D : Type v} [MeasurableSpace D] {Y : Type w}
    (A : Adversary X D Y) (L : Learner X D Y)
    (h : History X D Y) : D :=
  L.choosePolicy (learnerView h) (currentContext A h)

/-- The adversary's current visible witness depends on the completed
history, current context and current learner action, but not on the
current random draw. -/
def currentWitness {X : Type u} {D : Type v} [MeasurableSpace D] {Y : Type w}
    (A : Adversary X D Y) (L : Learner X D Y)
    (h : History X D Y) : Y :=
  A.chooseWitness h (currentContext A h) (currentPolicy A L h)

/-- Construct the completed round only after the sample y is drawn.
The witness and action fields are already fixed by the history. -/
def completedRound {X : Type u} {D : Type v} [MeasurableSpace D] {Y : Type w}
    (A : Adversary X D Y) (L : Learner X D Y)
    (h : History X D Y) (y : Y) : PublicRound X D Y :=
  ⟨currentContext A h, currentPolicy A L h, currentWitness A L h, y⟩

/-- The history update records the selected context, policy, pre-draw
witness, and only then the realized prediction. -/
def updateHistory {X : Type u} {D : Type v} [MeasurableSpace D] {Y : Type w}
    (A : Adversary X D Y) (L : Learner X D Y)
    (p : History X D Y × Y) : History X D Y :=
  p.1 ++ [completedRound A L p.1 p.2]

@[simp]
theorem completedRound_context {X : Type u} {D : Type v} [MeasurableSpace D] {Y : Type w}
    (A : Adversary X D Y) (L : Learner X D Y)
    (h : History X D Y) (y : Y) :
    (completedRound A L h y).context = A.chooseContext h := rfl

@[simp]
theorem completedRound_policy {X : Type u} {D : Type v} [MeasurableSpace D] {Y : Type w}
    (A : Adversary X D Y) (L : Learner X D Y)
    (h : History X D Y) (y : Y) :
    (completedRound A L h y).policy =
      L.choosePolicy (learnerView h) (A.chooseContext h) := rfl

@[simp]
theorem completedRound_witness {X : Type u} {D : Type v} [MeasurableSpace D] {Y : Type w}
    (A : Adversary X D Y) (L : Learner X D Y)
    (h : History X D Y) (y : Y) :
    (completedRound A L h y).witness =
      A.chooseWitness h (A.chooseContext h)
        (L.choosePolicy (learnerView h) (A.chooseContext h)) := rfl

@[simp]
theorem completedRound_prediction {X : Type u} {D : Type v} [MeasurableSpace D] {Y : Type w}
    (A : Adversary X D Y) (L : Learner X D Y)
    (h : History X D Y) (y : Y) :
    (completedRound A L h y).prediction = y := rfl

/-- The draw law is a genuine Markov kernel from learner actions/distributions
to labels.  Supplying this kernel is the precise probabilistic semantics of
the learner's randomized action. -/
noncomputable def drawAfterPolicy
    {X : Type u} {D : Type v} [MeasurableSpace D] {Y : Type w}
    [MeasurableSpace (History X D Y)]
    [MeasurableSpace Y]
    (A : Adversary X D Y) (L : Learner X D Y)
    (draw : ProbabilityTheory.Kernel D Y)
    (hpolicy : Measurable (currentPolicy A L)) :
    ProbabilityTheory.Kernel (History X D Y) Y :=
  draw ∘ₖ ProbabilityTheory.Kernel.deterministic
    (currentPolicy A L) hpolicy

theorem drawAfterPolicy_isMarkov
    {X : Type u} {D : Type v} [MeasurableSpace D] {Y : Type w}
    [MeasurableSpace (History X D Y)]
    [MeasurableSpace Y]
    (A : Adversary X D Y) (L : Learner X D Y)
    (draw : ProbabilityTheory.Kernel D Y)
    [ProbabilityTheory.IsMarkovKernel draw]
    (hpolicy : Measurable (currentPolicy A L)) :
    ProbabilityTheory.IsMarkovKernel (drawAfterPolicy A L draw hpolicy) := by
  dsimp [drawAfterPolicy]
  infer_instance

/-- Jointly retain the old history and draw the next label.  Copy followed
by parallel composition is the kernel form of (h, y), with y sampled from
the action selected at h. -/
noncomputable def jointHistoryDrawKernel
    {X : Type u} {D : Type v} [MeasurableSpace D] {Y : Type w}
    [MeasurableSpace (History X D Y)]
    [MeasurableSpace Y]
    (A : Adversary X D Y) (L : Learner X D Y)
    (draw : ProbabilityTheory.Kernel D Y)
    (hpolicy : Measurable (currentPolicy A L)) :
    ProbabilityTheory.Kernel (History X D Y) (History X D Y × Y) := by
  letI : ProbabilityTheory.IsMarkovKernel (drawAfterPolicy A L draw hpolicy) :=
    drawAfterPolicy_isMarkov A L draw hpolicy
  exact (ProbabilityTheory.Kernel.id ∥ₖ
    drawAfterPolicy A L draw hpolicy) ∘ₖ
      ProbabilityTheory.Kernel.copy (History X D Y)

theorem jointHistoryDrawKernel_isMarkov
    {X : Type u} {D : Type v} [MeasurableSpace D] {Y : Type w}
    [MeasurableSpace (History X D Y)]
    [MeasurableSpace Y]
    (A : Adversary X D Y) (L : Learner X D Y)
    (draw : ProbabilityTheory.Kernel D Y)
    [ProbabilityTheory.IsMarkovKernel draw]
    (hpolicy : Measurable (currentPolicy A L)) :
    ProbabilityTheory.IsMarkovKernel
      (jointHistoryDrawKernel A L draw hpolicy) := by
  letI : ProbabilityTheory.IsMarkovKernel (drawAfterPolicy A L draw hpolicy) :=
    drawAfterPolicy_isMarkov A L draw hpolicy
  dsimp [jointHistoryDrawKernel]
  infer_instance

/-- One complete protocol transition: sample according to the learner's
selected action, then append the resulting round to the old history. -/
noncomputable def publicProtocolTransition
    {X : Type u} {D : Type v} [MeasurableSpace D] {Y : Type w}
    [MeasurableSpace (History X D Y)]
    [MeasurableSpace Y]
    (A : Adversary X D Y) (L : Learner X D Y)
    (draw : ProbabilityTheory.Kernel D Y)
    (hpolicy : Measurable (currentPolicy A L))
    (_hupdate : Measurable (updateHistory A L)) :
    ProbabilityTheory.Kernel (History X D Y) (History X D Y) :=
  ProbabilityTheory.Kernel.map
    (jointHistoryDrawKernel A L draw hpolicy)
    (updateHistory A L)

theorem publicProtocolTransition_isMarkov
    {X : Type u} {D : Type v} [MeasurableSpace D] {Y : Type w}
    [MeasurableSpace (History X D Y)]
    [MeasurableSpace Y]
    (A : Adversary X D Y) (L : Learner X D Y)
    (draw : ProbabilityTheory.Kernel D Y)
    [ProbabilityTheory.IsMarkovKernel draw]
    (hpolicy : Measurable (currentPolicy A L))
    (hupdate : Measurable (updateHistory A L)) :
    ProbabilityTheory.IsMarkovKernel
      (publicProtocolTransition A L draw hpolicy hupdate) := by
  letI : ProbabilityTheory.IsMarkovKernel (jointHistoryDrawKernel A L draw hpolicy) :=
    jointHistoryDrawKernel_isMarkov A L draw hpolicy
  exact ProbabilityTheory.Kernel.IsMarkovKernel.map
    (jointHistoryDrawKernel A L draw hpolicy) hupdate

/-- Lift the one-step public transition to a kernel which reads the last
history in the complete finite historyPrefix.  Since each history stores all past
rounds, arbitrary history dependence is retained. -/
noncomputable def publicProtocolPrefixKernel
    {X : Type u} {D : Type v} [MeasurableSpace D] {Y : Type w}
    [MeasurableSpace (History X D Y)]
    [MeasurableSpace Y]
    (A : Adversary X D Y) (L : Learner X D Y)
    (draw : ProbabilityTheory.Kernel D Y)
    (hpolicy : Measurable (currentPolicy A L))
    (hupdate : Measurable (updateHistory A L))
    (n : ℕ) :
    ProbabilityTheory.Kernel
      (Π i : Finset.Iic n, History X D Y) (History X D Y) := by
  letI : ProbabilityTheory.IsMarkovKernel
      (publicProtocolTransition A L draw hpolicy hupdate) :=
    publicProtocolTransition_isMarkov A L draw hpolicy hupdate
  exact publicProtocolTransition A L draw hpolicy hupdate ∘ₖ
    ProbabilityTheory.Kernel.deterministic
      (fun historyPrefix : Π _i : Finset.Iic n, History X D Y =>
        historyPrefix ⟨n, by simp⟩)
      (by fun_prop)

theorem publicProtocolPrefixKernel_isMarkov
    {X : Type u} {D : Type v} [MeasurableSpace D] {Y : Type w}
    [MeasurableSpace (History X D Y)]
    [MeasurableSpace Y]
    (A : Adversary X D Y) (L : Learner X D Y)
    (draw : ProbabilityTheory.Kernel D Y)
    [ProbabilityTheory.IsMarkovKernel draw]
    (hpolicy : Measurable (currentPolicy A L))
    (hupdate : Measurable (updateHistory A L))
    (n : ℕ) :
    ProbabilityTheory.IsMarkovKernel
      (publicProtocolPrefixKernel A L draw hpolicy hupdate n) := by
  letI : ProbabilityTheory.IsMarkovKernel
      (publicProtocolTransition A L draw hpolicy hupdate) :=
    publicProtocolTransition_isMarkov A L draw hpolicy hupdate
  dsimp [publicProtocolPrefixKernel]
  infer_instance

/-- The complete law of all successive public histories, from the empty
history.  Mathlib's Ionescu--Tulcea theorem joins all rounds into one path
measure rather than treating the rounds as unrelated probability spaces. -/
noncomputable def publicProtocolTrajectoryMeasure
    {X : Type u} {D : Type v} [MeasurableSpace D] {Y : Type w}
    [MeasurableSpace (History X D Y)]
    [MeasurableSpace Y]
    (A : Adversary X D Y) (L : Learner X D Y)
    (draw : ProbabilityTheory.Kernel D Y)
    [ProbabilityTheory.IsMarkovKernel draw]
    (hpolicy : Measurable (currentPolicy A L))
    (hupdate : Measurable (updateHistory A L)) :
    Measure (Π n : ℕ, History X D Y) := by
  let κ : (n : ℕ) → ProbabilityTheory.Kernel
      (Π i : Finset.Iic n, History X D Y) History :=
    fun n => publicProtocolPrefixKernel A L draw hpolicy hupdate n
  letI : ∀ n, ProbabilityTheory.IsMarkovKernel (κ n) :=
    fun n => publicProtocolPrefixKernel_isMarkov A L draw hpolicy hupdate n
  exact ProbabilityTheory.Kernel.traj κ 0 (fun _ => ([] : History X D Y))

theorem publicProtocolTrajectoryMeasure_isProbability
    {X : Type u} {D : Type v} [MeasurableSpace D] {Y : Type w}
    [MeasurableSpace (History X D Y)]
    [MeasurableSpace Y]
    (A : Adversary X D Y) (L : Learner X D Y)
    (draw : ProbabilityTheory.Kernel D Y)
    [ProbabilityTheory.IsMarkovKernel draw]
    (hpolicy : Measurable (currentPolicy A L))
    (hupdate : Measurable (updateHistory A L)) :
    IsProbabilityMeasure
      (publicProtocolTrajectoryMeasure A L draw hpolicy hupdate) := by
  dsimp [publicProtocolTrajectoryMeasure]
  let κ : (n : ℕ) → ProbabilityTheory.Kernel
      (Π i : Finset.Iic n, History X D Y) History :=
    fun n => publicProtocolPrefixKernel A L draw hpolicy hupdate n
  letI : ∀ n, ProbabilityTheory.IsMarkovKernel (κ n) :=
    fun n => publicProtocolPrefixKernel_isMarkov A L draw hpolicy hupdate n
  infer_instance

/-- The exact tower property for the public protocol: for any integrable
full-path reward, conditioning on the public histories through round b
equals integration using the continuation trajectory kernel. -/
theorem publicProtocol_trajectory_tower
    {X : Type u} {D : Type v} [MeasurableSpace D] {Y : Type w}
    [MeasurableSpace (History X D Y)]
    [MeasurableSpace Y]
    (A : Adversary X D Y) (L : Learner X D Y)
    (draw : ProbabilityTheory.Kernel D Y)
    [ProbabilityTheory.IsMarkovKernel draw]
    (hpolicy : Measurable (currentPolicy A L))
    (hupdate : Measurable (updateHistory A L))
    {a b : ℕ} (hab : a ≤ b)
    (historyPrefix : Π i : Finset.Iic a, History X D Y)
    (reward : (Π n : ℕ, History X D Y) → ℝ)
    (hreward : Integrable reward
      (ProbabilityTheory.Kernel.traj
        (publicProtocolPrefixKernel A L draw hpolicy hupdate) a historyPrefix)) :
    (ProbabilityTheory.Kernel.traj
      (publicProtocolPrefixKernel A L draw hpolicy hupdate) a historyPrefix)
        [reward | MeasureTheory.Filtration.piLE b] =ᵐ[
          ProbabilityTheory.Kernel.traj
            (publicProtocolPrefixKernel A L draw hpolicy hupdate) a historyPrefix]
      fun path ↦ ∫ future, reward future ∂
        ProbabilityTheory.Kernel.traj
          (publicProtocolPrefixKernel A L draw hpolicy hupdate) b
          (Preorder.frestrictLe b path) := by
  exact trajectory_tower
    (publicProtocolPrefixKernel A L draw hpolicy hupdate)
    hab historyPrefix reward hreward

/-- A measurable one-round loss on a pair of consecutive public histories.
For a concrete partial-feedback game this is the indicator that the newly
sampled prediction is outside the hidden acceptable set determined by the
single globally realizable target family. -/
def roundLoss
    {X : Type u} {D : Type v} [MeasurableSpace D] {Y : Type w}
    (loss : History X D Y → History X D Y → ℝ)
    (oldHistory newHistory : History X D Y) : ℝ :=
  loss oldHistory newHistory

/-- Total loss over the first T rounds along one complete public-history path. -/
def finitePathLoss
    {X : Type u} {D : Type v} [MeasurableSpace D] {Y : Type w}
    (T : ℕ) (loss : History X D Y → History X D Y → ℝ)
    (path : Π n, History X D Y) : ℝ :=
  ∑ t : Fin T, roundLoss loss (path t.1) (path (t.1 + 1))

theorem finitePathLoss_measurable
    {X : Type u} {D : Type v} [MeasurableSpace D] {Y : Type w}
    [MeasurableSpace (History X D Y)]
    (T : ℕ) (loss : History X D Y → History X D Y → ℝ)
    (hloss : Measurable (fun p : History X D Y × History X D Y =>
      loss p.1 p.2)) :
    Measurable (finitePathLoss T loss) := by
  unfold finitePathLoss roundLoss
  fun_prop

/-- Tower property specialized to the cumulative measurable round loss.
Integrability is stated explicitly: it follows, for example, for a bounded
[0,1]-valued loss under the trajectory probability measure. -/
theorem finitePathLoss_tower
    {X : Type u} {D : Type v} [MeasurableSpace D] {Y : Type w}
    [MeasurableSpace (History X D Y)]
    [MeasurableSpace Y]
    (A : Adversary X D Y) (L : Learner X D Y)
    (draw : ProbabilityTheory.Kernel D Y)
    [ProbabilityTheory.IsMarkovKernel draw]
    (hpolicy : Measurable (currentPolicy A L))
    (hupdate : Measurable (updateHistory A L))
    (T : ℕ) (loss : History X D Y → History X D Y → ℝ)
    (hloss : Measurable (fun p : History X D Y × History X D Y =>
      loss p.1 p.2))
    {a b : ℕ} (hab : a ≤ b)
    (historyPrefix : Π i : Finset.Iic a, History X D Y)
    (hreward : Integrable (finitePathLoss T loss)
      (ProbabilityTheory.Kernel.traj
        (publicProtocolPrefixKernel A L draw hpolicy hupdate) a historyPrefix)) :
    (ProbabilityTheory.Kernel.traj
      (publicProtocolPrefixKernel A L draw hpolicy hupdate) a historyPrefix)
        [finitePathLoss T loss | MeasureTheory.Filtration.piLE b] =ᵐ[
          ProbabilityTheory.Kernel.traj
            (publicProtocolPrefixKernel A L draw hpolicy hupdate) a historyPrefix]
      fun path ↦ ∫ future, finitePathLoss T loss future ∂
        ProbabilityTheory.Kernel.traj
          (publicProtocolPrefixKernel A L draw hpolicy hupdate) b
          (Preorder.frestrictLe b path) := by
  exact publicProtocol_trajectory_tower
    A L draw hpolicy hupdate hab historyPrefix (finitePathLoss T loss) hreward

end PublicSetting.ProtocolKernel
