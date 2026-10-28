From Stdlib Require Import Arith Lia List.
Import ListNotations.

(* Formalization of the information order in Section 5.3 of
   Shao, Fang, Lin, and Tao, Partial Feedback Online Learning,
   arXiv:2601.21462v3.

   A current visible witness is chosen from the past public trace, current
   context, and current distribution/action. Its type does not expose the
   current sampled prediction. A single terminal target subfamily F must
   explain every round. The lower-bound example below is for bounded-support
   actions only and does not claim to solve the paper's open separation question. *)

Section PublicProtocol.

  Context {X D Y Omega : Type}.

  (* The learner knows its own earlier draws, but not the hidden acceptable
     sets or whether any of its predictions was correct. *)
  Record Observation := {
    observation_context : X;
    observation_policy : D;
    observation_witness : Y;
    observation_prediction : Y
  }.

  Record PublicRound := {
    round_context : X;
    round_policy : D;
    round_witness : Y;
    round_prediction : Y
  }.

  Definition observation_of (r : PublicRound) : Observation :=
    {| observation_context := round_context r;
       observation_policy := round_policy r;
       observation_witness := round_witness r;
       observation_prediction := round_prediction r |}.

  Definition learner_view (history : list PublicRound) : list Observation :=
    map observation_of history.

  Record Learner := {
    choose_policy : list Observation -> X -> D
  }.

  (* Public adversary observations include prior realized predictions, but not
     the current prediction sample when selecting the current witness. *)
  Record Adversary := {
    choose_context : list PublicRound -> X;
    choose_witness : list PublicRound -> X -> D -> Y
  }.

  Definition play_round
      (adversary : Adversary)
      (learner : Learner)
      (draw : D -> Omega -> Y)
      (history : list PublicRound)
      (omega : Omega) : list PublicRound :=
    let x := choose_context adversary history in
    let pi := choose_policy learner (learner_view history) x in
    let visible := choose_witness adversary history x pi in
    let prediction := draw pi omega in
    history ++
      [{| round_context := x;
          round_policy := pi;
          round_witness := visible;
          round_prediction := prediction |}].

  Lemma learner_view_length (history : list PublicRound) :
    length (learner_view history) = length history.
  Proof.
    unfold learner_view. apply length_map.
  Qed.

  Lemma play_round_length
      (adversary : Adversary)
      (learner : Learner)
      (draw : D -> Omega -> Y)
      (history : list PublicRound)
      (omega : Omega) :
    length (play_round adversary learner draw history omega) = length history + 1.
  Proof.
    unfold play_round. simpl. rewrite length_app. simpl. lia.
  Qed.

  Definition AcceptedLabels
      (F : (X -> Y) -> Prop) (x : X) (y : Y) : Prop :=
    exists f, F f /\ f x = y.

  (* One F is used for every row: this is global set-realizability. *)
  Definition GloballyRealizable
      (H F : (X -> Y) -> Prop) (trace : list PublicRound) : Prop :=
    (forall f, F f -> H f) /\
    (forall r, In r trace -> AcceptedLabels F (round_context r) (round_witness r)).

  Lemma target_member_acceptable
      (F : (X -> Y) -> Prop) (f : X -> Y) (hF : F f) (x : X) :
    AcceptedLabels F x (f x).
  Proof.
    exists f. split; [exact hF | reflexivity].
  Qed.

End PublicProtocol.

Definition ComplementFamily (prediction : nat -> nat) (f : nat -> nat) : Prop :=
  forall t, f t <> prediction t.

Definition ComplementAccepts (prediction : nat -> nat) (t y : nat) : Prop :=
  exists f, ComplementFamily prediction f /\ f t = y.

Lemma complement_family_accepts_iff (prediction : nat -> nat) (t y : nat) :
  ComplementAccepts prediction t y <-> y <> prediction t.
Proof.
  unfold ComplementAccepts, ComplementFamily.
  split.
  - intros [f [Hf Hft]].
    subst y. apply Hf.
  - intro Hy.
    exists (fun s => if Nat.eq_dec s t then y else prediction s + 1).
    split.
    + intros s. destruct (Nat.eq_dec s t) as [Heq | Hneq].
      * subst s. exact Hy.
      * assert (Hne : prediction s + 1 <> prediction s) by lia.
        simpl. exact Hne.
    + simpl. destruct (Nat.eq_dec t t); congruence.
Qed.

Lemma complement_family_nonempty (prediction : nat -> nat) :
  exists f : nat -> nat, ComplementFamily prediction f.
Proof.
  exists (fun t => prediction t + 1).
  intros t. unfold ComplementFamily. lia.
Qed.

(* A bounded-support sampler: every possible sample is below an action-specific
   finite bound. This captures finite-support action distributions on nat; it is
   explicitly not an encoding of all countably supported probability measures. *)
Record BoundedSupportSampler (D Omega : Type) := {
  sampler_bound : D -> nat;
  sampler_draw : D -> Omega -> nat;
  sampler_draw_lt_bound : forall d omega,
      sampler_draw d omega < sampler_bound d
}.

Arguments sampler_bound {D Omega} _ _.
Arguments sampler_draw {D Omega} _ _ _.
Arguments sampler_draw_lt_bound {D Omega} _ _ _.

Definition stream_prediction {D Omega : Type}
    (sampler : BoundedSupportSampler D Omega)
    (actions : nat -> D) (random_states : nat -> Omega) : nat -> nat :=
  fun t => sampler_draw sampler (actions t) (random_states t).

Definition stream_witness {D Omega : Type}
    (sampler : BoundedSupportSampler D Omega)
    (actions : nat -> D) : nat -> nat :=
  fun t => sampler_bound sampler (actions t).

Lemma stream_witness_ne_prediction {D Omega : Type}
    (sampler : BoundedSupportSampler D Omega)
    (actions : nat -> D) (random_states : nat -> Omega) (t : nat) :
  stream_witness sampler actions t <>
    stream_prediction sampler actions random_states t.
Proof.
  unfold stream_witness, stream_prediction.
  pose proof (sampler_draw_lt_bound sampler (actions t) (random_states t)).
  lia.
Qed.

(* One terminal target family F is fixed from the realized sampled path. At each
   coordinate t its acceptable labels are exactly those unequal to that sample. *)
Definition bounded_support_target {D Omega : Type}
    (sampler : BoundedSupportSampler D Omega)
    (actions : nat -> D) (random_states : nat -> Omega)
    (f : nat -> nat) : Prop :=
  ComplementFamily (stream_prediction sampler actions random_states) f.

Lemma bounded_support_visible_in_global_target {D Omega : Type}
    (sampler : BoundedSupportSampler D Omega)
    (actions : nat -> D) (random_states : nat -> Omega) :
  bounded_support_target sampler actions random_states
    (stream_witness sampler actions).
Proof.
  unfold bounded_support_target, ComplementFamily.
  intros t.
  apply stream_witness_ne_prediction.
Qed.

Fixpoint ProtocolTotalLoss (T : nat)
    (excluded prediction : nat -> nat) : nat :=
  match T with
  | O => 0
  | S n =>
      ProtocolTotalLoss n excluded prediction +
        (if Nat.eq_dec (prediction n) (excluded n) then 1 else 0)
  end.

Lemma bounded_support_prediction_loss {D Omega : Type}
    (T : nat)
    (sampler : BoundedSupportSampler D Omega)
    (actions : nat -> D) (random_states : nat -> Omega) :
  ProtocolTotalLoss T
    (stream_prediction sampler actions random_states)
    (stream_prediction sampler actions random_states) = T.
Proof.
  induction T as [|T IH].
  - reflexivity.
  - change
      (ProtocolTotalLoss T
         (stream_prediction sampler actions random_states)
         (stream_prediction sampler actions random_states) +
       (if Nat.eq_dec
          (stream_prediction sampler actions random_states T)
          (stream_prediction sampler actions random_states T)
        then 1 else 0) = S T).
    rewrite IH.
    destruct (Nat.eq_dec
      (stream_prediction sampler actions random_states T)
      (stream_prediction sampler actions random_states T)) as [_ | Hneq].
    + lia.
    + contradiction.
Qed.

Lemma bounded_support_comparator_loss_zero {D Omega : Type}
    (T : nat)
    (sampler : BoundedSupportSampler D Omega)
    (actions : nat -> D) (random_states : nat -> Omega) :
  ProtocolTotalLoss T
    (stream_prediction sampler actions random_states)
    (stream_witness sampler actions) = 0.
Proof.
  induction T as [|T IH].
  - reflexivity.
  - change
      (ProtocolTotalLoss T
         (stream_prediction sampler actions random_states)
         (stream_witness sampler actions) +
       (if Nat.eq_dec
          (stream_witness sampler actions T)
          (stream_prediction sampler actions random_states T)
        then 1 else 0) = 0).
    rewrite IH.
    destruct (Nat.eq_dec
      (stream_witness sampler actions T)
      (stream_prediction sampler actions random_states T)) as [Heq | Hneq].
    + exfalso.
      exact (stream_witness_ne_prediction sampler actions random_states T Heq).
    + reflexivity.
Qed.

Lemma bounded_support_pathwise_regret_gap {D Omega : Type}
    (T : nat)
    (sampler : BoundedSupportSampler D Omega)
    (actions : nat -> D) (random_states : nat -> Omega) :
  ProtocolTotalLoss T
    (stream_prediction sampler actions random_states)
    (stream_prediction sampler actions random_states)
  -
  ProtocolTotalLoss T
    (stream_prediction sampler actions random_states)
    (stream_witness sampler actions) = T.
Proof.
  rewrite (bounded_support_prediction_loss T sampler actions random_states).
  rewrite (bounded_support_comparator_loss_zero T sampler actions random_states).
  lia.
Qed.

(* General terminal target: exclude the realized prediction when it differs
   from the visible witness; on a collision, exclude witness+1 instead. *)
Definition terminal_exclusion (prediction visible : nat -> nat) (t : nat) : nat :=
  if Nat.eq_dec (prediction t) (visible t)
  then visible t + 1 else prediction t.

Lemma visible_ne_terminal_exclusion
    (prediction visible : nat -> nat) (t : nat) :
  visible t <> terminal_exclusion prediction visible t.
Proof.
  unfold terminal_exclusion.
  destruct (Nat.eq_dec (prediction t) (visible t)) as [Heq | Hneq].
  - lia.
  - congruence.
Qed.

Lemma prediction_eq_terminal_exclusion_iff
    (prediction visible : nat -> nat) (t : nat) :
  prediction t = terminal_exclusion prediction visible t <->
  prediction t <> visible t.
Proof.
  unfold terminal_exclusion.
  destruct (Nat.eq_dec (prediction t) (visible t)) as [Heq | Hneq].
  - split; [lia | congruence].
  - split.
    + intro Hsame. exact Hneq.
    + intro Hneq'. reflexivity.
Qed.

Definition TerminalFamily (prediction visible : nat -> nat) (f : nat -> nat) : Prop :=
  ComplementFamily (terminal_exclusion prediction visible) f.

Definition TerminalAccepts
    (prediction visible : nat -> nat) (t y : nat) : Prop :=
  ComplementAccepts (terminal_exclusion prediction visible) t y.

Lemma terminal_global_family_accepts_visible
    (prediction visible : nat -> nat) :
  (exists f, TerminalFamily prediction visible f) /\
  (forall t, TerminalAccepts prediction visible t (visible t)).
Proof.
  split.
  - apply complement_family_nonempty.
  - intros t.
    apply (proj2 (complement_family_accepts_iff
      (terminal_exclusion prediction visible) t (visible t))).
    apply visible_ne_terminal_exclusion.
Qed.

Fixpoint MismatchLoss (T : nat)
    (prediction visible : nat -> nat) : nat :=
  match T with
  | O => 0
  | S n =>
      MismatchLoss n prediction visible +
        (if Nat.eq_dec (prediction n) (visible n) then 0 else 1)
  end.

Lemma terminal_pathwise_loss
    (T : nat) (prediction visible : nat -> nat) :
  ProtocolTotalLoss T (terminal_exclusion prediction visible) prediction =
    MismatchLoss T prediction visible.
Proof.
  induction T as [|T IH].
  - reflexivity.
  - cbn [ProtocolTotalLoss MismatchLoss].
    rewrite IH.
    assert (Hstep :
      (if Nat.eq_dec (prediction T) (terminal_exclusion prediction visible T)
       then 1 else 0) =
      (if Nat.eq_dec (prediction T) (visible T) then 0 else 1)).
    {
      unfold terminal_exclusion.
      destruct (Nat.eq_dec (prediction T) (visible T)) as [Heq | Hneq].
      - destruct (Nat.eq_dec (prediction T) (visible T + 1)); lia.
      - destruct (Nat.eq_dec (prediction T) (prediction T)); [reflexivity | contradiction].
    }
    rewrite Hstep.
    reflexivity.
Qed.

Lemma terminal_comparator_loss_zero
    (T : nat) (prediction visible : nat -> nat) :
  ProtocolTotalLoss T (terminal_exclusion prediction visible) visible = 0.
Proof.
  induction T as [|T IH].
  - reflexivity.
  - cbn [ProtocolTotalLoss].
    rewrite IH.
    destruct (Nat.eq_dec
      (visible T) (terminal_exclusion prediction visible T)) as [Heq | Hneq].
    + exfalso. exact (visible_ne_terminal_exclusion prediction visible T Heq).
    + reflexivity.
Qed.

Lemma terminal_pathwise_regret_gap
    (T : nat) (prediction visible : nat -> nat) :
  ProtocolTotalLoss T (terminal_exclusion prediction visible) prediction -
  ProtocolTotalLoss T (terminal_exclusion prediction visible) visible =
    MismatchLoss T prediction visible.
Proof.
  rewrite (terminal_pathwise_loss T prediction visible).
  rewrite (terminal_comparator_loss_zero T prediction visible).
  lia.
Qed.

(* After the draw path is known, one nonempty global target family
   F = {f | forall t, f(t) <> prediction(t)} realizes each witness and
   excludes every sampled prediction. Witnesses were chosen pre-draw via the
   support bound. This gives a linear lower bound for this example/action class,
   not the randomized upper bound requested in the still-open separation problem. *)
Theorem bounded_support_public_attack {D Omega : Type}
    (T : nat)
    (sampler : BoundedSupportSampler D Omega)
    (actions : nat -> D) (random_states : nat -> Omega) :
  exists F : (nat -> nat) -> Prop,
    (exists f, F f) /\
    forall t, t < T ->
      ComplementAccepts (stream_prediction sampler actions random_states) t
        (stream_witness sampler actions t) /\
      ~ ComplementAccepts (stream_prediction sampler actions random_states) t
        (stream_prediction sampler actions random_states t).
Proof.
  set (prediction := stream_prediction sampler actions random_states).
  set (visible := stream_witness sampler actions).
  exists (ComplementFamily prediction).
  split.
  - apply complement_family_nonempty.
  - intros t Ht. split.
    + apply (proj2 (complement_family_accepts_iff prediction t (visible t))).
      unfold visible, prediction.
      apply stream_witness_ne_prediction.
    + intro Haccepted.
      apply (proj1 (complement_family_accepts_iff prediction t (prediction t))) in Haccepted.
      contradiction.
Qed.


(* For a fixed subfamily of constant hypotheses, the projected acceptable
   labels are independent of the instance. *)
Definition ConstantFamilyAccepts (F : nat -> Prop) (_context label : nat) : Prop :=
  F label.

Lemma constant_family_accepts_independent
    (F : nat -> Prop) (x x' y : nat) :
  ConstantFamilyAccepts F x y <-> ConstantFamilyAccepts F x' y.
Proof.
  reflexivity.
Qed.

(* This formally records why the standard set-valued-feedback separation
   does not transfer verbatim: one global family of constant hypotheses
   cannot induce different co-singleton exclusions at different rounds. *)
Lemma constant_hypothesis_complement_exclusion_is_fixed
    (excluded : nat -> nat) (F : nat -> Prop)
    (H : forall t y, ConstantFamilyAccepts F t y <-> y <> excluded t) :
  forall t s, excluded t = excluded s.
Proof.
  intros t s.
  assert (Hnot : ~ ConstantFamilyAccepts F t (excluded t)).
  {
    intro HF.
    apply (proj1 (H t (excluded t))) in HF.
    contradiction.
  }
  destruct (Nat.eq_dec (excluded t) (excluded s)) as [Heq | Hneq].
  - exact Heq.
  - exfalso.
    apply Hnot.
    apply (proj2 (H s (excluded t))).
    exact Hneq.
Qed.


(* A proposition stating the requested asymptotic separation is only a
   specification here; no theorem in this file proves the randomized upper bound. *)
Definition ProtocolIsSublinear (r : nat -> nat) : Prop :=
  forall a b : nat,
    0 < a -> 0 < b ->
    exists N : nat, forall T : nat, N <= T -> b * r T < a * T.

Definition ProtocolIsLinear (r : nat -> nat) : Prop :=
  exists a b N : nat,
    0 < a /\ 0 < b /\
    forall T : nat, N <= T -> a * T <= b * r T.

Definition PublicRandomizedDeterministicSeparation
    (DeterministicLearner : Type)
    (randomizedRegret : nat -> nat)
    (deterministicRegret : DeterministicLearner -> nat -> nat) : Prop :=
  ProtocolIsSublinear randomizedRegret /\
  forall learner : DeterministicLearner, ProtocolIsLinear (deterministicRegret learner).
