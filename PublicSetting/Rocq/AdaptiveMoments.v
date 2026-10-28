From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.

Module AdaptiveMoments.

Fixpoint event_count (samples : list nat) (event : nat -> bool) : nat :=
  match samples with
  | [] => 0
  | x :: xs => (if event x then 1 else 0) + event_count xs event
  end.

Fixpoint total_value (samples : list nat) (value : nat -> nat) : nat :=
  match samples with
  | [] => 0
  | x :: xs => value x + total_value xs value
  end.

Fixpoint factorial (n : nat) : nat :=
  match n with
  | 0 => 1
  | S k => S k * factorial k
  end.

Fixpoint outcomes (n : nat) : list nat :=
  match n with
  | 0 => [0]
  | S k => S k :: outcomes k
  end.

Definition hit_at (target : nat -> list nat -> nat)
    (history : list nat) (draw : nat) : bool :=
  Nat.eqb draw (target (length history) history).

Lemma outcomes_length : forall n, length (outcomes n) = S n.
Proof.
  induction n as [|n IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma outcomes_mem_le : forall n x, In x (outcomes n) -> x <= n.
Proof.
  induction n as [|n IH]; intros x Hin; simpl in Hin.
  - destruct Hin as [Hx | Hfalse].
    + subst x. lia.
    + contradiction.
  - destruct Hin as [Hx | Hin].
    + subst x. lia.
    + specialize (IH x Hin). lia.
Qed.

Lemma outcomes_nodup : forall n, NoDup (outcomes n).
Proof.
  induction n as [|n IH]; simpl.
  - constructor; [simpl; tauto | constructor].
  - constructor.
    + intro Hin.
      pose proof (outcomes_mem_le n (S n) Hin). lia.
    + exact IH.
Qed.

Lemma event_count_false_of_all_false :
  forall (samples : list nat) (event : nat -> bool),
    (forall x, In x samples -> event x = false) ->
    event_count samples event = 0.
Proof.
  induction samples as [|x xs IH]; intros event Hfalse; simpl.
  - reflexivity.
  - rewrite (Hfalse x (or_introl eq_refl)).
    assert (Htail : forall y, In y xs -> event y = false).
    { intros y Hy. apply Hfalse. right. exact Hy. }
    rewrite (IH event Htail). reflexivity.
Qed.

Lemma event_count_eq_le_one :
  forall (xs : list nat), NoDup xs ->
    forall target, event_count xs (fun x => Nat.eqb x target) <= 1.
Proof.
  induction xs as [|x xs IH]; intros Hnodup target; simpl.
  - lia.
  - inversion Hnodup as [|x' xs' Hnotin Htail]; subst.
    destruct (Nat.eqb x target) eqn:Hx.
    + apply Nat.eqb_eq in Hx. subst target.
      assert (Hfalse : forall z, In z xs -> Nat.eqb z x = false).
      { intros z Hz. apply Nat.eqb_neq. intro Heq. subst z. contradiction. }
      rewrite (event_count_false_of_all_false xs (fun z => Nat.eqb z x) Hfalse).
      simpl. lia.
    + simpl. specialize (IH Htail target). lia.
Qed.

Lemma event_count_outcomes_eq_le_one :
  forall n target,
    event_count (outcomes n) (fun x => Nat.eqb x target) <= 1.
Proof.
  intros n target.
  apply event_count_eq_le_one.
  apply outcomes_nodup.
Qed.

Lemma total_value_mono :
  forall (samples : list nat) (f g : nat -> nat),
    (forall x, f x <= g x) ->
    total_value samples f <= total_value samples g.
Proof.
  induction samples as [|x xs IH]; intros f g Hpoint; simpl.
  - lia.
  - apply Nat.add_le_mono.
    + apply Hpoint.
    + apply IH. exact Hpoint.
Qed.

Lemma total_value_const :
  forall (samples : list nat) (K : nat),
    total_value samples (fun _ => K) = K * length samples.
Proof.
  induction samples as [|x xs IH]; intros K; simpl.
  - rewrite Nat.mul_0_r. reflexivity.
  - rewrite (IH K). rewrite Nat.mul_succ_r. lia.
Qed.

Lemma total_value_indicator :
  forall (samples : list nat) (T : nat) (bad : nat -> bool),
    total_value samples (fun x => if bad x then T else 0) =
      T * event_count samples bad.
Proof.
  induction samples as [|x xs IH]; intros T bad; simpl.
  - rewrite Nat.mul_0_r. reflexivity.
  - destruct (bad x) eqn:Hbad; simpl; rewrite (IH T bad); lia.
Qed.

Lemma total_value_add :
  forall (samples : list nat) (f g : nat -> nat),
    total_value samples (fun x => f x + g x) =
      total_value samples f + total_value samples g.
Proof.
  induction samples as [|x xs IH]; intros f g; simpl.
  - reflexivity.
  - rewrite (IH f g). lia.
Qed.

Fixpoint weighted_future (target : nat -> list nat -> nat)
    (n : nat) (history : list nat) {struct n} : nat :=
  match n with
  | 0 => 1
  | S k =>
      total_value (outcomes (length history)) (fun draw =>
        (if hit_at target history draw then 2 else 1) *
          weighted_future target k (history ++ [draw]))
  end.

Fixpoint weighted_future_bound (n current : nat) : nat :=
  match n with
  | 0 => 1
  | S k => (current + 2) * weighted_future_bound k (S current)
  end.

Theorem weighted_future_le_bound :
  forall (target : nat -> list nat -> nat) n history,
    weighted_future target n history <= weighted_future_bound n (length history).
Proof.
  intros target n.
  induction n as [|n IH]; intros history; simpl.
  - lia.
  - set (b := weighted_future_bound n (S (length history))).
    assert (Hchild : forall draw,
      weighted_future target n (history ++ [draw]) <= b).
    {
      intros draw.
      specialize (IH (history ++ [draw])).
      replace (length (history ++ [draw])) with (S (length history)) in IH
        by (rewrite length_app; simpl; lia).
      unfold b. exact IH.
    }
    assert (Hpoint : forall draw,
      (if hit_at target history draw then 2 else 1) *
        weighted_future target n (history ++ [draw]) <=
      b + (if hit_at target history draw then b else 0)).
    {
      intros draw.
      destruct (hit_at target history draw) eqn:Hhit; simpl.
      - pose proof (Hchild draw). nia.
      - pose proof (Hchild draw). nia.
    }
    pose proof (total_value_mono (outcomes (length history))
      (fun draw => (if hit_at target history draw then 2 else 1) *
        weighted_future target n (history ++ [draw]))
      (fun draw => b + (if hit_at target history draw then b else 0)) Hpoint) as Hsum.
    assert (Hdecomp :
      total_value (outcomes (length history))
        (fun draw => b + (if hit_at target history draw then b else 0)) =
      b * length (outcomes (length history)) +
        b * event_count (outcomes (length history)) (hit_at target history)).
    {
      rewrite total_value_add.
      rewrite total_value_const.
      rewrite total_value_indicator.
      reflexivity.
    }
    assert (Hcount :
      event_count (outcomes (length history)) (hit_at target history) <= 1).
    {
      unfold hit_at.
      apply event_count_outcomes_eq_le_one.
    }
    assert (Hfinal :
      b * length (outcomes (length history)) +
        b * event_count (outcomes (length history)) (hit_at target history) <=
      (length history + 2) * b).
    {
      rewrite outcomes_length.
      nia.
    }
    eapply Nat.le_trans.
    + exact Hsum.
    + rewrite Hdecomp. exact Hfinal.
Qed.

Lemma factorial_succ : forall n, factorial (S n) = S n * factorial n.
Proof. reflexivity. Qed.

Theorem weighted_future_bound_mul_factorial :
  forall n current,
    weighted_future_bound n current * factorial (current + 1) =
    factorial (current + n + 1).
Proof.
  induction n as [|n IH]; intros current.
  - cbn [weighted_future_bound].
    replace (current + 0 + 1) with (current + 1) by lia.
    rewrite Nat.mul_1_l. reflexivity.
  - cbn [weighted_future_bound].
    replace (current + 2) with (S (current + 1)) by lia.
    rewrite (Nat.mul_comm (S (current + 1)) (weighted_future_bound n (S current))).
    rewrite <- Nat.mul_assoc.
    rewrite <- (factorial_succ (current + 1)).
    replace (S (current + 1)) with (S current + 1) by lia.
    rewrite (IH (S current)).
    replace (current + S n + 1) with (S current + n + 1) by lia.
    reflexivity.
Qed.

Theorem weighted_future_le_factorial_succ :
  forall (target : nat -> list nat -> nat) T,
    weighted_future target T [] <= factorial (T + 1).
Proof.
  intros target T.
  pose proof (weighted_future_le_bound target T []) as Hbound.
  pose proof (weighted_future_bound_mul_factorial T 0) as Hfactor.
  simpl in Hfactor.
  nia.
Qed.

End AdaptiveMoments.
