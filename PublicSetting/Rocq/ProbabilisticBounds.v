From Stdlib Require Import Arith Lia List Bool.
Import ListNotations.

(* Finite-counting lemmas for the randomized public-setting proof.
   The per-index stochastic tail premise is intentionally explicit: this file
   checks event-union aggregation and the expectation truncation, but does not
   pretend that the conditional-uniform-draw-to-factorial-tail bridge has
   already been formalized. *)

Section ProbabilisticBounds.
  Context {Omega : Type}.

  Fixpoint event_count (samples : list Omega) (event : Omega -> bool) : nat :=
    match samples with
    | [] => 0
    | x :: xs => (if event x then 1 else 0) + event_count xs event
    end.

  Fixpoint event_any (events : list (Omega -> bool)) : Omega -> bool :=
    match events with
    | [] => fun _ => false
    | e :: es => fun x => e x || event_any es x
    end.

  Fixpoint sum_event_counts (samples : list Omega)
      (events : list (Omega -> bool)) : nat :=
    match events with
    | [] => 0
    | e :: es => event_count samples e + sum_event_counts samples es
    end.

  Fixpoint total_value (samples : list Omega) (value : Omega -> nat) : nat :=
    match samples with
    | [] => 0
    | x :: xs => value x + total_value xs value
    end.

  Fixpoint factorial (n : nat) : nat :=
    match n with
    | 0 => 1
    | S k => S k * factorial k
    end.

  Lemma factorial_pos : forall n, 0 < factorial n.
  Proof.
    induction n; simpl; [lia|].
    lia.
  Qed.

  Lemma event_count_false :
    forall (samples : list Omega),
      event_count samples (fun _ => false) = 0.
  Proof.
    induction samples as [|x xs IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
  Qed.

  Lemma event_count_or_le :
    forall (samples : list Omega) (p q : Omega -> bool),
      event_count samples (fun x => p x || q x) <=
      event_count samples p + event_count samples q.
  Proof.
    induction samples as [|x xs IH]; intros p q; simpl.
    - lia.
    - destruct (p x); destruct (q x); simpl; specialize (IH p q); lia.
  Qed.

  Lemma event_count_any_le_sum :
    forall (samples : list Omega) (events : list (Omega -> bool)),
      event_count samples (event_any events) <=
      sum_event_counts samples events.
  Proof.
    intros samples events.
    induction events as [|e es IH]; simpl.
    - rewrite event_count_false. lia.
    - eapply Nat.le_trans.
      + apply event_count_or_le.
      + lia.
  Qed.

  Lemma factorial_mul_event_counts_le :
    forall (samples : list Omega) (events : list (Omega -> bool))
      (k q : nat),
      (forall event, In event events ->
        factorial k * event_count samples event <=
          q ^ k * length samples) ->
      factorial k * sum_event_counts samples events <=
        length events * (q ^ k * length samples).
  Proof.
    intros samples events.
    induction events as [|event events IH]; intros k q Htail; simpl.
    - lia.
    - assert (Hhead :
        factorial k * event_count samples event <= q ^ k * length samples).
      { apply Htail. left. reflexivity. }
      assert (Hrest :
        forall e, In e events ->
          factorial k * event_count samples e <= q ^ k * length samples).
      { intros e Hin. apply Htail. right. exact Hin. }
      specialize (IH k q Hrest).
      rewrite Nat.mul_add_distr_l.
      eapply Nat.le_trans.
      + apply Nat.add_le_mono; [exact Hhead|exact IH].
      + lia.
  Qed.

  Theorem factorial_mul_union_tail_le :
    forall (samples : list Omega) (events : list (Omega -> bool))
      (k q : nat),
      (forall event, In event events ->
        factorial k * event_count samples event <= q ^ k * length samples) ->
      factorial k * event_count samples (event_any events) <=
        length events * (q ^ k * length samples).
  Proof.
    intros samples events k q Htail.
    eapply Nat.le_trans.
    - apply Nat.mul_le_mono_l.
      apply event_count_any_le_sum.
    - apply factorial_mul_event_counts_le. exact Htail.
  Qed.

  Lemma bad_budget_of_union_tail_bound :
    forall (samples : list Omega) (events : list (Omega -> bool))
      (k q T : nat),
      (forall event, In event events ->
        factorial k * event_count samples event <= q ^ k * length samples) ->
      T * length events * q ^ k <= factorial k ->
      T * event_count samples (event_any events) <= length samples.
  Proof.
    intros samples events k q T Htail Harith.
    pose proof (factorial_mul_union_tail_le samples events k q Htail) as Hunion.
    assert (Hscaled :
      factorial k * (T * event_count samples (event_any events)) <=
      factorial k * length samples).
    {
      eapply Nat.le_trans.
      - replace (factorial k * (T * event_count samples (event_any events)))
          with (T * (factorial k * event_count samples (event_any events))) by nia.
        apply Nat.mul_le_mono_l. exact Hunion.
      - replace (T * (length events * (q ^ k * length samples)))
          with ((T * length events * q ^ k) * length samples) by nia.
        apply Nat.mul_le_mono_r. exact Harith.
    }
    destruct (le_gt_dec (T * event_count samples (event_any events)) (length samples))
      as [Hle | Hgt].
    - exact Hle.
    - assert (Hlt : length samples < T * event_count samples (event_any events)) by lia.
      pose proof (proj1 (Nat.mul_lt_mono_pos_l (factorial k) (length samples) (T * event_count samples (event_any events)) (factorial_pos k)) Hlt) as Hstrict.
      lia.
  Qed.

  Lemma total_value_mono :
    forall (samples : list Omega) (f g : Omega -> nat),
      (forall x, f x <= g x) ->
      total_value samples f <= total_value samples g.
  Proof.
    intros samples f g Hpoint.
    induction samples as [|x xs IH]; simpl; [lia|].
    specialize (Hpoint x). lia.
  Qed.

  Lemma total_value_const :
    forall (samples : list Omega) (K : nat),
      total_value samples (fun _ => K) = K * length samples.
  Proof.
    induction samples as [|x xs IH]; intros K; simpl.
    - rewrite Nat.mul_0_r. reflexivity.
    - rewrite (IH K). rewrite Nat.mul_succ_r. lia.
  Qed.

  Lemma total_value_indicator :
    forall (samples : list Omega) (T : nat) (bad : Omega -> bool),
      total_value samples (fun x => if bad x then T else 0) =
        T * event_count samples bad.
  Proof.
    induction samples as [|x xs IH]; intros T bad; simpl.
    - rewrite Nat.mul_0_r. reflexivity.
    - destruct (bad x); simpl; rewrite (IH T bad); rewrite ?Nat.mul_add_distr_l; simpl; lia.
  Qed.

  Lemma total_value_add :
    forall (samples : list Omega) (f g : Omega -> nat),
      total_value samples (fun x => f x + g x) =
        total_value samples f + total_value samples g.
  Proof.
    induction samples as [|x xs IH]; intros f g; simpl.
    - reflexivity.
    - rewrite (IH f g). lia.
  Qed.

  (* If factorial k * count(event_i) <= q^k * N for each member of events,
     then the finite union bound follows after cross-multiplication. *)
  Theorem total_value_le_threshold_plus_one :
    forall (samples : list Omega) (loss : Omega -> nat)
      (bad : Omega -> bool) (K T : nat),
      (forall x, loss x <= K + (if bad x then T else 0)) ->
      T * event_count samples bad <= length samples ->
      total_value samples loss <= (K + 1) * length samples.
  Proof.
    intros samples loss bad K T Hpoint Hbudget.
    eapply Nat.le_trans.
    - apply total_value_mono. exact Hpoint.
    - rewrite total_value_add.
      rewrite total_value_const.
      rewrite total_value_indicator.
      nia.
  Qed.

  Theorem total_value_le_from_factorial_tails :
    forall (samples : list Omega) (events : list (Omega -> bool))
      (loss : Omega -> nat) (K T q : nat),
      (forall event, In event events ->
        factorial K * event_count samples event <= q ^ K * length samples) ->
      T * length events * q ^ K <= factorial K ->
      (forall x, loss x <= K + (if event_any events x then T else 0)) ->
      total_value samples loss <= (K + 1) * length samples.
  Proof.
    intros samples events loss K T q Htail Harith Hpoint.
    eapply total_value_le_threshold_plus_one.
    - exact Hpoint.
    - apply bad_budget_of_union_tail_bound with (events := events) (k := K) (q := q).
      + exact Htail.
      + exact Harith.
  Qed.


  Lemma pow_two_mono : forall a b, a <= b -> 2 ^ a <= 2 ^ b.
  Proof.
    intros a b Hab.
    assert (Hex : exists d, b = a + d) by (exists (b - a); lia).
    destruct Hex as [d Hd].
    subst b.
    rewrite Nat.pow_add_r.
    assert (Hp : 1 <= 2 ^ d) by (induction d; simpl; lia).
    rewrite <- Nat.mul_1_r at 1.
    apply Nat.mul_le_mono_l. exact Hp.
  Qed.

  Definition score_tail_event (K : nat) (score : Omega -> nat) : Omega -> bool :=
    fun x => Nat.leb K (score x).

  (* Integer-scaled finite-sample Markov inequality:
     2^K times the number of samples with score >= K is at most the sum of
     the exponential weights. Repeated samples represent distinct outcomes. *)
  Theorem exponential_moment_tail_count_le :
    forall (samples : list Omega) (score : Omega -> nat) (K : nat),
      2 ^ K * event_count samples (score_tail_event K score) <=
        total_value samples (fun x => 2 ^ score x).
  Proof.
    intros samples score K.
    assert (Hpoint : forall x,
      (if score_tail_event K score x then 2 ^ K else 0) <= 2 ^ score x).
    {
      intros x. unfold score_tail_event.
      destruct (K <=? score x) eqn:Hcmp.
      - apply Nat.leb_le in Hcmp.
        apply pow_two_mono. exact Hcmp.
      - lia.
    }
    pose proof (total_value_mono samples
      (fun x => if score_tail_event K score x then 2 ^ K else 0)
      (fun x => 2 ^ score x) Hpoint) as Hmono.
    rewrite total_value_indicator in Hmono.
    exact Hmono.
  Qed.

  Lemma scaled_mul_sum_event_counts_le :
    forall (samples : list Omega) (events : list (Omega -> bool))
      (scale bound : nat),
      (forall event, In event events ->
        scale * event_count samples event <= bound * length samples) ->
      scale * sum_event_counts samples events <=
        length events * (bound * length samples).
  Proof.
    intros samples events.
    induction events as [|event events IH]; intros scale bound Htail; simpl.
    - lia.
    - assert (Hhead :
        scale * event_count samples event <= bound * length samples).
      { apply Htail. left. reflexivity. }
      assert (Hrest :
        forall e, In e events ->
          scale * event_count samples e <= bound * length samples).
      { intros e Hin. apply Htail. right. exact Hin. }
      specialize (IH scale bound Hrest).
      change (scale * (event_count samples event + sum_event_counts samples events)
        <= S (length events) * (bound * length samples)).
      rewrite Nat.mul_add_distr_l.
      eapply Nat.le_trans.
      + apply Nat.add_le_mono; [exact Hhead|exact IH].
      + rewrite Nat.mul_succ_l. nia.
  Qed.

  Theorem scaled_mul_union_tail_le :
    forall (samples : list Omega) (events : list (Omega -> bool))
      (scale bound : nat),
      (forall event, In event events ->
        scale * event_count samples event <= bound * length samples) ->
      scale * event_count samples (event_any events) <=
        length events * (bound * length samples).
  Proof.
    intros samples events scale bound Htail.
    eapply Nat.le_trans.
    - apply Nat.mul_le_mono_l.
      apply event_count_any_le_sum.
    - apply scaled_mul_sum_event_counts_le. exact Htail.
  Qed.

  Theorem bad_budget_of_scaled_union_tail_bound :
    forall (samples : list Omega) (events : list (Omega -> bool))
      (scale bound T : nat),
      0 < scale ->
      (forall event, In event events ->
        scale * event_count samples event <= bound * length samples) ->
      T * length events * bound <= scale ->
      T * event_count samples (event_any events) <= length samples.
  Proof.
    intros samples events scale bound T Hscale Htail Hbudget.
    pose proof (scaled_mul_union_tail_le samples events scale bound Htail) as Hunion.
    assert (Hscaled :
      scale * (T * event_count samples (event_any events)) <=
      scale * length samples).
    {
      eapply Nat.le_trans.
      - replace (scale * (T * event_count samples (event_any events)))
          with (T * (scale * event_count samples (event_any events))) by nia.
        apply Nat.mul_le_mono_l. exact Hunion.
      - replace (T * (length events * (bound * length samples)))
          with ((T * length events * bound) * length samples) by nia.
        apply Nat.mul_le_mono_r. exact Hbudget.
    }
    destruct (le_gt_dec (T * event_count samples (event_any events)) (length samples))
      as [Hle | Hgt].
    - exact Hle.
    - assert (Hlt : length samples < T * event_count samples (event_any events)) by lia.
      pose proof
        (proj1 (Nat.mul_lt_mono_pos_l scale (length samples)
          (T * event_count samples (event_any events)) Hscale) Hlt) as Hstrict.
      lia.
  Qed.

  Theorem exponential_moment_tail_count_le_of_bound :
    forall (samples : list Omega) (score : Omega -> nat) (K C : nat),
      total_value samples (fun x => 2 ^ score x) <= C * length samples ->
      2 ^ K * event_count samples (score_tail_event K score) <=
        C * length samples.
  Proof.
    intros samples score K C Hmoment.
    eapply Nat.le_trans.
    - apply exponential_moment_tail_count_le.
    - exact Hmoment.
  Qed.

  Theorem exponential_moment_union_tail_count_le :
    forall (samples : list Omega) (scores : list (Omega -> nat)) (K C : nat),
      (forall score, In score scores ->
        total_value samples (fun x => 2 ^ score x) <= C * length samples) ->
      2 ^ K * event_count samples
        (event_any (map (score_tail_event K) scores)) <=
        length scores * (C * length samples).
  Proof.
    intros samples scores K C Hmoments.
    assert (Htail :
      2 ^ K * event_count samples
        (event_any (map (score_tail_event K) scores)) <=
        length (map (score_tail_event K) scores) * (C * length samples)).
    {
      apply scaled_mul_union_tail_le with (scale := 2 ^ K) (bound := C).
      intros event Hin.
      apply in_map_iff in Hin.
      destruct Hin as [score [Hevent Hscore]].
      subst event.
      apply exponential_moment_tail_count_le_of_bound.
      apply Hmoments. exact Hscore.
    }
    rewrite length_map in Htail.
    exact Htail.
  Qed.

  Theorem total_value_le_from_exponential_moments :
    forall (samples : list Omega) (scores : list (Omega -> nat))
      (loss : Omega -> nat) (K T C : nat),
      (forall score, In score scores ->
        total_value samples (fun x => 2 ^ score x) <= C * length samples) ->
      T * length scores * C <= 2 ^ K ->
      (forall x, loss x <= K +
        (if event_any (map (score_tail_event K) scores) x then T else 0)) ->
      total_value samples loss <= (K + 1) * length samples.
  Proof.
    intros samples scores loss K T C Hmoments Hbudget Hpoint.
    eapply total_value_le_threshold_plus_one.
    - exact Hpoint.
    - apply bad_budget_of_scaled_union_tail_bound with
        (scale := 2 ^ K) (bound := C).
      + induction K as [|K IH]; simpl.
        * lia.
        * apply Nat.mul_pos; [lia | exact IH].
      + intros event Hin.
        apply in_map_iff in Hin.
        destruct Hin as [score [Hevent Hscore]].
        subst event.
        apply exponential_moment_tail_count_le_of_bound.
        apply Hmoments. exact Hscore.
      + rewrite length_map. exact Hbudget.
  Qed.

End ProbabilisticBounds.
