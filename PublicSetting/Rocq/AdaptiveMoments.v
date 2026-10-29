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
  simpl in Hbound.
  simpl in Hfactor.
  rewrite Nat.mul_1_r in Hfactor.
  rewrite Hfactor in Hbound.
  exact Hbound.
Qed.

(* Cross-multiplied expectation bound: weighted path sum <= (T+1) * T!,
   where factorial T is the number of finite uniform draw paths. *)
Theorem weighted_future_le_rounds_mul_factorial :
  forall (target : nat -> list nat -> nat) T,
    weighted_future target T [] <= (T + 1) * factorial T.
Proof.
  intros target T.
  pose proof (weighted_future_le_factorial_succ target T) as Hmoment.
  (* Normalize the successor index and unfold one factorial step.
     Rewriting the recursive equation directly can miss the term because
     factorial is a fixpoint whose successor case reduces by computation. *)
  replace (T + 1) with (S T) in Hmoment by lia.
  cbn [factorial] in Hmoment.
  replace (T + 1) with (S T) by lia.
  exact Hmoment.
Qed.


(* Cardinality of the finite uniform draw tree. A history of length current
   has current+1 possible next draws, so each complete T-round path has
   probability 1/(T!) under the sequential uniform sampler. *)
Fixpoint uniform_future_path_count (n current : nat) : nat :=
  match n with
  | 0 => 1
  | S k => (current + 1) * uniform_future_path_count k (S current)
  end.

Theorem uniform_future_path_count_mul_factorial :
  forall n current,
    uniform_future_path_count n current * factorial current =
    factorial (current + n).
Proof.
  induction n as [|n IH]; intros current.
  - cbn [uniform_future_path_count].
    rewrite Nat.mul_1_l.
    rewrite Nat.add_0_r.
    reflexivity.
  - cbn [uniform_future_path_count].
    replace (current + 1) with (S current) by lia.
    replace (current + S n) with (S current + n) by lia.
    assert (Hprod :
      (S current * uniform_future_path_count n (S current)) * factorial current =
      uniform_future_path_count n (S current) * (S current * factorial current)).
    {
      rewrite (Nat.mul_comm (S current) (uniform_future_path_count n (S current))).
      rewrite Nat.mul_assoc.
      reflexivity.
    }
    rewrite Hprod.
    rewrite <- factorial_succ.
    apply IH.
Qed.

Theorem uniform_future_path_count_empty :
  forall T, uniform_future_path_count T 0 = factorial T.
Proof.
  intro T.
  pose proof (uniform_future_path_count_mul_factorial T 0) as H.
  cbn [factorial] in H.
  rewrite Nat.mul_1_r in H.
  rewrite Nat.add_0_l in H.
  exact H.
Qed.

(* The pre-existing weighted_future is the unnormalized sum of
   2^(number of matches) over all leaves. Thus this theorem identifies its
   denominator exactly and states E[2^M] <= T+1 in cross-multiplied form. *)
Theorem uniform_path_exponential_moment_bound :
  forall (target : nat -> list nat -> nat) T,
    weighted_future target T [] <=
      (T + 1) * uniform_future_path_count T 0.
Proof.
  intros target T.
  rewrite uniform_future_path_count_empty.
  apply weighted_future_le_rounds_mul_factorial.
Qed.



(* Count complete future paths whose total number of hits is at least K. *)
Fixpoint tail_future_count (target : nat -> list nat -> nat)
    (n : nat) (history : list nat) (K : nat) : nat :=
  match n with
  | 0 => if Nat.eqb K 0 then 1 else 0
  | S k =>
      total_value (outcomes (length history)) (fun draw =>
        tail_future_count target k (history ++ [draw])
          (if hit_at target history draw then K - 1 else K))
  end.

Lemma total_value_mul_left :
  forall (samples : list nat) (c : nat) (f : nat -> nat),
    total_value samples (fun x => c * f x) =
      c * total_value samples f.
Proof.
  induction samples as [|x xs IH]; intros c f; simpl.
  - rewrite Nat.mul_0_r. reflexivity.
  - rewrite IH. rewrite Nat.mul_add_distr_l. reflexivity.
Qed.

(* Recursive Markov inequality for the actual sequential uniform draw tree. *)
Theorem tail_future_count_exponential_moment_le :
  forall (target : nat -> list nat -> nat) n history K,
    2 ^ K * tail_future_count target n history K <=
      weighted_future target n history.
Proof.
  intros target n.
  induction n as [|n IH]; intros history K.
  - destruct K; simpl; lia.
  - cbn [tail_future_count weighted_future].
    rewrite <- total_value_mul_left.
    apply total_value_mono.
    intros draw.
    destruct (hit_at target history draw) eqn:Hhit.
    + destruct K as [|K].
      * simpl.
        specialize (IH (history ++ [draw]) 0).
        simpl in IH.
        nia.
      * specialize (IH (history ++ [draw]) K).
        assert (Hpow : 2 ^ (S K) = 2 * 2 ^ K) by reflexivity.
        rewrite Hpow.
        rewrite <- Nat.mul_assoc.
        apply Nat.mul_le_mono_l.
        exact IH.
    + simpl.
      specialize (IH (history ++ [draw]) K).
      exact IH.
Qed.

Theorem tail_future_count_tail_bound :
  forall (target : nat -> list nat -> nat) T K,
    2 ^ K * tail_future_count target T [] K <=
      (T + 1) * factorial T.
Proof.
  intros target T K.
  eapply Nat.le_trans.
  - apply tail_future_count_exponential_moment_le.
  - apply weighted_future_le_rounds_mul_factorial.
Qed.



Fixpoint sum_tail_future_counts
    (targets : list (nat -> list nat -> nat)) (T K : nat) : nat :=
  match targets with
  | [] => 0
  | target :: rest =>
      tail_future_count target T [] K + sum_tail_future_counts rest T K
  end.

Theorem sum_tail_future_counts_bound :
  forall (targets : list (nat -> list nat -> nat)) T K,
    2 ^ K * sum_tail_future_counts targets T K <=
      length targets * ((T + 1) * factorial T).
Proof.
  induction targets as [|target targets IH]; intros T K; simpl.
  - lia.
  - pose proof (tail_future_count_tail_bound target T K) as Hhead.
    specialize (IH T K).
    rewrite Nat.mul_add_distr_l.
    eapply Nat.le_trans.
    + apply Nat.add_le_mono; [exact Hhead | exact IH].
    + simpl length.
      rewrite Nat.succ_mul.
      nia.
Qed.



(* Fixed-target lower bounds commute with mixing: if every deterministic
   policy pays at least c*T against the same target, then every uniform mixture
   over a finite list of those policies has the same lower bound in expectation,
   expressed without division. *)
Lemma total_value_mono :
  forall (samples : list nat) (f g : nat -> nat),
    (forall x, f x <= g x) ->
    total_value samples f <= total_value samples g.
Proof.
  induction samples as [|x xs IH]; intros f g Hpoint; simpl.
  - lia.
  - specialize (IH f g Hpoint). lia.
Qed.

Lemma total_value_constant :
  forall (samples : list nat) (k : nat),
    total_value samples (fun _ => k) = k * length samples.
Proof.
  induction samples as [|x xs IH]; intros k; simpl.
  - reflexivity.
  - rewrite IH. nia.
Qed.

Theorem same_fixed_target_linear_lower_bound_survives_mixing :
  forall (samples : list nat) (loss : nat -> nat) (c T : nat),
    (forall policy, c * T <= loss policy) ->
    c * T * length samples <= total_value samples loss.
Proof.
  intros samples loss c T Hlower.
  pose proof (total_value_mono samples (fun _ => c * T) loss Hlower) as Hmono.
  pose proof (total_value_constant samples (c * T)) as Hconst.
  rewrite Hconst in Hmono.
  exact Hmono.
Qed.

Lemma event_count_zero_if_not_in :
  forall (xs : list nat) target,
    ~ In target xs ->
    event_count xs (fun x => Nat.eqb x target) = 0.
Proof.
  induction xs as [|x xs IH]; intros target Hnot; simpl.
  - reflexivity.
  - assert (Heq : Nat.eqb x target = false).
    {
      destruct (Nat.eqb x target) eqn:E.
      - apply Nat.eqb_eq in E. subst target. exfalso. apply Hnot. left. reflexivity.
      - reflexivity.
    }
    rewrite Heq.
    apply IH.
    intro Hin. apply Hnot. right. exact Hin.
Qed.

Lemma event_count_eq_le_one :
  forall (xs : list nat), NoDup xs ->
    forall target, event_count xs (fun x => Nat.eqb x target) <= 1.
Proof.
  induction xs as [|x xs IH]; intros Hnodup target; simpl.
  - lia.
  - inversion Hnodup as [|x' xs' Hnotin Htail]; subst.
    destruct (Nat.eqb x target) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst target.
      pose proof (event_count_zero_if_not_in xs x Hnotin) as Hzero.
      rewrite Hzero. simpl. lia.
    + specialize (IH Htail target). simpl. rewrite Heq. exact IH.
Qed.

Lemma outcomes_nodup : forall n, NoDup (outcomes n).
Proof.
  induction n as [|n IH]; simpl.
  - constructor.
    + simpl. tauto.
    + constructor.
  - constructor.
    + intro Hin.
      pose proof (outcomes_mem_le n (S n) Hin).
      lia.
    + exact IH.
Qed.

Lemma event_count_outcomes_le_one :
  forall n target,
    event_count (outcomes n) (fun policy => Nat.eqb policy target) <= 1.
Proof.
  intros n target.
  apply event_count_eq_le_one.
  apply outcomes_nodup.
Qed.

Lemma total_value_indicator :
  forall (samples : list nat) (T : nat) (event : nat -> bool),
    total_value samples (fun x => if event x then T else 0) =
      T * event_count samples event.
Proof.
  induction samples as [|x xs IH]; intros T event; simpl.
  - reflexivity.
  - destruct (event x); simpl; rewrite IH; nia.
Qed.

Definition diagonal_target_loss (T policy target : nat) : nat :=
  if Nat.eqb policy target then T else 0.

Theorem diagonal_target_punishes_its_policy :
  forall T policy, diagonal_target_loss T policy policy = T.
Proof.
  intros T policy.
  unfold diagonal_target_loss.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

(* A finite loss matrix that isolates the quantifier issue. Every deterministic
   policy has its own target causing T loss, but for each fixed target the sum
   over T+1 equally likely policies is at most T. The matrix is a logical
   counterexample to the naive quantifier inference, not a claim that it is a
   legal partial-feedback online-learning construction. *)
Theorem diagonal_target_uniform_sum_le_horizon :
  forall T target,
    total_value (outcomes T)
      (fun policy => diagonal_target_loss T policy target) <= T.
Proof.
  intros T target.
  unfold diagonal_target_loss.
  rewrite total_value_indicator.
  pose proof (event_count_outcomes_le_one T target) as Hcount.
  eapply Nat.le_trans.
  - apply Nat.mul_le_mono_l. exact Hcount.
  - rewrite Nat.mul_1_r. lia.
Qed.

Theorem diagonal_target_uniform_sum_lt_sample_count :
  forall T target,
    total_value (outcomes T)
      (fun policy => diagonal_target_loss T policy target) < length (outcomes T).
Proof.
  intros T target.
  pose proof (diagonal_target_uniform_sum_le_horizon T target) as Hsum.
  rewrite outcomes_length.
  lia.
Qed.

End AdaptiveMoments.
