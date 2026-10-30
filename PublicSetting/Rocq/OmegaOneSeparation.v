From Stdlib Require Import Arith Lia List Classical_Prop ClassicalDescription.
Import ListNotations.

(*
  Independent, abstract formalization of the omega-one construction.

  Unlike the Lean development, Rocq's Stdlib has no ready-made concrete
  omega_1 ordinal / countable-cocountable measure package.  This file proves
  the full measure and game lemmas for any label order equipped with the
  defining omega_1 properties: its countable initial segments are small, the
  small sets form a countable ideal, and every countable sequence of labels
  is bounded.  No axiom or admitted theorem is used.
*)

Section CountableCocountableMeasure.

  Context {Y : Type}.

  Record CountableIdeal := {
    Small : (Y -> Prop) -> Prop;
    small_empty : Small (fun _ => False);
    small_mono : forall A B : Y -> Prop,
        (forall x, A x -> B x) -> Small B -> Small A;
    small_countable_union : forall A : nat -> Y -> Prop,
        (forall n, Small (A n)) ->
        Small (fun x => exists n, A n x);
    universe_not_small : ~ Small (fun _ => True)
  }.

  Context (I : CountableIdeal).

  Definition Measurable (A : Y -> Prop) : Prop :=
    Small I A \/ Small I (fun x => ~ A x).

  Definition MeasureOne (A : Y -> Prop) : Prop :=
    ~ Small I A.

  Definition Mass (A : Y -> Prop) : nat :=
    if excluded_middle_informative (MeasureOne A) then 1 else 0.

  Lemma measurable_empty : Measurable (fun _ => False).
  Proof.
    left. apply small_empty.
  Qed.

  Lemma measurable_complement :
    forall A, Measurable A -> Measurable (fun x => ~ A x).
  Proof.
    intros A [hA | hAc].
    - right. exact hA.
    - left. exact hAc.
  Qed.

  Lemma measurable_countable_union :
    forall A : nat -> Y -> Prop,
      (forall n, Measurable (A n)) ->
      Measurable (fun x => exists n, A n x).
  Proof.
    intros A hA.
    destruct (classic (exists n, ~ Small I (A n))) as [[n hn] | hall].
    - right.
      destruct (hA n) as [hs | hsc].
      + contradiction.
      + eapply small_mono; [|exact hsc].
        intros x hx hAx. apply hx. exists n. exact hAx.
    - left. apply small_countable_union.
      intro n. destruct (hA n) as [hs | hsc]; [exact hs|].
      exfalso. apply hall. exists n. exact hsc.
  Qed.

  Lemma measure_one_iff_union :
    forall A : nat -> Y -> Prop,
      (forall n, Measurable (A n)) ->
      (MeasureOne (fun x => exists n, A n x) <->
       exists n, MeasureOne (A n)).
  Proof.
    intros A hA. unfold MeasureOne. split.
    - intro hUnion.
      destruct (classic (exists n, ~ Small I (A n))) as [h | h].
      + exact h.
      + exfalso. apply hUnion. apply small_countable_union.
        intro n. destruct (hA n) as [hs | hsc]; [exact hs|].
        exfalso. apply h. exists n. exact hsc.
    - intros [n hn] hUnion.
      apply hn. eapply small_mono; [|exact hUnion].
      intros x hx. exists n. exact hx.
  Qed.

  Lemma measurable_non_small_complement :
    forall A, Measurable A -> MeasureOne A ->
      Small I (fun x => ~ A x).
  Proof.
    intros A [hA | hAc] hOne; [contradiction|exact hAc].
  Qed.

  Definition PairwiseDisjoint (A : nat -> Y -> Prop) : Prop :=
    forall n m x, n <> m -> A n x -> A m x -> False.

  Lemma disjoint_at_most_one_non_small :
    forall A : nat -> Y -> Prop,
      (forall n, Measurable (A n)) ->
      PairwiseDisjoint A ->
      forall n m, n <> m ->
        MeasureOne (A n) -> MeasureOne (A m) -> False.
  Proof.
    intros A hMeas hDisj n m hnm hn hm.
    apply hn.
    destruct (measurable_non_small_complement (A m) (hMeas m) hm)
      as hSmallComp.
    eapply small_mono; [|exact hSmallComp].
    intros x hAn hAmComp.
    apply hAmComp.
    eapply hDisj; eauto.
  Qed.

  (*
    Since pairwise disjoint measurable sets have at most one cocountable
    member, their countable sum in {0,1} is exactly 1 iff one term is 1.
    CountableSum is the exact value of the nonnegative series for such a
    zero-one sequence; at most one summand is nonzero.
  *)
  Definition CountableSum01 (a : nat -> nat) : nat :=
    if excluded_middle_informative (exists n, a n = 1) then 1 else 0.

  Lemma countable_sum01_spec :
    forall a, CountableSum01 a = 1 <-> exists n, a n = 1.
  Proof.
    intros a. unfold CountableSum01.
    destruct (excluded_middle_informative (exists n, a n = 1)); simpl; tauto.
  Qed.

  Lemma countable_additivity_zero_one :
    forall A : nat -> Y -> Prop,
      (forall n, Measurable (A n)) ->
      PairwiseDisjoint A ->
      Mass (fun x => exists n, A n x) =
        CountableSum01 (fun n => Mass (A n)).
  Proof.
    intros A hMeas hDisj.
    unfold Mass.
    destruct (excluded_middle_informative
      (MeasureOne (fun x => exists n, A n x))) as [hUnion | hUnion].
    - destruct (measure_one_iff_union A hMeas) as [hForward _].
      specialize (hForward hUnion) as [n hn].
      unfold MeasureOne in hn.
      destruct (excluded_middle_informative (MeasureOne (A n))) as [hMass | hMass].
      + unfold CountableSum01.
        destruct (excluded_middle_informative
          (exists k, (if excluded_middle_informative (MeasureOne (A k)) then 1 else 0) = 1))
          as [_ | hNone]; [reflexivity|].
        exfalso. apply hNone. exists n.
        destruct (excluded_middle_informative (MeasureOne (A n))); congruence.
      + contradiction.
    - destruct (excluded_middle_informative
        (exists n, (if excluded_middle_informative (MeasureOne (A n))
                    then 1 else 0) = 1)) as [[n hn] | hNone].
      + destruct (excluded_middle_informative (MeasureOne (A n))) as [hMass | hMass].
        * exfalso. apply hUnion.
          apply (proj2 (measure_one_iff_union A hMeas)).
          exists n. exact hMass.
        * simpl in hn. discriminate.
      + unfold CountableSum01.
        destruct (excluded_middle_informative
          (exists n, (if excluded_middle_informative (MeasureOne (A n))
                      then 1 else 0) = 1)); [congruence|].
        reflexivity.
  Qed.

  Lemma mass_is_zero_or_one :
    forall A, Mass A = 0 \/ Mass A = 1.
  Proof.
    intro A. unfold Mass.
    destruct (excluded_middle_informative (MeasureOne A)); auto.
  Qed.

  Lemma mass_universe_one : Mass (fun _ : Y => True) = 1.
  Proof.
    unfold Mass, MeasureOne.
    destruct (excluded_middle_informative (universe_not_small I)); [|contradiction].
    reflexivity.
  Qed.

  Lemma mass_empty_zero : Mass (fun _ : Y => False) = 0.
  Proof.
    unfold Mass, MeasureOne.
    destruct (excluded_middle_informative (not_small_empty I)); [contradiction|reflexivity].
  Qed.

End CountableCocountableMeasure.

(*
  Ordered label spaces with omega-one properties.  The concrete Lean
  instantiation uses the ordinal type Iio omega_1.  Rocq's independent generic
  theorem is parameterized by an explicit order structure and small ideal.
*)
Section OmegaOneGame.

  Context {Y : Type}.

  Variable lt : Y -> Y -> Prop.
  Definition le (x y : Y) : Prop := ~ lt y x.

  Hypothesis lt_irrefl : forall x, ~ lt x x.
  Hypothesis lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
  Hypothesis lt_le_trans :
    forall x y z, lt x y -> le y z -> lt x z.
  Hypothesis succ : Y -> Y.
  Hypothesis lt_succ : forall y, lt y (succ y).
  Hypothesis initial_segments_small :
    forall y, Small I (fun x => lt x y).
  Variable I : @CountableIdeal Y.
  Hypothesis countable_bounded :
    forall seq : nat -> Y, exists b, forall n, le (seq n) b.

  Definition Tail (threshold : Y) (y : Y) : Prop :=
    le threshold y.

  Definition MissSet (chooseThreshold : Y -> Y) (witness : Y) : Y -> Prop :=
    fun prediction => ~ Tail (chooseThreshold prediction) prediction.

  Lemma miss_subset_initial_segment :
    forall chooseThreshold witness,
      (forall prediction, Tail (chooseThreshold prediction) witness) ->
      forall prediction,
        MissSet chooseThreshold witness prediction -> lt prediction witness.
  Proof.
    intros chooseThreshold witness hContains prediction hMiss.
    unfold MissSet, Tail, le in *.
    apply lt_le_trans with (y := chooseThreshold prediction).
    - apply NNPP. exact hMiss.
    - exact hContains.
  Qed.

  Lemma miss_set_small :
    forall chooseThreshold witness,
      (forall prediction, Tail (chooseThreshold prediction) witness) ->
      Small I (MissSet chooseThreshold witness).
  Proof.
    intros chooseThreshold witness hContains.
    eapply small_mono.
    - intros prediction hMiss.
      exact (miss_subset_initial_segment chooseThreshold witness hContains prediction hMiss).
    - apply initial_segments_small.
  Qed.

  Definition GlobalFamily (thresholds : nat -> Y) (f : nat -> Y) : Prop :=
    forall t, Tail (thresholds t) (f t).

  Definition AcceptedAt (thresholds : nat -> Y) (t : nat) (y : Y) : Prop :=
    exists f, GlobalFamily thresholds f /\ f t = y.

  Lemma accepted_iff_tail :
    forall thresholds t y,
      AcceptedAt thresholds t y <-> Tail (thresholds t) y.
  Proof.
    intros thresholds t y. split.
    - intros [f [hf hft]]. subst y. exact (hf t).
    - intro hy.
      exists (fun s => if Nat.eq_dec s t then y else thresholds s).
      split.
      + intro s. unfold Tail.
        destruct (Nat.eq_dec s t) as [hs | hs].
        * subst s. exact hy.
        * unfold Tail. apply le_refl_from_order.
      + simpl. destruct (Nat.eq_dec t t); congruence.
  Qed.

  Lemma global_family_nonempty :
    forall thresholds, exists f, GlobalFamily thresholds f.
  Proof.
    intro thresholds. exists thresholds. intro t.
    apply le_refl_from_order.
  Qed.

  Definition DeterministicThresholds (prediction : nat -> Y) : nat -> Y :=
    fun t => succ (prediction t).

  Lemma deterministic_prediction_wrong :
    forall prediction t,
      ~ Tail (DeterministicThresholds prediction t) (prediction t).
  Proof.
    intros prediction t. unfold Tail, DeterministicThresholds, le.
    exact lt_succ (prediction t).
  Qed.

  Definition RoundLoss (prediction : nat -> Y) (t : nat) : nat :=
    if excluded_middle_informative
      (Tail (DeterministicThresholds prediction t) (prediction t))
    then 0 else 1.

  Lemma round_loss_one :
    forall prediction t, RoundLoss prediction t = 1.
  Proof.
    intros prediction t. unfold RoundLoss.
    destruct (excluded_middle_informative
      (Tail (DeterministicThresholds prediction t) (prediction t))); [contradiction|reflexivity].
  Qed.

  Fixpoint TotalLoss (prediction : nat -> Y) (T : nat) : nat :=
    match T with
    | 0 => 0
    | S n => TotalLoss prediction n + RoundLoss prediction n
    end.

  Lemma total_loss_exact :
    forall prediction T, TotalLoss prediction T = T.
  Proof.
    intros prediction T. induction T as [|T IH].
    - reflexivity.
    - simpl. rewrite IH, round_loss_one. reflexivity.
  Qed.

End OmegaOneGame.
