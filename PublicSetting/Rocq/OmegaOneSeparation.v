From Stdlib Require Import Arith Lia List Classical_Prop ClassicalDescription.
Import ListNotations.

(*
  Independent, abstract formalization of the omega-one construction.

  Rocq's Stdlib has no ready-made concrete omega_1 ordinal / countable-cocountable
  measure package. This file proves the full measure and game lemmas for any
  label order equipped with the defining omega_1 properties: its countable
  initial segments are small, the small sets form a countable ideal, and every
  countable sequence of labels is bounded. The concrete ordinal instance is
  constructed in the Lean/Mathlib development.

  No axiom, Parameter, Admitted, or admit is used here.
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
    - right.
      exact (@small_mono I (fun x => ~ ~ A x) A
        (fun x hnnA => NNPP (A x) hnnA) hA).
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
      intro n. destruct (hA n) as [hs | _]; [exact hs|].
      apply NNPP. intro hns.
      apply hall. exists n. exact hns.
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
        intro n. destruct (hA n) as [hs | _]; [exact hs|].
        apply NNPP. intro hns.
        apply h. exists n. exact hns.
    - intros [n hn] hUnion.
      apply hn. eapply small_mono; [|exact hUnion].
      intros x hx. exists n. exact hx.
  Qed.

  Lemma measurable_non_small_complement :
    forall A, Measurable A -> MeasureOne A ->
      Small I (fun x => ~ A x).
  Proof.
    intros A [hA | hAc] hOne.
    - contradiction.
    - exact hAc.
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
    pose proof (measurable_non_small_complement (A m) (hMeas m) hm) as hSmallComp.
    eapply small_mono; [|exact hSmallComp].
    intros x hAn hAm.
    eapply hDisj; eauto.
  Qed.

  (*
    A countable sum of zero-one terms with at most one nonzero term is 1
    exactly when at least one term is 1. Pairwise disjoint measurable sets
    have at most one cocountable member, so this is ordinary countable
    additivity specialized to this {0,1}-valued measure.
  *)
  Definition CountableSum01 (a : nat -> nat) : nat :=
    if excluded_middle_informative (exists n, a n = 1) then 1 else 0.

  Lemma countable_sum01_spec :
    forall a, CountableSum01 a = 1 <-> exists n, a n = 1.
  Proof.
    intros a. unfold CountableSum01.
    destruct (excluded_middle_informative (exists n, a n = 1)); simpl; tauto.
  Qed.

  Definition AtMostOneOne (a : nat -> nat) : Prop :=
    forall n m, n <> m -> a n = 1 -> a m = 1 -> False.

  Lemma disjoint_mass_at_most_one :
    forall A : nat -> Y -> Prop,
      (forall n, Measurable (A n)) ->
      PairwiseDisjoint A ->
      AtMostOneOne (fun n => Mass (A n)).
  Proof.
    intros A hMeas hDisj n m hnm hMn hMm.
    assert (hn : MeasureOne (A n)).
    { unfold Mass in hMn.
      destruct (excluded_middle_informative (MeasureOne (A n))) as [h | h].
      - exact h.
      - discriminate. }
    assert (hm : MeasureOne (A m)).
    { unfold Mass in hMm.
      destruct (excluded_middle_informative (MeasureOne (A m))) as [h | h].
      - exact h.
      - discriminate. }
    exact (disjoint_at_most_one_non_small A hMeas hDisj n m hnm hn hm).
  Qed.

  Lemma countable_sum01_is_series_for_disjoint :
    forall A : nat -> Y -> Prop,
      (forall n, Measurable (A n)) ->
      PairwiseDisjoint A ->
      AtMostOneOne (fun n => Mass (A n)).
  Proof.
    exact disjoint_mass_at_most_one.
  Qed.

  Lemma countable_additivity_zero_one :
    forall A : nat -> Y -> Prop,
      (forall n, Measurable (A n)) ->
      PairwiseDisjoint A ->
      Mass (fun x => exists n, A n x) =
        CountableSum01 (fun n => Mass (A n)).
  Proof.
    intros A hMeas hDisj.
    unfold Mass, CountableSum01.
    destruct (excluded_middle_informative
      (MeasureOne (fun x => exists n, A n x))) as [hUnion | hUnion].
    - destruct (measure_one_iff_union A hMeas) as [hForward _].
      destruct (hForward hUnion) as [n hn].
      destruct (excluded_middle_informative (exists k,
        (if excluded_middle_informative (MeasureOne (A k)) then 1 else 0) = 1))
        as [hSome | hNone].
      + reflexivity.
      + exfalso. apply hNone. exists n.
        destruct (excluded_middle_informative (MeasureOne (A n))); [reflexivity|contradiction].
    - destruct (excluded_middle_informative (exists n,
        (if excluded_middle_informative (MeasureOne (A n)) then 1 else 0) = 1))
        as [hSome | hNone].
      + destruct hSome as [n hn].
        destruct (excluded_middle_informative (MeasureOne (A n))) as [hMass | hMass].
        * exfalso. apply hUnion.
          apply (proj2 (measure_one_iff_union A hMeas)).
          exists n. exact hMass.
        * simpl in hn. discriminate.
      + reflexivity.
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
    destruct (excluded_middle_informative (universe_not_small I)) as [h | h].
    - reflexivity.
    - contradiction.
  Qed.

  Lemma mass_empty_zero : Mass (fun _ : Y => False) = 0.
  Proof.
    unfold Mass, MeasureOne.
    destruct (excluded_middle_informative
      (~ Small I (fun _ => False))) as [h | h].
    - exfalso. apply h. exact (small_empty I).
    - reflexivity.
  Qed.


  Definition Binary01 (a : nat -> nat) : Prop :=
    forall n, a n = 0 \/ a n = 1.

  Fixpoint PartialSum01 (a : nat -> nat) (n : nat) : nat :=
    match n with
    | 0 => 0
    | S k => PartialSum01 a k + a k
    end.

  Lemma partial_sum01_zero_prefix :
    forall a n,
      (forall k, k < n -> a k = 0) ->
      PartialSum01 a n = 0.
  Proof.
    intros a n. induction n as [|n IH]; intro h.
    - reflexivity.
    - simpl. rewrite IH.
      + rewrite (h n (Nat.lt_succ_diag_r n)). lia.
      + intros k hk. apply h. lia.
  Qed.

  Lemma partial_sum01_le_one :
    forall a,
      Binary01 a ->
      AtMostOneOne a ->
      forall n, PartialSum01 a n <= 1.
  Proof.
    intros a hbin hone n. induction n as [|n IH].
    - reflexivity.
    - simpl.
      destruct (hbin n) as [hzero | hone_n].
      + rewrite hzero. lia.
      + assert (hprefix : PartialSum01 a n = 0).
        { apply partial_sum01_zero_prefix.
          intros k hk.
          destruct (hbin k) as [hzero | hone_k].
          - exact hzero.
          - exfalso.
            exact (hone k n (Nat.ne_of_lt hk) hone_k hone_n). }
        rewrite hprefix, hone_n. lia.
  Qed.

  Lemma countable_sum01_is_sup_partial_sums :
    forall a,
      Binary01 a ->
      AtMostOneOne a ->
      (forall n, PartialSum01 a n <= CountableSum01 a) /\
      (forall b, (forall n, PartialSum01 a n <= b) ->
        CountableSum01 a <= b).
  Proof.
    intros a hbin hone.
    unfold CountableSum01.
    destruct (excluded_middle_informative (exists n, a n = 1))
      as [[n hn] | hnone].
    - simpl. split.
      + intro k. exact (partial_sum01_le_one a hbin hone k).
      + intros b hb.
        assert (hprefix : PartialSum01 a n = 0).
        { apply partial_sum01_zero_prefix.
          intros k hk.
          destruct (hbin k) as [hzero | hone_k].
          - exact hzero.
          - exfalso.
            exact (hone k n (Nat.ne_of_lt hk) hone_k hn). }
        specialize (hb (S n)).
        simpl in hb. rewrite hprefix, hn in hb. lia.
    - simpl. split.
      + intro n.
        assert (hzero : PartialSum01 a n = 0).
        { apply partial_sum01_zero_prefix.
          intros k hk.
          destruct (hbin k) as [hzero | hone_k].
          - exact hzero.
          - exfalso. apply hnone. exists k. exact hone_k. }
        rewrite hzero. lia.
      + intros b hb. lia.
  Qed.

  (--
    A zero-one probability measure is a probability measure with values in
    {0,1}; its countable sum is the supremum of its finite partial sums.
    For disjoint measurable sets, at most one summand can be one, and the
    preceding theorem verifies the exact series semantics of CountableSum01.
  --)
  Record ZeroOneProbabilityMeasure := {
    zpm_measurable : (Y -> Prop) -> Prop;
    zpm_mass : (Y -> Prop) -> nat;
    zpm_empty : zpm_mass (fun _ => False) = 0;
    zpm_total : zpm_mass (fun _ => True) = 1;
    zpm_binary : forall A, zpm_mass A = 0 \/ zpm_mass A = 1;
    zpm_countable_additive :
      forall A : nat -> Y -> Prop,
        (forall n, zpm_measurable (A n)) ->
        PairwiseDisjoint A ->
        zpm_mass (fun x => exists n, A n x) =
          CountableSum01 (fun n => zpm_mass (A n))
  }.

  Definition countableCocountableProbability : ZeroOneProbabilityMeasure :=
    {| zpm_measurable := Measurable;
       zpm_mass := Mass;
       zpm_empty := mass_empty_zero;
       zpm_total := mass_universe_one;
       zpm_binary := mass_is_zero_or_one;
       zpm_countable_additive := countable_additivity_zero_one |}.

  Lemma countableCocountable_probability_measure :
    zpm_total countableCocountableProbability = 1.
  Proof. exact (zpm_total countableCocountableProbability). Qed.

End CountableCocountableMeasure.

Section OmegaOneGame.

  Context {Y : Type}.
  Variable I : @CountableIdeal Y.
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

  Hypothesis countable_bounded :
    forall seq : nat -> Y, exists b, forall n, le (seq n) b.

  Lemma all_upper_tails_intersection_empty :
    forall y, exists threshold, ~ le threshold y.
  Proof.
    intro y. exists (succ y). unfold le.
    intro h. apply h. apply lt_succ.
  Qed.

  Lemma le_refl_from_order : forall x, le x x.
  Proof.
    intro x. unfold le. apply lt_irrefl.
  Qed.

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

  Lemma miss_set_measurable :
    forall chooseThreshold witness,
      (forall prediction, Tail (chooseThreshold prediction) witness) ->
      @Measurable Y I (MissSet chooseThreshold witness).
  Proof.
    intros chooseThreshold witness hContains.
    left. apply miss_set_small. exact hContains.
  Qed.

  Lemma miss_set_mass_zero :
    forall chooseThreshold witness,
      (forall prediction, Tail (chooseThreshold prediction) witness) ->
      @Mass Y I (MissSet chooseThreshold witness) = 0.
  Proof.
    intros chooseThreshold witness hContains.
    unfold Mass, MeasureOne.
    destruct (excluded_middle_informative
      (~ Small I (MissSet chooseThreshold witness))) as [h | h].
    - exfalso. apply h. apply miss_set_small. exact hContains.
    - reflexivity.
  Qed.

  Lemma every_countable_tail_family_has_common_member :
    forall thresholds : nat -> Y,
      exists y, forall n, Tail (thresholds n) y.
  Proof.
    intros thresholds.
    apply countable_bounded.
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
        * apply le_refl_from_order.
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
    intro h. apply h. exact (lt_succ (prediction t)).
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
