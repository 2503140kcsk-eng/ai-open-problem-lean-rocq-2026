From Stdlib Require Import Arith Lia.

(* Integer-scaled asymptotic definitions for natural-valued regret profiles. *)
Definition IsSublinear (r : nat -> nat) : Prop :=
  forall a b : nat,
    0 < a -> 0 < b ->
    exists N : nat, forall T : nat, N <= T -> b * r T < a * T.

Definition IsLinear (r : nat -> nat) : Prop :=
  exists a b N : nat,
    0 < a /\
    0 < b /\
    forall T : nat, N <= T -> a * T <= b * r T.

(* A single profile cannot be both o(T) and Omega(T). *)
Lemma sublinear_not_linear :
  forall r : nat -> nat, ~(IsSublinear r /\ IsLinear r).
Proof.
  intros r [Hsub [a [b [N [Ha [Hb Hlin]]]]]].
  destruct (Hsub a b Ha Hb) as [N' Hsub'].
  pose (T := Nat.max N N').
  assert (HN : N <= T).
  { unfold T. apply Nat.le_max_l. }
  assert (HN' : N' <= T).
  { unfold T. apply Nat.le_max_r. }
  specialize (Hlin T HN).
  specialize (Hsub' T HN').
  lia.
Qed.

(* A target family is one predicate F over hypotheses, fixed for all rounds. *)
Definition Consistent (excluded : nat -> nat) (h : nat -> nat) : Prop :=
  forall t, h t <> excluded t.

Definition Allowed (excluded : nat -> nat) (t y : nat) : Prop :=
  y <> excluded t.

Definition ValuesAt (excluded : nat -> nat) (t y : nat) : Prop :=
  exists h, Consistent excluded h /\ h t = y.

Definition GloballyConsistent (excluded : nat -> nat) : Prop :=
  (exists h, Consistent excluded h) /\
  forall t y, ValuesAt excluded t y <-> Allowed excluded t y.

(* All rounds share one target family: functions avoiding the entire sequence. *)
Lemma complement_singletons_globally_consistent :
  forall excluded : nat -> nat, GloballyConsistent excluded.
Proof.
  intros excluded.
  split.
  - exists (fun t => S (excluded t)).
    unfold Consistent.
    intros t.
    lia.
  - intros t y.
    unfold ValuesAt, Consistent, Allowed.
    split.
    + intros [h [Hh Hvalue]].
      subst y.
      apply Hh.
    + intro Hy.
      exists (fun s => if Nat.eq_dec s t then y else S (excluded s)).
      split.
      * intros s.
        destruct (Nat.eq_dec s t) as [Heq | Hneq].
        -- subst s. exact Hy.
        -- simpl. lia.
      * simpl.
        destruct (Nat.eq_dec t t); congruence.
Qed.

Fixpoint TotalLoss (T : nat) (excluded prediction : nat -> nat) : nat :=
  match T with
  | 0 => 0
  | S n =>
      TotalLoss n excluded prediction +
        (if Nat.eq_dec (prediction n) (excluded n) then 1 else 0)
  end.

(* This is an all-horizons pathwise statement, not a claim about randomized regret. *)
Lemma matched_path_loss :
  forall T : nat, forall path : nat -> nat, TotalLoss T path path = T.
Proof.
  induction T as [|T IH]; intros path; simpl.
  - reflexivity.
  - rewrite IH.
    destruct (Nat.eq_dec (path T) (path T)); [lia | contradiction].
Qed.

(* The desired public-setting separation is not established by these lemmas. *)
Definition AsymptoticSeparationSpec
    (DeterministicLearner : Type)
    (randomizedRegret : nat -> nat)
    (deterministicRegret : DeterministicLearner -> nat -> nat) : Prop :=
  IsSublinear randomizedRegret /\
  forall learner : DeterministicLearner, IsLinear (deterministicRegret learner).
