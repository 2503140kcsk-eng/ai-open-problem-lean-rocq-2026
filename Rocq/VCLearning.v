(* Machine-checked threshold shattering lemmas in Rocq 9.2.
   The information-complexity / eCMI result remains an open research target and
   is deliberately not represented as a theorem with a missing proof or vacuous conclusion here. *)

From Stdlib Require Import Arith Bool Lia.

Definition Concept (X : Type) := X -> bool.

(* Initial-segment threshold on nat: x is positive iff x < t. *)
Definition thresholdConcept (t : nat) : Concept nat :=
  fun x => Nat.ltb x t.

Definition ThresholdClass (h : Concept nat) : Prop :=
  exists t : nat, h = thresholdConcept t.

Definition ShattersSingleton (H : Concept nat -> Prop) (a : nat) : Prop :=
  forall label : bool, exists h, H h /\ h a = label.

Definition ShattersPair (H : Concept nat -> Prop) (a b : nat) : Prop :=
  forall first second : bool,
    exists h, H h /\ h a = first /\ h b = second.

(* Any label on a singleton is realized by a threshold. *)
Lemma thresholds_shatter_singleton :
  forall a, ShattersSingleton ThresholdClass a.
Proof.
  intros a label.
  destruct label.
  - exists (thresholdConcept (S a)).
    split.
    + exists (S a). reflexivity.
    + unfold thresholdConcept. apply Nat.ltb_lt. lia.
  - exists (thresholdConcept a).
    split.
    + exists a. reflexivity.
    + unfold thresholdConcept. apply Nat.ltb_ge. lia.
Qed.

(* If a < b, the forbidden labeling false,true cannot be realized by a threshold. *)
Lemma thresholds_not_shatter_pair :
  forall a b, a < b -> ~ ShattersPair ThresholdClass a b.
Proof.
  intros a b Hab Hshatters.
  destruct (Hshatters false true) as [h [Hclass [Ha Hb]]].
  destruct Hclass as [t Ht].
  subst h.
  unfold thresholdConcept in Ha, Hb.
  apply Nat.ltb_ge in Ha.
  apply Nat.ltb_lt in Hb.
  lia.
Qed.

Theorem threshold_class_dimension_one_pairwise :
  (forall a, ShattersSingleton ThresholdClass a) /\
  (forall a b, a < b -> ~ ShattersPair ThresholdClass a b).
Proof.
  split.
  - exact thresholds_shatter_singleton.
  - exact thresholds_not_shatter_pair.
Qed.

