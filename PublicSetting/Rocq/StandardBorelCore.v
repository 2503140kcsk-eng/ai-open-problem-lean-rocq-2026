From Stdlib Require Import Reals.

Open Scope R_scope.

(*
  The measure-theoretic/Fubini content is exposed as an explicit interface.
  Lean's StandardBorelCore.lean proves the product-measurable transitive
  relation core using Mathlib product measure.

  In the standard-Borel application, universal measurability of the
  coanalytic core relation supplies relationMeasurable after completion of
  the product probability measure. This Rocq file checks the transitivity /
  majority argument; it does NOT formalize the Suslin projection theorem or
  construct the completed product measure.
*)

Section StandardBorelCore.
  Context {Y Theta : Type}.
  Variable mass : (Y -> Prop) -> R.
  Variable relationMeasurable : (Y -> Y -> Prop) -> Prop.

  Hypothesis fubini_majority :
    forall R : Y -> Y -> Prop,
      relationMeasurable R ->
      (forall y, mass (fun x => R x y) > 1 / 2) ->
      exists x, mass (fun y => R x y) > 1 / 2.

  Hypothesis majority_sections_intersect :
    forall A B : Y -> Prop,
      mass A > 1 / 2 ->
      mass B > 1 / 2 ->
      exists z, A z /\ B z.

  Definition coreRelation (sets : Theta -> Y -> Prop) (x y : Y) : Prop :=
    forall theta, sets theta y -> sets theta x.

  Lemma coreRelation_transitive :
    forall (sets : Theta -> Y -> Prop) x z y,
      coreRelation sets x z ->
      coreRelation sets z y ->
      coreRelation sets x y.
  Proof.
    intros sets x z y hxz hzy theta hy.
    apply hxz.
    apply hzy.
    exact hy.
  Qed.

  Theorem standard_borel_core_point :
    forall (sets : Theta -> Y -> Prop),
      relationMeasurable (coreRelation sets) ->
      (forall y, mass (fun x => coreRelation sets x y) > 1 / 2) ->
      exists x0, forall y, coreRelation sets x0 y.
  Proof.
    intros sets hmeas hlarge.
    destruct (fubini_majority (coreRelation sets) hmeas hlarge)
      as [x0 hout].
    exists x0.
    intro y.
    destruct
      (majority_sections_intersect
        (fun z => coreRelation sets x0 z)
        (fun z => coreRelation sets z y)
        hout (hlarge y))
      as [z [hxz hzy]].
    exact (coreRelation_transitive sets x0 z y hxz hzy).
  Qed.

  Theorem standard_borel_universal_acceptable_point :
    forall (sets : Theta -> Y -> Prop),
      relationMeasurable (coreRelation sets) ->
      (forall y, mass (fun x => coreRelation sets x y) > 1 / 2) ->
      exists x0,
        forall theta, (exists y, sets theta y) -> sets theta x0.
  Proof.
    intros sets hmeas hlarge.
    destruct (standard_borel_core_point sets hmeas hlarge)
      as [x0 hall].
    exists x0.
    intros theta [y hy].
    exact (hall y theta hy).
  Qed.

End StandardBorelCore.

Print Assumptions standard_borel_universal_acceptable_point.
