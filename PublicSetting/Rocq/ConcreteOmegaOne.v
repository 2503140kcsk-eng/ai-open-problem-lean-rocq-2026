From gaia Require Import sset11.

(**
 Concrete first uncountable ordinal adapter, based on Gaia's Bourbaki set
 theory development.

 The object below is the actual set of ordinals whose cardinality is at most
 omega.  It is not the abstract Schutte Ord parameter used by
 hydra-battles/Schutte.
*)

Module PublicSettingConcreteOmegaOne.

  Definition omegaOne : Set := Ordinals1.aleph_one.
  Definition isCountableOrdinal (a : Set) : Prop :=
    Ordinals1.countable_ordinal a.

  Theorem omegaOne_iff_countable_ordinal (a : Set) :
      inc a omegaOne <-> isCountableOrdinal a.
  Proof.
    exact (Ordinals1.aleph_oneP a).
  Qed.


  (* The supremum of a countable family of countable ordinals is again
     a countable ordinal. This is the regularity property needed to show
     that countable subsets of omegaOne are bounded below omegaOne. *)
  Theorem omegaOne_countable_sup (E : Set) :
      countable_set E ->
      (forall a, inc a E -> isCountableOrdinal a) ->
      isCountableOrdinal (\osup E).
  Proof.
    exact (Ordinals1.countable_ordinal_sup E).
  Qed.

End PublicSettingConcreteOmegaOne.

Print Assumptions PublicSettingConcreteOmegaOne.omegaOne_iff_countable_ordinal.
Print Assumptions PublicSettingConcreteOmegaOne.omegaOne_countable_sup.
