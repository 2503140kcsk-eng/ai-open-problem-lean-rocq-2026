From gaia Require Import sset11 sset14.

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
  Theorem omegaOne_countable_sup (E : Set)
      (hE : countable_set E)
      (hE_ord : forall a, inc a E -> isCountableOrdinal a) :
      isCountableOrdinal (\osup E).
  Proof.
    exact (Ordinals1.countable_ordinal_sup hE hE_ord).
  Qed.


  (* The first uncountable ordinal is genuinely uncountable.  Gaia proves
     that deleting the finite initial segment from aleph_one still has
     cardinal aleph_one; this contradicts countability of aleph_one. *)
  Theorem omegaOne_not_countable :
      ~ countable_set omegaOne.
  Proof.
    intro hCount.
    have hSub : sub Ordinals4.Cantor_Omega omegaOne.
    {
      move => z /setC_P [hz _].
      exact hz.
    }
    have hCantorCount : countable_set Ordinals4.Cantor_Omega :=
      countable_sub hSub hCount.
    move /countableP : hCantorCount => hCardLe.
    have hAlephLe : aleph0 <=c aleph0 := cleR CS_aleph0.
    have hStrict : aleph0 <c omegaOne.
    {
      rewrite /omegaOne - Ordinals4.Cantor_omega_pr3.
      rewrite - Ordinals4.aleph0E.
      exact (Ordinals4.aleph_lt_ltc OS0 OS1).
    }
    have hImpossible : omegaOne <=c aleph0.
    {
      rewrite - Ordinals4.Cantor_omega_pr2.
      exact hCardLe.
    }
    exact (ocltNge hStrict hImpossible).
  Qed.

End PublicSettingConcreteOmegaOne.

Print Assumptions PublicSettingConcreteOmegaOne.omegaOne_iff_countable_ordinal.
Print Assumptions PublicSettingConcreteOmegaOne.omegaOne_countable_sup.
