From Stdlib Require Import ClassicalDescription FunctionalExtensionality PropExtensionality.
From PublicSetting Require Import OmegaOneSeparation.

(*
  Exact-realizability obstruction for the countable-cocountable law.

  This file does NOT approximate or replace the target measure. It proves
  that a sampler whose output range is countable cannot have that law as its
  pushforward: the target assigns mass 0 to its range, while every source
  probability measure assigns mass 1 to the preimage of the range.

  The result applies to finite-seed PRNGs, countable seed spaces, and
  terminating algorithms whose formal output representation is countable.
*)

Section CountableSupportObstruction.
  Context {Y : Type}.
  Variable I : @CountableIdeal Y.

  Hypothesis singleton_small :
    forall y : Y, Small I (fun z : Y => z = y).

  Variable M : Type.
  Variable zero one : M.
  Hypothesis one_neq_zero : one <> zero.

  Definition TargetMass (A : Y -> Prop) : M :=
    if excluded_middle_informative (Small I A) then zero else one.

  Definition NatRange (f : nat -> Y) : Y -> Prop :=
    fun y => exists n, y = f n.

  Lemma nat_range_small (f : nat -> Y) :
    Small I (NatRange f).
  Proof.
    unfold NatRange.
    apply (small_countable_union I (fun n y => y = f n)).
    intro n.
    exact (singleton_small (f n)).
  Qed.

  Definition SeedRange {Seed : Type} (sample : Seed -> Y) : Y -> Prop :=
    fun y => exists seed, y = sample seed.

  Lemma seed_range_small_of_enumeration
      {Seed : Type} (enum : nat -> Seed)
      (covers : forall seed, exists n, enum n = seed)
      (sample : Seed -> Y) :
    Small I (SeedRange sample).
  Proof.
    unfold SeedRange.
    eapply (small_mono I
      (fun y => exists seed, y = sample seed)
      (NatRange (fun n => sample (enum n)))).
    - intros y [seed hy].
      destruct (covers seed) as [n hn].
      exists n.
      rewrite hn.
      exact hy.
    - apply nat_range_small.
  Qed.

  Lemma target_mass_zero_of_small
      (A : Y -> Prop) (hA : Small I A) :
    TargetMass A = zero.
  Proof.
    unfold TargetMass.
    destruct (excluded_middle_informative (Small I A)); [reflexivity|].
    contradiction.
  Qed.

  Definition PushforwardMass {Seed : Type}
      (sourceMass : (Seed -> Prop) -> M)
      (sample : Seed -> Y) (A : Y -> Prop) : M :=
    sourceMass (fun seed => A (sample seed)).

  Lemma pushforward_mass_of_seed_range
      {Seed : Type} (sourceMass : (Seed -> Prop) -> M)
      (source_total : sourceMass (fun _ : Seed => True) = one)
      (sample : Seed -> Y) :
    PushforwardMass sourceMass sample (SeedRange sample) = one.
  Proof.
    unfold PushforwardMass, SeedRange.
    assert (hpre :
      (fun seed : Seed => exists y, sample seed = sample y) =
      (fun _ : Seed => True)).
    {
      apply functional_extensionality.
      intro seed.
      apply propositional_extensionality.
      split.
      - intros _. constructor.
      - intros _. exists seed. reflexivity.
    }
    rewrite hpre.
    exact source_total.
  Qed.

  Theorem no_enumerable_seed_sampler_realizes_target
      {Seed : Type} (enum : nat -> Seed)
      (covers : forall seed, exists n, enum n = seed)
      (sourceMass : (Seed -> Prop) -> M)
      (source_total : sourceMass (fun _ : Seed => True) = one)
      (sample : Seed -> Y) :
    PushforwardMass sourceMass sample (SeedRange sample) <>
      TargetMass (SeedRange sample).
  Proof.
    assert (hsmall : Small I (SeedRange sample)).
    {
      eapply seed_range_small_of_enumeration.
      exact covers.
    }
    rewrite (pushforward_mass_of_seed_range sourceMass source_total sample).
    rewrite (target_mass_zero_of_small (SeedRange sample) hsmall).
    exact one_neq_zero.
  Qed.

  Theorem target_mass_of_sampler_range_is_zero
      {Seed : Type} (enum : nat -> Seed)
      (covers : forall seed, exists n, enum n = seed)
      (sample : Seed -> Y) :
    TargetMass (SeedRange sample) = zero.
  Proof.
    apply target_mass_zero_of_small.
    exact (seed_range_small_of_enumeration enum covers sample).
  Qed.
End CountableSupportObstruction.
