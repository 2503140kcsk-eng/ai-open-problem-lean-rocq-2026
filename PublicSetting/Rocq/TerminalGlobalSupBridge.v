From Stdlib Require Import Arith List.
Import ListNotations.

(*
  Independent Rocq check of the order-theoretic core of the terminal bridge.

  A value of beta : X -> nat is one fixed global target-threshold function.
  It is not reselected at each round.  The theorem proves that every such
  globally compatible function is bounded by the sum of predictable
  witness-section misses.  In universal-upper-bound form this is the
  order-theoretic content of the terminal supremum inequality.

  This file deliberately does not postulate a probability space, a
  measurable path payoff, or a conditional-expectation tower theorem.
  Those are checked separately in the Lean measure-theoretic development.

  The elementary proof uses only Nat.ltb reflection and monotonicity of
  addition; it deliberately avoids automation that could enlarge the
  axiom dependency set.
*)

Section TerminalGlobalSupBridge.

  Context {X : Type}.

  Record PublicRound : Type := {
    round_context : X;
    round_witness : nat;
    round_prediction : nat
  }.

  Definition globallyCompatibleRound
      (beta : X -> nat) (r : PublicRound) : Prop :=
    beta (round_context r) <= round_witness r.

  Definition oneGlobalFamilyRoundLoss
      (beta : X -> nat) (r : PublicRound) : nat :=
    if Nat.ltb (round_prediction r) (beta (round_context r))
    then 1 else 0.

  Definition predictableRoundMiss (r : PublicRound) : nat :=
    if Nat.ltb (round_prediction r) (round_witness r)
    then 1 else 0.

  Fixpoint terminalLossForOneGlobalFamily
      (trace : list PublicRound) (beta : X -> nat) : nat :=
    match trace with
    | [] => 0
    | r :: rest =>
        oneGlobalFamilyRoundLoss beta r +
        terminalLossForOneGlobalFamily rest beta
    end.

  Fixpoint predictableMissCount (trace : list PublicRound) : nat :=
    match trace with
    | [] => 0
    | r :: rest =>
        predictableRoundMiss r + predictableMissCount rest
    end.

  Lemma one_global_family_round_loss_le_predictable
      (beta : X -> nat) (r : PublicRound) :
    globallyCompatibleRound beta r ->
    oneGlobalFamilyRoundLoss beta r <= predictableRoundMiss r.
  Proof.
    intro Hcompatible.
    unfold oneGlobalFamilyRoundLoss, predictableRoundMiss.
    destruct (Nat.ltb (round_prediction r)
      (beta (round_context r))) eqn:Hbeta.
    - apply Nat.ltb_lt in Hbeta.
      assert (Hmiss :
        Nat.ltb (round_prediction r) (round_witness r) = true).
      { apply Nat.ltb_lt.
        eapply Nat.lt_le_trans; [exact Hbeta | exact Hcompatible]. }
      rewrite Hmiss.
      apply Nat.le_refl.
    - destruct (Nat.ltb (round_prediction r) (round_witness r))
        eqn:Hmiss; simpl.
      + apply Nat.le_0_l.
      + apply Nat.le_refl.
  Qed.

  Theorem terminal_one_global_family_loss_le_predictable_miss_count :
    forall (trace : list PublicRound) (beta : X -> nat),
      Forall (globallyCompatibleRound beta) trace ->
      terminalLossForOneGlobalFamily trace beta <=
        predictableMissCount trace.
  Proof.
    induction trace as [|r rest IH].
    - intros beta Hcompat. reflexivity.
    - intros beta Hcompat.
      inversion Hcompat as [|r' rest' Hr Hrest]; subst.
      simpl.
      apply Nat.add_le_mono.
      + exact (one_global_family_round_loss_le_predictable beta r Hr).
      + exact (IH beta Hrest).
  Qed.

  Definition terminalSupremumBounded
      (trace : list PublicRound) (budget : nat) : Prop :=
    forall beta : X -> nat,
      Forall (globallyCompatibleRound beta) trace ->
      terminalLossForOneGlobalFamily trace beta <= budget.

  Theorem single_global_family_terminal_supremum_bound :
    forall trace,
      terminalSupremumBounded trace (predictableMissCount trace).
  Proof.
    intros trace beta Hcompatible.
    exact (terminal_one_global_family_loss_le_predictable_miss_count
      trace beta Hcompatible).
  Qed.

  Print Assumptions terminal_one_global_family_loss_le_predictable_miss_count.
  Print Assumptions single_global_family_terminal_supremum_bound.

End TerminalGlobalSupBridge.
