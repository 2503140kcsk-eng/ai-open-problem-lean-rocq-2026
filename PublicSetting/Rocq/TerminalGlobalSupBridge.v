From Stdlib Require Import Arith List.
Import ListNotations.

(*
  Independent Rocq check of the order-theoretic core of the terminal bridge.

  The label type and its strict/non-strict relations are parameters.  The
  only order law used is lt_le_trans, and decidable comparison is an explicit
  parameter rather than an imported classical axiom.

  One beta : X -> Label is fixed for the entire trace.  It is never selected
  afresh at each round.  The proof establishes that every globally
  compatible beta has terminal trace loss bounded by the predictable
  witness-miss count.

  This file does not assert a probability space, measurability, an upper
  integral, or a conditional-expectation tower theorem.  Those analytic
  statements remain in the Lean development.
*)

Section TerminalGlobalSupBridge.

  Context {X Label : Type}.
  Context (lt le : Label -> Label -> Prop).
  Context (lt_dec : forall a b, {lt a b} + {~ lt a b}).

  Hypothesis lt_le_trans :
    forall a b c, lt a b -> le b c -> lt a c.

  Record PublicRound : Type := {
    round_context : X;
    round_witness : Label;
    round_prediction : Label
  }.

  Definition globallyCompatibleRound
      (beta : X -> Label) (r : PublicRound) : Prop :=
    le (beta (round_context r)) (round_witness r).

  Definition oneGlobalFamilyRoundLoss
      (beta : X -> Label) (r : PublicRound) : nat :=
    if lt_dec (round_prediction r) (beta (round_context r))
    then 1 else 0.

  Definition predictableRoundMiss (r : PublicRound) : nat :=
    if lt_dec (round_prediction r) (round_witness r)
    then 1 else 0.

  Fixpoint terminalLossForOneGlobalFamily
      (trace : list PublicRound) (beta : X -> Label) : nat :=
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
      (beta : X -> Label) (r : PublicRound) :
    globallyCompatibleRound beta r ->
    oneGlobalFamilyRoundLoss beta r <= predictableRoundMiss r.
  Proof.
    intro Hcompatible.
    unfold oneGlobalFamilyRoundLoss, predictableRoundMiss.
    destruct (lt_dec (round_prediction r)
      (beta (round_context r))) as [Hbeta | Hnotbeta].
    - destruct (lt_dec (round_prediction r) (round_witness r))
        as [Hmiss | Hnotmiss].
      + simpl. apply Nat.le_refl.
      + exfalso.
        apply Hnotmiss.
        eapply lt_le_trans; eassumption.
    - destruct (lt_dec (round_prediction r) (round_witness r));
        simpl.
      + apply Nat.le_0_l.
      + apply Nat.le_refl.
  Qed.

  Theorem terminal_one_global_family_loss_le_predictable_miss_count :
    forall (trace : list PublicRound) (beta : X -> Label),
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
    forall beta : X -> Label,
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
