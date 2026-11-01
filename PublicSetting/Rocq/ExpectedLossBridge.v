From Stdlib Require Import Reals.

Open Scope R_scope.

(*
  Algebraic companion to the Lean ExpectedLossBridge module.
  Linearity of expectation and the tower identity are explicit interfaces.
  This checks finite-horizon aggregation independently in Rocq; it does not
  construct conditional expectation from a measure in Rocq.
*)

Section ExpectedLossBridge.
  Context {Omega : Type}.
  Variable expectation : (Omega -> R) -> R.
  Variable conditionalRisk : (Omega -> R) -> (Omega -> R).

  Hypothesis expectation_add :
    forall f g,
      expectation (fun omega => f omega + g omega) =
      expectation f + expectation g.

  Hypothesis tower_identity :
    forall f, expectation (conditionalRisk f) = expectation f.

  Fixpoint cumulativeLoss
      (T : nat) (loss : nat -> Omega -> R) : Omega -> R :=
    match T with
    | O => fun _ => 0
    | S n => fun omega => cumulativeLoss n loss omega + loss n omega
    end.

  Fixpoint cumulativeStageRisk
      (T : nat) (loss : nat -> Omega -> R) : Omega -> R :=
    match T with
    | O => fun _ => 0
    | S n =>
        fun omega =>
          cumulativeStageRisk n loss omega + conditionalRisk (loss n) omega
    end.

  Theorem expected_cumulative_loss_eq_expected_stagewise_risk :
    forall T loss,
      expectation (cumulativeStageRisk T loss) =
      expectation (cumulativeLoss T loss).
  Proof.
    induction T as [|T IH]; intros loss.
    - reflexivity.
    - change
        (expectation
          (fun omega =>
            cumulativeStageRisk T loss omega + conditionalRisk (loss T) omega) =
         expectation
          (fun omega => cumulativeLoss T loss omega + loss T omega)).
      rewrite
        (expectation_add (cumulativeStageRisk T loss)
          (conditionalRisk (loss T))).
      rewrite
        (expectation_add (cumulativeLoss T loss) (loss T)).
      rewrite (IH loss).
      rewrite (tower_identity (loss T)).
      reflexivity.
  Qed.

End ExpectedLossBridge.

Print Assumptions expected_cumulative_loss_eq_expected_stagewise_risk.
