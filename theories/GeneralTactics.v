Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.Peano_dec.

Ltac clear_id :=
  match goal with
  | [ H : ?x = ?x |- _ ] => clear H
  end.

Ltac invc H := inversion H; subst; clear H; repeat clear_id.

Ltac invc_existT :=
  match goal with
  | [ H : existT _ ?n _ = existT _ ?n _ |- _ ] =>
    match type of n with
    | nat => apply inj_pair2_eq_dec in H; [ invc H | apply eq_nat_dec ]
    end
  end.

Ltac invcd H :=
  invc H; subst; repeat invc_existT.

Ltac inversiond H :=
  inversion H; subst; repeat invc_existT.
