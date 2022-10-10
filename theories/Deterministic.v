Require Import Grisette.Eval.
Require Import Grisette.SymBoolOp.
Require Import Grisette.Invariant.
Require Import Grisette.Union.
Require Import Grisette.GeneralTactics.
Require Import Grisette.MergingStrategy.
Require Import Grisette.SubStrategy.
Require Import Lia.

Ltac remove_star :=
  match goal with
  | [ H: MrgIf _ _ _ _ ==>* EvalValue _ _ |- _] => apply eval_star_mrgif in H
  | [ H: SSMrgIf _ _ _ _ ==>* EvalValue _ _ |- _ ] => apply eval_star_ss in H
  | [ H: ISMrgIf _ _ _ _ ==>* EvalValue _ _ |- _ ] => apply eval_star_is in H
  | [ H: SIMrgIf _ _ _ _ ==>* EvalValue _ _ |- _ ] => apply eval_star_si in H
  | [ H: IIMrgIf _ _ _ _ ==>* EvalValue _ _ |- _ ] => apply eval_star_ii in H
  end.

Ltac find_same :=
  match goal with
    | [ H1 : ?x = _, H2 : ?x = _ |- _ ] => rewrite H1 in H2; invcd H2
    | [ H1 : ?x = _, H2 : _ = ?x |- _ ] => rewrite H1 in H2; invcd H2
    | [ H1 : _ = ?x, H2 : _ = ?x |- _ ] => rewrite <- H1 in H2; invcd H2
  end.

Theorem determinstic': forall {T n t} {ms : MergingStrategy T n},
  EvalTermsGood ms t ->
  forall {u1 u2},
  t ==>* (EvalValue ms u1) ->
  t ==>* (EvalValue ms u2) ->
  u1 = u2.
Proof.
  intros.
  assert (good:exists n1 (ms1 : MergingStrategy T n1), EvalTermsGood ms1 t).
  { exists n, ms. assumption. }
  generalize dependent n.
  generalize dependent u1.
  generalize dependent u2.
  apply EvalTerms_ind' with (t := t); intros; subst; eauto.
  all: inversion_initial_eval_good; simpl in *; try solve [exfalso; eauto].
  all: repeat remove_star.
  { specialize (value_evaluate_to_value H1).
    specialize (value_evaluate_to_value H2).
    intros.
    invcd H3.
    invcd H4.
    auto.
  }
  { destruct b;
    invcd H3; simpl in *; try solve [exfalso; auto];
    invcd H4; simpl in *; try solve [exfalso; auto];
    auto.
  }
  { invcd H4; simpl in *; try solve [exfalso; auto]. 
    invcd H5; simpl in *; try solve [exfalso; auto]. 
    rewrite H8 in H7. invcd H7. auto.
  }
  1-4: invcd H3; simpl in *; try solve [exfalso; auto];
    invcd H4; simpl in *; try solve [exfalso; auto]; 
    destruct ms; simpl in *; try solve [exfalso; auto];
    eapply H1; eauto with eval;
    invcd H2;
    econstructor; eauto with union.

  Ltac preprocess :=
    match goal with
    | [ H1 : EvalTermsGood ?ms ?t,
        H2 : ?t ==>* EvalValue ?ms ?u1,
        H3 : ?t ==>* EvalValue ?ms ?u2 |- _ ] =>
      invcd H1; repeat remove_star; invcd H2; try solve_aiu; invcd H3; try solve_aiu;
      repeat aiu_simplify; repeat find_same
    end.
  all: preprocess; auto 1.
  (* SSLt (auto) *)

  Ltac try1 :=
    match goal with
    | [ H : forall u2 u1 n ms, _ -> _ ==>* _ -> _ ==>* _ -> u1 = u2 |- _] =>
      eapply H
    end.

  all: try solve [try f_equal; try1; eauto 2 with eval; econstructor; eauto 2 with union inv].

  (* SSEq *)
  { eapply H3; eauto with eval.
    assert (ProperStrategy P0 (SortedStrategy n ind sub0)) by eauto 2 with inv.
    specialize (all_in_union_left_most' H0); simpl; intros.
    specialize (proper_ms_sub_from_subfunc H4 H5 H2) as [Psub ?].
    assert (HieraricalMergingInv Psub s1 t0) by eauto 2 with subinv.
    assert (HieraricalMergingInv Psub s1 f) by eauto 2 with subinv.
    econstructor; eauto.
  }

  (* SIEq *)
  { f_equal.
    eapply H5; eauto with eval.
    assert (ProperStrategy P0 (SortedStrategy n ind sub0)) by eauto 2 with inv.
    specialize (all_in_union_left_most' H0); simpl; intros.
    specialize (proper_ms_sub_from_subfunc H6 H7 H4) as [Psub ?].
    assert (HieraricalMergingInv Psub s1 t0) by eauto 2 with subinv.
    assert (HieraricalMergingInv Psub s1 ft) by eauto 3 with subinv inv.
    econstructor; eauto.
  }

  (* ISEq *)
  { f_equal.
    eapply H5; eauto 2 with eval.
    assert (ProperStrategy P0 (SortedStrategy n ind sub0)) by eauto 2 with inv.
    specialize (all_in_union_left_most' H0); simpl; intros.
    specialize (proper_ms_sub_from_subfunc H6 H7 H4) as [Psub ?].
    assert (HieraricalMergingInv Psub s1 tt) by eauto 3 with subinv inv.
    assert (HieraricalMergingInv Psub s1 f) by eauto 2 with subinv.
    econstructor; eauto.
  }

  (* IIEq *)
  { f_equal.
    - eapply H7; eauto 2 with eval.
      assert (ProperStrategy P0 (SortedStrategy n ind sub0)) by eauto 2 with inv.
      specialize (all_in_union_left_most' H0); simpl; intros.
      specialize (proper_ms_sub_from_subfunc H9 H10 H6) as [Psub ?].
      assert (HieraricalMergingInv Psub s1 tt) by eauto 3 with subinv inv.
      assert (HieraricalMergingInv Psub s1 ft) by eauto 3 with subinv inv.
      econstructor; eauto.
    - eapply H8; eauto 2 with eval.
      econstructor; eauto with inv.
   }
Qed.

