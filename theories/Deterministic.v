Require Import Grisette.Eval.
Require Import Grisette.SymBoolOp.
Require Import Grisette.Invariant.
Require Import Grisette.Union.
Require Import Grisette.GeneralTactics.
Require Import Grisette.MergingStrategy.
Require Import Grisette.SubStrategy.
Require Import Lia.
Require Import Coq.Arith.PeanoNat.

Ltac remove_star :=
  match goal with
  | [ H: MrgIf _ _ _ _ ==>(_)* EvalValue _ _ |- _] => apply eval_star_mrgif in H
  | [ H: SSMrgIf _ _ _ _ ==>(_)* EvalValue _ _ |- _ ] => apply eval_star_ss in H
  | [ H: ISMrgIf _ _ _ _ ==>(_)* EvalValue _ _ |- _ ] => apply eval_star_is in H
  | [ H: SIMrgIf _ _ _ _ ==>(_)* EvalValue _ _ |- _ ] => apply eval_star_si in H
  | [ H: IIMrgIf _ _ _ _ ==>(_)* EvalValue _ _ |- _ ] => apply eval_star_ii in H
  end.

Ltac find_same :=
  match goal with
    | [ H1 : ?x = _, H2 : ?x = _ |- _ ] => rewrite H1 in H2; invcd H2
    | [ H1 : ?x = _, H2 : _ = ?x |- _ ] => rewrite H1 in H2; invcd H2
    | [ H1 : _ = ?x, H2 : _ = ?x |- _ ] => rewrite <- H1 in H2; invcd H2
  end.

Lemma union_sub_rewrite_t :
  forall {T} c (t1 t2 f : Union T), If c t1 f = If c t2 f <-> t1 = t2.
Proof.
  intros.
  split; intros.
  invcd H; auto.
  subst. auto.
Qed.

Lemma union_sub_rewrite_f :
  forall {T} c (t f1 f2 : Union T), If c t f1 = If c t f2 <-> f1 = f2.
Proof.
  intros.
  split; intros.
  invcd H; auto.
  subst. auto.
Qed.

Lemma union_sub_rewrite_tf :
  forall {T} c (t1 t2 f1 f2 : Union T), If c t1 f1 = If c t2 f2 <-> t1 = t2 /\ f1 = f2.
Proof.
  intros.
  split; intros.
  invcd H; auto.
  intuition; subst; auto.
Qed.

Theorem determinstic': forall {T n t} {ms : MergingStrategy T n} {step1 step2},
  EvalTermsGood ms t ->
  forall {u1 u2},
  t ==>(step1)* (EvalValue ms u1) ->
  t ==>(step2)* (EvalValue ms u2) ->
  u1 = u2 /\ step1 = step2.
Proof.
  intros.
  assert (good:exists n1 (ms1 : MergingStrategy T n1), EvalTermsGood ms1 t).
  { exists n, ms. assumption. }
  generalize dependent n.
  generalize dependent u1.
  generalize dependent u2.
  generalize dependent step1.
  generalize dependent step2.
  apply EvalTerms_ind' with (t := t); intros; subst; eauto.
  all: inversion_initial_eval_good; simpl in *; try solve [exfalso; eauto].
  all: repeat remove_star.
  { specialize (value_evaluate_to_value H1).
    specialize (value_evaluate_to_value H2).
    intros.
    intuition; try lia.
    invcd H6.
    invcd H3.
    auto.
  }
  { destruct b;
    invcd H3; simpl in *; try solve [exfalso; auto];
    invcd H4; simpl in *; try solve [exfalso; auto];
    auto.
  }
  { invcd H4; simpl in *; try solve [exfalso; auto]. 
    invcd H5; simpl in *; try solve [exfalso; auto]. 
    rewrite H12 in H14. invcd H14. auto.
  }
  1-4: invcd H3; simpl in *; try solve [exfalso; auto];
    invcd H4; simpl in *; try solve [exfalso; auto];
    destruct ms; simpl in *; try solve [exfalso; auto];
    assert (Hd:d + 1 = d0 + 1 <-> d + 0 = d0 + 0) by lia; rewrite Hd;
    eapply H1; eauto with eval; invcd H2; econstructor; eauto with union.
  Ltac preprocess :=
    match goal with
    | [ H1 : EvalTermsGood ?ms ?t,
        H2 : ?t ==>(_)* EvalValue ?ms ?u1,
        H3 : ?t ==>(_)* EvalValue ?ms ?u2 |- _ ] =>
      invcd H1; repeat remove_star; invcd H2; try solve_aiu; invcd H3; try solve_aiu;
      repeat aiu_simplify; repeat find_same
    end.
  all: preprocess; auto 1.

  Ltac try1 :=
    match goal with
    | [ H : forall step2 step1 u2 u1 n ms, _ -> _ ==>(step1)* _ -> _ ==>(step2)* _ -> u1 = u2 /\ step1 = step2 |- _] =>
      eapply H
    end.

  all: try solve [intuition; try lia; try f_equal; eauto].
  all: try solve [
    assert (Hd:d0 + 1 = d + 1 <-> d0 + 0 = d + 0) by lia; rewrite Hd;
    try rewrite union_sub_rewrite_t; try rewrite union_sub_rewrite_f;
    try1; eauto 2 with eval; econstructor; eauto 2 with union inv].

  (* SSEq *)
  { assert (Hd:d0 + 1 = d + 1 <-> d0 + 0 = d + 0) by lia; rewrite Hd;
    eapply H3; eauto with eval.
    assert (ProperStrategy P0 (SortedStrategy n ind sub0)) by eauto 2 with inv.
    specialize (all_in_union_left_most' H0); simpl; intros.
    specialize (proper_ms_sub_from_subfunc H4 H5 H2) as [Psub ?].
    assert (HieraricalMergingInv Psub s1 t0) by eauto 2 with subinv.
    assert (HieraricalMergingInv Psub s1 f) by eauto 2 with subinv.
    econstructor; eauto.
  }

  (* SIEq *)
  { assert (Hd:d0 + 1 = d + 1 <-> d0 + 0 = d + 0) by lia; rewrite Hd;
    rewrite union_sub_rewrite_t.
    eapply H5; eauto with eval.
    assert (ProperStrategy P0 (SortedStrategy n ind sub0)) by eauto 2 with inv.
    specialize (all_in_union_left_most' H0); simpl; intros.
    specialize (proper_ms_sub_from_subfunc H6 H7 H4) as [Psub ?].
    assert (HieraricalMergingInv Psub s1 t0) by eauto 2 with subinv.
    assert (HieraricalMergingInv Psub s1 ft) by eauto 3 with subinv inv.
    econstructor; eauto.
  }

  (* ISEq *)
  { assert (Hd:d0 + 1 = d + 1 <-> d0 + 0 = d + 0) by lia; rewrite Hd;
    rewrite union_sub_rewrite_t.
    eapply H5; eauto 2 with eval.
    assert (ProperStrategy P0 (SortedStrategy n ind sub0)) by eauto 2 with inv.
    specialize (all_in_union_left_most' H0); simpl; intros.
    specialize (proper_ms_sub_from_subfunc H6 H7 H4) as [Psub ?].
    assert (HieraricalMergingInv Psub s1 tt) by eauto 3 with subinv inv.
    assert (HieraricalMergingInv Psub s1 f) by eauto 2 with subinv.
    econstructor; eauto.
  }

  (* IIEq *)
  { assert ((t'0 = t' /\ d0 + 0 = d1 + 0) /\ (f'0 = f' /\ d3 + 0 = d2 + 0)).
    { split.
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
    intuition.
    - f_equal; auto.
    - lia.
  }
Qed.

