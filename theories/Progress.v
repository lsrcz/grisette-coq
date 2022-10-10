Require Import Grisette.Union.
Require Import Grisette.SymBoolOp.
Require Import Grisette.MergingStrategy.
Require Import Grisette.SubStrategy.
Require Import Grisette.Invariant.
Require Import Grisette.SubStrategyInvariant.
Require Import Grisette.Eval.
Require Import Grisette.GeneralTactics.
Require Import Grisette.CpdtTactics.
Require Import Lia.
Require Import Coq.ZArith.BinInt.
Open Scope Z.
Open Scope nat.

Create HintDb progress discriminated.

Lemma hm_both_sup_p : forall {T} {P Psub} {n nsub} {ms : MergingStrategy T n}
  {mssub : MergingStrategy T nsub} {i} {u},
  SubStrategy Psub P i mssub ms ->
  HieraricalMergingInv Psub mssub u ->
  AllInUnion P u.
Proof.
  intros.
  induction u.
  - invcd H0. constructor. eapply proper_ms_sub_p; eauto.
  - constructor; eauto with inv. 
Qed.

Theorem progress : forall {T n t} {ms : MergingStrategy T n},
  EvalTermsGood ms t ->
  (exists u, t ==>* (EvalValue ms u) /\ EvalTermsGood ms (EvalValue ms u)).
Proof.
  intros.
  assert (good:exists n1 (ms1 : MergingStrategy T n1), EvalTermsGood ms1 t) by (repeat eexists; eauto).
  generalize dependent n.
  apply EvalTerms_ind' with (t := t); intros; subst; eauto.
  all: inversion_initial_eval_good; simpl in *; try solve [exfalso; eauto].
  (* EvalValue *)
  { repeat eexists; eauto with eval. }
  (* MrgIf concrete *)
  { destruct b; repeat eexists; eauto with eval. }
  (* MrgIf simple *)
  { repeat eexists; eauto.
    econstructor; econstructor; eauto.
    invcd H7.
    invcd H11.
    invcd H7. specialize (H5 c _ _ H9 H10).
    econstructor; econstructor; eauto.
    destruct H5. intuition.
    rewrite H5 in H0. invcd H0. eauto.
  }
  Ltac specialize_sorted_ms :=
    match goal with
    | [ H : is_sorted_strategy ?ms |- _] => destruct ms; simpl in H; [exfalso; auto | ]; intuition
    end.
  Ltac specialize_ih_mrgif_dispatch :=
    match goal with
    | [ H : forall n0 ms0, EvalTermsGood ms0 (?hd ?ms ?c ?t ?f) -> exists _, _ |- exists _, _] =>
      let H1 := fresh "H" in
      let u := fresh "u" in
      specialize (H _ ms);
      assert (H1:EvalTermsGood ms (hd ms c t f)) by (econstructor; eauto with eval inv union);
      specialize (H H1) as [u [? ?]]; exists u
    end.
  (* MrgIf dispatch *)
  1-4: specialize_sorted_ms;
    specialize_ih_mrgif_dispatch;
    econstructor; eauto with eval.
  (* SSLt *)
  { exists (If c t0 f); eauto.
    econstructor; econstructor; eauto with eval.
    assert (ProperStrategy P (SortedStrategy n ind sub)) by eauto with inv.
    assert (exists n (s : MergingStrategy T n) ev, sub ti = Some (MSSubLt s ev))
      as [n' [s' [H5 H5']]] by eauto with strategy.
    specialize (hm_sub_st H5 H0 H5' et) as [P1 ?].
    eapply HMSortedI; eauto with inv strategy union.
  }
  (* SSEq *)
  { inversiond H4.
    specialize (hm_sub_st ev H0 H2 et) as [P1 ?].
    specialize (hm_sub_st ev H1 H2 ef) as [P2 ?].
    assert (HieraricalMergingInv P1 s f) by eauto with inv.
    assert (EvalTermsGood s (MrgIf s c t0 f)) by (econstructor; eauto).
    specialize (H3 _ _ H8) as [u [H8' H8'']].
    assert (SSMrgIf (SortedStrategy n ind sub0) c t0 f ==>* EvalValue (SortedStrategy n ind sub0) u)
      by (econstructor; eauto with eval).
    exists u.
    intuition.
    invc H8''. assert (ProperStrategy P (SortedStrategy n ind sub0)) by eauto with inv.
    assert (ProperStrategy P3 s) by eauto with inv.
    specialize (all_in_union_left_most' H0); simpl; intros.
    econstructor.
    eapply hm_sup_hm; eauto.
    econstructor; eauto.
  }
  (* SSGt *)
  { exists (If (pnegsb c) f t0); eauto.
    econstructor; econstructor; eauto with eval.
    assert (ProperStrategy P (SortedStrategy n ind sub)) by eauto with inv.
    assert (exists n (s : MergingStrategy T n) ev, sub fi = Some (MSSubLt s ev))
      as [n' [s' [H5 H5']]] by eauto with strategy.
    specialize (hm_sub_st H5 H1 H5' ef) as [P1 ?].
    eapply HMSortedI; eauto with inv strategy union.
  }
  (* SIDeg *)
  { assert (EvalTermsGood (SortedStrategy n ind sub) (SSMrgIf (SortedStrategy n ind sub) c t0 f)).
    { econstructor; eauto with eval union. }
    specialize (H1 _ _ H3) as [u [H3' H3'']].
    exists u.
    intuition.
    econstructor; econstructor; eauto.
  }
  (* SILt *)
  { assert (EvalTermsGood (SortedStrategy n ind sub) (EvalValue (SortedStrategy n ind sub) (If c t0 (If fc ft ff)))).
    { econstructor. eapply hm_if_no_deg; simpl; eauto with inv.
      eapply (all_in_union_left_most' H1). }
    exists (If c t0 (If fc ft ff)).
    intuition.
    econstructor.
    eapply SILt; eauto.
    econstructor; eauto.
  }
  (* SIEq *)
  { assert (SubUnion ft (If fc ft ff)) by eauto with union.
    assert (ef0:HieraricalMergingInv P (SortedStrategy n ind sub) ft) by eauto with inv.
    inversiond ef; repeat aiu_simplify.
    - specialize (all_in_union_left_most' H9); simpl; intro.
      rewrite H2 in H12. invc H12. lia.
    - rewrite H20 in H4. invcd H4.
      clear ev.
      specialize (hm_sub_st ev0 H1 H20 ef0) as [P1 ?].
      specialize (hm_sub_st ev0 H0 H20 et) as [P2 ?].
      assert (HieraricalMergingInv P1 s t0) by eauto with inv.
      clear P2 H12.
      assert (EvalTermsGood s (MrgIf s c t0 ft)).
      { econstructor; eauto with eval. }
      specialize (H5 _ _ H12) as [u [H5' H5'']].
      exists (If (porsb c fc) u ff).
      intuition.
      econstructor.
      eapply SIEq; eauto.
      constructor.

      assert (SubStrategy P1 P z s (SortedStrategy n ind sub)).
      { specialize (all_in_union_left_most' H0); simpl; intros.
        econstructor; eauto with inv. }
      invcd H5''.
      assert (HieraricalMergingInv P1 s u) by eauto with inv.
      clear P0 H19.

      econstructor.
      eapply HMSortedI; eauto; try solve_aiu.

      specialize (hm_sup_all_in_union_ind H5 H15); repeat aiu_simplify.
      auto.
  }
  (* SIGt *)
  { assert (SubUnion ft (If fc ft ff)) by eauto with union.
    inversiond ef; repeat aiu_simplify.
    - specialize (all_in_union_left_most' H9); simpl; intro.
      rewrite H2 in H12. invc H12. lia.
    - assert (EvalTermsGood (SortedStrategy n ind sub) (MrgIf (SortedStrategy n ind sub) c t0 ff)).
      { econstructor; eauto with inv. }
      specialize (H5 _ _ H12) as [u [H5 H5']].
      exists (If (pandsb (pnegsb c) fc) ft u).
      intuition.
      { econstructor. eapply SIGt; eauto.
        constructor. 
      }
      invcd H5'.
      assert (HieraricalMergingInv P (SortedStrategy n ind sub) u) by eauto with inv.
      clear P0 H18.
      
      econstructor.
      eapply HMSortedI; repeat aiu_simplify; eauto with inv; try solve_aiu.
      eapply eval_do_not_change_index_lowerbound; eauto.

      constructor; solve_aiu.
  }
  (* ISDeg *)
  { assert (EvalTermsGood (SortedStrategy n ind sub) (SSMrgIf (SortedStrategy n ind sub) c t0 f)).
    { econstructor; eauto with eval union. }
    specialize (H1 _ _ H3) as [u [H3' H3'']].
    exists u.
    intuition.
    econstructor; econstructor; eauto.
  }
  (* ISLt *)
  { assert (EvalTermsGood (SortedStrategy n ind sub) (MrgIf (SortedStrategy n ind sub) c tf f)).
    { econstructor; eauto with eval union inv. }
    specialize (H5 _ _ H7) as [f' [H5 H5']].
    invcd H5'.
    assert (ProperStrategy P (SortedStrategy n ind sub)) by eauto with inv.
    specialize (all_in_union_left_most' H0); simpl; intros.
    specialize (proper_ms_ind_some_is_sub_some H8 H9) as [n' [ev' [s' ?]]].
    specialize (proper_ms_sub_from_subfunc H8 H9 H12) as [Psub ?].
    assert (HieraricalMergingInv P (SortedStrategy n ind sub) tt) by eauto with inv.
    assert (HieraricalMergingInv Psub s' tt) by eauto with subinv.
    exists (If (pandsb c tc) tt f').
    intuition.
    - econstructor. eapply ISLt; eauto. econstructor.
    - econstructor. eapply HMSortedI. 4: apply H12.
      all: repeat aiu_simplify; eauto. all: eauto 4 with inv.
      eapply eval_do_not_change_index_lowerbound; eauto.
      simpl. intuition; eauto 3 with union.
      invcd et; try solve_aiu.
      repeat aiu_simplify. assert (z = tfi) by eauto with union. lia.
  }
  (* ISEq *)
  { assert (ProperStrategy P (SortedStrategy n ind sub)) by eauto with inv.
    specialize (all_in_union_left_most' H1); simpl; intros.
    specialize (proper_ms_sub_from_subfunc H7 H8 H4) as [Psub ?].
    assert (HieraricalMergingInv P (SortedStrategy n ind sub) tt) by eauto with inv.
    assert (HieraricalMergingInv Psub s tt) by eauto with subinv.
    assert (EvalTermsGood s (MrgIf s c tt f)).
    { econstructor; eauto with subinv. }
    specialize (H5 _ _ H13) as [t' [H5 H5']].
    invcd H5'.
    assert (HieraricalMergingInv Psub s t') by eauto with inv.
    exists (If (porsb (pnegsb c) tc) t' tf).
    intuition.
    - econstructor. eapply ISEq; eauto. econstructor.
    - econstructor. eapply HMSortedI. 4: apply H4.
      all: repeat aiu_simplify; eauto. all: eauto 3 with inv.
      + eapply hm_both_sup_p; eauto.
      + eapply eval_do_not_change_index_sub_eq; simpl; eauto; intuition; eauto.
      + invcd et; try solve_aiu.
        repeat aiu_simplify. assert (z = tfi) by eauto 4 with union. lia.
  }
  (* ISGt *)
  { assert (EvalTermsGood (SortedStrategy n ind sub)
                          (EvalValue (SortedStrategy n ind sub) (If (pnegsb c) f (If tc tt tf)))).
    { econstructor. eapply hm_if_no_deg; simpl in *; eauto.
      exact (all_in_union_left_most' H0).
      lia.
    }
    specialize (H5 _ _ H7) as [u [H5 H5']]. 
    exists u.
    invcd_eval_value.
    intuition.
    econstructor. eapply ISGt; eauto. constructor.
  }

  (* IIDeg1 *)
  { assert (AllInUnion (fun x => AllInUnion (fun y => ind x = ind y) t0) t0) by eauto with union.
    assert (EvalTermsGood (SortedStrategy n ind sub) (SIMrgIf (SortedStrategy n ind sub) c t0 f)).
    { eauto with eval. }
    specialize (H1 _ _ H4) as [u [H1 H1']].
    exists u.
    intuition.
    econstructor. eapply IIDeg1; eauto. constructor.
  }

  (* IIDeg2 *)
  { assert (AllInUnion (fun x => AllInUnion (fun y => ind x = ind y) f) f) by eauto with union.
    assert (EvalTermsGood (SortedStrategy n ind sub) (ISMrgIf (SortedStrategy n ind sub) c (If tc tt tf) f)).
    { eauto with eval. }
    specialize (H4 _ _ H7) as [u [H4 H4']].
    exists u.
    intuition.
    econstructor. eapply IIDeg2; eauto. constructor.
  }

  (* IILt *)
  { assert (EvalTermsGood (SortedStrategy n ind sub)
                          (MrgIf (SortedStrategy n ind sub) c tf (If fc ft ff))).
    { econstructor; eauto with eval union inv. }
    specialize (H7 _ _ H9) as [f' [H7 H7']].
    exists (If (pandsb c tc) tt f').

    intuition.
    econstructor. eapply IILt; eauto. constructor.

    assert (ProperStrategy P (SortedStrategy n ind sub)) by eauto with inv.
    specialize (all_in_union_left_most' H0); simpl; intros.
    specialize (proper_ms_ind_some_is_sub_some H10 H11) as [n' [ev' [s' ?]]].
    specialize (proper_ms_sub_from_subfunc H10 H11 H12) as [Psub ?].
    assert (HieraricalMergingInv P (SortedStrategy n ind sub) tt) by eauto 3 with inv.
    assert (HieraricalMergingInv Psub s' tt) by eauto with subinv.
    invcd H7'.
    assert (HieraricalMergingInv P (SortedStrategy n ind sub) f') by eauto 3 with inv.

    econstructor. eapply HMSortedI; eauto; repeat aiu_simplify; eauto 3 with inv.
    eapply eval_do_not_change_index_lowerbound; eauto.
    simpl. intuition; eauto 3 with union.
    invcd et; try solve_aiu.
    repeat aiu_simplify. assert (z = tfi) by eauto with union. lia.

    eapply hm_lm_is_lowerbound; eauto.
    simpl. exact (all_in_union_left_most' H2).
  }

  (* IIEq *)
  { assert (EvalTermsGood (SortedStrategy n ind sub)
                          (MrgIf (SortedStrategy n ind sub) c tf ff)).
    { econstructor; eauto with eval union inv. }
    specialize (H8 _ _ H10) as [f' [H8 H8']].

    assert (ProperStrategy P (SortedStrategy n ind sub)) by eauto with inv.
    specialize (all_in_union_left_most' H0); simpl; intros.
    specialize (proper_ms_sub_from_subfunc H11 H12 H6) as [Psub ?].
    assert (HieraricalMergingInv P (SortedStrategy n ind sub) tt) by eauto 2 with inv.
    assert (HieraricalMergingInv Psub s tt) by eauto with subinv.
    assert (HieraricalMergingInv P (SortedStrategy n ind sub) ft) by eauto 2 with inv.
    assert (HieraricalMergingInv Psub s ft) by eauto with subinv.
    assert (EvalTermsGood s (MrgIf s c tt ft)).
    { econstructor; eauto with subinv. }
    specialize (H7 _ _ H21) as [t' [H7 H7']].
    exists (If (pitesb c tc fc) t' f').

    intuition.
    econstructor. eapply IIEq; eauto. constructor.

    invcd H8'.
    assert (HieraricalMergingInv P (SortedStrategy n ind sub) f') by eauto 3 with inv.
    invcd H7'.
    assert (HieraricalMergingInv Psub s t') by eauto 3 with inv.

    econstructor. eapply HMSortedI; eauto; repeat aiu_simplify; eauto 3 with inv.

    - eapply hm_both_sup_p; eauto.
    - eapply eval_do_not_change_index_sub_eq; simpl; eauto; intuition; eauto.
    - eapply eval_do_not_change_index_lowerbound; eauto.
      simpl. intuition; eauto 3 with union.
      + invcd et; try solve_aiu.
        repeat aiu_simplify. assert (z = tfi) by eauto 4 with union. lia.
      + invcd ef; try solve_aiu.
        repeat aiu_simplify. assert (z = ffi) by eauto 4 with union. lia.
  }

  (* IIGt *)
  { assert (EvalTermsGood (SortedStrategy n ind sub)
                          (MrgIf (SortedStrategy n ind sub) c (If tc tt tf) ff)).
    { econstructor; eauto with eval union inv. }
    specialize (H7 _ _ H9) as [f' [H7 H7']].
    exists (If (pandsb (pnegsb c) fc) ft f').

    assert (ProperStrategy P (SortedStrategy n ind sub)) by eauto with inv.
    specialize (all_in_union_left_most' H2); simpl; intros.
    specialize (proper_ms_ind_some_is_sub_some H10 H11) as [n' [ev' [s' ?]]].
    specialize (proper_ms_sub_from_subfunc H10 H11 H12) as [Psub ?].
    assert (HieraricalMergingInv P (SortedStrategy n ind sub) ft) by eauto 3 with inv.
    assert (HieraricalMergingInv Psub s' ft) by eauto with subinv.
    invcd H7'.
    assert (HieraricalMergingInv P (SortedStrategy n ind sub) f') by eauto 3 with inv.

    intuition.
    econstructor. eapply IIGt; eauto. constructor.

    econstructor. eapply HMSortedI; eauto; repeat aiu_simplify; eauto 3 with inv.
    eapply eval_do_not_change_index_lowerbound; eauto.
    simpl. intuition; eauto 3 with union.

    - assert (fti < tti)%Z by lia. eapply hm_lm_is_lowerbound; eauto.
      simpl. exact (all_in_union_left_most' H0). 

    - invcd ef; try solve_aiu.
      repeat aiu_simplify. assert (z = ffi) by eauto with union. lia.
  }
Qed.


  
  
  
