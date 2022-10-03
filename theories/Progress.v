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

Definition all_in_et {T} P (et : EvalTerms T) : Prop :=
  match et with
  | EvalValue _ u => AllInUnion P u
  | MrgIf _ _ t f => AllInUnion P t /\ AllInUnion P f
  | SSMrgIf _ _ t f => AllInUnion P t /\ AllInUnion P f
  | SIMrgIf _ _ t f => AllInUnion P t /\ AllInUnion P f
  | ISMrgIf _ _ t f => AllInUnion P t /\ AllInUnion P f
  | IIMrgIf _ _ t f => AllInUnion P t /\ AllInUnion P f
  end.

#[global] Hint Unfold all_in_et : progress.

Lemma value_evaluate_to_value : forall {T n1 n2} {ms1 : MergingStrategy T n1}
  {ms2 : MergingStrategy T n2} {u1 u2},
  EvalValue ms1 u1 ==>* EvalValue ms2 u2 -> EvalValue ms1 u1 = EvalValue ms2 u2.
Proof.
  intros.
  invcd H; auto.
  invcd H0.
Qed.

Ltac invcd_eval_value :=
  match goal with
  | [ H: EvalValue ?ms1 ?r1 ==>* EvalValue ?ms2 ?r2 |- _] =>
    apply value_evaluate_to_value in H; invcd H
  end.

#[global] Hint Resolve value_evaluate_to_value : progress.

Ltac invcd_eval_rule H :=
  invcd H; simpl in *; try solve [exfalso; auto].

Theorem subrt_proper_sub : forall {T n1} {P1 P2} {n2} {sub : MergingStrategy T n1} {ms : MergingStrategy T n2},
  SubStrategyRT P1 P2 sub ms -> ProperStrategy P1 sub.
Proof.
  intros.
  invcd H; eauto with sub.
Qed.

#[global] Hint Resolve subrt_proper_sub : sub.


Theorem eval_do_not_change_index_subrt : forall {T n n1} {P ind sub} {i t} {Psub} {s : MergingStrategy T n1},
  ProperStrategy P (SortedStrategy n ind sub) ->
  SubStrategyRT Psub P s (SortedStrategy n ind sub) ->
  EvalTermsGood s t ->
  all_in_et (fun (x : T) => ind x = Some i) t ->
  forall u, t ==>* (EvalValue s u) ->
  AllInUnion (fun (x : T) => ind x = Some i) u.
Proof.
  intros.
  assert (good:exists n1 (ms1 : MergingStrategy T n1), EvalTermsGood ms1 t) by (repeat eexists; eauto).
  generalize dependent u.
  generalize dependent ind.
  generalize dependent sub.
  generalize dependent Psub.
  generalize dependent n1.
  apply EvalTerms_ind' with (t := t); intros; try invcd_eval_value; subst; eauto.
  { invcd H6. invcd_eval_rule H7;
    invcd_eval_value; intuition.
  }
  { clear t good.
    invcd H3.
    invcd H7. invcd_eval_rule H3.
    repeat invcd_eval_value.
    rewrite H14 in H0. invcd H0.
    invcd H6. invcd H0. invcd H3.
    eapply H1; clear H1; eauto; econstructor.
    - clear H5 H4 sub H2 H Psub. eauto with inv.
    - invcd H5.
      eapply proper_ms_subt_simple.
      4: apply H14.
      all: eauto.
  }
  1-4: destruct ms; simpl in H0; try solve [exfalso; auto];
    invcd H2; invcd H5; invcd H6; invcd H5; try solve [exfalso; auto];
    invcd_eval_value;
    eapply H1; simpl; eauto;
    econstructor; eauto; constructor; constructor; auto.
  { invcd H6. invcd H7. invcd H6; try solve_aiu.
    invcd_eval_value.
    solve_aiu.
  }
  { invcd H7. invcd H8. invcd H7; try solve_aiu.
    invcd_eval_value.
    assert (i0 = i1) by eauto with union.
    subst.
    rewrite H2 in H21. invcd H21.
    clear H19 H20.
    specialize (all_in_union_left_most' H0); simpl; intros.
    invcd H4.
    assert (ProperStrategy Psub (SortedStrategy n2 ind sub)) by eauto with sub.
    assert (ProperStrategy P0 (SortedStrategy n2 ind sub)) by eauto with inv.
    specialize (proper_ms_sub_from_subfunc H4 H7 H2) as [Psub' Hsub'].
    eapply H3; simpl in *.
    5: apply H22.
    all: eauto.
    - specialize (proper_ms_sub_from_subfunc H8 H7 H2) as [Psub'' Hsub''].
      econstructor; eapply hm_sub_hm; eauto.
    - eapply sub_subrt_subrt; eauto.
  }
  { invcd H6. invcd H7. invcd H6; try solve_aiu.
     invcd_eval_value.
     solve_aiu.
  }
  { invcd H5.
    invcd H6.
    invcd H5.
    { invcd_eval_value.
      eapply H1. 5: apply H18.
      all: simpl; eauto with eval union.
    }
    1-3: invcd H0;
      specialize (all_in_union_left_most' H12); simpl; intros;
      rewrite H19 in H0; invcd H0;
      solve_aiu.
  }
  1-3: invcd H6; clear H15 H21;
    invcd H9; invcd H11;
    invcd H10;
    invcd H9; try solve_aiu; [
      invcd H22;
      specialize (all_in_union_left_most' H16); simpl; intros;
      rewrite H9 in H2; invcd H2; solve_aiu |
      invcd_eval_value
    ].
  { eauto with union. }
  { assert (ti = ti0) by eauto with union. subst.
    rewrite H4 in H28. invcd H28.
    constructor; eauto.
    assert (HieraricalMergingInv P0 (SortedStrategy n0 ind sub1) ft) by eauto with inv.
    assert (ProperStrategy P0 (SortedStrategy n0 ind sub1)) by eauto with inv.
    specialize (all_in_union_left_most' H25); simpl; intro.
    assert (ProperStrategy Psub (SortedStrategy n0 ind sub1)) by eauto with sub.
    specialize (all_in_union_left_most' H0); simpl; intros.
    specialize (proper_ms_sub_from_subfunc H12 H14 H4) as [Psub' Hsub'].
    eapply H5. 5: apply H29.
    all: simpl; eauto.
    - specialize (proper_ms_sub_from_subfunc H10 H11 H4) as [Psub'' Hsub''].
      econstructor; eapply hm_sub_hm; eauto.
    - eapply sub_subrt_subrt; eauto.
  }
  { assert (ti0 = ti) by eauto with union.
    assert (fti0 = fti) by eauto with union.
    subst.
    rewrite H26 in H2. invcd H2.
    constructor; eauto.
    assert (HieraricalMergingInv P0 (SortedStrategy n0 ind sub1) ff) by eauto with inv.

    eapply H5. 5: apply H29.
    all: simpl; eauto.
    econstructor; eauto.
  }
Admitted.

Theorem eval_do_not_change_index : forall {T n} {ind sub} {i t},
  EvalTermsGood (SortedStrategy n ind sub) t ->
  all_in_et (fun (x : T) => ind x = Some i) t ->
  forall u, t ==>* (EvalValue (SortedStrategy n ind sub) u) ->
  AllInUnion (fun (x : T) => ind x = Some i) u.
Proof.
  intros.
  specialize (good_implies_proper_strategy H) as [Psub Hsub].
  eapply eval_do_not_change_index_subrt; eauto.
  eapply Subrt_refl. eauto.
Qed.


(*
Theorem eval_do_not_change_index' : forall {T n} {ind sub} {t} {z},
  EvalTermsGood (SortedStrategy n ind sub) t ->
  all_in_et (fun (x : T) => exists z1, ind x = Some z1 /\ (z1 > z)%Z) t ->
  forall u, t ==>* (EvalValue (SortedStrategy n ind sub) u) ->
  AllInUnion (fun (x : T) => exists z1, ind x = Some z1 /\ (z1 > z)%Z) u.
Proof.
  intros.
  assert (good:exists n1 (ms1 : MergingStrategy T n1), EvalTermsGood ms1 t) by (repeat eexists; eauto).
  generalize dependent u.
  generalize dependent ind.
  generalize dependent sub.
  apply EvalTerms_ind' with (t := t); intros; subst; eauto.
  { invcd H2; eauto. invcd H3. }
  { invcd H2.
    assert (Ht:EvalTermsGood (SortedStrategy n0 ind sub) (EvalValue (SortedStrategy n0 ind sub) t0))
      by (eauto with eval).
    assert (Hf:EvalTermsGood (SortedStrategy n0 ind sub) (EvalValue (SortedStrategy n0 ind sub) f))
      by (eauto with eval).
    destruct b; simpl in *; intuition.
    - invcd H4. invcd H0; try solve [exfalso; eauto].
      invcd_eval_value.
      specialize (H3 _ _ Ht H2 u).
      assert (EvalValue (SortedStrategy n0 ind sub) u ==>* EvalValue (SortedStrategy n0 ind sub) u)
        by (eauto with eval).
      intuition.
    - invcd H4. invcd H1; try solve [exfalso; eauto].
      invcd_eval_value.
      specialize (H3 _ _ Hf H5 u).
      assert (EvalValue (SortedStrategy n0 ind sub) u ==>* EvalValue (SortedStrategy n0 ind sub) u)
        by (eauto with eval).
      intuition.
  }
  { invcd H3. }
  1-4: destruct ms; simpl in H0; try solve [exfalso; auto];
    invcd H4; invcd H5; try solve [exfalso; auto];
    invcd_eval_value;
    eapply H1; eauto;
    invcd H2;
    econstructor; eauto; constructor; constructor; auto.
  { invcd H4. invcd H5; invcd H4; try solve_aiu.
    invcd_eval_value.
    solve_aiu.
  }
Admitted.
*)

(*
Theorem eval_do_not_change_index' : forall {T n n1} {P ind sub} {i t} {Psub} {s : MergingStrategy T n1} {z},
  ProperStrategy P (SortedStrategy n ind sub) ->
  SubStrategy Psub P z s (SortedStrategy n ind sub) ->
  EvalTermsGood s t ->
  all_in_et (fun (x : T) => ind x = Some i) t ->
  forall u, t ==>* (EvalValue s u) ->
  AllInUnion (fun (x : T) => ind x = Some i) u.
Proof.
  intros.
  assert (good:exists n1 (ms1 : MergingStrategy T n1), EvalTermsGood ms1 t) by (repeat eexists; eauto).
  generalize dependent u.
  generalize dependent ind.
  generalize dependent sub.
  generalize dependent z.
  generalize dependent Psub.
  generalize dependent n1.
  apply EvalTerms_ind' with (t := t); intros; subst; eauto.
  { invcd H4; eauto. invcd H5. }
  { invcd H2. destruct b; intuition.
    - eapply H2; eauto.
      + econstructor; eauto.
      + invcd H5. simpl; eauto.
      + invcd H6. invcd H0; eauto; simpl in *; try solve [exfalso; eauto].
    - eapply H2; eauto.
      + econstructor; eauto.
      + invcd H5. simpl; eauto.
      + invcd H6. invcd H1; eauto; simpl in *; try solve [exfalso; eauto].
  }
  { inversiond H3.
    invcd H11.
    invcd H15.
    invcd H12.
    specialize (H9 c _ _ H13 H14) as [r' [H9 H9']].
    rewrite H9 in H0. invc H0.
    assert (EvalTermsGood (SimpleStrategy m) (EvalValue (SimpleStrategy m) (Single r))).
    econstructor; econstructor; eauto.
    specialize (H1 _ _ H0 _ _ _ _ H4 H5).
    invcd H7; invcd H8; try solve [simpl in *; exfalso; eauto].
    rewrite H19 in H9. invcd H9.
    assert (EvalValue (SimpleStrategy m) (Single r) = EvalValue (SimpleStrategy m) u) by eauto with progress.
    invcd H7. invcd H6. invcd H7. invcd H8.
    constructor.
    eauto with strategy.
  }
  1-4: destruct ms; invcd H0;
    invcd H2;
    eapply H1; eauto;
    [econstructor; eauto; econstructor; econstructor; eauto |
    invcd H6; invcd H0; try solve [simpl in *; exfalso; eauto];
    specialize (value_evaluate_to_value H2); intros; invcd H0;
    auto].
  { invcd H6; invcd H7; invcd H6; repeat aiu_simplify; try lia.
    specialize (value_evaluate_to_value H10). intros. invcd H6.
    constructor; eauto.
  }
  { invcd H4. invcd H7; invcd H8; invcd H7; repeat aiu_simplify; try lia.
    specialize (value_evaluate_to_value H10). intros. invcd H7.
    clear H10 H18 H19 H13.

    assert (ProperStrategy P0 (SortedStrategy n0 idx sub1)) by (eauto with inv).

    rewrite H23 in H2. invcd H2.

    eapply H3.
    5: apply H24.
    2: apply H5.
    3: simpl; eauto.
    

    
    invcd H7.
    specialize (all_in_union_left_most' H1). simpl. intros.
    specialize (H16 _ _ _ _ ev H7 H2) as [P' [H16 H16']].

    assert (EvalTermsGood s (MrgIf s c t0 f)).
    econstructor; eauto. admit. admit.
    eapply H3.
    eapply H8.
    apply H5.
    apply H6.
    all: eauto.
    - econstructor; eauto.
    - simpl; eauto.
    - rewrite H3 in H21. invcd H21.
      specialize (value_evaluate_to_value H11). intros. invcd H7.

      


   }
  { admit. }
  { specialize (value_evaluate_to_value H10). intros. invcd H6.
    constructor; eauto.
  }
Admitted.


#[global] Hint Resolve eval_do_not_change_index : progress.
*)


Theorem progress : forall {T n t} {ms : MergingStrategy T n},
  EvalTermsGood ms t ->
  (exists u, t ==>* (EvalValue ms u) /\ EvalTermsGood ms (EvalValue ms u)).
  (*~ is_eval_value t ->
  (exists t' n' (ms' : MergingStrategy T n'), t ==> t' /\ EvalTermsGood ms' t' /\ SubStrategyRT ms' ms).*)
Proof.
  intros.
  assert (good:exists n1 (ms1 : MergingStrategy T n1), EvalTermsGood ms1 t) by (repeat eexists; eauto).
  generalize dependent n.
  apply EvalTerms_ind' with (t := t); intros; subst; eauto.
  all: inversion_initial_eval_good; simpl in *; try solve [exfalso; eauto].
  { repeat eexists; eauto with eval. }
  { destruct b; repeat eexists; eauto with eval. }
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
  1-4: specialize_sorted_ms;
    specialize_ih_mrgif_dispatch;
    econstructor; eauto with eval.
  { exists (If c t0 f); eauto.
    econstructor; econstructor; eauto with eval.
    assert (ProperStrategy P (SortedStrategy n idx sub)) by eauto with inv.
    assert (exists n (s : MergingStrategy T n) ev, sub ti = Some (MSSubLt s ev))
      as [n' [s' [H5 H5']]] by eauto with strategy.
    specialize (hm_sub_st H5 H0 H5' et) as [P1 ?].
    eapply HMSortedI; eauto with inv strategy union.
  }
  { inversiond H4.
    specialize (hm_sub_st ev H0 H2 et) as [P1 ?].
    specialize (hm_sub_st ev H1 H2 ef) as [P2 ?].
    assert (HieraricalMergingInv P1 s f) by eauto with inv.
    assert (EvalTermsGood s (MrgIf s c t0 f)) by (econstructor; eauto).
    specialize (H3 _ _ H8) as [u [H8' H8'']].
    assert (SSMrgIf (SortedStrategy n idx sub0) c t0 f ==>* EvalValue (SortedStrategy n idx sub0) u)
      by (econstructor; eauto with eval).
    exists u.
    intuition.
    - invc H8''. assert (ProperStrategy P (SortedStrategy n idx sub0)) by eauto with inv.
      econstructor.
      eapply hm_sup_st; eauto.
      assert (all_in_et (fun x : T => idx x = Some i) (SSMrgIf (SortedStrategy n idx sub0) c t0 f)) by eauto with progress.
      specialize (eval_do_not_change_index H4 H12 _ H3). intuition.
  }
  { exists (If (pnegsb c) f t0); eauto.
    econstructor; econstructor; eauto with eval.
    assert (ProperStrategy P (SortedStrategy n idx sub)) by eauto with inv.
    assert (exists n (s : MergingStrategy T n) ev, sub fi = Some (MSSubLt s ev))
      as [n' [s' [H5 H5']]] by eauto with strategy.
    specialize (hm_sub_st H5 H1 H5' ef) as [P1 ?].
    eapply HMSortedI; eauto with inv strategy union.
  }
  { assert (EvalTermsGood (SortedStrategy n idx sub) (SSMrgIf (SortedStrategy n idx sub) c t0 f)).
    { econstructor; eauto with eval union. }
    specialize (H1 _ _ H3) as [u [H3' H3'']].
    exists u.
    intuition.
    econstructor; econstructor; eauto with progress.
  }
  { assert (EvalTermsGood (SortedStrategy n idx sub) (EvalValue (SortedStrategy n idx sub) (If c t0 (If fc ft ff)))).
    { econstructor. eapply hm_if_no_deg; simpl; eauto with inv.
      eapply (all_in_union_left_most' H1). }
    exists (If c t0 (If fc ft ff)).
    intuition.
    econstructor.
    eapply SILt; eauto.
    econstructor; eauto with progress.
  }
  { assert (SubUnion ft (If fc ft ff)) by eauto with union.
    assert (ef0:HieraricalMergingInv P (SortedStrategy n idx sub) ft) by eauto with inv.
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

      assert (SubStrategy P1 P z s (SortedStrategy n idx sub)).
      { specialize (all_in_union_left_most' H0); simpl; intros.
        econstructor; eauto with inv. }
      invcd H5''.
      assert (HieraricalMergingInv P1 s u) by eauto with inv.
      clear P0 H19.

      specialize (hm_sub_st' _ H15 H14 H5) as [? [? ?]]; repeat aiu_simplify.

      econstructor.
      eapply HMSortedI; eauto; try solve_aiu.
   }
  { assert (SubUnion ft (If fc ft ff)) by eauto with union.
    inversiond ef; repeat aiu_simplify.
    - specialize (all_in_union_left_most' H9); simpl; intro.
      rewrite H2 in H12. invc H12. lia.
    - assert (EvalTermsGood (SortedStrategy n idx sub) (MrgIf (SortedStrategy n idx sub) c t0 ff)).
      { econstructor; eauto with inv. }
      specialize (H5 _ _ H12) as [u [H5 H5']].
      exists (If (pandsb (pnegsb c) fc) ft u).
      intuition.
      { econstructor. eapply SIGt; eauto.
        constructor. 
      }
      invcd H5'.
      assert (HieraricalMergingInv P (SortedStrategy n idx sub) u) by eauto with inv.
      clear P0 H18.
      
      econstructor.
      eapply HMSortedI; repeat aiu_simplify; eauto with inv; try solve_aiu.
      eapply eval_do_not_change_index'; eauto.

      constructor; eauto with union.

      eapply all_in_union_lower_bound; eauto; lia.
  }
    
  
  
  
