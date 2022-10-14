Require Import Grisette.MergingStrategy.
Require Import Grisette.Invariant.
Require Import Grisette.SubStrategy.
Require Import Grisette.GeneralTactics.
Require Import Grisette.Union.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.ZArith.BinInt.
Require Import Lia.
Open Scope Z.
Open Scope nat.

Create HintDb subinv discriminated.

Lemma hm_sup_single_case : forall {T Psub Pms nsub nms} {ind sub}
  {msub : MergingStrategy T nsub} {z} t,
  HieraricalMergingInv Psub msub (Single t) ->
  ProperStrategy Pms (SortedStrategy nms ind sub) ->
  SubStrategy Psub Pms z msub (SortedStrategy nms ind sub) ->
  exists evlt', Pms t /\ ind t = Some z /\ sub z = Some (MSSubLt msub evlt').
Proof.
  intros.
  invc_hm H.
  inversiond H1.
  inversiond H0.
  specialize (proper_ms_sub_ind H1 _ H6) as [? [? ?]].
  eexists; intuition; eauto.
  eapply proper_ms_sub_p; eauto.
Qed.

Theorem hm_sup_aux : forall {T Psub nsub}
  {msub : MergingStrategy T nsub} t,
  HieraricalMergingInv Psub msub t ->
  forall {Pms nms ind sub},
  ProperStrategy Pms (SortedStrategy nms ind sub) ->
  forall {z},
  SubStrategy Psub Pms z msub (SortedStrategy nms ind sub) ->
  HieraricalMergingInv Pms (SortedStrategy nms ind sub) t /\
  exists evlt', AllInUnion (fun x => Pms x /\ ind x = Some z /\ sub z = Some (MSSubLt msub evlt')) t.
Proof.
  intros.
  induction t; intros.
  - inversion H; subst; repeat invc_existT.
    specialize (proper_ms_sub_p H1 _ H6). intros.
    split.
    + constructor; eauto.
    + specialize (hm_sup_single_case _ H H0 H1) as [evlt' [? [? ?]]].
      exists evlt'; intuition.
  - assert (SubUnion t1 (If s t1 t2)) by eauto with union.
    assert (SubUnion t2 (If s t1 t2)) by eauto with union.
    inversiond H1.
    assert (HieraricalMergingInv Psub msub t1) by eauto with inv.
    assert (HieraricalMergingInv Psub msub t2) by eauto with inv.
    clear H2 H3.
    specialize (IHt1 H4) as [IHt11 [evlt1' IHt12]]. clear H4.
    specialize (IHt2 H5) as [IHt21 [evlt2' IHt22]]. clear H5.
    specialize (all_in_union_exist t1 IHt12) as [t1v [Ht1P [Ht1I Ht1S]]].
    specialize (all_in_union_exist t2 IHt22) as [t2v [Ht2P [Ht2I Ht2S]]].
    split.
    + econstructor; eauto; aiu_imply.
    + exists evlt1'. econstructor; eauto.
      rewrite (proof_irrelevance _ evlt1' evlt2').
      eauto.
Qed.

Theorem hm_sup : forall {T Psub nsub}
  {msub : MergingStrategy T nsub} {t},
  HieraricalMergingInv Psub msub t ->
  forall {Pms nms ind sub z},
  SubStrategy Psub Pms z msub (SortedStrategy nms ind sub) ->
  HieraricalMergingInv Pms (SortedStrategy nms ind sub) t /\
  exists evlt', AllInUnion (fun x => Pms x /\ ind x = Some z /\ sub z = Some (MSSubLt msub evlt')) t.
Proof.
  intros.
  inversiond H0.
  eapply hm_sup_aux; eauto.
Qed.

#[global] Hint Resolve hm_sup : subinv.

Theorem hm_sup_hm : forall {T Psub nsub}
  {msub : MergingStrategy T nsub} t,
  HieraricalMergingInv Psub msub t ->
  forall {Pms nms ind sub z},
  SubStrategy Psub Pms z msub (SortedStrategy nms ind sub) ->
  HieraricalMergingInv Pms (SortedStrategy nms ind sub) t.
Proof.
  intros.
  specialize (hm_sup H H0). intuition.
Qed.

#[global] Hint Resolve hm_sup_hm : subinv.

Theorem hm_sup_all_in_union_ind : forall {T} {P Psub : T -> Prop} {n nsub : nat} {ind sub}
  {mssub : MergingStrategy T nsub}
  {u : Union T} {z},
  SubStrategy Psub P z mssub (SortedStrategy n ind sub) ->
  HieraricalMergingInv Psub mssub u ->
  AllInUnion (fun x => P x /\ ind x = Some z) u.
Proof.
  intros.
  inversiond H.
  induction u.
  - constructor. inversiond H4. inversiond H0.
    assert (P t) by (eapply proper_ms_sub_p; eauto).
    intuition; eauto with inv strategy.
    unfold SortedSubDefinedNoOverlap in H7.
    apply H3 in H1 as [z' [n' [s' [evlt' [H1 H1']]]]].
    specialize (H13 _ _ _ _ evlt' H1 H1') as [P' [H13 H13']].
    specialize (H7 _ _ _ _ _ _ _ _ evlt' evlt _ _ H1 H11 H1' H12 (proper_ms_implies_defined_at H13) (proper_ms_implies_defined_at H10)).
    assert (exists v, P' v /\ Psub v) by (exists t; intuition).
    apply H7 in H2.
    subst.
    auto.
  - assert (HieraricalMergingInv Psub mssub u1) by eauto with inv.
    assert (HieraricalMergingInv Psub mssub u2) by eauto with inv.
    intuition.
Qed.

#[global] Hint Resolve hm_sup_all_in_union_ind : subinv.

Theorem hm_supt_hm : forall {T Psub P} {n} {ind sub} {nsub} {mssub : MergingStrategy T nsub} {u},
  SubStrategyT Psub P mssub (SortedStrategy n ind sub) ->
  HieraricalMergingInv Psub mssub u ->
  HieraricalMergingInv P (SortedStrategy n ind sub) u.
Proof.
  intros.
  induction H.
  - inversiond H.
    eapply hm_sup_hm; eauto.
  - inversiond H1.
    + inversiond H6.
      specialize (IHSubStrategyT sub1 H0).
      inversiond H.
      eapply hm_sup_hm; eauto.
    + inversiond H3.
      specialize (IHSubStrategyT sub1 H0).
      inversiond H.
      eapply hm_sup_hm; eauto.
Qed.

#[global] Hint Resolve hm_supt_hm : subinv.

Theorem hm_supt_all_in_union_ind : forall {T Psub P} {n} {ind sub} {nsub} {mssub : MergingStrategy T nsub},
  SubStrategyT Psub P mssub (SortedStrategy n ind sub) ->
  exists i, forall u, HieraricalMergingInv Psub mssub u -> AllInUnion (fun x => ind x = Some i) u.
Proof.
  intros.
  inversiond H.
  - exists z. intros. specialize (hm_sup_all_in_union_ind H4 H0). intros; solve_aiu.
  - exists z. intros. assert (is_sorted_strategy mid) by eauto with sub.
    destruct mid; simpl in *; try solve [exfalso; auto].
    specialize (hm_supt_hm H H0).
    specialize (hm_supt_hm H5 H0).
    intros.
    specialize (hm_sup_all_in_union_ind H1 H3). intros.
    solve_aiu.
Qed.

Theorem hm_sub_hm : forall {T Psub nsub}
  {msub : MergingStrategy T nsub} {t},
  forall {Pms nms ind sub z},
  HieraricalMergingInv Pms (SortedStrategy nms ind sub) t ->
  AllInUnion (fun x => ind x = Some z) t ->
  SubStrategy Psub Pms z msub (SortedStrategy nms ind sub) ->
  HieraricalMergingInv Psub msub t.
Proof.
  intros.
  assert (ProperStrategy Psub msub) by eauto with sub.
  invcd H.
  - constructor; eauto. invcd H0.
    eauto with strategy.
    invcd H1.
    invcd H7.
    specialize (H12 _ _ _ _ evlt H3 H15) as [P' [? ?]].
    specialize (proper_ms_same_set H H2).
    intros.
    rewrite <- H7. auto.
  - repeat aiu_simplify.
    invcd H1.
    rewrite H19 in H9. invcd H9.
    assert (ProperStrategy Ps s) by eauto with inv.
    specialize (proper_ms_same_set H0 H2).
    intros.
    specialize (hm_same_set' H11 H1). auto.
  - repeat aiu_simplify.
    specialize (all_in_union_left_most' H14).
    specialize (all_in_union_left_most' H3).
    simpl.
    intros.
    destruct H0.
    rewrite H6 in H0.
    intuition.
    inversion H9.
    lia.
Qed.

#[global] Hint Resolve hm_sub_hm : subinv.

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
