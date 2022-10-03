Require Import Grisette.MergingStrategy.
Require Import Grisette.GeneralTactics.
Require Import Grisette.Union.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.ZArith.BinInt.
Require Import Lia.
Open Scope Z.
Open Scope nat.

Create HintDb inv discriminated.

Inductive HieraricalMergingInv {T} (P : T -> Prop) : forall {n} (ms : MergingStrategy T n) (u : Union T), Prop :=
  | HMSingle : forall (v : T) {n} {ms : MergingStrategy T n},
    ProperStrategy P ms ->
    P v ->
    HieraricalMergingInv P ms (Single v)
  | HMSortedD : forall c t f n ind sub z Ps n1 (ev : n1 < n) s,
    ProperStrategy P (SortedStrategy n ind sub) ->
    AllInUnion (fun x => P x /\ ind x = Some z) t ->
    AllInUnion (fun x => P x /\ ind x = Some z) f ->
    sub z = Some (MSSubLt s ev) ->
    HieraricalMergingInv Ps s (If c t f) -> 
    HieraricalMergingInv P (SortedStrategy n ind sub) (If c t f)
  | HMSortedI : forall c t f n ind sub z Ps n1 (ev : n1 < n) s,
    ProperStrategy P (SortedStrategy n ind sub) ->
    AllInUnion (fun x => P x /\ ind x = Some z) t ->
    AllInUnion (fun x => P x /\ exists z1, ind x = Some z1 /\ (z1 > z)%Z) f ->
    sub z = Some (MSSubLt s ev) ->
    HieraricalMergingInv Ps s t -> 
    HieraricalMergingInv P (SortedStrategy n ind sub) f -> 
    HieraricalMergingInv P (SortedStrategy n ind sub) (If c t f).

Lemma hm_implies_proper_ms : forall {T P n} {ms : MergingStrategy T n} {u : Union T},
  HieraricalMergingInv P ms u -> ProperStrategy P ms.
Proof.
  intros.
  invc H; invc_existT; auto.
Qed.

#[global] Hint Resolve hm_implies_proper_ms : inv.

Ltac invc_hm H :=
  invc H; subst; repeat invc_existT.

Theorem hm_sub_st : forall {T} {P : T -> Prop} {n n1 : nat} {ind sub}
  {mssub : MergingStrategy T n1}
  {u : Union T} {z} (evlt' : n1 < n),
  AllInUnion (fun x => ind x = Some z) u ->
  sub z = Some (MSSubLt mssub evlt') ->
  HieraricalMergingInv P (SortedStrategy n ind sub) u ->
  exists P1, HieraricalMergingInv P1 mssub u.
Proof.
  intros.
  inversion H1; subst; repeat invc_existT.
  - inversion H3; repeat invc_existT.
    inversion H. subst. intuition.
    specialize (H11 _ _ _ _ evlt' H4 H0) as [P' [? ?]].
    exists P'.
    constructor; auto.
  - inversion H4; repeat invc_existT.
    inversion H; subst; intuition.
    assert (AllInUnion (fun x => ind x = Some z0) t) by aiu_imply.
    assert (AllInUnion (fun x => ind x = Some z0) f) by aiu_imply.
    assert (z = z0) by eauto with union. subst.
    rewrite H0 in H8.
    inversion H8.
    subst.
    invc_existT.
    destruct s.
    + inversion H10.
    + exists Ps. auto. 
  - inversion H; subst.
    assert (AllInUnion (fun x => ind x = Some z0) t) by aiu_imply.
    assert (z = z0) by eauto with union.
    subst.
    assert (forall x, P x /\ (exists z1 : Z, ind x = Some z1 /\ (z1 > z0)%Z) ->
        ~ (P x /\ ind x = Some z0)).
    { intros. firstorder. unfold not. intros. firstorder. rewrite H10 in H15. inversion H15. lia. }

    specialize (all_in_union_contra (fun x : T => P x /\ ind x = Some z0) H6).
    intros.
    simpl in H10.
    specialize (H10 H3).
    exfalso.
    apply H10.
    rewrite <- all_in_union_and in H6.
    rewrite <- all_in_union_and.
    intuition.
Qed.

#[global] Hint Resolve hm_sub_st : inv.

Theorem hm_sub_st1 : forall {T} {P : T -> Prop} {n n1 : nat} {ind sub}
  {mssub : MergingStrategy T n1}
  {u : Union T} {z} (evlt' : n1 < n),
  AllInUnion (fun x => P x /\ ind x = Some z) u ->
  sub z = Some (MSSubLt mssub evlt') ->
  HieraricalMergingInv P (SortedStrategy n ind sub) u ->
  exists P1, HieraricalMergingInv P1 mssub u.
Proof.
  intros.
  rewrite <- all_in_union_and in H. intuition. eauto with inv.
Qed.

#[global] Hint Resolve hm_sub_st1 : inv.

Theorem hm_same_set : forall {T P1 P2 n} {s : MergingStrategy T n} {u1 u2},
  HieraricalMergingInv P1 s u1 -> HieraricalMergingInv P2 s u2 -> (forall v, P1 v <-> P2 v).
Proof.
  intros.
  inversion H; inversion H0; repeat invc_existT; eauto with strategy.
Qed.

#[global] Hint Resolve hm_same_set : inv.

Theorem hm_same_set' : forall {T P1 P2 n} {s : MergingStrategy T n} {u},
  HieraricalMergingInv P1 s u -> (forall v, P1 v <-> P2 v) -> HieraricalMergingInv P2 s u.
Proof.
  intros.
  induction u; inversion H; subst; repeat invc_existT.
  - econstructor; eauto with inv strategy; firstorder.
  - econstructor; eauto with inv strategy; firstorder.
    + apply (all_in_union_implies H7). firstorder.
    + apply (all_in_union_implies H8). firstorder.
  - eapply HMSortedI; eauto with inv strategy; firstorder.
    + apply (all_in_union_implies H6). firstorder.
    + apply (all_in_union_implies H8). firstorder.
Qed.

#[global] Hint Resolve hm_same_set' : inv.

Theorem hm_sub : forall {T} (P : T -> Prop) {n} (ms : MergingStrategy T n) (u u1 : Union T),
  HieraricalMergingInv P ms u -> SubUnion u1 u -> HieraricalMergingInv P ms u1.
Proof.
  intros.
  generalize dependent u1.

  induction H; intros.
  - inversion H1; subst.
    constructor; auto.
  - destruct u1. 
    + invc H4;
      try specialize (all_sub_union H0 H7) as HA;
      try specialize (all_sub_union H1 H7) as HA;
      invc HA; econstructor; intuition; eauto.
    + inversion H4; subst; eapply HMSortedD; eauto.
      all: try specialize (all_sub_union H0 H7) as HA;
           try specialize (all_sub_union H1 H7) as HA; invc HA; intuition.
  - destruct u1.
    + invc H5;
      try specialize (all_sub_union H0 H8) as HA;
      try specialize (all_sub_union H1 H8) as HA;
      invc HA; econstructor; intuition; eauto.
    + invc H5.
      * eapply HMSortedI; eauto.
      * eapply HMSortedD; eauto; specialize (all_sub_union H0 H8) as HA; invc HA; intuition.
      * auto.
Qed.

#[global] Hint Resolve hm_sub : inv.

Theorem hm_sub_if_true : forall {T} {P : T -> Prop} {n} {ms : MergingStrategy T n} {c} {t f : Union T},
  HieraricalMergingInv P ms (If c t f) -> HieraricalMergingInv P ms t.
Proof.
  intros.
  assert (SubUnion t (If c t f)) as Hsub by eauto with union.
  eauto with inv.
Qed.

#[global] Hint Resolve hm_sub_if_true : inv.

Theorem hm_sub_if_false : forall {T} {P : T -> Prop} {n} {ms : MergingStrategy T n} {c} {t f : Union T},
  HieraricalMergingInv P ms (If c t f) -> HieraricalMergingInv P ms f.
Proof.
  intros.
  assert (SubUnion f (If c t f)) as Hsub by eauto with union.
  eauto with inv.
Qed.

#[global] Hint Resolve hm_sub_if_false : inv.

Lemma all_in_union_same_ind_exist : forall {T P n ind sub u},
  HieraricalMergingInv P (SortedStrategy n ind sub) u ->
  AllInUnion (fun x : T => AllInUnion (fun y : T => ind x = ind y) u) u ->
  exists z, AllInUnion (fun x : T => ind x = Some z) u.
Proof.
  intros.
  assert (exists z, AllInUnion (fun x : T => ind x = z) u).
  - induction u.
    + exists (ind t). eauto with union.
    + inversion H; subst; repeat invc_existT.
      * exists (Some z). constructor; eauto; aiu_imply. 
      * specialize (lm_exist (If s u1 u2)) as [lmi ?].
        specialize (all_in_union_left_most H0 H1).
        intros.
        inversion H1; subst.
        inversion H2; subst.
        specialize (all_in_union_left_most H8 H5).
        intros.
        exists (ind lmi).
        eauto with union.
  - inversion H; subst; repeat invc_existT.
    + inversion H3; subst; repeat invc_existT. apply H6 in H5.
      firstorder. exists x. eauto with union.
    + exists z.
      constructor; aiu_imply.
    + specialize (lm_exist (If c t f)) as [lmi ?].
      specialize (all_in_union_left_most H0 H2).
      intros.
      invc H2.
      inversion H3; subst.
      specialize (all_in_union_left_most H5 H12) as [HP He].
      exists z.
      rewrite He in H10.
      rewrite He in H14.
      eauto with union.
Qed.

#[global] Hint Resolve all_in_union_same_ind_exist : inv.

Lemma all_in_union_same_ind_inexist : forall {T P n ind sub c t f z0},
  HieraricalMergingInv P (SortedStrategy n ind sub) (If c t f) ->
  AllInUnion (fun x : T => AllInUnion (fun y : T => ind x = ind y) (If c t f)) (If c t f) ->
  AllInUnion (fun x : T => P x /\ ind x = Some z0) t ->
  AllInUnion (fun x : T => P x /\ exists z1 : Z, ind x = Some z1 /\ (z1 > z0)%Z) f ->
  False.
Proof.
  intros.
  specialize (all_in_union_same_ind_exist H H0) as [z ?].
  invc H3.
  specialize (lm_exist t) as [lmt Hlmt].
  specialize (lm_exist f) as [lmf Hlmf].
  specialize (all_in_union_left_most H1 Hlmt).
  specialize (all_in_union_left_most H6 Hlmt).
  specialize (all_in_union_left_most H2 Hlmf).
  specialize (all_in_union_left_most H8 Hlmf).
  intros.
  invc H3.
  invc H4.
  invc H5.
  invc H7.
  intuition.
  destruct H9.
  intuition.
  rewrite H10 in H9.
  rewrite H5 in H11.
  rewrite <- H11 in H9.
  invc H9.
  lia.
Qed.

#[global] Hint Resolve all_in_union_same_ind_inexist : inv.

Lemma all_in_union_nested_lm' : forall {T n P} {ind : T -> option Z} {sub} {u : Union T},
  HieraricalMergingInv P (SortedStrategy n ind sub) u ->
  AllInUnion (fun x : T => AllInUnion (fun y : T => ind x = ind y) u) u ->
  exists i, Some i = ind (left_most u).
Proof.
  intros.
  induction u.
  - simpl in *. inversion H; subst; invc_existT.
    inversion H4; subst; invc_existT.
    apply H3 in H5. firstorder. exists x. auto.
  - assert (HieraricalMergingInv P (SortedStrategy n ind sub) u1) by eauto with union inv.
    assert (HieraricalMergingInv P (SortedStrategy n ind sub) u2) by eauto with union inv.
    intuition.
    invc H; subst; invc_existT; 
    repeat aiu_simplify; simpl; eauto with union.
Qed.

#[global] Hint Resolve all_in_union_nested_lm' : inv.

Lemma hm_is_p : forall {T P n} {s : MergingStrategy T n} {u},
  HieraricalMergingInv P s u ->
  AllInUnion P u.
Proof.
  intros.
  invcd H.
  - eauto with union.
  - solve_aiu.
  - solve_aiu.
Qed.

#[global] Hint Resolve hm_is_p : inv.

Lemma hm_lm_is_lowerbound : forall {T P n} {ind : T -> option Z} {sub} {u} {i} {il},
  HieraricalMergingInv P (SortedStrategy n ind sub) u ->
  ind (left_most u) = Some i ->
  (il < i)%Z ->
  AllInUnion (fun x : T => exists z : Z, ind x = Some z /\ (z > il)%Z) u.
Proof.
  intros.
  invcd H; try solve_aiu;
  simpl in H0; specialize (all_in_union_left_most' H5) as [? ?];
  rewrite H0 in H2; invc H2.
  - eapply all_in_union_lower_bound; eauto.
    solve_aiu.
  - constructor.
    eapply all_in_union_lower_bound; eauto; solve_aiu.
    eapply all_in_union_lower_bound'; eauto; solve_aiu.
Qed.

#[global] Hint Resolve hm_lm_is_lowerbound : inv.

Lemma hm_if_no_deg : forall {T P} {n} {ind : T -> option Z} {sub} {c t f} {ti} {flmi},
  HieraricalMergingInv P (SortedStrategy n ind sub) t ->
  HieraricalMergingInv P (SortedStrategy n ind sub) f ->
  AllInUnion (fun x => ind x = Some ti) t ->
  ind (left_most f) = Some flmi ->
  (ti < flmi)%Z ->
  HieraricalMergingInv P (SortedStrategy n ind sub) (If c t f).
Proof.
  intros.
  specialize (all_in_union_left_most' H1); simpl; intros.
  assert (ProperStrategy P (SortedStrategy n ind sub)) by eauto with inv.
  inversiond H5.
  specialize (proper_ms_ind_some_is_sub_some H5 H4) as [n' [ev' [s' ?]]].
  specialize (hm_sub_st ev' H1 H6 H) as [P1 ?].
  
  eapply HMSortedI; repeat aiu_simplify; eauto with inv strategy.
Qed.

#[global] Hint Resolve hm_if_no_deg : inv.
  
Theorem hm_simple_result : forall {T P} {m} {c} {tv fv r : T},
  HieraricalMergingInv P (SimpleStrategy m) (Single tv) ->
  HieraricalMergingInv P (SimpleStrategy m) (Single fv) ->
  m c tv fv = Some r ->
  HieraricalMergingInv P (SimpleStrategy m) (Single r).
Proof.
  intros.
  invcd H.
  invcd H0.
  invcd H5.
  specialize (H0 c _ _ H6 H7) as [r' [? ?]].
  rewrite H in H1. invcd H1.
  constructor; eauto.
Qed.

#[global] Hint Resolve hm_simple_result : inv.
