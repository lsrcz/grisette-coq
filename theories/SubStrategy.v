Require Import Grisette.MergingStrategy.
Require Import Grisette.GeneralTactics.
Require Import Grisette.Union.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Logic.Classical_Prop.

Create HintDb sub discriminated.

Inductive SubStrategy {T} : forall {n1 n} P1 P, Z -> MergingStrategy T n1 -> MergingStrategy T n -> Prop :=
  | SubSorted : forall {n1 n P1 P ind sub} {s : MergingStrategy T n1} {z v evlt},
    ProperStrategy P (SortedStrategy n ind sub) ->
    ProperStrategy P1 s ->
    ind v = Some z ->
    sub z = Some (MSSubLt s evlt) ->
    SubStrategy P1 P z s (SortedStrategy n ind sub).

Arguments SubSorted {T n1 n P1 P ind sub s z v evlt}.
#[global] Hint Constructors SubStrategy : sub.

Theorem proper_ms_sub_from_subfunc : forall {T P n nsub} {ind sub} {mssub : MergingStrategy T nsub} {ev : nsub < n} {x i},
  ProperStrategy P (SortedStrategy n ind sub) ->
  ind x = Some i ->
  sub i = Some (MSSubLt mssub ev) ->
  exists Psub, SubStrategy Psub P i mssub (SortedStrategy n ind sub).
Proof.
  intros.
  inversiond H.
  specialize (H10 _ _ _ _ ev H0 H1) as [P' [? ?]]. 
  exists P'.
  econstructor; eauto.
Qed.

Theorem proper_ms_sub_p : forall {T P0 P1 n0 n1} {ms0 : MergingStrategy T n0}
  {ms1 : MergingStrategy T n1} {z},
  SubStrategy P0 P1 z ms0 ms1 -> forall x, P0 x -> P1 x.
Proof.
  intros.
  inversiond H.
  inversiond H3.
  specialize (H7 _ _ _ _ evlt P0 H10 H11 (proper_ms_implies_defined_at H4)).
  apply H7. auto.
Qed.

Theorem proper_ms_sub_ind : forall {T P0 P1} {ns} {s : MergingStrategy T ns} {n ind sub} {z},
  SubStrategy P0 P1 z s (SortedStrategy n ind sub) ->
  forall x, P0 x -> ind x = Some z /\ exists evlt, sub z = Some (MSSubLt s evlt).
Proof.
  intros.
  inversiond H.
  inversiond H4.
  assert (P1 x) by (eapply proper_ms_sub_p; eauto).
  specialize (H3 _ H1) as [z1 [n1 [s1 [evlt1 [H3 H3']]]]].
  specialize (H13 _ _ _ _ evlt1 H3 H3') as [P' [H13 H13']].

  unfold SortedSubDefinedNoOverlap in H7.
  specialize (H7 _ _ _ _ _ _ _ _ evlt evlt1 _ _ H11 H3 H12 H3'
    (proper_ms_implies_defined_at H10) (proper_ms_implies_defined_at H13)).
  assert (exists v, P0 v /\ P' v) by (exists x; auto).
  apply H7 in H2.
  subst.
  intuition; auto.
  exists evlt; auto.
Qed.

#[global] Hint Resolve proper_ms_sub_ind : sub.

Theorem proper_ms_sub_simple : forall {T P0 P1} {n ind sub} {m} {z},
  SubStrategy P0 P1 z (SimpleStrategy m) (SortedStrategy n ind sub) ->
  forall {c} {t f : T} {i r},
  ind t = Some i ->
  ind f = Some i ->
  m c t f = Some r ->
  ind r = Some i.
Proof.
  intros.
  inversiond H.
  inversiond H12.
  unfold SimpleDefinedNoBeyond in H5.
  assert (P0 t /\ P0 f).
  { assert ((P0 t /\ P0 f) \/ ~(P0 t /\ P0 f)) by apply classic.
    destruct H3; auto.
    apply not_and_or in H3. apply (H5 c) in H3. rewrite H2 in H3. congruence.
  }
  unfold SimpleDefinedAt in H4.
  intuition.
  specialize (H4 c _ _ H7 H8) as [r' [H4 H4']].
  rewrite H4 in H2. invc H2.
  specialize (proper_ms_sub_ind H _ H4') as [Hr1 [? Hr2]].

  specialize (proper_ms_sub_ind H _ H7) as [Ht1 [? Ht2]].
  rewrite H0 in Ht1. invc Ht1. auto.
Qed.

#[global] Hint Resolve proper_ms_sub_simple : sub.

Inductive SubStrategyT {T} {n1} P1 : forall {n}, (T -> Prop) -> MergingStrategy T n1 -> MergingStrategy T n -> Prop := 
  | Sub_single : forall sub {n2} (sub2 : MergingStrategy T n2) {P2} {z},
      SubStrategy P1 P2 z sub sub2 -> SubStrategyT P1 P2 sub sub2
  | Sub_trans : forall sub {n2} (mid : MergingStrategy T n2) {n} (ms : MergingStrategy T n) {Pmid Pms} {z},
      SubStrategy Pmid Pms z mid ms -> SubStrategyT P1 Pmid sub mid -> SubStrategyT P1 Pms sub ms.

#[global] Hint Constructors SubStrategyT : sub.

Theorem subt_only_on_sorted : forall {T n1} {P1 P2} {n2} {sub : MergingStrategy T n1} {ms : MergingStrategy T n2},
  SubStrategyT P1 P2 sub ms -> is_sorted_strategy ms.
Proof.
  intros.
  induction H.
  - destruct sub2; simpl; auto.
    invc H.
  - invcd H. simpl; auto.
Qed.

#[global] Hint Resolve subt_only_on_sorted : sub.

Theorem subt_proper_sub : forall {T n1} {P1 P2} {n2} {sub : MergingStrategy T n1} {ms : MergingStrategy T n2},
  SubStrategyT P1 P2 sub ms -> ProperStrategy P1 sub.
Proof.
  intros.
  induction H.
  - invcd H; eauto.
  - eauto.
Qed.

#[global] Hint Resolve subt_proper_sub : sub.

Theorem subt_proper_sup : forall {T n1} {P1 P2} {n2} {sub : MergingStrategy T n1} {ms : MergingStrategy T n2},
  SubStrategyT P1 P2 sub ms -> ProperStrategy P2 ms.
Proof.
  intros.
  invcd H.
  - invcd H4; eauto.
  - invcd H1; eauto.
Qed.

#[global] Hint Resolve subt_proper_sup : sub.

Theorem proper_ms_subt_p : forall {T P0 P1} {n ind sub} {n1} {mssub : MergingStrategy T n1},
  SubStrategyT P0 P1 mssub (SortedStrategy n ind sub) ->
  forall (t : T), P0 t -> P1 t.
Proof.
  intros.
  induction H.
  - eapply proper_ms_sub_p; eauto.
  - assert (is_sorted_strategy mid) by eauto with sub.
    destruct mid; simpl in *; try solve [exfalso; auto].
    specialize (IHSubStrategyT sub1).
    eapply proper_ms_sub_p; eauto.
Qed.

Theorem proper_ms_subt_ind : forall {T P0 P1} {n ind sub} {n1} {mssub : MergingStrategy T n1},
  SubStrategyT P0 P1 mssub (SortedStrategy n ind sub) ->
  exists z, forall (t : T), P0 t -> ind t = Some z.
Proof.
  intros.
  invcd H.
  - exists z. intros. specialize (proper_ms_sub_ind H4 _ H). intuition.
  - assert (is_sorted_strategy mid) by eauto with sub.
    destruct mid; simpl in *; try solve [exfalso; auto].
    assert (forall t, P0 t -> Pmid t). 
    eapply proper_ms_subt_p; eauto.
    exists z.
    intros.
    apply H0 in H2.
    eapply proper_ms_sub_ind; eauto.
Qed.

Theorem proper_ms_subt_simple : forall {T P0 P1} {n ind sub} {m},
  SubStrategyT P0 P1 (SimpleStrategy m) (SortedStrategy n ind sub) ->
  forall {c} {t f : T} {r},
  m c t f = Some r ->
  exists i, ind t = Some i /\ ind f = Some i /\ ind r = Some i.
Proof.
  intros.
  specialize (proper_ms_subt_ind H) as [z ?].
  assert (ProperStrategy P0 (SimpleStrategy m)) by eauto with sub.
  invcd H2.
  unfold SimpleDefinedNoBeyond in H5.
  assert (P0 t /\ P0 f) as [? ?].
  { assert ((P0 t /\ P0 f) \/ ~(P0 t /\ P0 f)) by apply classic.
    destruct H2; eauto.
    apply not_and_or in H2.
    specialize (H5 c _ _ H2).
    rewrite H0 in H5. congruence.
  }
  specialize (H4 c _ _ H2 H3) as [r' [? ?]].
  rewrite H4 in H0. invc H0.
  exists z.
  firstorder.
Qed.

Theorem proper_ms_subt_simple_t : forall {T P0 P1} {n ind sub} {m},
  SubStrategyT P0 P1 (SimpleStrategy m) (SortedStrategy n ind sub) ->
  forall {c} {t f : T} {i r},
  ind t = Some i ->
  m c t f = Some r ->
  ind r = Some i.
Proof.
  intros.
  specialize (proper_ms_subt_simple H H1) as [z [? [? ?]]].
  rewrite H0 in H2. invc H2.
  auto.
Qed.

Theorem proper_ms_subt_simple_f : forall {T P0 P1} {n ind sub} {m},
  SubStrategyT P0 P1 (SimpleStrategy m) (SortedStrategy n ind sub) ->
  forall {c} {t f : T} {i r},
  ind f = Some i ->
  m c t f = Some r ->
  ind r = Some i.
Proof.
  intros.
  specialize (proper_ms_subt_simple H H1) as [z [? [? ?]]].
  rewrite H0 in H3. invc H3.
  auto.
Qed.

Inductive SubStrategyRT {T} {n1} P1 : forall {n}, (T -> Prop) -> MergingStrategy T n1 -> MergingStrategy T n -> Prop := 
  | Subrt_refl : forall sub, ProperStrategy P1 sub -> SubStrategyRT P1 P1 sub sub
  | Subrt_trans : forall {n P2} {sub : MergingStrategy T n1} {ms : MergingStrategy T n}, SubStrategyT P1 P2 sub ms -> SubStrategyRT P1 P2 sub ms.

#[global] Hint Constructors SubStrategyRT : sub.

Theorem subrt_proper_sub : forall {T n1} {P1 P2} {n2} {sub : MergingStrategy T n1} {ms : MergingStrategy T n2},
  SubStrategyRT P1 P2 sub ms -> ProperStrategy P1 sub.
Proof.
  intros.
  invcd H; eauto with sub.
Qed.

#[global] Hint Resolve subrt_proper_sub : sub.

Theorem subrt_proper_sup : forall {T n1} {P1 P2} {n2} {sub : MergingStrategy T n1} {ms : MergingStrategy T n2},
  SubStrategyRT P1 P2 sub ms -> ProperStrategy P2 ms.
Proof.
  intros.
  invcd H; eauto with sub.
Qed.

#[global] Hint Resolve subrt_proper_sup : sub.

Lemma sub_subt_subt :
  forall {T} {Psub Pmid Pms} {nsub nmid nms}
  {sub : MergingStrategy T nsub}
  {mid : MergingStrategy T nmid}
  {ms : MergingStrategy T nms} {i},
  SubStrategy Psub Pmid i sub mid -> SubStrategyT Pmid Pms mid ms ->
  SubStrategyT Psub Pms sub ms.
Proof.
  intros.
  generalize dependent nsub.
  generalize dependent Psub.
  induction H0; intros; eapply Sub_trans; eauto.
  eapply Sub_single. eauto.
Qed.

#[global] Hint Resolve sub_subt_subt : sub.

Lemma sub_subrt_subt :
  forall {T} {Psub Pmid Pms} {nsub nmid nms}
  {sub : MergingStrategy T nsub}
  {mid : MergingStrategy T nmid}
  {ms : MergingStrategy T nms} {i},
  SubStrategy Psub Pmid i sub mid -> SubStrategyRT Pmid Pms mid ms ->
  SubStrategyT Psub Pms sub ms.
Proof.
  intros.
  invcd H0; eauto with sub.
Qed.

#[global] Hint Resolve sub_subrt_subt : sub.

Lemma sub_subrt_subrt :
  forall {T} {Psub Pmid Pms} {nsub nmid nms}
  {sub : MergingStrategy T nsub}
  {mid : MergingStrategy T nmid}
  {ms : MergingStrategy T nms} {i},
  SubStrategy Psub Pmid i sub mid -> SubStrategyRT Pmid Pms mid ms ->
  SubStrategyRT Psub Pms sub ms.
Proof.
  intros.
  econstructor.
  eauto with sub.
Qed.

#[global] Hint Resolve sub_subrt_subrt : sub.
