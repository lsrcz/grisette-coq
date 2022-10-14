Require Import Grisette.SymBoolOp.
Require Import Grisette.GeneralTactics.
Require Import Grisette.Union.
Require Import Coq.ZArith.BinInt.
Require Import Program.
Require Import Coq.Logic.Classical_Prop.
Require Import Lia.

Create HintDb strategy discriminated.

Inductive MSSub P (n : nat) :=
  | MSSubLt : forall {n1 : nat} (m : P n1) (ev : ((n1 < n) % nat)), MSSub P n.

Arguments MSSubLt {P n n1}.

Inductive MergingStrategy T : nat -> Type :=
  | SimpleStrategy : forall (m : SymBool -> T -> T -> option T), MergingStrategy T 0
  | SortedStrategy : forall n (ind : T -> option Z) (sub : Z -> option (MSSub (MergingStrategy T) n)),
      MergingStrategy T n.

Arguments SimpleStrategy {T}.
Arguments SortedStrategy {T}.

Section MergingStrategy_ind'.
  Variable T : Type.
  Variable P : forall n : nat, MergingStrategy T n -> Prop.
  Hypothesis s_case : forall m : SymBool -> T -> T -> option T, P 0 (SimpleStrategy m).
  Hypothesis so_case : forall n (ind : T -> option Z) (sub : Z -> option (MSSub (MergingStrategy T) n))
    (IHsubs : forall v z n1 s evlt, ind v = Some z -> sub z = Some (MSSubLt s evlt) -> P n1 s),
    P n (SortedStrategy n ind sub).
  Program Fixpoint MergingStrategy_ind' n (ms : MergingStrategy T n) {measure n lt} : P n ms :=
    match ms with
    | SimpleStrategy m => s_case m
    | SortedStrategy n ind sub =>
      so_case n ind sub (fun v z n1 s evlt ev1 ev2 => MergingStrategy_ind' n1 s)
    end.
End MergingStrategy_ind'.

Definition is_sorted_strategy {T n} (ms : MergingStrategy T n) :=
  match ms with
  | SortedStrategy _ _ _ => True
  | _ => False
  end.

#[global] Hint Unfold is_sorted_strategy : strategy.

Theorem is_sorted_strategy_dec {T n} (ms : MergingStrategy T n) :
  {is_sorted_strategy ms} + {~ is_sorted_strategy ms}.
Proof.
  destruct ms; eauto with strategy.
Qed.

Definition ms_depth {T n} (t : MergingStrategy T n) : nat := n.

Definition SimpleDefinedAt {T} (m : SymBool -> T -> T -> option T) (P : T -> Prop) : Prop :=
  forall (c : SymBool) (t f : T), P t -> P f -> exists r, m c t f = Some r /\ P r.

#[global] Hint Unfold SimpleDefinedAt : strategy.

Definition SortedDefinedAt {T n}
  (ind : T -> option Z)
  (sub : Z -> option (MSSub (MergingStrategy T) n))
  (P : T -> Prop): Prop :=
  forall v, P v -> exists z n1 (s : MergingStrategy T n1) evlt, ind v = Some z /\ sub z = Some (MSSubLt s evlt).

#[global] Hint Unfold SortedDefinedAt : strategy.

Inductive DefinedAt {T} (P : T -> Prop) : forall {n}, MergingStrategy T n -> Prop :=
  | DASimple : forall {m},
    SimpleDefinedAt m P ->
    DefinedAt P (SimpleStrategy m)
  | DASorted : forall {n ind sub},
    SortedDefinedAt ind sub P ->
    DefinedAt P (SortedStrategy n ind sub).

Definition SimpleDefinedNoBeyond {T} (m : SymBool -> T -> T -> option T) (P : T -> Prop) : Prop :=
  forall (c : SymBool) (t f : T), ~ P t \/ ~ P f -> m c t f = None.

#[global] Hint Unfold SimpleDefinedAt : strategy.

Definition SortedDefinedNoBeyond {T n}
  (ind : T -> option Z)
  (sub : Z -> option (MSSub (MergingStrategy T) n))
  (P : T -> Prop): Prop :=
  forall v, ~ P v -> ind v = None.

#[global] Hint Unfold SortedDefinedAt : strategy.

Definition SortedSubDefinedNoBeyond {T n}
  (ind : T -> option Z)
  (sub : Z -> option (MSSub (MergingStrategy T) n))
  (P : T -> Prop): Prop :=
  forall v z n1 (s : MergingStrategy T n1) evlt P', ind v = Some z -> sub z = Some (MSSubLt s evlt) ->
    DefinedAt P' s -> forall v', P' v' -> P v'.

Definition SortedSubDefinedNoOverlap {T n}
  (ind : T -> option Z)
  (sub : Z -> option (MSSub (MergingStrategy T) n))
  (P : T -> Prop): Prop :=
  forall v1 v2 z1 z2 n1 n2 (s1 : MergingStrategy T n1) (s2 : MergingStrategy T n2)
    evlt1 evlt2 P1 P2,
    ind v1 = Some z1 ->
    ind v2 = Some z2 ->
    sub z1 = Some (MSSubLt s1 evlt1) ->
    sub z2 = Some (MSSubLt s2 evlt2) ->
    DefinedAt P1 s1 -> DefinedAt P2 s2 ->
    (exists v, P1 v /\ P2 v) -> z1 = z2.

Inductive ProperStrategy {T} (P : T -> Prop) : forall {n}, MergingStrategy T n -> Prop :=
  | PMSimple : forall {m},
    SimpleDefinedAt m P ->
    SimpleDefinedNoBeyond m P ->
    ProperStrategy P (SimpleStrategy m)
  | PMSorted : forall {n ind sub},
    SortedDefinedAt ind sub P ->
    SortedDefinedNoBeyond ind sub P ->
    SortedSubDefinedNoBeyond ind sub P ->
    SortedSubDefinedNoOverlap ind sub P ->
    (forall v z n1 (s : MergingStrategy T n1) evlt, ind v = Some z -> sub z = Some (MSSubLt s evlt) ->
      exists P', ProperStrategy P' s /\ P' v) ->
    ProperStrategy P (SortedStrategy n ind sub).

Lemma proper_ms_depth : forall {T} {P} {n} {ind sub} {v : T},
  ProperStrategy P (SortedStrategy n ind sub) -> P v -> n > 0.
Proof.
  intros.
  invcd H.
  apply H3 in H0 as [z' [n' [s' [evlt' [? ?]]]]].
  lia.
Qed.

#[global] Hint Resolve proper_ms_depth : strategy.

Theorem proper_ms_same_set : forall {T P1 P2 n} {s : MergingStrategy T n},
  ProperStrategy P1 s -> ProperStrategy P2 s -> (forall v, P1 v <-> P2 v).
Proof.
  intros.
  induction s using MergingStrategy_ind'; inversion H; inversion H0; subst; split; intros.
  - specialize (H2 (ConSymBool true) v v H1 H1) as [r H2].
    specialize (H6 (ConSymBool true) v v).
    assert (P2 v \/ ~ P2 v) by apply classic.
    firstorder. congruence.
  - specialize (H5 (ConSymBool true) v v H1 H1) as [r H5].
    specialize (H3 (ConSymBool true) v v).
    assert (P1 v \/ ~ P1 v) by apply classic.
    firstorder. congruence.
  - apply H3 in H1.
    destruct H1 as [? [? [? [? ?]]]].
    assert (P2 v \/ ~ P2 v) by apply classic.
    intuition.
    apply (H12 _) in H1.
    congruence.
  - apply H11 in H1.
    destruct H1 as [? [? [? [? ?]]]].
    assert (P1 v \/ ~ P1 v) by apply classic.
    intuition.
    apply (H4 _) in H1.
    congruence.
Qed.

#[global] Hint Resolve proper_ms_same_set : strategy.

Theorem proper_ms_same_set' : forall {T P1 P2 n} {s : MergingStrategy T n},
  ProperStrategy P1 s -> (forall v, P1 v <-> P2 v) -> ProperStrategy P2 s.
Proof.
  intros.
  inversion H; subst; repeat invc_existT.
  - econstructor; eauto. 
    + unfold SimpleDefinedAt in *.
      intros. specialize (H4 c t f). rewrite <- H0 in H2. rewrite <- H0 in H1. firstorder.
    + unfold SimpleDefinedNoBeyond in *.
      intros. repeat (rewrite <- H0 in H1). exact (H5 c t f H1).
  - econstructor; eauto.
    + unfold SortedDefinedAt in *.
      intros. specialize (H2 v). rewrite <- H0 in H1. firstorder.
    + unfold SortedDefinedNoBeyond in *.
      intros. rewrite <- H0 in H1. exact (H3 v H1).
    + unfold SortedSubDefinedNoBeyond in *.
      intros. specialize (H4 v z n1 s evlt P' H1 H6 H8 v' H9). firstorder.
Qed.

#[global] Hint Resolve proper_ms_same_set' : strategy.

Theorem proper_ms_implies_defined_at : forall {T P n} {s : MergingStrategy T n},
  ProperStrategy P s -> DefinedAt P s.
Proof.
  intros.
  inversion H; subst; invc_existT; constructor; auto.
Qed.

Theorem proper_ms_sub_same : forall {T P n nsub} {x1 x2 : T} {z1 z2 ind sub mssub}
  (evlt1 evlt2 : nsub < n),
  ProperStrategy P (SortedStrategy n ind sub) ->
  ind x1 = Some z1 ->
  ind x2 = Some z2 ->
  sub z1 = Some (MSSubLt mssub evlt1) ->
  sub z2 = Some (MSSubLt mssub evlt2) ->
  z1 = z2.
Proof.
  intros.
  inversion H; subst; invc_existT.
  unfold SortedDefinedNoBeyond in *.
  unfold SortedSubDefinedNoOverlap in *.
  assert (H11':=H11).
  specialize (H11 _ _ _ _ evlt1 H0 H2) as [P1 [? ?]].
  specialize (H11' _ _ _ _ evlt2 H1 H3) as [P2 [? ?]].
  specialize (proper_ms_same_set H4 H9).
  intros.
  specialize (H10 _ _ _ _ _ _ _ _ evlt1 evlt2 P1 P2 H0 H1 H2 H3).
  specialize (H10 (proper_ms_implies_defined_at H4) (proper_ms_implies_defined_at H9)).
  assert (exists v : T, P1 v /\ P2 v) by (exists x1; firstorder).
  auto.
Qed.

#[global] Hint Resolve proper_ms_sub_same : strategy.

Theorem proper_ms_ind_some_is_p : forall {T P n} {ind sub},
  ProperStrategy P (SortedStrategy n ind sub) ->
  forall (x : T) z, ind x = Some z -> P x.
Proof.
  intros.
  invcd H.
  assert (P x \/ ~ P x) by apply classic.
  intuition.
  apply H4 in H1.
  congruence.
Qed.

Theorem proper_ms_p_is_ind_some : forall {T P n} {ind sub},
  ProperStrategy P (SortedStrategy n ind sub) ->
  forall (x : T), P x -> exists z, ind x = Some z.
Proof.
  intros; invcd H; apply H3 in H0; firstorder.
Qed.

#[global] Hint Resolve proper_ms_p_is_ind_some : strategy.

Theorem proper_ms_p_ind_some_eqv : forall {T P n} {ind sub},
  ProperStrategy P (SortedStrategy n ind sub) ->
  forall (x : T), P x <-> exists z, ind x = Some z.
Proof.
  intros. split; intros; eauto with strategy.
  destruct H0.
  eapply proper_ms_ind_some_is_p; eauto.
Qed.

#[global] Hint Resolve proper_ms_p_is_ind_some : strategy.

Theorem proper_ms_ind_some_is_sub_some : forall {T P n} {ind sub},
  ProperStrategy P (SortedStrategy n ind sub) ->
  forall {x : T} {z}, ind x = Some z -> exists n1 (ev : n1 < n) s, sub z = Some (MSSubLt s ev).
Proof.
  intros.
  inversiond H.
  assert (exists z, ind x = Some z) by (exists z; auto).
  rewrite <- (proper_ms_p_ind_some_eqv H) in H1.
  apply H3 in H1.
  destruct H1 as [z' [n' [s' [evlt' [H1 H1']]]]].
  rewrite H0 in H1. invc H1.
  firstorder.
Qed.

#[global] Hint Resolve proper_ms_ind_some_is_sub_some : strategy.

Theorem proper_ms_p_is_sub_some : forall {T P n} {ind sub},
  ProperStrategy P (SortedStrategy n ind sub) ->
  forall {x : T}, P x -> exists n1 (ev : n1 < n) s z, sub z = Some (MSSubLt s ev).
Proof.
  intros.
  invcd H.
  apply H3 in H0.
  firstorder.
  repeat eexists; eauto.
Qed.

#[global] Hint Resolve proper_ms_p_is_sub_some : strategy.

Theorem proper_all_union_inject_px : forall {T P n} {ind sub} {t u},
  ProperStrategy P (SortedStrategy n ind sub) ->
  AllInUnion (fun (x : T) => ind x = Some t) u ->
  AllInUnion (fun x => P x /\ ind x = Some t) u.
Proof.
  intros.
  inversiond H.
  induction u.
  - constructor. invc H0. intuition.
    eapply proper_ms_ind_some_is_p; eauto.
  - invc H0. constructor; intuition.
Qed.

#[global] Hint Resolve proper_all_union_inject_px : strategy.

Theorem proper_all_union_sub_exist : forall {T P n} {ind sub} {t u},
  ProperStrategy P (SortedStrategy n ind sub) ->
  AllInUnion (fun (x : T) => ind x = Some t) u ->
  exists n1 (s : MergingStrategy T n1) evlt, sub t = Some (MSSubLt s evlt).
Proof.
  intros.
  inversiond H.
  induction u.
  - invc H0. specialize (proper_ms_ind_some_is_p H _ _ H2); intros.
    apply H3 in H0.
    firstorder.
    rewrite H2 in H0; invc H0.
    repeat eexists; eauto.
  - invc H0. intuition.
Qed.

#[global] Hint Resolve proper_all_union_sub_exist : strategy.
