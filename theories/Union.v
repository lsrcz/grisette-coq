Require Import Grisette.GeneralTactics.
Require Import Grisette.SymBoolOp.
Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.ZArith_dec.
Require Import Lia.
Open Scope Z.
Open Scope nat.

Create HintDb union discriminated.

#[global] Hint Resolve not_eq_con_means_not_isconc : union.

Inductive Union T :=
  | Single : T -> Union T
  | If : SymBool -> Union T -> Union T -> Union T.

Arguments Single {T} _.
Arguments If {T} _ _ _.

Definition is_single {a} (u : Union a) :=
  match u with
  | Single _ => True
  | _ => False
  end.

#[global] Hint Unfold is_single : union.

Definition is_if {a} (u : Union a) :=
  match u with
  | If _ _ _ => True
  | _ => False
  end.

#[global] Hint Unfold is_if : union.

Fixpoint union_depth {T} (t : Union T) : nat :=
  match t with
  | Single _ => 1
  | If _ t f => S (max (union_depth t) (union_depth f))
  end.

Lemma union_depth_geq_1 : forall {T} {t : Union T},
  union_depth t >= 1.
Proof.
  intros.
  induction t; simpl; lia.
Qed.

#[global] Hint Resolve union_depth_geq_1 : union.

Inductive AllInUnion {T} (P : T -> Prop) : Union T -> Prop :=
  | AIUSingle : forall {x}, P x -> AllInUnion P (Single x)
  | AIUIf : forall c {t f}, AllInUnion P t -> AllInUnion P f -> AllInUnion P (If c t f).

#[global] Hint Constructors AllInUnion : union.

Theorem all_in_union_and : forall {T} {P Q : T -> Prop} {u : Union T},
  (AllInUnion P u /\ AllInUnion Q u) <-> AllInUnion (fun x => P x /\ Q x) u.
Proof.
  intros.
  split.
  - induction u; intuition; inversion H0; inversion H1; subst; eauto with union.
  - induction u; intuition; inversion H; subst; intuition.
Qed.

#[global] Hint Resolve all_in_union_and : union.

Theorem all_in_union_implies : forall {T} {P Q : T -> Prop} {u : Union T},
  AllInUnion P u -> (forall x, P x -> Q x) -> AllInUnion Q u.
Proof.
  intros.
  induction u; inversion H; eauto with union.
Qed.

#[global] Hint Resolve all_in_union_implies : union.

Theorem all_in_union_contra : forall {T} {P : T -> Prop} Q {u : Union T},
  AllInUnion P u -> (forall x, P x -> ~ Q x) -> ~ AllInUnion Q u.
Proof.
  intros.
  induction u; inversion H; subst; intro; inversion H1; firstorder.
Qed.

#[global] Hint Resolve all_in_union_contra : union.

Inductive LeftMost {T} : T -> Union T -> Prop :=
  | LeftMostSingle : forall x, LeftMost x (Single x)
  | LeftMostIfTrue : forall b x t f, LeftMost x t -> LeftMost x (If b t f).

Inductive SubUnion {T} : forall (u1 u : Union T), Prop :=
  | SubUnionSelf : forall u, SubUnion u u
  | SubUnionIfTrue : forall u1 c t f, SubUnion u1 t -> SubUnion u1 (If c t f)
  | SubUnionIfFalse : forall u1 c t f, SubUnion u1 f -> SubUnion u1 (If c t f).

#[global] Hint Constructors LeftMost : union.
#[global] Hint Constructors SubUnion : union.

Lemma lm_exist : forall {T} (u : Union T), exists x, LeftMost x u.
Proof.
  intros.
  induction u; firstorder; eexists; eauto with union.
Qed.

#[global] Hint Resolve lm_exist : union.

Lemma lm_unique : forall {T} (u : Union T) x y, LeftMost x u -> LeftMost y u -> x = y.
Proof.
  intros.
  induction u; invc H; invc H0; eauto.
Qed.

#[global] Hint Resolve lm_unique : union.

Fixpoint left_most {T} (u : Union T) : T :=
  match u with
  | Single v => v
  | If _ t f => left_most t
  end.

Lemma left_most_correct : forall {T} {u : Union T} {t : T},
  left_most u = t <-> LeftMost t u.
Proof.
  intros.
  induction u; simpl; intuition; subst; eauto with union.
  invc H3.
  intuition.
Qed.

#[global] Hint Resolve left_most_correct : union.

Lemma left_most_correct' : forall {T} {u : Union T},
  LeftMost (left_most u) u.
Proof.
  intros.
  induction u; simpl; intuition; subst; eauto.
Qed.

#[global] Hint Resolve left_most_correct' : union.

Lemma all_in_union_exist : forall {T P} (u : Union T),
  AllInUnion P u -> exists x, P x.
Proof.
  intros.
  induction u.
  + inversion H; eauto.
  + inversion H; subst; eauto.
Qed.

#[global] Hint Resolve all_in_union_exist : union.

Lemma all_sub_union : forall {T} {u1 u : Union T} {P : T -> Prop},
  AllInUnion P u -> SubUnion u1 u -> AllInUnion P u1.
Proof.
  intros.
  induction u; invc H0; invc H; eauto with union.
Qed.

#[global] Hint Resolve all_sub_union : union.

Lemma all_in_union_left_most : forall {T} {P : T -> Prop} {u x}, AllInUnion P u -> LeftMost x u -> P x.
Proof.
  intros.
  induction u; inversion H; subst; inversion H0; subst; auto.
Qed.

Lemma all_in_union_left_most' : forall {T} {P : T -> Prop} {u}, AllInUnion P u -> P (left_most u).
Proof.
  intros. assert (LeftMost (left_most u) u) by eauto with union.
  eapply all_in_union_left_most; eauto with union.
Qed.

Lemma all_in_union_same_left_most' : forall {T} {u : Union T} {ind} {z ui : Z},
  AllInUnion (fun x => ind x = Some z) u -> Some ui = ind (left_most u) ->
  ui = z.
Proof.
  intros.
  apply all_in_union_left_most' in H.
  simpl in H.
  rewrite H in H0. invc H0. reflexivity.
Qed.

#[global] Hint Resolve all_in_union_same_left_most' : union.

Lemma all_in_union_ind_eq : forall {T} {P : T -> Prop} {u : Union T} {z1 z2} {ind : T -> option Z},
  AllInUnion (fun x : T => P x /\ ind x = Some z1) u ->
  AllInUnion (fun x : T => P x /\ ind x = Some z2) u ->
  z1 = z2.
Proof.
  intros.
  induction u.
  - inversion H; inversion H0; subst; firstorder; rewrite H3 in H4; invc H4; auto.
  - inversion H; inversion H0; subst; firstorder.
Qed.

#[global] Hint Resolve all_in_union_ind_eq : union.

Lemma all_in_union_ind_eq' : forall {T} {u : Union T} {z1 z2} {ind : T -> option Z},
  AllInUnion (fun x : T => ind x = Some z1) u ->
  AllInUnion (fun x : T => ind x = Some z2) u ->
  z1 = z2.
Proof.
  intros.
  induction u.
  - inversion H; inversion H0; subst; firstorder. rewrite H2 in H4; invc H4; auto.
  - inversion H; inversion H0; subst; firstorder.
Qed.

#[global] Hint Resolve all_in_union_ind_eq' : union.

Lemma all_in_union_ind_lt_eq : forall {T P} {u : Union T} {z z0 : Z} {ind : T -> option Z},
  AllInUnion (fun x : T => P x /\ ind x = Some z) u ->
  (z0 < z)%Z ->
  AllInUnion (fun x : T => P x /\ (exists z1 : Z, ind x = Some z1 /\ (z1 > z0)%Z)) u.
Proof.
  intros.
  induction u.
  - constructor. inversion H. subst. intuition. exists z; intuition; lia.
  - constructor; inversion H; intuition.
Qed.

#[global] Hint Resolve all_in_union_ind_lt_eq : union.

Lemma all_in_union_ind_gt_eq : forall {T P} {u : Union T} {z z0 : Z} {ind : T -> option Z},
  AllInUnion (fun x : T => P x /\ ind x = Some z) u ->
  (z > z0)%Z ->
  AllInUnion (fun x : T => P x /\ (exists z1 : Z, ind x = Some z1 /\ (z1 > z0)%Z)) u.
Proof.
  intros.
  induction u.
  - constructor. inversion H. subst. intuition. exists z; intuition; lia.
  - constructor; inversion H; intuition.
Qed.

#[global] Hint Resolve all_in_union_ind_gt_eq : union.

Lemma all_in_union_ind_lt_lt : forall {T P} {u : Union T} {z z0 : Z} {ind : T -> option Z},
  AllInUnion (fun x : T => P x /\ (exists z1 : Z, ind x = Some z1 /\ (z1 > z)%Z)) u ->
  (z0 < z)%Z ->
  AllInUnion (fun x : T => P x /\ (exists z1 : Z, ind x = Some z1 /\ (z1 > z0)%Z)) u.
Proof.
  intros.
  induction u.
  - constructor; inversion H; intuition. destruct H4. exists x0; intuition; lia.
  - constructor; inversion H; intuition.
Qed.

#[global] Hint Resolve all_in_union_ind_lt_lt : union.

Lemma all_in_union_if :
  forall {T} {P} {c} {t f : Union T},
  AllInUnion P (If c t f) <-> AllInUnion P t /\ AllInUnion P f.
Proof.
  intros. firstorder; inversion H; auto with union.
Qed.

#[global] Hint Resolve all_in_union_if : union.

Lemma all_in_union_two_inds : forall {T} {ind : T -> option Z} {u : Union T} {i j},
  AllInUnion (fun x : T => ind x = Some i) u ->
  AllInUnion (fun x : T => ind x = Some j) u ->
  i = j.
Proof.
  intros.
  specialize (all_in_union_left_most' H).
  specialize (all_in_union_left_most' H0).
  simpl.
  intros.
  rewrite H1 in H2. invcd H2. reflexivity.
Qed.

#[global] Hint Resolve all_in_union_two_inds : union.

Ltac aiu_simplify :=
  match goal with
  | [ H : AllInUnion (fun x => ?a /\ ?b) ?u |- _] =>
    let H1 := fresh "H" in
    let H2 := fresh "H" in
    assert (H1: AllInUnion (fun x => a) u) by (apply (all_in_union_implies H); firstorder);
    assert (H2: AllInUnion (fun x => b) u) by (apply (all_in_union_implies H); firstorder);
    clear H
  | [ |- AllInUnion (fun x => ?P /\ ?Q) ?u] =>
    rewrite <- all_in_union_and; simpl; split
  | [ |- AllInUnion ?P (If ?c ?t ?f)] =>
    constructor
  | [ H1 : AllInUnion (fun x => ?ind x = Some ?z) ?u,
      H2 : Some ?z' = ?ind (left_most ?u) |- _] =>
      let Hx := fresh "Hx" in
      specialize (all_in_union_same_left_most' H1 H2) as Hx; subst; try clear Hx; clear H2
  | [H1 : AllInUnion (fun x => ?ind x = Some ?z) ?u,
     H2 : AllInUnion (fun x => ?ind x = Some ?z') ?u |- _] =>
     let Hx := fresh "Hx" in
     assert (Hx:z=z') by (apply (all_in_union_two_inds H1 H2)); subst; try clear Hx; try clear H2
  end.

Ltac aiu_imply :=
  match goal with
  | [H : AllInUnion _ ?x |- AllInUnion _ ?x] => solve [apply (all_in_union_implies H); firstorder]
  | [H : AllInUnion (fun x => ?ind x = Some ?z) ?u |- AllInUnion (fun x => ?ind x = Some ?z') ?u] =>
    match goal with
    | [H' : z = z' |- _] => rewrite <- H'; apply H
    | [H' : Some z' = ?ind (left_most u) |- _] =>
      specialize (all_in_union_same_left_most' H H'); intro; subst; apply H
    | [H' : ?ind (left_most u) = Some z' |- _] => symmetry in H'; aiu_imply
    end
  | [ H1 : Some ?ti = ?ind (left_most ?u),
      H2 : AllInUnion (fun x => AllInUnion (fun y => ?ind x = ?ind y) ?u) ?u |-
      AllInUnion (fun x => ?ind x = Some ?ti) ?u] =>
    eauto with union
  end.

Lemma all_in_union_single_implies_all_in_union_nested :
  forall {T} {ind : T -> option Z} {u : Union T} {i},
  AllInUnion (fun x : T => ind x = Some i) u ->
  AllInUnion (fun x : T => AllInUnion (fun y : T => ind x = ind y) u) u.
Proof.
  intros.
  inversion H; subst; simpl; eauto with union.
  assert (forall x, ind x = Some i -> AllInUnion (fun y => ind x = ind y) (If c t f)).
  - intros. rewrite H2. aiu_imply.
  - constructor; aiu_imply.
Qed.

#[global] Hint Resolve all_in_union_single_implies_all_in_union_nested : union.

Ltac aiu_exists_single :=
  match goal with
  | [ H2 : ?ind ?v = Some ?z', H3 : (?z < ?z')%Z |-
      AllInUnion (fun x => exists z1, ?ind x = Some z1 /\ (z1 > ?z)%Z) (Single ?v)] =>
    constructor; intuition; exists z'; intuition; lia
  end.

Ltac aiu_exists_if :=
  match goal with
  | [ H1 : AllInUnion (fun x => ?ind x = Some ?z0) (If ?c ?t ?f),
      H2 : (?z < ?z0)%Z |-
      AllInUnion (fun x => (exists z1, ?ind x = Some z1 /\ (z1 > ?z)%Z)) (If ?c ?t ?f)] =>
    invc H1;
    constructor; intuition;
    multimatch goal with
    | [ H : AllInUnion (fun x => ?ind x = Some ?z0) ?s |-
        AllInUnion (fun x => (exists z1, ?ind x = Some z1 /\ (z1 > ?z)%Z)) ?s] =>
      apply (all_in_union_implies H); firstorder; exists z0; intuition; lia
    end
  end.

Ltac aiu_if :=
  match goal with
  | [ H1 : AllInUnion (fun x => ?ind x = Some ?z) ?t,
      H2 : AllInUnion (fun x => ?ind x = Some ?z) ?f |-
      AllInUnion (fun x => ?ind x = Some ?z) (If ?c ?t ?f)] =>
      constructor; auto
  end.

Ltac aiu_if_nested_aux :=
  eapply all_in_union_single_implies_all_in_union_nested; econstructor; eauto with union.

Ltac aiu_if_nested :=
  match goal with
  | [ H1 : AllInUnion (fun x => ?ind x = Some ?z) ?t,
      H2 : AllInUnion (fun x => ?ind x = Some ?z) ?f |-
      AllInUnion (fun x => AllInUnion (fun y => ?ind x = ?ind y) (If ?c ?t ?f)) (If ?c ?t ?f)] =>
      aiu_if_nested_aux
  | [ H1 : AllInUnion (fun x => ?ind x = Some ?z) ?t,
      H2 : AllInUnion (fun x => ?ind x = Some ?z) ?f |-
      AllInUnion (fun x => AllInUnion (fun y => ?ind x = ?ind y) (If ?c ?t ?f)) ?t] =>
      let H := fresh "H" in
      assert (H:AllInUnion (fun x => AllInUnion (fun y => ind x = ind y) (If c t f)) (If c t f)) by aiu_if_nested_aux
      ;invc H; auto
  | [ H1 : AllInUnion (fun x => ?ind x = Some ?z) ?t,
      H2 : AllInUnion (fun x => ?ind x = Some ?z) ?f |-
      AllInUnion (fun x => AllInUnion (fun y => ?ind x = ?ind y) (If ?c ?t ?f)) ?f] =>
      let H := fresh "H" in
      assert (H:AllInUnion (fun x => AllInUnion (fun y => ind x = ind y) (If c t f)) (If c t f)) by aiu_if_nested_aux;
      invc H; auto
  end.

Ltac aiu_contra :=
  match goal with
  | [ H1 : Some ?z = ?ind (left_most ?u),
      H2 : AllInUnion (fun x => exists z1, ?ind x = Some z1 /\ (z1 > ?z)%Z) ?u |- _] =>
    let Hx := fresh "Hx" in
    specialize (all_in_union_left_most' H2) as [? [Hx ?]]; rewrite Hx in H1; invc H1; lia
  end.

Ltac solve_aiu :=
  solve [
    repeat aiu_simplify;
    solve [
        aiu_exists_single
      | aiu_exists_if
      | aiu_imply
      | aiu_if
      | aiu_if_nested
      | aiu_contra
      | lia]].

Lemma all_in_union_nested_lm : forall {T} {ind : T -> option Z} {u : Union T} {i},
  AllInUnion (fun x : T => AllInUnion (fun y : T => ind x = ind y) u) u ->
  Some i = ind (left_most u) ->
  AllInUnion (fun x : T => ind x = Some i) u.
Proof.
  intros.
  remember (left_most u).
  symmetry in Heqt.
  rewrite left_most_correct in Heqt.
  specialize (all_in_union_left_most H Heqt).
  simpl in *.
  intros.
  rewrite H0. eauto with union.
Qed.

#[global] Hint Resolve all_in_union_nested_lm : union.

Lemma all_in_union_lower_bound : forall {T} {ind : T -> option Z} {u : Union T} {i il : Z},
  AllInUnion (fun x : T => ind x = Some i) u ->
  (il < i)%Z ->
  AllInUnion (fun x : T => exists z, ind x = Some z /\ (z > il)%Z) u.
Proof.
  intros.
  induction u; repeat aiu_simplify.
  - invc H. constructor. exists i. intuition. lia.
  - invc H. intuition.
  - invc H. intuition.
Qed.

#[global] Hint Resolve all_in_union_lower_bound : union.

Lemma all_in_union_lower_bound' : forall {T} {ind : T -> option Z} {u : Union T} {i il : Z},
  AllInUnion (fun x : T => exists z, ind x = Some z /\ (z > i)%Z) u ->
  (il < i)%Z ->
  AllInUnion (fun x : T => exists z, ind x = Some z /\ (z > il)%Z) u.
Proof.
  intros.
  induction u; repeat aiu_simplify.
  - invc H. destruct H2 as [? ?]. constructor. exists x. intuition. lia.
  - invc H. intuition.
  - invc H. intuition.
Qed.

#[global] Hint Resolve all_in_union_lower_bound' : union.
