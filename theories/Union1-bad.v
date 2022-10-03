Require Import Grisette.SymBoolOp.
Require Import Coq.ZArith.Int.
Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.ZArith_dec.
Require Import Lia.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Logic.ClassicalFacts.
Require Import Coq.Logic.Classical_Prop.
Require Import Grisette.CpdtTactics.
Open Scope Z.

Ltac invc H := inversion H; subst; clear H.

Inductive Union a :=
  | Single : a -> Union a
  | If : SymBool -> Union a -> Union a -> Union a.

Arguments Single {a} _.
Arguments If {a} _ _ _.

Inductive InUnion a : a -> Union a -> Prop :=
  | InSingle : forall x, InUnion a x (Single x)
  | InIfTrue : forall b x f t, InUnion a x t -> InUnion a x (If b t f)
  | InIfFalse : forall b x t f, InUnion a x f -> InUnion a x (If b t f).

Arguments InUnion {a} _ _.
Arguments InSingle {a} _.
Arguments InIfTrue {a} _ _ _ _.
Arguments InIfFalse {a} _ _ _ _.

Hint Constructors InUnion.

Inductive AllValue {a} : Union a -> (a -> Prop) -> Prop :=
  | AllSingle : forall {x} {P : a -> Prop}, P x -> AllValue (Single x) P
  | AllIf : forall {b t f} {P : a -> Prop}, AllValue t P -> AllValue f P -> AllValue (If b t f) P.

Inductive LeftMost a : a -> Union a -> Prop :=
  | LeftMostSingle : forall x, LeftMost a x (Single x)
  | LeftMostIfTrue : forall b x t f, LeftMost a x t -> LeftMost a x (If b t f).

Arguments LeftMost {a} _ _.
Arguments LeftMostSingle {a} _.
Arguments LeftMostIfTrue {a b} _ _ _.

Hint Constructors LeftMost.

Lemma LeftMostIsInUnion : forall {a} {x : a} {u}, LeftMost x u -> InUnion x u.
Proof.
  intros.
  induction H; auto.
Qed.

Hint Resolve LeftMostIsInUnion.

Lemma LeftMostExistence : forall {a} (u : Union a), exists x, LeftMost x u.
Proof.
  intros.
  induction u.
  - exists a0. auto.
  - destruct IHu1 as [x1 Hx1].
    exists x1. auto.
Qed.

Lemma LeftMostUnique : forall {a} (u : Union a) x y, LeftMost x u -> LeftMost y u -> x = y.
Proof.
  intros.
  induction u; invc H; invc H0; auto.
Qed.

Inductive MergingStrategy a :=
  | SimpleStrategy : forall (m: SymBool -> a -> a -> option a), MergingStrategy a
  | SortedStrategy : forall (ind : a -> option Z) (sub : Z -> option (MergingStrategy a)), MergingStrategy a.

Print nat_ind.
Print MergingStrategy_ind.

Arguments SimpleStrategy {a}.
Arguments SortedStrategy {a}.

(*
Fixpoint height {a} (u : MergingStrategy a) : nat :=
  match u with
  | SimpleStrategy _ => 0
  | SortedStrategy _ sub => S (max (height (sub 0)) (height (sub 1)))
  end.

Fixpoint MergingStrategy_ind' (a : Type) (P : MergingStrategy a -> Prop)
    (f1 : forall (m : SymBool -> a -> a -> option a), P (SimpleStrategy m))
    (f2 : forall (ind : a -> option Z) (sub : Z -> option (MergingStrategy a)),
      (forall a z s, ind a = Some z -> sub z = Some s -> P s) -> P (SortedStrategy ind sub))
    (s : MergingStrategy a) : P s :=
  match s as s0 return (P s0) with
  | SimpleStrategy m => f1 m
  | SortedStrategy ind sub => f2 ind sub (fun a1 z s H1 H2 => MergingStrategy_ind' a P f1 f2 s)
  end.
  *)


Inductive ProperStrategy {a} (P : a -> Prop) : MergingStrategy a -> Prop :=
  | ProperSimpleStrategy : forall m,
    (forall b x y, (P x /\ P y) <-> exists v, m b x y = Some v) ->
    (forall b x y v, m b x y = Some v -> P v) ->
    ProperStrategy P (SimpleStrategy m)
  | ProperSortedStrategy : forall ind sub,
    (forall x, P x -> (exists z s, ind x = Some z /\ sub z = Some s)) ->
    (forall x z s, ind x = Some z /\ sub z = Some s -> exists P1, ProperStrategy P1 s /\ P1 x /\
       forall y, P1 y -> P y /\ ind y = Some z <-> P1 y) ->
    (forall x, ~ P x -> ind x = None) ->
    ProperStrategy P (SortedStrategy ind sub).

Definition SubStrategy {a} (P : a -> Prop) ind sub (ssub : MergingStrategy a) : Prop :=
  ProperStrategy P (SortedStrategy ind sub) /\ exists x z, P x /\ ind x = Some z /\ sub z = Some ssub.

Inductive HM {a} (P : a -> Prop) : MergingStrategy a -> Union a -> Prop :=
  | HMSingle : forall (m : SymBool -> a -> a -> option a) x,
    ProperStrategy P (SimpleStrategy m) ->
    P x ->
    HM P (SimpleStrategy m) (Single x)
  | HMSortedS : forall (ind : a -> option Z) (sub : Z -> option (MergingStrategy a))
    (x : a) (z : Z) (s : MergingStrategy a) (P1 : a -> Prop),
    ProperStrategy P (SortedStrategy ind sub) ->
    ind x = Some z ->
    sub z = Some s ->
    P x ->
    P1 x ->
    HM P1 s (Single x) ->
    HM P (SortedStrategy ind sub) (Single x)
  | HMSortedIDeg : forall (ind : a -> option Z) (sub : Z -> option (MergingStrategy a))
    c (t1 f1 : a) (t f : Union a) (z : Z) (s : MergingStrategy a) (P1 : a -> Prop),
    ProperStrategy P (SortedStrategy ind sub) ->
    ind t1 = ind f1 ->
    LeftMost t1 t ->
    LeftMost f1 f ->
    sub z = Some s ->
    ProperStrategy P1 s ->
    (forall v, InUnion v t -> P v /\ P1 v /\ ind v = Some z) ->
    (forall v, InUnion v f -> P v /\ P1 v /\ ind v = Some z) ->
    HM P1 s (If c t f) ->
    HM P (SortedStrategy ind sub) t ->
    HM P (SortedStrategy ind sub) f ->
    HM P (SortedStrategy ind sub) (If c t f)
  | HMSortedI : forall (ind : a -> option Z) (sub : Z -> option (MergingStrategy a))
    c (t1 f1 : a) (t f : Union a) (zt : Z) (zf : Z) (s : MergingStrategy a) (P1 : a -> Prop),
    ProperStrategy P (SortedStrategy ind sub) ->
    ind t1 = Some zt ->
    ind f1 = Some zf ->
    zt < zf ->
    LeftMost t1 t ->
    LeftMost f1 f ->
    sub zt = Some s ->
    ProperStrategy P1 s ->
    (forall v, InUnion v t -> P v /\ P1 v /\ ind v = Some zt) ->
    (forall v, InUnion v f -> P v) ->
    HM P1 s t ->
    HM P (SortedStrategy ind sub) t ->
    HM P (SortedStrategy ind sub) f ->
    HM P (SortedStrategy ind sub) (If c t f).

Arguments HMSingle {a} P {m} {x} _ _.
Arguments HMSortedS {a} P {ind sub x z s P1} _ _ _ _.

Hint Constructors HM.

Lemma HMInUnionP : forall {a} {P : a -> Prop} {s : MergingStrategy a} {u}, HM P s u -> forall x, InUnion x u -> P x.
Proof.
  intros.
  inversion H; inversion H0; inversion H1; subst; eauto; try congruence.
  - inversion H16; subst; eauto. specialize (H7 x H14). intuition.
  - inversion H16; subst; eauto. specialize (H8 x H14). intuition.
  - inversion H18; subst. specialize (H9 x H16). intuition.
  - inversion H18; subst. apply (H10 x H16).
Qed.

Lemma ProperStrategySameSet : forall {a} {P1 P2 : a -> Prop} {s}, ProperStrategy P1 s -> ProperStrategy P2 s ->
  forall x, P1 x <-> P2 x.
Proof.
  intros.
  induction s; inversion H; inversion H0; subst; try congruence; split.
  1-2: 
    specialize (H3 (ConSymBool true) x x);
    specialize (H2 (ConSymBool true) x x);
    specialize (H5 (ConSymBool true) x x);
    specialize (H6 (ConSymBool true) x x);
    intuition.
  - intros. specialize (H3 x H1). destruct H3 as [z[s[H3 H3']]].
    assert (P2 x \/ ~ P2 x). { apply classic. }
    intuition.
    apply H10 in H6. congruence.
  - intros. specialize (H8 x H1). destruct H8 as [z[s[H8 H8']]].
    assert (P1 x \/ ~ P1 x). { apply classic. }
    intuition.
    apply H5 in H6. congruence.
Qed.

Lemma ProperStrategySameSubSet : forall {a} {P : a -> Prop} {ind sub}, ProperStrategy P (SortedStrategy ind sub) ->
  forall {x z s P1}, ind x = Some z -> sub z = Some s -> ProperStrategy P1 s -> forall y, P1 y -> P y /\ ind y = Some z.
Proof.
  intros.
  invc H. inversion H2. subst.
  - specialize (H7 x z (SimpleStrategy m)); intuition;
    destruct H5 as [P1' H5]; intuition;
    specialize (ProperStrategySameSet H2 H7); intros;
    rewrite H9 in H3.
    + rewrite <- H10 in H3.
      assert (P y \/ ~ P y). { apply classic. }
      intuition. apply H3.
    + assert (P1' y). apply H3.
      apply H10 in H3.
      intuition.
  - specialize (H7 x z s); intuition;
    destruct H10 as [P1' H10]; intuition;
    specialize (ProperStrategySameSet H2 H7); intros;
    rewrite H11 in H3; specialize (H12 y); intuition.
Qed.

Ltac invc_all_safe_HM :=
  repeat match goal with
           | [ H : HM _ (SimpleStrategy _) _ |- _ ] => invc H
           | [ H : HM _ (SortedStrategy _) (If _ _ _) |- _ ] => invc H
         end; subst.

Ltac elim_same :=
  match goal with
    | [ H : ?x = ?x |- _ ] => clear H
  end.

Ltac find_same_l :=
  match goal with
    | [ H1 : ?x = _, H2 : ?x = _ |- _ ] => rewrite H1 in H2; invc H2
    | [ H1 : ?x = _, H2 : _ = ?x |- _ ] => rewrite H1 in H2; invc H2
  end.

Ltac find_same_r :=
  match goal with
    | [ H1 : _ = ?x, H2 : ?x = _ |- _ ] => rewrite <- H1 in H2; invc H2
    | [ H1 : _ = ?x, H2 : _ = ?x |- _ ] => rewrite <- H1 in H2; invc H2
  end.

Ltac find_dup_strategy :=
  repeat match goal with
    | [ H : SimpleStrategy _ = SimpleStrategy _ |- _ ] => invc H
    | [ H : SortedStrategy _ _ = SortedStrategy _ _ |- _ ] => invc H
  end.

Ltac find_dup_leftmost :=
  repeat match goal with
    | [ H1 : LeftMost ?x ?u, H2 : LeftMost ?y ?u |- _ ] => specialize (LeftMostUnique u x y H1 H2); intro; subst; clear H1
  end.

Ltac find_same_proper_setpred P1 P2 :=
  match goal with
    | [ H1 : ProperStrategy P1 ?x, H2 : ProperStrategy P2 ?x |- _ ] => specialize (ProperStrategySameSet H1 H2); intro
  end.

Ltac use_same_setpred :=
  match goal with
    | [ H : forall x : _, ?p1 x <-> ?p2 x, H' : ?p1 ?xt |- ?p2 ?xt ] => rewrite H in H'; exact H'
    | [ H : forall x : _, ?p1 x <-> ?p2 x, H' : ?p2 ?xt |- ?p1 ?xt ] => rewrite <- H in H'; exact H'
  end.

Ltac solve_in_union :=
  match goal with
    | [ H1 : LeftMost ?x ?u, H2 : forall v : _, InUnion v ?u -> ?P1 v /\ _ /\ _ |- ?P1 ?x ] =>
        apply LeftMostIsInUnion in H1; apply H2 in H1; intuition
    | [ H1 : LeftMost ?x ?u, H2 : forall v : _, InUnion v ?u -> _ /\ ?P1 v /\ _ |- ?P1 ?x ] =>
        apply LeftMostIsInUnion in H1; apply H2 in H1; intuition
    | [ H1 : LeftMost ?x ?u, H2 : forall v : _, InUnion v ?u -> _ /\ _ /\ ?ind v = Some ?z |- ?ind ?x = Some ?z ] =>
        apply LeftMostIsInUnion in H1; apply H2 in H1; intuition
    | [ H1 : InUnion ?x ?u, H2 : forall v : _, InUnion v ?u -> ?P1 v /\ _ /\ _ |- ?P1 ?x ] =>
        apply H2 in H1; intuition
    | [ H1 : InUnion ?x ?u, H2 : forall v : _, InUnion v ?u -> _ /\ ?P1 v /\ _ |- ?P1 ?x ] =>
        apply H2 in H1; intuition
    | [ H1 : InUnion ?x ?u, H2 : forall v : _, InUnion v ?u -> _ /\ _ /\ ?ind v = Some ?z |- ?ind ?x = Some ?z ] =>
        apply H2 in H1; intuition
    | [ H2 : forall v : _, InUnion v (Single ?x) -> ?P1 v /\ _ /\ _ |- ?P1 ?x ] =>
        specialize (H2 _ (InSingle x)); intuition
    | [ H2 : forall v : _, InUnion v (Single ?x) -> _ /\ ?P1 v /\ _ |- ?P1 ?x ] =>
        specialize (H2 _ (InSingle x)); intuition
    | [ H2 : forall v : _, InUnion v (Single ?x) -> _ /\ _ /\ ?ind v = Some ?z |- ?ind ?x = Some ?z ] =>
        specialize (H2 _ (InSingle x)); intuition
    | [ H1 : InUnion ?v1 ?t, H2 : forall v : _, InUnion v (If ?c ?t ?f) -> ?P1 v /\ _ /\ _ |- ?P1 ?v1 ] =>
        specialize (H2 _ (InIfTrue c v1 f t H1)); intuition
    | [ H1 : InUnion ?v1 ?t, H2 : forall v : _, InUnion v (If ?c ?t ?f) -> _ /\ ?P1 v /\ _ |- ?P1 ?v1 ] =>
        specialize (H2 _ (InIfTrue c v1 f t H1)); intuition
    | [ H1 : InUnion ?v1 ?t, H2 : forall v : _, InUnion v (If ?c ?t ?f) -> _ /\ _ /\ ?ind v = Some ?z |- ?ind ?v1 = Some ?z ] =>
        specialize (H2 _ (InIfTrue c v1 f t H1)); intuition
    | [ H1 : InUnion ?v1 ?f, H2 : forall v : _, InUnion v (If ?c ?t ?f) -> ?P1 v /\ _ /\ _ |- ?P1 ?v1 ] =>
        specialize (H2 _ (InIfFalse c v1 t f H1)); intuition
    | [ H1 : InUnion ?v1 ?f, H2 : forall v : _, InUnion v (If ?c ?t ?f) -> _ /\ ?P1 v /\ _ |- ?P1 ?v1 ] =>
        specialize (H2 _ (InIfFalse c v1 t f H1)); intuition
    | [ H1 : InUnion ?v1 ?f, H2 : forall v : _, InUnion v (If ?c ?t ?f) -> _ /\ _ /\ ?ind v = Some ?z |- ?ind ?v1 = Some ?z ] =>
        specialize (H2 _ (InIfFalse c v1 t f H1)); intuition
  end.

Ltac invc_all_simple_inunion :=
  repeat match goal with
           | [ H : InUnion _ (Single _) |- _ ] => invc H
           | [ H : InUnion _ (If _ _ _) |- _ ] => invc H
         end; subst.

Lemma PMSameSet : forall {a} {P1 P2 : a -> Prop} {s},
  (forall x, P1 x <-> P2 x) -> ProperStrategy P1 s -> ProperStrategy P2 s.
Proof.
  intros.
  inversion H0.
  - constructor; intros; eauto.
    + split.
      * intros. intuition. rewrite <- H in H5. rewrite <- H in H6. specialize (H1 b x y). intuition.
      * intros. intuition; specialize (H1 b x y); intuition; rewrite H in H6; rewrite H in H7; intuition.
    + apply H2 in H4. rewrite H in H4. auto.
  - constructor; intros; eauto.
    + rewrite <- H in H5. apply H1 in H5. auto.
    + apply H2 in H5. destruct H5. intuition.
      exists x0. intuition; apply H8 in H7; intuition; rewrite H in H11; auto.
    + assert (P1 x \/ ~ P1 x). { apply classic. }
      intuition.
      rewrite H in H7. congruence.
Qed.

Hint Resolve PMSameSet.

Inductive SubUnion {a} : Union a -> Union a -> Prop :=
  | SubUnionReflexive : forall (u : Union a), SubUnion u u
  | SubUnionLeft: forall c (t f u: Union a), SubUnion u t -> SubUnion u (If c t f)
  | SubUnionRight: forall c (t f u: Union a), SubUnion u f -> SubUnion u (If c t f).

Lemma HMSubUnion : forall {a} {P1 : a -> Prop} {s u u1},
  HM P1 s u -> SubUnion u1 u -> HM P1 s u1.
Proof.
  intros.
  generalize dependent u1.
  generalize dependent s.
  generalize dependent P1.
  induction u; intros.
  - inversion H0. auto.
  - inversion H0; subst; auto.
    + inversion H; subst.
      apply (IHu1 _ _ H15 _ H3).
      apply (IHu1 _ _ H17 _ H3).
    + inversion H; subst.
      apply (IHu2 _ _ H16 _ H3).
      apply (IHu2 _ _ H18 _ H3).
Qed.

Lemma HMSameSet : forall {a} {P1 P2 : a -> Prop} {s u1},
  (forall x, P1 x <-> P2 x) -> HM P1 s u1 -> HM P2 s u1.
Proof.
  intros.
  generalize dependent P1.
  generalize dependent P2.
  generalize dependent s.
  induction u1; intros.
  - inversion H0; subst; auto.
    + eapply HMSingle; eauto.
      rewrite H in H4. auto.
    + eapply HMSortedS; eauto.
      rewrite H in H5. auto.
  - inversion H0; subst.
    + eapply HMSortedIDeg; eauto; intros.
      * apply H10 in H1. intuition. rewrite H in H2. auto.
      * apply H11 in H1. intuition. rewrite H in H2. auto.
    + eapply HMSortedI.
      4: apply H7.
      all: eauto; intros.
      * apply H12 in H1. intuition. rewrite H in H2. auto.
      * apply H13 in H1. intuition. rewrite H in H1. auto.
Qed.

Inductive EvalTerms a :=
  | EvalValue : Union a -> EvalTerms a
  | MrgIf : forall (ms : MergingStrategy a) (c : SymBool) (t f: Union a), EvalTerms a
  | SSMrgIf : forall (ms : MergingStrategy a) (c : SymBool) (t f: Union a), EvalTerms a
  | ISMrgIf : forall (ms : MergingStrategy a) (c : SymBool) (t f: Union a), EvalTerms a
  | SIMrgIf : forall (ms : MergingStrategy a) (c : SymBool) (t f: Union a), EvalTerms a
  | IIMrgIf : forall (ms : MergingStrategy a) (c : SymBool) (t f: Union a), EvalTerms a.

Hint Constructors EvalTerms.

Arguments EvalValue {a}.
Arguments MrgIf {a}.
Arguments SSMrgIf {a}.
Arguments ISMrgIf {a}.
Arguments SIMrgIf {a}.
Arguments IIMrgIf {a}.

Definition IsSortedStrategy {a} (ms : MergingStrategy a) :=
  match ms with
  | SortedStrategy _ _ => True
  | _ => False
  end.

Hint Unfold IsSortedStrategy.

Definition IsSingle {a} (u : Union a) :=
  match u with
  | Single _ => True
  | _ => False
  end.

Hint Unfold IsSingle.

Definition IsIf {a} (u : Union a) :=
  match u with
  | If _ _ _ => True
  | _ => False
  end.

Definition IsSome {a} (o : option a) :=
  match o with
  | Some _ => True
  | None => False
  end.

Hint Unfold IsIf.

Print SubStrategy.

Inductive EvalTermsGood {a} P : MergingStrategy a -> EvalTerms a -> Prop :=
  | EvalValueGood : forall {ms u}, HM P ms u -> EvalTermsGood P ms (EvalValue u)
  | MrgIfGood : forall {ms c t f},
    HM P ms t -> 
    HM P ms f -> 
    EvalTermsGood P ms (MrgIf ms c t f)
  | SortedSSGood : forall {c t f ind sub}
    (et : HM P (SortedStrategy ind sub) t) 
    (ef : HM P (SortedStrategy ind sub) f),
    ~ IsConc c ->
    (forall v1 v2, InUnion v1 t -> InUnion v2 t -> ind v1 = ind v2) ->
    (forall v1 v2, InUnion v1 f -> InUnion v2 f -> ind v1 = ind v2) ->
    EvalTermsGood P (SortedStrategy ind sub) (SSMrgIf (SortedStrategy ind sub) c t f)
  | SortedISGood : forall {c t f ind sub}
    (et : HM P (SortedStrategy ind sub) t) 
    (ef : HM P (SortedStrategy ind sub) f),
    ~ IsConc c ->
    IsIf t ->
    (forall v1 v2, InUnion v1 f -> InUnion v2 f -> ind v1 = ind v2) ->
    EvalTermsGood P (SortedStrategy ind sub) (ISMrgIf (SortedStrategy ind sub) c t f)
  | SortedSIGood : forall {c t f ind sub}
    (et : HM P (SortedStrategy ind sub) t) 
    (ef : HM P (SortedStrategy ind sub) f),
    ~ IsConc c ->
    (forall v1 v2, InUnion v1 t -> InUnion v2 t -> ind v1 = ind v2) ->
    IsIf f ->
    EvalTermsGood P (SortedStrategy ind sub) (SIMrgIf (SortedStrategy ind sub) c t f)
  | SortedIIGood : forall {c t f ind sub}
    (et : HM P (SortedStrategy ind sub) t) 
    (ef : HM P (SortedStrategy ind sub) f),
    ~ IsConc c ->
    IsIf t ->
    IsIf f ->
    EvalTermsGood P (SortedStrategy ind sub) (IIMrgIf (SortedStrategy ind sub) c t f).

Hint Constructors EvalTermsGood.

Arguments EvalValueGood {a P ms u}.
Arguments MrgIfGood {a P ms c t f}.
Arguments SortedSSGood {a P c t f ind sub}.

Inductive EvalRule {a} : EvalTerms a -> EvalTerms a -> Prop :=
  | MrgIfTrue : forall (ms : MergingStrategy a) t f,
    EvalRule (MrgIf ms (ConSymBool true) t f) (EvalValue t)
  | MrgIfFalse : forall (ms : MergingStrategy a) t f,
    EvalRule (MrgIf ms (ConSymBool false) t f) (EvalValue f)
  | MrgIfSimple : forall (m : SymBool -> a -> a -> option a) (c : SymBool) (t f: a) v1,
    m c t f = Some v1 ->
    ~ IsConc c ->
    EvalRule (MrgIf (SimpleStrategy m) c (Single t) (Single f)) (EvalValue (Single v1))
  | MrgIfSortedSS : forall s c t f,
    IsSortedStrategy s ->
    ~ IsConc c ->
    IsSingle t ->
    IsSingle f ->
    EvalRule (MrgIf s c t f) (SSMrgIf s c t f)
  | MrgIfSortedSI : forall s c t f,
    IsSortedStrategy s ->
    ~ IsConc c ->
    IsSingle t ->
    IsIf f ->
    EvalRule (MrgIf s c t f) (SIMrgIf s c t f)
  | MrgIfSortedIS : forall s c t f,
    IsSortedStrategy s ->
    ~ IsConc c ->
    IsIf t ->
    IsSingle f ->
    EvalRule (MrgIf s c t f) (ISMrgIf s c t f)
  | MrgIfSortedII : forall s c t f,
    IsSortedStrategy s ->
    ~ IsConc c ->
    IsIf t ->
    IsIf f ->
    EvalRule (MrgIf s c t f) (IIMrgIf s c t f)
  | SSLt : forall idx sub c t f t1 f1 ti fi,
    LeftMost t1 t ->
    LeftMost f1 f ->
    idx t1 = Some ti ->
    idx f1 = Some fi ->
    ti < fi ->
    EvalRule (SSMrgIf (SortedStrategy idx sub) c t f) (EvalValue (If c t f))
  | SSEq : forall idx sub c t f t1 f1 ti fi ts,
    LeftMost t1 t ->
    LeftMost f1 f ->
    idx t1 = Some ti ->
    idx f1 = Some fi ->
    ti = fi ->
    sub ti = Some ts ->
    EvalRule (SSMrgIf (SortedStrategy idx sub) c t f) (MrgIf ts c t f)
  | SSGt : forall idx sub c t f t1 f1 ti fi,
    LeftMost t1 t ->
    LeftMost f1 f ->
    idx t1 = Some ti ->
    idx f1 = Some fi ->
    ti > fi ->
    EvalRule (SSMrgIf (SortedStrategy idx sub) c t f) (EvalValue (If (pnegsb c) f t)).

Arguments clos_trans {A} _ _ _.

Notation "t1 '==>' t2" := (EvalRule t1 t2) (at level 75).
Notation "t1 '==>*' t2" := (clos_trans EvalRule t1 t2) (at level 75).

Hint Constructors EvalRule.

Theorem progress : forall a P (ms : MergingStrategy a) t, EvalTermsGood P ms t ->
  (exists u, t = (EvalValue u)) \/ (exists t', t ==> t' /\ EvalTermsGood P ms t') \/
  (exists t' ind sub ssub P', t ==> t' /\ EvalTermsGood P' ssub t' /\ SubStrategy P ind sub ssub).
Proof.
  intros.
  invc H.
  left. eexists; eauto.
  all: right.
  - left. destruct (IsConcDec c) as [Hc|Hc].
    + destruct c; inversion Hc. destruct b; eexists; split; eauto.
    + destruct ms.
      * invc_all_safe_HM; invc H2.
        destruct (H0 c x0 x).
        crush.
        eexists; split; eauto.
      * destruct t0; destruct f;
        eexists; split; try eauto;
        [apply SortedSSGood | apply SortedSIGood | apply SortedISGood];
        intros; eauto; inversion H; inversion H2; subst; eauto.
  - destruct (LeftMostExistence t0) as [t1 Ht1].
    destruct (LeftMostExistence f) as [f1 Hf1].
    invc et; invc ef; subst; eauto; try congruence.
    Ltac solve_simple_case zt' zf' lt :=
        assert (zt' < zf') by lia; find_dup_leftmost;
        eexists; split;
        match lt with
        | True => try eapply SSLt
        | _ => try eapply SSGt
        end;
        eauto; try solve [solve_in_union];
        constructor; eapply HMSortedI with (zt := zt') (zf := zf'); eauto; intros; invc_all_simple_inunion; intuition; solve_in_union.
    Ltac bad_in_union :=
          match goal with
          | [ Heq : forall v1 v2 : _, InUnion v1 (If ?c ?t ?f) -> InUnion v2 (If ?c ?t ?f) -> ?ind v1 = ?ind v2,
              Hit0 : ?ind ?t0 = Some ?zt,
              Hif0 : ?ind ?f0 = Some ?zf,
              HLMt0 : LeftMost ?t0 ?t,
              HLMf0 : LeftMost ?f0 ?f |- _] =>
            let ht := fresh "Ht" in
            let hf := fresh "Hf" in
            assert (zt = zf) by
            ( assert (InUnion t0 t) by (exact (LeftMostIsInUnion HLMt0));
              assert (InUnion f0 f) by (exact (LeftMostIsInUnion HLMf0));
              assert (Ht:InUnion t0 (If c t f)) by (constructor; auto);
              assert (Hf:InUnion f0 (If c t f)) by (constructor; auto);
              specialize (Heq _ _ Ht Hf); rewrite Hit0 in Heq; rewrite Hif0 in Heq; invc Heq; auto); lia
          end.
    Ltac solve_eq_case_step1 t' ind0 sub0 s0 P0 :=
      repeat find_same_r;
      repeat find_same_l;
      exists t';
      exists ind0; exists sub0; exists s0;
      exists P0.
    Ltac solve_eq_case_step2 P0 P1 :=
      subst; intuition; eauto; try congruence;
      intuition; eauto; find_dup_strategy;
      econstructor; eauto; try solve solve_in_union;
      econstructor; eauto; find_same_proper_setpred P0 P1; use_same_setpred.
    + destruct (Z_dec z z0) as [[Hlt|Hgt]|Heq].
      * left. invc Ht1; invc Hf1; invc H10; invc H16; solve_simple_case z z0 True.
      * left. invc Ht1; invc Hf1; invc H10; invc H16; solve_simple_case z0 z False.
      * right. invc Ht1; invc Hf1.
        solve_eq_case_step1 (MrgIf s0 c (Single x) (Single x0)) ind sub s0 P0.
        inversion H10; inversion H16; subst; solve_eq_case_step2 P0 P1.
    + destruct (Z_dec z z0) as [[Hlt|Hgt]|Heq].
      * left. invc Ht1; invc Hf1; invc H10; invc H19; solve_simple_case z z0 True.
      * left. invc Ht1; invc Hf1; invc H10; invc H19; solve_simple_case z0 z False.
      * right. invc Ht1; invc Hf1. solve_eq_case_step1 (MrgIf s0 c (Single x) (If c0 t f2)) ind sub s0 P0.
        inversion H10; inversion H19; subst; solve_eq_case_step2 P0 P1.
    + destruct (Z_dec z zt) as [[Hlt|Hgt]|Heq].
      * left. invc Ht1; invc Hf1; invc H10; solve_simple_case z zt True.
      * bad_in_union.
      * bad_in_union.
    + destruct (Z_dec z z0) as [[Hlt|Hgt]|Heq].
      * left. invc Ht1; invc Hf1; invc H21; solve_simple_case z z0 True.
      * left. invc Ht1; invc Hf1; invc H21; solve_simple_case z0 z False.
      * right. invc Ht1; invc Hf1. solve_eq_case_step1 (MrgIf s0 c (If c0 t f2) (Single x)) ind sub s0 P0.
        split. econstructor; eauto. solve_in_union.
        split. econstructor; eauto.
        inversion H12; inversion H21; subst.

        all: intuition; eauto; try congruence.
        all: intuition; eauto; find_dup_strategy.
        all: econstructor; eauto; try solve solve_in_union.
        -- 
        specialize (H45 x z1 s1).
        intuition.
        destruct H.
        intuition.
        econstructor; eauto; find_same_proper_setpred P0 P1; try use_same_setpred.
        econstructor; eauto; find_same_proper_setpred P0 P1; try use_same_setpred.
        
        
        solve_eq_case_step2 P0 P1.

        intuition.
        econstructor; eauto; try solve_in_union.
        econstructor.
        assert (HM P0 s0 (If c0 t f2)). admit. auto. auto.

        econstructor; auto. exists x; exists z0; intuition; auto.
    +


        inversion H13; inversion H19; subst; try congruence.

        all: intuition; eauto; try congruence; intuition; eauto; find_dup_strategy;
        econstructor; eauto; try solve_in_union.
        econstructor; eauto; find_same_proper_setpred P0 P1; use_same_setpred.
        
        try solve_eq_case_step2 P1 P0.
        

  

    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
  - admit.
  - admit.
  - admit.

        
        eexists; split.
        -- eapply SSEq; eauto; try congruence.
           eapply MrgIfSimple; eauto.
           inversion H3. inversion H18. subst.  
        -- admit.
        --  eapply MrgIfSimple; auto.
        eapply EvalValueGood; eapply HMSortedI.
      