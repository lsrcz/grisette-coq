Require Import Grisette.SymBoolOp.
Require Import Coq.ZArith.Int.
Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.ZArith_dec.
Require Import Lia.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.
Open Scope Z.

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

Lemma LeftMostExistence : forall {a} (u : Union a), exists x, LeftMost x u.
Proof.
  intros.
  induction u.
  - exists a0. auto.
  - destruct IHu1 as [x1 Hx1].
    exists x1. auto.
Qed.

Definition eqp {T} {P : T -> Prop} (a b : { x : T | P x}) : Prop := proj1_sig a = proj1_sig b.

Definition ltp {PZ : Z -> Prop} (a b : { x : Z | PZ x}) : Prop := proj1_sig a < proj1_sig b.

Definition gtp {PZ : Z -> Prop} (a b : { x : Z | PZ x}) : Prop := proj1_sig a > proj1_sig b.

Theorem eqpltpgtp_dec : forall {PZ : Z -> Prop} (a b : { x : Z | PZ x}), {ltp a b} + {gtp a b} + {eqp a b}.
Proof.
  intros.
  destruct a as [a Pa].
  destruct b as [b Pb].
  unfold eqp, ltp, gtp. simpl.
  apply Z_dec.
Qed.

Theorem ltpeqptrans1 : forall {PZ : Z -> Prop} (a b c : { x : Z | PZ x}), ltp a b -> eqp a c -> ltp c b.
Proof.
  intros.
  unfold ltp in *. unfold eqp in *. lia. 
Qed.

Theorem ltpeqptrans2 : forall {PZ : Z -> Prop} (a b c : { x : Z | PZ x}), ltp a b -> eqp b c -> ltp a c.
Proof.
  intros.
  unfold ltp in *. unfold eqp in *. lia. 
Qed.


Inductive MergingStrategy a (P : a -> Prop) :=
  | SimpleStrategy : (SymBool -> { x : a | P x } -> { x : a | P x } -> {x : a | P x}) -> MergingStrategy a P
  | SortedStrategy : forall (PZ : Z -> Prop) (P' : a -> Prop)
     (ind: { x : a | P x } -> { x : Z | PZ x})
     (sub: { x : Z | PZ x} -> MergingStrategy a P'),
     (forall x, P x -> P' x) ->
     (forall v1 v2, eqp v1 v2 -> eqp (ind v1) (ind v2)) ->
     (forall i1 i2, eqp i1 i2 -> sub i1 = sub i2) ->
      MergingStrategy a P.

Arguments SimpleStrategy {a P} _.
Arguments SortedStrategy {a P PZ P'} _ _ _ _ _.

Inductive ProperStrategy a (P : a -> Prop) : MergingStrategy a P -> Prop :=
  | SimpleProper : forall (s : SymBool -> { x : a | P x } -> { x : a | P x } -> {x : a | P x}),
    ProperStrategy a P (SimpleStrategy s)
  | SortedProper : forall (PZ : Z -> Prop) (P' : a -> Prop)
    (ind : { x : a | P x } -> { x : Z | PZ x})
    (sub : { x : Z | PZ x} -> MergingStrategy a P')
    (ev : forall x, P x -> P' x)
    (ev2 : forall (x : {x : a | P x}), ProperStrategy a P' (sub (ind x)))
    (evind : forall v1 v2, eqp v1 v2 -> eqp (ind v1) (ind v2))
    (evsub : forall i1 i2, eqp i1 i2 -> sub i1 = sub i2),
    ProperStrategy a P (SortedStrategy ind sub ev evind evsub).

Arguments SimpleProper {a P} _.
Arguments SortedProper {a P PZ P' ind sub ev ev2 evind evsub}.

Inductive HM {a} {P : a -> Prop} : MergingStrategy a P -> Union a -> Prop :=
  | HMSingle : forall x (m : (SymBool -> { x : a | P x } -> { x : a | P x } -> {x : a | P x})),
    P x ->
    HM (SimpleStrategy m) (Single x)
  | HMSortedS : forall (PZ : Z -> Prop) (P' : a -> Prop)
    (ind : { x : a | P x } -> { x : Z | PZ x})
    (sub : { x : Z | PZ x} -> MergingStrategy a P')
    (ev : forall x, P x -> P' x)
    (evind : forall v1 v2, eqp v1 v2 -> eqp (ind v1) (ind v2))
    (evsub : forall i1 i2, eqp i1 i2 -> sub i1 = sub i2)
    (x : a),
    P x ->
    HM (SortedStrategy ind sub ev evind evsub) (Single x)
  | HMSortedIDeg : forall (PZ : Z -> Prop) (P' : a -> Prop)
    (ind : { x : a | P x } -> { x : Z | PZ x})
    (sub : { x : Z | PZ x} -> MergingStrategy a P')
    (ev : forall x, P x -> P' x)
    (evind : forall v1 v2, eqp v1 v2 -> eqp (ind v1) (ind v2))
    (evsub : forall i1 i2, eqp i1 i2 -> sub i1 = sub i2)
    u
    {c}
    {t : Union a}
    {f : Union a}
    {l}
    (evl : LeftMost l u)
    (evucons : u = If c t f)
    (evu : forall v, InUnion v u -> P v),
    (forall v1 v2 (ev1u : InUnion v1 u) (ev2u : InUnion v2 u), eqp (ind (exist P v1 (evu v1 ev1u))) (ind (exist P v2 (evu v2 ev2u)))) ->
    HM (sub (ind (exist P l (evu l (LeftMostIsInUnion evl))))) u ->
    HM (SortedStrategy ind sub ev evind evsub) u
  | HMSortedI : forall (PZ : Z -> Prop) (P' : a -> Prop)
    (ind : { x : a | P x } -> { x : Z | PZ x})
    (sub : { x : Z | PZ x} -> MergingStrategy a P')
    (ev : forall x, P x -> P' x)
    (evind : forall v1 v2, eqp v1 v2 -> eqp (ind v1) (ind v2))
    (evsub : forall i1 i2, eqp i1 i2 -> sub i1 = sub i2)
    c
    (t : Union a)
    (f : Union a)
    (evt : forall v, InUnion v t -> P v)
    (evf : forall v, InUnion v f -> P v),
    (forall v1 v2 e1 e2, InUnion v1 t -> InUnion v2 t -> eqp (ind (exist P v1 e1)) (ind (exist P v2 e2))) ->
    (forall v1 v2 e1 e2, InUnion v1 t -> InUnion v2 f -> ltp (ind (exist P v1 e1)) (ind (exist P v2 e2))) ->
    (forall v (e : LeftMost v t), HM (sub (ind (exist P v (evt v (LeftMostIsInUnion e))))) t) ->
    HM (SortedStrategy ind sub ev evind evsub) f ->
    HM (SortedStrategy ind sub ev evind evsub) (If c t f).

Arguments HMSingle {a P} _ _ _.
Arguments HMSortedS {a P PZ P' ind sub ev evind evsub} _ _.
Arguments HMSortedI {a P PZ P' ind sub ev evind evsub} _ _.

Hint Constructors HM.

Lemma HMInUnionP : forall {a} {P : a -> Prop} {m : MergingStrategy a P} {u}, HM m u -> forall {v}, InUnion v u -> P v.
Proof.
  intros a P m u H v H1.
  inversion H; inversion H1; subst; eauto; try congruence. 
  all: inversion H9; subst; eauto.
Qed.

Lemma HMLeftMostP : forall {a} {P : a -> Prop} {m : MergingStrategy a P} {u}, HM m u -> forall {v}, LeftMost v u -> P v.
Proof.
  intros.
  apply HMInUnionP with (v := v) in H; auto. apply LeftMostIsInUnion in H0; auto.
Qed.

Lemma HMX : forall {a} {P : a -> Prop} {PZ} {P' : a -> Prop} {m : MergingStrategy a P} {u}
  (ind : { x : a | P x } -> { x : Z | PZ x})
  (sub : { x : Z | PZ x} -> MergingStrategy a P')
  (ev : forall x, P x -> P' x)
  (evind : forall v1 v2, eqp v1 v2 -> eqp (ind v1) (ind v2))
  (evsub : forall i1 i2, eqp i1 i2 -> sub i1 = sub i2)
  (evm: m = SortedStrategy ind sub ev evind evsub),
  HM m u ->
  (forall (v1 v2 : a) (e1 : P v1) (e2 : P v2), InUnion v1 u -> InUnion v2 u -> eqp (ind (exist P v1 e1)) (ind (exist P v2 e2))) ->
  forall v H,
  InUnion v u ->
  HM (sub (ind (exist P v H))) u.
Proof.
  intros.
  inversion H; subst; try congruence. 
  - destruct (sub (ind (exist P v H1))); eauto.
  - inversion H5. subst. 

Inductive EvalTerms a :=
  | EvalValue : Union a -> EvalTerms a
  | MrgIf : forall {P} (ms : MergingStrategy a P) (c : SymBool) (t f: Union a), EvalTerms a
  | SSMrgIf : forall {P} (ms : MergingStrategy a P) (c : SymBool) (t f: Union a), EvalTerms a
  | ISMrgIf : forall {P} (ms : MergingStrategy a P) (c : SymBool) (t f: Union a), EvalTerms a
  | SIMrgIf : forall {P} (ms : MergingStrategy a P) (c : SymBool) (t f: Union a), EvalTerms a
  | IIMrgIf : forall {P} (ms : MergingStrategy a P) (c : SymBool) (t f: Union a), EvalTerms a.

Hint Constructors EvalTerms.

Arguments EvalValue {a} _.
Arguments MrgIf {a P} _ _ _ _.
Arguments SSMrgIf {a P} _ _ _ _.
Arguments ISMrgIf {a P} _ _ _ _.
Arguments SIMrgIf {a P} _ _ _ _.
Arguments IIMrgIf {a P} _ _ _ _.

Inductive EvalTermsGood {a P} : MergingStrategy a P -> EvalTerms a -> Prop :=
  | EvalValueGood : forall {ms u}, HM ms u -> EvalTermsGood ms (EvalValue u)
  | MrgIfGood : forall {ms c t f},
    HM ms t -> 
    HM ms f -> 
    EvalTermsGood ms (MrgIf ms c t f)
  | SortedSSGood : forall {ms c t f PZ P' ind} {sub : { x : Z | PZ x} -> MergingStrategy a P'} {ev evind evsub}
    (ems : ms = SortedStrategy ind sub ev evind evsub)
    (et : HM ms t) 
    (ef : HM ms f),
    ~ IsConc c ->
    (forall v1 v2 e1 e2, InUnion v1 t -> InUnion v2 t -> eqp (ind (exist P v1 e1)) (ind (exist P v2 e2))) ->
    (forall v1 v2 e1 e2, InUnion v1 f -> InUnion v2 f -> eqp (ind (exist P v1 e1)) (ind (exist P v2 e2))) ->
    EvalTermsGood ms (SSMrgIf ms c t f).

Hint Constructors EvalTermsGood.

Inductive EvalRule {a} : EvalTerms a -> EvalTerms a -> Prop :=
  | MrgIfTrue : forall {P} (ms : MergingStrategy a P) t f (evt : HM ms t) (evf : HM ms f),
    EvalRule (MrgIf ms (ConSymBool true) t f) (EvalValue t)
  | MrgIfFalse : forall {P} (ms : MergingStrategy a P) t f (evt : HM ms t) (evf : HM ms f),
    EvalRule (MrgIf ms (ConSymBool false) t f) (EvalValue f)
  | MrgIfSimple : forall {P} (ms : MergingStrategy a P) m (ems : ms = SimpleStrategy m)
    c t1 f1 (evt : HM ms (Single t1)) (evf : HM ms (Single f1)) (pt : P t1) (pf : P f1),
    ~ IsConc c ->
    EvalRule (MrgIf ms c (Single t1) (Single f1)) (EvalValue (Single (proj1_sig (m c (exist P t1 pt) (exist P f1 pf)))))
  | MrgIfSortedSS : forall {P} (ms : MergingStrategy a P) {PZ P'}
    {ind}
    {sub : { x : Z | PZ x} -> MergingStrategy a P'}
    {ev evind evsub}
    (ems : ms = SortedStrategy ind sub ev evind evsub)
    c t1 f1 (evt : HM ms (Single t1)) (evf : HM ms (Single f1)) (pt : P t1) (pf : P f1)
    (evc : ~ IsConc c),
    EvalRule (MrgIf ms c (Single t1) (Single f1)) (SSMrgIf ms c (Single t1) (Single f1))
  | SSLt : forall {P} (ms : MergingStrategy a P) {PZ P'}
    {ind}
    {sub : { x : Z | PZ x} -> MergingStrategy a P'}
    {ev evind evsub}
    (ems : ms = SortedStrategy ind sub ev evind evsub)
    c t f tl fl (etl : LeftMost tl t) (efl : LeftMost fl f) (evt : HM ms t) (evf : HM ms f)
    (evc : ~ IsConc c),
    ltp (ind (exist P tl (HMLeftMostP evt etl))) (ind (exist P fl (HMLeftMostP evf efl))) ->
    EvalRule (SSMrgIf ms c t f) (EvalValue (If c t f)).

Arguments clos_trans {A} _ _ _.

Notation "t1 '==>' t2" := (EvalRule t1 t2) (at level 75).
Notation "t1 '==>*' t2" := (clos_trans EvalRule t1 t2) (at level 75).

Hint Constructors EvalRule.

Ltac invc H := inversion H; subst; clear H.

Lemma proj1_sig_preserves_pred : forall a (P : a -> Prop) (v : {a | P a}), P (proj1_sig v).
Proof.
  intros.
  destruct v.
  eauto.
Qed.

Theorem progress : forall a P (ms : MergingStrategy a P) t, EvalTermsGood ms t ->
  (exists u, t = (EvalValue u)) \/ (exists t', t ==> t' /\ EvalTermsGood ms t').
Proof.
  intros.
  destruct H.
  1: left. exists u. auto.
  all: right; specialize (IsConcDec c) as [Hc|Hc].
  3: destruct c; invc Hc; try congruence; simpl in H; destruct H; auto.
  1: destruct c; invc Hc; destruct b; eexists; eauto.
  - destruct ms.
    + invc H. invc H0. eexists. split.
      eapply MrgIfSimple; eauto. constructor. constructor.
      eapply proj1_sig_preserves_pred.
    + destruct t; destruct f.
      * eexists. split.
        eapply MrgIfSortedSS; invc H; invc H0; eauto.
        apply (SortedSSGood eq_refl); auto; intros v1 v2 e1 e2 H1 H2;
        inversion H1; inversion H2; subst; apply e.
      * admit.
      * admit.
      * admit.
  - 
    specialize (LeftMostExistence t) as Ht.
    specialize (LeftMostExistence f) as Hf.
    destruct Ht as [tl Htl].
    destruct Hf as [fl Hfl].
    remember (HMLeftMostP et Htl) as Hpt.
    remember (HMLeftMostP ef Hfl) as Hpf.
    specialize (eqpltpgtp_dec (ind (exist P tl Hpt)) (ind (exist P fl Hpf))).
    intros HCmp.
    destruct HCmp as [[HCmp|HCmp]|HCmp].
    + eexists. split.
      eapply SSLt; eauto.
      * rewrite HeqHpt in HCmp. rewrite HeqHpf in HCmp. eauto.
      * constructor. rewrite ems. eapply HMSortedI; eauto.
        -- inversion ef; intros; subst; eauto.
          ++ invc H5. auto.
          ++ invc H5. auto.
          ++ invc H8; auto.
        -- intros.
           specialize (H0 tl v1 Hpt e1 (LeftMostIsInUnion Htl) H2).
           specialize (H1 fl v2 Hpf e2 (LeftMostIsInUnion Hfl) H3).
           eapply ltpeqptrans1. eapply ltpeqptrans2. apply HCmp. apply H1. apply H0.
        -- intros. induction et; try congruence.
          ++ invc H4. inversion e. subst. invc H3.
           


  induction t. intros.
  - left; exists u; auto. 
  - right; specialize (IsConcDec c) as [Hc|Hc].
     destruct c; try inversion Hc;
     destruct b; eexists; inversion H; split; eauto.
  -   
    -

    1: destruct c; try congruence.
  
  - destruct c; try inversion H. destruct b; eexists; eauto.
  - induction ms.
    + inversion evt. inversion evf. subst. eexists; eauto. 
    + generalize dependent f. induction t; intros; induction f.
      * eexists. split.
        -- eapply MrgIfSortedSS; eauto. inversion evt; subst; eauto. inversion evf; subst; eauto.
        -- inversion evt; subst; try congruence. inversion evf; subst; try congruence.
           



  intros.
  induction t.
  1: right; exists u; auto.
  all: left;
    specialize (IsConcDec c);
    intros.
  all: destruct H as [i|i]; try congruence.
    + destruct c; simpl in i; try destruct i; try eauto.
      destruct b; eauto.
    + destruct ms.
      * destruct t; destruct f. 2-4: eexists; inversion h0; inversion h.
        eauto.
      * destruct t; destruct f.
        -- eexists. eapply MrgIfSortedSS; inversion h; inversion h0; eauto.
        -- admit.
        -- admit.
        -- admit.
    + specialize (LeftMostExistence t) as Ht.
      specialize (LeftMostExistence f) as Hf.
      intros.
      eexists.
      destruct Ht as [tl Htl].
      destruct Hf as [fl Hfl].
      specialize (HMLeftMostP h Htl) as Hpt.
      specialize (HMLeftMostP h0 Hfl) as Hpf.
      specialize (eqpltpgtp_dec (ind (exist P tl Hpt)) (ind (exist P fl Hpf))).
      intros.
      destruct H as [[H|H]|H].
      * eapply SSLt; eauto.
        rewrite (evind _ _ (HMLeftMostP h Htl)) in H.
        rewrite (evind _ _ (HMLeftMostP h0 Hfl)) in H.
        apply H.
      * admit. 
      * 

