Require Import String.
Require Import Bool.
Require Import Relations.Relation_Definitions.
Require Import Classes.RelationClasses.

Class SymBoolOp A (SymBoolEquiv : relation A) `{Equivalence _ SymBoolEquiv}: Type := SymBoolOpBuilder {
  conb : bool -> A;
  symb : string -> A;
  extract_con : A -> option bool;
  negsb : A -> A;
  orsb : A -> A -> A;
  andsb : A -> A -> A;
  itesb : A -> A -> A -> A;

  pnegsb : A -> A;
  porsb : A -> A -> A;
  pandsb : A -> A -> A;
  pitesb : A -> A -> A -> A;

  extract_con_spec : forall b, extract_con (conb b) = Some b;

  itesb_spec : forall a b c, SymBoolEquiv (itesb c a b) (orsb (andsb c a) (andsb (negsb c) b));
  pnegsb_correct : forall a, SymBoolEquiv (pnegsb a) (negsb a);
  pandsb_correct : forall a b, SymBoolEquiv (pandsb a b) (andsb a b);
  porsb_correct : forall a b, SymBoolEquiv (porsb a b) (orsb a b);
  pitesb_correct : forall a b c, SymBoolEquiv (pitesb c a b) (itesb c a b);

  pnegsb_con : forall sb b, extract_con sb = Some b -> extract_con (pnegsb sb) = Some (negb b);

  porsb_true_left : forall sb sb1, extract_con sb = Some true -> extract_con (porsb sb sb1) = Some true;
  porsb_true_right : forall sb sb1, extract_con sb = Some true -> extract_con (porsb sb1 sb) = Some true;
  porsb_false_left : forall sb sb1, extract_con sb = Some false -> porsb sb sb1 = sb1;
  porsb_false_right : forall sb sb1, extract_con sb = Some false -> porsb sb1 sb = sb1;
  porsb_con : forall sb sb1 b b1,
    extract_con sb = Some b ->
    extract_con sb1 = Some b1 ->
    extract_con (porsb sb sb1) = Some (b || b1);

  pandsb_false_left : forall sb sb1, extract_con sb = Some false -> extract_con (pandsb sb sb1) = Some false;
  pandsb_false_right : forall sb sb1, extract_con sb = Some false -> extract_con (pandsb sb1 sb) = Some false;
  pandsb_true_left : forall sb sb1, extract_con sb = Some true -> pandsb sb sb1 = sb1;
  pandsb_true_right : forall sb sb1, extract_con sb = Some true -> pandsb sb1 sb = sb1;
  pandsb_con : forall sb sb1 b b1,
    extract_con sb = Some b ->
    extract_con sb1 = Some b1 ->
    extract_con (pandsb sb sb1) = Some (b && b1);

  pitesb_true_cond : forall sc t f, extract_con sc = Some true -> pitesb sc t f = t;
  pitesb_false_cond : forall sc t f, extract_con sc = Some false -> pitesb sc t f = f;

  pitesb_true_false : forall sc t f, extract_con t = Some true -> extract_con f = Some false -> pitesb sc t f = sc;
  pitesb_true_true : forall sc t f, extract_con t = Some true ->
    extract_con f = Some true -> extract_con (pitesb sc t f) = Some true;
  pitesb_false_false : forall sc t f, extract_con t = Some false ->
    extract_con f = Some false -> extract_con (pitesb sc t f) = Some false;
}.

Declare Scope sbool_scope.
Delimit Scope sbool_scope with sbool_scope.
Bind Scope sbool_scope with SymBoolOp.
Notation "'!~' x" := (pnegsb x) (at level 30): sbool_scope.
Infix "&&~" := pandsb (at level 40, left associativity): sbool_scope.
Infix "||~" := porsb (at level 50, left associativity): sbool_scope.
Notation "'pite' c a b" := (pitesb c a b) (at level 70): sbool_scope.


Inductive SymBool :=
  | SymSymBool : string -> SymBool
  | ConSymBool : bool -> SymBool
  | NotSymBool : SymBool -> SymBool
  | AndSymBool : SymBool -> SymBool -> SymBool
  | OrSymBool : SymBool -> SymBool -> SymBool
  | ItebSymBool : SymBool -> SymBool -> SymBool -> SymBool.

Definition extract_con_SymBool (v: SymBool): option bool := match v with
  | ConSymBool v => Some v
  | _ => None
end.

Definition partial_eval_not (v: SymBool): SymBool := match v with
  | ConSymBool v => ConSymBool (negb v)
  | _ => NotSymBool v
end.

Definition partial_eval_and (a b: SymBool): SymBool := match a, b with
  | ConSymBool true, _ => b
  | ConSymBool false, _ => a
  | _, ConSymBool true => a
  | _, ConSymBool false => b
  | _, _ => AndSymBool a b
end.

Definition partial_eval_or (a b: SymBool): SymBool := match a, b with
  | ConSymBool true, _ => a
  | ConSymBool false, _ => b
  | _, ConSymBool true => b
  | _, ConSymBool false => a
  | _, _ => OrSymBool a b
end.

Definition partial_eval_ite (c a b: SymBool): SymBool := match c, a, b with
  | ConSymBool true, _, _ => a
  | ConSymBool false, _, _ => b
  | _, ConSymBool true, ConSymBool true => a
  | _, ConSymBool false, ConSymBool false => a
  | _, ConSymBool true, ConSymBool false => c
  | _, _, _ => ItebSymBool c a b
end.

Inductive SymBoolEquiv : relation SymBool :=
  | OrComm : forall a b, SymBoolEquiv (OrSymBool a b) (OrSymBool b a)
  | AndComm : forall a b, SymBoolEquiv (AndSymBool a b) (AndSymBool b a)
  | OrAssoc : forall a b c, SymBoolEquiv (OrSymBool a (OrSymBool b c)) (OrSymBool (OrSymBool a b) c)
  | AndAssoc : forall a b c, SymBoolEquiv (AndSymBool a (AndSymBool b c)) (AndSymBool (AndSymBool a b) c)
  | OrDistributive : forall a b c, SymBoolEquiv (AndSymBool a (OrSymBool b c)) (OrSymBool (AndSymBool a b) (AndSymBool a c))
  | AndDistributive : forall a b c, SymBoolEquiv (OrSymBool a (AndSymBool b c)) (AndSymBool (OrSymBool a b) (OrSymBool a c))
  | OrIdent : forall a, SymBoolEquiv (OrSymBool (ConSymBool false) a) a
  | AndIdent : forall a, SymBoolEquiv (AndSymBool (ConSymBool true) a) a
  | OrComplement : forall a, SymBoolEquiv (OrSymBool (NotSymBool a) a) (ConSymBool true)
  | AndComplement : forall a, SymBoolEquiv (AndSymBool (NotSymBool a) a) (ConSymBool false)

  | NotCon : forall b, SymBoolEquiv (NotSymBool (ConSymBool b)) (ConSymBool (negb b))

  | IteSemantics : forall c a b,
      SymBoolEquiv (ItebSymBool c a b) (OrSymBool (AndSymBool c a) (AndSymBool (NotSymBool c) b))

  | SymBoolEquivReflexive : forall a, SymBoolEquiv a a
  | SymBoolEquivSymmetric : forall a b, SymBoolEquiv a b -> SymBoolEquiv b a
  | SymBoolEquivTransitive : forall a b c, SymBoolEquiv a b -> SymBoolEquiv b c -> SymBoolEquiv a c
  | SymBoolEquivSubstNot : forall a b c, SymBoolEquiv (NotSymBool a) b ->
      SymBoolEquiv a c -> SymBoolEquiv (NotSymBool c) b
  | SymBoolEquivSubstAndL : forall a b c d, SymBoolEquiv (AndSymBool a b) c ->
      SymBoolEquiv a d -> SymBoolEquiv (AndSymBool d b) c
  | SymBoolEquivSubstAndR : forall a b c d, SymBoolEquiv (AndSymBool a b) c ->
      SymBoolEquiv b d -> SymBoolEquiv (AndSymBool a d) c
  | SymBoolEquivSubstOrL : forall a b c d, SymBoolEquiv (OrSymBool a b) c ->
      SymBoolEquiv a d -> SymBoolEquiv (OrSymBool d b) c
  | SymBoolEquivSubstOrR : forall a b c d, SymBoolEquiv (OrSymBool a b) c ->
      SymBoolEquiv b d -> SymBoolEquiv (OrSymBool a d) c.

Theorem AndIdempotent : forall a, SymBoolEquiv (AndSymBool a a) a.
Proof.
  intros.
  eapply SymBoolEquivTransitive.
  apply SymBoolEquivSymmetric.
  apply OrIdent.

  assert (SymBoolEquiv (ConSymBool false) (AndSymBool a (NotSymBool a))).
  eauto using SymBoolEquiv.
  eapply SymBoolEquivSubstOrL.
  2: apply SymBoolEquivSymmetric; apply H.

  apply SymBoolEquivTransitive with (b:=AndSymBool a (OrSymBool a (NotSymBool a))).
  eauto using SymBoolEquiv.
  eauto using SymBoolEquiv.
Qed.

Theorem OrIdempotent : forall a, SymBoolEquiv (OrSymBool a a) a.
Proof.
  intros.
  eapply SymBoolEquivTransitive.
  apply SymBoolEquivSymmetric.
  apply AndIdent.

  assert (SymBoolEquiv (ConSymBool true) (OrSymBool a (NotSymBool a))).
  eauto using SymBoolEquiv.
  eapply SymBoolEquivSubstAndL.
  2: apply SymBoolEquivSymmetric; apply H.

  apply SymBoolEquivTransitive with (b:=OrSymBool a (AndSymBool a (NotSymBool a))).
  eauto using SymBoolEquiv.
  eauto using SymBoolEquiv.
Qed.

Global Hint Resolve AndIdempotent OrIdempotent : sboolequiv.

Theorem AndNull : forall a, SymBoolEquiv (AndSymBool (ConSymBool false) a) (ConSymBool false).
Proof.
  intros.
  apply SymBoolEquivTransitive with (b:=AndSymBool (AndSymBool (NotSymBool a) a) a).
  eauto using SymBoolEquiv with sboolequiv.
  eauto using SymBoolEquiv with sboolequiv.
Qed.

Theorem OrNull : forall a, SymBoolEquiv (OrSymBool (ConSymBool true) a) (ConSymBool true).
Proof.
  intros.
  apply SymBoolEquivTransitive with (b:=OrSymBool (OrSymBool (NotSymBool a) a) a).
  eauto using SymBoolEquiv with sboolequiv.
  eauto using SymBoolEquiv with sboolequiv.
Qed.

Global Hint Resolve AndNull OrNull : sboolequiv.

Theorem IfTrue : forall t f, SymBoolEquiv (ItebSymBool (ConSymBool true) t f) t.
Proof.
  intros.
  eapply SymBoolEquivTransitive.
  apply IteSemantics.

  apply SymBoolEquivTransitive with
    (b:=(OrSymBool (AndSymBool (ConSymBool true) t) (AndSymBool (ConSymBool false) f))).
  eauto 4 using SymBoolEquiv with sboolequiv.
  apply SymBoolEquivTransitive with
    (b:=(OrSymBool t (ConSymBool false))).
  eauto 4 using SymBoolEquiv with sboolequiv.
  eauto 3 using SymBoolEquiv with sboolequiv.
Qed.

Theorem IfFalse : forall t f, SymBoolEquiv (ItebSymBool (ConSymBool false) t f) f.
Proof.
  intros.
  eapply SymBoolEquivTransitive.
  apply IteSemantics.
  apply SymBoolEquivTransitive with
    (b:=(OrSymBool (AndSymBool (ConSymBool false) t) (AndSymBool (ConSymBool true) f))).
  eauto 4 using SymBoolEquiv with sboolequiv.
  apply SymBoolEquivTransitive with
    (b:=(OrSymBool (ConSymBool false) (AndSymBool (ConSymBool true) f))).
  eauto 3 using SymBoolEquiv with sboolequiv.
  eauto 3 using SymBoolEquiv with sboolequiv.
Qed.

Theorem IfValueAllTrue : forall c,
  SymBoolEquiv (ItebSymBool c (ConSymBool true) (ConSymBool true)) (ConSymBool true).
Proof.
  intros.
  eapply SymBoolEquivTransitive.
  apply IteSemantics.

  apply SymBoolEquivTransitive with
    (b:=(OrSymBool (AndSymBool (ConSymBool true) c) (AndSymBool (ConSymBool true) (NotSymBool c)))).
  eauto 4 using SymBoolEquiv with sboolequiv.
  apply SymBoolEquivTransitive with
    (b:=(OrSymBool c (NotSymBool c))).
  eauto 4 using SymBoolEquiv with sboolequiv.
  eauto 3 using SymBoolEquiv with sboolequiv.
Qed.

Theorem IfValueAllFalse : forall c,
  SymBoolEquiv (ItebSymBool c (ConSymBool false) (ConSymBool false)) (ConSymBool false).
Proof.
  intros.
  eapply SymBoolEquivTransitive.
  apply IteSemantics.

  apply SymBoolEquivTransitive with
    (b:=(OrSymBool (AndSymBool (ConSymBool false) c) (AndSymBool (ConSymBool false) (NotSymBool c)))).
  eauto 4 using SymBoolEquiv with sboolequiv.
  eauto 4 using SymBoolEquiv with sboolequiv.
Qed.

Theorem IfValueTrueFalse : forall c,
  SymBoolEquiv (ItebSymBool c (ConSymBool true) (ConSymBool false)) c.
Proof.
  intros.
  eapply SymBoolEquivTransitive.
  apply IteSemantics.

  apply SymBoolEquivTransitive with
    (b:=(OrSymBool (AndSymBool (ConSymBool true) c) (AndSymBool (ConSymBool false) (NotSymBool c)))).
  eauto 4 using SymBoolEquiv with sboolequiv.
  apply SymBoolEquivTransitive with
    (b:=(OrSymBool c (ConSymBool false))).
  eauto 4 using SymBoolEquiv with sboolequiv.
  eauto 3 using SymBoolEquiv with sboolequiv.
Qed.

Theorem IfValueFalseTrue : forall c,
  SymBoolEquiv (ItebSymBool c (ConSymBool false) (ConSymBool true)) (NotSymBool c).
Proof.
  intros.
  eapply SymBoolEquivTransitive.
  apply IteSemantics.

  apply SymBoolEquivTransitive with
    (b:=(OrSymBool (AndSymBool (ConSymBool false) c) (AndSymBool (ConSymBool true) (NotSymBool c)))).
  eauto 4 using SymBoolEquiv with sboolequiv.
  apply SymBoolEquivTransitive with
    (b:=(OrSymBool (ConSymBool false) (NotSymBool c))).
  eauto 4 using SymBoolEquiv with sboolequiv.
  eauto 3 using SymBoolEquiv with sboolequiv.
Qed.

Global Hint Resolve IfTrue IfFalse IfValueAllTrue IfValueTrueFalse IfValueAllFalse IfValueFalseTrue: sboolequiv.

Global Instance SymBoolEquivIsEquivalence: Equivalence SymBoolEquiv.
Proof.
  constructor;
  eauto using SymBoolEquiv.
Qed.
Print auto.


Global Instance SymBoolOpForSymBool: SymBoolOp SymBool SymBoolEquiv.
Proof.
Ltac destruct_symbool a := destruct a; try (match goal with
| H: extract_con_SymBool (SymSymBool _) = Some _ |- _ => inversion H
| H: extract_con_SymBool (ConSymBool _) = Some _ |- _ => inversion H; clear H
| H: extract_con_SymBool (NotSymBool _) = Some _ |- _ => inversion H
| H: extract_con_SymBool (AndSymBool _ _) = Some _ |- _ => inversion H
| H: extract_con_SymBool (OrSymBool _ _) = Some _ |- _ => inversion H
| H: extract_con_SymBool (ItebSymBool _ _ _) = Some _ |- _ => inversion H
end); simpl; eauto 2 using SymBoolEquiv with sboolequiv.
Ltac destruct_bool a := destruct a; simpl; eauto 2 using SymBoolEquiv with sboolequiv.
Ltac destruct_bool_strong a := destruct a; simpl; eauto 3 using SymBoolEquiv with sboolequiv.
Ltac auto_destruct_bool_with tac := match goal with
| |- extract_con_SymBool (if ?b then _ else _) = Some _ => tac b
| |- (if ?b then _ else _) = _ => tac b
| |- SymBoolEquiv (if ?b then _ else _) _ => tac b
end.
Ltac auto_destruct_bool := auto_destruct_bool_with destruct_bool.
Ltac auto_destruct_bool_strong := auto_destruct_bool_with destruct_bool_strong.
  refine (SymBoolOpBuilder SymBool SymBoolEquiv _
    ConSymBool SymSymBool extract_con_SymBool
    NotSymBool OrSymBool AndSymBool ItebSymBool
    partial_eval_not partial_eval_or partial_eval_and partial_eval_ite
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
  all: intros; eauto 2 using SymBoolEquiv with sboolequiv.

  destruct_symbool a.
  1,2: destruct_symbool a; destruct_symbool b; repeat auto_destruct_bool_strong.
  destruct_symbool a; destruct_symbool b; destruct_symbool c; repeat auto_destruct_bool.
  1,2: destruct_symbool sb.
  1-9: destruct_symbool sb; destruct_symbool sb1 ; repeat auto_destruct_bool.
  1-2: destruct_symbool sc.
  all: destruct_symbool t; destruct_symbool f; destruct_symbool sc; repeat auto_destruct_bool.
Qed.

(*
Inductive IsConc : SymBool -> Prop :=
  IsConcCon : forall b, IsConc (ConSymBool b).

Hint Constructors IsConc.

Inductive NotIsConc : SymBool -> Prop :=
  | NotIsConcSym : forall b, NotIsConc (SymSymBool b)
  | NotIsConcNot : forall b, NotIsConc (NotSymBool b)
  | NotIsConcAnd : forall b1 b2, NotIsConc (AndSymBool b1 b2)
  | NotIsConcOr : forall b1 b2, NotIsConc (OrSymBool b1 b2)
  | NotIsConcIteb : forall b1 b2 b3, NotIsConc (ItebSymBool b1 b2 b3).

Hint Constructors NotIsConc.

Theorem IsConcDec : forall b, {IsConc b} + {NotIsConc b}.
Proof.
  intros.
  destruct b; eauto.
Qed.
*)

Definition IsConc (b: SymBool) : Prop :=
  match b with
  | ConSymBool _ => True
  | _ => False
  end.

Theorem IsConcDec : forall b, {IsConc b} + {~ IsConc b}.
Proof.
  intros.
  destruct b; eauto.
  left. simpl. auto.
Qed.

Theorem not_eq_con_means_not_isconc : forall c,
  (forall b, ConSymBool b <> c) -> ~ IsConc c.
Proof.
  intros.
  destruct c; simpl; eauto.
  specialize (H b); eauto.
Qed.

Ltac solve_is_conc :=
  match goal with
  | [ H : forall b, ConSymBool b <> ?c |- ~IsConc ?c ] =>
    destruct c as [b| | | | |]; eauto; specialize (H b); congruence
  end.

