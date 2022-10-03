Require Import Grisette.MergingStrategy.
Require Import Grisette.SubStrategy.
Require Import Grisette.Union.
Require Import Grisette.SymBoolOp.
Require Import Grisette.Invariant.
Require Import Grisette.SubStrategyInvariant.
Require Import Grisette.GeneralTactics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.ZArith_dec.
Require Import Lia.
Require Import Program.
Open Scope Z.
Open Scope nat.

Create HintDb eval discriminated.

Inductive EvalTerms T :=
  | EvalValue : forall n (ms : MergingStrategy T n), Union T -> EvalTerms T
  | MrgIf : forall n (ms : MergingStrategy T n) (c : SymBool) (t f: Union T), EvalTerms T
  | SSMrgIf : forall n (ms : MergingStrategy T n) (c : SymBool) (t f: Union T), EvalTerms T
  | ISMrgIf : forall n (ms : MergingStrategy T n) (c : SymBool) (t f: Union T), EvalTerms T
  | SIMrgIf : forall n (ms : MergingStrategy T n) (c : SymBool) (t f: Union T), EvalTerms T
  | IIMrgIf : forall n (ms : MergingStrategy T n) (c : SymBool) (t f: Union T), EvalTerms T.

#[global] Hint Constructors EvalTerms : eval.

Arguments EvalValue {T n}.
Arguments MrgIf {T n}.
Arguments SSMrgIf {T n}.
Arguments ISMrgIf {T n}.
Arguments SIMrgIf {T n}.
Arguments IIMrgIf {T n}.

Inductive EvalTermsGood {T n} : MergingStrategy T n -> EvalTerms T -> Prop :=
  | EvalValueGood : forall {P} {ms : MergingStrategy T n} {u}, HieraricalMergingInv P ms u -> EvalTermsGood ms (EvalValue ms u)
  | MrgIfGood : forall {P} {ms : MergingStrategy T n} {c t f},
    HieraricalMergingInv P ms t -> 
    HieraricalMergingInv P ms f -> 
    EvalTermsGood ms (MrgIf ms c t f)
  | SortedSSGood : forall {P c t f ind sub}
    (et : HieraricalMergingInv P (SortedStrategy n ind sub) t) 
    (ef : HieraricalMergingInv P (SortedStrategy n ind sub) f),
    ~ IsConc c ->
    (AllInUnion (fun x => AllInUnion (fun y => ind x = ind y) t) t) ->
    (AllInUnion (fun x => AllInUnion (fun y => ind x = ind y) f) f) ->
    EvalTermsGood (SortedStrategy n ind sub) (SSMrgIf (SortedStrategy n ind sub) c t f)
  | SortedISGood : forall {P c t f ind sub}
    (et : HieraricalMergingInv P (SortedStrategy n ind sub) t) 
    (ef : HieraricalMergingInv P (SortedStrategy n ind sub) f),
    ~ IsConc c ->
    is_if t ->
    (AllInUnion (fun x => AllInUnion (fun y => ind x = ind y) f) f) ->
    EvalTermsGood (SortedStrategy n ind sub) (ISMrgIf (SortedStrategy n ind sub) c t f)
  | SortedSIGood : forall {P c t f ind sub}
    (et : HieraricalMergingInv P (SortedStrategy n ind sub) t) 
    (ef : HieraricalMergingInv P (SortedStrategy n ind sub) f),
    ~ IsConc c ->
    (AllInUnion (fun x => AllInUnion (fun y => ind x = ind y) t) t) ->
    is_if f ->
    EvalTermsGood (SortedStrategy n ind sub) (SIMrgIf (SortedStrategy n ind sub) c t f)
  | SortedIIGood : forall {P c t f ind sub}
    (et : HieraricalMergingInv P (SortedStrategy n ind sub) t) 
    (ef : HieraricalMergingInv P (SortedStrategy n ind sub) f),
    ~ IsConc c ->
    is_if t ->
    is_if f ->
    EvalTermsGood (SortedStrategy n ind sub) (IIMrgIf (SortedStrategy n ind sub) c t f).

#[global] Hint Constructors EvalTermsGood : eval.

Lemma ss_good_implies_if_good : forall {T n} {ind sub} {c} {t f : Union T},
  EvalTermsGood (SortedStrategy n ind sub) (SSMrgIf (SortedStrategy n ind sub) c t f) ->
  EvalTermsGood (SortedStrategy n ind sub) (MrgIf (SortedStrategy n ind sub) c t f). 
Proof.
  intros.
  invcd H.
  econstructor; eauto.
Qed.

#[global] Hint Resolve ss_good_implies_if_good : eval.

Lemma si_same_f_good_implies_ss_good : forall {T n} {ind sub} {c} {t f : Union T},
  EvalTermsGood (SortedStrategy n ind sub) (SIMrgIf (SortedStrategy n ind sub) c t f) ->
  AllInUnion (fun x => AllInUnion (fun y => ind x = ind y) f) f ->
  EvalTermsGood (SortedStrategy n ind sub) (SSMrgIf (SortedStrategy n ind sub) c t f). 
Proof.
  intros.
  invcd H.
  econstructor; eauto.
Qed.

#[global] Hint Resolve si_same_f_good_implies_ss_good : eval.

Lemma is_same_t_good_implies_ss_good : forall {T n} {ind sub} {c} {t f : Union T},
  EvalTermsGood (SortedStrategy n ind sub) (ISMrgIf (SortedStrategy n ind sub) c t f) ->
  AllInUnion (fun x => AllInUnion (fun y => ind x = ind y) t) t ->
  EvalTermsGood (SortedStrategy n ind sub) (SSMrgIf (SortedStrategy n ind sub) c t f). 
Proof.
  intros.
  invcd H.
  econstructor; eauto.
Qed.

#[global] Hint Resolve is_same_t_good_implies_ss_good : eval.

Lemma good_implies_proper_strategy : forall {T n} {ms : MergingStrategy T n} {e},
  EvalTermsGood ms e ->
  exists P, ProperStrategy P ms.
Proof.
  intros.
  invcd H.
  1-2: assert (ProperStrategy P ms) by eauto with inv; eexists; eauto.
  all: assert (ProperStrategy P (SortedStrategy n ind sub)) by eauto with inv; eexists; eauto.
Qed.

#[global] Hint Resolve good_implies_proper_strategy : eval.


Inductive EvalRule {T} : EvalTerms T -> EvalTerms T -> Prop :=
  | MrgIfTrue : forall {n} (ms : MergingStrategy T n) t f,
    EvalRule (MrgIf ms (ConSymBool true) t f) (EvalValue ms t)
  | MrgIfFalse : forall {n} (ms : MergingStrategy T n) t f,
    EvalRule (MrgIf ms (ConSymBool false) t f) (EvalValue ms f)
  | MrgIfSimple : forall m c t f r,
    m c t f = Some r ->
    ~ IsConc c ->
    EvalRule (MrgIf (SimpleStrategy m) c (Single t) (Single f)) (EvalValue (SimpleStrategy m) (Single r))
  | MrgIfSortedSS : forall {n} (s : MergingStrategy T n) c t f r,
    is_sorted_strategy s ->
    ~ IsConc c ->
    is_single t ->
    is_single f ->
    clos_refl_trans_1n _ EvalRule (SSMrgIf s c t f) (EvalValue s r) ->
    EvalRule (MrgIf s c t f) (EvalValue s r)
  | MrgIfSortedSI : forall {n} (s : MergingStrategy T n) c t f r,
    is_sorted_strategy s ->
    ~ IsConc c ->
    is_single t ->
    is_if f ->
    clos_refl_trans_1n _ EvalRule (SIMrgIf s c t f) (EvalValue s r) ->
    EvalRule (MrgIf s c t f) (EvalValue s r)
  | MrgIfSortedIS : forall {n} (s : MergingStrategy T n) c t f r,
    is_sorted_strategy s ->
    ~ IsConc c ->
    is_if t ->
    is_single f ->
    clos_refl_trans_1n _ EvalRule (ISMrgIf s c t f) (EvalValue s r) ->
    EvalRule (MrgIf s c t f) (EvalValue s r)
  | MrgIfSortedII : forall {n} (s : MergingStrategy T n) c t f r,
    is_sorted_strategy s ->
    ~ IsConc c ->
    is_if t ->
    is_if f ->
    clos_refl_trans_1n _ EvalRule (IIMrgIf s c t f) (EvalValue s r) ->
    EvalRule (MrgIf s c t f) (EvalValue s r)
  | SSLt : forall {n} ind sub c t f ti fi,
    AllInUnion (fun x => ind x = Some ti) t ->
    AllInUnion (fun x => ind x = Some fi) f ->
    (ti < fi)%Z ->
    EvalRule (SSMrgIf (SortedStrategy n ind sub) c t f) (EvalValue (SortedStrategy n ind sub) (If c t f))
  | SSEq : forall {n} ind sub c t f i n1 s (ev : n1 < n) r,
    AllInUnion (fun x => ind x = Some i) t ->
    AllInUnion (fun x => ind x = Some i) f ->
    sub i = Some (MSSubLt s ev) ->
    clos_refl_trans_1n _ EvalRule (MrgIf s c t f) (EvalValue s r) ->
    EvalRule (SSMrgIf (SortedStrategy n ind sub) c t f) (EvalValue (SortedStrategy n ind sub) r)
  | SSGt : forall {n} ind sub c t f ti fi,
    AllInUnion (fun x => ind x = Some ti) t ->
    AllInUnion (fun x => ind x = Some fi) f ->
    (ti > fi)%Z ->
    EvalRule (SSMrgIf (SortedStrategy n ind sub) c t f) (EvalValue (SortedStrategy n ind sub) (If (pnegsb c) f t))
  | SIDeg : forall {n} ind sub c t f fi r,
    AllInUnion (fun x => ind x = Some fi) f ->
    clos_refl_trans_1n _ EvalRule (SSMrgIf (SortedStrategy n ind sub) c t f) (EvalValue (SortedStrategy n ind sub) r) ->
    EvalRule (SIMrgIf (SortedStrategy n ind sub) c t f) (EvalValue (SortedStrategy n ind sub) r)
  | SILt : forall {n} ind sub c t fc ft ff ti fti ffi,
    AllInUnion (fun x => ind x = Some ti) t ->
    AllInUnion (fun x => ind x = Some fti) ft ->
    ind (left_most ff) = Some ffi ->
    (fti <> ffi)%Z ->
    (ti < fti)%Z ->
    EvalRule (SIMrgIf (SortedStrategy n ind sub) c t (If fc ft ff))
             (EvalValue (SortedStrategy n ind sub) (If c t (If fc ft ff)))
  | SIEq : forall {n} ind sub c t fc ft ff ti ffi n1 s t' (ev : n1 < n),
    AllInUnion (fun x => ind x = Some ti) t ->
    AllInUnion (fun x => ind x = Some ti) ft ->
    ind (left_most ff) = Some ffi ->
    (ti <> ffi)%Z ->
    sub ti = Some (MSSubLt s ev) ->
    clos_refl_trans_1n _ EvalRule (MrgIf s c t ft) (EvalValue s t') ->
    EvalRule (SIMrgIf (SortedStrategy n ind sub) c t (If fc ft ff))
             (EvalValue (SortedStrategy n ind sub) (If (porsb c fc) t' ff))
  | SIGt : forall {n} ind sub c t fc ft ff ti fti ffi f',
    AllInUnion (fun x => ind x = Some ti) t ->
    AllInUnion (fun x => ind x = Some fti) ft ->
    ind (left_most ff) = Some ffi ->
    (fti <> ffi)%Z ->
    (ti > fti)%Z ->
    clos_refl_trans_1n _ EvalRule (MrgIf (SortedStrategy n ind sub) c t ff) (EvalValue (SortedStrategy n ind sub) f') ->
    EvalRule (SIMrgIf (SortedStrategy n ind sub) c t (If fc ft ff))
             (EvalValue (SortedStrategy n ind sub) (If (pandsb (pnegsb c) fc) ft f')).

#[global] Hint Constructors EvalRule : eval.

Arguments clos_refl_trans_1n {A} _ _ _.
#[global] Hint Constructors clos_refl_trans_1n : eval.

Notation "t1 '==>' t2" := (EvalRule t1 t2) (at level 75).
Notation "t1 '==>*' t2" := (clos_refl_trans_1n EvalRule t1 t2) (at level 75).

Definition metric {T} (t : EvalTerms T) : nat :=
  match t with
  | EvalValue _ _ => 0
  | MrgIf ms c t f => 4 + 4 * (ms_depth ms + union_depth t + union_depth f)
  | SSMrgIf ms c t f => 1 + 4 * (ms_depth ms + union_depth t + union_depth f)
  | ISMrgIf ms c t f => 2 + 4 * (ms_depth ms + union_depth t + union_depth f)
  | SIMrgIf ms c t f => 2 + 4 * (ms_depth ms + union_depth t + union_depth f)
  | IIMrgIf ms c t f => 3 + 4 * (ms_depth ms + union_depth t + union_depth f)
  end.

#[global] Hint Unfold metric : eval.

  (*
Lemma eval_reduce_metric : forall {T n} {t t1 : EvalTerms T} {ms : MergingStrategy T n},
  EvalTermsGood ms t ->
  t ==> t1 ->
  metric t1 < metric t.
Proof.
  intros.
  destruct t.
  - inversion H0.
  - invcd H0; simpl; try lia.
  - invcd H0; simpl; try lia.
    unfold ms_depth. lia.
  - admit.
  - admit.
  - admit.
Admitted.

#[global] Hint Resolve eval_reduce_metric : eval.
*)

Ltac invc_initial_eval_good :=
  match goal with
  | [ H : EvalTermsGood ?m (EvalValue ?m' _) |- _] => invc H; subst; repeat invc_existT
  | [ H : EvalTermsGood ?m (MrgIf ?m' _ ?t ?f) |- _] => invc H; subst; repeat invc_existT
  | [ H : EvalTermsGood ?m (SSMrgIf ?m' _ ?t ?f) |- _] => invc H; subst; repeat invc_existT
  | [ H : EvalTermsGood ?m (SIMrgIf ?m' _ ?t ?f) |- _] => invc H; subst; repeat invc_existT
  | [ H : EvalTermsGood ?m (ISMrgIf ?m' _ ?t ?f) |- _] => invc H; subst; repeat invc_existT
  | [ H : EvalTermsGood ?m (IIMrgIf ?m' _ ?t ?f) |- _] => invc H; subst; repeat invc_existT
  end.

Ltac inversion_initial_eval_good :=
  match goal with
  | [ H : EvalTermsGood ?m (EvalValue ?m' _) |- _] => inversiond H
  | [ H : EvalTermsGood ?m (MrgIf ?m' _ ?t ?f) |- _] => inversiond H
  | [ H : EvalTermsGood ?m (SSMrgIf ?m' _ ?t ?f) |- _] => inversiond H
  | [ H : EvalTermsGood ?m (SIMrgIf ?m' _ ?t ?f) |- _] => inversiond H
  | [ H : EvalTermsGood ?m (ISMrgIf ?m' _ ?t ?f) |- _] => inversiond H
  | [ H : EvalTermsGood ?m (IIMrgIf ?m' _ ?t ?f) |- _] => inversiond H
  end.

Ltac invc_all_hm :=
  match goal with
  | [ H1 : HieraricalMergingInv _ _ _, H2 : HieraricalMergingInv _ _ _ |- _] => invc H1; invc H2
  | [ H : HieraricalMergingInv _ _ _ |- _] => invc H
  end.

Section EvalTerms_ind'.
  Variable T : Type.
  Variable P : EvalTerms T -> Prop.
  Hypothesis EvalValueCase : forall {n : nat} (ms : MergingStrategy T n) (u : Union T),
    EvalTermsGood ms (EvalValue ms u) -> P (EvalValue ms u).
  Hypothesis EvalMrgIfConcCase : forall {n : nat} (ms : MergingStrategy T n) (b : bool) (t f : Union T),
    EvalTermsGood ms (MrgIf ms (ConSymBool b) t f) -> 
    (b = true -> P (EvalValue ms t)) ->
    (b = false -> P (EvalValue ms f)) ->
    P (MrgIf ms (ConSymBool b) t f).
  Hypothesis EvalMrgIfSimpleCase : forall m (c : SymBool) tv fv r,
    ~IsConc c -> m c tv fv = Some r ->
    P (EvalValue (SimpleStrategy m) (Single r)) ->
    EvalTermsGood (SimpleStrategy m) (MrgIf (SimpleStrategy m) c (Single tv) (Single fv)) -> 
    P (MrgIf (SimpleStrategy m) c (Single tv) (Single fv)).
  Hypothesis EvalMrgIfSSCase : forall {n : nat} (ms : MergingStrategy T n) (c : SymBool) tv fv,
    ~IsConc c -> is_sorted_strategy ms ->
    P (SSMrgIf ms c (Single tv) (Single fv)) -> P (MrgIf ms c (Single tv) (Single fv)).
  Hypothesis EvalMrgIfSICase : forall {n : nat} (ms : MergingStrategy T n) (c : SymBool) tv fc ft ff,
    ~IsConc c -> is_sorted_strategy ms ->
    P (SIMrgIf ms c (Single tv) (If fc ft ff)) -> P (MrgIf ms c (Single tv) (If fc ft ff)).
  Hypothesis EvalMrgIfISCase : forall {n : nat} (ms : MergingStrategy T n) (c : SymBool) tc tt tf fv,
    ~IsConc c -> is_sorted_strategy ms ->
    P (ISMrgIf ms c (If tc tt tf) (Single fv)) -> P (MrgIf ms c (If tc tt tf) (Single fv)).
  Hypothesis EvalMrgIfIICase : forall {n : nat} (ms : MergingStrategy T n) (c : SymBool) tc tt tf fc ft ff,
    ~IsConc c -> is_sorted_strategy ms ->
    P (IIMrgIf ms c (If tc tt tf) (If fc ft ff)) -> P (MrgIf ms c (If tc tt tf) (If fc ft ff)).
  Hypothesis EvalSSLtCase : forall {n : nat} ind sub (c : SymBool) (t f : Union T) ti fi,
    ~IsConc c ->
    AllInUnion (fun x => ind x = Some ti) t ->
    AllInUnion (fun x => ind x = Some fi) f ->
    (ti < fi)%Z ->
    P (SSMrgIf (SortedStrategy n ind sub) c t f).
  Hypothesis EvalSSEqCase : forall {n : nat} ind sub (c : SymBool) (t f : Union T) i
    n1 (s : MergingStrategy T n1) (ev : n1 < n),
    ~IsConc c ->
    AllInUnion (fun x => ind x = Some i) t ->
    AllInUnion (fun x => ind x = Some i) f ->
    sub i = Some (MSSubLt s ev) ->
    P (MrgIf s c t f) ->
    P (SSMrgIf (SortedStrategy n ind sub) c t f).
  Hypothesis EvalSSGtCase : forall {n : nat} ind sub (c : SymBool) (t f : Union T) ti fi,
    ~IsConc c ->
    AllInUnion (fun x => ind x = Some ti) t ->
    AllInUnion (fun x => ind x = Some fi) f ->
    (ti > fi)%Z ->
    P (SSMrgIf (SortedStrategy n ind sub) c t f).
  Hypothesis EvalSIDegCase : forall {n : nat} ind sub c t f fi,
    ~IsConc c ->
    AllInUnion (fun x => ind x = Some fi) f ->
    P (SSMrgIf (SortedStrategy n ind sub) c t f) ->
    P (SIMrgIf (SortedStrategy n ind sub) c t f).
  Hypothesis EvalSILtCase : forall {n : nat} ind sub c t fc ft ff ti fti ffi,
    ~IsConc c ->
    AllInUnion (fun x => ind x = Some ti) t ->
    AllInUnion (fun x => ind x = Some fti) ft ->
    ind (left_most ff) = Some ffi ->
    (fti <> ffi)%Z ->
    (ti < fti)%Z ->
    P (EvalValue (SortedStrategy n ind sub) (If c t (If fc ft ff))) ->
    P (SIMrgIf (SortedStrategy n ind sub) c t (If fc ft ff)).
  Hypothesis EvalSIEqCase : forall {n : nat} ind sub c t fc ft ff ti ffi n1 s (ev : n1 < n),
    ~IsConc c ->
    AllInUnion (fun x => ind x = Some ti) t ->
    AllInUnion (fun x => ind x = Some ti) ft ->
    ind (left_most ff) = Some ffi ->
    (ti <> ffi)%Z ->
    sub ti = Some (MSSubLt s ev) ->
    P (MrgIf s c t ft) ->
    P (SIMrgIf (SortedStrategy n ind sub) c t (If fc ft ff)).
  Hypothesis EvalSIGtCase : forall {n : nat} ind sub c t fc ft ff ti fti ffi,
    ~IsConc c ->
    AllInUnion (fun x => ind x = Some ti) t ->
    AllInUnion (fun x => ind x = Some fti) ft ->
    ind (left_most ff) = Some ffi ->
    (fti <> ffi)%Z ->
    (ti > fti)%Z ->
    P (MrgIf (SortedStrategy n ind sub) c t ff) ->
    P (SIMrgIf (SortedStrategy n ind sub) c t (If fc ft ff)).
  Hypothesis EvalISMrgIfCase : forall {n : nat} (ms : MergingStrategy T n) (c : SymBool) (t f : Union T),
    P (ISMrgIf ms c t f).
  Hypothesis EvalIIMrgIfCase : forall {n : nat} (ms : MergingStrategy T n) (c : SymBool) (t f : Union T),
    P (IIMrgIf ms c t f).

  Ltac solve_eval_terms_good :=
    match goal with
    | [ good : EvalTermsGood ?ms ?t |- EvalTermsGood ?ms ?t1 ] =>
      invc good; subst; invc_existT; eauto with eval
    end.
  Ltac solve_eval_terms_good' :=
    match goal with
    | [ good : EvalTermsGood ?ms ?t |- _] =>
      invc good; subst; invc_existT; eauto with eval union
    end.
  Ltac solve_eval_terms_good'' :=
    match goal with
    | [ good : EvalTermsGood ?ms (MrgIf ?msx ?c ?t ?f) |- exists n1 ms, EvalTermsGood ms ?t1 ] =>
      eexists; exists msx;
      inversion good; subst; invc_existT;
      econstructor; eauto
    end.

  Ltac clear_ind_funcs :=
    clear
      EvalValueCase
      EvalMrgIfConcCase
      EvalMrgIfSimpleCase
      EvalMrgIfSSCase
      EvalMrgIfSICase
      EvalMrgIfISCase
      EvalMrgIfIICase
      EvalSSLtCase
      EvalSSEqCase
      EvalSSGtCase
      EvalISMrgIfCase
      EvalSIDegCase
      EvalSILtCase
      EvalSIEqCase
      EvalSIGtCase
      EvalIIMrgIfCase.
    
  Obligation Tactic := (program_simpl;
    try simpl_one_dep_JMeq; subst;
    try match goal with
    | [ |- exists n1 ms, EvalTermsGood ms (EvalValue ?msc _)] =>
           eexists; exists msc
    | [ |- exists n1 ms, EvalTermsGood ms (MrgIf ?msc _ _ _)] =>
           eexists; exists msc
    | [ |- exists n1 ms, EvalTermsGood ms (SSMrgIf ?msc _ _ _)] =>
           eexists; exists msc
    | [ |- exists n1 ms, EvalTermsGood ms (SIMrgIf ?msc _ _ _)] =>
           eexists; exists msc
    | [ |- exists n1 ms, EvalTermsGood ms (ISMrgIf ?msc _ _ _)] =>
           eexists; exists msc
    | [ |- exists n1 ms, EvalTermsGood ms (IIMrgIf ?msc _ _ _)] =>
           eexists; exists msc
    end;
    try match goal with
    | [ |- EvalTermsGood _ _ ] => clear_ind_funcs
    | [ |- AllInUnion _ _ ] => clear_ind_funcs
    end;
    repeat invc_initial_eval_good;
    simpl in *;
    try solve [
      (*solve_eval_terms_good |*)
      solve_is_conc |
      unfold ms_depth; nia |
      invc_all_hm; eauto; solve_aiu |
      econstructor; eauto; invc_all_hm; eauto; solve_aiu
      (*solve_eval_terms_good' |
      solve_eval_terms_good''*)
    ]).

  Program Fixpoint EvalTerms_ind' (t : EvalTerms T) 
    (good: exists n (ms : MergingStrategy T n), EvalTermsGood ms t) {measure (metric t) lt} : P t :=
    match t with
    | EvalValue ms1 u => EvalValueCase ms1 u _
    | @MrgIf _ n ms c t f =>
      match c with
      | ConSymBool b => EvalMrgIfConcCase ms b t f _ _ _
      | _ =>
        match ms with
        | SimpleStrategy m =>
          match t, f with
          | Single tv, Single fv =>
            match m c tv fv with
            | Some r => EvalMrgIfSimpleCase m c tv fv r _ _ (EvalTerms_ind' (EvalValue ms (Single r)) _) _
            | None => _
            end
          | _, _ => _
          end
        | SortedStrategy nms ind sub =>
          match t with
          | Single tv =>
            match f with
            | Single fv => EvalMrgIfSSCase ms c tv fv _ _ (EvalTerms_ind' (SSMrgIf ms c (Single tv) (Single fv)) _)
            | If fc ft ff => EvalMrgIfSICase ms c tv fc ft ff _ _ (EvalTerms_ind' (SIMrgIf ms c (Single tv) (If fc ft ff)) _)
            end
          | If tc itt tf =>
            match f with
            | Single fv => EvalMrgIfISCase ms c tc itt tf fv _ _ (EvalTerms_ind' (ISMrgIf ms c (If tc itt tf) (Single fv)) _)
            | If fc ft ff => EvalMrgIfIICase ms c tc itt tf fc ft ff _ _
                               (EvalTerms_ind' (IIMrgIf ms c (If tc itt tf) (If fc ft ff)) _)
            end
          end
        end
      end
    | SSMrgIf ms c t f =>
      match ms with
      | SimpleStrategy m => _
      | SortedStrategy nms ind sub =>
        let tlm := left_most t in
        let flm := left_most f in
        let tis := ind tlm in
        let fis := ind flm in
        match tis, fis with
        | Some ti, Some fi =>
          match Z_dec ti fi with
          | inleft (left _) => EvalSSLtCase ind sub c t f ti fi _ _ _ _
          | inleft (right _) => EvalSSGtCase ind sub c t f ti fi _ _ _ _
          | inright _ =>
            match sub ti with
            | Some (MSSubLt s ev) => EvalSSEqCase ind sub c t f ti _ s ev _ _ _ _ (EvalTerms_ind' (MrgIf s c t f) _)
            | None => _
            end
          end
        | _, _ => _
        end
      end
    | SIMrgIf ms c t f =>
      match ms with
      | SimpleStrategy m => _
      | SortedStrategy nms ind sub =>
        match f with
        | Single _ => _
        | If fc ft ff =>
          let tlm := left_most t in
          let ftlm := left_most ft in
          let fflm := left_most ff in
          let tis := ind tlm in
          let ftis := ind ftlm in
          let ffis := ind fflm in
          match tis, ftis, ffis with
          | Some ti, Some fti, Some ffi =>
            match Z_dec fti ffi with
            | inright _ => EvalSIDegCase ind sub c t (If fc ft ff) ffi _ _ (EvalTerms_ind' (SSMrgIf ms c t (If fc ft ff)) _)
            | inleft (left _) =>
              match Z_dec ti fti with
              | inleft (left _) => EvalSILtCase ind sub c t fc ft ff ti fti ffi _ _ _ _ _ _
                  (EvalTerms_ind' (EvalValue ms (If c t (If fc ft ff))) _)
              | inleft (right _) => EvalSIGtCase ind sub c t fc ft ff ti fti ffi _ _ _ _ _ _ 
                  (EvalTerms_ind' (MrgIf ms c t ff) _)
              | inright _ =>
                match sub ti with
                | Some (MSSubLt s ev) => EvalSIEqCase ind sub c t fc ft ff ti ffi _ s ev _ _ _ _ _ _
                    (EvalTerms_ind' (MrgIf s c t ft) _)
                | None => _
                end
              end
            | inleft (right _) => _
            end
          | _, _, _ => _
          end
        end
      end
    | ISMrgIf ms c t f => EvalISMrgIfCase ms c t f
    | IIMrgIf ms c t f => EvalIIMrgIfCase ms c t f
    end.
  Obligation Tactic := (program_simpl;
    try simpl_one_dep_JMeq; subst;
    try match goal with
    | [ |- exists n1 ms, EvalTermsGood ms (EvalValue ?msc _)] =>
           eexists; exists msc
    | [ |- exists n1 ms, EvalTermsGood ms (MrgIf ?msc _ _ _)] =>
           eexists; exists msc
    | [ |- exists n1 ms, EvalTermsGood ms (SSMrgIf ?msc _ _ _)] =>
           eexists; exists msc
    | [ |- exists n1 ms, EvalTermsGood ms (SIMrgIf ?msc _ _ _)] =>
           eexists; exists msc
    | [ |- exists n1 ms, EvalTermsGood ms (ISMrgIf ?msc _ _ _)] =>
           eexists; exists msc
    | [ |- exists n1 ms, EvalTermsGood ms (IIMrgIf ?msc _ _ _)] =>
           eexists; exists msc
    end;
    try match goal with
    | [ |- EvalTermsGood _ _ ] => clear_ind_funcs
    | [ |- AllInUnion _ _ ] => clear_ind_funcs
    end;
    repeat invc_initial_eval_good;
    simpl in *).
  Next Obligation.
    eauto with eval union.
  Defined.
  Next Obligation.
    eauto with eval union.
  Defined.
  Next Obligation.
    invcd H5; invcd H9.
    invc H2. unfold SimpleDefinedAt in H0. specialize (H0 c _ _ H3 H5) as [? ?]. intuition.
    rewrite <- Heq_anonymous in H0. invc H0. eauto.
    econstructor. econstructor; eauto.
  Defined.
  Next Obligation.
    invcd H5; invcd H9.
    invc H2. unfold SimpleDefinedAt in H0. specialize (H0 c _ _ H3 H5) as [? ?]. intuition.
    rewrite H0 in Heq_anonymous. invc Heq_anonymous.
  Defined.
  Next Obligation.
    invcd H5; invcd H9.
    specialize (n1 v v0).
    exfalso. apply n1. auto.
  Defined.
  Next Obligation.
    inversiond H5; inversiond H9;
    econstructor; eauto with union; try solve_is_conc.
  Defined.
  Next Obligation.
    inversiond H5; inversiond H9;
    econstructor; eauto with union; try solve_is_conc.
  Defined.
  Next Obligation.
    inversiond H5; inversiond H9;
    econstructor; eauto with union; try solve_is_conc.
  Defined.
  Next Obligation.
    eauto with eval union.
  Defined.
  Next Obligation.
    eauto with eval union.
  Defined.
  Next Obligation.
    eauto with eval union.
  Defined.
  Next Obligation.
    eauto with eval union.
  Defined.
  Next Obligation.
    eauto with eval union.
  Defined.
  Next Obligation.
    eauto with eval union.
  Defined.
  Next Obligation.
    eauto with eval union.
  Defined.
  Next Obligation.
    clear EvalTerms_ind'.
    clear H6.
    assert (exists P, HieraricalMergingInv P s t) as [P1 H1] by (eapply hm_sub_st; eauto with inv union).
    assert (exists P, HieraricalMergingInv P s f) as [P2 H2] by (eapply hm_sub_st; eauto with inv union).
    econstructor. eauto with inv; try solve_is_conc.
    eauto with inv.
  Defined.
  Next Obligation.
    assert (ProperStrategy P0 (SortedStrategy wildcard'0 ind sub)) by eauto with inv.
    invcd H.
    unfold SortedDefinedNoBeyond in H3.
    assert (P0 (left_most t) \/ ~ P0 (left_most t)) by apply classic.
    intuition.
    - apply H2 in H0 as [z1 [n1 [s1 [evlt1 [H0 H0']]]]].  
      rewrite <- Heq_tis in H0.
      invc H0. rewrite <- Heq_anonymous in H0'. invc H0'.
    - apply H3 in H0. congruence.
  Defined.
  Next Obligation.
    assert (exists ti, Some ti = ind (left_most t)) as [ti ?] by eauto with inv.
    assert (exists fi, Some fi = ind (left_most f)) as [fi ?] by eauto with inv.
    specialize (n ti fi).
    intuition.
  Defined.
  Next Obligation.
    eauto with eval union.
  Defined.
  Next Obligation.
    assert (ProperStrategy P0 (SortedStrategy wildcard'0 ind sub)) by eauto with inv.
    assert (AllInUnion (fun x => ind x = Some ti) t) by admit.
    symmetry in Heq_tis.
    econstructor; eauto.
    inversiond H.
    specialize (proper_ms_ind_some_is_sub_some H Heq_tis) as [nsub [evlts [mssub Hsub]]].
    specialize (hm_sub_st evlts H0 Hsub et) as [P1 t1].
    eapply HMSortedI.
    4: apply Hsub.
    all: eauto 4 with inv union strategy.

    admit.
  Admitted.
  Next Obligation.
    eauto with eval union.
  Defined.

  Next Obligation.
    econstructor; eauto.
    assert (SubUnion ff (If fc ft ff)) by eauto with union.
    eauto with inv.
  Defined.
  Next Obligation.
    eauto with eval union.
  Defined.

  Next Obligation.
    assert (ProperStrategy P0 (SortedStrategy wildcard'0 ind sub)) by eauto with inv.
    invcd H.
    unfold SortedDefinedNoBeyond in H3.
    assert (P0 (left_most t) \/ ~ P0 (left_most t)) by apply classic.
    intuition.
    - apply H2 in H0 as [z1 [n1 [s1 [evlt1 [H0 H0']]]]].  
      rewrite <- Heq_tis in H0.
      invc H0. admit.
    - apply H3 in H0. congruence.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
    invcd ef; repeat aiu_simplify.
    - solve_aiu.
    - specialize (all_in_union_left_most' H0) as [z1 [H3 H3']].
      rewrite <- Heq_ffis in H3. invc H3. lia.
  Qed.
  Next Obligation.
  Admitted.
End EvalTerms_ind'.

