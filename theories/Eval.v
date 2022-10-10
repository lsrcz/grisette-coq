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

Lemma ii_same_t_good_implies_si_good : forall {T n} {ind sub} {c} {t f : Union T},
  EvalTermsGood (SortedStrategy n ind sub) (IIMrgIf (SortedStrategy n ind sub) c t f) ->
  AllInUnion (fun x => AllInUnion (fun y => ind x = ind y) t) t ->
  EvalTermsGood (SortedStrategy n ind sub) (SIMrgIf (SortedStrategy n ind sub) c t f). 
Proof.
  intros.
  invcd H.
  econstructor; eauto.
Qed.

#[global] Hint Resolve ii_same_t_good_implies_si_good : eval.

Lemma ii_same_f_good_implies_is_good : forall {T n} {ind sub} {c} {t f : Union T},
  EvalTermsGood (SortedStrategy n ind sub) (IIMrgIf (SortedStrategy n ind sub) c t f) ->
  AllInUnion (fun x => AllInUnion (fun y => ind x = ind y) f) f ->
  EvalTermsGood (SortedStrategy n ind sub) (ISMrgIf (SortedStrategy n ind sub) c t f). 
Proof.
  intros.
  invcd H.
  econstructor; eauto.
Qed.

#[global] Hint Resolve ii_same_f_good_implies_is_good : eval.

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
             (EvalValue (SortedStrategy n ind sub) (If (pandsb (pnegsb c) fc) ft f'))
  | ISDeg : forall {n} ind sub c t f ti r,
    AllInUnion (fun x => ind x = Some ti) t ->
    clos_refl_trans_1n _ EvalRule (SSMrgIf (SortedStrategy n ind sub) c t f) (EvalValue (SortedStrategy n ind sub) r) ->
    EvalRule (ISMrgIf (SortedStrategy n ind sub) c t f) (EvalValue (SortedStrategy n ind sub) r)
  | ISLt : forall {n} ind sub c tc tt tf f tti tfi fi f',
    AllInUnion (fun x => ind x = Some tti) tt ->
    AllInUnion (fun x => ind x = Some fi) f ->
    ind (left_most tf) = Some tfi ->
    (tti <> tfi)%Z ->
    (tti < fi)%Z ->
    clos_refl_trans_1n _ EvalRule (MrgIf (SortedStrategy n ind sub) c tf f) (EvalValue (SortedStrategy n ind sub) f') ->
    EvalRule (ISMrgIf (SortedStrategy n ind sub) c (If tc tt tf) f)
             (EvalValue (SortedStrategy n ind sub) (If (pandsb c tc) tt f'))
  | ISEq : forall {n} ind sub c tc tt tf f tfi fi n1 s t' (ev : n1 < n),
    AllInUnion (fun x => ind x = Some fi) tt ->
    AllInUnion (fun x => ind x = Some fi) f ->
    ind (left_most tf) = Some tfi ->
    (tfi <> fi)%Z ->
    sub fi = Some (MSSubLt s ev) ->
    clos_refl_trans_1n _ EvalRule (MrgIf s c tt f) (EvalValue s t') ->
    EvalRule (ISMrgIf (SortedStrategy n ind sub) c (If tc tt tf) f)
             (EvalValue (SortedStrategy n ind sub) (If (porsb (pnegsb c) tc) t' tf))
  | ISGt : forall {n} ind sub c tc tt tf f tti tfi fi,
    AllInUnion (fun x => ind x = Some tti) tt ->
    AllInUnion (fun x => ind x = Some fi) f ->
    ind (left_most tf) = Some tfi ->
    (tti <> tfi)%Z ->
    (tti > fi)%Z ->
    EvalRule (ISMrgIf (SortedStrategy n ind sub) c (If tc tt tf) f)
             (EvalValue (SortedStrategy n ind sub) (If (pnegsb c) f (If tc tt tf)))
  | IIDeg1 : forall {n} ind sub c t f ti r,
    AllInUnion (fun x => ind x = Some ti) t ->
    clos_refl_trans_1n _ EvalRule (SIMrgIf (SortedStrategy n ind sub) c t f)
                                  (EvalValue (SortedStrategy n ind sub) r) ->
    EvalRule (IIMrgIf (SortedStrategy n ind sub) c t f)
             (EvalValue (SortedStrategy n ind sub) r)
  | IIDeg2 : forall {n} ind sub c tc tt tf f tti tfi fi r,
    AllInUnion (fun x => ind x = Some tti) tt ->
    AllInUnion (fun x => ind x = Some fi) f ->
    ind (left_most tf) = Some tfi ->
    (tti <> tfi)%Z ->
    clos_refl_trans_1n _ EvalRule (ISMrgIf (SortedStrategy n ind sub) c (If tc tt tf) f)
                                  (EvalValue (SortedStrategy n ind sub) r) ->
    EvalRule (IIMrgIf (SortedStrategy n ind sub) c (If tc tt tf) f)
             (EvalValue (SortedStrategy n ind sub) r)
  | IILt : forall {n} ind sub c tc tt tf fc ft ff tti tfi fti ffi f',
    AllInUnion (fun x => ind x = Some tti) tt ->
    ind (left_most tf) = Some tfi ->
    AllInUnion (fun x => ind x = Some fti) ft ->
    ind (left_most ff) = Some ffi ->
    (tti <> tfi)%Z ->
    (fti <> ffi)%Z ->
    (tti < fti)%Z ->
    clos_refl_trans_1n _ EvalRule (MrgIf (SortedStrategy n ind sub) c tf (If fc ft ff))
                                  (EvalValue (SortedStrategy n ind sub) f') ->
    EvalRule (IIMrgIf (SortedStrategy n ind sub) c (If tc tt tf) (If fc ft ff))
             (EvalValue (SortedStrategy n ind sub) (If (pandsb c tc) tt f'))
  | IIEq : forall {n} ind sub c tc tt tf fc ft ff tfi fti ffi n1 s (ev : n1 < n) t' f',
    AllInUnion (fun x => ind x = Some fti) tt -> 
    ind (left_most tf) = Some tfi ->
    AllInUnion (fun x => ind x = Some fti) ft ->
    ind (left_most ff) = Some ffi ->
    (fti <> tfi)%Z ->
    (fti <> ffi)%Z ->
    sub fti = Some (MSSubLt s ev) ->
    clos_refl_trans_1n _ EvalRule (MrgIf s c tt ft) (EvalValue s t') ->
    clos_refl_trans_1n _ EvalRule (MrgIf (SortedStrategy n ind sub) c tf ff)
                                  (EvalValue (SortedStrategy n ind sub) f') ->
    EvalRule (IIMrgIf (SortedStrategy n ind sub) c (If tc tt tf) (If fc ft ff))
             (EvalValue (SortedStrategy n ind sub) (If (pitesb c tc fc) t' f'))
  | IIGt : forall {n} ind sub c tc tt tf fc ft ff tti tfi fti ffi f',
    AllInUnion (fun x => ind x = Some tti) tt ->
    ind (left_most tf) = Some tfi ->
    AllInUnion (fun x => ind x = Some fti) ft ->
    ind (left_most ff) = Some ffi ->
    (tti <> tfi)%Z ->
    (fti <> ffi)%Z ->
    (tti > fti)%Z ->
    clos_refl_trans_1n _ EvalRule (MrgIf (SortedStrategy n ind sub) c (If tc tt tf) ff)
                                  (EvalValue (SortedStrategy n ind sub) f') ->
    EvalRule (IIMrgIf (SortedStrategy n ind sub) c (If tc tt tf) (If fc ft ff))
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
  Hypothesis EvalISDegCase : forall {n : nat} ind sub c t f ti,
    ~IsConc c ->
    AllInUnion (fun x => ind x = Some ti) t ->
    P (SSMrgIf (SortedStrategy n ind sub) c t f) ->
    P (ISMrgIf (SortedStrategy n ind sub) c t f).
  Hypothesis EvalISLtCase : forall {n : nat} ind sub c tc tt tf f tti tfi fi,
    ~IsConc c ->
    AllInUnion (fun x => ind x = Some tti) tt ->
    AllInUnion (fun x => ind x = Some fi) f ->
    ind (left_most tf) = Some tfi ->
    (tti <> tfi)%Z ->
    (tti < fi)%Z ->
    P (MrgIf (SortedStrategy n ind sub) c tf f) ->
    P (ISMrgIf (SortedStrategy n ind sub) c (If tc tt tf) f).
  Hypothesis EvalISEqCase : forall {n : nat} ind sub c tc tt tf f tfi fi n1 s (ev : n1 < n),
    ~IsConc c ->
    AllInUnion (fun x => ind x = Some fi) tt ->
    AllInUnion (fun x => ind x = Some fi) f ->
    ind (left_most tf) = Some tfi ->
    (tfi <> fi)%Z ->
    sub fi = Some (MSSubLt s ev) ->
    P (MrgIf s c tt f) ->
    P (ISMrgIf (SortedStrategy n ind sub) c (If tc tt tf) f).
  Hypothesis EvalISGtCase : forall {n : nat} ind sub c tc tt tf f tti tfi fi,
    ~IsConc c ->
    AllInUnion (fun x => ind x = Some tti) tt ->
    AllInUnion (fun x => ind x = Some fi) f ->
    ind (left_most tf) = Some tfi ->
    (tti <> tfi)%Z ->
    (tti > fi)%Z ->
    P (EvalValue (SortedStrategy n ind sub) (If (pnegsb c) f (If tc tt tf))) ->
    P (ISMrgIf (SortedStrategy n ind sub) c (If tc tt tf) f).
  Hypothesis EvalIIDeg1Case : forall {n : nat} ind sub c t f ti,
    ~IsConc c ->
    AllInUnion (fun x => ind x = Some ti) t ->
    P (SIMrgIf (SortedStrategy n ind sub) c t f) ->
    P (IIMrgIf (SortedStrategy n ind sub) c t f).
  Hypothesis EvalIIDeg2Case : forall {n : nat} ind sub c tc tt tf f tti tfi fi,
    ~IsConc c ->
    AllInUnion (fun x => ind x = Some tti) tt ->
    ind (left_most tf) = Some tfi ->
    AllInUnion (fun x => ind x = Some fi) f ->
    (tti <> tfi)%Z ->
    P (ISMrgIf (SortedStrategy n ind sub) c (If tc tt tf) f) ->
    P (IIMrgIf (SortedStrategy n ind sub) c (If tc tt tf) f).
  Hypothesis EvalIILtCase : forall {n : nat} ind sub c tc tt tf fc ft ff tti tfi fti ffi,
    ~IsConc c ->
    AllInUnion (fun x => ind x = Some tti) tt ->
    ind (left_most tf) = Some tfi ->
    AllInUnion (fun x => ind x = Some fti) ft ->
    ind (left_most ff) = Some ffi ->
    (tti <> tfi)%Z ->
    (fti <> ffi)%Z ->
    (tti < fti)%Z ->
    P (MrgIf (SortedStrategy n ind sub) c tf (If fc ft ff)) ->
    P (IIMrgIf (SortedStrategy n ind sub) c (If tc tt tf) (If fc ft ff)).
  Hypothesis EvalIIEqCase : forall {n : nat} ind sub c tc tt tf fc ft ff tfi fti ffi n1 s (ev : n1 < n),
    ~IsConc c ->
    AllInUnion (fun x => ind x = Some fti) tt ->
    ind (left_most tf) = Some tfi ->
    AllInUnion (fun x => ind x = Some fti) ft ->
    ind (left_most ff) = Some ffi ->
    (fti <> tfi)%Z ->
    (fti <> ffi)%Z ->
    sub fti = Some (MSSubLt s ev) ->
    P (MrgIf s c tt ft) ->
    P (MrgIf (SortedStrategy n ind sub) c tf ff) ->
    P (IIMrgIf (SortedStrategy n ind sub) c (If tc tt tf) (If fc ft ff)).
  Hypothesis EvalIIGtCase : forall {n : nat} ind sub c tc tt tf fc ft ff tti tfi fti ffi,
    ~IsConc c ->
    AllInUnion (fun x => ind x = Some tti) tt ->
    ind (left_most tf) = Some tfi ->
    AllInUnion (fun x => ind x = Some fti) ft ->
    ind (left_most ff) = Some ffi ->
    (tti <> tfi)%Z ->
    (fti <> ffi)%Z ->
    (tti > fti)%Z ->
    P (MrgIf (SortedStrategy n ind sub) c (If tc tt tf) ff) ->
    P (IIMrgIf (SortedStrategy n ind sub) c (If tc tt tf) (If fc ft ff)).

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
      EvalSIDegCase
      EvalSILtCase
      EvalSIEqCase
      EvalSIGtCase
      EvalISDegCase
      EvalISLtCase
      EvalISEqCase
      EvalISGtCase
      EvalIIDeg1Case
      EvalIIDeg2Case
      EvalIILtCase
      EvalIIEqCase
      EvalIIGtCase.
    
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
      unfold ms_depth; simpl in *; lia |
      invc_all_hm; eauto; solve_aiu |
      econstructor; eauto; invc_all_hm; eauto; solve_aiu |
      eauto with eval union
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
    | ISMrgIf ms c t f =>
      match ms with
      | SimpleStrategy m => _
      | SortedStrategy nms ind sub =>
        match t with
        | Single _ => _
        | If tc ttu tf =>
          let ttlm := left_most ttu in
          let tflm := left_most tf in
          let flm := left_most f in
          let ttis := ind ttlm in
          let tfis := ind tflm in
          let fis := ind flm in
          match ttis, tfis, fis with
          | Some tti, Some tfi, Some fi =>
            match Z_dec tti tfi with
            | inright _ => EvalISDegCase ind sub c (If tc ttu tf) f tti _ _ (EvalTerms_ind' (SSMrgIf ms c (If tc ttu tf) f) _)
            | inleft (left _) =>
              match Z_dec tti fi with
              | inleft (left _) => EvalISLtCase ind sub c tc ttu tf f tti tfi fi _ _ _ _ _ _
                  (EvalTerms_ind' (MrgIf ms c tf f) _)
              | inleft (right _) => EvalISGtCase ind sub c tc ttu tf f tti tfi fi _ _ _ _ _ _
                  (EvalTerms_ind' (EvalValue ms (If (pnegsb c) f (If tc ttu tf))) _)
              | inright _ =>
                match sub tti with
                | Some (MSSubLt s ev) => EvalISEqCase ind sub c tc ttu tf f tfi fi _ s ev _ _ _ _ _ _
                    (EvalTerms_ind' (MrgIf s c ttu f) _)
                | None => _
                end
              end
            | inleft (right _) => _
            end
          | _, _, _ => _
          end
        end
      end
    | IIMrgIf ms c t f =>
      match ms with
      | SimpleStrategy m => _
      | SortedStrategy nms ind sub =>
        match t, f with
        | If tc ttu tf, If fc ft ff =>
          let ttlm := left_most ttu in
          let tflm := left_most tf in
          let ftlm := left_most ft in
          let fflm := left_most ff in
          let ttis := ind ttlm in
          let tfis := ind tflm in
          let ftis := ind ftlm in
          let ffis := ind fflm in
          match ttis, tfis, ftis, ffis with
          | Some tti, Some tfi, Some fti, Some ffi =>
            match Z_dec tti tfi with
            | inright _ => EvalIIDeg1Case ind sub c (If tc ttu tf) (If fc ft ff) tti _ _ (EvalTerms_ind' (SIMrgIf ms c (If tc ttu tf) (If fc ft ff)) _)
            | inleft (left _) =>
              match Z_dec fti ffi with
              | inright _ => EvalIIDeg2Case ind sub c tc ttu tf (If fc ft ff) tti tfi fti _ _ _ _ _ (EvalTerms_ind' (ISMrgIf ms c (If tc ttu tf) (If fc ft ff)) _)
              | inleft (left _) =>
                match Z_dec tti fti with
                | inleft (left _) => EvalIILtCase ind sub c tc ttu tf fc ft ff tti tfi fti ffi _ _ _ _ _ _ _ _
                    (EvalTerms_ind' (MrgIf ms c tf (If fc ft ff)) _)
                | inleft (right _) => EvalIIGtCase ind sub c tc ttu tf fc ft ff tti tfi fti ffi _ _ _ _ _ _ _ _
                    (EvalTerms_ind' (MrgIf ms c (If tc ttu tf) ff) _)
                | inright _ =>
                  match sub tti with
                  | Some (MSSubLt s ev) => EvalIIEqCase ind sub c tc ttu tf fc ft ff tfi fti ffi _ s ev _ _ _ _ _ _ _ _
                      (EvalTerms_ind' (MrgIf s c ttu ft) _)
                      (EvalTerms_ind' (MrgIf ms c tf ff) _)
                  | None => _
                  end
                end
              | inleft (right _) => _
              end
            | inleft (right _) => _
            end
          | _, _, _, _ => _
          end
        | _, _ => _
        end
      end
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
    simpl in * ).
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
    assert (ProperStrategy P0 (SortedStrategy wildcard'0 ind sub)) by eauto with inv.
    assert (AllInUnion (fun x => ind x = Some ti) t) by solve_aiu.
    symmetry in Heq_tis.
    econstructor; eauto.
    inversiond H.
    specialize (proper_ms_ind_some_is_sub_some H Heq_tis) as [nsub [evlts [mssub Hsub]]].
    specialize (hm_sub_st evlts H0 Hsub et) as [P1 t1].
    eapply HMSortedI.
    4: apply Hsub.
    all: eauto 4 with inv strategy.
    aiu_simplify.
    eauto with inv.
    eapply hm_lm_is_lowerbound; eauto.
  Defined.
  Next Obligation.
    econstructor; eauto.
    assert (SubUnion ff (If fc ft ff)) by eauto with union.
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
      invc H0.
      symmetry in Heq_ftis.
      specialize (H8 _ _ _ _ evlt1 Heq_ftis H0') as [P' [H8 H8']].
      symmetry in Heq_ftis.
      assert (ProperStrategy P0 (SortedStrategy wildcard'0 ind sub)) by eauto with inv.
      assert (SubStrategy P' P0 z1 s1 (SortedStrategy wildcard'0 ind sub)) by eauto with sub.
      assert (AllInUnion (fun x => ind x = Some z1) t) by solve_aiu.
      assert (AllInUnion (fun x => (AllInUnion (fun y => ind x = ind y) ft)) ft) by eauto with inv.
      assert (AllInUnion (fun x => ind x = Some z1) ft) by solve_aiu.
      assert (HieraricalMergingInv P0 (SortedStrategy wildcard'0 ind sub) ft) by eauto with inv.
      rewrite <- Heq_anonymous in H0'.
      invcd H0'.
      econstructor; eauto with subinv.
    - apply H3 in H0. congruence.
  Defined.
  Next Obligation.
    invcd ef.
    - specialize (all_in_union_left_most' H7) as [? ?].
      rewrite <- Heq_ftis in H0.
      invcd H0.
      invcd H5.
      apply H2 in H as [z' [n' [s' [e' [H H']]]]].
      rewrite <- Heq_ftis in H.
      invcd H.
      rewrite H' in Heq_anonymous.
      congruence.
    - specialize (all_in_union_left_most' H7) as [? ?].
      rewrite <- Heq_ftis in H0.
      invcd H0.
      invcd H4.
      apply H2 in H as [z' [n' [s' [e' [H H']]]]].
      rewrite <- Heq_ftis in H.
      invcd H.
      rewrite H' in Heq_anonymous.
      congruence.
  Defined.
  Next Obligation.
    invcd ef; repeat aiu_simplify.
    - solve_aiu.
    - specialize (all_in_union_left_most' H0) as [z1 [H3 H3']].
      rewrite <- Heq_ffis in H3. invc H3. lia.
  Defined.
  Next Obligation.
    assert (HieraricalMergingInv P0 (SortedStrategy wildcard'2 ind sub) ft) by eauto with inv.
    assert (HieraricalMergingInv P0 (SortedStrategy wildcard'2 ind sub) ff) by eauto with inv.
    specialize (hm_lm_ind_exist et) as [ti ?].
    specialize (hm_lm_ind_exist H) as [fti ?].
    specialize (hm_lm_ind_exist H0) as [ffi ?].
    specialize (n ti fti ffi).
    intuition.
  Defined.


  (* IS *)
  Next Obligation.
    econstructor; eauto with inv.
  Defined.
  Next Obligation.
    econstructor.
    assert (fi < tti)%Z by lia.
    eapply hm_if_no_deg; eauto.
    solve_aiu.
  Defined.
  Next Obligation.
    assert (ProperStrategy P0 (SortedStrategy wildcard'0 ind sub)) by eauto with inv.
    symmetry in Heq_fis.
    symmetry in Heq_anonymous.
    (*specialize (proper_ms_ind_some_is_sub_some H Heq_fis) as [n' [ev' [s' ?]]].*)
    specialize (proper_ms_sub_from_subfunc H Heq_fis Heq_anonymous) as [Psub ?].
    assert (AllInUnion (fun x => ind x = Some fi) f) by eauto with union.
    assert (AllInUnion (fun x => ind x = Some fi) ttu) by eauto with inv.
    assert (HieraricalMergingInv Psub s f) by eauto with subinv.
    assert (HieraricalMergingInv P0 (SortedStrategy wildcard'0 ind sub) ttu) by eauto with inv.
    assert (HieraricalMergingInv Psub s ttu) by eauto with subinv.
    econstructor; eauto.
  Defined.
  Next Obligation.
    assert (ProperStrategy P0 (SortedStrategy wildcard'0 ind sub)) by eauto with inv.
    symmetry in Heq_fis.
    specialize (proper_ms_ind_some_is_sub_some H Heq_fis) as [n' [ev' [s' ?]]].
    rewrite H0 in Heq_anonymous. congruence.
  Defined.
  Next Obligation.
    invcd et.
    - solve_aiu.
    - specialize (all_in_union_left_most' H7) as [? ?].
      specialize (all_in_union_left_most' H8) as [? [z' [? ?]]].
      rewrite H0 in Heq_ttis. rewrite H2 in Heq_tfis.
      invcd Heq_ttis. invcd Heq_tfis. lia.
  Defined.
  Next Obligation.
    assert (HieraricalMergingInv P0 (SortedStrategy wildcard'2 ind sub) ttu) by eauto with inv.
    assert (HieraricalMergingInv P0 (SortedStrategy wildcard'2 ind sub) tf) by eauto with inv.
    specialize (hm_lm_ind_exist ef) as [fi ?].
    specialize (hm_lm_ind_exist H) as [tti ?].
    specialize (hm_lm_ind_exist H0) as [tfi ?].
    specialize (n tti tfi fi).
    intuition.
  Defined.

  (* II *)
  Next Obligation.
    econstructor; eauto with inv.
  Defined.
  Next Obligation.
    econstructor; eauto with inv.
  Defined.
  Next Obligation.
    assert (ProperStrategy P0 (SortedStrategy wildcard'0 ind sub)) by eauto with inv.
    symmetry in Heq_ttis.
    symmetry in Heq_anonymous.
    specialize (proper_ms_sub_from_subfunc H Heq_ttis Heq_anonymous) as [Psub ?].
    assert (AllInUnion (fun x => ind x = Some fti) ft) by eauto with inv.
    assert (AllInUnion (fun x => ind x = Some fti) ttu) by eauto with inv.
    assert (HieraricalMergingInv P0 (SortedStrategy wildcard'0 ind sub) ft) by eauto with inv.
    assert (HieraricalMergingInv Psub s ft) by eauto with subinv.
    assert (HieraricalMergingInv P0 (SortedStrategy wildcard'0 ind sub) ttu) by eauto with inv.
    assert (HieraricalMergingInv Psub s ttu) by eauto with subinv.
    econstructor; eauto.
  Defined.
  Next Obligation.
    econstructor; eauto with inv.
  Defined.
  Next Obligation.
    assert (ProperStrategy P0 (SortedStrategy wildcard'0 ind sub)) by eauto with inv.
    symmetry in Heq_ftis.
    specialize (proper_ms_ind_some_is_sub_some H Heq_ftis) as [n' [ev' [s' ?]]].
    rewrite H0 in Heq_anonymous. congruence.
  Defined.
  Next Obligation.
    invcd ef.
    - solve_aiu.
    - specialize (all_in_union_left_most' H7) as [? ?].
      specialize (all_in_union_left_most' H8) as [? [z' [? ?]]].
      rewrite H0 in Heq_ftis. rewrite H2 in Heq_ffis.
      invcd Heq_ftis. invcd Heq_ffis. lia.
  Defined.
  Next Obligation.
    invcd et.
    - solve_aiu.
    - specialize (all_in_union_left_most' H7) as [? ?].
      specialize (all_in_union_left_most' H8) as [? [z' [? ?]]].
      rewrite H0 in Heq_ttis. rewrite H2 in Heq_tfis.
      invcd Heq_ttis. invcd Heq_tfis. lia.
  Defined.
  Next Obligation.
    assert (HieraricalMergingInv P0 (SortedStrategy wildcard'3 ind sub) ttu) by eauto with inv.
    assert (HieraricalMergingInv P0 (SortedStrategy wildcard'3 ind sub) tf) by eauto with inv.
    assert (HieraricalMergingInv P0 (SortedStrategy wildcard'3 ind sub) ft) by eauto with inv.
    assert (HieraricalMergingInv P0 (SortedStrategy wildcard'3 ind sub) ff) by eauto with inv.
    specialize (hm_lm_ind_exist H) as [tti ?].
    specialize (hm_lm_ind_exist H0) as [tfi ?].
    specialize (hm_lm_ind_exist H1) as [fti ?].
    specialize (hm_lm_ind_exist H2) as [ffi ?].
    specialize (n tti tfi fti ffi).
    intuition.
  Defined.
  Next Obligation.
    destruct t as [tv|tc tt tf]; destruct f as [fv|fc ft ff]; simpl in *; try solve [exfalso; auto].
    specialize (n tc tt tf fc ft ff).
    intuition.
  Defined.
End EvalTerms_ind'.

Definition all_in_et {T} P (et : EvalTerms T) : Prop :=
  match et with
  | EvalValue _ u => AllInUnion P u
  | MrgIf _ _ t f => AllInUnion P t /\ AllInUnion P f
  | SSMrgIf _ _ t f => AllInUnion P t /\ AllInUnion P f
  | SIMrgIf _ _ t f => AllInUnion P t /\ AllInUnion P f
  | ISMrgIf _ _ t f => AllInUnion P t /\ AllInUnion P f
  | IIMrgIf _ _ t f => AllInUnion P t /\ AllInUnion P f
  end.

#[global] Hint Unfold all_in_et : eval.

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

#[global] Hint Resolve value_evaluate_to_value : eval.

Ltac invcd_eval_rule H :=
  invcd H; simpl in *; try solve [exfalso; auto].

Lemma all_in_union_if_contra : forall {T} {ind : T -> option Z} {c} {t f} {ti fi} {i},
  AllInUnion (fun x => ind x = Some ti) t ->
  ind (left_most f) = Some fi ->
  ti <> fi ->
  AllInUnion (fun x => ind x = Some i) (If c t f) ->
  False.
Proof.
  intros.
  invcd H2.
  specialize (all_in_union_left_most' H7); simpl; intros.
  rewrite H0 in H2. invcd H2. solve_aiu.
Qed.

Theorem eval_do_not_change_index_subrt : forall {T n n1} {P ind sub} {i t} {Psub} {s : MergingStrategy T n1} (b : bool),
  ProperStrategy P (SortedStrategy n ind sub) ->
  SubStrategyRT Psub P s (SortedStrategy n ind sub) ->
  EvalTermsGood s t ->
  (if b
    then all_in_et (fun (x : T) => ind x = Some i) t
    else all_in_et (fun x => exists i1, ind x = Some i1 /\ (i1 > i)%Z) t) ->
  forall u, t ==>* (EvalValue s u) ->
  (if b
    then AllInUnion (fun (x : T) => ind x = Some i) u
    else AllInUnion (fun x => exists i1, ind x = Some i1 /\ (i1 > i)%Z) u).
Proof.
  intros.
  assert (good:exists n1 (ms1 : MergingStrategy T n1), EvalTermsGood ms1 t) by (repeat eexists; eauto).
  generalize dependent u.
  generalize dependent ind.
  generalize dependent sub.
  generalize dependent Psub.
  generalize dependent n1.
  apply EvalTerms_ind' with (t := t); intros; try invcd_eval_value; subst; eauto.
  { invcd H6. destruct b; simpl in *; invcd_eval_rule H7;
    invcd_eval_value; intuition.
  }
  { clear t good.
    invcd H3.
    invcd H7. invcd_eval_rule H3.
    repeat invcd_eval_value.
    rewrite H14 in H0. invcd H0.
    destruct b; simpl in *;
    invcd H6; invcd H0; invcd H3;
    eapply H1; clear H1; eauto; econstructor.
    1,3: clear H5 H4 sub H2 H Psub; eauto with inv.
    - invcd H5.
      eapply proper_ms_subt_simple_t.
      3: apply H14.
      all: eauto.
    - destruct H7 as [i1 ?].
      invcd H5.
      exists i1.
      intuition.
      eapply proper_ms_subt_simple_t.
      3: apply H14.
      all: eauto.
  }
  1-4: destruct b; simpl in *; destruct ms; simpl in H0; try solve [exfalso; auto];
    invcd H2; invcd H5; invcd H6; invcd H5; try solve [exfalso; auto];
    invcd_eval_value;
    eapply H1; simpl; eauto;
    econstructor; eauto; constructor; constructor; auto.
  { destruct b; simpl in *; invcd H6; invcd H7; invcd H6; try solve_aiu;
    invcd_eval_value;
    solve_aiu.
  }
  { destruct b; simpl in *.
    all: invcd H7; invcd H8; invcd H7; try solve_aiu.
    all: invcd_eval_value.
    all: assert (i0 = i1) by eauto with union.
    all: subst.
    all: rewrite H2 in H21; invcd H21.
    all: clear H19 H20.
    all: specialize (all_in_union_left_most' H0); simpl; intros.
    all: invcd H4.
    all: assert (ProperStrategy Psub (SortedStrategy n2 ind sub)) by eauto with sub.
    all: assert (ProperStrategy P0 (SortedStrategy n2 ind sub)) by eauto with inv.
    all: specialize (proper_ms_sub_from_subfunc H4 H7 H2) as [Psub' Hsub'].
    all: eapply H3; simpl in *.
    5,10: apply H22.
    all: eauto.
    1,3: specialize (proper_ms_sub_from_subfunc H8 H7 H2) as [Psub'' Hsub''];
         econstructor; eapply hm_sub_hm; eauto.
    all: eapply sub_subrt_subrt; eauto.
  }
  { destruct b; simpl in *; invcd H6; invcd H7; invcd H6; try solve_aiu.
    all: invcd_eval_value.
    all: solve_aiu.
  }

  (* SIDeg *)
  { destruct b; simpl in *.
    all: invcd H5.
    all: invcd H6.
    all: invcd H5.
    1,5: invcd_eval_value;
      eapply H1;[ | | | | apply H18];
      simpl; eauto with eval union.
    all: invcd H0;
      specialize (all_in_union_left_most' H12); simpl; intros;
      rewrite H19 in H0; invcd H0;
      solve_aiu.
  }
  
  (* SI* *)
  1-3: destruct b; simpl in *; (invcd H6; clear H15 H21;
    invcd H9; invcd H11;
    invcd H10;
    invcd H9; try solve_aiu);
    try solve [exfalso; eauto 2 using all_in_union_if_contra]; invcd_eval_value.

  (* SILt *)
  1-2: eauto with union.

  (* SIEq *)
  1-2: assert (ti = ti0) by eauto with union; subst.
  1-2: rewrite H4 in H28; invcd H28.
  1-2: constructor; eauto.
  1-2: assert (HieraricalMergingInv P0 (SortedStrategy n0 ind sub1) ft) by eauto with inv.
  1-2: assert (ProperStrategy P0 (SortedStrategy n0 ind sub1)) by eauto with inv.
  1-2: specialize (all_in_union_left_most' H25); simpl; intro.
  1-2: assert (ProperStrategy Psub (SortedStrategy n0 ind sub1)) by eauto with sub.
  1-2: specialize (all_in_union_left_most' H0); simpl; intros.
  1-2: specialize (proper_ms_sub_from_subfunc H12 H14 H4) as [Psub' Hsub'].
  1-2: eapply H5.
  5,10: apply H29.
  1-8: simpl; eauto.
  1,3: specialize (proper_ms_sub_from_subfunc H10 H11 H4) as [Psub'' Hsub''];
      econstructor; eapply hm_sub_hm; eauto.
  1,2: eapply sub_subrt_subrt; eauto.

  (* SIGt *)
  1,2: constructor; auto;
    eapply H5; intuition; eauto;
    econstructor; eauto with inv.

  (* ISDeg *)
  { destruct b; simpl in *.
  all: invcd H5.
  all: invcd H6.
  all: invcd H5.
  1,5: invcd_eval_value;
    eapply H1; [ | | | | apply H18];
    simpl; eauto with eval union.

  all: invcd H0;
    specialize (all_in_union_left_most' H12); simpl; intros;
    rewrite H19 in H0; invcd H0;
    solve_aiu.
  }

  (* IS* *)
  1-3: destruct b; simpl in *; (invcd H6; clear H15 H21;
    invcd H9; invcd H6; invcd H10; invcd H6; try solve_aiu);
    try solve [exfalso; eauto 2 using all_in_union_if_contra]; invcd_eval_value.

  (* ISLt *)
  1-2: constructor; auto;
    eapply H5; intuition; eauto;
    econstructor; eauto with inv.
    
  (* ISEq *)
  1-2: assert (fi = fi0) by eauto with union; subst.
  1-2: rewrite H4 in H28; invcd H28.
  1-2: constructor; eauto.
  1-2: assert (HieraricalMergingInv P0 (SortedStrategy n0 ind sub1) tt) by eauto with inv.
  1-2: assert (ProperStrategy P0 (SortedStrategy n0 ind sub1)) by eauto with inv.
  1-2: specialize (all_in_union_left_most' H25); simpl; intro.
  1-2: assert (ProperStrategy Psub (SortedStrategy n0 ind sub1)) by eauto with sub.
  1-2: specialize (all_in_union_left_most' H0); simpl; intros.
  1-2: specialize (proper_ms_sub_from_subfunc H12 H14 H4) as [Psub' Hsub'].
  1-2: eapply H5.
  5,10: apply H29.
  1-8: simpl; eauto.
  1,3: specialize (proper_ms_sub_from_subfunc H9 H10 H4) as [Psub'' Hsub''];
      econstructor; eapply hm_sub_hm; eauto.
  1,2: eapply sub_subrt_subrt; eauto.

  (* ISGt *)
  1-2: eauto with union.

  (* IIDeg1 *)
  { destruct b; simpl in *.
  all: invcd H5.
  all: invcd H6.
  all: invcd H5.
  1,6: invcd_eval_value;
    eapply H1; [ | | | | apply H18];
    simpl; eauto with eval union.

  all: invcd H0; specialize (all_in_union_left_most' H12); simpl; intros.
  1,5: rewrite H19 in H0; invcd H0;
    solve_aiu.
  all: rewrite H17 in H0; invcd H0;
    solve_aiu.
  }

  (* IIDeg2 *)
  { destruct b; simpl in *.
  all: invcd H8.
  all: invcd H9.
  all: invcd H8.
  2,7: invcd_eval_value;
    eapply H4; [ | | | | apply H26];
    simpl; eauto with eval union.

  1,5: invcd H20; specialize (all_in_union_left_most' H15); simpl; intros;
  rewrite H8 in H1; invcd H1; solve_aiu.

  all: invcd H2; specialize (all_in_union_left_most' H15); simpl; intros;
  rewrite H25 in H2; invcd H2; solve_aiu.
  }

  (* II* *)
  1,3: destruct b; simpl in *; (invcd H8; clear H17 H22 H23;
  invcd H11; invcd H8; invcd H13; invcd H12; invcd H8; try solve_aiu);
  try solve [exfalso; eauto 2 using all_in_union_if_contra]; invcd_eval_value.

  (* IILt, IIGt *)
  1-4: constructor; auto;
    eapply H7; intuition; eauto;
    econstructor; eauto with inv.

  (* IIEq *)
  destruct b; simpl in *; (invcd H9; clear H18 H23 H24;
  invcd H12; invcd H9; invcd H14; invcd H13; invcd H9; try solve_aiu);
  try solve [exfalso; eauto 2 using all_in_union_if_contra]; invcd_eval_value; constructor.


  2,4: eapply H8; intuition; eauto;
  econstructor; eauto with inv.

  1-2: assert (fti = fti0) by eauto with union; subst.
  1-2: rewrite H6 in H35; invcd H35.
  1-2: assert (HieraricalMergingInv P0 (SortedStrategy n0 ind sub1) tt) by eauto with inv.
  1-2: assert (HieraricalMergingInv P0 (SortedStrategy n0 ind sub1) ft) by eauto with inv.
  1-2: assert (ProperStrategy P0 (SortedStrategy n0 ind sub1)) by eauto with inv.
  1-2: assert (ProperStrategy Psub (SortedStrategy n0 ind sub1)) by eauto with sub.
  1-2: specialize (all_in_union_left_most' H29); simpl; intro.
  1-2: specialize (all_in_union_left_most' H31); simpl; intros.
  1-2: specialize (proper_ms_sub_from_subfunc H14 H17 H6) as [Psub' Hsub'].
  1-2: eapply H7.
  5,10: apply H36.
  1-8: simpl; eauto.
  1,3: specialize (proper_ms_sub_from_subfunc H13 H17 H6) as [Psub'' Hsub''];
      econstructor; eapply hm_sub_hm; eauto.
  1,2: eapply sub_subrt_subrt; eauto.
Qed.

Theorem eval_do_not_change_index_subrt_eq : forall {T n n1} {P ind sub} {i t} {Psub} {s : MergingStrategy T n1},
  SubStrategyRT Psub P s (SortedStrategy n ind sub) ->
  EvalTermsGood s t ->
  all_in_et (fun (x : T) => ind x = Some i) t ->
  forall u, t ==>* (EvalValue s u) ->
  AllInUnion (fun (x : T) => ind x = Some i) u.
Proof.
  intros.
  assert (ProperStrategy P (SortedStrategy n ind sub)) by eauto with sub.
  eapply (eval_do_not_change_index_subrt true); eauto.
Qed.

Theorem eval_do_not_change_index_subrt_lowerbound : forall {T n n1} {P ind sub} {i t} {Psub} {s : MergingStrategy T n1},
  SubStrategyRT Psub P s (SortedStrategy n ind sub) ->
  EvalTermsGood s t ->
  all_in_et (fun x => exists i1, ind x = Some i1 /\ (i1 > i)%Z) t ->
  forall u, t ==>* (EvalValue s u) ->
  AllInUnion (fun x => exists i1, ind x = Some i1 /\ (i1 > i)%Z) u.
Proof.
  intros.
  assert (ProperStrategy P (SortedStrategy n ind sub)) by eauto with sub.
  eapply (eval_do_not_change_index_subrt false); eauto.
Qed.

Theorem eval_do_not_change_index_eq : forall {T n} {ind sub} {i t},
  EvalTermsGood (SortedStrategy n ind sub) t ->
  all_in_et (fun (x : T) => ind x = Some i) t ->
  forall u, t ==>* (EvalValue (SortedStrategy n ind sub) u) ->
  AllInUnion (fun (x : T) => ind x = Some i) u.
Proof.
  intros.
  assert (exists P, ProperStrategy P (SortedStrategy n ind sub)) as [P ?] by eauto with eval.
  eapply (eval_do_not_change_index_subrt_eq); eauto with sub.
Qed.

#[global] Hint Resolve eval_do_not_change_index_eq : eval.

Theorem eval_do_not_change_index_sub_eq : forall {T n n1} {P ind sub} {i t} {Psub} {s : MergingStrategy T n1},
  SubStrategy Psub P i s (SortedStrategy n ind sub) ->
  EvalTermsGood s t ->
  all_in_et (fun (x : T) => ind x = Some i) t ->
  forall u, t ==>* (EvalValue s u) ->
  AllInUnion (fun (x : T) => ind x = Some i) u.
Proof.
  intros.
  eapply (eval_do_not_change_index_subrt_eq); eauto with sub.
Qed.

#[global] Hint Resolve eval_do_not_change_index_sub_eq : eval.

Theorem eval_do_not_change_index_lowerbound : forall {T n} {ind sub} {i t},
  EvalTermsGood (SortedStrategy n ind sub) t ->
  all_in_et (fun x => exists i1, ind x = Some i1 /\ (i1 > i)%Z) t ->
  forall u, (t : EvalTerms T) ==>* (EvalValue (SortedStrategy n ind sub) u) ->
  AllInUnion (fun x => exists i1, ind x = Some i1 /\ (i1 > i)%Z) u.
Proof.
  intros.
  assert (exists P, ProperStrategy P (SortedStrategy n ind sub)) as [P ?] by eauto with eval.
  eapply (eval_do_not_change_index_subrt_lowerbound); eauto with sub.
Qed.

#[global] Hint Resolve eval_do_not_change_index_lowerbound : eval.

Theorem eval_do_not_change_index_sub_lowerbound : forall {T n n1} {P ind sub} {i t} {Psub} {s : MergingStrategy T n1},
  ProperStrategy P (SortedStrategy n ind sub) ->
  SubStrategy Psub P i s (SortedStrategy n ind sub) ->
  EvalTermsGood s t ->
  all_in_et (fun x => exists i1, ind x = Some i1 /\ (i1 > i)%Z) t ->
  forall u, t ==>* (EvalValue s u) ->
  AllInUnion (fun x => exists i1, ind x = Some i1 /\ (i1 > i)%Z) u.
Proof.
  intros.
  eapply (eval_do_not_change_index_subrt_lowerbound); eauto with sub.
Qed.

#[global] Hint Resolve eval_do_not_change_index_sub_lowerbound : eval.

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

