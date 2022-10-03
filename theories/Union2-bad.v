Require Import Grisette.SymBoolOp.
Require Import Grisette.Union.
Require Import Grisette.GeneralTactics.
Require Import Coq.ZArith.Int.
Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.ZArith_dec.
Require Import Lia.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Logic.ClassicalFacts.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.Classical_Prop.
Require Import Grisette.CpdtTactics.
Require Import Program.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.Peano_dec.
Require Import String.
Require Import List.
Open Scope Z.
Open Scope nat.

(*
Inductive EvalChain {T} : nat -> EvalTerms T -> EvalTerms T -> Prop :=
  | ECRefl : forall x, EvalChain 0 x x
  | ECStep : forall x y, EvalRule x y -> EvalChain 1 x y
  | ECTrans : forall n x y z, EvalRule x y -> EvalChain n y z -> EvalChain (S n) x z. 
  *)

Notation "t1 '==>*(' n ')' t2" := (EvalChain n t1 t2) (at level 75).
    
Hint Constructors EvalChain.

Theorem progress : forall {T n t} {ms : MergingStrategy T n},
  EvalTermsGood ms t ->
  (exists u, t ==>* (EvalValue ms u) /\ EvalTermsGood ms (EvalValue ms u)).
  (*~ is_eval_value t ->
  (exists t' n' (ms' : MergingStrategy T n'), t ==> t' /\ EvalTermsGood ms' t' /\ SubStrategyRT ms' ms).*)
Proof.
  intros.
  assert (good:exists n1 (ms1 : MergingStrategy T n1), EvalTermsGood ms1 t) by (repeat eexists; eauto).
  generalize dependent n.
  apply EvalTerms_ind' with (t := t); intros; subst; eauto.
  all: invc_initial_eval_good; simpl in *; try solve [exfalso; eauto].
  { repeat eexists; eauto. }
  { destruct b; repeat eexists; eauto. }
  { repeat eexists; eauto.
    econstructor; econstructor; eauto.
    invc H7; subst; invc_existT.
    invc H11; subst; invc_existT.
    invc H8. specialize (H7 c _ _ H9 H12). crush.
  }
  Ltac specialize_sorted_ms :=
    match goal with
    | [ H : IsSortedStrategy ?ms |- _] => destruct ms; simpl in H; [exfalso; auto | ]; intuition
    end.
  Ltac specialize_ih_mrgif_dispatch :=
    match goal with
    | [ H : forall n0 ms0, EvalTermsGood ms0 (?hd ?ms ?c ?t ?f) -> exists _, _ |- exists _, _] =>
      let H1 := fresh "H" in
      let u := fresh "u" in
      specialize (H _ ms);
      assert (H1:EvalTermsGood ms (hd ms c t f)) by (econstructor; eauto);
      specialize (H H1) as [u [? ?]]; exists u
    end.
  1-4:
    specialize_sorted_ms;
    specialize_ih_mrgif_dispatch;
    econstructor; eauto.
  { repeat eexists; eauto.
    econstructor; econstructor; eauto.
    all: admit.
   }
  { admit. }
  { exists (If (pnegsb c) f t0); eauto.
    intuition. eauto.
    econstructor; econstructor. eauto. all: eauto.
    all: admit.
   }



      

   [specialize (H3 ms0)|specialize (H1 ms0)].


Restart.
  intros.
  induction t;
  invc H; subst; repeat invc_existT.
  left; eexists; eauto.
  all: right.
  - destruct (IsConcDec c) as [Hc|Hc].
    + destruct c; invc Hc. destruct b; repeat eexists; eauto.
    + destruct ms0.
      * invc H3; invc H7; subst. repeat invc_existT.
        invc H1.
        unfold SimpleDefinedAt in H7.
        specialize (H7 c _ _ H4 H6) as [r [? ?]].
        repeat eexists; econstructor; eauto.
        econstructor; eauto.
      * destruct t; destruct f; repeat eexists; eauto 6.
  Ltac solve_ss_ne lt ti' fi' :=
    repeat eexists;
    [ match lt with
      | True => eapply SSLt with (ti := ti') (fi := fi')
      | _ => eapply SSGt with (ti := ti') (fi := fi')
      end;
      try solve [econstructor; eauto|lia|solve_aiu]
    | econstructor;
      eapply HMSortedI; eauto; try solve_aiu|eauto].

  Ltac conds_for_single ind sub v :=
    match goal with
    | [H1 : SortedDefinedAt ind sub ?P,
       H2 : forall v z n1 s evlt, ind v = Some z -> sub z = Some (MSSubLt s evlt) ->
              exists P', ProperStrategy P' s /\ P' v,
       H3 : ?P v|- _] =>
      let h1 := fresh "H1" in
      let h2 := fresh "H2" in
      assert (h1:=H1); assert (h2:=H2);
      let z := fresh "z" in
      let n := fresh "n" in
      let s := fresh "s" in
      let evlt := fresh "evlt" in
      let h1' := fresh "H1" in
      let h1'' := fresh "H1" in
      specialize (h1 _ H3) as [z [n [s [evlt [h1' h1'']]]]];
      let P' := fresh "P" in
      specialize (h2 _ _ _ _ evlt h1' h1'') as [P' [? ?]];
      assert (HieraricalMergingInv P' s (Single v)) by (econstructor; eauto)
    end.

  Ltac clear_all_ps_sorted_inv_res :=
    repeat match goal with
    | [H : SortedSubDefinedNoOverlap _ _ _ |- _] => clear H
    | [H : SortedSubDefinedNoBeyond _ _ _ |- _] => clear H
    | [H : SortedDefinedNoBeyond _ _ _ |- _] => clear H
    | [H : SortedDefinedAt _ _ _ |- _] => clear H
    | [H : forall v z n1 s evlt, ?ind v = Some z -> ?sub z = Some (MSSubLt s evlt) ->
             exists P', ProperStrategy P' s /\ P' v |- _] => clear H
    end.

  Ltac find_eq_substrategy :=
    match goal with
    | [H1 : ?sub ?z = Some (MSSubLt ?s1 ?evlt1),
       H2 : ?sub ?z = Some (MSSubLt ?s2 ?evlt2) |- _] =>
       rewrite H1 in H2; invc H2; subst; repeat invc_existT
    end.
      
  - inversion et; inversion ef; repeat invc_existT;
    try congruence; try solve [exfalso;eauto].
    + inversion H1; repeat invc_existT.
      conds_for_single ind sub0 v.
      conds_for_single ind sub0 v0.
      clear_all_ps_sorted_inv_res.
      destruct (Z_dec z0 z1) as [[Hlt|Hgt]|Heq]; subst.
      * solve_ss_ne True z0 z1.
      * solve_ss_ne False z0 z1.
      * exists (MrgIf s0 c (Single v) (Single v0)). repeat eexists;
        try econstructor; eauto.
        find_eq_substrategy. eauto.
        econstructor; repeat eexists; eauto.
    + inversion H1; invc_existT.
      conds_for_single ind sub0 v.
      assert (AllInUnion (fun x : T => P x /\ ind x = Some z) (If c0 t0 f0)) by auto.
      clear_all_ps_sorted_inv_res.
      destruct (Z_dec z0 z) as [[Hlt|Hgt]|Heq]; subst.
      * solve_ss_ne True z0 z.
      * solve_ss_ne False z0 z.
      * exists (MrgIf s0 c (Single v) (If c0 t0 f0)).
        exists n.
        repeat eexists; firstorder; try econstructor; eauto; try solve_aiu.
        assert (exists P1, HieraricalMergingInv P1 s0 (If c0 t0 f0)) as [? ?] by eauto.
        eauto.
        econstructor; repeat eexists; eauto.
    + inversion H2; invc_existT.
      conds_for_single ind sub0 v.
      assert (AllInUnion (fun x : T => P x /\ ind x = Some z) (If c0 t0 f0)) by auto.
      clear_all_ps_sorted_inv_res.
      destruct (Z_dec z z0) as [[Hlt|Hgt]|Heq]; subst.
      * solve_ss_ne True z z0.
      * solve_ss_ne False z z0.
      * exists (MrgIf s0 c (If c0 t0 f0) (Single v)).
        exists n.
        repeat eexists; firstorder; try econstructor; eauto; try solve_aiu.
        assert (exists P1, HieraricalMergingInv P1 s0 (If c0 t0 f0)) as [? ?] by eauto.
        eauto.
        econstructor; repeat eexists; eauto.
    + assert (AllInUnion (fun x : T => P x /\ ind x = Some z) (If c0 t0 f0)) by auto.
      assert (AllInUnion (fun x : T => P x /\ ind x = Some z0) (If c1 t1 f1)) by auto.
      destruct (Z_dec z z0) as [[Hlt|Hgt]|Heq]; subst.
      * solve_ss_ne True z z0.
      * solve_ss_ne False z z0.
      * exists (MrgIf s0 c (If c0 t0 f0) (If c1 t1 f1)).
        exists n3.
        repeat eexists; firstorder; try econstructor; eauto; try solve_aiu.
        assert (exists P1, HieraricalMergingInv P1 s0 (If c0 t0 f0)) as [? ?] by eauto.
        eauto.
        specialize (all_in_union_left_most' H15) as [HP HP'].
        econstructor; repeat eexists; eauto.
  - admit.
  - inversion et; inversion ef; repeat invc_existT;
    try congruence; try solve [exfalso;eauto].
    + inversion H1; repeat invc_existT.
      conds_for_single ind sub0 v.
      clear_all_ps_sorted_inv_res.
      exists (SSMrgIf (SortedStrategy n0 ind sub0) c (Single v) (If c0 t0 f0)); repeat eexists;
        [apply SIDeg with (fi := z)| |]; econstructor; eauto; solve_aiu.
    + admit.
    + inversion H2; repeat invc_existT.
      assert (AllInUnion (fun x : T => P x /\ ind x = Some z0) (If c1 t1 f1)) by auto.
      clear_all_ps_sorted_inv_res.
      exists (SSMrgIf (SortedStrategy n0 ind sub0) c (If c0 t0 f0) (If c1 t1 f1)); repeat eexists;
        [apply SIDeg with (fi := z0)| |]; econstructor; eauto; solve_aiu.
    + admit. 
  - admit.
Admitted.


Theorem deterministic : forall {T n} {t t1 t2 : EvalTerms T} {ms : MergingStrategy T n},
  EvalTermsGood ms t ->
  t ==> t1 ->
  t ==> t2 -> t1 = t2.
Proof.
  intros.
  invc H.
  - invc H1.
  - invc H1; invc H0; repeat invc_existT; eauto; try congruence.
    all: simpl in *; try solve [eauto; exfalso; eauto];
    try match goal with
    | [H : IsSingle ?u, H1 : IsIf ?u |- _] => destruct u; simpl in *; exfalso; eauto
    end. admit.
  - invc H1; invc H0; repeat invc_existT; eauto; try congruence.
    all: simpl in *; try solve [eauto; exfalso; eauto].
    Check all_in_union_ind_eq'.
    all: repeat match goal with
    | [H1 : AllInUnion (fun x => ?ind x = Some ?t1) ?t,
       H2 : AllInUnion (fun x => ?ind x = Some ?t2) ?t |- _] =>
       specialize (all_in_union_ind_eq' H1 H2); intros; subst;
       clear H1; clear H2
    end; try lia.
    rewrite H18 in H14. inversion H14; subst. invc_existT. eauto.
  - admit.
  - admit.
  - admit.
Admitted.

Hint Resolve deterministic.

Theorem deterministic_strong1 : forall {T n} {t t1 t2 : EvalTerms T} {ms : MergingStrategy T n},
  EvalTermsGood ms t ->
  t ==> t1 ->
  t ==>* t2 ->
  t2 ==> t1 \/ t1 ==>* t2.
Proof.
  intros.
  induction H1; eauto.
  inversion H2; subst.
  - assert (z = t1) by eauto. subst. eauto.
  - assert (y = t1) by eauto. subst. eauto.
Qed.

Hint Resolve deterministic_strong1.


Theorem good_evals_to_good : forall {T n} {t t1 : EvalTerms T} {ms : MergingStrategy T n},
  EvalTermsGood ms t -> t ==> t1 -> exists n1 (ms1 : MergingStrategy T n1), EvalTermsGood ms1 t1.
Proof.
  intros.
  specialize (progress H). firstorder; subst.
  - inversion H0. 
  - specialize (deterministic H H0 H1). intros. subst. eauto.
Qed.

Hint Resolve good_evals_to_good.

Theorem good_always_evals_to_good : forall {T n} {t t1 : EvalTerms T} {ms : MergingStrategy T n},
  EvalTermsGood ms t -> t ==>* t1 -> exists n1 (ms1 : MergingStrategy T n1), EvalTermsGood ms1 t1.
Proof.
  intros.
  generalize dependent ms.
  generalize dependent n.
  induction H0; intros; eauto.
  specialize (good_evals_to_good H1 H) as [n1 [ms1 PEy]].
  specialize (IHclos_refl_trans_1n _ ms1). auto.
Qed.

Hint Resolve good_always_evals_to_good.


Print clos_refl_trans_1n.

Inductive NumOfStep {T} : forall {t0 t1 : EvalTerms T} (e : t0 ==>* t1), nat -> Prop :=
  | NOSRefl : forall t, NumOfStep (rt1n_refl _ _ t) 0
  | NOSTrans : forall t1 t2 t3 n23 (step: t1 ==> t2) (res : t2 ==>* t3), NumOfStep res n23 ->
      NumOfStep (Relation_Operators.rt1n_trans (EvalTerms T) EvalRule t1 t2 t3 step res) (S n23).

Theorem metric_is_max_eval_step : forall {T n} {t : EvalTerms T} {ms : MergingStrategy T n},
  EvalTermsGood ms t ->
  forall n nsms (sms : MergingStrategy T nsms) tt, t ==>*(n) EvalValue sms tt -> n <= metric t.
Proof.
  intros.
  generalize dependent n.
  induction H0; intros; subst; simpl; try lia.
  - inversion H0; simpl; try lia.
    subst. inversion H. 
  - specialize (progress H1) as [Hp|Hp]; [destruct Hp as [? Hp] | destruct Hp as [? [? [? Hp]]]]; subst.
    + invc H.
    + intuition.
      specialize (deterministic H1 H H2). intros. subst.
      specialize (IHEvalChain _ _ H4).
      assert (metric x0 < metric x) by eauto.
      lia.
Qed.

Theorem metric_is_max_eval_step' : forall {T n} {t : EvalTerms T} {ms : MergingStrategy T n},
  EvalTermsGood ms t ->
  forall n nsms (sms : MergingStrategy T nsms) tt
  (eval : t ==>* EvalValue sms tt),
  NumOfStep eval n -> n <= metric t.
Proof.
  intros.
  generalize dependent n.
  induction H0; intros; subst; simpl; try lia.
  specialize (progress H) as [Hp|Hp]; [destruct Hp as [? Hp] | destruct Hp as [? [? [? Hp]]]]; subst.
  - invc step.
  - destruct Hp.
    specialize (deterministic H step H1). intros. subst. intuition.
    assert (n23 <= metric x) by eauto.
    assert (metric x < metric t1) by eauto.
    lia.
Qed.

Theorem metric_is_max_eval_step'' : forall {T n} {t t1 : EvalTerms T} {ms : MergingStrategy T n},
  EvalTermsGood ms t ->
  forall nstep
  (eval : t ==>* t1),
  NumOfStep eval nstep -> nstep <= metric t.
Proof.
  intros.
  generalize dependent n.
  induction H0; intros; subst; simpl; try lia.
  specialize (progress H) as [Hp|Hp]; [destruct Hp as [? Hp] | destruct Hp as [? [? [? Hp]]]]; subst.
  - invc step.
  - destruct Hp.
    specialize (deterministic H step H1). intros. subst. intuition.
    assert (n23 <= metric x) by eauto.
    assert (metric x < metric t1) by eauto.
    lia.
Qed.

Print EvalTerms_ind.


Ltac inv_eval_evalvalue :=
  repeat match goal with
  | [ H : EvalValue _ _ ==>* _ |- _ ] => invc H
  | [ H : EvalValue _ _ ==> _ |- _ ] => invc H
  end.

Theorem deterministic_strong : forall {T n} {t t1 t2 : EvalTerms T} {ms : MergingStrategy T n},
  EvalTermsGood ms t ->
  t ==>* t1 ->
  t ==>* t2 ->
  t1 ==>* t2 \/ t2 ==>* t1.
Proof.
  intros.
  generalize dependent t2.
  generalize dependent t1.

  Ltac find_all_union_bad_i :=
    repeat match goal with
    | [H1 : AllInUnion (fun x => ?idx x = Some ?i) ?u,
       H2 : AllInUnion (fun x => ?idx x = Some ?j) ?u,
       H3 : AllInUnion (fun x => ?idx x = Some ?k) ?u,
       H4 : AllInUnion (fun x => ?idx x = Some ?l) ?u |- _] => fail
    | [H1 : AllInUnion (fun x => ?idx x = Some ?i) ?u,
       H2 : AllInUnion (fun x => ?idx x = Some ?j) ?u,
       H3 : AllInUnion (fun x => ?idx x = Some ?k) ?u |- _] =>
       assert (i = j) by eauto;
       assert (j = k) by eauto;
       clear H1; clear H2; clear H3
    | [H1 : AllInUnion (fun x => ?idx x = Some ?i) ?u,
       H2 : AllInUnion (fun x => ?idx x = Some ?j) ?u |- _] =>
       assert (i = j) by eauto;
       clear H1; clear H2
    end.

  apply EvalTerms_ind' with (t := t); intros; try inv_eval_evalvalue; eauto.
  Ltac invc_star :=
    repeat match goal with
    | [ H : MrgIf ?s ?c ?t ?f ==>* _, H1 : MrgIf ?s ?c ?t ?f ==>* _ |- _ ] => invc H; invc H1; subst; repeat invc_existT; eauto
    | [ H : SSMrgIf ?s ?c ?t ?f ==>* _, H1 : SSMrgIf ?s ?c ?t ?f ==>* _ |- _ ] => invc H; invc H1; subst; repeat invc_existT; eauto
    | [ H : SIMrgIf ?s ?c ?t ?f ==>* _, H1 : SIMrgIf ?s ?c ?t ?f ==>* _ |- _ ] => invc H; invc H1; subst; repeat invc_existT; eauto
    | [ H : ISMrgIf ?s ?c ?t ?f ==>* _, H1 : ISMrgIf ?s ?c ?t ?f ==>* _ |- _ ] => invc H; invc H1; subst; repeat invc_existT; eauto
    | [ H : IIMrgIf ?s ?c ?t ?f ==>* _, H1 : IIMrgIf ?s ?c ?t ?f ==>* _ |- _ ] => invc H; invc H1; subst; repeat invc_existT; eauto
    end.
  Ltac invc_eval :=
    repeat match goal with
    | [ H : MrgIf ?s ?c ?t ?f ==> _, H1 : MrgIf ?s ?c ?t ?f ==> _ |- _ ] => invc H; invc H1; subst; repeat invc_existT; eauto
    | [ H : SSMrgIf ?s ?c ?t ?f ==> _, H1 : SSMrgIf ?s ?c ?t ?f ==> _ |- _ ] => invc H; invc H1; subst; repeat invc_existT; eauto
    | [ H : SIMrgIf ?s ?c ?t ?f ==> _, H1 : SIMrgIf ?s ?c ?t ?f ==> _ |- _ ] => invc H; invc H1; subst; repeat invc_existT; eauto
    | [ H : ISMrgIf ?s ?c ?t ?f ==> _, H1 : ISMrgIf ?s ?c ?t ?f ==> _ |- _ ] => invc H; invc H1; subst; repeat invc_existT; eauto
    | [ H : IIMrgIf ?s ?c ?t ?f ==> _, H1 : IIMrgIf ?s ?c ?t ?f ==> _ |- _ ] => invc H; invc H1; subst; repeat invc_existT; eauto
    end.
  1-10: invc_star; invc_eval; try inv_eval_evalvalue; crush; try solve [find_all_union_bad_i; lia].
  - rewrite H13 in H12. invc H12. auto.
  - find_all_union_bad_i. subst. rewrite H18 in H22. invc_hm H22. rewrite H2 in H18. invc_hm H18. eauto.
  - admit.
  - admit.
Admitted.

Hint Resolve deterministic_strong.

Theorem evals_trans : forall {T} {t1 t2 t3 : EvalTerms T},
  t1 ==>* t2 -> t2 ==>* t3 -> t1 ==>* t3.
Proof.
  intros.
  induction H; eauto.
Qed.

Hint Resolve evals_trans.

Definition joinable {T} (t1 t2 : EvalTerms T) : Prop :=
  exists t', t1 ==>* t' /\ t2 ==>* t'.

Hint Unfold joinable.

Theorem joinable_refl : forall {T} {t : EvalTerms T},
  joinable t t.
Proof.
  eauto.
Qed.

Hint Resolve joinable_refl.

Theorem good_terms_joinable_trans : forall {T n1 n2 n3} {t1 t2 t3 : EvalTerms T}
  {ms1 : MergingStrategy T n1}
  {ms2 : MergingStrategy T n2}
  {ms3 : MergingStrategy T n3},
  EvalTermsGood ms1 t1 ->
  EvalTermsGood ms2 t2 ->
  EvalTermsGood ms3 t3 ->
  joinable t1 t2 -> joinable t2 t3 -> joinable t1 t3.
Proof.
  intros.
  induction H2; intros; unfold joinable in *; intuition.
  destruct H3.
  intuition.
  specialize (deterministic_strong H0 H5 H3).
  intuition.
  - exists x0. intuition. inversion H4; subst; eauto.
  - exists x. intuition. inversion H6; subst; eauto.
Qed.

Hint Resolve good_terms_joinable_trans.

Theorem confluent_base : forall {T n1} {t t1 t2 : EvalTerms T}
  {ms1 : MergingStrategy T n1},
  EvalTermsGood ms1 t ->
  t ==> t1 ->
  t ==>* t2 ->
  joinable t1 t2.
Proof.
  intros.
  generalize dependent t1.
  induction H1; intros; eauto.
  - assert (t1 = y) by eauto. subst. eauto.
Qed.

Hint Resolve confluent_base.

Theorem confluent : forall {T n1} {t t1 t2 : EvalTerms T}
  {ms1 : MergingStrategy T n1},
  EvalTermsGood ms1 t ->
  t ==>* t1 ->
  t ==>* t2 ->
  joinable t1 t2.
Proof.
  intros. unfold joinable.
  induction H0; subst; eauto.
  induction H1.
  - exists z. eauto.
  - assert (y = y0) by eauto. subst.
    assert (z ==>* z0 \/ z0 ==>* z) as [Hz|Hz] by eauto;
    eexists; eauto.
Qed.


Theorem mmm : forall {T} {t : EvalTerms T} {n} {ms : MergingStrategy T n},
  EvalTermsGood ms t ->
  exists P n1 (ms1 : MergingStrategy T n1) u, t ==>* (EvalValue ms1 u) /\ HieraricalMergingInv P ms u.
Proof.
  intros.
  generalize dependent ms.
  Check EvalTerms_ind'.
  apply EvalTerms_ind' with (t := t); intros.
  - inversion H0; subst; invc_existT.
    repeat eexists; eauto.
  - destruct b; inversion H2; subst; invc_existT;
    repeat eexists; eauto.
  - inversion H2; subst; repeat invc_existT.
    exists P; repeat eexists; eauto.
    inversion H3; subst; invc_existT; eauto.
    invc H7.
    invc H9.
    inversion H11;
    subst; repeat invc_existT.
    specialize (H9 c _ _ H12 H15) as [r1 [H9 H9']].
    rewrite H0 in H9; invc H9.
    constructor; eauto.
  - admit.
  - admit.
  
  eauto; intros.
  (*
  3-6: destruct H2 as [n0 [ms0 [u0 H2]]];
       exists n0; exists ms0; exists u0;
       econstructor; eauto.
       *)
  - repeat eexists.
    econstructor; eauto.
    econstructor; eauto.
  - admit.


  - destruct b; repeat eexists; eauto.
  - destruct H2 as [? [? [? H2]]].
    invc H2; subst; try invc_existT.
    + repeat eexists; econstructor; eauto.
    + invc H3.
  - repeat eexists; econstructor; eauto.
  - destruct H3 as [? [? [? ?]]]. repeat eexists. econstructor; eauto.
  - repeat eexists; econstructor; eauto.

