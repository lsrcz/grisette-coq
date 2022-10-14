Require Import Grisette.Eval.
Require Import Grisette.Terminate.
Require Import Grisette.GeneralTactics.
Require Import Grisette.Union.
Require Import Grisette.SymBoolOp.
Require Import Grisette.MergingStrategy.
Require Import Grisette.SubStrategy.
Require Import Grisette.Deterministic.
Require Import Grisette.Invariant.
Require Import Lia.
Require Import Program.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Arith.PeanoNat.
Open Scope Z.
Open Scope nat.

Definition max_step {T} (t : EvalTerms T) : nat :=
  match t with
  | EvalValue _ _ => 0
  | MrgIf ms c t f => 4 + 4 * ms_depth ms * (union_size t + union_size f)
  | SSMrgIf ms c t f => 1 + 4 * ms_depth ms * (union_size t + union_size f)
  | ISMrgIf ms c t f => 2 + 4 * ms_depth ms * (union_size t + union_size f)
  | SIMrgIf ms c t f => 2 + 4 * ms_depth ms * (union_size t + union_size f)
  | IIMrgIf ms c t f => 3 + 4 * ms_depth ms * (union_size t + union_size f)
  end.

Theorem linear': forall {T n t} {ms : MergingStrategy T n} {step1},
  EvalTermsGood ms t ->
  forall {u1},
  t ==>(step1) (EvalValue ms u1) ->
  step1 <= max_step t.
Proof.
  intros.
  assert (good:exists n1 (ms1 : MergingStrategy T n1), EvalTermsGood ms1 t).
  { exists n, ms. assumption. }
  generalize dependent n.
  generalize dependent u1.
  generalize dependent step1.
  apply EvalTerms_ind' with (t := t); intros; subst; eauto.
  all: inversion_initial_eval_good; simpl in *; try solve [exfalso; eauto].
  { invcd H1; try lia. }
  { destruct b;
    invcd H3; simpl in *; try solve [exfalso; auto];
    lia.
  }
  { invcd H4; simpl in *; try solve [exfalso; auto]. 
    lia.
  }
  1-4: invcd H3; simpl in *; try solve [exfalso; auto];
    destruct ms; simpl in *; try solve [exfalso; auto].
  { rewrite Nat.add_1_r; apply le_n_S; apply le_S; apply le_S; rewrite <- (Nat.add_0_r d).
    eapply H1; eauto with eval;
      invcd H2; econstructor; eauto with union. }
  { rewrite Nat.add_1_r; apply le_n_S; apply le_S; rewrite <- (Nat.add_0_r d).
    eapply H1; eauto with eval;
      invcd H2; econstructor; eauto with union. }
  { rewrite Nat.add_1_r; apply le_n_S; apply le_S; rewrite <- (Nat.add_0_r d).
    eapply H1; eauto with eval;
      invcd H2; econstructor; eauto with union. }
  { rewrite Nat.add_1_r; apply le_n_S; rewrite <- (Nat.add_0_r d).
    eapply H1; eauto with eval;
      invcd H2; econstructor; eauto with union. }

  Ltac preprocess :=
    match goal with
    | [ H1 : EvalTermsGood ?ms ?t,
        H2 : ?t ==>(_) EvalValue ?ms ?u1 |- _ ] =>
      invcd H1; invcd H2; try solve_aiu;
      repeat aiu_simplify; repeat find_same
    end.
  Ltac unz_aux v :=
    match v with
    | S ?v' => unz_aux v' 
    | ?v1 + ?v2 => unz_aux v1; unz_aux v2
    | ?v1 * ?v2 => unz_aux v1; unz_aux v2
    | union_size ?u => assert (union_size u > 0) by eauto with union
    | ms_depth (SortedStrategy ?n _ _) => assert (n > 0) by eauto with inv
    | _ => auto
    end.

  Ltac unz :=
    match goal with
    | [ |- _ <= ?t ] => unz_aux t
    end.
  all: preprocess; unz; unfold ms_depth in *; simpl in *; auto 1.

  Ltac try1 :=
    match goal with
    | [ H : forall step1 u1 n ms, (EvalTermsGood ms (?op ?ms1 ?c ?t0 ?ff)) -> ?H2 -> step1 <= _,
        H2 : ?op ?ms1 ?c ?t0 ?ff ==>(?step) EvalValue ?ms1 ?u |- _] =>
      let He := fresh "H" in
      assert (He:EvalTermsGood ms1 (op ms1 c t0 ff)) by (econstructor; eauto with inv union);
      specialize (H step u _ ms1 He); intuition; nia
    end.
  all: try solve [try1].

  { assert (EvalTermsGood s0 (MrgIf s0 c t0 f)).
    { assert (ProperStrategy P (SortedStrategy n ind sub0)) by eauto 2 with inv.
      specialize (all_in_union_left_most' H0); simpl; intros.
      specialize (proper_ms_sub_from_subfunc H12 H13 H2) as [Psub ?].
      assert (HieraricalMergingInv Psub s0 t0) by eauto 2 with subinv.
      assert (HieraricalMergingInv Psub s0 f) by eauto 2 with subinv.
      econstructor; eauto.
    }
    specialize (H3 _ _ _ _ H12 H24).
    nia.
  }

  { assert (EvalTermsGood s0 (MrgIf s0 c t0 ft)).
    { assert (ProperStrategy P (SortedStrategy n ind sub0)) by eauto 2 with inv.
      specialize (all_in_union_left_most' H0); simpl; intros.
      specialize (proper_ms_sub_from_subfunc H15 H20 H4) as [Psub ?].
      assert (HieraricalMergingInv Psub s0 t0) by eauto 2 with subinv.
      assert (HieraricalMergingInv Psub s0 ft) by eauto 3 with subinv inv.
      econstructor; eauto.
    }
    specialize (H5 _ _ _ _ H15 H30).
    nia.
  }

  { assert (EvalTermsGood s0 (MrgIf s0 c tt f)).
    { assert (ProperStrategy P (SortedStrategy n ind sub0)) by eauto 2 with inv.
      specialize (all_in_union_left_most' H0); simpl; intros.
      specialize (proper_ms_sub_from_subfunc H15 H20 H4) as [Psub ?].
      assert (HieraricalMergingInv Psub s0 tt) by eauto 3 with subinv inv.
      assert (HieraricalMergingInv Psub s0 f) by eauto 2 with subinv.
      econstructor; eauto.
    }
    specialize (H5 _ _ _ _ H15 H30).
    unfold ms_depth in *; simpl in *.
    nia.
  }

  { assert (EvalTermsGood (SortedStrategy n ind sub0) (MrgIf (SortedStrategy n ind sub0) c tf ff))
      by (econstructor; eauto 2 with inv).
    specialize (H8 _ _ _ _ H23 H38).
    assert (EvalTermsGood s0 (MrgIf s0 c tt ft)).
    { assert (ProperStrategy P (SortedStrategy n ind sub0)) by eauto 2 with inv.
      specialize (all_in_union_left_most' H0); simpl; intros.
      specialize (proper_ms_sub_from_subfunc H24 H25 H6) as [Psub ?].
      assert (HieraricalMergingInv Psub s0 tt) by eauto 3 with subinv inv.
      assert (HieraricalMergingInv Psub s0 ft) by eauto 3 with subinv inv.
      econstructor; eauto.
    }
    specialize (H7 _ _ _ _ H24 H37).
    nia.
  }
Qed.  
