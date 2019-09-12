Require Export List Omega.
Import ListNotations.
From icl Require Import util.

(** * Assignments. *)

Inductive variable := V: nat -> variable.

Definition variables := list variable.

Definition assignment := list (variable * bool).

Definition assignments := list assignment.

Definition vars_in (α : assignment): variables :=
  map fst α.

Reserved Notation "v / α ↦ b" (at level 10).
Inductive mapsto: variable -> assignment -> bool -> Prop := 
| mapsto_hd: forall v α_tl b,
    v/((v, b) :: α_tl) ↦ b
| mapstox_tl: forall v1 v2 α b1 b2,
    v1 <> v2 -> (v1 / α ↦ b1) -> (v1 / ((v2, b2) :: α) ↦ b1)
where "v / α ↦ b" := (mapsto v α b).

Hint Constructors mapsto.

Definition equiv_assignments (vs : variables) (α1 α2 : assignment) :=
  forall (v : variable),
    v el vs ->
    forall b, v / α1 ↦ b <-> v / α2 ↦ b.

(** * Lemmas *)
Section Lemmas. 

  Section PropertiesOfAssignments.

    Global Instance variable_eq_dec:
      eq_dec variable.
    Proof.
      intros v1 v2.
      destruct v1 as [n], v2 as [m].
      decide (n = m).
      - left; rewrite e; reflexivity.
      - right; intros C; apply n0; inversion C; reflexivity.
    Defined.

    Global Instance assignment_eq_dec:
      eq_dec assignment.
    Proof.
      apply list_eq_dec.
      intros [v1 [ | ]] [v2 [ | ]]; destruct (variable_eq_dec v1 v2).
      all: try(subst; left; auto; fail).
      all: try(right; intros EQ; inversion EQ; subst; auto; fail).
    Qed.

    Lemma mapsto_injective:
      forall (α : assignment) (v : variable) (b1 b2 : bool),
        v / α ↦ b1 ->
        v / α ↦ b2 ->
        b1 = b2.
    Proof.
      intros ? ? ? ? M1 M2.
      induction α.
      - inversion M1.
      - destruct a.
        decide (v = v0); [subst | ].
        + inversion M1; subst; [ | exfalso; auto].
          inversion M2; subst; [reflexivity | exfalso; auto].
        + inversion M1; subst; [exfalso; auto | ].
          inversion M2; subst; [exfalso; auto | ].
          apply IHα; auto.
    Qed.

    Corollary mapsto_injective_contr:
      forall (α : assignment) (v : variable),
        v / α ↦ false -> 
        v / α ↦ true ->
        False.
    Proof.
      intros ? ? EV1 EV2; assert (F := mapsto_injective _ _ _ _ EV1 EV2); easy.
    Qed.
    
    Lemma mapsto_dec:
      forall (α : assignment) (v : variable),
        v el vars_in α ->
        {v / α ↦ true} + {v / α ↦ false}. 
    Proof.
      induction α; intros v1 ?. 
      { inversion_clear H. }
      { destruct a as [v2 b].
        decide (v1 = v2); [subst | ].
        { destruct b; [left|right]; constructor. } 
        { specialize (IHα v1).
          feed IHα.
          inversion_clear H; [exfalso; eauto | destruct α; eauto]. 
          destruct IHα as [IH1|IH2]; [left|right]; constructor; auto.
        } 
      }
    Defined.

    Lemma nel_mapsto:
      forall (α : assignment) (v : variable) (b : bool),
        v nel vars_in α ->
        ~ v / α ↦ b.
    Proof.
      intros ? ? ? NEL MAP.
      apply NEL; clear NEL.
      induction MAP; [left|right]; auto.
    Qed.
    
    Lemma mapsto_total:
      forall (α : assignment) (v : variable),
        {v el vars_in α /\ v / α ↦ true} +
        {v nel vars_in α /\ forall b, ~ v / α ↦ b} +
        {v el vars_in α /\ v / α ↦ false}.
    Proof.
      intros.
      decide (v el vars_in α) as [EL|NEL].
      destruct (mapsto_dec _ _ EL).
      - left; left; split; auto.
      - right; split; auto.
      - left; right; split; [auto|intros b EL; eapply nel_mapsto; eauto].
    Qed.

    Lemma equiv_assignments_dec:
      forall (vs : variables) (α β : assignment),
        dec (equiv_assignments vs α β).
    Proof.
      induction vs.
      - intros; left; split; destruct H.
      - intros.
        destruct (mapsto_total α a) as [[[EL1 EV1]|[EL1 EV1]]|[EL1 EV1]];
          destruct (mapsto_total β a) as [[[EL2 EV2]|[EL2 EV2]]|[EL2 EV2]].
        all: specialize (IHvs α β); destruct IHvs as [IH|IH].
        all: try(right; intros EQU; apply IH; clear IH;
                 intros ? EL ?; apply EQU; right; auto; fail).
        all: try(left; intros v [EQ|EL] [ | ]; subst;
                 [ split; intros; auto
                 | split; intros; exfalso; eauto using mapsto_injective_contr
                 | apply IH; auto
                 | apply IH; auto]; fail).
        right; intros EQU; apply (EV2 true); apply EQU; [left| ]; auto.
        right; intros EQU; specialize (EQU a (or_introl eq_refl) true);
          apply proj1 in EQU; apply EQU in EV1; eauto using mapsto_injective_contr.
        right; intros EQU; apply (EV1 true); apply EQU; [left| ]; auto.
        left; intros ? [EQ|EL]; subst; split; intros EV;
          try((apply EV1 in EV || apply EV2 in EV); destruct EV);
          try(apply IH; auto).
        right; intros EQU; apply (EV1 false); apply EQU; [left| ]; auto.
        right; intros EQU; specialize (EQU a (or_introl eq_refl) false);
          apply proj1 in EQU; apply EQU in EV1; eauto using mapsto_injective_contr.
        right; intros EQU; apply (EV2 false); apply EQU; [left| ]; auto.
        left; intros v [EQ|EL] [ | ]; subst;
          try(split; intros; auto; fail);
          try(split; intros; exfalso; eauto using mapsto_injective_contr; fail);
          try(apply IH; auto; fail).
    Qed.
    
  End PropertiesOfAssignments.
  
  (** Properties of Equivalence. *)
  Section PropertiesOfEquivalence.

    Section EquivalenceRelation.

      Lemma equiv_assignments_refl:
        forall (vs : variables) (α : assignment),
          equiv_assignments vs α α.
      Proof.
        intros ? ? ? EL ?; split; intros EV; assumption.
      Qed.
      
      Lemma equiv_assignments_sym:
        forall (vs : variables) (α β : assignment),
          equiv_assignments vs α β ->
          equiv_assignments vs β α.
      Proof.
        intros ? ? ? EQU ? EL ?; split; intros EV; apply EQU; auto.
      Qed.
      
      Lemma equiv_assignments_trans:
        forall (vs : variables) (α β γ : assignment),
          equiv_assignments vs α β ->
          equiv_assignments vs β γ ->
          equiv_assignments vs α γ.
      Proof.
        intros ? ? ? ? EQU1 EQU2 ? EL ?; split; intros EV;
          [apply EQU2|apply EQU1]; auto; [apply EQU1|apply EQU2]; auto.
      Qed.
      
    End EquivalenceRelation.

    Lemma equiv_assignments_nodup:
      forall (vs : variables) (α β : assignment),
        equiv_assignments vs α β <->
        equiv_assignments (nodup variable_eq_dec vs) α β.
    Proof.
      intros vs α β; split; intros EQ v EL.
      - specialize (EQ v); feed EQ; apply nodup_In in EL; auto.
      - specialize (EQ v); feed EQ; auto. apply nodup_In; eauto.
    Qed.

    Lemma equiv_assignments_narrow_vars:
      forall (vs vs_sub : variables) (α1 α2 : assignment),
        vs_sub ⊆ vs ->
        equiv_assignments vs α1 α2 -> 
        equiv_assignments vs_sub α1 α2.
    Proof.
      intros ϕ x β1 β2 NEQ EQU v EL b.
      specialize (NEQ v EL).
      specialize (EQU _ NEQ b).
      destruct EQU as [EV1 EV2].
      split; auto.
    Qed.

    Lemma equiv_assignments_cancel_cons:
      forall (α1 α2 : assignment) (vs : list variable) (a : variable) (b : bool),
        a nel vs ->
        equiv_assignments (a :: vs) ((a, b) :: α1) ((a, b) :: α2) ->
        equiv_assignments vs α1 α2.
    Proof.
      intros α1 α2 ? ? ? NEL EQU v EL ?.
      decide (v = a) as [EQ|NEQ]; subst; split; intros EV.
      1-2: exfalso; auto. 
      1: specialize (EQU v (or_intror EL) b0); destruct EQU as [EQU _].
      2: specialize (EQU v (or_intror EL) b0); destruct EQU as [_ EQU ].
      all: feed EQU; [right;auto| ].
      all: inversion EQU; subst; [exfalso | ]; auto.
    Qed.

    Lemma equiv_assignments_cancel_subset:
      forall (vs vs_sub : variables) (v : variable) (b : bool) (α1 α2 : assignment),
        vs_sub ⊆ vs ->
        v nel vs_sub ->
        equiv_assignments vs ((v, b) :: α1) ((v, b) :: α2) ->
        equiv_assignments vs_sub α1 α2.
    Proof.
      intros ? ? v ? ? ? INCL NEL EQU x EL b.
      decide (x = v) as [EQ|NEQ]; [subst;exfalso;auto| ]; split; intros EV;
        specialize (INCL _ EL); specialize (EQU _ INCL b);
          [destruct EQU as [EQU _] | destruct EQU as [_ EQU]].
      all: feed EQU; auto; inversion EQU; subst; [exfalso | ]; auto.
    Qed.

    Lemma non_equiv_assignments:
      forall (α1 α2 : assignment) (vs : variables) (a : variable) (b : bool),
        ~ equiv_assignments (a :: vs) ((a, b) :: α1) ((a, negb b) :: α2).
    Proof.
      intros ? ? ? ? ? EQ.
      specialize (EQ a); feed EQ; [left; auto | ].
      specialize (EQ b); destruct EQ as [EQU _].
      destruct b; feed EQU; auto; inversion_clear EQU; auto.
    Qed.
   
  End PropertiesOfEquivalence.

End Lemmas.
