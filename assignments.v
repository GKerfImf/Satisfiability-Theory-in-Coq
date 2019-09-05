Require Export List Omega.
Import ListNotations.
From icl Require Import util.

(** * Assignments. *)

(* TODO: comment *)
Inductive variable := V: nat -> variable.

(* *)
Definition variables := list variable.

(* TODO: comment *)
(* Basically, here we have a choice (?) 
   We can introduce a strong type for assignments, in this case equality will be easy to decide, 
   Or we can have weak structure here, but then we'll get a lot of "different" assignments, 
   which has to be equivalent. 
   
   I decided to use some relatively weak structure. 

   My plan is to introduce a notion of "equivalence" and use it everywhere instead of equality. 

*)
(* List be cause I want the whole thing to be computable *)
Definition assignment := list (variable * bool).


Definition assignments := list assignment.

(* Variables are important.   
   Maybe it's a bad deifintion, but consider a formula 
         x1 ∨ x2 ∨ T.
   How many sat as. are there? 
   My answer would be  "On which variables?" 
    That is, assignments [x1 ↦ F] [x1 ↦ T, x3 ↦ T] 
    are both sat. ass. even though the first one 
    doesn't set variable x2, and the second sets 
    a variable x3.
 *)


(* I don't like "map" here. *)
(* TODO: comment *)
Fixpoint vars_in (α: assignment): variables :=
  match α with
  | [] => []
  | (v,b)::tl => v :: vars_in tl
  end.

(* TODO: comment *)
Reserved Notation "v / α ↦ b" (at level 10).

(* TODO: fix naming *)
Inductive mapsto: variable -> assignment -> bool -> Prop := 
| maps_hd: forall var α_tl b,
    var/((var, b) :: α_tl) ↦ b
| maps_tl: forall var var' c α b,
    var <> var' -> (var/α ↦ b) -> (var/((var',c)::α) ↦ b)
where "v / α ↦ b" := (mapsto v α b).

Hint Constructors mapsto.


(* TODO: comment *)
Definition equiv_assignments (vs : variables) (α1 α2 : assignment) :=
  forall (v : variable),
    v el vs ->
    forall b, v / α1 ↦ b <-> v / α2 ↦ b.

(** * Lemmas *)
Section Lemmas. 

  Section PropertiesOfAssignments.
    
    (* TODO: comment *)
    Global Instance eq_var_dec:
      eq_dec variable.
    Proof.
      intros v1 v2.
      destruct v1 as [n], v2 as [m].
      decide (n = m).
      - left; rewrite e; reflexivity.
      - right; intros C; apply n0; inversion C; reflexivity.
    Defined. (* Todo: Qed? *)

    (* admit_ *)
    Global Instance eq_assignment_dec :
      eq_dec assignment.
    Proof.
      intros x y.
      
    Admitted.


    Lemma todo2:
      forall (α : assignment) (v : variable) (b1 b2 : bool),
        v / α ↦ b1 ->
        v / α ↦ b2 ->
        b1 = b2.
    Proof.
      intros ? ? ? ? M1 M2.
      induction α.
      { inversion M1. }
      { destruct a.
        decide (v = v0); [subst | ].
        { inversion M1; subst; [ | exfalso; auto].
          inversion M2; subst; [reflexivity | exfalso; auto].
        }
        { inversion M1; subst; [exfalso; auto | ].
          inversion M2; subst; [exfalso; auto | ].
          apply IHα; auto.
        }
      }
    Qed.

    Corollary todo46:
      forall (α : assignment) (v : variable),
        v / α ↦ false -> 
        v / α ↦ true ->
        False.
    Proof.
      intros ? ? EV1 EV2; assert (F := todo2 _ _ _ _ EV1 EV2); easy.
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

    Lemma todo21:
      forall (α : assignment) (v : variable) (b : bool),
        v nel vars_in α ->
        ~ v / α ↦ b.
    Proof.
      intros ? ? ? NEL MAP.
      apply NEL; clear NEL.
      induction MAP.
      { left; reflexivity. }
      { right; assumption. }
    Qed.


    Lemma todo22:
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
      - left; right; split; [auto|intros b EL; eapply todo21; eauto].
    Qed.

  End PropertiesOfAssignments.


  (** Properties of Equivalence. *)
  (* TODO *)
  Section PropertiesOfEquivalence.

    Section EquivalenceRelation.

      Lemma equiv_assignments_refl :
        forall (vs : variables) (α : assignment),
          equiv_assignments vs α α.
      Proof.
        intros ? ? ? EL ?; split; intros EV; assumption.
      Qed.
      
      Lemma equiv_assignments_sym :
        forall (vs : variables) (α β : assignment),
          equiv_assignments vs α β ->
          equiv_assignments vs β α.
      Proof.
        intros ? ? ? EQU ? EL ?; split; intros EV; apply EQU; auto.
      Qed.
      
      Lemma equiv_assignments_trans :
        forall (vs : variables) (α β γ : assignment),
          equiv_assignments vs α β ->
          equiv_assignments vs β γ ->
          equiv_assignments vs α γ.
      Proof.
        intros ? ? ? ? EQU1 EQU2 ? EL ?; split; intros EV;
          [apply EQU2|apply EQU1]; auto; [apply EQU1|apply EQU2]; auto.
      Qed.
      
    End EquivalenceRelation.

    (* 333 *)
    Lemma todo28:
      forall (vs vs_sub : variables) (v : variable) (b : bool) (α1 α2 : assignment),
        incl vs_sub vs ->
        v nel vs_sub ->
        equiv_assignments vs ((v,b)::α1) ((v,b)::α2) ->
        equiv_assignments vs_sub α1 α2.
    Proof.
      intros ? ? v ? ? ? INCL NEL EQU x EL b.
      decide (x = v) as [EQ|NEQ]; [subst;exfalso;auto| ]; split; intros EV;
        specialize (INCL _ EL); specialize (EQU _ INCL b);
          [destruct EQU as [EQU _] | destruct EQU as [_ EQU]].
      all: feed EQU; auto; inversion EQU; subst; [exfalso | ]; auto.
    Qed.

    (* 3123 *)
    Lemma todo53:
      forall (α_upd α : assignment) (v : variable) (b : bool),
        v nel vars_in α_upd ->
        v / α ↦ b <-> v / α_upd ++ α ↦ b.
    Proof.
      intros ? ? ? ? NEL.
      induction α_upd; split; intros EV.
      { simpl in EV; assumption. }
      { simpl in EV; assumption. }
      { destruct a as [vu bu]; simpl; constructor.
        { intros EQ; subst vu; apply NEL; left; reflexivity. }
        { apply IHα_upd; auto.
          intros EL; apply NEL; clear NEL; right; assumption. }
      } 
      { destruct a as [vu bu].
        assert(NEQ:= nel_cons_neq _ _ _ NEL).
        simpl in EV; inversion EV; subst; [exfalso;auto| ].
        clear EV H4; rename H5 into EV.
        specialize (IHα_upd (nel_cons _ _ _ NEL)); destruct IHα_upd as [_ IH];
          specialize (IH EV); auto.
      } 
    Qed.

    (* 123 12 *)
    Lemma equiv_assign_disj_update:
      forall (vs : variables) (α_upd α1 α2 : assignment),
        disj_sets vs (vars_in α_upd) ->
        equiv_assignments vs (α_upd ++ α1) (α_upd ++ α2) ->
        equiv_assignments vs α1 α2.
    Proof.
      intros ? ? ? ? DISJ EQU ? EL ?.
      specialize (EQU v EL b).
      destruct EQU as [EQU1 EQU2].    
      specialize (DISJ v); destruct DISJ as [DISJ _]; specialize (DISJ EL).
      split; intros EV. 
      - eapply todo53; eauto.
        apply EQU1.
        apply todo53; auto.
      - eapply todo53; eauto.
        apply EQU2.
        apply todo53; auto.
    Qed.      

    (* 13 *)
    Lemma equiv_nodup:
      forall (vs : variables) (α β : assignment),
        equiv_assignments vs α β <->
        equiv_assignments (nodup eq_var_dec vs) α β.
    Proof.
      intros vs α β; split; intros EQ v EL.
      - specialize (EQ v); feed EQ; apply nodup_In in EL; auto.
      - specialize (EQ v); feed EQ; auto. apply nodup_In; eauto.
    Qed.
    
    (* 123 *)
    Lemma todo27:
      forall (vs vs_sub : variables) (α1 α2 : assignment),
        incl vs_sub vs ->
        equiv_assignments vs α1 α2 -> 
        equiv_assignments vs_sub α1 α2.
    Proof.
      intros ϕ x β1 β2 NEQ EQU v EL b.
      specialize (NEQ v EL).
      specialize (EQU _ NEQ b).
      destruct EQU as [EV1 EV2].
      split; auto.
    Qed.

    (* 123 *)
    Lemma todo41:
      forall (α1 α2 : assignment) (vs : list variable) (a : variable) (b : bool),
        a nel vs ->
        equiv_assignments (a::vs) ((a,b)::α1) ((a,b)::α2) ->
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

    (* 123 *)
    Lemma todo42:
      forall (α1 α2 : assignment) (vs : variables) (a : variable) (b : bool),
        ~ equiv_assignments (a :: vs) ((a, b)::α1) ((a, negb b)::α2).
    Proof.
      intros ? ? ? ? ? EQ.
      specialize (EQ a); feed EQ; [left; auto | ].
      specialize (EQ b); destruct EQ as [EQU _].
      destruct b; feed EQU; auto; inversion_clear EQU; auto.
    Qed.

    Lemma todo107:
      eq_dec assignment.
    Proof.
    Admitted.

    Lemma todo108:
      forall (vs : variables) (α β : assignment),
        dec (equiv_assignments vs α β).
    Proof.
    Admitted.
    
  End PropertiesOfEquivalence.

End Lemmas.