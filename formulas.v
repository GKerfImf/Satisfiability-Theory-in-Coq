Require Export List Omega.
Import ListNotations.

From icl Require Export util assignments.

(** * Formulas *)

(* TODO: comment *)
Inductive formula :=
| F : formula
| T : formula
| Var : variable -> formula
| Neg : formula -> formula
| Conj : formula -> formula -> formula
| Disj : formula -> formula -> formula.

(* Supplementary notation for formulas. *)
Notation "[| x |]" := (Var x) (at level 0).
Notation "¬ x" := (Neg x) (at level 40). 
Notation "x '∧' y" := (Conj x y) (at level 40, left associativity).
Notation "x '∨' y" := (Disj x y) (at level 41, left associativity).

Definition xor (ϕl ϕr : formula) := ((ϕl ∧ ¬ ϕr) ∨ (¬ ϕl ∧ ϕr)). 
Notation "x '⊕' y" := (xor x y) (at level 41, left associativity).

Definition impl (ϕl ϕr : formula) := ¬ϕl ∧ ϕr. 
Notation "x '⇒' y" := (impl x y) (at level 41, left associativity).

(* As you can see, we have quite weak type for assignment. 
   Therefore, we have a lot of assignments that are equivalent
   TODO
 *)


(* TODO: def *)
(* TODO: comment *)
Reserved Notation "'ℇ' '(' ϕ ')' α ≡ b" (at level 10).

Inductive formula_eval : formula -> assignment -> bool -> Prop :=

| ev_true: forall (α : assignment), ℇ (T) α ≡ true
| ev_false: forall (α : assignment), ℇ (F) α ≡ false
                                  
| ev_var: forall (v : variable) (α : assignment) (b : bool),
    (v/α ↦ b) -> ℇ ([|v|]) α ≡ b
                  
| ev_neg: forall (ϕ : formula) (α : assignment) (b : bool),
    ℇ (ϕ) α ≡ (negb b) -> ℇ (¬ϕ) α ≡ b
                           
| ev_conj_t: forall (ϕl ϕr : formula) (α : assignment),
    ℇ (ϕl) α ≡ true -> ℇ (ϕr) α ≡ true -> ℇ (ϕl ∧ ϕr) α ≡ true
| ev_conj_fl: forall (ϕl ϕr : formula) (α : assignment),
    ℇ (ϕl) α ≡ false -> ℇ (ϕl ∧ ϕr) α ≡ false
| ev_conj_fr: forall (ϕl ϕr : formula) (α : assignment),
    ℇ (ϕr) α ≡ false -> ℇ (ϕl ∧ ϕr) α ≡ false
                         
| ev_disj_f: forall (ϕl ϕr : formula) (α : assignment),
    ℇ (ϕl) α ≡ false -> ℇ (ϕr) α ≡ false -> ℇ (ϕl ∨ ϕr) α ≡ false              
| ev_disj_tl: forall (ϕl ϕr : formula) (α : assignment),
    ℇ (ϕl) α ≡ true -> ℇ (ϕl ∨ ϕr) α ≡ true
| ev_disj_tr: forall (ϕl ϕr : formula) (α : assignment),
    ℇ (ϕr) α ≡ true -> ℇ (ϕl ∨ ϕr) α ≡ true
                        
where "'ℇ' '(' ϕ ')' α ≡ b" := (formula_eval ϕ α b). 

Hint Constructors formula_eval.

(* *)
Definition sat_assignment (ϕ : formula) (α : assignment) :=
  formula_eval ϕ α true.

Definition unsat_assignment (ϕ : formula) (α : assignment) :=
  formula_eval ϕ α false.



Reserved Notation "ϕ [ x ↦ ψ ]" (at level 10).

Fixpoint substitute (ϕ : formula) (v : variable) (ψ : formula): formula :=
  match ϕ with
  | T => T
  | F => F
  | [| v0 |] => if decision (v = v0) then ψ else Var v0
  | ¬ ϕn => ¬ ϕn[v ↦ ψ]
  | ϕl ∧ ϕr => ϕl[v ↦ ψ] ∧ ϕr[v ↦ ψ]
  | ϕl ∨ ϕr => ϕl[v ↦ ψ] ∨ ϕr[v ↦ ψ]
  end
where "ϕ [ x ↦ f ]" := (substitute ϕ x f).

(* Simpl? *)

(* TODO: *)
Fixpoint leaves (ϕ : formula): variables :=
  match ϕ with
  | T | F => []
  | Var v => [v]
  | ¬ ϕ => leaves ϕ
  | ϕ1 ∧ ϕ2 => leaves ϕ1 ++ leaves ϕ2
  | ϕ1 ∨ ϕ2 => leaves ϕ1 ++ leaves ϕ2
  end.

(* => [V 0; V 1; V 0; V 1] *)
(* Compute (leaves ([|V 0|] ⊕ [|V 1|])). *)


(* Definition of the size of a formula. *)
Definition formula_size (ϕ: formula): nat :=
  length (leaves ϕ).


(* => 4 *)
(* Compute (formula_size ([|V 0|] ⊕ [|V 1|])). *)

(* TODO: comment *)
Fixpoint number_of_nodes (ϕ: formula): nat :=
  match ϕ with
  | T | F | Var _ => 1
  | ¬ ϕ => 1 + number_of_nodes ϕ
  | ϕl ∨ ϕr => 1 + number_of_nodes ϕl + number_of_nodes ϕr
  | ϕl ∧ ϕr => 1 + number_of_nodes ϕl + number_of_nodes ϕr
  end.

(** * Lemmas *) 
Section Lemmas.
  
  Lemma formula_eval_inj:
    forall (ϕ : formula) (α : assignment) (b1 b2 : bool),
      ℇ (ϕ) α ≡ b1 ->
      ℇ (ϕ) α ≡ b2 ->
      b1 = b2.
  Proof.
    induction ϕ; intros ? ? ? EV1 EV2.
    all: inversion_clear EV1; inversion_clear EV2;
      auto 2; eauto 2 using todo2; destruct b1, b2; eauto.
  Qed.

  Lemma equiv_sat:
    forall (ϕ : formula) (α : assignment) (β : assignment),
      equiv_assignments (leaves ϕ) α β ->
      forall (b : bool), 
        ℇ (ϕ) α ≡ b ->
        ℇ (ϕ) β ≡ b.
  Proof.
    intros ?; induction ϕ; intros ? ? EQ b EV.
    - inversion_clear EV; constructor.
    - inversion_clear EV; constructor.
    - inversion_clear EV.
      constructor; apply EQ; [left | ]; auto.
    - apply IHϕ with (b := negb b) in EQ.
      + constructor; assumption.
      + inversion_clear EV; assumption.
    - specialize (IHϕ1 α β); feed IHϕ1. 
      { eapply todo27; eauto; intros x IN; simpl; apply in_app_iff; left; auto. } 
      specialize (IHϕ2 α β); feed IHϕ2. 
      { eapply todo27; eauto; intros x IN; simpl; apply in_app_iff; right; auto. } 
      inversion_clear EV.
      + constructor; eauto.
      + apply ev_conj_fl; eauto.
      + apply ev_conj_fr; eauto.
    - specialize (IHϕ1 α β); feed IHϕ1. 
      { eapply todo27; eauto; intros x IN; simpl; apply in_app_iff; left; auto. } 
      specialize (IHϕ2 α β); feed IHϕ2. 
      { eapply todo27; eauto; intros x IN; simpl; apply in_app_iff; right; auto. } 
      inversion_clear EV.
      + constructor; eauto.
      + apply ev_disj_tl; eauto.
      + apply ev_disj_tr; eauto.
  Qed.

  Lemma todo13:
    forall (ϕ : formula) (α : assignment) (v : variable) (b a : bool),
      v nel leaves ϕ ->
      ℇ (ϕ) α ≡ b <-> ℇ (ϕ) (v,a)::α ≡ b.
  Proof.
    intros ? ? ? ? ? NEL; split; intros EV;
      generalize dependent a; generalize dependent b;
        generalize dependent v; generalize dependent α.
    { induction ϕ; intros.
      - inversion_clear EV. constructor.
      - inversion_clear EV. constructor.
      - constructor. constructor. intros EQ. subst.
        inversion_clear EV.
        apply NEL. left. reflexivity.
        inversion_clear EV. assumption.
      - simpl in *; inversion_clear EV.
        specialize (IHϕ _ _ NEL _ H a).
        constructor; assumption.
      - inversion_clear EV; [constructor|apply ev_conj_fl|apply ev_conj_fr].
        all: try(apply IHϕ1; auto; intros EL; apply NEL; apply in_app_iff; left; assumption).
        all: try(apply IHϕ2; auto; intros EL; apply NEL; apply in_app_iff; right; assumption).
      - inversion_clear EV; [constructor|apply ev_disj_tl|apply ev_disj_tr].
        all: try(apply IHϕ1; auto; intros EL; apply NEL; apply in_app_iff; left; assumption).
        all: try(apply IHϕ2; auto; intros EL; apply NEL; apply in_app_iff; right; assumption).
    }
    { induction ϕ; intros.
      - inversion_clear EV; constructor.
      - inversion_clear EV; constructor.
      - inversion EV; subst.
        inversion H0; subst.
        + exfalso; apply NEL; left; auto. 
        + constructor; assumption.
      - inversion_clear EV; constructor.
        eapply IHϕ; eauto.
      - inversion_clear EV; [constructor|apply ev_conj_fl|apply ev_conj_fr].
        all: try(eapply IHϕ1; eauto; intros EL; apply NEL; apply in_app_iff; left; assumption).
        all: try(eapply IHϕ2; eauto; intros EL; apply NEL; apply in_app_iff; right; assumption).
      - inversion_clear EV; [constructor|apply ev_disj_tl|apply ev_disj_tr].
        all: try(eapply IHϕ1; eauto; intros EL; apply NEL; apply in_app_iff; left; assumption).
        all: try(eapply IHϕ2; eauto; intros EL; apply NEL; apply in_app_iff; right; assumption).
    }
  Qed.


  (* TODO: move to Alg2. *)
  Section FormulaSizeProperties.

    Lemma todo9:
      forall (ϕ : formula),
        formula_size (¬ ϕ) = formula_size ϕ.
    Proof.
      intros ?; unfold formula_size; simpl; reflexivity.
    Qed.

    Lemma todo10:
      forall (ϕl ϕr : formula),
        formula_size (ϕl ∧ ϕr) = formula_size ϕl + formula_size ϕr.
    Proof.
      intros; unfold formula_size; simpl; rewrite app_length; reflexivity.
    Qed.
    
    Lemma todo11:
      forall (ϕl ϕr : formula),
        formula_size (ϕl ∨ ϕr) = formula_size ϕl + formula_size ϕr.
    Proof.
      intros; unfold formula_size; simpl; rewrite app_length; reflexivity.
    Defined.


    
    Lemma todo17:
      forall (ϕ : formula) (x : variable),
        formula_size (ϕ [x ↦ T]) <= formula_size ϕ.
    Proof.
      intros; induction ϕ.
      { easy. }
      { easy. }
      { simpl; decide (x = v); [compute; omega | easy]. }
      { simpl; rewrite todo9, todo9; eauto. }
      { simpl; rewrite todo10, todo10.
        apply plus_le_compat; assumption. }
      { simpl; rewrite todo11, todo11.
        apply plus_le_compat; assumption. }
    Qed.
    
    Lemma todo18:
      forall (ϕ : formula) (x : variable),
        formula_size (ϕ [x ↦ F]) <= formula_size ϕ.
    Proof.
      intros; induction ϕ.
      { easy. }
      { easy. }
      { simpl; decide (x = v); [compute; omega | easy]. }
      { simpl; rewrite todo9, todo9; eauto. }
      { simpl; rewrite todo10, todo10.
        apply plus_le_compat; assumption. }
      { simpl; rewrite todo11, todo11.
        apply plus_le_compat; assumption. }
    Qed.

    
    Lemma todo19:
      forall (ϕl ϕr : formula) (x : variable),
        x el leaves (ϕl ∧ ϕr) ->
        {x el leaves ϕl} + {x el leaves ϕr}.
    Proof.
      intros ϕl ϕr x L.
      simpl in L; apply in_app_or_dec in L; auto using eq_var_dec.
    Qed.

    (* Del: *)
    Lemma todo20:
      forall (ϕl ϕr : formula) (x : variable),
        x el leaves (ϕl ∨ ϕr) ->
        {x el leaves ϕl} + {x el leaves ϕr}.
    Proof.
      intros ϕl ϕr x L.
      simpl in L; apply in_app_or_dec in L; auto using eq_var_dec. 
    Qed.
    
    
    Lemma todo3:
      forall (ϕ : formula) (x : variable),
        x el leaves ϕ -> 
        formula_size (ϕ[x ↦ T]) < formula_size ϕ.
    Proof.
      induction ϕ; intros ? L.
      { easy. }
      { easy. }
      { apply singl_in in L; subst.
        simpl; decide (v = v); [compute; omega | easy]. }
      { simpl; rewrite todo9, todo9; eauto. }
      { simpl; rewrite todo10, todo10.
        apply todo19 in L; destruct L as [L|L].
        { specialize (IHϕ1 _ L).
          apply Nat.le_lt_trans with (formula_size (ϕ1 [x ↦ T]) + formula_size ϕ2).
          { apply Nat.add_le_mono_l; apply todo17. }
          { apply Nat.add_lt_mono_r; assumption. }
        }
        { specialize (IHϕ2 _ L).
          apply Nat.le_lt_trans with (formula_size (ϕ1) + formula_size (ϕ2 [x ↦ T])).
          { apply Nat.add_le_mono_r; apply todo17. }
          { apply Nat.add_lt_mono_l; assumption. }
        }
      }
      { simpl; rewrite todo11, todo11.
        apply todo19 in L; destruct L as [L|L].
        { specialize (IHϕ1 _ L).
          apply Nat.le_lt_trans with (formula_size (ϕ1 [x ↦ T]) + formula_size ϕ2).
          { apply Nat.add_le_mono_l; apply todo17. }
          { apply Nat.add_lt_mono_r; assumption. }
        }
        { specialize (IHϕ2 _ L).
          apply Nat.le_lt_trans with (formula_size (ϕ1) + formula_size (ϕ2 [x ↦ T])).
          { apply Nat.add_le_mono_r; apply todo17. }
          { apply Nat.add_lt_mono_l; assumption. }
        }
      }
    Qed.

    Lemma todo5:
      forall (ϕ : formula) (x : variable),
        x el leaves ϕ -> 
        formula_size (ϕ[x ↦ F]) < formula_size ϕ.
    Proof.
      induction ϕ; intros ? L.
      { easy. }
      { easy. }
      { apply singl_in in L; subst.
        simpl; decide (v = v); [compute; omega | easy]. }
      { simpl; rewrite todo9, todo9; eauto. }
      { simpl; rewrite todo10, todo10.
        apply todo19 in L; destruct L as [L|L].
        { specialize (IHϕ1 _ L).
          apply Nat.le_lt_trans with (formula_size (ϕ1 [x ↦ F]) + formula_size ϕ2).
          { apply Nat.add_le_mono_l; apply todo18. }
          { apply Nat.add_lt_mono_r; assumption. }
        }
        { specialize (IHϕ2 _ L).
          apply Nat.le_lt_trans with (formula_size (ϕ1) + formula_size (ϕ2 [x ↦ F])).
          { apply Nat.add_le_mono_r; apply todo18. }
          { apply Nat.add_lt_mono_l; assumption. }
        }
      }
      { simpl; rewrite todo11, todo11.
        apply todo19 in L; destruct L as [L|L].
        { specialize (IHϕ1 _ L).
          apply Nat.le_lt_trans with (formula_size (ϕ1 [x ↦ F]) + formula_size ϕ2).
          { apply Nat.add_le_mono_l; apply todo18. }
          { apply Nat.add_lt_mono_r; assumption. }
        }
        { specialize (IHϕ2 _ L).
          apply Nat.le_lt_trans with (formula_size (ϕ1) + formula_size (ϕ2 [x ↦ F])).
          { apply Nat.add_le_mono_r; apply todo18. }
          { apply Nat.add_lt_mono_l; assumption. }
        }
      }
    Qed.

    Lemma todo12:
      forall (ϕ : formula) (v : variable), 
        v nel leaves (ϕ [v ↦ T]).
    Proof.
      intros.
      induction ϕ; intros EL; simpl in *.
      all: try(auto;fail).
      all: try(apply in_app_iff in EL; destruct EL as [EL|EL]; auto).
      decide (v = v0) as [EQ|NEQ].
      + unfold leaves in *; destruct EL.
      + apply singl_in in EL; auto.
    Qed.

    Lemma todo14:
      forall (ϕ : formula) (v : variable), 
        v nel leaves (ϕ [v ↦ F]).
    Proof.
      intros.
      induction ϕ; intros EL; simpl in *.
      all: try(auto;fail).
      all: try(apply in_app_iff in EL; destruct EL as [EL|EL]; auto).
      decide (v = v0) as [EQ|NEQ].
      + unfold leaves in *; destruct EL.
      + apply singl_in in EL; auto.
    Qed.

  End FormulaSizeProperties.


  Definition get_var (ϕ : formula) (NE : formula_size ϕ > 0):
    { v : variable | v el leaves ϕ }.
  Proof.
    unfold formula_size in NE.
    destruct (leaves ϕ).
    { simpl in NE; omega. }
    { exists v; left; reflexivity. }
  Defined.


  (* TODO: comment *)
  Definition formula_vars (ϕ : formula) :=
    nodup eq_var_dec (leaves ϕ).

  Definition sets_all_variables (ϕ : formula) (α : assignment) := 
    incl (leaves ϕ) (vars_in α).


  Lemma sets_all_variables_dec:
    forall (ϕ : formula) (α : assignment),
      dec (sets_all_variables ϕ α).
  Proof.
    intros; unfold sets_all_variables.
    induction (leaves ϕ) as [ | v vs].
    { left; intros v IN; exfalso; auto. }
    { decide (v el vars_in α) as [INv|NINv].
      - destruct IHvs as [IH|IH].
        + left; intros x INx.
          destruct INx as [EQ|INx]; [subst; assumption | apply IH; assumption].
        + right; intros C; apply IH; clear IH.
          intros a INa.
          apply C; right; assumption.
      - right; intros C.
        apply NINv.
        specialize (C v); feed C; [left; reflexivity | ]; assumption.
    } 
  Defined.


  (* TODO: comment *)
  Definition equivalent (ϕ1 ϕ2 : formula) :=
    forall (α : assignment) (b : bool), ℇ (ϕ1) α ≡ b <-> ℇ (ϕ2) α ≡ b.

  (** Properties of Equivalence. *)
  Section PropertiesOfEquivalence.
    
    Lemma formula_equivalence_refl: 
      forall (ϕ : formula),
        equivalent ϕ ϕ.
    Proof.
      intros ? ? ?; split; intros EV; assumption.
    Qed.

    Lemma formula_equivalence_sym: 
      forall (ϕ ψ : formula),
        equivalent ϕ ψ ->
        equivalent ψ ϕ.
    Proof.
      intros ? ? EQ ? ?; split; intros EV.
      - apply EQ in EV; assumption.
      - apply EQ; assumption.
    Qed.
    
    Lemma formula_equivalence_trans:
      forall (ϕ1 ϕ2 ϕ3 : formula),
        equivalent ϕ1 ϕ2 ->
        equivalent ϕ2 ϕ3 ->
        equivalent ϕ1 ϕ3.
    Proof.
      intros ? ? ? EV1 EV2 ? ?; split; intros EV.
      - apply EV2; apply EV1; assumption. 
      - apply EV1; apply EV2; assumption. 
    Qed.
    
    Lemma formula_equivalence_double_neg:
      forall (ϕ ψ : formula),
        equivalent ϕ ψ <-> 
        equivalent (¬ ¬ ϕ) ψ.
    Proof.
      intros ?; split; intros EQU ? ?; split; intros EV.
      - inversion_clear EV; inversion_clear H; apply EQU; destruct b; auto.
      - constructor; constructor; apply EQU; destruct b; auto.
      - specialize (EQU α b); destruct EQU.
        feed H; [constructor; destruct b; auto| ].
        inversion_clear H; destruct b; auto.
      - specialize (EQU α b); destruct EQU.
        feed H0; [auto| ].
        inversion_clear H0; inversion_clear H1; destruct b; auto.
    Qed.
    
    Lemma formula_equivalence_negate_both_sides:
      forall (ϕ ψ : formula),
        equivalent ϕ ψ <->
        equivalent (¬ ϕ) (¬ ψ).
    Proof.
      intros ? ?; split; intros EQU; split; intros EV.
      - inversion_clear EV; constructor; apply EQU; assumption. 
      - inversion_clear EV; constructor; apply EQU; assumption.
      - specialize (EQU α (negb b)); destruct EQU.
        feed H; [constructor; destruct b; auto| ].
        inversion_clear H; destruct b; auto.
      - specialize (EQU α (negb b)); destruct EQU.
        feed H0; [constructor; destruct b; auto| ].
        inversion_clear H0; destruct b; auto.
    Qed.

    Corollary formula_equivalence_move_negation: 
      forall (ϕ ψ : formula),
        equivalent ϕ (¬ ψ) ->
        equivalent (¬ ϕ) ψ.
    Proof.
      intros ? ? EV.
      apply formula_equivalence_negate_both_sides.
      apply ->formula_equivalence_double_neg; assumption.
    Qed.
    
    Lemma fo_eq_1:
      forall (ϕ1 ϕ2 ψ1 ψ2: formula),
        equivalent ϕ1 ψ1 ->
        equivalent ϕ2 ψ2 ->
        equivalent (ϕ1 ∧ ϕ2) (ψ1 ∧ ψ2).
    Proof.
      intros ? ? ? ? EQ1 EQ2 ? ?; split; intros EV.
      { destruct b.
        { inversion_clear EV.
          constructor.
          - apply EQ1; assumption.
          - apply EQ2; assumption.
        }
        { inversion_clear EV.
          apply ev_conj_fl; apply EQ1; assumption.
          apply ev_conj_fr; apply EQ2; assumption.
        } 
      }
      { destruct b.
        { inversion_clear EV.
          constructor.
          - apply EQ1; assumption.
          - apply EQ2; assumption.
        }
        { inversion_clear EV.
          apply ev_conj_fl; apply EQ1; assumption.
          apply ev_conj_fr; apply EQ2; assumption.
        } 
      }
    Qed.
    
    Lemma fo_eq_11:
      forall (ϕ1 ϕ2 ψ1 ψ2: formula),
        equivalent ϕ1 ψ1 ->
        equivalent ϕ2 ψ2 ->
        equivalent (ϕ1 ∨ ϕ2) (ψ1 ∨ ψ2).
    Proof.
      intros ? ? ? ? EQ1 EQ2 ? ?; split; intros EV.
      { destruct b.
        { inversion_clear EV.
          apply ev_disj_tl; apply EQ1; assumption.
          apply ev_disj_tr; apply EQ2; assumption.
        } 
        { inversion_clear EV.
          constructor.
          - apply EQ1; assumption.
          - apply EQ2; assumption.
        }
      }
      { destruct b.
        { inversion_clear EV.
          apply ev_disj_tl; apply EQ1; assumption.
          apply ev_disj_tr; apply EQ2; assumption.
        } 
        { inversion_clear EV.
          constructor.
          - apply EQ1; assumption.
          - apply EQ2; assumption.
        }
      }
    Qed.

    (* TODO: More general form? *)
    Lemma formula_equi_1:
      forall (ϕ1 ϕ2 ψ : formula),
        equivalent (ϕ1 ∧ ϕ2) ψ ->
        equivalent (ϕ2 ∧ ϕ1) ψ.
    Proof.
      intros ? ? ? EQ ? ?; split; intros EV.
      { apply EQ.
        inversion_clear EV.
        - constructor; assumption.
        - apply ev_conj_fr; assumption.
        - apply ev_conj_fl; assumption.
      }
      { apply EQ in EV.
        inversion_clear EV.
        - constructor; assumption.
        - apply ev_conj_fr; assumption.
        - apply ev_conj_fl; assumption.
      }    
    Qed.
    
    Lemma formula_equi_3:
      forall (ϕ1 ϕ2 ψ : formula),
        equivalent (ϕ1 ∨ ϕ2) ψ ->
        equivalent (ϕ2 ∨ ϕ1) ψ.
    Proof.
      intros ? ? ? EQ ? ?; split; intros EV.
      { apply EQ.
        inversion_clear EV.
        - constructor; assumption.
        - apply ev_disj_tr; assumption.
        - apply ev_disj_tl; assumption.
      }
      { apply EQ in EV.
        inversion_clear EV.
        - constructor; assumption.
        - apply ev_disj_tr; assumption.
        - apply ev_disj_tl; assumption.
      }
    Qed.  

    Lemma formula_equivalence_T_neg_F: 
      equivalent T (¬ F).
    Proof.
      intros α b; split; intros.
      - inversion_clear H; constructor; constructor.
      - inversion_clear H.
        destruct b; simpl in *.
        constructor.
        inversion_clear H0.
    Qed.


    Corollary fo_eq_2:
      forall (ϕ1 ϕ2 : formula),
        equivalent ϕ1 T ->
        equivalent ϕ2 T ->
        equivalent (ϕ1 ∧ ϕ2) T.
    Proof.
      intros.
      apply formula_equivalence_trans with (T ∧ T).
      apply fo_eq_1; auto. clear H H0.
      intros ? ?; split; intros EV.
      - inversion_clear EV;[constructor|inversion_clear H|inversion_clear H].
      - inversion_clear EV; constructor; constructor.
    Qed.

    (* TODO: More general form? *)
    Corollary fo_eq_3:
      forall (ϕ1 ϕ2 : formula),
        equivalent ϕ1 F ->
        equivalent (ϕ1 ∧ ϕ2) F.
    Proof.
      intros ? ? EQU ? ?; split; intros EV.
      { inversion_clear EV.
        apply EQU in H; inversion_clear H0.
        all: try (inversion_clear H).
        all: try (constructor).
      }
      { inversion_clear EV.
        constructor; apply EQU; constructor.
      }    
    Qed.

    (* TODO: More general form? *)
    Lemma formula_equi_2:
      forall (ϕ1 ϕ2 : formula),
        equivalent ϕ1 T -> 
        equivalent (ϕ1 ∨ ϕ2) T.
    Proof.
      intros ? ? EQ ? ?; split; intros EV.
      { destruct b.
        - constructor.
        - inversion_clear EV.
          apply EQ in H; inversion_clear H.
      }
      { destruct b.
        - apply ev_disj_tl.
          apply EQ; assumption.
        - inversion_clear EV.
      }
    Qed.

    Corollary fo_eq_21:
      forall (ϕ1 ϕ2 : formula),
        equivalent ϕ1 F ->
        equivalent ϕ2 F ->
        equivalent (ϕ1 ∨ ϕ2) F.
    Proof.
      intros.
      apply formula_equivalence_trans with (F ∨ F).
      apply fo_eq_11; auto. clear H H0.
      intros ? ?; split; intros EV.
      - inversion_clear EV;[constructor|inversion_clear H|inversion_clear H].
      - inversion_clear EV; constructor; constructor.
    Qed.



    Lemma admit_fo_eq_5:
      forall (ϕl ϕr ψ : formula),
        equivalent (ϕl ∧ ϕr) ψ <-> equivalent (¬ (¬ ϕl ∨ ¬ ϕr)) ψ.
    Proof.
      intros ? ? ?; split; intros EQ.
      
    Admitted.

    Lemma admit_fo_eq_6:
      forall (ϕl ϕr ψ : formula),
        equivalent (ϕl ∨ ϕr) ψ <-> equivalent (¬ (¬ ϕl ∧ ¬ ϕr)) ψ.
    Proof.
      intros ? ? ?; split; intros EQ.
      
      
    Admitted.

  End PropertiesOfEquivalence.

End Lemmas.