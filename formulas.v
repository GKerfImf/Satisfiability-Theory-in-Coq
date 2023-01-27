Require Export List Omega.
Import ListNotations.
From icl Require Export util assignments.

(** * Formulas *)
Inductive formula :=
| F : formula
| T : formula
| Var : variable -> formula
| Neg : formula -> formula
| Conj : formula -> formula -> formula
| Disj : formula -> formula -> formula.

Notation "[| x |]" := (Var x) (at level 0).
Notation "¬ x" := (Neg x) (at level 40). 
Notation "x '∧' y" := (Conj x y) (at level 40, left associativity).
Notation "x '∨' y" := (Disj x y) (at level 41, left associativity).

Definition xor (x y : formula) := (x ∧ ¬y) ∨ (¬x ∧ y). 
Notation "x '⊕' y" := (xor x y) (at level 41, left associativity).

Definition impl (x y : formula) := ¬x ∨ y. 
Notation "x '⇒' y" := (impl x y) (at level 41, left associativity).


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


Definition sat_assignment (ϕ : formula) (α : assignment) :=
  formula_eval ϕ α true.

Definition unsat_assignment (ϕ : formula) (α : assignment) :=
  formula_eval ϕ α false.


Reserved Notation "ϕ [ x ↦ ψ ]" (at level 10).
Fixpoint substitute (ϕ : formula) (v : variable) (ψ : formula) : formula :=
  match ϕ with
  | T => T
  | F => F
  | [|v'|] => if decision (v = v') then ψ else Var v'
  | ¬ ϕn => ¬ ϕn[v ↦ ψ]
  | ϕl ∧ ϕr => ϕl[v ↦ ψ] ∧ ϕr[v ↦ ψ]
  | ϕl ∨ ϕr => ϕl[v ↦ ψ] ∨ ϕr[v ↦ ψ]
  end
where "ϕ [ x ↦ f ]" := (substitute ϕ x f).

Fixpoint leaves (ϕ : formula) : variables :=
  match ϕ with
  | T | F => []
  | Var v => [v]
  | ¬ ϕ => leaves ϕ
  | ϕ1 ∧ ϕ2 => leaves ϕ1 ++ leaves ϕ2
  | ϕ1 ∨ ϕ2 => leaves ϕ1 ++ leaves ϕ2
  end.

(* Note that the formula size is the number of leaves 
   of the formula and not the number of variables.
   That is, formula_size (x1 ⊕ x2) = 4. *)
Definition formula_size (ϕ : formula) : nat :=
  length (leaves ϕ).

Definition get_var (ϕ : formula) (NE : formula_size ϕ > 0):
  { v : variable | v el leaves ϕ }.
Proof.
  unfold formula_size in NE.
  destruct (leaves ϕ).
  - simpl in NE; omega.
  - exists v; left; reflexivity.
Defined.


Definition formula_vars (ϕ : formula) :=
  nodup variable_eq_dec (leaves ϕ).

Definition sets_all_variables (α : assignment) (ϕ : formula) := 
  leaves ϕ ⊆ vars_in α.


Fixpoint number_of_nodes (ϕ : formula) : nat :=
  match ϕ with
  | T | F | Var _ => 1
  | ¬ ϕ => 1 + number_of_nodes ϕ
  | ϕl ∨ ϕr => 1 + number_of_nodes ϕl + number_of_nodes ϕr
  | ϕl ∧ ϕr => 1 + number_of_nodes ϕl + number_of_nodes ϕr
  end.

Definition equivalent (ϕ1 ϕ2 : formula) :=
  forall (α : assignment) (b : bool),
    ℇ (ϕ1) α ≡ b <-> ℇ (ϕ2) α ≡ b.


(** * Lemmas *) 
Section Lemmas.

  Lemma sets_all_variables_dec:
    forall (ϕ : formula) (α : assignment),
      dec (sets_all_variables α ϕ).
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

  Lemma formula_eval_injective:
    forall (ϕ : formula) (α : assignment) (b1 b2 : bool),
      ℇ (ϕ) α ≡ b1 ->
      ℇ (ϕ) α ≡ b2 ->
      b1 = b2.
  Proof.
    induction ϕ; intros ? ? ? EV1 EV2.
    all: inversion_clear EV1; inversion_clear EV2;
      auto 2; eauto 2 using mapsto_injective; destruct b1, b2; eauto.
  Qed.

  Lemma formula_eval_assignment_transfer:
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
      { eapply equiv_assignments_narrow_vars; eauto;
          intros x IN; simpl; apply in_app_iff; left; auto. } 
      specialize (IHϕ2 α β); feed IHϕ2. 
      { eapply equiv_assignments_narrow_vars; eauto;
          intros x IN; simpl; apply in_app_iff; right; auto. } 
      inversion_clear EV.
      + constructor; eauto.
      + apply ev_conj_fl; eauto.
      + apply ev_conj_fr; eauto.
    - specialize (IHϕ1 α β); feed IHϕ1. 
      { eapply equiv_assignments_narrow_vars; eauto;
          intros x IN; simpl; apply in_app_iff; left; auto. } 
      specialize (IHϕ2 α β); feed IHϕ2. 
      { eapply equiv_assignments_narrow_vars; eauto;
          intros x IN; simpl; apply in_app_iff; right; auto. } 
      inversion_clear EV.
      + constructor; eauto.
      + apply ev_disj_tl; eauto.
      + apply ev_disj_tr; eauto.
  Qed.

  Lemma formula_eval_nel_cons:
    forall (ϕ : formula) (α : assignment) (v : variable) (b a : bool),
      v nel leaves ϕ ->
      ℇ (ϕ) α ≡ b <-> ℇ (ϕ) (v,a) :: α ≡ b.
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

  Section SubstitutionProperties.
    
    Lemma leaves_nel_subst_T:
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

    Lemma leaves_nel_subst_F:
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
    
    Lemma leaves_subset_subst_T:
      forall (ϕ : formula) (x : variable),
        leaves (ϕ [x ↦ T]) ⊆ leaves ϕ.
    Proof.
      intros ϕ x v EL.
      induction ϕ.
      - destruct EL.
      - destruct EL.
      - simpl in EL; decide (x = v0); [destruct EL|assumption].
      - apply IHϕ; assumption.
      - simpl in EL; apply in_app_iff in EL; destruct EL as [EL|EL];
          simpl; apply in_app_iff; [left|right]; auto.
      - simpl in EL; apply in_app_iff in EL; destruct EL as [EL|EL];
          simpl; apply in_app_iff; [left|right]; auto.
    Qed.
    
    Lemma leaves_subset_subst_F:
      forall (ϕ : formula) (x : variable),
        leaves (ϕ [x ↦ F]) ⊆ leaves ϕ.
    Proof.
      intros ϕ x v EL.
      induction ϕ.
      - destruct EL.
      - destruct EL.
      - simpl in EL; decide (x = v0); [destruct EL|assumption].
      - apply IHϕ; assumption.
      - simpl in EL; apply in_app_iff in EL; destruct EL as [EL|EL];
          simpl; apply in_app_iff; [left|right]; auto.
      - simpl in EL; apply in_app_iff in EL; destruct EL as [EL|EL];
          simpl; apply in_app_iff; [left|right]; auto.
    Qed.
    
    Corollary sets_all_variables_subst_T:
      forall (ϕ : formula) (x : variable) (α : assignment),
        sets_all_variables α ϕ ->
        sets_all_variables α (ϕ [x ↦ T]).
    Proof.
      intros ? ? ? SET.
      intros v EL; apply SET.
      apply leaves_subset_subst_T in EL; assumption.
    Qed.
    
    Corollary sets_all_variables_subst_F:
      forall (ϕ : formula) (x : variable) (α: assignment),
        sets_all_variables α ϕ ->
        sets_all_variables α (ϕ [x ↦ F]).
    Proof.
      intros ? ? ? SET.
      intros v EL; apply SET.
      apply leaves_subset_subst_F in EL; assumption.
    Qed.
    
    Lemma leaves_el_neq_subst_T:
      forall (ϕ : formula) (v1 v2 : variable),
        v1 <> v2 ->
        v1 el leaves ϕ ->
        v1 el leaves (ϕ [v2 ↦ T]).
    Proof.
      intros ? ? ? NEQ EL.
      induction ϕ.
      all: try(auto; fail).
      - apply singl_in in EL; subst; simpl. 
        decide (v2 = v) as [EQ|NEQ2]; [exfalso;subst|left]; auto. 
      - simpl in *; apply in_app_iff in EL; destruct EL as [EL|EL];
          apply in_app_iff; [left|right]; auto.
      - simpl in *; apply in_app_iff in EL; destruct EL as [EL|EL];
          apply in_app_iff; [left|right]; auto.
    Qed.
    
    Lemma leaves_el_neq_subst_F:
      forall (ϕ : formula) (v1 v2 : variable),
        v1 <> v2 ->
        v1 el leaves ϕ ->
        v1 el leaves (ϕ [v2 ↦ F]).
    Proof.
      intros ? ? ? NEQ EL.
      induction ϕ.
      all: try(auto; fail).
      - apply singl_in in EL; subst; simpl. 
        decide (v2 = v) as [EQ|NEQ2]; [exfalso;subst|left]; auto.
      - simpl in *; apply in_app_iff in EL; destruct EL as [EL|EL];
          apply in_app_iff; [left|right]; auto.
      - simpl in *; apply in_app_iff in EL; destruct EL as [EL|EL];
          apply in_app_iff; [left|right]; auto.
    Qed.

  End SubstitutionProperties.
 
  Section FormulaSizeProperties.
    
    Lemma leaves_el_and:
      forall (ϕl ϕr : formula) (x : variable),
        x el leaves (ϕl ∧ ϕr) ->
        {x el leaves ϕl} + {x el leaves ϕr}.
    Proof.
      intros ϕl ϕr x L.
      simpl in L; apply in_app_or_dec in L; auto using variable_eq_dec.
    Qed.

    Lemma leaves_el_or:
      forall (ϕl ϕr : formula) (x : variable),
        x el leaves (ϕl ∨ ϕr) ->
        {x el leaves ϕl} + {x el leaves ϕr}.
    Proof.
      intros ϕl ϕr x L.
      simpl in L; apply in_app_or_dec in L; auto using variable_eq_dec. 
    Qed.

    
    Lemma formula_size_neg:
      forall (ϕ : formula),
        formula_size (¬ ϕ) = formula_size ϕ.
    Proof.
      intros ?; unfold formula_size; simpl; reflexivity.
    Qed.

    Lemma formula_size_and:
      forall (ϕl ϕr : formula),
        formula_size (ϕl ∧ ϕr) = formula_size ϕl + formula_size ϕr.
    Proof.
      intros; unfold formula_size; simpl; rewrite app_length; reflexivity.
    Qed.
    
    Lemma formula_size_or:
      forall (ϕl ϕr : formula),
        formula_size (ϕl ∨ ϕr) = formula_size ϕl + formula_size ϕr.
    Proof.
      intros; unfold formula_size; simpl; rewrite app_length; reflexivity.
    Qed.
    
    
    Lemma formula_size_subst_T_le:
      forall (ϕ : formula) (x : variable),
        formula_size (ϕ [x ↦ T]) <= formula_size ϕ.
    Proof.
      intros; induction ϕ.
      - easy.
      - easy.
      - simpl; decide (x = v); [compute; omega|easy].
      - simpl; rewrite !formula_size_neg; eauto.
      - simpl; rewrite !formula_size_and.
        auto using plus_le_compat.
      - simpl; rewrite !formula_size_or.
        auto using plus_le_compat.
    Qed.
    
    Lemma formula_size_subst_F_le:
      forall (ϕ : formula) (x : variable),
        formula_size (ϕ [x ↦ F]) <= formula_size ϕ.
    Proof.
      intros; induction ϕ.
      - easy.
      - easy.
      - simpl; decide (x = v); [compute; omega|easy].
      - simpl; rewrite !formula_size_neg; eauto.
      - simpl; rewrite !formula_size_and.
        auto using plus_le_compat. 
      - simpl; rewrite !formula_size_or.
        auto using plus_le_compat.
    Qed.
    
    Lemma formula_size_subst_T_lt:
      forall (ϕ : formula) (x : variable),
        x el leaves ϕ -> 
        formula_size (ϕ[x ↦ T]) < formula_size ϕ.
    Proof.
      induction ϕ; intros ? L.
      { easy. }
      { easy. }
      { apply singl_in in L; subst.
        simpl; decide (v = v); [compute; omega|easy]. }
      { simpl; rewrite !formula_size_neg; eauto. }
      { simpl; rewrite !formula_size_and.
        apply leaves_el_and in L; destruct L as [L|L].
        - specialize (IHϕ1 _ L).
          apply Nat.le_lt_trans with (formula_size (ϕ1 [x ↦ T]) + formula_size ϕ2).
          + apply Nat.add_le_mono_l; apply formula_size_subst_T_le.
          + apply Nat.add_lt_mono_r; assumption.
        - specialize (IHϕ2 _ L).
          apply Nat.le_lt_trans with (formula_size (ϕ1) + formula_size (ϕ2 [x ↦ T])).
          + apply Nat.add_le_mono_r; apply formula_size_subst_T_le.
          + apply Nat.add_lt_mono_l; assumption.
      }
      { simpl; rewrite !formula_size_or.
        apply leaves_el_and in L; destruct L as [L|L].
        - specialize (IHϕ1 _ L).
          apply Nat.le_lt_trans with (formula_size (ϕ1 [x ↦ T]) + formula_size ϕ2).
          + apply Nat.add_le_mono_l; apply formula_size_subst_T_le.
          + apply Nat.add_lt_mono_r; assumption.
        - specialize (IHϕ2 _ L).
          apply Nat.le_lt_trans with (formula_size (ϕ1) + formula_size (ϕ2 [x ↦ T])).
          + apply Nat.add_le_mono_r; apply formula_size_subst_T_le.
          + apply Nat.add_lt_mono_l; assumption.
      }
    Qed.

    Lemma formula_size_subst_F_lt:
      forall (ϕ : formula) (x : variable),
        x el leaves ϕ -> 
        formula_size (ϕ[x ↦ F]) < formula_size ϕ.
    Proof.
      induction ϕ; intros ? L.
      { easy. }
      { easy. }
      { apply singl_in in L; subst.
        simpl; decide (v = v); [compute; omega|easy]. } 
      { simpl; rewrite !formula_size_neg; eauto. } 
      { simpl; rewrite !formula_size_and.
        apply leaves_el_and in L; destruct L as [L|L].
        - specialize (IHϕ1 _ L).
          apply Nat.le_lt_trans with (formula_size (ϕ1 [x ↦ F]) + formula_size ϕ2).
          + apply Nat.add_le_mono_l; apply formula_size_subst_F_le.
          + apply Nat.add_lt_mono_r; assumption.
        - specialize (IHϕ2 _ L).
          apply Nat.le_lt_trans with (formula_size (ϕ1) + formula_size (ϕ2 [x ↦ F])).
          + apply Nat.add_le_mono_r; apply formula_size_subst_F_le.
          + apply Nat.add_lt_mono_l; assumption.
      } 
      { simpl; rewrite !formula_size_or.
        apply leaves_el_and in L; destruct L as [L|L].
        - specialize (IHϕ1 _ L).
          apply Nat.le_lt_trans with (formula_size (ϕ1 [x ↦ F]) + formula_size ϕ2).
          + apply Nat.add_le_mono_l; apply formula_size_subst_F_le.
          + apply Nat.add_lt_mono_r; assumption.
        - specialize (IHϕ2 _ L).
          apply Nat.le_lt_trans with (formula_size (ϕ1) + formula_size (ϕ2 [x ↦ F])).
          + apply Nat.add_le_mono_r; apply formula_size_subst_F_le.
          + apply Nat.add_lt_mono_l; assumption.
      }
    Qed.

  End FormulaSizeProperties.

  (** Properties of Equivalence. *)
  Section PropertiesOfEquivalence.

    Section FormulaEquivalenceIsEquivalenceRelation.
      
      Lemma formula_equiv_refl: 
        forall (ϕ : formula),
          equivalent ϕ ϕ.
      Proof.
        intros ? ? ?; split; intros EV; assumption.
      Qed.

      Lemma formula_equiv_sym: 
        forall (ϕ1 ϕ2 : formula),
          equivalent ϕ1 ϕ2 ->
          equivalent ϕ2 ϕ1.
      Proof.
        intros ? ? EQ ? ?; split; intros EV.
        - apply EQ in EV; assumption.
        - apply EQ; assumption.
      Qed.
      
      Lemma formula_equiv_trans:
        forall (ϕ1 ϕ2 ϕ3 : formula),
          equivalent ϕ1 ϕ2 ->
          equivalent ϕ2 ϕ3 ->
          equivalent ϕ1 ϕ3.
      Proof.
        intros ? ? ? EV1 EV2 ? ?; split; intros EV.
        - apply EV2; apply EV1; assumption. 
        - apply EV1; apply EV2; assumption. 
      Qed.

    End FormulaEquivalenceIsEquivalenceRelation.

    Lemma formula_equiv_double_neg:
      forall (ϕ : formula),
        equivalent ϕ (¬ ¬ ϕ).
    Proof.
      intros ? ? [ | ]; split; intros EV; auto.
      all: inversion_clear EV; inversion_clear H; auto.
    Qed.
    
    Lemma formula_equiv_neg_compose:
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

    Corollary formula_equiv_neg_move: 
      forall (ϕ ψ : formula),
        equivalent ϕ (¬ ψ) ->
        equivalent (¬ ϕ) ψ.
    Proof.
      intros ? ? EV.
      apply formula_equiv_neg_compose.
      apply formula_equiv_trans with (ϕ); auto.
      apply formula_equiv_sym, formula_equiv_double_neg.
    Qed.
    
    Lemma formula_equiv_and_compose:
      forall (ϕ1 ϕ2 ψ1 ψ2: formula),
        equivalent ϕ1 ψ1 ->
        equivalent ϕ2 ψ2 ->
        equivalent (ϕ1 ∧ ϕ2) (ψ1 ∧ ψ2).
    Proof.
      intros ? ? ? ? EQ1 EQ2 ? [ | ]; split; intros EV.
      all: inversion_clear EV; constructor; [apply EQ1|apply EQ2]; auto. 
    Qed.

    Corollary formula_equiv_and_compose_T:
      forall (ϕ1 ϕ2 : formula),
        equivalent ϕ1 T ->
        equivalent ϕ2 T ->
        equivalent (ϕ1 ∧ ϕ2) T.
    Proof.
      intros.
      apply formula_equiv_trans with (T ∧ T).
      apply formula_equiv_and_compose; auto. clear H H0.
      intros ? ?; split; intros EV.
      - inversion_clear EV;[constructor|inversion_clear H|inversion_clear H].
      - inversion_clear EV; constructor; constructor.
    Qed.

    Lemma formula_equiv_and_compose_F:
      forall (ϕ1 ϕ2 : formula),
        equivalent ϕ1 F ->
        equivalent (ϕ1 ∧ ϕ2) F.
    Proof.
      intros ? ? EQU ? [ | ]; split; intros EV.
      all: inversion_clear EV; auto.
      - apply EQU; auto.
      - constructor; apply EQU; auto.
    Qed.
        
    Lemma formula_equiv_or_compose:
      forall (ϕ1 ϕ2 ψ1 ψ2: formula),
        equivalent ϕ1 ψ1 ->
        equivalent ϕ2 ψ2 ->
        equivalent (ϕ1 ∨ ϕ2) (ψ1 ∨ ψ2).
    Proof.
      intros ? ? ? ? EQ1 EQ2 ? [ | ]; split; intros EV.
      all: inversion_clear EV; constructor; [apply EQ1|apply EQ2]; auto. 
    Qed.

    Corollary formula_equiv_or_compose_F:
      forall (ϕ1 ϕ2 : formula),
        equivalent ϕ1 F ->
        equivalent ϕ2 F ->
        equivalent (ϕ1 ∨ ϕ2) F.
    Proof.
      intros.
      apply formula_equiv_trans with (F ∨ F).
      apply formula_equiv_or_compose; auto. clear H H0.
      intros ? ?; split; intros EV.
      - inversion_clear EV;[constructor|inversion_clear H|inversion_clear H].
      - inversion_clear EV; constructor; constructor.
    Qed.
    
    Lemma formula_equiv_or_compose_T:
      forall (ϕ1 ϕ2 : formula),
        equivalent ϕ1 T -> 
        equivalent (ϕ1 ∨ ϕ2) T.
    Proof.
      intros ? ? EQU ? [ | ]; split; intros EV.
      all: inversion_clear EV; auto.
      - constructor; apply EQU; auto.
      - apply EQU; auto.
    Qed.
    
    Lemma formula_equiv_and_comm:
      forall (ϕ1 ϕ2 : formula),
        equivalent (ϕ1 ∧ ϕ2) (ϕ2 ∧ ϕ1).
    Proof.
      intros ? ? ? [ | ]; split; intros EV.
      all: inversion_clear EV.
      all: try(constructor; auto; fail).
    Qed.
    
    Lemma formula_equiv_or_comm:
      forall (ϕ1 ϕ2 : formula),
        equivalent (ϕ1 ∨ ϕ2) (ϕ2 ∨ ϕ1).
    Proof.
      intros ? ? ? [ | ]; split; intros EV.
      all: inversion_clear EV.
      all: try(constructor; auto; fail).
    Qed.

    Lemma formula_equiv_demorgan_and:
      forall (ϕ1 ϕ2 : formula),
        equivalent (ϕ1 ∧ ϕ2) (¬(¬ϕ1 ∨ ¬ϕ2)).
    Proof.
      intros ? ? ? [ | ]; split; intros EV.
      - inversion_clear EV; auto.
      - inversion_clear EV; inversion_clear H; inversion_clear H0; inversion_clear H1; auto.
      - inversion_clear EV; constructor; [apply ev_disj_tl | apply ev_disj_tr]; auto.
      - inversion_clear EV; inversion_clear H;
          [apply ev_conj_fl | apply ev_conj_fr]; inversion_clear H0; auto.
    Qed.
    
    Lemma formula_equiv_demorgan_or:
      forall (ϕ1 ϕ2 : formula),
        equivalent (ϕ1 ∨ ϕ2) (¬(¬ϕ1 ∧ ¬ϕ2)).
    Proof.
      intros ? ? ? [ | ]; split; intros EV.
      - inversion_clear EV; auto.
      - inversion_clear EV; inversion_clear H;
          [apply ev_disj_tl | apply ev_disj_tr]; inversion_clear H0; auto.
      - inversion_clear EV; auto. 
      - inversion_clear EV; inversion_clear H; inversion_clear H0; inversion_clear H1; auto.
    Qed.
 
    Lemma formula_equiv_T_neg_F: 
      equivalent T (¬ F).
    Proof.
      intros α [ | ]; split; intros EV; inversion_clear EV; simpl in *; auto; inversion_clear H.
    Qed.
    
  End PropertiesOfEquivalence.

End Lemmas.