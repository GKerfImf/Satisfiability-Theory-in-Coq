Require Export List Omega.
Import ListNotations.

From icl Require Export util assignments formulas. 

Require Export List Omega.
Import ListNotations.
From icl Require Import util assignments formulas number_of_models.


(** * Algorithm 1: *)
(** Just compute the list of all assignments, and then filter *)
Section Algorithm1.
  
  Definition set_with_all_assignments_on (vs: variables) (αs: assignments) :=
    set_with_all (equiv_assignments vs) (fun α => incl vs (vars_in α)) αs.
  
  Fixpoint all_assignments_on (vs: variables): assignments :=
    match vs with
    | [] => [[]]
    | v::vs => map (cons (v,false)) (all_assignments_on vs)
                  ++ map (cons (v,true)) (all_assignments_on vs)
    end.

  (* TODO: fix name *)
  Lemma size_of_list_of_all_assignments:
    forall (vs : variables),
      length (all_assignments_on vs) = Nat.pow 2 (length vs).
  Proof.
    induction vs; simpl. 
    { reflexivity. }
    { rewrite app_length, !map_length, <- plus_n_O, <- IHvs.
      reflexivity. } 
  Qed.

  (* TODO: fix name *) 
  Lemma list_of_all_assignments_dupfree:
    forall (vs : variables),
      NoDup vs ->
      dupfree vs (all_assignments_on vs). 
  Proof.
    intros ? ND; split.
    { induction vs.
      - constructor; [intros C; easy | constructor ].
      - apply NoDup_cons_iff in ND; destruct ND as [NEL ND].
        feed IHvs; [assumption | ].
        apply dfnn_ext; [easy | assumption | assumption].
    } 
    { induction vs; intros α1 α2 EL1 EL2 NEQ EQ.
      { inversion EL1; inversion EL2; subst; auto. }
      { apply NoDup_cons_iff in ND; destruct ND as [NEL ND].
        feed IHvs; auto.
        simpl in EL1, EL2; apply in_app_iff in EL1; apply in_app_iff in EL2.
        destruct EL1 as [EL1|EL1], EL2 as [EL2|EL2];
          apply in_map_iff in EL1; apply in_map_iff in EL2;
            destruct EL1 as [α1_tl [EQ1 EL1]], EL2 as [α2_tl [EQ2 EL2]].
        { rewrite <-EQ1, <-EQ2 in EQ, NEQ; clear EQ1 EQ2 α1 α2.
          rename α1_tl into α1, α2_tl into α2.
          apply cons_disj in NEQ.
          specialize (IHvs _ _ EL1 EL2 NEQ).
          apply IHvs; clear IHvs.
          eapply todo41; eauto 2.
        }
        { rewrite <-EQ1, <-EQ2 in EQ, NEQ; clear EQ1 EQ2 NEQ.
          apply todo42 in EQ; assumption. }
        { rewrite <-EQ1, <-EQ2 in EQ, NEQ; clear EQ1 EQ2 NEQ.
          apply todo42 in EQ; assumption. }
        { rewrite <-EQ1, <-EQ2 in EQ, NEQ; clear EQ1 EQ2 α1 α2.
          rename α1_tl into α1, α2_tl into α2.
          apply cons_disj in NEQ.
          specialize (IHvs _ _ EL1 EL2 NEQ).
          apply IHvs; clear IHvs.
          eapply todo41; eauto 2.
        } 
      }
    }
  Qed.

  (* TODO: fix name *)
  Lemma all_assignments_in_this_list:
    forall (vs : variables), 
      set_with_all_assignments_on vs (all_assignments_on vs).
  Proof.
    induction vs; intros α INCL.
    { exists []; split.
      - intros v EL; inversion EL.
      - left; reflexivity. }
    { specialize (IHvs α); feed IHvs; auto.
      { intros v EL; apply INCL; right; auto. }
      destruct IHvs as [β [EQU IN]].
      destruct (todo22 α a) as [[[EL MAP]|[NEL2 NMAP]]|[EL MAP]].
      { exists ((a,true)::β); split.
        { intros v EL2; destruct EL2 as [EQ|EL2]; subst; intros b; split; intros EV.
          - apply (todo2 _ _ _ _ MAP) in EV; subst; constructor.
          - inversion EV; subst; [ |exfalso]; auto.
          - decide (a = v) as [EQ|NEQ]; [subst | ].
            apply EQU in MAP; apply EQU in EV; auto.
            apply (todo2 _ _ _ _ MAP) in EV; subst; constructor.
            constructor; auto; apply EQU; auto.
          - admit.

        } 
        { simpl; apply in_app_iff; right.
          apply in_map_iff; exists β; split; auto.
        } 
      }
      { exfalso; apply NEL2; apply INCL; left; auto. } 
      { exists ((a,false)::β); split.
        { intros v EL2; destruct EL2 as [EQ|EL2]; subst.
          admit. admit.
        } 
        { simpl; apply in_app_iff; left.
          apply in_map_iff; exists β; split; auto.
        } 
      }      
    }
  Admitted.
  
  Definition compute_formula (ϕ : formula) (α : assignment) (SET : sets_all_variables ϕ α):
    { b : bool | formula_eval ϕ α b }.
  Proof.
    induction ϕ.
    { exists false. constructor. }
    { exists true. constructor. }
    { feed (SET v).
      { left; reflexivity. }
      destruct (mapsto_dec α v SET) as [M|M]; [exists true| exists false]; constructor; assumption. }
    { destruct IHϕ as [b EV].
      simpl in SET; assumption.
      exists (negb b); constructor; rewrite Bool.negb_involutive; assumption. }
    { apply inclusion_app in SET; destruct SET.
      destruct IHϕ1 as [b1 EV1]; destruct IHϕ2 as [b2 EV2]; try auto.
      exists (andb b1 b2).
      destruct b1, b2; simpl in *; try(constructor; auto; fail). }
    { simpl in SET; apply inclusion_app in SET; destruct SET.
      destruct IHϕ1 as [b1 EV1]; destruct IHϕ2 as [b2 EV2]; try auto.
      exists (orb b1 b2).
      destruct b1, b2; simpl in *; try(constructor; auto; fail). }
  Defined.


  Lemma todo51:
    forall (vs : variables) (α : assignment),
      α el all_assignments_on vs ->
      equi (vars_in α) vs.
  Proof.
    induction vs; intros ? EL; simpl in EL.
    { destruct EL as [EL|F]; [subst |exfalso]; auto.
      split; intros x EL; destruct EL.
    } 
    { apply in_app_iff in EL; destruct EL as [EL|EL].
      { apply in_map_iff in EL; destruct EL as [α_tl [EQ EL]]; subst α.
        specialize (IHvs _ EL).
        simpl; apply todo52; assumption.
      }
      { apply in_map_iff in EL; destruct EL as [α_tl [EQ EL]]; subst α.
        specialize (IHvs _ EL).
        simpl; apply todo52; assumption. 
      }
    } 
  Qed.
  
  Lemma todo32:
    forall (ϕ : formula) (α : assignment),
      α el all_assignments_on (formula_vars ϕ) ->
      sets_all_variables ϕ α.
  Proof.
    intros ? ? EL.
    apply todo51 in EL; rename EL into EQU. 
    intros v EL; apply EQU.
    apply nodup_In; assumption.
  Qed.      

  (* TODO: match ~> if *)
  Definition formula_sat_filter (ϕ : formula) (α : assignment): bool :=
    match sets_all_variables_dec ϕ α with 
    | left _ SETS => let '(exist _ b _) := compute_formula ϕ α SETS in b
    | right _ => false
    end.
  
  (* TODO: comment *)
  Definition algorithm1 (ϕ: formula): {n: nat | #sat ϕ ≃ n }.
  Proof. 
    set (vars := formula_vars ϕ). 
    assert(EX: { αs | list_of_all_sat_assignments ϕ αs }).
    { exists (filter (fun α => formula_sat_filter ϕ α) (all_assignments_on vars)).
      split;[split | split].
      { apply dffil.
        destruct(list_of_all_assignments_dupfree vars).
        - apply NoDup_nodup.
        - assumption.
      }
      { intros α1 α2 EL1 EL2 NEQ EQU.
        apply filter_In in EL1; destruct EL1 as [EL1 SAT1].
        apply filter_In in EL2; destruct EL2 as [EL2 SAT2].
        apply equiv_nodup in EQU.
        apply list_of_all_assignments_dupfree in EQU; try (apply NoDup_nodup || assumption).
      }
      { intros α EL.  
        apply filter_In in EL; destruct EL as [EL TR]. 
        unfold formula_sat_filter in *; destruct (sets_all_variables_dec ϕ α) as [D|D]; [ | easy].
        destruct (compute_formula ϕ α D) as [b EV]; subst b.
        split; assumption.
      } 
      { intros α [SETS SAT].
        assert(H := all_assignments_in_this_list vars α).
        feed H; [eapply incl_trans; eauto; apply incl_nodup| ]. 
        destruct H as [β [EQ EL]].
        exists β; split.
        - clear EL; intros ? EL b; split; intros EV.
          all: apply EQ; auto; apply nodup_In; auto.
        - apply filter_In; split; [assumption | ].
          unfold formula_sat_filter; destruct (sets_all_variables_dec ϕ β) as [S|S].
          + apply equiv_nodup in EQ.
            destruct (compute_formula ϕ β S) as [b EV].
            apply admit_equiv_sat with (β := β) in SAT; [ | assumption].
            eapply formula_eval_inj; eauto 2.
          + exfalso; apply S.
            apply todo32; assumption. 
      }
    }
    destruct EX as [αs AS]; exists (length αs); exists αs; split; auto.
  Defined.

  (* => 16 *)
(*  Compute (proj1_sig (algorithm1 (x1))).
  Compute (proj1_sig (algorithm1 (x1 ⊕ x2 ⊕ x3 ⊕ x4 ⊕ x5))).
  Compute (proj1_sig (algorithm1 (x1 ∨ x2 ∨ x3 ∨ x4 ∨ x5))). *)

  
End Algorithm1.


(** * Algorithm 2: *)
(** With transformation ϕ = (ϕ[x ↦ T] ∧ x) ∨ (ϕ[x ↦ F] ∧ ¬x). *)
  (* 
   The main idea of the algorithm is the following: 
       #sat F = 0
       #sat T = 1 
       #sat ϕ = #sat (x ∧ ϕ[x ↦ T] ∨ ¬x ∧ ϕ[x ↦ F]) 
              = #sat (x ∧ ϕ[x ↦ T]) + #sat (¬x ∧ ϕ[x ↦ F])
              = #sat (ϕ[x ↦ T]) + #sat (ϕ[x ↦ F])

   *)

Section Algorithm2.

  Section SubstitutionProperties.
    
    Lemma todo57:
      forall (ϕ : formula) (x : variable),
        incl (leaves (ϕ [x ↦ T])) (leaves ϕ).
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

    Corollary todo71:
      forall ϕ x (α: assignment),
        sets_all_variables ϕ α ->
        sets_all_variables (ϕ [x ↦ T]) α.
    Proof.
      intros ? ? ? SET.
      intros v EL; apply SET.
      apply todo57 in EL; assumption.
    Qed.

    
    Lemma todo58:
      forall (ϕ : formula) (x : variable),
        incl (leaves (ϕ [x ↦ F])) (leaves ϕ).
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

    Corollary todo72:
      forall ϕ x (α: assignment),
        sets_all_variables ϕ α ->
        sets_all_variables (ϕ [x ↦ F]) α.
    Proof.
      intros ? ? ? SET.
      intros v EL; apply SET.
      apply todo58 in EL; assumption.
    Qed.
    
    Lemma todo73:
      forall (ϕ : formula) (v1 v2 : variable),
        v1 <> v2 ->
        v1 el leaves ϕ ->
        v1 el leaves (ϕ [v2 ↦ T]).
    Proof.
      intros ? ? ? NEQ EL.
      induction ϕ.
      all: try(auto; fail).
      { apply singl_in in EL; subst; simpl. 
        decide (v2 = v) as [EQ|NEQ2]; [exfalso;subst|left]; auto. } 
      { simpl in *; apply in_app_iff in EL; destruct EL as [EL|EL];
          apply in_app_iff; [left|right]; auto. }
      { simpl in *; apply in_app_iff in EL; destruct EL as [EL|EL];
          apply in_app_iff; [left|right]; auto. }
    Qed.
    
    Lemma todo74:
      forall (ϕ : formula) (v1 v2 : variable),
        v1 <> v2 ->
        v1 el leaves ϕ ->
        v1 el leaves (ϕ [v2 ↦ F]).
    Proof.
      intros ? ? ? NEQ EL.
      induction ϕ.
      all: try(auto; fail).
      { apply singl_in in EL; subst; simpl. 
        decide (v2 = v) as [EQ|NEQ2]; [exfalso;subst|left]; auto. } 
      { simpl in *; apply in_app_iff in EL; destruct EL as [EL|EL];
          apply in_app_iff; [left|right]; auto. }
      { simpl in *; apply in_app_iff in EL; destruct EL as [EL|EL];
          apply in_app_iff; [left|right]; auto. }
    Qed.

  End SubstitutionProperties.

  Section BaseCase.

    Lemma formula_size_dec:
      forall (ϕ : formula),
        {formula_size ϕ = 0} + {formula_size ϕ > 0}.
    Proof.
      intros.
      induction ϕ.
      { left; easy. }
      { left; easy. }
      { right; unfold formula_size; simpl; omega. }
      { destruct IHϕ as [IH|IH]. 
        - left; assumption.
        - right; assumption.
      }
      { destruct IHϕ1 as [IH1|IH1].
        - destruct IHϕ2 as [IH2|IH2].
          + left; unfold formula_size in *; simpl.
            rewrite app_length, IH1, IH2. easy.
          + right; unfold formula_size in *; simpl.
            rewrite app_length, IH1; easy.
        - right; unfold formula_size in *; simpl.
          rewrite app_length; omega.
      }
      { destruct IHϕ1 as [IH1|IH1].
        - destruct IHϕ2 as [IH2|IH2].
          + left; unfold formula_size in *; simpl.
            rewrite app_length, IH1, IH2. easy.
          + right; unfold formula_size in *; simpl.
            rewrite app_length, IH1; easy.
        - right; unfold formula_size in *; simpl.
          rewrite app_length; omega.
      }
    Defined.

    Lemma zero_size_formula_constant_dec:
      forall (ϕ : formula),
        formula_size ϕ = 0 -> 
        {equivalent ϕ T} + {equivalent ϕ F}.
    Proof.
      intros ? SIZE.
      induction ϕ.
      { right; intros ? ?; split; intros EV; assumption. }
      { left; intros ? ?; split; intros EV; assumption. }
      { exfalso; compute in SIZE; easy. }
      { rewrite todo9 in SIZE. 
        feed IHϕ; auto.
        destruct IHϕ as [IH|IH]; [right | left].
        { apply formula_equivalence_move_negation.
          apply formula_equivalence_trans with T; auto.
          apply formula_equivalence_T_neg_F. }
        { apply formula_equivalence_move_negation.
          apply formula_equivalence_trans with F; auto.
          apply formula_equivalence_sym, formula_equivalence_move_negation, formula_equivalence_T_neg_F. } }
      { rewrite todo10 in SIZE.
        apply plus_is_O in SIZE.
        destruct SIZE as [S1 S2].
        feed IHϕ1; auto; feed IHϕ2; auto.
        destruct IHϕ1 as [IH1|IH1].
        - destruct IHϕ2 as [IH2|IH2].
          + left; apply fo_eq_2; auto.
          + right; clear IH1.
            apply formula_equi_1, fo_eq_3; auto.
        - right; clear IHϕ2.
          apply fo_eq_3; auto.
      }
      { rewrite todo11 in SIZE.
        apply plus_is_O in SIZE.
        destruct SIZE as [S1 S2].
        feed IHϕ1; auto; feed IHϕ2; auto.
        destruct IHϕ1 as [IH1|IH1].
        - clear IHϕ2; left. 
          apply formula_equi_2; auto.
        - destruct IHϕ2 as [IH2|IH2].
          + left; apply formula_equi_3, formula_equi_2; auto. 
          + right.
            apply fo_eq_21; auto; apply fo_eq_11.
      }
    Defined.

    Lemma count5:
      forall (ϕ : formula),
        formula_size ϕ = 0 -> 
        equivalent ϕ T -> 
        number_of_sat_assignments ϕ 1.
    Proof.
      intros ? Z EQ.
      exists [[]]. split; [split; [split | split] | ].
      - constructor; [easy| constructor]. 
      - intros ? ? EL1 EL2 NEQ.
        exfalso; apply NEQ.
        apply singl_in in EL1; apply singl_in in EL2; subst.
        auto.
      - intros ? EL.
        apply singl_in in EL; subst; split.
        + intros v EL; exfalso.
          apply length_zero_iff_nil in Z; rewrite Z in EL.
          destruct EL.
        + apply EQ; constructor.
      - intros.
        exists []; split.
        apply length_zero_iff_nil in Z; rewrite Z.
        + easy.        
        + left; auto.
      - reflexivity.
    Qed.
          
    Corollary count3:
      number_of_sat_assignments T 1.
    Proof.
      apply count5.
      - reflexivity.
      - apply formula_equivalence_refl.
    Qed.      
      
    Lemma count6:
      forall (ϕ : formula),
        formula_size ϕ = 0 -> 
        equivalent ϕ F -> 
        number_of_sat_assignments ϕ 0.
    Proof.
      intros ? Z EQ.
      exists []. split; [split; [split | split] | ].
      - constructor.
      - intros ? ? EL1 EL2 NEQ; destruct EL1.
      - intros ? EL; destruct EL.
      - intros α [_ SAT].
        apply EQ in SAT.
        inversion_clear SAT.
      - reflexivity.
    Qed.
    
    Corollary count4: 
      number_of_sat_assignments F 0.
    Proof.
      apply count6.
      - reflexivity.
      - apply formula_equivalence_refl.
    Qed.
    
  End BaseCase.

  Section InductionStep.

    Lemma todo76:
      forall (ϕ : formula) (x : variable) (α : assignment) (b : bool),
        x / α ↦ true ->
        ℇ (ϕ) α ≡ b <-> ℇ (ϕ [x ↦ T]) α ≡ b.
    Proof.
      intros ϕ; induction ϕ; intros x α b M; split; intros EV.
      all: try(inversion_clear EV; constructor; fail).
      all: try(inversion_clear EV; simpl;
               [ eapply ev_conj_t; [eapply IHϕ1|eapply IHϕ2]
               | eapply ev_conj_fl; eapply IHϕ1
               | eapply ev_conj_fr; eapply IHϕ2]; eauto).
      all: try(inversion_clear EV; simpl;
               [ eapply ev_disj_f; [eapply IHϕ1|eapply IHϕ2]
               | eapply ev_disj_tl; eapply IHϕ1
               | eapply ev_disj_tr; eapply IHϕ2]; eauto).
      all: try(simpl; constructor; eapply IHϕ; [ | inversion_clear EV]; eauto).
      { inversion_clear EV.
        simpl in *; decide (x = v) as [EQ|NEQ];
          [subst; apply (todo2 _ _ _ _ H) in M; subst| ]; auto. }
      { simpl in *; decide (x = v) as [EQ|NEQ]; [subst; inversion_clear EV| ]; auto. }
    Qed. 
  
    Lemma todo77:
      forall (ϕ : formula) (x : variable) (α : assignment) (b : bool),
        x / α ↦ false ->
        ℇ (ϕ) α ≡ b <-> ℇ (ϕ [x ↦ F]) α ≡ b.
    Proof.
      intros ϕ; induction ϕ; intros x α b M; split; intros EV.
      all: try(inversion_clear EV; constructor; fail).
      all: try(inversion_clear EV; simpl;
               [ eapply ev_conj_t; [eapply IHϕ1|eapply IHϕ2]
               | eapply ev_conj_fl; eapply IHϕ1
               | eapply ev_conj_fr; eapply IHϕ2]; eauto).
      all: try(inversion_clear EV; simpl;
               [ eapply ev_disj_f; [eapply IHϕ1|eapply IHϕ2]
               | eapply ev_disj_tl; eapply IHϕ1
               | eapply ev_disj_tr; eapply IHϕ2]; eauto).
      all: try(simpl; constructor; eapply IHϕ; [ | inversion_clear EV]; eauto).
      { inversion_clear EV.
        simpl in *; decide (x = v) as [EQ|NEQ];
          [subst; apply (todo2 _ _ _ _ H) in M; subst| ]; auto. }
      { simpl in *; decide (x = v) as [EQ|NEQ]; [subst; inversion_clear EV| ]; auto. }
    Qed. 

    
    Lemma switch:
      forall (ϕ : formula) (x : variable) (α : assignment) (b : bool),
        x el vars_in α ->
        ℇ (ϕ) α ≡ b <-> ℇ ([|x|] ∧ ϕ[x ↦ T] ∨ ¬[|x|] ∧ ϕ[x ↦ F]) α ≡ b.
    Proof.
      intros ϕ ? ? ? SET.
      destruct (mapsto_dec _ _ SET); destruct b; split; intros EV.
      - apply ev_disj_tl; constructor; [ |apply todo76]; auto.
      - inversion_clear EV; inversion_clear H.
        + apply <-todo76; eauto.
        + exfalso; clear H1.
          inversion_clear H0; inversion_clear H.
          apply (todo2 _ _ _ _ m) in H0; inversion H0.
      - eapply todo76 in EV; eauto; constructor;
          [apply ev_conj_fr|apply ev_conj_fl]; auto.
      - eapply todo76; eauto.
        inversion_clear EV; inversion_clear H0; inversion_clear H; try assumption.
        + inversion_clear H1; apply (formula_eval_inj _ _ _ _ H) in H0; inversion H0.
        + inversion_clear H0; apply (todo2 _ _ _ _ H) in m; inversion m.
      - apply ev_disj_tr; constructor; [ |apply todo77]; auto.
      - inversion_clear EV; inversion_clear H.
        + exfalso; clear H1.
          inversion_clear H0.
          apply (todo2 _ _ _ _ m) in H; inversion H.
        + apply <-todo77; eauto.
      - eapply todo77 in EV; eauto. 
      - eapply todo77; eauto.
        inversion_clear EV; inversion_clear H0; inversion_clear H; try assumption.
        + inversion_clear H1; apply (formula_eval_inj _ _ _ _ H) in H0; inversion H0.
        + inversion_clear H1; inversion_clear H; apply (todo2 _ _ _ _ H1) in m; inversion m.
    Qed.


    Variable ϕ : formula.
    
    Variable x : variable.
    Hypothesis H_leaf : x el leaves ϕ.

    Variables αs1 αs2 : assignments.
    
    
    Lemma todo54:
      dupfree (leaves (ϕ [x ↦ T])) αs1 ->
      dupfree (leaves (ϕ [x ↦ F])) αs2 ->
      dupfree (leaves ϕ) (map (cons (x, true)) αs1 ++ map (cons (x, false)) αs2).
    Proof.
      intros [ND1 NE1] [ND2 NE2].
      split.
      { apply dfnn_ext; [ | assumption | assumption].
        intros F; inversion_clear F.
      }
      { intros α1 α2 EL1 EL2 EQ NEQ. 
        apply in_app_iff in EL1; apply in_app_iff in EL2.
        destruct EL1 as [EL1|EL1], EL2 as [EL2|EL2]. 
        { apply in_map_iff in EL1; destruct EL1 as [β1 [EQ1 EL1]].
          apply in_map_iff in EL2; destruct EL2 as [β2 [EQ2 EL2]]; subst α1 α2.
          specialize (NE1 _ _ EL1 EL2).
          feed NE1; [intros C; apply EQ; rewrite C; reflexivity | ].
          apply NE1; clear NE1.
          apply todo28 with (vs_sub := leaves (ϕ [x ↦ T])) in NEQ;
            [assumption | apply todo57 | apply todo12].
        }
        { apply in_map_iff in EL1; apply in_map_iff in EL2.
          destruct EL1 as [α1_tl [EQ1 _]], EL2 as [α2_tl [EQ2 _]]; subst α1 α2.
          specialize (NEQ x H_leaf true); destruct NEQ as [NEQ _]; feed NEQ; auto.
          inversion_clear NEQ; auto.
        }
        { apply in_map_iff in EL1; apply in_map_iff in EL2.
          destruct EL1 as [α1_tl [EQ1 _]], EL2 as [α2_tl [EQ2 _]]; subst α1 α2.
          specialize (NEQ x H_leaf true); destruct NEQ as [_ NEQ]; feed NEQ; auto.
          inversion_clear NEQ; auto.
        }
        { apply in_map_iff in EL1; destruct EL1 as [β1 [EQ1 EL1]].
          apply in_map_iff in EL2; destruct EL2 as [β2 [EQ2 EL2]]; subst α1 α2.
          specialize (NE2 _ _ EL1 EL2).
          feed NE2; [intros C; apply EQ; rewrite C; reflexivity | ].
          apply NE2; clear NE2.
          apply todo28 with (vs_sub := leaves (ϕ [x ↦ F])) in NEQ;
            [assumption | apply todo58 | apply todo14].
        }
      }
    Qed.

    (* Note that it is not a brute-force. *)
    Lemma todo55:
      set_with_sat_assignments (ϕ[x ↦ T]) αs1 -> 
      set_with_sat_assignments (ϕ[x ↦ F]) αs2 -> 
      set_with_sat_assignments
        ϕ (map (cons (x, true)) αs1 ++ map (cons(x, false)) αs2).
    Proof.
      intros SAT1 SAT2; intros α ELt; split.
      { apply in_app_iff in ELt; destruct ELt as [EL|EL]; apply in_map_iff in EL;
          destruct EL as [α_tl [EQ EL]]; subst α.
        - intros v IN.
          decide (x = v) as [EQ|NEQ]; subst.
          + left; reflexivity.
          + specialize (SAT1 α_tl EL); destruct SAT1 as [SET1 _].
            right; apply SET1, todo73; auto.
        - intros v IN.
          decide (x = v) as [EQ|NEQ]; subst.
          + left; reflexivity.
          + specialize (SAT2 α_tl EL); destruct SAT2 as [SET2 _].
            right; apply SET2, todo74; auto.     
      }
      apply switch with x.
      { apply in_app_iff in ELt; destruct ELt as [EL|EL]; apply in_map_iff in EL;
          destruct EL as [α_tl [EQ EL]]; subst α; simpl; left; reflexivity. }
      apply in_app_or in ELt; destruct ELt as [EL|EL].
      { apply ev_disj_tl, ev_conj_t.
        { apply in_map_iff in EL.
          destruct EL as [mα [EQ1 MEM1]]; subst α; auto.
        } 
        { apply in_map_iff in EL.
          destruct EL as [mα [EQ MEM]]; subst α.
          apply admit_todo13.
          apply todo12.
          apply SAT1; assumption.
        }
      }
      { apply ev_disj_tr, ev_conj_t.
        { apply in_map_iff in EL.
          destruct EL as [mα [EQ MEM]]; subst α; auto.
        }
        { apply in_map_iff in EL.
          destruct EL as [mα [EQ MEM]]; subst α.
          apply admit_todo13. apply todo14.
          apply SAT2; assumption.
        }
      }
    Qed.
    
    Lemma todo56:
      set_with_all_sat_assignments (ϕ [x ↦ T]) αs1 -> 
      set_with_all_sat_assignments (ϕ [x ↦ F]) αs2 -> 
      set_with_all_sat_assignments
        ϕ (map (cons (x, true)) αs1 ++ map (cons (x, false)) αs2).
    Proof.
      intros SET1 SET2. 
      intros α [SETS SAT].
      apply (switch _ x _ _ (SETS x H_leaf)) in SAT.
      inversion_clear SAT; inversion_clear H.
      { specialize (SET1 α); feed SET1.
        { split; [apply todo71| ]; auto. } 
        destruct SET1 as [β [EQ EL]].
        inversion_clear H0. 
        exists ((x,true)::β); split.
        { intros v ELl b.
          decide (v = x) as [E|NEQ]; [subst | ]; split; intros EV.
          - apply (todo2 _ _ _ _ H) in EV; subst; constructor.
          - inversion_clear EV; [ | exfalso]; auto.
          - constructor; [assumption| ]; apply EQ; [ | assumption]; auto using todo73.
          - inversion_clear EV; [assumption| ]; apply EQ; auto using todo73.
        }
        { apply in_app_iff; left.
          apply in_map_iff; exists β; easy.
        }
      }
      { specialize (SET2 α); feed SET2.
        { split; [apply todo72| ]; auto. }
        destruct SET2 as [β [EQ EL]].
        inversion_clear H0; inversion_clear H; simpl in H0.
        exists ((x,false)::β); split.
        { intros v ELl b.
          decide (v = x) as [E|NEQ]; [subst | ]; split; intros EV.
          - apply (todo2 _ _ _ _ H0) in EV; subst; constructor.
          - inversion_clear EV; [ | exfalso]; auto.
          - constructor; [assumption| ]; apply EQ; [ | assumption]; auto using todo74.
          - inversion_clear EV; [assumption| ]; apply EQ; auto using todo74.
        }
        { apply in_app_iff; right.
          apply in_map_iff; exists β; easy.
        }
      } 
    Qed. 
    
  End InductionStep.
  
  Definition algorithm2 (ϕ : formula): {n : nat | number_of_sat_assignments ϕ n}.
  Proof.
    generalize dependent ϕ.
    apply size_recursion with formula_size; intros ϕ IHϕ. 
    destruct (formula_size_dec ϕ) as [Zero|Pos].
    { destruct (zero_size_formula_constant_dec ϕ Zero) as [Tr|Fl].
      - exists 1; apply count5; assumption.
      - exists 0; apply count6; assumption. } 
    { assert (V := get_var _ Pos).
      destruct V as [x IN]; clear Pos.
      assert (IH1 := IHϕ (ϕ[x ↦ T])); assert(IH2 := IHϕ (ϕ[x ↦ F])); clear IHϕ.
      specialize (IH1 (todo3 _ _ IN)); specialize (IH2 (todo5 _ _ IN)).
      destruct IH1 as [nl EQ1], IH2 as [nr EQ2].
      exists (nl + nr).
      destruct EQ1 as [αs1 [LAA1 LEN1]], EQ2 as [αs2 [LAA2 LEN2]].
      exists (map (fun α => (x, true)::α) αs1 ++ map (fun α => (x,false)::α) αs2).
      split; [split; [ | split] | ].
      { destruct LAA1 as [ND1 _], LAA2 as [ND2 _]; apply todo54; auto. }
      { destruct LAA1 as [_ [SAT1 _]], LAA2 as [_ [SAT2 _]]; apply todo55; auto. }
      { destruct LAA1 as [_ [_ SET1]], LAA2 as [_ [_ SET2]];apply todo56; assumption. } 
      { rewrite app_length, map_length, map_length, <- LEN1, <- LEN2; reflexivity. } 
    }
  Defined.
  
  (* => 32 *)
  (* Compute (proj1_sig (algorithm2 (fold_left (fun ϕ x => ϕ ⊕ [|V x|]) ([1;2;3;4;5;6;7;8;9]) F))). *)
  (* Compute (proj1_sig (algorithm1 (x0 ⊕ x1 ⊕ x2 ⊕ x3 ⊕ x4 ⊕ x5 ⊕ x6 ⊕ x7))).
  Compute (proj1_sig (algorithm2 (x0 ⊕ x1 ⊕ x2 ⊕ x3 ⊕ x4 ⊕ x5 ⊕ x6 ⊕ x7))). *)

End Algorithm2.

(** * "Bonus" 1: Counting k-Cliques. *)
(** This "bonus" gives nothing significant. The only reason I include this section is 
    to see the performance of the algorithms on real formulas. *)
Section kCliques.

  (* TODO: check *)
  (* Full proof of the correctness seems quite difficult, since one has to: 
     0) define the notion of a graph
     1) define the notion of clique 
     2) define the notion of the number of k-cliques
     3) construct a reduction k-Clique problem to formula satisfiability problem
     4) show that this reduction respects the number of cliques!
        (i.e., the standart reduction for decision problems doesn't work). *)
  
  (* Considering the foregoing, I won't prove any properties of the reduction.
     I'll use the problem of counting the k-cliques as a "generator" of 
     nontrivial boolean formulas. *)

  (* Mostly, the resulting formulas TODO very big (200+ leaves), so evaluation 
     does take looong time. However, for small examples I was able to count TODO *)

  Record graph :=
    { vtcs : list nat; 
      edges : nat -> nat -> bool;
(*    arefl : rel_list_antirefl vtcs edges *)
(*    sym : rel_list_sym vtcs edges        *)
    }.

  Definition cart_prod {X : Type} (xs ys : list X) : list (X * X) :=
    flat_map (fun x => map (fun y => (x,y)) ys) xs.

  Definition lt_pairs (xs : list nat) : list (nat * nat) :=
    filter (fun '(x,y) => if lt_dec x y then true else false) (cart_prod xs xs).

  Definition le_pairs (xs : list nat) : list (nat * nat) :=
    filter (fun '(x,y) => if le_dec x y then true else false) (cart_prod xs xs).

  Definition neq_pairs (xs : list nat) : list (nat * nat) :=
    filter (fun '(x,y) => if nat_eq_dec x y then false else true) (cart_prod xs xs).
  
  Fixpoint range (l r : nat): list nat :=
    match l,r with
    | 0,0 => [0]
    | l,S r => if le_dec l (S r) then range l r ++ [S r] else []
    | _,_ => []
    end.

  Definition transform (k : nat) (g : graph) : formula :=
    (* Extract vertices and edges from graph. *)
    let '(Vs, Es) :=
        match g with
          {| vtcs := vtcs; edges := edges |} =>
          (vtcs, edges)
        end in

    (* Pick at least one vertex from each group. *)
    let r1 : formula :=
        fold_left
          Conj
          (map (fun k =>
                  fold_left
                    Disj
                    (map (fun v => [|V (100 * k + v)|]) Vs)
                    F
               )
               (range 0 (k-1)))
          T in

    (* Pick at most one vertext from each group. *)
    let r2 :=
        fold_left
          Conj 
          (flat_map
             (fun k =>
                map
                  (fun '(v1,v2) => ¬[|V (100 * k + v1) |] ∨ ¬ [|V (100 * k + v2) |])
                  (lt_pairs Vs)
             )
             (range 0 (k-1)))
          T in

    (* Can't pick TODO *)
    let r3 : formula :=
        fold_left
          Conj 
          (map
             (fun '(k1,k2) =>
                fold_left
                  Conj 
                  (map (fun v => ¬ [|V (100 * k1 + v)|] ∨ ¬ [|V (100 * k2 + v)|]) Vs)
                  T
             )
             (lt_pairs (range 0 (k-1))))
          T in 

    (* In order to count each clique only once, I introduce an ordering
       on the vertices. TODO *) 
    let r4 : formula :=
        fold_left
          Conj 
          (map
             (fun '(v1,v2) =>
                fold_left
                  Conj
                  (map
                     (fun '(k1,k2) => ¬[|V (100 * k1 + v2)|] ∨ ¬[|V (100 * k2 + v1)|])
                     (lt_pairs (range 0 (k-1))))
                    T
             )
             (lt_pairs Vs))
          T in

    (* TODO: *)
    let r5 : formula :=
        fold_left
          Conj 
          (flat_map
             (fun '(v1,v2) =>
                if Es v1 v2
                then []
                else map
                       (fun '(k1,k2) =>  ¬[|V (100 * k1 + v1)|] ∨ ¬[|V (100 * k2 + v2)|])
                       (neq_pairs (range 0 (k-1))))
             (lt_pairs Vs))
          T in
    r1 ∧ r2 ∧ r3 ∧ r4 ∧ r5.

  Definition counting_k_cliques (k : nat) (g : graph) :=
    proj1_sig (algorithm2 (transform k g)).
  
  Definition graph1 :=
    {| vtcs := [1;2;3;4];
       edges v1 v2 :=
         match v1, v2 with
         | 1,2 | 2,1 => true
         | 1,3 | 3,1 => true
         | 2,3 | 3,2 => true
         | 1,4 | 4,1 => true 
         | _, _ => false
         end;
    |}.
  
  Definition graph_triangle :=
    {| vtcs := [1;2;3];
       edges v1 v2 :=
         match v1, v2 with
         | 1,2 | 2,1 => true
         | 1,3 | 3,1 => true
         | 2,3 | 3,2 => true
         | _, _ => false
         end;
    |}.

  Definition graph_4_clique :=
    {| vtcs := [1;2;3;4];
       edges v1 v2 :=
         match v1, v2 with
         | 1,2 | 2,1 => true
         | 1,3 | 3,1 => true
         | 1,4 | 4,1 => true
         | 2,3 | 3,2 => true
         | 2,4 | 4,2 => true
         | 3,4 | 4,3 => true
         | _, _ => false
         end;
    |}.
  

  (* TODO: spelling? *)
    Definition graph_pentagram :=
    {| vtcs := [1;2;3;4;5];
       edges v1 v2 :=
         match v1, v2 with
         | 1,2 | 2,1 => true
         | 1,3 | 3,1 => true
         | 1,4 | 4,1 => true
         | 1,5 | 5,1 => true

         | 2,3 | 3,2 => true
         | 2,4 | 4,2 => true
         | 2,5 | 5,2 => true

         | 3,4 | 4,3 => true
         | 3,5 | 5,3 => true

         | 4,5 | 5,4 => true
                         
         | _, _ => false
         end;
    |}.

    
    (* Compute ( (transform 3 graph_pentagram)). *)
    Compute (counting_k_cliques 3 graph_triangle).
(*  Compute (counting_k_cliques 3 graph1).

    Compute (counting_k_cliques 3 graph_pentagram).
    Compute (counting_k_cliques' 3 graph_pentagram). *)
        
    
      
 
  
    
End kCliques.


(** * Bonus 2: A (failed) attempt to come up with a third algorithm. *)
  (* Algorithm
   1) Transform ϕ to dnf
   2) Map each monomial into a certificate1
   3) By construction, all these certificates are disjoint
   4) Calculate the number of sat. assignments
   *)
(** With certificates and DNF *)
Section Algorithm3.
  
  Section Literal.

    Inductive literal :=
    | Positive: variable -> literal
    | Negative: variable -> literal.

    Inductive literal_eval: literal -> assignment -> bool -> Prop :=
    | lit_ev_pos: forall (v: variable) (α: assignment) (b: bool),
        (v/α ↦ b) -> literal_eval (Positive v) α b
    | lit_ev_neg: forall (v: variable) (α: assignment) (b: bool),
        (v/α ↦ (negb b)) -> literal_eval (Negative v) α b.
  
    
    Lemma admit_todo47:
      forall (α : assignment) (l : literal) (b1 b2 : bool),
        literal_eval l α b1 ->
        literal_eval l α b2 ->
        b1 = b2.
    Proof.
      intros ? ? ? ? M1 M2.
    Admitted.
    
    Corollary todo48:
      forall (α : assignment) (l : literal),
        literal_eval l α true ->
        literal_eval l α false ->
        False.
    Proof.
      intros ? ? EV1 EV2; assert (F := admit_todo47 _ _ _ _ EV1 EV2); easy.
    Qed.
    
  End Literal.

  Hint Constructors literal_eval.
  
  
  Section Monomial.
    
    Definition monomial := list literal.
    
    Inductive monomial_eval: monomial -> assignment -> bool -> Prop :=
    | mon_ev_true: forall (m: monomial) (α: assignment),
        (forall (l: literal), l el m -> literal_eval l α true) -> 
        monomial_eval m α true
    | mon_ev_false: forall (m: monomial) (α: assignment),
        (exists (l: literal), l el m /\ literal_eval l α false) -> 
        monomial_eval m α false.


    (* TODO: comment *)
    Definition monomial_sat_assignment (m: monomial) (α: assignment) :=
      monomial_eval m α true.

    (* TODO: comment *)
    Definition monomial_satisfiable (m: monomial) :=
      exists (α: assignment), monomial_sat_assignment m α.


    (* TODO: comment *)
    Definition monomial_unsat_assignment (m: monomial) (α: assignment) :=
      monomial_eval m α false.

    (* TODO: comment *)
    Definition monomial_unsatisfiable (m: monomial) :=
      forall (α: assignment), monomial_unsat_assignment m α.


    
    Global Instance admit_mon_eq_dec:
      eq_dec monomial.
    Proof.
      intros.    
    Admitted.

    Lemma todo49:
      forall (α : assignment) (m : monomial),
        (forall l, l el m -> literal_eval l α true)
        \/ (exists l, l el m /\ forall b, ~ literal_eval l α b)
        \/ (exists l, l el m /\ literal_eval l α false).
    Proof.
      clear; intros; induction m.
      left; intros l EL; inversion EL.      
      destruct IHm as [IH|[IH|IH]].
      { destruct a; destruct (todo22 α v) as [[[V H]|[V H]]|[V H]].
        - left; intros l EL; destruct EL as [EQ|IN]; subst; auto.
        - right; left; exists (Positive v); split; [left| ]; auto.
          intros b EV; inversion_clear EV.
          eauto using todo21.
        - right; right; exists (Positive v); split; [left| ]; auto.
        - right; right; exists (Negative v); split; [left| ]; auto.
        - right; left; exists (Negative v); split; [left| ]; auto.
          intros b EV; inversion_clear EV.
          eauto using todo21.
        - left; intros l EL; destruct EL as [EQ|IN]; subst; auto. 
      }     
      { destruct IH as [l [EL NE]].
        right; left.
        exists l; split; [right | ]; auto.  
      }
      { destruct IH as [l [EL NE]].
        right; right.
        exists l; split; [right | ]; auto.  
      }
    Qed. 

  End Monomial.

  Section DNF.
    
    Definition dnf := list monomial.

    Inductive dnf_eval: dnf -> assignment -> bool -> Prop :=
    | dnf_ev_true: forall (d: dnf) (α: assignment),
        (exists (m: monomial), m el d /\ monomial_eval m α true) -> 
        dnf_eval d α true
    | dnf_ev_false: forall (d: dnf) (α: assignment),
        (forall (m: monomial), m el d -> monomial_eval m α false) -> 
        dnf_eval d α false.

    (* TODO: comment *)
    Definition dnf_representation (ϕ: formula) (ψ: dnf) :=
      forall (α: assignment) (b: bool),
        formula_eval ϕ α b <-> dnf_eval ψ α b.
    
    (* *)
    Definition equivalent_dnf (ψ1 ψ2: dnf) :=
      forall (α: assignment) (b: bool),
        dnf_eval ψ1 α b <-> dnf_eval ψ2 α b.  

    
    Lemma admit_tr_eq_rep:
      forall (ϕ1 ϕ2: formula) (ψ: dnf), 
        equivalent ϕ1 ϕ2 ->
        dnf_representation ϕ2 ψ ->
        dnf_representation ϕ1 ψ.
    Proof.
    Admitted.

    Lemma admit_tr_eq_rep_2:
      forall (ϕ : formula) (ψ1 ψ2 : dnf),
        equivalent_dnf ψ1 ψ2 ->
        dnf_representation ϕ ψ1 ->
        dnf_representation ϕ ψ2.
    Proof.
    Admitted.
    

    Lemma todo15:
      forall (ϕ1 ϕ2: formula), 
        equivalent ϕ1 ϕ2 -> 
        {ψ : dnf | dnf_representation ϕ1 ψ} ->
        {ψ : dnf | dnf_representation ϕ2 ψ}.
    Proof.
      intros ? ? EQ REP.
      destruct REP as [ψ REP].
      exists ψ; apply admit_tr_eq_rep with ϕ1; auto.
      apply formula_equivalence_sym; assumption.
    Qed.


    Lemma admit_todo50:
      forall (α : assignment) (ψ : dnf),
        (forall m, m el ψ -> monomial_unsat_assignment m α) \/
        (exists m, m el ψ /\ forall b, ~ monomial_eval m α b) \/
        (exists m, m el ψ /\ monomial_sat_assignment m α).
    Proof.
      intros.
      induction ψ.
      left. intros . inversion_clear H.
      
      destruct IHψ as [IH|[IH|IH]]. 
      { destruct (todo49 α a) as [H|[H|H]].
        
        admit.
        admit.
        left.
        admit.
      }
      { admit. }
      { admit. }
    Admitted.
    
    
  End DNF.

  Section FormulaToDNF.

    (* TODO: comment *)
    Fixpoint bottom_negations (ϕ: formula): Prop :=
      match ϕ with
      | T | F | [|_|] | ¬ [|_|]=> True
      | ϕl ∧ ϕr => bottom_negations ϕl /\ bottom_negations ϕr
      | ϕl ∨ ϕr => bottom_negations ϕl /\ bottom_negations ϕr
      | ¬ _ => False
      end.

    (* TODO: comment *)
    Definition move_negations (ϕ: formula):
      {neg_ϕ : formula | equivalent ϕ neg_ϕ
                         /\ bottom_negations neg_ϕ }.
    Proof.
      generalize dependent ϕ. 
      apply size_recursion with number_of_nodes; intros ϕ IH.
      destruct ϕ.
      { (* move_negations F := F. *)
        exists F; split.
        - apply formula_equivalence_refl.
        - constructor.
      }
      { (* move_negations T := T. *)
        exists T; split.
        - apply formula_equivalence_refl.
          - constructor.
        }
        { (* move_negations [|v|] := [|v|]. *)
          exists [|v|]; split.
          - apply formula_equivalence_refl.
          - constructor.
        }
        { destruct ϕ.
          { (* move_negations (¬F) := T. *)
            exists T; split. 
            - apply formula_equivalence_sym;
                apply formula_equivalence_T_neg_F.
            - constructor.
          }
          { (* move_negations (¬T) := F. *)
            exists F; split.
            - apply formula_equivalence_move_negation;
                apply formula_equivalence_T_neg_F.
            - constructor.
          }
          { (* move_negations (¬[|v|]) := ¬ [|v|]. *)
            exists (¬ [|v|]); split.
            - apply formula_equivalence_refl.
            - constructor.
          }
          { (* move_negations (¬ ¬ ϕ) := move_negations ϕ. *)
            assert (IH1 := IH ϕ); feed IH1; [simpl; omega| clear IH].
            destruct IH1 as [neg_ϕ [EQ LIT]].
            exists neg_ϕ; split.
            - apply formula_equivalence_move_negation.
              apply ->formula_equivalence_negate_both_sides; assumption.
            - assumption.
          }
          { (* move_negations (¬(ϕl ∧ ϕr)) := move_negations ϕl ∨ move_negations ϕr. *)
            assert (IH1 := IH (¬ ϕ1)); feed IH1; [simpl; omega| ].
            assert (IH2 := IH (¬ ϕ2)); feed IH2; [simpl; omega| clear IH].
            destruct IH1 as [neg_ϕ1 [EQ1 BOT1]], IH2 as [neg_ϕ2 [EQ2 BOT2]].
            exists (neg_ϕ1 ∨ neg_ϕ2); split. 
            - apply formula_equivalence_move_negation, admit_fo_eq_5.
              apply ->formula_equivalence_negate_both_sides; apply fo_eq_11; assumption.
            - split; assumption.     
          }
          { (* move_negations (¬(ϕl ∨ ϕr)) := move_negations ϕl ∧ move_negations ϕr. *)
            assert (IH1 := IH (¬ ϕ1)); feed IH1; [simpl; omega| ].
            assert (IH2 := IH (¬ ϕ2)); feed IH2; [simpl; omega| ].
            destruct IH1 as [neg_ϕ1 [EQ1 BOT1]], IH2 as [neg_ϕ2 [EQ2 BOT2]].
            exists (neg_ϕ1 ∧ neg_ϕ2); split.
            - apply formula_equivalence_move_negation, admit_fo_eq_6.
              apply ->formula_equivalence_negate_both_sides; apply fo_eq_1; assumption. 
            - split; assumption.
          }   
        }
        { (* move_negations (ϕl ∧ ϕr) := move_negations ϕl ∧ move_negations ϕr. *)
          assert (IH1 := IH ϕ1); feed IH1; [simpl; omega| ].
          assert (IH2 := IH ϕ2); feed IH2; [simpl; omega| ].
          destruct IH1 as [neg_ϕ1 [EQ1 BOT1]], IH2 as [neg_ϕ2 [EQ2 BOT2]].
          exists (neg_ϕ1 ∧ neg_ϕ2); split.
          - apply fo_eq_1; assumption. 
          - split; assumption.
        }
        { (* move_negations (ϕl ∨ ϕr) := move_negations ϕl ∨ move_negations ϕr. *)
          assert (IH1 := IH ϕ1); feed IH1; [simpl; omega| ].
          assert (IH2 := IH ϕ2); feed IH2; [simpl; omega| ].
          destruct IH1 as [neg_ϕ1 [EQ1 BOT1]], IH2 as [neg_ϕ2 [EQ2 BOT2]].
          exists (neg_ϕ1 ∨ neg_ϕ2); split.
          - apply fo_eq_11; assumption.
          - split; assumption.
        }
      Qed.

      (* Compute (proj1_sig (move_negations (¬ (x0 ∨ x1) ∧ (x2 ∨ x3)))). *)

      Lemma dnf_representation_of_T:
        dnf_representation T [[]].   
      Proof.
        split; intros EV.
        { inversion_clear EV.
          constructor; intros.
          exists []; split.
          - left; reflexivity.
          - constructor.
            intros; inversion_clear H.
        }
        { inversion_clear EV.
          - constructor.
          - exfalso.
            specialize (H ([])); feed H; [left; auto | ].
            inversion_clear H. 
            destruct H0 as [t  [IN EV]].
            inversion_clear IN.
        } 
      Qed.

      Lemma dnf_representation_of_F:
        dnf_representation F [].   
      Proof.
        split; intros EV.
        { inversion_clear EV.
          constructor; intros.
          inversion_clear H.
        }
        { inversion_clear EV.
          - destruct H as [m [IN EV]]; inversion_clear IN.
          - constructor.
        } 
      Qed.

      Lemma dnf_representation_of_var:
        forall (v : variable),
          dnf_representation [|v|] [[Positive v]].   
      Proof.
        intros; split; intros EV.
        { inversion_clear EV.
          destruct b; constructor.
          { exists [Positive v]; split.
            - left; reflexivity.
            - constructor; intros lit EL.
              apply singl_in in EL; subst.
              constructor; assumption.
          }
          { intros m EL.
            apply singl_in in EL; subst.
            constructor; exists (Positive v); split.
            - left; reflexivity.
            - constructor; assumption.
          }
        } 
        { constructor.
          inversion_clear EV.
          { destruct H as [m [EL MON]].
            apply singl_in in EL; subst.
            inversion_clear MON.
            specialize (H (Positive v)); feed H; [left; auto | ].
            inversion_clear H; assumption.
          }
          { specialize (H ([Positive v])); feed H; [left; auto | ].
            inversion_clear H; destruct H0 as [lit [EL F]]. 
            apply singl_in in EL; subst.
            inversion_clear F; assumption.
          }
        }
      Qed.

      Lemma dnf_representation_of_neg_var:
        forall (v: variable),
          dnf_representation (¬[|v|]) [[Negative v]].   
      Proof.
        intros; split; intros EV.
        { inversion_clear EV; inversion_clear H.
          destruct b; constructor.
          { exists [Negative v]; split.
            - left; reflexivity.
            - constructor; intros lit EL.
              apply singl_in in EL; subst.
              constructor; assumption.
          }
          { intros m EL.
            apply singl_in in EL; subst.
            constructor; exists (Negative v); split.
            - left; reflexivity.
            - constructor; assumption.
          }
        } 
        { constructor; constructor.
          inversion_clear EV.
          { destruct H as [m [EL MON]].
            apply singl_in in EL; subst.
            inversion_clear MON.
            specialize (H (Negative v)); feed H; [left; auto | ].
            inversion_clear H; assumption.
          }
          { specialize (H ([Negative v])); feed H; [left; auto | ].
            inversion_clear H; destruct H0 as [lit [EL F]]. 
            apply singl_in in EL; subst.
            inversion_clear F; assumption.
          }
        }
      Qed.

      Section And.
        
        (* TODO: comment *)
        Definition flat_product {X: Type} (xs ys: list (list X)):list(list X) :=
          flat_map (fun (y:list X) =>
                      map (fun (x: list X) => x ++ y) xs) ys.

        (* => [[x0;x1; x4;x5]; [x2;x3; x4;x5]; [x0;x1; x6;x7]; [x2;x3; x6;x7]] *)
        (* Compute (flat_product ([[x0;x1];[x2;x3]]) ([[x4;x5];[x6;x7]])). *)

        Lemma todo43:
          forall (X : Type) (xss yss : list (list X)) (xs ys : list X),
            xs el xss ->
            ys el yss ->
            xs ++ ys el flat_product xss yss.
        Proof.
          intros ? ? ? ? ? EL1 EL2.
          induction xss.
          { destruct EL1. }
          { destruct EL1 as [EQ|EL1]; subst.
            { clear IHxss; apply in_flat_map.
              exists ys; split; [ | left]; auto. }
            { feed IHxss; auto.
              apply in_flat_map in IHxss; destruct IHxss as [ys' [EL MAP]].
              apply in_flat_map; exists ys'; split; [ | right]; auto. }
          } 
        Qed.

        Lemma todo44:
          forall (X : Type) (xss yss : list (list X)) (zs : list X),
            zs el flat_product xss yss ->
            exists xs ys, xs ++ ys = zs /\ xs el xss /\ ys el yss.
        Proof.
          intros ? ? ? ? EL.
          induction xss.
          { apply in_flat_map in EL; destruct EL as [? [? H]]; destruct H. }
          { apply in_flat_map in EL; destruct EL as [ys [EL MAP]].
            destruct MAP as [EQ|MAP].
            { subst zs; exists a, ys; repeat split; [left;reflexivity| assumption]. }
            { feed IHxss; [apply in_flat_map; exists ys; split; assumption| ]. 
              destruct IHxss as [xs' [ys' [EQ [EL1 EL2]]]].
              exists xs', ys'; repeat split; [ |right| ]; assumption.
            }
          }
        Qed.

        Lemma dnf_representation_of_and:
          forall (ϕl ϕr: formula) (ψl ψr: dnf),
            dnf_representation ϕl ψl ->
            dnf_representation ϕr ψr ->
            dnf_representation (ϕl ∧ ϕr) (flat_product ψl ψr).
        Proof.
          intros ? ? ? ? REP1 REP2; split; intros EV.
          { inversion_clear EV.
            { apply REP1 in H; apply REP2 in H0; clear REP1 REP2.
              inversion_clear H; inversion_clear H0; rename H into MR, H1 into ML.
              destruct ML as [ml [ELl Ml]], MR as [mr [ELr Mr]].
              constructor; exists (ml ++ mr); split.
              - apply todo43; assumption.
              - inversion_clear Ml; inversion_clear Mr; rename H into Ml, H0 into Mr.
                constructor; intros lit EL; apply in_app_iff in EL; destruct EL as [EL|EL]; eauto. 
            }
            { apply REP1 in H; clear REP1 REP2.
              inversion_clear H; rename H0 into MF.
              constructor; intros m EL.
              apply todo44 in EL; destruct EL as [ml [mr [EQ [EL1 EL2]]]]; subst m.
              specialize (MF ml EL1); inversion_clear MF; destruct H as [lit [EL EV]].
              constructor; exists lit; split; [apply in_app_iff;left | ]; auto.
            }
            { apply REP2 in H; clear REP1 REP2.
              inversion_clear H; rename H0 into MF.
              constructor; intros m EL.
              apply todo44 in EL; destruct EL as [ml [mr [EQ [EL1 EL2]]]]; subst m.
              specialize (MF mr EL2); inversion_clear MF; destruct H as [lit [EL EV]].
              constructor; exists lit; split; [apply in_app_iff;right | ]; auto.
            }        
          }
          { inversion_clear EV.
            { destruct H as [mon [FL EV]].
              apply todo44 in FL; destruct FL as [ml [mr [EQ [ELl ELr]]]]; subst.
              inversion_clear EV; rename H into EL.
              constructor; [apply REP1|apply REP2]; constructor;
                [exists ml|exists mr]; split; auto; constructor; intros lit ELlit;
                  apply EL; apply in_app_iff; [left|right]; auto.
            }
            { destruct (admit_todo50 α ψl) as [EVl|[EVl|EVl]], (admit_todo50 α ψr) as [EVr|[EVr|EVr]].
              all: try(apply ev_conj_fl; apply REP1; constructor; assumption).
              all: try(apply ev_conj_fr; apply REP2; constructor; assumption).
              all: exfalso.
              all: destruct EVl as [ml [ELl Fl]], EVr as [mr [ELr Fr]].
              all: specialize (H _ (todo43 _ _ _ _ _ ELl ELr)).
              all: inversion_clear H.
              all: destruct H0 as [l [EL LIT]].
              all: apply in_app_iff in EL; destruct EL as [EL|EL].
              all: try(apply Fl with false; constructor; exists l; split; assumption).
              all: try(apply Fr with false; constructor; exists l; split; assumption).
              all: try(inversion_clear Fr; specialize (H _ EL); eauto using todo48). 
              all: try(inversion_clear Fl; specialize (H _ EL); eauto using todo48). 
            }
          }
        Qed.

      End And.
      
      Lemma dnf_representation_of_or:
        forall (ϕl ϕr : formula) (ψl ψr : dnf),
          dnf_representation ϕl ψl ->
          dnf_representation ϕr ψr ->
          dnf_representation (ϕl ∨ ϕr) (ψl ++ ψr).
      Proof.
        intros ? ? ? ? REP1 REP2; split; intros EV.
        { inversion_clear EV.
          { apply REP1 in H; apply REP2 in H0; clear REP1 REP2.
            inversion_clear H; inversion_clear H0; rename H into MR, H1 into ML.
            constructor; intros mon EL.
            apply in_app_iff in EL; destruct EL as [EL|EL]; auto.
          }
          { apply REP1 in H; clear REP1 REP2.
            inversion_clear H; destruct H0 as [m [EL MON]].
            constructor; exists m; split.
            - apply in_or_app; left; assumption.
            - assumption. }
          { apply REP2 in H; clear REP1 REP2.
            inversion_clear H; destruct H0 as [m [EL MON]].
            constructor; exists m; split.
            - apply in_or_app; right; assumption.
            - assumption. }
        }
        { inversion_clear EV.
          destruct H as [m [EL MON]]; apply in_app_iff in EL; destruct EL as [EL|EL];
            [apply ev_disj_tl; apply REP1 | apply ev_disj_tr; apply REP2];
            constructor; exists m; split; auto.
          constructor; (apply REP1 || apply REP2);
            constructor; intros m EL;
              apply H; apply in_app_iff; [left|right]; assumption.
        }     
      Qed.

      Definition to_dnf ( ϕ : formula): { ψ : dnf | dnf_representation ϕ ψ }.
      Proof.
        assert (NEG := move_negations ϕ).
        destruct NEG as [neg_ϕ [EQ NEG]]. 
        apply todo15 with neg_ϕ; [apply formula_equivalence_sym; auto| clear EQ ϕ].
        induction neg_ϕ.
        { (* to_dnf F := []. *)
          exists []; apply dnf_representation_of_F.
        }
        { (* to_dnf T := [[]]. *)
          exists [[]]; apply dnf_representation_of_T.
        }
        { (* to_dnf [|v|] := [[Positive v]]. *)
          exists [[Positive v]]; apply dnf_representation_of_var.
        }
        { (* to_dnf (¬[|v|]) := [[Negative v]]. *)
          assert (LIT : {v | neg_ϕ = [|v|]}).
          { destruct neg_ϕ; try (exfalso; auto; fail).
            exists v; reflexivity. }
          destruct LIT as [v EQ]; subst neg_ϕ.
          exists [[Negative v]].
          apply dnf_representation_of_neg_var.
        } 
        { (* to_dnf (ϕl ∧ ϕr) := (to_dnf ϕl) × (to_dnf ϕr). *)
          destruct NEG as [NEG1 NEG2].
          feed IHneg_ϕ1; auto; clear NEG1.
          feed IHneg_ϕ2; auto; clear NEG2.
          destruct IHneg_ϕ1 as [ψ1 REP1], IHneg_ϕ2 as [ψ2 REP2].
          exists (flat_product ψ1 ψ2); apply dnf_representation_of_and; auto.
        }
        { (* to_dnf (ϕl ∨ ϕr) := (to_dnf ϕl) ++ (to_dnf ϕr). *)
          destruct NEG as [NEG1 NEG2].
          feed IHneg_ϕ1; auto; clear NEG1.
          feed IHneg_ϕ2; auto; clear NEG2.
          destruct IHneg_ϕ1 as [ψ1 REP1], IHneg_ϕ2 as [ψ2 REP2].
          exists (ψ1 ++ ψ2); apply dnf_representation_of_or; auto.
        }
      Qed.

      (* Compute (proj1_sig (to_dnf ((x0 ∨ x1) ∧ (x0 ∨ x2)))). *)

    End FormulaToDNF.

    Section Certificates.

      Definition ext_assignment (vs : variables) (α ext_α : assignment) :=
        incl vs (vars_in ext_α) /\
        forall (v : variable) (b : bool),
          v el vars_in α ->
          v / α ↦ b ->
          v / ext_α ↦ b.

      (* TODO: pred ~> record *)
      Definition certificate1 (ϕ : formula) (ξ : assignment) :=
        forall ext_ξ, ext_assignment (leaves ϕ) ξ ext_ξ -> ℇ (ϕ) ext_ξ ≡ true.

      (* TODO: comment *)
      Fixpoint monomial_to_certificate1 (m : monomial): assignment :=
        match m with
        | [] => []
        | Positive v :: m' => (v, true) :: monomial_to_certificate1 m'
        | Negative v :: m' => (v, false) :: monomial_to_certificate1 m'
        end.

      (* Note that [monomial_to_certificate] can fail on an unsatisfiable monomial. *)
      Example todo29:
        let var := V 0 in
        let mon := [Negative var; Positive var] in
        let α := monomial_to_certificate1 mon in 
        monomial_unsat_assignment mon α.
      Proof.
        intros; unfold monomial_unsat_assignment, mon in *; clear mon.
        constructor; exists (Positive var); split.
        - right; left; reflexivity.
        - simpl; constructor; constructor.
      Qed.

      Lemma admit_monomial_to_certificate1:
        forall (ϕ : formula) (ψ : dnf),
          dnf_representation ϕ ψ -> 
          forall (mon : monomial),
            mon el ψ ->
            monomial_satisfiable mon ->
            { ξ | certificate1 ϕ ξ }.
      Proof.
        intros ? ? DNF ? MON SAT.

      Admitted.
        
      (* list minus? *)
      Definition all_extensions_on (ξ : assignment) (vs : variables): assignments :=
        map (fun β => ξ ++ β) (all_assignments_on vs). 

      Lemma admit_contains_extensions:
        forall (ξ : assignment) (vs : variables) (α : assignment),
          α el all_extensions_on ξ vs ->
          ext_assignment vs ξ α.
      Proof.
        intros ? ? ? EL.
        apply in_map_iff in EL; destruct EL as [α_tl [EQ EL]]; subst α.
        split.
        { admit. }
        { intros ? ? EL2 EV.
          admit.
        }
      Admitted.

      Print Assumptions admit_contains_extensions.

      (* TODO: fix *)
      Lemma size_of_list_of_all_extensions:
        forall (ξ : assignment) (vs : variables),
          length (all_extensions_on ξ vs) = Nat.pow 2 (length vs).
      Proof.
        induction vs; simpl. 
        { reflexivity. }
        { unfold all_extensions_on in *; simpl.
          rewrite !map_length in IHvs.
          rewrite !map_length, app_length, !map_length, <- plus_n_O, <- IHvs.
          reflexivity. } 
      Qed. 
      
    End Certificates.

End Algorithm3.


