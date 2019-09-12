Require Export List Omega.
Import ListNotations.
From icl Require Import util assignments formulas number_of_models.

(** * Algorithm 1 *)
(* Algorithm 1 just computes all the possible assignments 
   and then filters all non-satisfying assignments. *)
Section Algorithm1.

  (* Generate all the possible assignments on a given set of variables. *)
  Fixpoint all_assignments_on (vs : variables) : assignments :=
    match vs with
    | [] => [[]] | v::vs =>
                  map (cons (v,false)) (all_assignments_on vs) ++
                      map (cons (v,true)) (all_assignments_on vs)
    end.

  Lemma vars_of_assignment_in_all_assignments_on:
    forall (vs : variables) (α : assignment),
      α el all_assignments_on vs ->
      equi (vars_in α) vs.
  Proof.
    induction vs; intros ? EL; simpl in EL.
    - destruct EL as [EL|F]; [subst |exfalso]; auto.
      split; intros x EL; destruct EL.
    - apply in_app_iff in EL; destruct EL as [EL|EL].
      + apply in_map_iff in EL; destruct EL as [α_tl [EQ EL]]; subst α.
        specialize (IHvs _ EL); simpl; auto using equi_cons.
      + apply in_map_iff in EL; destruct EL as [α_tl [EQ EL]]; subst α.
        specialize (IHvs _ EL); simpl; auto using equi_cons.
  Qed.
  
  Corollary assignment_in_all_assignments_on_sets_all_variables:
    forall (ϕ : formula) (α : assignment),
      α el all_assignments_on (formula_vars ϕ) ->
      sets_all_variables α ϕ.
  Proof.
    intros ? ? EL.
    apply vars_of_assignment_in_all_assignments_on in EL; rename EL into EQU. 
    intros v EL; apply EQU.
    apply nodup_In; assumption.
  Qed.
  
  Lemma size_of_list_of_all_assignments_on:
    forall (vs : variables),
      length (all_assignments_on vs) = Nat.pow 2 (length vs).
  Proof.
    induction vs; simpl; auto.
    rewrite app_length, !map_length, <- plus_n_O, <- IHvs; auto.
  Qed.
 
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
        apply nodup_app_of_map_cons; easy.
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
          apply neq_cons in NEQ.
          specialize (IHvs _ _ EL1 EL2 NEQ).
          apply IHvs; clear IHvs.
          eapply equiv_assignments_cancel_cons; eauto 2.
        }
        { rewrite <-EQ1, <-EQ2 in EQ, NEQ; clear EQ1 EQ2 NEQ.
          apply non_equiv_assignments in EQ; assumption. }
        { rewrite <-EQ1, <-EQ2 in EQ, NEQ; clear EQ1 EQ2 NEQ.
          apply non_equiv_assignments in EQ; assumption. }
        { rewrite <-EQ1, <-EQ2 in EQ, NEQ; clear EQ1 EQ2 α1 α2.
          rename α1_tl into α1, α2_tl into α2.
          apply neq_cons in NEQ.
          specialize (IHvs _ _ EL1 EL2 NEQ).
          apply IHvs; clear IHvs.
          eapply equiv_assignments_cancel_cons; eauto 2.
        } 
      }
    }
  Qed.

  (* Any assignment that sets variables vs has an equivalen assignment 
     that belongs to the set with all assignments on variables vs. *)
  Definition set_with_all_assignments_on (vs : variables) (αs : assignments) :=
    set_with_all (equiv_assignments vs) (fun α => vs ⊆ vars_in α) αs.
 
  Lemma all_assignments_in_all_assignments_on:
    forall (vs : variables), 
      set_with_all_assignments_on vs (all_assignments_on vs).
  Proof.
    induction vs; intros α INCL.
    { exists []; split.
      - intros v EL; inversion EL.
      - left; auto. }
    { specialize (IHvs α); feed IHvs; auto.
      { intros v EL; apply INCL; right; auto. }
      destruct IHvs as [β [EQU IN]].
      destruct (mapsto_total α a) as [[[EL MAP]|[NEL2 NMAP]]|[EL MAP]].
      { exists ((a,true)::β); split.
        { intros v EL2; destruct EL2 as [EQ|EL2]; subst; intros b; split; intros EV.
          - apply (mapsto_injective _ _ _ _ MAP) in EV; subst; constructor.
          - inversion EV; subst; [ |exfalso]; auto.
          - decide (a = v) as [EQ|NEQ]; [subst | ].
            apply EQU in MAP; apply EQU in EV; auto.
            apply (mapsto_injective _ _ _ _ MAP) in EV; subst; constructor.
            constructor; auto; apply EQU; auto.
          - decide (a = v) as [EQ|NEQ]; [subst | ].
            + inversion EV; subst; [ | exfalso]; auto.
            + inversion EV; subst; [exfalso | apply EQU]; auto.
        } 
        { simpl; apply in_app_iff; right.
          apply in_map_iff; exists β; split; auto.
        } 
      }
      { exfalso; apply NEL2; apply INCL; left; auto. } 
      { exists ((a,false)::β); split.
        { intros v EL2; destruct EL2 as [EQ|EL2]; subst; intros b; split; intros EV.
          - apply (mapsto_injective _ _ _ _ MAP) in EV; subst; constructor.
          - inversion EV; subst; [ |exfalso]; auto.
          - decide (a = v) as [EQ|NEQ]; [subst | ].
            apply EQU in MAP; apply EQU in EV; auto.
            apply (mapsto_injective _ _ _ _ MAP) in EV; subst; constructor.
            constructor; auto; apply EQU; auto.
          - decide (a = v) as [EQ|NEQ]; [subst | ].
            + inversion EV; subst; [ | exfalso]; auto.
            + inversion EV; subst; [exfalso | apply EQU]; auto.
        } 
        { simpl; apply in_app_iff; left.
          apply in_map_iff; exists β; split; auto.
        } 
      }      
    }
  Qed.

  Definition compute_formula (ϕ : formula) (α : assignment) (SET : sets_all_variables α ϕ):
    { b : bool | formula_eval ϕ α b }.
  Proof.
    induction ϕ.
    - exists false; auto. 
    - exists true; auto.
    - feed (SET v).
      { left; auto. }
      destruct (mapsto_dec α v SET) as [M|M]; [exists true| exists false]; auto. 
    - destruct IHϕ as [b EV].
      simpl in SET; assumption.
      exists (negb b); constructor; rewrite Bool.negb_involutive; auto.
    - apply inclusion_app in SET; destruct SET.
      destruct IHϕ1 as [b1 EV1]; destruct IHϕ2 as [b2 EV2]; auto.
      exists (andb b1 b2).
      destruct b1, b2; simpl in *; try(constructor; auto; fail). 
    - simpl in SET; apply inclusion_app in SET; destruct SET.
      destruct IHϕ1 as [b1 EV1]; destruct IHϕ2 as [b2 EV2]; auto.
      exists (orb b1 b2).
      destruct b1, b2; simpl in *; try(constructor; auto; fail).
  Defined.
    
  Definition formula_sat_filter (ϕ : formula) (α : assignment) : bool :=
    match sets_all_variables_dec ϕ α with 
    | left _ SETS => let '(exist _ b _) := compute_formula ϕ α SETS in b
    | right _ => false
    end.
  
  (* Now for a function ϕ, the algorithm 
     1) Generates the list of all assignments on ϕ's variables
     2) Keeps assignment such that ℇ ϕ α ≡ true. *)
  Definition algorithm1 (ϕ : formula) : { n : nat | #sat ϕ ≃ n }.
  Proof. 
    set (vars := formula_vars ϕ). 
    assert(EX: { αs | list_of_all_sat_assignments ϕ αs }).
    { exists (filter (fun α => formula_sat_filter ϕ α) (all_assignments_on vars)).
      split;[split | split].
      { apply nodup_filter.
        destruct(list_of_all_assignments_dupfree vars).
        - apply NoDup_nodup.
        - assumption.
      }
      { intros α1 α2 EL1 EL2 NEQ EQU.
        apply filter_In in EL1; destruct EL1 as [EL1 SAT1].
        apply filter_In in EL2; destruct EL2 as [EL2 SAT2].
        apply equiv_assignments_nodup in EQU.
        apply list_of_all_assignments_dupfree in EQU; try (apply NoDup_nodup || auto).
      }
      { intros α EL.  
        apply filter_In in EL; destruct EL as [EL TR]. 
        unfold formula_sat_filter in *; destruct (sets_all_variables_dec ϕ α) as [D|D]; [ | easy].
        destruct (compute_formula ϕ α D) as [b EV]; subst b.
        split; assumption.
      } 
      { intros α [SETS SAT].
        assert(H := all_assignments_in_all_assignments_on vars α).
        feed H; [eapply incl_tran; eauto; apply incl_nodup| ]. 
        destruct H as [β [EQ EL]].
        exists β; split.
        - clear EL; intros ? EL b; split; intros EV.
          all: apply EQ; auto; apply nodup_In; auto.
        - apply filter_In; split; auto.
          unfold formula_sat_filter; destruct (sets_all_variables_dec ϕ β) as [S|S].
          + apply equiv_assignments_nodup in EQ.
            destruct (compute_formula ϕ β S) as [b EV].
            apply formula_eval_assignment_transfer with (β := β) in SAT; auto.
            eapply formula_eval_injective; eauto 2.
          + exfalso; apply S.
            auto using assignment_in_all_assignments_on_sets_all_variables. 
      }
    }
    destruct EX as [αs AS]; exists (length αs); exists αs; split; auto.
  Defined.

  Section Tests.

    Let x1 := [|V 1|].
    Let x2 := [|V 2|].
    Let x3 := [|V 3|].
    Let x4 := [|V 4|].
    Let x5 := [|V 5|].
    
    Let or_n n := fold_left (fun ϕ x => ϕ ∨ [|V x|]) (range 1 n) F.
    Let xor_n n := fold_left (fun ϕ x => ϕ ⊕ [|V x|]) (range 1 n) F.
    
    (* Compute (proj1_sig (algorithm1 x1)). => 1 : nat *)
    (* Compute (proj1_sig (algorithm1 (x1 ∨ x2 ∨ x3 ∨ x4 ∨ x5))). => 31 : nat *)
    (* Compute (proj1_sig (algorithm1 (x1 ⊕ x2 ⊕ x3 ⊕ x4 ⊕ x5))). => 16 : nat *)
    (* Compute (proj1_sig (algorithm1 (or_n 8))). => 255 : nat *)
    
    (* It already takes a few seconds. *)
    (* Compute (proj1_sig (algorithm1 (xor_n 8))). => 128 : nat *)
                
  End Tests.
  
End Algorithm1.

(** * Algorithm 2: *)
(** With transformation ϕ = (ϕ[x ↦ T] ∧ x) ∨ (ϕ[x ↦ F] ∧ ¬x). *)
Section Algorithm2.
  (* The main idea of the algorithm is the following: 
       #sat F = 0
       #sat T = 1 
       #sat ϕ = #sat (x ∧ ϕ[x ↦ T] ∨ ¬x ∧ ϕ[x ↦ F]) 
              = #sat (x ∧ ϕ[x ↦ T]) + #sat (¬x ∧ ϕ[x ↦ F])
              = #sat (ϕ[x ↦ T]) + #sat (ϕ[x ↦ F]).                *)

  (* We start from "switch"-lemma which claims that 
     ϕ is equivalent to (ϕ[x ↦ T] ∧ x) ∨ (ϕ[x ↦ F] ∧ ¬x).  *)
  Section Switch.

    (* For any formula ϕ and any assignments α which sets x to true 
       formulas ϕ and ϕ[x ↦ T] evaluates to the same value. *) 
    Lemma formula_eval_subst_T:
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
      - inversion_clear EV.
        simpl in *; decide (x = v) as [EQ|NEQ];
          [subst; apply (mapsto_injective _ _ _ _ H) in M; subst| ]; auto.
      - simpl in *; decide (x = v) as [EQ|NEQ]; [subst; inversion_clear EV| ]; auto.
    Qed. 

    (* Similarly for false. For any formula ϕ and any assignments α which
       sets x to false formulas ϕ and ϕ[x ↦ F] evaluates to the same value. *) 
    Lemma formula_eval_subst_F:
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
      - inversion_clear EV.
        simpl in *; decide (x = v) as [EQ|NEQ];
          [subst; apply (mapsto_injective _ _ _ _ H) in M; subst| ]; auto.
      - simpl in *; decide (x = v) as [EQ|NEQ]; [subst; inversion_clear EV| ]; auto.
    Qed. 

    (* Proof by case analysis on [x / α ↦ b] and b. *)
    Lemma switch:
      forall (ϕ : formula) (x : variable) (α : assignment) (b : bool),
        x el vars_in α ->
        ℇ (ϕ) α ≡ b <-> ℇ ([|x|] ∧ ϕ[x ↦ T] ∨ ¬[|x|] ∧ ϕ[x ↦ F]) α ≡ b.
    Proof.
      intros ϕ ? ? ? SET.
      destruct (mapsto_dec _ _ SET); destruct b; split; intros EV.
      - apply ev_disj_tl; constructor; [ |apply formula_eval_subst_T]; auto.
      - inversion_clear EV; inversion_clear H.
        + apply <-formula_eval_subst_T; eauto.
        + exfalso; clear H1.
          inversion_clear H0; inversion_clear H.
          apply (mapsto_injective _ _ _ _ m) in H0; inversion H0.
      - eapply formula_eval_subst_T in EV; eauto; constructor;
          [apply ev_conj_fr|apply ev_conj_fl]; auto.
      - eapply formula_eval_subst_T; eauto.
        inversion_clear EV; inversion_clear H0; inversion_clear H; try assumption.
        + inversion_clear H1; apply (formula_eval_injective _ _ _ _ H) in H0; inversion H0.
        + inversion_clear H0; apply (mapsto_injective _ _ _ _ H) in m; inversion m.
      - apply ev_disj_tr; constructor; [ |apply formula_eval_subst_F]; auto.
      - inversion_clear EV; inversion_clear H.
        + exfalso; clear H1.
          inversion_clear H0.
          apply (mapsto_injective _ _ _ _ m) in H; inversion H.
        + apply <-formula_eval_subst_F; eauto.
      - eapply formula_eval_subst_F in EV; eauto. 
      - eapply formula_eval_subst_F; eauto.
        inversion_clear EV; inversion_clear H0; inversion_clear H; try assumption.
        + inversion_clear H1; apply (formula_eval_injective _ _ _ _ H) in H0; inversion H0.
        + inversion_clear H1; inversion_clear H; apply (mapsto_injective _ _ _ _ H1) in m; inversion m.
    Qed.

  End Switch.

  (* The algorithm proceeds by induction on formula size. *)

  (* Any formula of size 0 is equivalent to either T or F. Moreover, we know that
     T (of size 0) has one satisfying assignment and F has zero sat. assignments. *)
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
      { right; intros ? ?; split; intros EV; auto. }
      { left; intros ? ?; split; intros EV; auto. }
      { exfalso; compute in SIZE; easy. }
      { rewrite formula_size_neg in SIZE. 
        feed IHϕ; auto.
        destruct IHϕ as [IH|IH]; [right | left].
        { apply formula_equiv_neg_move.
          apply formula_equiv_trans with T; auto.
          apply formula_equiv_T_neg_F. }
        { apply formula_equiv_neg_move.
          apply formula_equiv_trans with F; auto.
          apply formula_equiv_sym, formula_equiv_neg_move, formula_equiv_T_neg_F. } }
      { rewrite formula_size_and in SIZE.
        apply plus_is_O in SIZE.
        destruct SIZE as [S1 S2].
        feed IHϕ1; auto; feed IHϕ2; auto.
        destruct IHϕ1 as [IH1|IH1].
        - destruct IHϕ2 as [IH2|IH2].
          + left; apply formula_equiv_and_compose_T; auto.
          + right; clear IH1.
            apply formula_equiv_trans with (ϕ2 ∧ ϕ1).
            apply formula_equiv_and_comm. apply formula_equiv_and_compose_F; auto.
        - right; clear IHϕ2.
          apply formula_equiv_and_compose_F; auto.
      }
      { rewrite formula_size_or in SIZE.
        apply plus_is_O in SIZE.
        destruct SIZE as [S1 S2].
        feed IHϕ1; auto; feed IHϕ2; auto.
        destruct IHϕ1 as [IH1|IH1].
        - clear IHϕ2; left. 
          apply formula_equiv_or_compose_T; auto.
        - destruct IHϕ2 as [IH2|IH2].
          + left. apply formula_equiv_trans with (ϕ2 ∨ ϕ1).
            apply formula_equiv_or_comm. apply formula_equiv_or_compose_T; auto.
          + right. apply formula_equiv_or_compose_F; auto; apply fo_eq_11.
      }
    Defined.

    Lemma number_or_satisfying_assignments_of_eqT:
      forall (ϕ : formula),
        equivalent ϕ T ->
        #sat ϕ ≃ (Nat.pow 2 (length (formula_vars ϕ))).
    Proof.
      intros ? EQ.
      exists (all_assignments_on (formula_vars ϕ)).
      split; [split; [split | split] | ].

      - apply list_of_all_assignments_dupfree.
        apply NoDup_nodup.
      - assert(H := list_of_all_assignments_dupfree
                      (formula_vars ϕ)).
        feed H. apply NoDup_nodup. destruct H as [H1 H2].
        intros ? ? EL1 EL2 NEQ EQU.
        apply equiv_assignments_nodup in EQU.
        apply H2 with (x1 := x1) (x2 := x2); auto.
      - intros α EL; split.
        auto using assignment_in_all_assignments_on_sets_all_variables.
        apply EQ; constructor.
      - intros α [SETS SAT].
        assert(H := all_assignments_in_all_assignments_on (formula_vars ϕ) α).
        feed H.
        { apply incl_tran with (leaves ϕ); try apply incl_nodup; auto. }
        destruct H as [β [EQU EL]].
        exists β; split; [apply equiv_assignments_nodup| ]; auto.
      - rewrite size_of_list_of_all_assignments_on; auto.
    Qed.
          
    Corollary number_or_satisfying_assignments_of_T:
      #sat T ≃ 1.
    Proof.
      apply number_or_satisfying_assignments_of_eqT, formula_equiv_refl.
    Qed.      
      
    Lemma number_or_satisfying_assignments_of_eqF:
      forall (ϕ : formula),
        equivalent ϕ F ->
        #sat ϕ ≃ 0.
    Proof.
      intros ? EQ.
      exists []. split; [split; [split | split] | ]; auto.
      - constructor.
      - intros ? EL; destruct EL.
      - intros α [_ SAT].
        apply EQ in SAT.
        inversion_clear SAT.
    Qed.
    
    Corollary number_or_satisfying_assignments_of_F:
      #sat F ≃ 0.
    Proof.
      apply number_or_satisfying_assignments_of_eqF, formula_equiv_refl.
    Qed.
    
  End BaseCase.

  (* For the induction step we assume that lists with satisfying 
     assignments are know for formulas ϕ[x ↦ T] and ϕ[x ↦ F]. *) 
  Section InductionStep.

    (* Consider a formula ϕ. *)
    Variable ϕ : formula.

    (* And its leaf x. *)
    Variable x : variable.
    Hypothesis H_leaf : x el leaves ϕ.

    (* Let αs1 and αs2 be lists of satisfying assignments for 
       formulas ϕ[x ↦ T] and ϕ[x ↦ F] respectively. *)
    Variables αs1 αs2 : assignments.
    
    Lemma app_sat_assignments_is_dupfree:
      dupfree (leaves (ϕ [x ↦ T])) αs1 ->
      dupfree (leaves (ϕ [x ↦ F])) αs2 ->
      dupfree (leaves ϕ) (map (cons (x, true)) αs1 ++ map (cons (x, false)) αs2).
    Proof.
      intros [ND1 NE1] [ND2 NE2]; split.
      { apply nodup_app_of_map_cons; auto.
        intros F; inversion_clear F.
      }
      { intros α1 α2 EL1 EL2 EQ NEQ. 
        apply in_app_iff in EL1; apply in_app_iff in EL2.
        destruct EL1 as [EL1|EL1], EL2 as [EL2|EL2]. 
        { apply in_map_iff in EL1; destruct EL1 as [β1 [EQ1 EL1]].
          apply in_map_iff in EL2; destruct EL2 as [β2 [EQ2 EL2]]; subst α1 α2.
          specialize (NE1 _ _ EL1 EL2).
          feed NE1; [intros C; apply EQ; rewrite C; auto | ].
          apply NE1; clear NE1.
          apply equiv_assignments_cancel_subset with (vs_sub := leaves (ϕ [x ↦ T])) in NEQ;
            auto using leaves_subset_subst_T, leaves_nel_subst_T.
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
          feed NE2; [intros C; apply EQ; rewrite C; auto | ].
          apply NE2; clear NE2.
          apply equiv_assignments_cancel_subset with (vs_sub := leaves (ϕ [x ↦ F])) in NEQ;
            auto using leaves_subset_subst_F, leaves_nel_subst_F.
        }
      }
    Qed.
    
    Lemma app_sat_assignments_is_set_with_sat_assignments:
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
          + left; auto.
          + specialize (SAT1 α_tl EL); destruct SAT1 as [SET1 _].
            right; apply SET1, leaves_el_neq_subst_T; auto.
        - intros v IN.
          decide (x = v) as [EQ|NEQ]; subst.
          + left; auto.
          + specialize (SAT2 α_tl EL); destruct SAT2 as [SET2 _].
            right; apply SET2, leaves_el_neq_subst_F; auto.     
      }
      apply switch with x.
      { apply in_app_iff in ELt; destruct ELt as [EL|EL]; apply in_map_iff in EL;
          destruct EL as [α_tl [EQ EL]]; subst α; simpl; left; auto. }
      apply in_app_or in ELt; destruct ELt as [EL|EL].
      { apply ev_disj_tl, ev_conj_t.
        { apply in_map_iff in EL.
          destruct EL as [mα [EQ1 MEM1]]; subst α; auto.
        } 
        { apply in_map_iff in EL.
          destruct EL as [mα [EQ MEM]]; subst α.
          apply formula_eval_nel_cons, SAT1; auto using leaves_nel_subst_T; auto.
        }
      }
      { apply ev_disj_tr, ev_conj_t.
        { apply in_map_iff in EL.
          destruct EL as [mα [EQ MEM]]; subst α; auto.
        }
        { apply in_map_iff in EL.
          destruct EL as [mα [EQ MEM]]; subst α.
          apply formula_eval_nel_cons, SAT2; auto using leaves_nel_subst_F; auto.
        }
      }
    Qed.
    
    Lemma app_sat_assignments_is_set_with_all_sat_assignments:
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
        { split; [apply sets_all_variables_subst_T| ]; auto. } 
        destruct SET1 as [β [EQ EL]].
        inversion_clear H0. 
        exists ((x,true)::β); split.
        { intros v ELl b.
          decide (v = x) as [E|NEQ]; [subst | ]; split; intros EV.
          - apply (mapsto_injective _ _ _ _ H) in EV; subst; constructor.
          - inversion_clear EV; [ | exfalso]; auto.
          - constructor; auto; apply EQ; auto using leaves_el_neq_subst_T.
          - inversion_clear EV; auto; apply EQ; auto using leaves_el_neq_subst_T.
        }
        { apply in_app_iff; left.
          apply in_map_iff; exists β; easy.
        }
      }
      { specialize (SET2 α); feed SET2.
        { split; [apply sets_all_variables_subst_F| ]; auto. }
        destruct SET2 as [β [EQ EL]].
        inversion_clear H0; inversion_clear H; simpl in H0.
        exists ((x,false)::β); split.
        { intros v ELl b.
          decide (v = x) as [E|NEQ]; [subst | ]; split; intros EV.
          - apply (mapsto_injective _ _ _ _ H0) in EV; subst; constructor.
          - inversion_clear EV; [ | exfalso]; auto.
          - constructor; auto; apply EQ; auto using leaves_el_neq_subst_F.
          - inversion_clear EV; auto; apply EQ; auto using leaves_el_neq_subst_F.
        }
        { apply in_app_iff; right.
          apply in_map_iff; exists β; easy.
        }
      } 
    Qed. 

    Lemma app_sat_assignments_sum_length:
      forall (nl nr : nat),
        length αs1 = nl ->
        length αs2 = nr ->
        length (map (cons (x, true)) αs1 ++ map (cons (x, false)) αs2) = nl + nr.
    Proof.
      intros nl nr LEN1 LEN2.
      rewrite app_length, map_length, map_length, <- LEN1, <- LEN2; auto.
    Qed.
    
  End InductionStep.
  
  Definition algorithm2 (ϕ : formula) : { n : nat | #sat ϕ ≃ n }.
  Proof.
    generalize dependent ϕ.
    apply size_recursion with formula_size; intros ϕ IHϕ. 
    destruct (formula_size_dec ϕ) as [Zero|Pos].
    { destruct (zero_size_formula_constant_dec ϕ Zero) as [Tr|Fl].
      - exists 1.
        assert(EQ := nodup_length_le _ (leaves ϕ)); unfold formula_size in Zero;
          rewrite Zero in EQ; rewrite Nat.le_0_r in EQ.
        assert(One := number_or_satisfying_assignments_of_eqT ϕ Tr); unfold formula_vars in One;
          rewrite EQ in One; simpl in One.
        assumption.
      - exists 0; auto using number_or_satisfying_assignments_of_eqF. } 
    { assert (V := get_var _ Pos).
      destruct V as [x IN]; clear Pos.
      assert (IH1 := IHϕ (ϕ[x ↦ T])); assert(IH2 := IHϕ (ϕ[x ↦ F])); clear IHϕ.
      specialize (IH1 (formula_size_subst_T_lt _ _ IN));
        specialize (IH2 (formula_size_subst_F_lt _ _ IN)).
      destruct IH1 as [nl EQ1], IH2 as [nr EQ2].
      exists (nl + nr).
      destruct EQ1 as [αs1 [LAA1 LEN1]], EQ2 as [αs2 [LAA2 LEN2]].
      exists (map (fun α => (x, true)::α) αs1 ++ map (fun α => (x,false)::α) αs2).
      destruct LAA1 as [ND1 [SAT1 SET1]], LAA2 as [ND2 [SAT2 SET2]].
      split; [split; [ | split] | ];
        auto using app_sat_assignments_is_dupfree,
        app_sat_assignments_is_set_with_sat_assignments,
        app_sat_assignments_is_set_with_all_sat_assignments,
        app_sat_assignments_sum_length.
    }
  Defined.

  Section Tests.

    Let or_n n := fold_left (fun ϕ x => ϕ ∨ [|V x|]) (range 1 n) F.
    Let xor_n n := fold_left (fun ϕ x => ϕ ⊕ [|V x|]) (range 1 n) F.

    (* Compute (proj1_sig (algorithm1 (or_n 5))). => 31 : nat *)
    (* Compute (proj1_sig (algorithm1 (or_n 8))). => 255 : nat *)
    (* Compute (proj1_sig (algorithm1 (or_n 10))). => 1023 : nat *)
    (* Compute (proj1_sig (algorithm1 (or_n 15))). => 32767 : nat *)
    (* Compute (proj1_sig (algorithm1 (or_n 16))). => Stack overflow. *)
    
    (* Compute (proj1_sig (algorithm1 (xor_n 5))). => 16 : nat *)
    (* Compute (proj1_sig (algorithm1 (xor_n 8))). => 128 : nat *)
    
  End Tests.

End Algorithm2.

(** * Bonus 1: A (failed) attempt to come up with a third algorithm. *)
(* Algorithm
   1) Transform ϕ to DNF form
   2) Map each monomial into a certificate1
   3) Make these certificates disjoint 
      (i.e. they set at least one variable to different values)
   4) Calculate the number of sat. assignments. *)
Section Algorithm3.
  
  Section Literal.

    Inductive literal :=
    | Positive: variable -> literal
    | Negative: variable -> literal.

    Inductive literal_eval: literal -> assignment -> bool -> Prop :=
    | lit_ev_pos: forall (v : variable) (α : assignment) (b : bool),
        (v / α ↦ b) -> literal_eval (Positive v) α b
    | lit_ev_neg: forall (v : variable) (α : assignment) (b : bool),
        (v / α ↦ (negb b)) -> literal_eval (Negative v) α b.
  
    Lemma literal_eval_injective:
      forall (α : assignment) (l : literal) (b1 b2 : bool),
        literal_eval l α b1 ->
        literal_eval l α b2 ->
        b1 = b2.
    Proof.
      intros ? ? ? ? M1 M2.
      destruct b1, b2; auto; exfalso.
      all: inversion M1; subst; inversion M2; subst.
      all: eapply mapsto_injective_contr; eauto. 
    Qed.
    
    Corollary literal_eval_injective_contr:
      forall (α : assignment) (l : literal),
        literal_eval l α true ->
        literal_eval l α false ->
        False.
    Proof.
      intros ? ? EV1 EV2; assert (F := literal_eval_injective _ _ _ _ EV1 EV2); easy.
    Qed.
    
  End Literal.
  Hint Constructors literal_eval.

  Section Monomial.
    
    Definition monomial := list literal.
    
    Inductive monomial_eval: monomial -> assignment -> bool -> Prop :=
    | mon_ev_true: forall (m : monomial) (α : assignment),
        (forall l, l el m -> literal_eval l α true) -> 
        monomial_eval m α true
    | mon_ev_false: forall (m : monomial) (α : assignment),
        (exists l, l el m /\ literal_eval l α false) -> 
        monomial_eval m α false.


    Definition monomial_sat_assignment (m : monomial) (α : assignment) :=
      monomial_eval m α true.

    Definition monomial_satisfiable (m : monomial) :=
      exists (α : assignment), monomial_sat_assignment m α.

    Definition monomial_unsat_assignment (m : monomial) (α : assignment) :=
      monomial_eval m α false.

    Definition monomial_unsatisfiable (m : monomial) :=
      forall (α : assignment), monomial_unsat_assignment m α.


    Lemma literal_eval_total:
      forall (α : assignment) (m : monomial),
        (forall l, l el m -> literal_eval l α true) \/
        ((exists l, l el m /\ forall b, ~ literal_eval l α b)
         /\ (forall l, l el m -> (exists b, literal_eval l α b) -> literal_eval l α true)) \/
        (exists l, l el m /\ literal_eval l α false).
    Proof.
      clear; intros; induction m.
      left; intros l EL; inversion EL.      
      destruct IHm as [IH|[IH|IH]].
      { destruct a; destruct (mapsto_total α v) as [[[V H]|[V H]]|[V H]].
        - left; intros l EL; destruct EL as [EQ|IN]; subst; auto.
        - right; left; split. 
          + exists (Positive v); split; [left| ]; auto.
            intros b EV; inversion_clear EV.
            apply nel_mapsto in H0; auto.
          + intros ? [EQ|EL] [b EV]; subst; apply IH; auto.
            inversion_clear EV; specialize (H _ H0); destruct H.
        - right; right; exists (Positive v); split; [left| ]; auto.
        - right; right; exists (Negative v); split; [left| ]; auto.
        - right; left; split.
          + exists (Negative v); split; [left| ]; auto.
            intros b EV; inversion_clear EV.
            apply nel_mapsto in H0; auto.
          + intros ? [EQ|EL] [b EV]; subst; apply IH; auto.
            inversion_clear EV; specialize (H _ H0); destruct H.
        - left; intros l EL; destruct EL as [EQ|IN]; subst; auto. 
      }     
      { destruct IH as [[l [EL NE]] ALL], a, (mapsto_total α v) as [[[V H]|[V H]]|[V H]]; right.
        - left; split.
          + exists l; split; [right | ]; auto.
          + intros l2 [EQ|EL2] [b EV]; subst; [constructor|apply ALL]; eauto.
        - left; split.
          + exists l; split; [right | ]; auto.
          + intros l2 [EQ|EL2] [b EV]; subst.
            exfalso; inversion_clear EV; eapply H; eauto.
            apply ALL; eauto.
        - right.
          exists (Positive v); split; [left| ]; auto.
        - right.
          exists (Negative v); split; [left| ]; auto.      
        - left; split.
          + exists l; split; [right | ]; auto.
          + intros l2 [EQ|EL2] [b EV]; subst.
            exfalso; inversion_clear EV; eapply H; eauto.
            apply ALL; eauto.
        - left; split.
          + exists l; split; [right | ]; auto.
          + intros l2 [EQ|EL2] [b EV]; subst; [constructor|apply ALL]; eauto.
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
    | dnf_ev_true: forall (d : dnf) (α : assignment),
        (exists m, m el d /\ monomial_eval m α true) -> 
        dnf_eval d α true
    | dnf_ev_false: forall (d : dnf) (α : assignment),
        (forall m, m el d -> monomial_eval m α false) -> 
        dnf_eval d α false.

    Definition dnf_representation (ϕ : formula) (ψ : dnf) :=
      forall (α : assignment) (b : bool),
        formula_eval ϕ α b <-> dnf_eval ψ α b.
    
    Definition equivalent_dnf (ψ1 ψ2 : dnf) :=
      forall (α : assignment) (b : bool),
        dnf_eval ψ1 α b <-> dnf_eval ψ2 α b.
    
    
    Lemma dnf_representation_formula_transfer:
      forall (ϕ1 ϕ2 : formula) (ψ : dnf), 
        equivalent ϕ1 ϕ2 ->
        dnf_representation ϕ2 ψ ->
        dnf_representation ϕ1 ψ.
    Proof.
      intros ? ? ? EQU DNF1.
      intros ? b; split; intros EV.
      apply DNF1, EQU; assumption.
      apply EQU, DNF1; assumption.
    Qed.

    Corollary dnf_representation_sigma_formula_transfer:
      forall (ϕ1 ϕ2 : formula), 
        equivalent ϕ1 ϕ2 -> 
        {ψ : dnf | dnf_representation ϕ1 ψ} ->
        {ψ : dnf | dnf_representation ϕ2 ψ}.
    Proof.
      intros ? ? EQ REP.
      destruct REP as [ψ REP].
      exists ψ; apply dnf_representation_formula_transfer with ϕ1; auto.
      apply formula_equiv_sym; assumption.
    Qed.

    Lemma monomial_sat_total:
      forall (α : assignment) (ψ : dnf),
        (forall m, m el ψ -> monomial_unsat_assignment m α) \/
        (exists m, m el ψ /\ forall b, ~ monomial_eval m α b) \/
        (exists m, m el ψ /\ monomial_sat_assignment m α).
    Proof.
      intros.
      induction ψ.
      - left; intros; inversion_clear H.
      - destruct IHψ as [IH|[IH|IH]].
        + destruct (literal_eval_total α a) as [H|[H|H]].
          * right; right.
            exists a; split; [left|constructor]; auto.
          * right; left; destruct H as [[l [EL NO]] ALL].
            exists a; split; [left| ]; auto; intros [ | ] MON.
            apply NO with (b := true); inversion_clear MON; auto.
            inversion_clear MON; destruct H as [l2 [EL2 NO2]].
            specialize (ALL l2 EL2 (@ex_intro _ (literal_eval l2 α) false NO2)).
            eapply literal_eval_injective_contr; eauto.
          * left.
            destruct H as [l [EL ALL]].
            intros m [EQ|EL2]; subst.
            constructor; exists l; split; auto.
            apply IH; auto.
        + right; left.
          destruct IH as [m [EL ALL]].
          exists m; split; [right| ]; auto.
        + right; right.
          destruct IH as [m [EL ALL]].
          exists m; split; [right| ]; auto.
    Qed.
        
  End DNF.

  Section FormulaToDNF.

    Fixpoint bottom_negations (ϕ : formula) : Prop :=
      match ϕ with
      | T | F | [|_|] | ¬ [|_|]=> True
      | ϕl ∧ ϕr => bottom_negations ϕl /\ bottom_negations ϕr
      | ϕl ∨ ϕr => bottom_negations ϕl /\ bottom_negations ϕr
      | ¬ _ => False
      end.

    (* By repetitive application of DeMorgan's laws, one 
       can move all negations to the bottom of a formula. *)
    Definition move_negations (ϕ : formula):
      {neg_ϕ : formula | equivalent ϕ neg_ϕ
                         /\ bottom_negations neg_ϕ }.
    Proof.
      generalize dependent ϕ. 
      apply size_recursion with number_of_nodes; intros ϕ IH.
      destruct ϕ.
      { (* move_negations F := F. *)
        exists F; split.
        - apply formula_equiv_refl.
        - constructor.
      }
      { (* move_negations T := T. *)
        exists T; split.
        - apply formula_equiv_refl.
        - constructor.
      }
      { (* move_negations [|v|] := [|v|]. *)
        exists [|v|]; split.
        - apply formula_equiv_refl.
        - constructor.
      }
      { destruct ϕ.
        { (* move_negations (¬F) := T. *)
          exists T; split. 
          - apply formula_equiv_sym;
              apply formula_equiv_T_neg_F.
          - constructor.
        }
        { (* move_negations (¬T) := F. *)
          exists F; split.
          - apply formula_equiv_neg_move;
              apply formula_equiv_T_neg_F.
          - constructor.
        }
        { (* move_negations (¬[|v|]) := ¬ [|v|]. *)
          exists (¬ [|v|]); split.
          - apply formula_equiv_refl.
          - constructor.
        }
        { (* move_negations (¬ ¬ ϕ) := move_negations ϕ. *)
          assert (IH1 := IH ϕ); feed IH1; [simpl; omega| clear IH].
          destruct IH1 as [neg_ϕ [EQ LIT]].
          exists neg_ϕ; split.
          - apply formula_equiv_neg_move.
            apply ->formula_equiv_neg_compose; assumption.
          - assumption.
        }
        { (* move_negations (¬(ϕl ∧ ϕr)) := move_negations ϕl ∨ move_negations ϕr. *)
          assert (IH1 := IH (¬ ϕ1)); feed IH1; [simpl; omega| ].
          assert (IH2 := IH (¬ ϕ2)); feed IH2; [simpl; omega| clear IH].
          destruct IH1 as [neg_ϕ1 [EQ1 BOT1]], IH2 as [neg_ϕ2 [EQ2 BOT2]].
          exists (neg_ϕ1 ∨ neg_ϕ2); split. 
          - apply formula_equiv_neg_move.
            apply formula_equiv_trans with (¬(¬ϕ1 ∨ ¬ϕ2)).
            apply formula_equiv_demorgan_and.
            apply ->formula_equiv_neg_compose; apply formula_equiv_or_compose; auto.
          - split; assumption.     
        }
        { (* move_negations (¬(ϕl ∨ ϕr)) := move_negations ϕl ∧ move_negations ϕr. *)
          assert (IH1 := IH (¬ ϕ1)); feed IH1; [simpl; omega| ].
          assert (IH2 := IH (¬ ϕ2)); feed IH2; [simpl; omega| ].
          destruct IH1 as [neg_ϕ1 [EQ1 BOT1]], IH2 as [neg_ϕ2 [EQ2 BOT2]].
          exists (neg_ϕ1 ∧ neg_ϕ2); split.
          - apply formula_equiv_neg_move.
            apply formula_equiv_trans with (¬(¬ϕ1 ∧ ¬ϕ2)).
            apply formula_equiv_demorgan_or.
            apply ->formula_equiv_neg_compose; apply formula_equiv_and_compose; auto. 
          - split; assumption.
        }   
      }
      { (* move_negations (ϕl ∧ ϕr) := move_negations ϕl ∧ move_negations ϕr. *)
        assert (IH1 := IH ϕ1); feed IH1; [simpl; omega| ].
        assert (IH2 := IH ϕ2); feed IH2; [simpl; omega| ].
        destruct IH1 as [neg_ϕ1 [EQ1 BOT1]], IH2 as [neg_ϕ2 [EQ2 BOT2]].
        exists (neg_ϕ1 ∧ neg_ϕ2); split.
        - apply formula_equiv_and_compose; assumption. 
        - split; assumption.
      }
      { (* move_negations (ϕl ∨ ϕr) := move_negations ϕl ∨ move_negations ϕr. *)
        assert (IH1 := IH ϕ1); feed IH1; [simpl; omega| ].
        assert (IH2 := IH ϕ2); feed IH2; [simpl; omega| ].
        destruct IH1 as [neg_ϕ1 [EQ1 BOT1]], IH2 as [neg_ϕ2 [EQ2 BOT2]].
        exists (neg_ϕ1 ∨ neg_ϕ2); split.
        - apply formula_equiv_or_compose; auto.
        - split; assumption.
      }
    Qed.

    (* Next we inductively transform a formula into its DNF representation. *)

    Lemma dnf_representation_of_T:
      dnf_representation T [[]].   
    Proof.
      split; intros EV.
      { inversion_clear EV.
        constructor; intros.
        exists []; split.
        - left; auto.
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
          - left; auto. 
          - constructor; intros lit EL.
            apply singl_in in EL; subst; auto.
        }
        { intros m EL.
          apply singl_in in EL; subst.
          constructor; exists (Positive v); split; try left; auto.
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
      forall (v : variable),
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

    Lemma dnf_representation_of_and:
      forall (ϕl ϕr : formula) (ψl ψr : dnf),
        dnf_representation ϕl ψl ->
        dnf_representation ϕr ψr ->
        dnf_representation (ϕl ∧ ϕr) (ψl ×× ψr).
    Proof.
      intros ? ? ? ? REP1 REP2; split; intros EV.
      { inversion_clear EV.
        { apply REP1 in H; apply REP2 in H0; clear REP1 REP2.
          inversion_clear H; inversion_clear H0; rename H into MR, H1 into ML.
          destruct ML as [ml [ELl Ml]], MR as [mr [ELr Mr]].
          constructor; exists (ml ++ mr); split.
          - apply app_in_flat_product; assumption.
          - inversion_clear Ml; inversion_clear Mr; rename H into Ml, H0 into Mr.
            constructor; intros lit EL; apply in_app_iff in EL; destruct EL as [EL|EL]; eauto. 
        }
        { apply REP1 in H; clear REP1 REP2.
          inversion_clear H; rename H0 into MF.
          constructor; intros m EL.
          apply flat_product_contains_only_apps in EL; destruct EL as [ml [mr [EQ [EL1 EL2]]]]; subst m.
          specialize (MF ml EL1); inversion_clear MF; destruct H as [lit [EL EV]].
          constructor; exists lit; split; [apply in_app_iff;left | ]; auto.
        }
        { apply REP2 in H; clear REP1 REP2.
          inversion_clear H; rename H0 into MF.
          constructor; intros m EL.
          apply flat_product_contains_only_apps in EL; destruct EL as [ml [mr [EQ [EL1 EL2]]]]; subst m.
          specialize (MF mr EL2); inversion_clear MF; destruct H as [lit [EL EV]].
          constructor; exists lit; split; [apply in_app_iff;right | ]; auto.
        }        
      }
      { inversion_clear EV.
        { destruct H as [mon [FL EV]].
          apply flat_product_contains_only_apps in FL; destruct FL as [ml [mr [EQ [ELl ELr]]]]; subst.
          inversion_clear EV; rename H into EL.
          constructor; [apply REP1|apply REP2]; constructor;
            [exists ml|exists mr]; split; auto; constructor; intros lit ELlit;
              apply EL; apply in_app_iff; [left|right]; auto.
        }
        { destruct (monomial_sat_total α ψl) as [EVl|[EVl|EVl]], (monomial_sat_total α ψr) as [EVr|[EVr|EVr]].
          all: try(apply ev_conj_fl; apply REP1; constructor; assumption).
          all: try(apply ev_conj_fr; apply REP2; constructor; assumption).
          all: exfalso.
          all: destruct EVl as [ml [ELl Fl]], EVr as [mr [ELr Fr]].
          all: specialize (H _ (app_in_flat_product _ _ _ _ ELl ELr)).
          all: inversion_clear H.
          all: destruct H0 as [l [EL LIT]].
          all: apply in_app_iff in EL; destruct EL as [EL|EL].
          all: try(apply Fl with false; constructor; exists l; split; assumption).
          all: try(apply Fr with false; constructor; exists l; split; assumption).
          all: try(inversion_clear Fr; specialize (H _ EL); eauto using literal_eval_injective_contr). 
          all: try(inversion_clear Fl; specialize (H _ EL); eauto using literal_eval_injective_contr). 
        }
      }
    Qed.

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

    (* Final algorithm works as follows: 
       1) Move all the negations to the leaves/bottom 
       2) Inductively build the DNF respesentation. *)
    Definition to_dnf (ϕ : formula) : { ψ : dnf | dnf_representation ϕ ψ }.
    Proof.
      assert (NEG := move_negations ϕ).
      destruct NEG as [neg_ϕ [EQ NEG]]. 
      apply dnf_representation_sigma_formula_transfer with neg_ϕ;
        [apply formula_equiv_sym; auto| clear EQ ϕ].
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

  End FormulaToDNF.

  Section Certificates.

    Definition ext_assignment (vs : variables) (α ext_α : assignment) :=
      vs ⊆ vars_in ext_α /\
      forall (v : variable) (b : bool),
        v el vars_in α ->
        v / α ↦ b ->
        v / ext_α ↦ b.
    
    Definition certificate1 (ϕ : formula) (ξ : assignment) :=
      forall ext_ξ, ext_assignment (leaves ϕ) ξ ext_ξ -> ℇ (ϕ) ext_ξ ≡ true.

    Fixpoint monomial_to_certificate1 (m : monomial) : assignment :=
      match m with
      | [] => []
      | Positive v :: m' => (v, true) :: monomial_to_certificate1 m'
      | Negative v :: m' => (v, false) :: monomial_to_certificate1 m'
      end.

    (* Note that [monomial_to_certificate] can fail on an unsatisfiable monomial. *)
    Example ex_unsat:
      let var := V 0 in
      let mon := [Negative var; Positive var] in
      let α := monomial_to_certificate1 mon in 
      monomial_unsat_assignment mon α.
    Proof.
      intros; unfold monomial_unsat_assignment, mon in *; clear mon.
      constructor; exists (Positive var); split.
      - right; left; auto. 
      - simpl; constructor; constructor.
    Qed.

    Lemma sat_mon_contains_no_conflicting_literals:
      forall (mon : monomial) (v : variable),
        monomial_satisfiable mon -> 
        Positive v el mon ->
        Negative v el mon ->
        False.
    Proof.
      intros ? ? SAT N P.
      inversion_clear SAT as [α SAT2].
      inversion_clear SAT2.
      assert(F1 := H _ P); assert(F2 := H _ N); clear H N P.
      inversion_clear F1; inversion_clear F2.
      destruct (mapsto_injective_contr _ _ H H0).
    Qed.

    Lemma mon_sat_cons:
      forall (l : literal) (mon : monomial),
        monomial_satisfiable (l :: mon) ->
        monomial_satisfiable mon.
    Proof.
      intros ? ? SAT.
      inversion_clear SAT as [α SAT2].
      exists α; constructor; intros.
      inversion_clear SAT2; apply H0; right; assumption.
    Qed.
    
    Lemma pos_literal_in_cert_vars:
      forall (mon : monomial) (v : variable),
        Positive v el mon -> 
        v el vars_in (monomial_to_certificate1 mon).
    Proof.
      intros; induction mon.
      - destruct H.
      - destruct H as [EQ|EL]; [subst; clear IHmon | ].
        + simpl; left; reflexivity.
        + destruct a; simpl; right; auto.
    Qed.

    Lemma neg_literal_in_cert_vars:
      forall (mon : monomial) (v : variable),
        Negative v el mon -> 
        v el vars_in (monomial_to_certificate1 mon).
    Proof.
      intros; induction mon.
      - destruct H.
      - destruct H as [EQ|EL]; [subst; clear IHmon | ].
        + simpl; left; reflexivity.
        + destruct a; simpl; right; auto.
    Qed.
    
    Lemma pos_literal_mapsto_true:
      forall (mon : monomial) (v : variable),
        Positive v el mon ->
        monomial_satisfiable mon -> 
        v / monomial_to_certificate1 mon ↦ true.
    Proof.
      intros ? ? EL SAT; induction mon as [ |m mon]; [destruct EL| ].
      destruct EL as [EQ|EL]; [subst; clear IHmon| ]. 
      - simpl; constructor.
      - destruct m; decide (v = v0) as [ |NEQ]; subst.
        + constructor.
        + specialize (IHmon EL (mon_sat_cons _ _ SAT)).
          simpl; constructor; auto.
        + exfalso; apply sat_mon_contains_no_conflicting_literals with (v := v0) (mon := Negative v0 :: mon);
            [ |right|left]; auto.
        + simpl; constructor; auto.
          eauto using IHmon, mon_sat_cons.
    Qed.
    
    Lemma neg_literal_mapsto_false:
      forall (mon : monomial) (v : variable),
        Negative v el mon ->
        monomial_satisfiable mon -> 
        v / monomial_to_certificate1 mon ↦ false.
    Proof.
      intros ? ? EL SAT; induction mon as [ |m mon]; [destruct EL| ].
      destruct EL as [EQ|EL]; [subst; clear IHmon| ]. 
      - simpl; constructor.
      - destruct m; decide (v = v0) as [ |NEQ]; subst.
        + exfalso; apply sat_mon_contains_no_conflicting_literals with (v := v0) (mon := Positive v0 :: mon);
            [ |left|right]; auto.
        + simpl; constructor; auto.
          eauto using IHmon, mon_sat_cons.
        + constructor.
        + constructor; eauto using mon_sat_cons.
    Qed.
    
    
    Lemma monomial_to_certificate1_correct:
      forall (ϕ : formula) (ψ : dnf),
        dnf_representation ϕ ψ -> 
        forall (mon : monomial),
          mon el ψ ->
          monomial_satisfiable mon ->
          certificate1 ϕ (monomial_to_certificate1 mon).
    Proof.
      intros ? ? DNF ? MON SAT. intros ? [INC EXT].
      apply DNF.
      constructor; exists mon; split; auto.
      constructor; intros [v|v] EL; constructor; simpl; apply EXT.
      all: auto using pos_literal_in_cert_vars, neg_literal_in_cert_vars,
           pos_literal_mapsto_true, neg_literal_mapsto_false.
    Qed. 

    (* The final thing is to note that if two certificates are disjoint then the 
       sets of their extensions are also disjoint. So we can calculate:
       num. of models of ϕ = 
         sum_{mon el dnf(ϕ)} 2^(num. of vars in ϕ - num. of vars in mon). *)

    (* Problem: but it’s not always possible to make certificates disjoint. 
       For example [ϕ = x1 ∨ x2] is in DNF. So there are two certificates --
       x1 and x2. They are not disjoint (and there is no clear way to make them 
       disjoint). Thus, an assignment (x1 ↦ true, x2 ↦ true) is an extension 
       of both certificates. Thus, we'll double-count this assignment. *)

    (* But transformation to DNF looks beautiful, so I did not delete this part. *)
    
  End Certificates.

End Algorithm3.

(** * "Bonus" 2: Counting k-Cliques. *)
(** This "bonus" gives nothing significant. The only reason I include this section is 
    to see the performance of the algorithms on real formulas (it is bad). *)
Section kCliques.

  (* Full proof of the correctness seems quite difficult. Loosely speaking, one has to:
     0) define the notion of a graph
     1) define the notion of a clique 
     2) define the notion of the number of k-cliques in a graph
     3) construct a reduction k-Clique problem to formula satisfiability problem
     4) show that this reduction respects the number of cliques!
        (i.e., the standart reduction for decision problems doesn't work). *)
  
  (* Considering the foregoing, I won't prove any properties of the reduction.
     I'll use the problem of counting the k-cliques as a "generator" of 
     nontrivial boolean formulas. *)

  (* Mostly, the resulting formulas are very big (200+ leaves); so evaluation takes 
     a looong time. However, for small examples I was able to get some results.  *)

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

  Definition transform (k : nat) (g : graph) : formula :=
    (* Extract vertices and edges from the graph. *)
    let '(Vs, Es) :=
        match g with
          {| vtcs := vtcs; edges := edges |} =>
          (vtcs, edges)
        end in

    (* The transformation copies the graph k times.
       Each copy corresponds to one vertex in a clique. *)

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

    (* Pick at most one vertex from each group. *)
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

    (* Can't pick the same vertex twice. *)
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

    (* Pick only adjacent vertices. *)
    let r4 : formula :=
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

    (* In order to count each clique only once, we need 
       to introduce an ordering on the vertices. *) 
    let r5 : formula :=
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
    r1 ∧ r2 ∧ r3 ∧ r4 ∧ r5.

  (* To count the number of k-cligues in a graph g, the algorithm 
     first transforms the graph into a corresponding boolean formula, 
     and then runs algorithm2 on the obtained formula. *)
  Definition counting_k_cliques (k : nat) (g : graph) :=
    proj1_sig (algorithm2 (transform k g)).

  Section Tests.
    
    Definition graph_3_clique :=
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
    
    Definition graph_5_clique :=
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

    (* Note that 1-clique is a vertex, 2-clique is an edge. *)

    (* Take ~12 sec. *)
    (* Compute (counting_k_cliques 1 graph_3_clique). => 3 : nat *)
    (* Compute (counting_k_cliques 2 graph_3_clique). => 3 : nat *)
    (* Compute (counting_k_cliques 3 graph_3_clique). => 1 : nat *)
    (* Compute (counting_k_cliques 4 graph_3_clique). => 0 : nat *)

    (* Take ~10 sec. *)
    (* Compute (counting_k_cliques 1 graph_4_clique). => 4 : nat *)
    (* Compute (counting_k_cliques 2 graph_4_clique). => 6 : nat *)
    (* Compute (counting_k_cliques 3 graph_4_clique). => 4 : nat *)
    (* Takes ~240 sec. *)
    (* Compute (counting_k_cliques 4 graph_4_clique). => 1 : nat *)

    (* Take ~4 sec. *)
    (* Compute (counting_k_cliques 1 graph_5_clique). => 5 : nat *)
    (* Compute (counting_k_cliques 2 graph_5_clique). => 10 : nat *)
    (* Takes ~100 sec. *)
    (* Basically it says that a pentagram contains 10 triangles.  *)
    (* Compute (counting_k_cliques 3 graph_5_clique). => 10 : nat *)
    (* No answer after ~2100 sec. *)
    (* Compute (counting_k_cliques 4 graph_5_clique). *)
    (* Compute (counting_k_cliques 5 graph_5_clique). *)

  End Tests.

End kCliques.