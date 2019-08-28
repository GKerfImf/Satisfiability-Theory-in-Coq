Require Export List Omega.
Import ListNotations.

From icl Require Export util assignments formulas.


(** Next, we define a set of all satisfying assignment of a formula. *)
Section ListOfAllSatAssignment.
  
  (* Set of all satisfying assignment must not have any duplicates (up to equivalence).  *)
  Definition dupfree (vs: variables) (αs: assignments) :=
    dupfree_rel (equiv_assignments vs) αs.

  (* Set of all satisfying assignment contains only satisfying assignments
     that set all the variables. *)
  Definition set_with_sat_assignments (ϕ : formula) (αs : assignments) :=
    set_with (fun α => sets_all_variables ϕ α /\ sat_assignment ϕ α) αs.

  (* TODO: fix comment *)
  (* For any satisfying assignment of the formula there is an equivalen one
     which is contained in set of all satisfying assignments. *)
  Definition set_with_all_sat_assignments (ϕ : formula) (αs : assignments) :=
    set_with_all
      (equiv_assignments (leaves ϕ))
      (fun α => sets_all_variables ϕ α /\ sat_assignment ϕ α)
      αs.

  (* Conjunction of the TODO  *)
  Definition list_of_all_sat_assignments (ϕ : formula) (αs : assignments) :=
    dupfree (leaves ϕ) αs /\
    set_with_sat_assignments ϕ αs /\
    set_with_all_sat_assignments ϕ αs.

  Definition number_of_sat_assignments (ϕ : formula) (n : nat) :=
    exists (αs : assignments),
      list_of_all_sat_assignments ϕ αs /\
      length αs = n.

  (* Fail! *)
(*  Lemma kek1:
    list_of_all_sat_assignments (T ∨ [|V 0|]) ([[(V 0, true)];[(V 0, false)]]).
  Proof.
    repeat split.
    - apply NoDup_cons. intros EL. apply singl_in in EL. inversion EL.
      apply NoDup_cons. intros EL. destruct EL.
      constructor.
    - intros. destruct H as [EQ1|[EQ1|EL1]]; destruct H0 as [EQ2|[EQ2|EL2]]; subst.
      all: try(exfalso;auto;fail).
      all: intros EQ; simpl in *.
      all: specialize (EQ (V 0)); feed EQ; [left; reflexivity| ].
      all: destruct EQ as [b [EV1 EV2]].
      all: inversion EV1; subst; inversion EV2; subst; auto.
    - intros α [EQ|[EQ|F]]; subst; constructor; constructor.
    - intros α [SET SAT].
      simpl.
      specialize (SET (V 0)); feed SET; [left; auto| ].
      destruct (mapsto_dec _ _ SET).
      + exists ([(V 0, true)]); split.
        intros v EL; apply singl_in in EL; subst.
        exists true; split; auto.
        left; reflexivity.
      + exists ([(V 0, false)]); split.
        intros v EL; apply singl_in in EL; subst.
        exists false; split; auto.
        right; left; reflexivity.
  Qed.
  
  Lemma kek2:
    list_of_all_sat_assignments (T ∨ [|V 0|]) ([[(V 0, true)];[(V 0, false)];[]]).
  Proof.
    repeat split.
    - apply NoDup_cons. intros EL. destruct EL as [EQ|[EQ|F]]; (inversion EQ || auto).
      apply NoDup_cons. intros EL. apply singl_in in EL. inversion EL.
      apply NoDup_cons. intros EL. destruct EL.
      constructor.
    - intros. destruct H as [EQ1|[EQ1|[EQ1|EL1]]]; destruct H0 as [EQ2|[EQ2|[EQ2|EL2]]]; subst.
      all: try(exfalso;auto;fail).
      all: intros EQ; simpl in *.
      all: specialize (EQ (V 0)); feed EQ; [left; reflexivity| ].
      all: destruct EQ as [b [EV1 EV2]].
      all: inversion EV1; subst; inversion EV2; subst; auto.
    - intros α [EQ|[EQ|F]]; subst; constructor; constructor.
    - intros α [SET SAT].
      simpl.
      specialize (SET (V 0)); feed SET; [left; auto| ].
      destruct (mapsto_dec _ _ SET).
      + exists ([(V 0, true)]); split.
        intros v EL; apply singl_in in EL; subst.
        exists true; split; auto.
        left; reflexivity.
      + exists ([(V 0, false)]); split.
        intros v EL; apply singl_in in EL; subst.
        exists false; split; auto.
        right; left; reflexivity.
  Qed.
*)  

  Theorem admit_todo70:
    forall (ϕ : formula) (n1 n2 : nat),
      number_of_sat_assignments ϕ n1 ->
      number_of_sat_assignments ϕ n2 ->
      n1 = n2.
  Proof.
    intros ? ? ? N1 N2.
    decide (n1 = n2) as [EQ|NEQ]; [auto|exfalso].
    destruct N1 as [αs1 [[[ND1 DF1] [SAT1 AllSAT1]] N1]], N2 as [αs2 [[[ND2 DF2] [SAT2 AllSAT2]] N2]].
    apply not_eq in NEQ; destruct NEQ as [LT|GT].
    { 
      
      
      rewrite <-N1, <-N2 in LT; clear N1 N2.
      eapply admit_75 with
          (R := fun α β =>
                  sets_all_variables ϕ α ->
                  sets_all_variables ϕ β ->
                  equiv_assignments (leaves ϕ) α β) in LT; eauto.
      { destruct LT as [α [EL ALL]].
        specialize (SAT2 α EL); destruct SAT2 as [SET2 SAT2].
        specialize (AllSAT1 α (conj SET2 SAT2)).
        destruct AllSAT1 as [β [EQU ELβ]].
        specialize (ALL β ELβ).
        auto.
      }
      { admit. }
      { clear; intros α SET _; intros v EL.
        specialize (SET _ EL).
        admit.
      } 
      { admit. }
      { split; eauto.
        intros. admit. }
      { admit. } 
        
    }

    { admit.
    }
    
  Admitted.

  Print Assumptions admit_todo70.
  
End ListOfAllSatAssignment.

(* TODO: move to section *)
Notation "'#sat' ϕ '≃' n" := (number_of_sat_assignments ϕ n) (at level 10).

