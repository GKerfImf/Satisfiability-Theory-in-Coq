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
    { rewrite <-N1, <-N2 in LT; clear N1 N2.
      eapply anti_pigeonhole with (R := equiv_assignments (leaves ϕ)) in LT; eauto.
      { destruct LT as [α [EL ALL]].
        specialize (SAT2 α EL); destruct SAT2 as [SET2 SAT2].
        specialize (AllSAT1 α (conj SET2 SAT2)).
        destruct AllSAT1 as [β [EQU ELβ]].
        specialize (ALL β ELβ); auto. 
      }
      { apply todo107. }
      { apply todo108. } 
      { apply equiv_assignments_sym. }
      { apply equiv_assignments_trans. }
      { split; eauto. }
      { split; eauto. }
    }
    { rewrite <-N1, <-N2 in GT; clear N1 N2.
      eapply anti_pigeonhole with (R := equiv_assignments (leaves ϕ)) in GT; eauto.
      { destruct GT as [α [EL ALL]].
        specialize (SAT1 α EL); destruct SAT1 as [SET1 SAT1].
        specialize (AllSAT2 α (conj SET1 SAT1)).
        destruct AllSAT2 as [β [EQU ELβ]].
        specialize (ALL β ELβ); auto. 
      }
      { apply todo107. }
      { apply todo108. } 
      { apply equiv_assignments_sym. }
      { apply equiv_assignments_trans. }
      { split; eauto. }
      { split; eauto. }
    }
  Qed.

  Print Assumptions admit_todo70.
  
End ListOfAllSatAssignment.

(* TODO: move to section *)
Notation "'#sat' ϕ '≃' n" := (number_of_sat_assignments ϕ n) (at level 10).

