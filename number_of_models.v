From icl Require Export util assignments formulas.

(** * Set of all satisfying assignment *)

(* Set of all satisfying assignment must not have any duplicates (up to equivalence).  *)
Definition dupfree (vs : variables) (αs : assignments) :=
  dupfree_rel (equiv_assignments vs) αs.

(* Set of all satisfying assignment contains only satisfying assignments 
   that set all the variables. For example, formula [x1 ∨ x2 ∨ T] has 
   only four satisfying assignments. *)
Definition set_with_sat_assignments (ϕ : formula) (αs : assignments) :=
  set_with (fun α => sets_all_variables α ϕ /\ sat_assignment ϕ α) αs.

(* For any satisfying assignment (that sets all the variables) of 
   the formula there is an equivalent assignment which is contained 
   in the set of all satisfying assignments. *)
Definition set_with_all_sat_assignments (ϕ : formula) (αs : assignments) :=
  set_with_all
    (equiv_assignments (leaves ϕ))
    (fun α => sets_all_variables α ϕ /\ sat_assignment ϕ α)
    αs.

(* We define a list of all sat. assignments as conjunction of the properties above. *)
Definition list_of_all_sat_assignments (ϕ : formula) (αs : assignments) :=
  dupfree (leaves ϕ) αs /\
  set_with_sat_assignments ϕ αs /\
  set_with_all_sat_assignments ϕ αs.

(* The number of sat. assignments is the length of a list of all sat. assignments. *)
Definition number_of_sat_assignments (ϕ : formula) (n : nat) :=
  exists (αs : assignments),
    list_of_all_sat_assignments ϕ αs /\
    length αs = n.
Notation "'#sat' ϕ '≃' n" := (number_of_sat_assignments ϕ n) (at level 10).

(* Note that this number is unique. *)
Theorem number_of_sat_assignments_is_unique:
  forall (ϕ : formula) (n1 n2 : nat),
    #sat ϕ ≃ n1 -> 
    #sat ϕ ≃ n2 -> 
    n1 = n2.
Proof.
  intros ? ? ? N1 N2.
  decide (n1 = n2) as [EQ|NEQ]; [auto|exfalso].
  destruct N1 as [αs1 [[[ND1 DF1] [SAT1 AllSAT1]] N1]], N2 as [αs2 [[[ND2 DF2] [SAT2 AllSAT2]] N2]].
  apply not_eq in NEQ; destruct NEQ as [LT|GT].
  { rewrite <-N1, <-N2 in LT; clear N1 N2.
    eapply antipigeonhole with (R := equiv_assignments (leaves ϕ)) in LT; eauto.
    - destruct LT as [α [EL ALL]].
      specialize (SAT2 α EL); destruct SAT2 as [SET2 SAT2].
      specialize (AllSAT1 α (conj SET2 SAT2)).
      destruct AllSAT1 as [β [EQU ELβ]].
      specialize (ALL β ELβ); auto. 
    - apply assignment_eq_dec.
    - apply equiv_assignments_dec. 
    - apply equiv_assignments_sym.
    - apply equiv_assignments_trans.
    - split; eauto.
    - split; eauto.
  }
  { rewrite <-N1, <-N2 in GT; clear N1 N2.
    eapply antipigeonhole with (R := equiv_assignments (leaves ϕ)) in GT; eauto.
    - destruct GT as [α [EL ALL]].
      specialize (SAT1 α EL); destruct SAT1 as [SET1 SAT1].
      specialize (AllSAT2 α (conj SET1 SAT1)).
      destruct AllSAT2 as [β [EQU ELβ]].
      specialize (ALL β ELβ); auto. 
    - apply assignment_eq_dec. 
    - apply equiv_assignments_dec. 
    - apply equiv_assignments_sym. 
    - apply equiv_assignments_trans. 
    - split; eauto. 
    - split; eauto.
  }
Qed.