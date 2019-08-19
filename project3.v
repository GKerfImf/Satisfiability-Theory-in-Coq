Require Export List Omega.
Import ListNotations.


Lemma TODO0:
  False.
Proof. Admitted.

Lemma TODO1:
  False.
Proof. Admitted.

Lemma TODO2:
  False.
Proof. Admitted.

Lemma TODO3:
  False.
Proof. Admitted.

Lemma TODO4:
  False.
Proof. Admitted.

Lemma TODO5:
  False.
Proof. Admitted.

Lemma TODO6:
  False.
Proof. Admitted.

Lemma TODO7:
  False.
Proof. Admitted.

Lemma TODO8:
  False.
Proof. Admitted.

Lemma TODO9:
  False.
Proof. Admitted.


(*** Qed. ~> Defined. *)

Lemma app_length: forall {A: Type} (l l': list A), length (l++l') = length l + length l'.
Proof.
  induction l; simpl; auto.
Defined.

Lemma plus_is_O n m : n + m = 0 -> n = 0 /\ m = 0.
Proof.
  destruct n; now split.
Defined.

Theorem NoDup_cons_iff (A : Type) (a : A) (l : list A):
  NoDup (a::l) <-> ~ In a l /\ NoDup l.
Proof.
  split.
  + inversion_clear 1. now split.
  + now constructor.
Defined.

(*** Feed. *)

(* This tactic feeds the precondition of an implication in order to derive the conclusion
   (taken from http://comments.gmane.org/gmane.science.mathematics.logic.coq.club/7013).

   Usage: feed H.

   H: P -> Q  ==becomes==>  H: P
                            ____
                            Q

   After completing this proof, Q becomes a hypothesis in the context. *)
Ltac feed H :=
  match type of H with
  | ?foo -> _ =>
    let FOO := fresh in
    assert foo as FOO; [|specialize (H FOO); clear FOO]
  end.

(* Generalization of feed for multiple hypotheses.
   feed_n is useful for accessing conclusions of long implications.

   Usage: feed_n 3 H.
     H: P1 -> P2 -> P3 -> Q.

   We'll be asked to prove P1, P2 and P3, so that Q can be inferred. *)
Ltac feed_n n H := match constr:(n) with
  | O => idtac
  | (S ?m) => feed H ; [| feed_n m H]
  end.

(*** Smolka's *)

Definition dec X := {X} + {~X}.
Notation "'eq_dec' X" := (forall x y: X, dec (x = y)) (at level 70).

Notation "x 'el' A" := (In x A) (at level 70).
Notation "x 'nel' A" := (~ In x A) (at level 70).

Existing Class dec.
Definition decision (X : Prop) (D : dec X) : dec X := D.
Arguments decision X {D}.

Tactic Notation "decide" constr(p) := 
  destruct (decision p).
Tactic Notation "decide" constr(p) "as" simple_intropattern(i) := 
  destruct (decision p) as i.

Lemma size_recursion (X: Type) (σ: X -> nat) (p: X -> Type):
  (forall x, (forall y, σ y < σ x -> p y) -> p x) -> 
  forall x, p x.
Proof.
  intros D x. apply D.
  cut (forall n y, σ y < n -> p y).
  now eauto.
  clear x. intros n.
  induction n; intros y E.
  - exfalso. omega. 
  - apply D. intros x F. apply IHn. omega.
Defined.

Instance nat_eq_dec: 
  eq_dec nat.
Proof.
  intros x y. hnf. decide equality.
Defined.

(*** ??? *)

Definition equi {X: Type} (A B: list X) : Prop :=
  incl A B /\ incl B A.

Hint Unfold equi.

Lemma inclusion_app {T: Type} (xs1 xs2 xs: list T): 
  incl (xs1 ++ xs2) xs ->
  incl xs1 xs /\ incl xs2 xs.
Proof.
  intros; split.
  - intros x IN.
      specialize (H x).
      assert (EL: x el xs1 ++ xs2).
      { apply in_or_app; left; assumption. }
      eauto.
  - intros x IN.
      specialize (H x).
      assert (EL: x el xs1 ++ xs2).
      { apply in_or_app; right; assumption. }
      eauto.
Defined.

Instance list_in_dec {T: Type} (x: T) (xs: list T): 
  eq_dec T -> dec (x el xs).
Proof.
  intros D; apply in_dec; exact D.
Defined.

Instance inclusion_dec {T: Type} (xs1 xs2: list T):
  eq_dec T -> dec (incl xs1 xs2).
Proof.
  intros D.
  induction xs1.
  { left.
    intros x IN; inversion IN. }
  { destruct IHxs1 as [INCL|NINCL].
    decide (a el xs2) as [IN|NIN].
    { left; intros x IN'.
      destruct IN'.
      - subst x; assumption.
      - specialize (INCL x); auto. } 
    { right.
      intros CONTR.
      apply NIN, CONTR.
      left; reflexivity.
    }
    { right.
      intros CONTR; apply NINCL; clear NINCL.
      intros x IN.
      apply CONTR.
      right; assumption.
    }
  }
Defined.

Lemma singl_in {X: Type} (x y: X):
  x el [y] -> x = y.
Proof.
  intros.
  inversion_clear H; [subst; reflexivity | inversion_clear  H0].
Qed.

(*** TODO *)
(*** Predicates on lists with equivalence *)

Fixpoint mem_e {X: Type} (R: X -> X -> Prop) (x: X) (xs: list X): Prop :=
  match xs with
  | [] => False
  | h::tl => (R x h) \/ (mem_e R x tl)
  end.

(* Definition incl_e {X: Type} (R: X -> X -> Prop) (xs1 xs2: list X) :=
  forall x, mem_e R x xs1 -> mem_e R x xs2.

Definition equiv_e {X: Type} (R: X -> X -> Prop) (xs1 xs2: list X) :=
  incl_e R xs1 xs2 /\ incl_e R xs2 xs1.  *)

  
Lemma mem_app:
  forall {X: Type} (R: X -> X -> Prop) (x: X) (xs1 xs2: list X),
  mem_e R x (xs1 ++ xs2) ->
  {mem_e R x xs1} + {mem_e R x xs2}. 
Proof.
Admitted.

Lemma mem_app_equiv:
  forall {X: Type} (R: X -> X -> Prop) (x: X) (xs1 xs2: list X),
  mem_e R x (xs1 ++ xs2) <-> (mem_e R x xs1) \/ (mem_e R x xs2). 
Proof.
Admitted.


Lemma mem_map_iff:
  forall {X: Type} (R: X -> X -> Prop) (f: X -> X) (l: list X) (y: X),
    mem_e R y (map f l) <-> (exists x: X, R (f x) y /\ mem_e R x l).
Proof.
Admitted.

Fixpoint dupfree_rel {X: Type} (rel: X -> X -> Prop) (xs: list X): Prop :=
  match xs with
  | [] => True
  | h::tl => (~ mem_e rel h tl) /\ (dupfree_rel rel tl)
  end.

(* Definition dufree *)


(* TODO: name *)
Definition set_with {X: Type} (p: X -> Prop) (xs: list X): Prop :=
  forall x, x el xs -> p x.

(* TODO: name *)
Definition set_with_all {X: Type} (rel: X -> X -> Prop) (p: X -> Prop) (xs: list X): Prop :=
  forall x, p x -> exists y, rel x y /\ y el xs.




Lemma dfnn :
  forall (X : Type) (xs : list (list X)) (a b : X), 
    a <> b -> 
    NoDup xs ->
    NoDup (map (fun x => a :: x) xs ++ map (fun x =>  b :: x) xs).
Proof.
  intros X ? ? ? NEQ ND.
  induction xs.
  - simpl; constructor.
  - apply NoDup_cons_iff in ND; destruct ND as [NEL ND].
    feed IHxs; [assumption | ].     
    simpl. 
    apply NoDup_cons_iff; split.
    { admit. } 
    { 
      assert (H : forall (T: Type) (l1 l2: list T), NoDup (l1 ++ l2) -> NoDup (l2 ++ l1)).
      admit.
      apply H.
      simpl. apply NoDup_cons_iff; split.
      intros C.
      apply in_app_or in C; destruct C as [C|C].
      { apply in_map_iff in C.
        destruct C as [x [EQ EL]].
        inversion EQ; subst x; clear EQ.
        easy.
      }
      { apply in_map_iff in C.
        destruct C as [x [EQ EL]].
        inversion EQ; subst x; clear EQ.
        easy.
      }    
      apply H; assumption.
    } 
Admitted.

Lemma dfnn_ext :
  forall (X : Type) (xs1 xs2 : list (list X)) (a b : X), 
    NoDup xs1 ->
    NoDup xs2 -> 
    NoDup (map (fun x => a :: x) xs1 ++ map (fun x =>  b :: x) xs2).
Proof.
  intros T ? ? ? NEQ ND.
  admit (* Todo: 9/10 *).
Admitted.


Lemma test2:
  forall (X: Type) (xss: list(list X)) (xl: list X),
    NoDup xss <-> NoDup (map (fun xs => xl ++ xs) xss).
Proof.
Admitted.

Lemma dffil:
  forall (T: Type) (p: T -> bool) (vs: list T),
    NoDup vs ->
    NoDup (filter p vs).
Proof.
  intros T p; induction vs; intros ND.
  { simpl; constructor. }
  { apply NoDup_cons_iff in ND.
    destruct ND as [NEL ND].
    simpl; destruct (p a).
    { constructor.
      intros IN; apply NEL; clear NEL.
      apply filter_In in IN; destruct IN as [IN _]; assumption.
      apply IHvs; assumption.
    }
    { apply IHvs; assumption. }
  }
Defined.
    
    
Lemma app_disj :
  forall (X : Type) (xsl : list X) (xsr1 xsr2 : list X),
    xsl ++ xsr1 <> xsl ++ xsr2 <-> xsr1 <> xsr2.
Proof.
  intros X ? ? ?; split; intros NEQ.
  { intros NEQ2; apply NEQ; rewrite NEQ2; reflexivity. }
  { intros NEQ2; apply NEQ; clear NEQ.
    induction xsl.
    { simpl in NEQ2; rewrite NEQ2; reflexivity. }
    { inversion NEQ2; feed IHxsl; try assumption. }
  }
Qed.

Lemma cons_disj:
  forall (X : Type) (x : X) (xs1 xs2 : list X),
    x :: xs1 <> x :: xs2 <-> xs1 <> xs2.
Proof.
  intros ? ? ? ?; split; intros NEQ1 NEQ2.
  { apply NEQ1; rewrite NEQ2; reflexivity. }
  { inversion NEQ2; subst.
    apply NEQ1; reflexivity.
  }
Qed.


(*** Assignments. *)

(* TODO: comment *)
Inductive variable := V: nat -> variable.

(* TODO: comment *)
Instance eq_var_dec (v1 v2: variable): 
  dec (v1 = v2).
Proof.
  destruct v1 as [n], v2 as [m].
  decide (n = m).
  - left; rewrite e; reflexivity.
  - right; intros C; apply n0; inversion C; reflexivity.
Defined. 

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

(* TODO: name *)
Lemma todo2:
  forall (α: assignment) (v: variable) (b1 b2: bool),
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

Lemma mapsto_dec:
  forall (α: assignment) (v: variable),
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


(* TODO: comment *)
Definition ext_assignment (α ext_α: assignment) :=
  forall (v: variable) (b: bool),
    v el vars_in α ->
    v / α ↦ b ->
    v / ext_α ↦ b.

(* TODO: comment *)
Definition equiv_assignments (vs: variables) (α1 α2: assignment) :=
  forall (v: variable),
    v el vs ->
    exists (b: bool), v / α1 ↦ b /\ v / α2 ↦ b.

(* TODO: comment *)
Definition disjoint_assignments (vs: variables) (α1 α2: assignment) :=
  exists (v: variable) (b: bool),
    v el vs /\
    v / α1 ↦ b /\
    v / α2 ↦ (negb b).


(* TODO: comment *)
(* Lemma assignments_on_vars_dec:
  forall vs α, dec (assignment_on_variables vs α).
Proof.
  induction vs; intros.
  - destruct α; [left | right]. 
    + intros x IN; inversion IN. 
    + intros C.
      destruct p.
      admit.
  - admit. 
Admitted. *)



(* TODO: comment *)
(* Lemma assignments_equiv_dec:
  forall vs α1 α2, dec (equiv_assignments vs α1 α2).
Proof.
Admitted. *)

(* There is a problem that is related to the fact that 
   two assignments can be equivalent, but not equal. 
   But we still need to consider a list of assignments and so on.
   So, I intrtoduce a new predicate for IN. 
 *)

(* *)
Definition mem_a (vs: variables) (α: assignment) (αs: assignments): Prop :=
  mem_e (equiv_assignments vs) α αs.

(* *)
Definition dupfree_a (vs: variables) (αs: assignments): Prop :=
  dupfree_rel (equiv_assignments vs) αs.

Definition dupfree_ex (vs: variables) (αs: assignments) :=
  NoDup αs /\
  (forall α1 α2,
      α1 el αs ->
      α2 el αs ->
      α1 <> α2 ->
      ~ equiv_assignments vs α1 α2).


Lemma test :
  forall (vs: variables) (αs: assignments),
    dupfree_a vs αs <->
    NoDup αs /\ (forall α1 α2,
                   α1 el αs ->
                   α2 el αs ->
                   α1 <> α2 ->
                   ~ equiv_assignments vs α1 α2
               ).
Proof.
  intros; split; [intros DUP| intros [DUP NE]].
  { split.
    { induction αs.
      - constructor.
      - admit. 
    } 
    { intros ? ? ? ? ? N.
      admit. 
    }
  }
  { 
    induction αs.
    - constructor.
    - feed IHαs. admit. feed IHαs. admit.      
      constructor; [ | assumption].
      intros C.
      admit.
  }
Admitted.






(* Definition incl_a (vs: variables) (αs1 αs2: assignments): Prop :=
  incl_e (equiv_assignments vs) αs1 αs2.

Definition equiv_a (vs: variables) (αs1 αs2: assignments): Prop :=
  equiv_e (equiv_assignments vs) αs1 αs2. *)
  

(* Section Example1.
  Let x1 := V 0.
  Let x2 := V 1.
  Let x3 := V 2.
  Compute (all_assignments_on [x1; x2; x3]).
  Goal assignment_on_variables [x1; x2; x3] [(x1, false); (x2, true); (x3, false)].
  Proof.
    intros.
    split; intros.
    { destruct H as [EQ1| [EQ2 | [EQ3 | C]]]; subst.
      - exists false; constructor.
      - exists true. constructor. intros C; inversion C. constructor.
      - exists false. constructor. intros C; inversion C. constructor. admit. constructor.
      - inversion C.
    }
    { destruct H as [b H].
      inversion_clear H. admit. 
      inversion_clear H1. admit.
      inversion_clear H2. admit.
      inversion_clear H3.
    }
  Admitted.
  Goal equiv_assignments [x1; x2; x3] 
       [(x1, false); (x2, true); (x3, false)]
       [(x1, false); (x3, false); (x2, true)]. 
  Proof. Admitted.
  Goal equiv_assignments [x1; x3] 
       [(x1, false); (x2, true); (x3, false)]
       [(x1, false); (x2, false); (x3, false)].
  Proof. Admitted.  
End Example1. *)


(*** Formulas *)

(* TODO: comment *)
Inductive formula :=
| F: formula
| T: formula
| Var: variable -> formula
| Neg: formula -> formula
| Conj: formula -> formula -> formula
| Disj: formula -> formula -> formula.
  
(* Supplementary notation for formulas. *)
Notation "[| x |]" := (Var x) (at level 0).
Notation "¬ x" := (Neg x) (at level 40). 
Notation "x '∧' y" := (Conj x y) (at level 40, left associativity).
Notation "x '∨' y" := (Disj x y) (at level 41, left associativity).

Definition xor (ϕl ϕr: formula) := ((ϕl ∧ ¬ ϕr) ∨ (¬ ϕl ∧ ϕr)). 
Notation "x '⊕' y" := (xor x y) (at level 41, left associativity).

Definition impl (ϕl ϕr: formula) := ¬ϕl ∧ ϕr. 
Notation "x '⇒' y" := (impl x y) (at level 41, left associativity).


Let x0 := [|V 0|].
Let x1 := [|V 1|].
Let x2 := [|V 2|].
Let x3 := [|V 3|].
Let x4 := [|V 4|].
Let x5 := [|V 5|].
Let x6 := [|V 6|].
Let x7 := [|V 7|].


(* TODO: def *)
(* TODO: comment *)
Reserved Notation "'ℇ' '(' ϕ ')' α ≡ b" (at level 10).

Inductive formula_eval: formula -> assignment -> bool -> Prop :=

| ev_true: forall (α: assignment), formula_eval T α true
| ev_false: forall (α: assignment), formula_eval F α false
                                   
| ev_var: forall (v: variable) (α: assignment) (b: bool),
    (v/α ↦ b) -> (formula_eval [|v|] α b)
                  
| ev_neg: forall (ϕn: formula) (α: assignment) (b: bool),
    formula_eval ϕn α (negb b) -> formula_eval (¬ ϕn) α b
                          
| ev_conj_t: forall (ϕl ϕr: formula) (α: assignment),
    formula_eval ϕl α true -> formula_eval ϕr α true -> formula_eval (ϕl ∧ ϕr) α true
| ev_conj_fl: forall (ϕl ϕr: formula) (α: assignment),
    formula_eval ϕl α false -> formula_eval (ϕl ∧ ϕr) α false
| ev_conj_fr: forall (ϕl ϕr: formula) (α: assignment),
    formula_eval ϕr α false -> formula_eval (ϕl ∧ ϕr) α false
                           
| ev_disj_f: forall (ϕl ϕr: formula) (α: assignment),
    formula_eval ϕl α false -> formula_eval ϕr α false -> formula_eval (ϕl ∨ ϕr) α false                   
| ev_disj_tl: forall (ϕl ϕr: formula) (α: assignment),
    formula_eval ϕl α true -> formula_eval (ϕl ∨ ϕr) α true
| ev_disj_tr: forall (ϕl ϕr: formula) (α: assignment),
    formula_eval ϕr α true -> formula_eval (ϕl ∨ ϕr) α true
where "'ℇ' '(' ϕ ')' α ≡ b" := (formula_eval ϕ α b). 

Hint Constructors formula_eval.

(* *)
Definition sat_assignment (ϕ: formula) (α: assignment) :=
  formula_eval ϕ α true.

Definition unsat_assignment (ϕ: formula) (α: assignment) :=
  formula_eval ϕ α false.





(* TODO: comment *)

Reserved Notation "ϕ [ x ↦ ψ ]" (at level 10).

Fixpoint substitute (ϕ: formula) (v: variable) (ψ: formula): formula :=
  match ϕ with
  | T => T
  | F => F
  | [| v0 |] => if decision (v = v0) then ψ else Var v0
  | ¬ ϕn => ¬ ϕn[v ↦ ψ]
  | ϕl ∧ ϕr => ϕl[v ↦ ψ] ∧ ϕr[v ↦ ψ]
  | ϕl ∨ ϕr => ϕl[v ↦ ψ] ∨ ϕr[v ↦ ψ]
  end
where "ϕ [ x ↦ f ]" := (substitute ϕ x f).



(* TODO: *)
Fixpoint leaves (ϕ: formula): variables :=
  match ϕ with
  | T | F => []
  | Var v => [v]
  | ¬ ϕ => leaves ϕ
  | ϕ1 ∧ ϕ2 => leaves ϕ1 ++ leaves ϕ2
  | ϕ1 ∨ ϕ2 => leaves ϕ1 ++ leaves ϕ2
  end.

(* => [V 0; V 1; V 0; V 1] *)
Compute (leaves ([|V 0|] ⊕ [|V 1|])). 


(* Definition of the size of a formula. *)
Definition formula_size (ϕ: formula): nat :=
  length (leaves ϕ).

(* => 4 *)
Compute (formula_size ([|V 0|] ⊕ [|V 1|])).


Section FormulaProp.

  Lemma todo9:
    forall (ϕ: formula), formula_size (¬ ϕ) = formula_size ϕ.
  Proof.
  Admitted.

  Lemma todo10:
    forall (ϕl ϕr: formula), formula_size (ϕl ∧ ϕr) = formula_size ϕl + formula_size ϕr.
  Proof.
  Admitted.

  Lemma todo11:
    forall (ϕl ϕr: formula), formula_size (ϕl ∨ ϕr) = formula_size ϕl + formula_size ϕr.
  Proof.
    intros; unfold formula_size; simpl; rewrite app_length; reflexivity.
  Defined.


  Lemma todo3:
    forall (ϕ: formula) (x: variable),
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
      admit.  }
    { admit. }
    
  Admitted.

  Lemma todo5:
    forall (ϕ: formula) (x: variable),
      x el leaves ϕ -> 
      formula_size (ϕ[x ↦ F]) < formula_size ϕ.
  Proof.

  Admitted.


  Lemma todo4:
    forall (ϕ: formula),
      formula_size ϕ > 0 -> 
      exists x,
        x el leaves ϕ /\
        formula_size (ϕ[x ↦ T]) < formula_size ϕ.
  Proof.

  Admitted.

End FormulaProp.


Definition get_var (ϕ: formula) (NE: formula_size ϕ > 0):
  {v: variable | v el leaves ϕ}.
Proof.
  unfold formula_size in NE.
  destruct (leaves ϕ).
  { simpl in NE; omega. }
  { exists v; left; reflexivity. }
Defined.


(* TODO: comment *)
Definition formula_vars (ϕ: formula) :=
  nodup eq_var_dec (leaves ϕ).

Definition sets_all_variables (ϕ: formula) (α: assignment) := 
  incl (leaves ϕ) (vars_in α).

(*
Definition sets_all_variables_ex (ϕ: formula) (α: assignment) := 
  incl (formula_vars ϕ) (vars_in α).
*)

Lemma sets_all_variables_dec:
  forall (ϕ: formula) (α:assignment), dec (sets_all_variables ϕ α).
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

Definition equivalent (ϕ1 ϕ2: formula) :=
  forall (α: assignment) (b: bool), ℇ (ϕ1) α ≡ b <-> ℇ (ϕ2) α ≡ b.

Section PropertiesOfEquivalence.
  
  Lemma formula_equivalence_refl: 
    forall (ϕ: formula),
      equivalent ϕ ϕ.
  Proof.
  Admitted.

  Lemma formula_equivalence_sym: 
    forall (ϕ ψ: formula),
      equivalent ϕ ψ ->
      equivalent ψ ϕ.
  Proof.
  Admitted.

  Lemma formula_equivalence_trans:
    forall (ϕ1 ϕ2 ϕ3: formula),
      equivalent ϕ1 ϕ2 ->
      equivalent ϕ2 ϕ3 ->
      equivalent ϕ1 ϕ3.
  Proof.
  Admitted.


  Lemma formula_equivalence_neg: 
    forall (ϕ ψ: formula),
      equivalent ϕ (¬ ψ) ->
      equivalent (¬ ϕ) ψ.
  Proof.
  Admitted.

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


  Lemma fo_eq_1:
    forall (ϕ1 ϕ2 ψ1 ψ2: formula),
      equivalent ϕ1 ψ1 ->
      equivalent ϕ2 ψ2 ->
      equivalent (ϕ1 ∧ ϕ2) (ψ1 ∧ ψ2).
  Proof.
  Admitted.

  Lemma fo_eq_11:
    forall (ϕ1 ϕ2 ψ1 ψ2: formula),
      equivalent ϕ1 ψ1 ->
      equivalent ϕ2 ψ2 ->
      equivalent (ϕ1 ∨ ϕ2) (ψ1 ∨ ψ2).
  Proof.
  Admitted.
  

  Corollary fo_eq_2:
    forall (ϕ1 ϕ2: formula),
      equivalent ϕ1 T ->
      equivalent ϕ2 T ->
      equivalent (ϕ1 ∧ ϕ2) T.
  Proof.
    intros.
    apply formula_equivalence_trans with (T ∧ T).
    apply fo_eq_1; auto.
    admit.
  Admitted.

  (* TODO: More general form? *)
  Corollary fo_eq_3:
    forall (ϕ1 ϕ2: formula),
      equivalent ϕ1 F ->
      equivalent (ϕ1 ∧ ϕ2) F.
  Proof.
    intros.
    admit.
  Admitted.

  (* TODO: More general form? *)
  Corollary formula_equi_1:
    forall (ϕ1 ϕ2 ψ: formula),
      equivalent (ϕ1 ∧ ϕ2) ψ ->
      equivalent (ϕ2 ∧ ϕ1) ψ.
  Proof.
    intros.
    admit.
  Admitted.

  (* TODO: More general form? *)
  Corollary formula_equi_3:
    forall (ϕ1 ϕ2 ψ: formula),
      equivalent (ϕ1 ∨ ϕ2) ψ ->
      equivalent (ϕ2 ∨ ϕ1) ψ.
  Proof.
    intros.
    admit.
  Admitted.


  (* TODO: More general form? *)
  Lemma formula_equi_2:
    forall (ϕ1 ϕ2: formula),
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
  Defined.



  Corollary fo_eq_21:
    forall (ϕ1 ϕ2: formula),
      equivalent ϕ1 F ->
      equivalent ϕ2 F ->
      equivalent (ϕ1 ∨ ϕ2) F.
  Proof.
    intros.
    admit.
  Admitted.

  Lemma fo_eq_4:
    forall (ϕ ψ: formula),
      equivalent ϕ ψ ->
      equivalent (¬ ϕ) (¬ ψ).
  Proof.
    intros.
    admit.
  Admitted.


  Lemma fo_eq_5:
    forall (ϕl ϕr ψ: formula),
      equivalent (ϕl ∧ ϕr) ψ <-> equivalent (¬ (¬ ϕl ∨ ¬ ϕr)) ψ.
  Proof.
    intros ? ? ?; split; intros EQ.
    
  Admitted.

  Lemma fo_eq_6:
    forall (ϕl ϕr ψ: formula),
      equivalent (ϕl ∨ ϕr) ψ <-> equivalent (¬ (¬ ϕl ∧ ¬ ϕr)) ψ.
  Proof.
    intros ? ? ?; split; intros EQ.
    
  Admitted.

End PropertiesOfEquivalence.
  

Lemma equiv_sat:
  forall (ϕ : formula) (α : assignment) (β : assignment),
    equiv_assignments (leaves ϕ) α β ->
    forall (b : bool), 
      ℇ (ϕ) α ≡ b ->
      ℇ (ϕ) β ≡ b.
Proof.
  intros ? ? ? EQ b EV.
Admitted.


Lemma ev_inj:
  forall (ϕ : formula) (α : assignment) (b1 b2 : bool),
    ℇ (ϕ) α ≡ b1 ->
    ℇ (ϕ) α ≡ b2 ->
    b1 = b2.
Proof.
  intros ? ? ? ? EV1 EV2.
Admitted.


(* TODO: comment *)
Definition set_with_sat_assignments (ϕ: formula) (αs: assignments) :=
  set_with (sat_assignment ϕ) αs.

Definition set_with_all_sat_assignments (ϕ: formula) (αs: assignments) :=
  set_with_all (equiv_assignments (leaves ϕ)) (sat_assignment ϕ) αs.




  
(* TODO: del variables? *)
(* TODO: add variables? *)
Definition list_of_all_sat_assignments (vs: variables) (ϕ: formula) (αs: assignments) :=
  dupfree_ex vs αs /\
  set_with_sat_assignments ϕ αs /\
  set_with_all_sat_assignments ϕ αs.

(* TODO: fix leaves to vars *)
Definition number_of_sat_assignments (ϕ: formula) (n: nat) :=
  exists (αs: assignments),
    list_of_all_sat_assignments (formula_vars ϕ) ϕ αs /\
    length αs = n.

Notation "'#sat' ϕ '≃' n" := (number_of_sat_assignments ϕ n) (at level 10).


(* TODO: move this *)
Definition set_with_all_assignments_on (vs: variables) (αs: assignments) :=
  set_with_all (equiv_assignments vs) (fun _ => True) αs.

(* TODO: check if this def does make sense. *)
Definition set_with_all_extensions_on (α: assignment) (vs: variables) (αs: assignments) :=
  set_with_all (equiv_assignments vs) (ext_assignment α) αs.
  





Lemma todo13:
  forall ϕ b v x α,
    v nel leaves ϕ ->
    ℇ (ϕ) α ≡ b <-> ℇ (ϕ) (v,x)::α ≡ b.
Proof. Admitted.

Lemma todo12:
  forall ϕ v, 
    v nel leaves (ϕ [v ↦ T]).
Proof.
Admitted.

Lemma todo14:
  forall ϕ v, 
    v nel leaves (ϕ [v ↦ F]).
Proof.
Admitted.



(*** Alg 1: *)
(** Just compute the list of all assignments, and then filter *)

Fixpoint all_assignments_on (vs: variables): assignments :=
  match vs with
  | [] => [[]]
  | v::vs => map (fun α => (v,false)::α) (all_assignments_on vs)
              ++ map (fun α => (v,true)::α) (all_assignments_on vs)
  end.

(* TODO: fix name *)
Lemma size_of_list_of_all_assignments:
  forall (vs: variables),
    length (all_assignments_on vs) = Nat.pow 2 (length vs).
Proof.
  induction vs; simpl. 
  { reflexivity. }
  { rewrite app_length, !map_length, <- plus_n_O, <- IHvs.
    reflexivity. } 
Qed.

(* TODO: fix name *)
Lemma list_of_all_assignments_dupfree:
  forall (vs: variables),
    NoDup vs ->
    dupfree_ex vs (all_assignments_on vs). 
Proof.
  intros ? ND; split.
  { induction vs.
    - constructor; [intros C; easy | constructor ].
    - apply NoDup_cons_iff in ND; destruct ND as [NEL ND].
      feed IHvs; [assumption | ].
      apply dfnn; [easy | assumption].
  } 
  { induction vs; intros ? ? EL1 EL2 NEQ EQ.
    { inversion EL1; inversion EL2; subst; auto. }
    { apply NoDup_cons_iff in ND; destruct ND as [NEL ND].
      feed IHvs; auto.
      simpl in EL1, EL2; apply in_app_iff in EL1; apply in_app_iff in EL2.
      destruct EL1 as [EL1|EL1], EL2 as [EL2|EL2];
        apply in_map_iff in EL1; apply in_map_iff in EL2;
          destruct EL1 as [α1_tl [EQ1 EL1]], EL2 as [α2_tl [EQ2 EL2]].
      - rewrite <-EQ1, <-EQ2 in EQ, NEQ; clear EQ1 EQ2 α1 α2.
        rename α1_tl into α1, α2_tl into α2.
        apply cons_disj in NEQ.
        specialize (IHvs _ _ EL1 EL2 NEQ).
        apply IHvs.
        admit (* Todo: 3/10 *).
      - rewrite <-EQ1, <-EQ2 in EQ, NEQ.
        specialize (EQ a); feed EQ; [left; auto | ].
        admit (* Todo: 4/10 *).
      - admit (* Todo: 4/10 *).
      - admit (* Todo: 4/10 *).
    }
  } 
Admitted.

(* TODO: fix name *)
Lemma all_assignments_in_this_list:
  forall (vs: variables), 
    set_with_all_assignments_on vs (all_assignments_on vs).
Proof.
  induction vs; intros α _.
  { exists []; split.
    - intros v EL; inversion EL.
    - left; reflexivity. }
  { specialize (IHvs α); feed IHvs; auto.
    destruct IHvs as [β [EQ IN]].
    admit (* Todo: 6/10 *).
  }
Admitted.


Lemma setsallvars:
  forall (ϕ : formula) (α : assignment),
    α el all_assignments_on (formula_vars ϕ) ->
    sets_all_variables ϕ α.
Proof.
  admit (* TODO: 8/10 *).
Admitted.
  



(* TODO: comment *)
Definition all_extensions_on (α: assignment) (vs: variables): assignments :=
  map (fun β => α ++ β) (all_assignments_on vs).
  
Lemma size_of_list_of_all_extensions:
  forall (α: assignment) (vs: variables),
    length (all_extensions_on α vs) = Nat.pow 2 (length vs).
Proof.
  induction vs; simpl. 
  { reflexivity. }
  { unfold all_extensions_on in *; simpl.
    rewrite !map_length in IHvs.
    rewrite !map_length, app_length, !map_length, <- plus_n_O, <- IHvs.
    reflexivity. } 
Qed.


Lemma equiv_assighn_app:
  forall (vs : variables) (α_update α1 α2 : assignment),
    equiv_assignments vs α1 α2  <->
    equiv_assignments vs (α_update ++ α1) (α_update ++ α2).
Proof.
  intros ? ? ? ?; split; intros EQ.
  
Admitted.


(* *)
Lemma equiv_nodup:
  forall (vs : variables) (α β : assignment),
    equiv_assignments vs α β <->
    equiv_assignments (nodup eq_var_dec vs) α β.
Proof.
  intros vs α β; split; intros EQ.
Admitted.
  
Lemma list_of_all_extensions_dupfree:
  forall (α: assignment) (vs: variables),
    dupfree_ex vs (all_extensions_on α vs). 
Proof.
  intros; split.
  { induction vs.
    - unfold all_extensions_on; simpl; constructor.
      intros C; inversion_clear C.
      constructor; intros C; inversion_clear C.
    - unfold all_extensions_on; simpl.
      apply test2, dfnn.
      + easy.
      + unfold all_extensions_on in IHvs.
        apply test2 in IHvs. 
        assumption.
  }
  { intros ? ? EL1 EL2 NEQ EQ. 
    apply in_map_iff in EL1; apply in_map_iff in EL2.
    destruct EL1 as [α1_tl [EQ1 EL1]].
    destruct EL2 as [α2_tl [EQ2 EL2]].
    rewrite <-EQ1, <- EQ2 in NEQ, EQ; clear EQ1 EQ2 α1 α2.
    apply app_disj in NEQ; apply equiv_assighn_app in EQ; clear α.
    generalize dependent α1_tl.
    generalize dependent α2_tl.
    induction vs; intros.
    { inversion EL1; inversion EL2; subst; auto. }
    { simpl in EL1, EL2.
      apply in_app_iff in EL1; apply in_app_iff in EL2.
      destruct EL1 as [EL1|EL1]; destruct EL2 as [EL2|EL2];
        apply in_map_iff in EL1; apply in_map_iff in EL2;
          destruct EL1 as [α1_tltl [EQ1 EL1]]; destruct EL2 as [α2_tltl [EQ2 EL2]].
      - rewrite <-EQ1, <-EQ2 in EQ, NEQ; clear EQ1 EQ2 α2_tl α1_tl.
        rename α1_tltl into α1, α2_tltl into α2.
        apply cons_disj in NEQ.
        specialize (IHvs _ EL2 _ EL1 NEQ).
        apply IHvs.
        
        admit (* Todo: 3/10 *).
      - rewrite <-EQ1, <-EQ2 in EQ, NEQ.
        specialize (EQ a); feed EQ; [left; auto | ].
        admit (* Todo: 4/10 *).
      - admit (* Todo: 4/10 *).
      - admit (* Todo: 4/10 *).
    }
  } 
Admitted.

(* TODO: fix name *)
Lemma all_extensions_in_this_list:
  forall (vs: variables) (α: assignment), 
    set_with_all_extensions_on α vs (all_assignments_on vs).
Proof.
  induction vs.
  { intros α ext_α EXT.
    exists []; simpl. admit (* Todo: 2/10 *). }
  { intros α ext_α EXT. 
    admit (* Todo: 8/10 *).
  }
Admitted.


(* vs: variables *)
Definition compute_formula (ϕ : formula) (α : assignment) (SET : sets_all_variables ϕ α):
  {b: bool | formula_eval ϕ α b}.
  induction ϕ.
  - exists false. constructor.
  - exists true. constructor.
  - feed (SET v).
    { left; reflexivity. }
    destruct (mapsto_dec α v SET) as [M|M]; [exists true| exists false]; constructor; assumption.
  - destruct IHϕ as [b EV].
    simpl in SET; assumption.
    exists (negb b); constructor; rewrite Bool.negb_involutive; assumption.
  - apply inclusion_app in SET; destruct SET.
    destruct IHϕ1 as [b1 EV1]; destruct IHϕ2 as [b2 EV2]; try auto.
    exists (andb b1 b2).
    destruct b1, b2; simpl in *; try(constructor; auto; fail). 
  - simpl in SET; apply inclusion_app in SET; destruct SET.
    destruct IHϕ1 as [b1 EV1]; destruct IHϕ2 as [b2 EV2]; try auto.
    exists (orb b1 b2).
    destruct b1, b2; simpl in *; try(constructor; auto; fail).
Defined.




Definition formula_sat_filter (ϕ : formula) (α : assignment): bool :=
  match sets_all_variables_dec ϕ α with 
  | left _ SETS => let '(exist _ b _) := compute_formula ϕ α SETS in b
  | right _ => false
  end.


(* TODO: comment *)
Definition algorithm1 (ϕ: formula): {n: nat | #sat ϕ ≃ n }.
Proof.
  set (vars := formula_vars ϕ). 
  assert(EX: { αs | list_of_all_sat_assignments vars ϕ αs }).
  { exists (filter (fun α => formula_sat_filter ϕ α) (all_assignments_on vars)).
    repeat split.
    { apply dffil.
      assert (ND := list_of_all_assignments_dupfree vars).
      destruct ND. apply NoDup_nodup.
      assumption.
    }
    { intros ? ? EL1 EL2 NEQ.
      apply filter_In in EL1; destruct EL1 as [EL1 SAT1].
      apply filter_In in EL2; destruct EL2 as [EL2 SAT2].
      apply list_of_all_assignments_dupfree; try (apply NoDup_nodup || assumption).
    } 
    { intros α EL.
      apply filter_In in EL; destruct EL as [EL TR].
      unfold formula_sat_filter in *; destruct (sets_all_variables_dec ϕ α) as [D|D]; [ | easy].
      destruct (compute_formula ϕ α D) as [b EV]; subst b.
      assumption.
    } 
    { intros α SAT.
      assert (H := all_assignments_in_this_list vars α).
      feed H; [constructor | ].
      destruct H as [β [EQ EL]].
      exists β; repeat split.
      - apply equiv_nodup; assumption.
      - apply filter_In; split; [assumption | ].
        unfold formula_sat_filter; destruct (sets_all_variables_dec ϕ β) as [S|S].
        + apply equiv_nodup in EQ.
          destruct (compute_formula ϕ β S) as [b EV].
          apply equiv_sat with (β := β) in SAT; [ | assumption].
          eapply ev_inj; eauto 2.
        + exfalso; apply S.
          apply setsallvars; assumption.
    } 
  }
  destruct EX as [αs AS]; exists (length αs); exists αs; split; auto.
Defined.

(* => 16 *)
Compute (proj1_sig (algorithm1 (x1 ⊕ x2 ⊕ x3 ⊕ x4 ⊕ x5))).

Compute (algorithm1 (x1 ⊕ x2)).

(*** Alg 2: *)
(** With transformation ϕ = (ϕ[x ↦ T] ∧ x) ∨ (ϕ[x ↦ F] ∧ ¬x). *)


(* *)
Lemma substitute_equiv':
  forall (ϕ ψ1 ψ2: formula) (v: variable),
    (forall (α: assignment) (b: bool),       ℇ (ψ1) α ≡ b ->        ℇ (ψ2) α ≡ b) -> 
    (forall (α: assignment) (b: bool), ℇ (ϕ[v ↦ ψ1]) α ≡ b -> ℇ (ϕ[v ↦ ψ2]) α ≡ b).
Proof.
  induction ϕ; intros ? ? ? EQ ? ?; simpl in *.
  { intros EV; assumption. }
  { intros EV; assumption. }
  { decide (v0 = v); eauto 2; split; eauto 2. }
  { intros EV.
    constructor.
    inversion_clear EV; rename H into EV.
    apply IHϕ with ψ1; eauto 2. }
  { intros EV.
    inversion_clear EV; try(constructor; eauto 2; fail). }
  { intros EV.
    inversion_clear EV; try(constructor; eauto 2; fail). }
Qed.

Lemma substitute_equiv:
  forall (ϕ ψ1 ψ2: formula) (v: variable),
    equivalent ψ1 ψ2 ->
    equivalent (ϕ[v ↦ ψ1]) (ϕ[v ↦ ψ2]).
Proof.
  intros; split.
  apply substitute_equiv'; apply H.
  apply substitute_equiv'; apply H.
Qed.


Lemma switch:
  forall (ϕ: formula) (x: variable),
    equivalent ϕ ([|x|] ∧ ϕ[x ↦ T] ∨ ¬[|x|] ∧ ϕ[x ↦ F]). 
Proof.
  
Admitted.


Lemma count1:
  forall (ϕ: formula) (x: variable) (n: nat),
    x el (leaves ϕ) ->
    number_of_sat_assignments (ϕ[x ↦ T]) n
    = number_of_sat_assignments ([|x|] ∧ ϕ) n.
Proof.
Admitted.

Lemma count2:
  forall (ϕ: formula) (x: variable) (n: nat),
    x el (leaves ϕ) ->
    number_of_sat_assignments (ϕ[x ↦ T]) n
    = number_of_sat_assignments ([|x|] ∧ ϕ) n.
Proof.
Admitted.



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
    { apply formula_equivalence_neg.
      apply formula_equivalence_trans with T; auto.
      apply formula_equivalence_T_neg_F. }
    { apply formula_equivalence_neg.
      apply formula_equivalence_trans with F; auto.
      apply formula_equivalence_sym, formula_equivalence_neg, formula_equivalence_T_neg_F. } }
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


Lemma count3:
  number_of_sat_assignments T 1.
Proof. 
  intros.
  exists [[]]; repeat split.  
  - constructor; [easy| constructor]. 
  - intros ? ? EL1 EL2 NEQ.
    exfalso; apply NEQ.
    admit.
  - intros ? EL.
    admit.
  - intros.
    exists [].
    simpl; split.
    intros v EL. easy.
    left; reflexivity.
Admitted.

Lemma count5:
  forall (ϕ: formula),
    equivalent ϕ T -> 
    number_of_sat_assignments ϕ 1.
Proof.
  intros.
Admitted.

Lemma count4: 
  number_of_sat_assignments F 0.
Proof.
  intros.
  exists []; repeat split; intros.
  - constructor.
  - easy.
  - easy.
  - admit.
Admitted.

Lemma count6:
  forall (ϕ: formula),
    equivalent ϕ F -> 
    number_of_sat_assignments ϕ 0.
Proof.
  intros.
Admitted.



(* 
   The main idea of the algorithm is the following: 
       #sat F = 0
       #sat T = 1 
       #sat ϕ = #sat (x ∧ ϕ[x ↦ T] ∨ ¬x ∧ ϕ[x ↦ F]) 
              = #sat (x ∧ ϕ[x ↦ T]) + #sat (¬x ∧ ϕ[x ↦ F])
              = #sat (ϕ[x ↦ T]) + #sat (ϕ[x ↦ F])

*)   
Definition algorithm2:
  forall (ϕ: formula), {n: nat| number_of_sat_assignments ϕ n}.
Proof.
  apply size_recursion with formula_size; intros ϕ IHϕ. 
  destruct (formula_size_dec ϕ) as [Zero|Pos].
  { destruct (zero_size_formula_constant_dec ϕ Zero) as [Tr|Fl].
    - exists 1; apply count5; assumption.
    - exists 0; apply count6; assumption. } 
  { assert (V := get_var _ Pos).
    destruct V as [x IN]; clear Pos.
    assert (SW := switch ϕ x). 
    assert (IH1 := IHϕ (ϕ[x ↦ T])); assert(IH2 := IHϕ (ϕ[x ↦ F])); clear IHϕ.
    specialize (IH1 (todo3 _ _ IN)); specialize (IH2 (todo5 _ _ IN)).
    destruct IH1 as [nl EQ1], IH2 as [nr EQ2].
    exists (nl + nr).
    destruct EQ1 as [αs1 [LAA1 LEN1]], EQ2 as [αs2 [LAA2 LEN2]].
    exists (map (fun α => (x, true)::α) αs1 ++ map (fun α => (x,false)::α) αs2). 
    repeat split.
    { destruct LAA1 as [DF1 _], LAA2 as [DF2 _], DF1 as [ND1 _], DF2 as [ND2 _].
      apply dfnn_ext; assumption.
    }
    { intros ? ? EL1 EL2 EQ NEQ.
      apply in_app_iff in EL1; apply in_app_iff in EL2.
      destruct EL1 as [EL1|EL1], EL2 as [EL2|EL2]. 
      - apply in_map_iff in EL1; destruct EL1 as [β1 [EQ1 EL1]].
        apply in_map_iff in EL2; destruct EL2 as [β2 [EQ2 EL2]].
        subst α1 α2; clear LEN1 LEN2.
        destruct LAA1 as [[_ ND] _].
        specialize (ND _ _ EL1 EL2).
        feed ND. exfalso; apply TODO1.
        apply ND.
        
        exfalso; apply TODO1 (* Todo: 3/10 *).
      - specialize (NEQ x).
        feed NEQ. exfalso; apply TODO5 (* Todo: 1/10 *).
        exfalso; apply TODO2 (* Todo: 3/10 *).
      - exfalso; apply TODO3 (* Todo: 5/10 *).
      - exfalso; apply TODO4 (* Todo: 5/10 *).
    }
    { intros α ELt; apply SW; clear SW.
      destruct (in_app_or _ _ _ ELt) as [EL|EL]; clear ELt.
      { apply ev_disj_tl, ev_conj_t.
        { apply in_map_iff in EL.
          destruct EL as [mα [EQ1 MEM1]]; subst α.
          constructor; constructor.
        } 
        { apply in_map_iff in EL.
          destruct EL as [mα [EQ MEM]]; subst α.
          apply todo13.
          apply todo12.
          apply LAA1; assumption.
        }
      }
      { apply ev_disj_tr, ev_conj_t.
        { apply in_map_iff in EL.
          destruct EL as [mα [EQ MEM]]; subst α.
          constructor; constructor; constructor.
        }
        { apply in_map_iff in EL.
          destruct EL as [mα [EQ MEM]]; subst α.
          apply todo13. apply todo14.
          apply LAA2; assumption.
        }
      }
    }
    { intros ? SAT; apply SW in SAT; clear SW.
      inversion_clear SAT; inversion_clear H.
      { apply LAA1 in H1; destruct H1 as [β [EQ EL]].
        inversion_clear H0; rename x8 into α. 
        exists ((x,true)::β); split.
        { exfalso; apply TODO3. }
        { apply in_app_iff; left.
          apply in_map_iff; exists β; easy.
        }
      }
      { apply LAA2 in H1; destruct H1 as [β [EQ EL]].
        inversion_clear H0. 
        exists ((x,false)::β); split.
        { exfalso; apply TODO3. }
        apply in_app_iff; right.
        apply in_map_iff; exists β; easy.
      }
    }
    { rewrite app_length, map_length, map_length.
      rewrite <- LEN1, <- LEN2; reflexivity.
    } 
  } 
Defined.

(* => 32 *)
Compute (proj1_sig (algorithm2 (x1 ⊕ x2 ⊕ x3 ⊕ x4 ⊕ x5 ⊕ x6))).


(*** Alg 3: *)
(** With certificates and DNF *)

(* Algorithm
   1) Transform ϕ to dnf
   2) Map each monomial into a certificate1
   3) By construction, all these certificates are disjoint
   4) Calculate the number of sat. assignments
*)


(* *)
Inductive literal :=
| Positive: variable -> literal
| Negative: variable -> literal.

Inductive literal_eval: literal -> assignment -> bool -> Prop :=
| lit_ev_pos: forall (v: variable) (α: assignment) (b: bool),
    (v/α ↦ b) -> literal_eval (Positive v) α b
| lit_ev_neg: forall (v: variable) (α: assignment) (b: bool),
    (v/α ↦ b) -> literal_eval (Negative v) α (negb b).

(* *)
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
  monomial_eval m α true.

(* TODO: comment *)
Definition monomial_unsatisfiable (m: monomial) :=
  forall (α: assignment), monomial_unsat_assignment m α.


(* TODO: comment *)
Definition dnf := list monomial.

Inductive dnf_eval: dnf -> assignment -> bool -> Prop :=
| dnf_ev_true: forall (d: dnf) (α: assignment),
    (exists (m: monomial), m el d /\ monomial_eval m α true) -> 
    dnf_eval d α true
| dnf_ev_false: forall (d: dnf) (α: assignment),
    (forall (m: monomial), m el d -> monomial_eval m α false) -> 
    dnf_eval d α false.

(* *)
Definition equivalent_dnf (ψ1 ψ2: dnf) :=
  forall (α: assignment) (b: bool),
    dnf_eval ψ1 α b <-> dnf_eval ψ2 α b.  

(* TODO: comment *)
Definition dnf_representation (ϕ: formula) (ψ: dnf) :=
 forall (α: assignment) (b: bool),
   formula_eval ϕ α b <-> dnf_eval ψ α b.


(* *)
Lemma lemma1:
  forall (ϕ: formula) (ψ: dnf) (α: assignment),
    dnf_representation ϕ ψ ->
    sat_assignment ϕ α <-> exists m, m el ψ /\ monomial_sat_assignment m α. 
Proof.
  intros ? ? ? REP; split; intros EV.
  { apply REP in EV; clear REP ϕ.
    inversion_clear EV.
    eauto.
  }
  { apply REP; clear REP ϕ.
    destruct EV as [m [IN EV]].
    constructor; eauto.
  }
Qed.



(* TODO: comment *)
Definition certificate1 (ϕ: formula) (ξ: assignment): Prop :=
  forall ext_α, ext_assignment ξ ext_α -> ℇ (ϕ) ext_α ≡ true.




(*
Definition certificate_to_assignments (ϕ: formula) (ξ: assignment) (C: certificate1 ϕ ξ):
  {αs : assignments |
   dupfree_a (leaves ϕ) αs 
   /\ all_in_set αs (ext_assignment ξ)
   /\ set_of_all αs (ext_assignment ξ) (equiv_assignments (leaves ϕ))}.
Proof.
Admitted.
*)

(*
Lemma test1:
  forall (ϕ: formula) (ξ1 ξ2: assignment),
    certificate1 ϕ ξ1 ->
    certificate1 ϕ ξ2 ->
    disjoint_assignments (leaves ϕ) ξ1 ξ2 ->
    forall (ext_ξ1 ext_ξ2: assignment),
      ext_assignment ξ1 ext_ξ1 ->
      ext_assignment ξ2 ext_ξ2 ->
      disjoint_assignments (leaves ϕ) ext_ξ1 ext_ξ2.
Proof.
Admitted.
 *)


(* TODO: comment *)
Fixpoint monomial_to_certificate (m: monomial): assignment :=
  match m with
  | [] => []
  | Positive v :: m' => (v, true) :: monomial_to_certificate m'
  | Negative v :: m' => (v, false) :: monomial_to_certificate m'
  end.

(* TODO: comment *)
Definition dnf_to_certs (ψ: dnf): assignments := map monomial_to_certificate ψ.

(* TODO: *)
Definition cert_to_assign (ϕ: formula) (ξ: assignment): assignments :=
  map (fun α => ξ ++ α) (all_assignments_on (leaves ϕ)).

Definition certs_to_assigns (ϕ: formula) (ξs: assignments): assignments :=
  flat_map (cert_to_assign ϕ) ξs.
  

Theorem th1:
  forall (ϕ: formula) (ψ: dnf),
    dnf_representation ϕ ψ -> 
    
    {n: nat | number_of_sat_assignments ϕ n}.
Proof.
  intros ? ? DNF.

  (* TODO: fix *)
  set (vars := nodup eq_var_dec (leaves ϕ)).
  set (n_vs := length vars).

  exists (fold_right Nat.add 0 (map (fun n => Nat.pow 2 n) (map (fun m => n_vs - length m) ψ))).
  exists (certs_to_assigns ϕ (dnf_to_certs ψ)); repeat split.
  { clear DNF.
    unfold certs_to_assigns.
    admit (* 5/10  *).
  }
  { intros. 
    admit (* 4/10 *).
  }
  { intros. 
    admit (* 2/10 *).
  }
  { intros ? SAT; apply DNF in SAT; clear DNF.
    inversion_clear SAT.
    destruct H as [m [EL SM]].
    admit (* 6/10 *).
  }
  { clear DNF; induction ψ.
    { reflexivity. }
    { simpl; rewrite app_length, IHψ, Nat.add_cancel_r.
      (* 2/10 *)
      admit.
    }
  }     
Admitted.


(* Note that we can get things like x∧¬x in one monomial *)
Definition all_monomials_satisfiable (ψ: dnf) :=
  forall (m: monomial), m el ψ -> monomial_satisfiable m.


Definition comparable {T: Type} (xs ys: list T) :=
  incl xs ys \/ incl ys xs.

Definition all_monomials_disjoint (ψ: dnf) :=
  forall (m1 m2: monomial),
    m1 el ψ ->
    m2 el ψ ->
    comparable m1 m2 ->
    m1 = m2.




(* *)
Definition certificate_to_assignments (*ξ: certificate1*):
  { αs: assignments | forall α, α el αs -> ext_assignment α α }.
Proof.

Admitted.




(* TODO: comment *)
Definition flat_product {X: Type} (xs ys: list (list X)):list(list X) :=
  flat_map (fun (y:list X) =>
         map (fun (x: list X) => x ++ y) xs) ys.

Compute (flat_product ([ [x0;x1];[x2;x3] ]) ([[x4;x5];[x6;x7]]) ).

(* TODO: comment *)
Fixpoint neg_size (ϕ: formula): nat :=
  match ϕ with
  | ¬ ϕ => 1 + neg_size ϕ
  | ϕl ∨ ϕr => neg_size ϕl + neg_size ϕr + 1
  | ϕl ∧ ϕr => neg_size ϕl + neg_size ϕr + 1
  | _ => 1
  end.

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
  {neg_ϕ : formula | equivalent ϕ neg_ϕ /\ bottom_negations neg_ϕ }.
Proof.
 generalize dependent ϕ. 
 apply size_recursion with neg_size; intros ϕ IH.
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
     - apply formula_equivalence_neg;
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
     - apply formula_equivalence_neg.
       apply fo_eq_4; assumption.
     - assumption.
   }
   { (* move_negations (¬(ϕl ∧ ϕr)) := move_negations ϕl ∨ move_negations ϕr. *)
     assert (IH1 := IH (¬ ϕ1)); feed IH1; [simpl; omega| ].
     assert (IH2 := IH (¬ ϕ2)); feed IH2; [simpl; omega| clear IH].
     destruct IH1 as [neg_ϕ1 [EQ1 BOT1]], IH2 as [neg_ϕ2 [EQ2 BOT2]].
     exists (neg_ϕ1 ∨ neg_ϕ2); split. 
     - apply formula_equivalence_neg, fo_eq_5, fo_eq_4, fo_eq_11; assumption.
     - split; assumption.     
   }
   { (* move_negations (¬(ϕl ∨ ϕr)) := move_negations ϕl ∧ move_negations ϕr. *)
     assert (IH1 := IH (¬ ϕ1)); feed IH1; [simpl; omega| ].
     assert (IH2 := IH (¬ ϕ2)); feed IH2; [simpl; omega| ].
     destruct IH1 as [neg_ϕ1 [EQ1 BOT1]], IH2 as [neg_ϕ2 [EQ2 BOT2]].
     exists (neg_ϕ1 ∧ neg_ϕ2); split.
     - apply formula_equivalence_neg, fo_eq_6, fo_eq_4, fo_eq_1; assumption. 
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
Defined.


Compute (move_negations (¬ (x0 ∨ x1) ∧ (x2 ∨ x3))).
 



Lemma tr_eq_rep:
  forall (ϕ1 ϕ2: formula) (ψ: dnf), 
    equivalent ϕ1 ϕ2 ->
    dnf_representation ϕ2 ψ ->
    dnf_representation ϕ1 ψ.
Proof.
Admitted.

(* 
Lemma tr_eq_rep:
  forall (ϕ1 ϕ2: formula) (ψ: dnf), 
    equivalent ϕ1 ϕ2 ->
    dnf_representation ϕ2 ψ ->
    dnf_representation ϕ1 ψ.
Proof.
Admitted.

{ψ : dnf | dnf_representation ϕ ψ} *)
  
  

 (* TODO: comment *)
(* As you can see, *)
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
  forall (v: variable),
    dnf_representation [|v|] [[Positive v]].   
Proof.
  intros; split; intros EV.
  { inversion_clear EV.
    destruct b; constructor.
    admit. admit.
  }
  { inversion_clear EV.
    destruct H as [m [IN EV]].
    apply singl_in in IN; subst m.
    inversion_clear EV.
    admit.
    admit. 
  } 
Admitted.

Lemma dnf_representation_of_neg_var:
  forall (v: variable),
    dnf_representation (¬ [|v|]) [[Negative v]].   
Proof.
  intros; split; intros EV.
  { inversion_clear EV.
    destruct b; constructor.
    admit. admit.
  }
  { inversion_clear EV.
    destruct H as [m [IN EV]].
    apply singl_in in IN; subst m.
    inversion_clear EV.
    admit.
    admit. 
  } 
Admitted.


Lemma dnf_representation_of_and:
  forall (ϕl ϕr: formula) (ψl ψr: dnf),
    dnf_representation ϕl ψl ->
    dnf_representation ϕr ψr ->
    dnf_representation (ϕl ∧ ϕr) (flat_product ψl ψr).
Proof.
  intros ? ? ? ? REP1 REP2; split; intros EV.
  { admit (* Todo: 9/10 *). }
  { admit (* Todo: 9/10 *). }
Admitted.
  
Lemma dnf_representation_of_or:
  forall (ϕl ϕr: formula) (ψl ψr: dnf),
    dnf_representation ϕl ψl ->
    dnf_representation ϕr ψr ->
    dnf_representation (ϕl ∨ ϕr) (ψl ++ ψr).
Proof.
  intros ? ? ? ? REP1 REP2; split; intros EV.
  { admit. }
  { admit. }
Admitted.

Lemma todo15:
  forall (ϕ1 ϕ2: formula), 
    equivalent ϕ1 ϕ2 -> 
    {ψ : dnf | dnf_representation ϕ1 ψ} ->
    {ψ : dnf | dnf_representation ϕ2 ψ}.
Proof.
  intros ? ? EQ REP.
  destruct REP as [ψ REP].
  exists ψ; apply tr_eq_rep with ϕ1; auto.
  apply formula_equivalence_sym; assumption.
Defined.

  
Definition to_dnf_1 (ϕ: formula): {ψ: dnf | dnf_representation ϕ ψ}.
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
Defined.

Compute (proj1_sig (to_dnf_1 ((x0 ∨ x1) ∧ (x0 ∨ x2)))).


Definition to_dnf_2 (ϕ: formula):
  {ψ: dnf | dnf_representation ϕ ψ
            /\ all_monomials_satisfiable ψ}.
Proof.
Admitted.



Definition to_dnf_3 (ϕ: formula):
  {ψ: dnf | dnf_representation ϕ ψ
            /\ all_monomials_satisfiable ψ
            /\ NoDup ψ
            /\ all_monomials_disjoint ψ}.
Proof.
Admitted.





Lemma theorem1:
  forall (ϕ: formula) (ψ: dnf) (m: monomial) α,
    dnf_representation ϕ ψ ->
    m el ψ ->
    monomial_sat_assignment m α -> 
    certificate1 ϕ (monomial_to_certificate m).
Proof.
  intros ? ? mon DNF INm ? EQU.
  (* apply DNF.
  constructor; exists mon; split; auto.
  constructor; intros l INl.
  induction mon. admit.
  feed IHmon. admit.
  inversion_clear INl; [subst a| ].
  { 
    destruct l; simpl in *.
    - destruct b. constructor. admit. 
    - constructor. (* *) admit. 
    - admit. 
  } 
  { apply IHmon; [ | assumption].
    intros v EL.
    destruct a; simpl in *. apply EQU; eauto .
    specialize (EQU v).    
    apply EQU.
    simpl in EQU.      
  simpl in *.
  constructor. *)
Admitted.



(* TODO: Certificates are disjoint *)





(*Lemma l0:
  forall ϕ α,
    incl (vars_in_formula ϕ) (vars_in_assignment α) ->
    {eval ϕ α true} + {eval ϕ α false}.
Proof.
  intros.
  induction ϕ.
  - right; constructor.
  - left; constructor.
  - admit. 
  - apply IHϕ in H; clear IHϕ. admit. 
  - simpl in H. admit. 
  - admit. 
Admitted.

*)



(* Lemma l1:
  forall ϕ1 ϕ2 α, 
  eval (ϕ1 ∨ ϕ2) α true -> eval ϕ1 α true \/ eval ϕ2 α true.
Proof.
  intros.
  inversion_clear H; [left | right]; assumption.
Qed.

Lemma l2:
  forall ϕ1 ϕ2 α, 
  eval (ϕ1 ∧ ϕ2) α true -> (eval ϕ1 α true) /\ (eval ϕ2 α true).
Proof.
  intros.
  inversion_clear H; split; assumption.
Qed.

Lemma l3:
  forall ϕ1 ϕ2 α b, 
  eval (ϕ1 ∧ ϕ2) α b <-> eval (¬ (¬ ϕ1 ∨ ¬ ϕ2)) α b.
Proof.
  intros; split; intros EV.
  { constructor.
    inversion_clear EV. rename H into EV1, H0 into EV2.
    - apply ev_disj_f; constructor; simpl; assumption.
    - apply ev_disj_tl; constructor; simpl; assumption.
    - apply ev_disj_tr; constructor; simpl; assumption.
  }
  { inversion_clear EV. 
    remember (negb b) as s; rewrite Bool.negb_involutive_reverse.
    rewrite <- Heqs; clear Heqs b.
    inversion_clear H. rename H0 into EV1, H1 into EV2. 
    - inversion_clear EV1. inversion_clear EV2.
      constructor; simpl in *; assumption.
    - inversion_clear H0. simpl in *.
      apply ev_conj_fl; assumption.
    - inversion_clear H0. simpl in *.
      apply ev_conj_fr; assumption.
  }       
Qed. 

Lemma l4:
  forall ϕ1 ϕ2 α b, 
  eval (ϕ1 ∨ ϕ2) α b <-> eval (¬ (¬ ϕ1 ∧ ¬ ϕ2)) α b.
Proof.
  intros; split; intros EV.
  { constructor.
    inversion_clear EV. rename H into EV1, H0 into EV2.
    - apply ev_conj_t; constructor; simpl; assumption.
    - apply ev_conj_fl; constructor; simpl; assumption.
    - apply ev_conj_fr; constructor; simpl; assumption.
  }
  { inversion_clear EV. 
    remember (negb b) as s; rewrite Bool.negb_involutive_reverse.
    rewrite <- Heqs; clear Heqs b.
    inversion_clear H. rename H0 into EV1, H1 into EV2. 
    - inversion_clear EV1. inversion_clear EV2.
      constructor; simpl in *; assumption.
    - inversion_clear H0. simpl in *.
      apply ev_disj_tl; assumption.
    - inversion_clear H0. simpl in *.
      apply ev_disj_tr; assumption.
  }       
Qed.

Lemma distributive_property:
  forall ϕ1 ϕ2 ϕ3 α b,
    eval (ϕ1 ∧ (ϕ2 ∨ ϕ3)) α b <-> eval ((ϕ1 ∧ ϕ2) ∨ (ϕ1 ∧ ϕ3)) α b.
Proof.
  intros; split; intros.
  { destruct b.
    apply l2 in H; destruct H as [X YZ].
    apply l1 in YZ; destruct YZ as [Y|Z].
    apply ev_disj_tl; apply ev_conj_t; assumption.
    apply ev_disj_tr; apply ev_conj_t; assumption.
    inversion_clear H. admit. admit .
  } 
  admit. 
Admitted.
*)

(* As you can see, we have quite weak type for assignment. 
   Therefore, we have a lot of assignments that are equivalent
   TODO
 *)







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



