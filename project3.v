Require Export List Omega.
Import ListNotations.
 
(** * Feed tactic. *)

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

(** Smolka's *)

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

(** Qed. ~> Defined. *)

Lemma singl_in {X: Type} (x y: X):
  x el [y] -> x = y.
Proof.
  intros.
  inversion_clear H; [subst; reflexivity | inversion_clear  H0].
Qed.

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

Lemma in_cons_or_dec:
  forall (A : Type) (decA: eq_dec A) (l : list A) (a b : A),
    a el b::l -> 
    {a = b} + {a el l}.
Proof.
  intros ? ? ? ? ? EL.
  induction l as [ | c]. 
  { apply singl_in in EL; left; auto. }
  { decide (a = c) as [EQ1|NEQ1]; decide (a = b) as [EQ2|NEQ2]; subst.
    - left; reflexivity.
    - right; left; reflexivity.
    - left; reflexivity.
    - right.
      destruct EL as [F|[F|EL]]; try(subst;exfalso;auto;fail).
      feed IHl; [right;assumption| ].
      destruct IHl; right; assumption. 
  }
Defined.

Lemma in_app_or_dec:
  forall (A : Type) (decA: eq_dec A) (l l' : list A) (a : A),
    a el l ++ l' ->
    {a el l} + {a el l'}.
Proof.
  intros ? ? ? ? ? EL.
  induction l. 
  { right; assumption. }
  { simpl in EL; apply in_cons_or_dec in EL; auto.
    destruct EL as [EQ|EL].
    - subst a0; left; left; reflexivity.
    - apply IHl in EL; clear IHl; destruct EL as [EL|EL].
      + left; right; assumption.
      + right; assumption.
  }
Defined.

Lemma NoDup_nodup {A : Type} (decA: eq_dec A) l: NoDup (nodup decA l).
Proof.
  induction l as [|a l' Hrec]; simpl.
  - constructor.
  - destruct (in_dec decA a l'); simpl.
    * assumption.
    * constructor; [ now rewrite nodup_In | assumption].
Defined.

(** * ??? *)

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


Definition intrs_sets {X : Type} (A B : list X) :=
  exists x, x el A /\ x el B.

Definition disj_sets {X : Type} (A B : list X) :=
  forall x, (x el A -> x nel B) /\ (x el B -> x nel A).

Lemma disj_sets_sym:
  forall {X : Type} (A B : list X),
    disj_sets A B <-> disj_sets B A.
Proof.
  intros; split; intros DISJ; split; intros EL; eauto 2; destruct (DISJ x); eauto.
Qed.    

Lemma disj_sets_cons:
  forall {X : Type} (a : X) (A B : list X),
    disj_sets (a::A) B -> disj_sets A B.
Proof.
  intros ? ? ? ? DISJ; split; intros EL1 EL2.
  all: specialize (DISJ x); destruct DISJ as [D1 D2].
  all: feed D1; [right;auto| ]; feed D2; auto.
Qed.

Lemma nel_cons:
  forall {X : Type} (x a : X) (A : list X),
    x nel a::A -> x nel A. 
Proof.
  intros ? ? ? ? NEL EL; apply NEL; right; auto.   
Qed.

Lemma nel_cons_neq:
  forall {X : Type} (x a : X) (A : list X),
    x nel a::A -> x <> a. 
Proof.
  intros ? ? ? ? NEL EL; subst; apply NEL; left; auto.   
Qed.


Lemma incl_trans:
  forall {X : Type} (A B C : list X),
    incl A B -> incl B C -> incl A C.
Proof.
  intros ? ? ? ? IN1 IN2 x EL; eauto 3.
Qed.

Lemma incl_nodup:
  forall {X : Type} {decX: eq_dec X} (A : list X),
    incl (nodup decX A) A.
Proof.
  intros ? decX ? ? EL; apply nodup_In in EL; assumption.
Qed.

Lemma todo52:
  forall {X : Type} (xs ys : list X) (a : X),
    equi xs ys -> equi (a::xs) (a::ys).
Proof.
  intros ? ? ? ? EQU; split; intros b EL; destruct EQU as [IN1 IN2].
  destruct EL as [EQ|EL]; [subst| ]; [left|right]; auto.
  destruct EL as [EQ|EL]; [subst| ]; [left|right]; auto.
Qed.


(** * TODO *)
(** * Predicates on lists with equivalence *)

(* TODO: name *)
Section Sec1. 

  Context {X : Type}.
  Hypothesis X_dec: eq_dec X.
  
  Variable R : X -> X -> Prop.

  Hypothesis R_refl: forall x, R x x.
  Hypothesis R_sym: forall x y, R x y -> R y x.

  Fixpoint mem_e (x : X) (xs : list X): Prop :=
    match xs with
    | [] => False
    | h::tl => (R x h) \/ (mem_e x tl)
    end.

  Lemma todo36:
    forall (a x : X) (xs : list X),
      mem_e a xs -> mem_e a (x::xs).
  Proof.
    intros a ax xs NM.
    induction xs.
    { destruct NM. }
    { destruct NM as [NM|NM].
      right; left; assumption.
      feed IHxs; auto.
      destruct IHxs.
      left; assumption.
      right; right; assumption.
    }
  Defined.
  
  Lemma todo24:
    forall (a x : X) (xs : list X),
      ~ mem_e a (x :: xs) -> ~ mem_e a xs.
  Proof.
    intros a ax xs.
    assert (H: forall (A B: Prop), (A -> B) -> (~ B -> ~ A)).
    { clear; intros ? ? f nb a; auto. }
    apply H; apply todo36.
  Defined.
        
  Lemma todo23:
    forall (a : X) (xs : list X),
      ~ mem_e a xs -> forall x, x el xs -> ~ R a x. 
  Proof.
    intros a xs NM x EL NR.
    induction xs.
    { destruct EL. }
    { destruct EL as [EQ|EL]; subst.
      apply NM; left; assumption.
      apply todo24 in NM; feed IHxs; auto. }
  Qed.

  Lemma todo26:
    forall (a : X) (xs : list X),
      mem_e a xs -> exists x, x el xs /\ R a x.
  Proof.
    intros a xs MEM; induction xs.
    { inversion MEM. }
    { destruct MEM as [Ra|MEM].
      - exists a0; split; [left | ]; auto.
      - feed IHxs; auto. destruct IHxs as [x [EL Ra]].
        exists x; split; [right | ]; auto.
    } 
  Defined.

  Lemma todo25:
    forall (x : X) (xs : list X), x el xs -> mem_e x xs.
  Proof.
    intros a xs NEL.
    induction xs.
    { auto. }
    { destruct NEL as [EQ|NEL]; subst; [left|right]; auto. }
  Qed.    

  (* *)
  Definition dupfree_rel (xs : list X): Prop :=
    NoDup xs /\ (forall x1 x2, x1 el xs -> x2 el xs -> x1 <> x2 -> ~ R x1 x2).
  
  Fixpoint dupfree_rel_classic (xs : list X): Prop :=
    match xs with
    | [] => True
    | h::tl => (~ mem_e h tl) /\ (dupfree_rel_classic tl)
    end.
  
  Lemma dupfrees_are_equivalent:
    forall (xs : list X),
      dupfree_rel xs <-> dupfree_rel_classic xs.
  Proof.
    intros; split; intros DUP.
    { induction xs.
      { constructor. }
      { feed IHxs.
        { destruct DUP as [ND DUP].
          apply List.NoDup_cons_iff in ND; destruct ND as [NEL ND].
          split.
          - assumption.
          - intros ? ? EL1 EL2 NEQ.
            apply DUP; [right | right | ]; assumption.
        }
        split; [ | assumption].
        intros MEM.
        apply todo26 in MEM; destruct MEM as [x [EL RAX]].
        destruct DUP as [ND DUP].
        decide (a = x).
        { subst; apply List.NoDup_cons_iff in ND; destruct ND as [ND _]; auto. }
        { specialize (DUP a x).
          apply DUP in RAX; [ |left|right| ]; try auto 2.
        }
      }
    }
    { induction xs.
      { split; [constructor | intros ? ? EL; inversion EL]. }
      { destruct DUP as [NM DUP].
        feed IHxs; [assumption | ].
        destruct IHxs as [DUP1 DUP2].
        split.
        { constructor.
          intros NEL; apply NM.
          apply todo25; auto.
          assumption. }
        { intros ? ? EL1 EL2 NEQ NR.
          destruct EL1 as [EQ1|IN1], EL2 as [EQ2|IN2]; subst.
          - exfalso; auto.
          - apply todo23 with (x := x2) in NM; auto.
          - apply todo23 with (x := x1) in NM; auto.
          - apply DUP2 with (x1 := x1) (x2 := x2); eauto 2.
        } 
      }         
    }
  Qed.
  
End Sec1.

(* TODO: name *)
Definition set_with {X: Type} (p: X -> Prop) (xs: list X): Prop :=
  forall x, x el xs -> p x.

(* TODO: name *)
Definition set_with_all {X: Type} (rel: X -> X -> Prop) (p: X -> Prop) (xs: list X): Prop :=
  forall x, p x -> exists y, rel x y /\ y el xs.

Lemma todo37:
  forall (X : Type) (l l' : list X),
    NoDup (l ++ l') -> 
    NoDup (l' ++ l).
Proof.
  intros X l l' ND.
  induction l'.
  { rewrite <- app_nil_end in ND; assumption. }
  { apply NoDup_remove in ND; destruct ND as [ND NEL].
    apply IHl' in ND; clear IHl'.
    simpl; apply NoDup_cons_iff; split; [ | assumption].
    intros EL; apply NEL; clear NEL.
    apply List.in_app_or in EL; destruct EL.
    - apply List.in_or_app; right; assumption.
    - apply List.in_or_app; left; assumption.
  } 
Defined.


Lemma todo39:
  forall (X : Type) (f : X -> X) (xs : list X),
    (forall a b, f a = f b -> a = b) -> 
    NoDup xs <-> NoDup (map f xs).
Proof.
  intros ? ? ? INJ; split; intros ND.
  { induction xs.
    { assumption. } 
    { apply NoDup_cons_iff in ND; destruct ND  as [NEL ND].
      feed IHxs; auto.
      simpl; apply NoDup_cons_iff; split; [ | auto].
      intros EL; apply in_map_iff in EL; destruct EL as [a' [EQ NEL2]].
      apply INJ in EQ; subst; auto.
    }
  }
  { induction xs.
    { assumption. } 
    { simpl in ND; apply NoDup_cons_iff in ND; destruct ND  as [NEL ND].
      feed IHxs; auto.
      simpl; apply NoDup_cons_iff; split; [ | auto].
      intros EL; apply NEL; clear NEL.
      apply in_map_iff; exists a; split; auto.
    }
  }
Defined.
 
Corollary todo38:
  forall (X : Type) (xss : list (list X)) (x : X),
    NoDup xss <->  NoDup (map (fun xs => x :: xs) xss).
Proof.
  intros ? ? ?.
  apply todo39; auto.
  clear; intros; inversion H; reflexivity.
Defined.

  
Corollary todo40:
  forall (X : Type) (xss : list (list X)) (xsl: list X),
    NoDup xss <-> NoDup (map (fun xsr => xsl ++ xsr) xss).
Proof.
  intros.
  apply todo39. 
  clear; intros ? ? EQ.
  induction xsl; simpl in EQ; [assumption | inversion EQ]; auto.
Defined.


Lemma dfnn_ext :
  forall (X : Type) (xs1 xs2 : list (list X)) (a b : X),
    a <> b ->
    NoDup xs1 ->
    NoDup xs2 -> 
    NoDup (map (fun x => a :: x) xs1 ++ map (fun x =>  b :: x) xs2).
Proof.
  intros T ? ? ? ? NEQ ND1 ND2.
  induction xs1. simpl.
  { eapply todo38 in ND2; eauto. }
  { apply NoDup_cons_iff in ND1; destruct ND1 as [NEL1 ND1].
    feed IHxs1; [assumption | ]; simpl.
    apply NoDup_cons_iff; split; [ | assumption].
    { clear IHxs1; intros EL; apply in_app_iff in EL; destruct EL as [EL|EL].
      - apply in_map_iff in EL; destruct EL as [a_tl [EQ EL]].
        inversion EQ; subst a0; clear EQ; auto. 
      - apply in_map_iff in EL; destruct EL as [b_tl [EQ EL]].
        inversion EQ; subst a0; clear EQ; auto.
    }
  }
Defined.

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


(** * Assignments. *)

(* TODO: comment *)
Inductive variable := V: nat -> variable.

(* TODO: comment *)
Global Instance eq_var_dec: eq_dec variable.
Proof.
  intros v1 v2.
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

(* admit_ *)
Global Instance eq_assignment_dec: eq_dec assignment.
Proof.
Admitted.

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

Hint Constructors mapsto.

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
    v / α ↦ b ->
    False.
Proof.
  intros ? ? ? NEL MAP.
  apply NEL; clear NEL.
  induction MAP.
  { left; reflexivity. }
  { right; assumption. }
Defined.


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
Defined.

(* TODO: comment *)
Definition equiv_assignments (vs : variables) (α1 α2 : assignment) :=
  forall (v : variable),
    v el vs ->
    exists (b : bool), v / α1 ↦ b /\ v / α2 ↦ b.

Section Properties.

  Lemma todo28:
    forall (vs vs_sub : variables) (v : variable) (b : bool) (α1 α2 : assignment),
      incl vs_sub vs ->
      v nel vs_sub ->
      equiv_assignments vs ((v,b)::α1) ((v,b)::α2) ->
      equiv_assignments vs_sub α1 α2.
  Proof.
    intros ? ? v ? ? ? INCL NEL EQU x EL.
    decide (x = v) as [EQ|NEQ]; [subst;exfalso;auto| ].
    specialize (INCL _ EL).
    specialize (EQU _ INCL); destruct EQU as [c [EV1 EV2]].
    exists c; split. 
    inversion EV1; subst; [exfalso;auto|assumption].
    inversion EV2; subst; [exfalso;auto|assumption].
  Qed.
  

  Lemma todo53:
    forall (α_upd α : assignment) (v : variable) (b : bool),
      v nel vars_in α_upd -> 
      v / α_upd ++ α ↦ b ->
      v / α ↦ b.
  Proof.
    intros ? ? ? ? NEL EV.
    induction α_upd.
    { simpl in EV; assumption. }
    { destruct a as [vu bu].
      assert(NEQ:= nel_cons_neq _ _ _ NEL).
      simpl in EV; inversion EV; subst; [exfalso;auto| ].
      clear EV H4; rename H5 into EV.
      specialize (IHα_upd (nel_cons _ _ _ NEL) EV).
      assumption.
    } 
  Qed.
    
  Lemma equiv_assign_disj_update:
    forall (vs : variables) (α_upd α1 α2 : assignment),
      disj_sets vs (vars_in α_upd) ->
      equiv_assignments vs (α_upd ++ α1) (α_upd ++ α2) ->
      equiv_assignments vs α1 α2.
  Proof.
    intros ? ? ? ? DISJ EQU ? EL.
    specialize (EQU v EL).
    destruct EQU as [b [EV1 EV2]].
    specialize (DISJ v); destruct DISJ as [DISJ _]; specialize (DISJ EL).
    exists b; split; eapply todo53; eauto 2.
  Qed.
 
  

  (* *)
  Lemma admit_equiv_nodup:
    forall (vs : variables) (α β : assignment),
      equiv_assignments vs α β <->
      equiv_assignments (nodup eq_var_dec vs) α β.
  Proof.
    intros vs α β; split; intros EQ.
  Admitted.

 

    
  Lemma admit_todo27:
    forall (vs vs_sub : variables) (α1 α2 : assignment),
      incl vs_sub vs ->
      equiv_assignments vs α1 α2 -> 
      equiv_assignments vs_sub α1 α2.
  Proof.
    intros ϕ x β1 β2 NEQ.
  Admitted.

  
  
  Lemma admit_todo41:
    forall (α1 α2 : assignment) (vs : list variable) (a : variable) (b : bool),
      a nel vs ->
      equiv_assignments (a::vs) ((a,b)::α1) ((a,b)::α2) ->
      equiv_assignments vs α1 α2.
  Proof.
    intros α1 α2 ? ? ? NEL EQU v EL.
    decide (v = a) as [EQ|NEQ]; subst.
    { exfalso; auto. }
    { specialize (EQU v); feed EQU; [right;auto| ].
      destruct EQU as [b' [EV1 EV2]].
      exists b'; split.
      admit (* Todo: 1/10 *).
      admit (* Todo: 1/10 *).  
    }
  Admitted.

  Lemma todo42:
    forall (α1 α2 : assignment) (vs : variables) (a : variable) (b : bool),
      ~ equiv_assignments (a :: vs) ((a, b)::α1) ((a, negb b)::α2).
  Proof.
    intros ? ? ? ? ? EQ.
    specialize (EQ a); feed EQ; [left; auto | ].
    destruct b; destruct EQ as [b [EV1 EV2]]; destruct b; (inversion_clear EV1; fail || inversion_clear EV2); auto. 
  Defined.
  

End Properties.


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


Lemma formula_eval_inj:
  forall (ϕ : formula) (α : assignment) (b1 b2 : bool),
    ℇ (ϕ) α ≡ b1 ->
    ℇ (ϕ) α ≡ b2 ->
    b1 = b2.
Proof.
  induction ϕ; intros ? ? ? EV1 EV2.
  all: inversion_clear EV1; inversion_clear EV2;
    auto 2; eauto 2 using todo2; destruct b1, b2; eauto.
Defined.

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

(* TODO: comment *)
Fixpoint number_of_nodes (ϕ: formula): nat :=
  match ϕ with
  | T | F | Var _ => 1
  | ¬ ϕ => 1 + number_of_nodes ϕ
  | ϕl ∨ ϕr => 1 + number_of_nodes ϕl + number_of_nodes ϕr
  | ϕl ∧ ϕr => 1 + number_of_nodes ϕl + number_of_nodes ϕr
  end.

 


Lemma admit_equiv_sat:
  forall (ϕ : formula) (α : assignment) (β : assignment),
    equiv_assignments (leaves ϕ) α β ->
    forall (b : bool), 
      ℇ (ϕ) α ≡ b ->
      ℇ (ϕ) β ≡ b.
Proof.
  intros ? ? ? EQ b EV.
  
Admitted.




Lemma admit_todo13:
  forall ϕ b v x α,
    v nel leaves ϕ ->
    ℇ (ϕ) α ≡ b <-> ℇ (ϕ) (v,x)::α ≡ b.
Proof.

Admitted.


(* TODO: move to Alg2. *)
Section FormulaSizeProperties.

  Lemma todo9:
    forall (ϕ : formula),
      formula_size (¬ ϕ) = formula_size ϕ.
  Proof.
    intros ?; unfold formula_size; simpl; reflexivity.
  Defined.

  Lemma todo10:
    forall (ϕl ϕr : formula),
      formula_size (ϕl ∧ ϕr) = formula_size ϕl + formula_size ϕr.
  Proof.
    intros; unfold formula_size; simpl; rewrite app_length; reflexivity.
  Defined.
    
  Lemma todo11:
    forall (ϕl ϕr : formula),
      formula_size (ϕl ∨ ϕr) = formula_size ϕl + formula_size ϕr.
  Proof.
    intros; unfold formula_size; simpl; rewrite app_length; reflexivity.
  Defined.

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
  Defined.
  
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
  Defined.

  Lemma todo19:
    forall (ϕl ϕr : formula) (x : variable),
      x el leaves (ϕl ∧ ϕr) ->
      {x el leaves ϕl} + {x el leaves ϕr}.
  Proof.
    intros ϕl ϕr x L.
    simpl in L; apply in_app_or_dec in L; auto using eq_var_dec.
  Defined.

  Lemma todo20:
    forall (ϕl ϕr : formula) (x : variable),
      x el leaves (ϕl ∨ ϕr) ->
      {x el leaves ϕl} + {x el leaves ϕr}.
  Proof.
    intros ϕl ϕr x L.
    simpl in L; apply in_app_or_dec in L; auto using eq_var_dec. 
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
  Defined.

  Lemma todo5:
    forall (ϕ: formula) (x: variable),
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
  Defined.

  Lemma admit_todo4:
    forall (ϕ : formula),
      formula_size ϕ > 0 -> 
      exists (x : variable),
        x el leaves ϕ /\
        formula_size (ϕ[x ↦ T]) < formula_size ϕ.
  Proof.
    intros ? SIZE.
    (* Todo: 3/10 *)
  Admitted.

  Lemma admit_todo12:
    forall ϕ v, 
      v nel leaves (ϕ [v ↦ T]).
  Proof.
    admit (* Todo: 1/10 *).
  Admitted.

  Lemma admit_todo14:
    forall ϕ v, 
      v nel leaves (ϕ [v ↦ F]).
  Proof.
    admit (* Todo: 1/10 *).
  Admitted.



End FormulaSizeProperties.


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
Definition equivalent (ϕ1 ϕ2 : formula) :=
  forall (α : assignment) (b : bool), ℇ (ϕ1) α ≡ b <-> ℇ (ϕ2) α ≡ b.

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
    { apply EQ in EV; assumption. }
    { apply EQ; assumption. }
  Qed.
    
  Lemma formula_equivalence_trans:
    forall (ϕ1 ϕ2 ϕ3 : formula),
      equivalent ϕ1 ϕ2 ->
      equivalent ϕ2 ϕ3 ->
      equivalent ϕ1 ϕ3.
  Proof.
    intros ? ? ? EV1 EV2 ? ?; split; intros EV.
    { apply EV2; apply EV1; assumption. }
    { apply EV1; apply EV2; assumption. }
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
  Defined.
  
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
  Defined.

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
  Defined.
  
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
  Defined.


  
  

  Lemma formula_equivalence_T_neg_F: 
    equivalent T (¬ F).
  Proof.
    intros α b; split; intros.
    - inversion_clear H; constructor; constructor.
    - inversion_clear H.
      destruct b; simpl in *.
      constructor.
      inversion_clear H0.
  Defined.


  Corollary admit_fo_eq_2:
    forall (ϕ1 ϕ2 : formula),
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
  Corollary admit_fo_eq_3:
    forall (ϕ1 ϕ2 : formula),
      equivalent ϕ1 F ->
      equivalent (ϕ1 ∧ ϕ2) F.
  Proof.
    intros.
    admit.
  Admitted.



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
  Defined.

  Corollary admit_fo_eq_21:
    forall (ϕ1 ϕ2 : formula),
      equivalent ϕ1 F ->
      equivalent ϕ2 F ->
      equivalent (ϕ1 ∨ ϕ2) F.
  Proof.
    intros.
    admit.
  Admitted.




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

  (* *)
  Lemma substitute_equiv':
    forall (ϕ ψ1 ψ2 : formula) (v : variable),
      (forall (α : assignment) (b : bool),        ℇ (ψ1) α ≡ b ->        ℇ (ψ2) α ≡ b) -> 
      (forall (α : assignment) (b : bool), ℇ (ϕ[v ↦ ψ1]) α ≡ b -> ℇ (ϕ[v ↦ ψ2]) α ≡ b).
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
  Defined.

  Lemma substitute_equiv:
    forall (ϕ ψ1 ψ2 : formula) (v : variable),
      equivalent ψ1 ψ2 ->
      equivalent (ϕ[v ↦ ψ1]) (ϕ[v ↦ ψ2]).
  Proof.
    intros; split.
    apply substitute_equiv'; apply H.
    apply substitute_equiv'; apply H.
  Defined.



End PropertiesOfEquivalence.


(** Next, we define a set of all satisfying assignment of a formula. *)
Section ListOfAllSatAssignment.
  
  (* Set of all satisfying assignment must not have any duplicates (up to equivalence).  *)
  Definition dupfree (vs: variables) (αs: assignments) :=
    dupfree_rel (equiv_assignments vs) αs.

  (* Set of all satisfying assignment contains only satisfying assignments. *)
  Definition set_with_sat_assignments (ϕ : formula) (αs : assignments) :=
    set_with (sat_assignment ϕ) αs.

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


End ListOfAllSatAssignment.

(* TODO: move to section *)
Notation "'#sat' ϕ '≃' n" := (number_of_sat_assignments ϕ n) (at level 10).


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
          eapply admit_todo41; eauto 2.
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
          eapply admit_todo41; eauto 2.
        } 
      }
    }
  Defined.

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
        { intros v EL2; destruct EL2 as [EQ|EL2]; subst.
          - exists true; split; auto. 
          - specialize (EQU v EL2); destruct EQU as [b [EV1 EV2]].
            exists b; decide (a = v) as [EQ|NEQ]; [ |split;auto]. 
            subst; split; [assumption| assert(H := todo2 _ _ _ _ EV1 MAP); subst; constructor].
        } 
        { simpl; apply in_app_iff; right.
          apply in_map_iff; exists β; split; auto.
        } 
      }
      { exfalso; apply NEL2; apply INCL; left; auto. } 
      { exists ((a,false)::β); split.
        { intros v EL2; destruct EL2 as [EQ|EL2]; subst.
          - exists false; split; auto. 
          - specialize (EQU v EL2); destruct EQU as [b [EV1 EV2]].
            exists b; decide (a = v) as [EQ|NEQ]; [ |split;auto]. 
            subst; split; [assumption| assert(H := todo2 _ _ _ _ EV1 MAP); subst; constructor].
        } 
        { simpl; apply in_app_iff; left.
          apply in_map_iff; exists β; split; auto.
        } 
      }      
    }
  Qed.
  
  Definition compute_formula (ϕ : formula) (α : assignment) (SET : sets_all_variables ϕ α):
    {b: bool | formula_eval ϕ α b}.
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
      repeat split. 
      { apply dffil.
        destruct(list_of_all_assignments_dupfree vars).
        - apply NoDup_nodup.
        - assumption.
      }
      { intros α1 α2 EL1 EL2 NEQ EQU.
        apply filter_In in EL1; destruct EL1 as [EL1 SAT1].
        apply filter_In in EL2; destruct EL2 as [EL2 SAT2].
        apply admit_equiv_nodup in EQU.
        apply list_of_all_assignments_dupfree in EQU; try (apply NoDup_nodup || assumption).
      } 
      { intros α EL. 
        apply filter_In in EL; destruct EL as [EL TR].
        unfold formula_sat_filter in *; destruct (sets_all_variables_dec ϕ α) as [D|D]; [ | easy].
        destruct (compute_formula ϕ α D) as [b EV]; subst b.
        assumption.
      } 
      { intros α [SETS SAT].
        assert (H := all_assignments_in_this_list vars α).
        feed H. { eapply incl_trans; eauto; apply incl_nodup. }          
        destruct H as [β [EQ EL]].
        exists β; repeat split.
        - apply admit_equiv_nodup; assumption.
        - apply filter_In; split; [assumption | ].
          unfold formula_sat_filter; destruct (sets_all_variables_dec ϕ β) as [S|S].
          + apply admit_equiv_nodup in EQ.
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
  Compute (proj1_sig (algorithm1 (x1 ⊕ x2 ⊕ x3 ⊕ x4 ⊕ x5))).
  Compute (proj1_sig (algorithm1 (x1 ∨ x2 ∨ x3 ∨ x4 ∨ x5))).

  
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

  
 


  Lemma admit_count3:
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

  Lemma admit_count5:
    forall (ϕ: formula),
      formula_size ϕ = 0 -> 
      equivalent ϕ T -> 
      number_of_sat_assignments ϕ 1.
  Proof.
    intros.
  Admitted.

  Lemma admit_count4: 
    number_of_sat_assignments F 0.
  Proof.
    intros.
    exists []; repeat split; intros.
    - constructor.
    - easy.
    - easy.
    - admit.
  Admitted.

  Lemma admit_count6:
    forall (ϕ: formula),
      formula_size ϕ = 0 -> 
      equivalent ϕ F -> 
      number_of_sat_assignments ϕ 0.
  Proof.
    intros.
  Admitted.

  
  Lemma admit_todo57:
    forall (ϕ : formula) (x : variable), incl (leaves (ϕ [x ↦ T])) (leaves ϕ).
  Proof.
    intros ϕ x.
  Admitted.
    
  Lemma admit_todo58:
    forall (ϕ : formula) (x : variable), incl (leaves (ϕ [x ↦ F])) (leaves ϕ).
  Proof.
    intros ϕ x.
  Admitted.


  Section BaseCase.

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
          + left; apply admit_fo_eq_2; auto.
          + right; clear IH1.
            apply formula_equi_1, admit_fo_eq_3; auto.
        - right; clear IHϕ2.
          apply admit_fo_eq_3; auto.
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
            apply admit_fo_eq_21; auto; apply fo_eq_11.
      }
    Defined.
    

  End BaseCase.
  
  Section Induc.



    Variable ϕ : formula.
    Variable x : variable.

    Hypothesis H_leaf : x el leaves ϕ.


        
    Lemma admit_switch:
      forall (ϕ : formula) (x : variable),
        equivalent ϕ ([|x|] ∧ ϕ[x ↦ T] ∨ ¬[|x|] ∧ ϕ[x ↦ F]). 
    Proof.
      
    Admitted.

    

    
    Variables αs1 αs2 : assignments.
    
    
    Lemma admit_todo54:
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
          [assumption | apply admit_todo57 | apply admit_todo12].
      }
      { specialize (NEQ x).
        feed NEQ; [assumption | ].
        destruct NEQ as [b [ EV1 EV2]].
        apply in_map_iff in EL1; apply in_map_iff in EL2.
        destruct EL1 as [α1_tl [EQ1 _]], EL2 as [α2_tl [EQ2 _]]; subst α1 α2.
        inversion EV1; subst; auto.
        inversion EV2; subst; auto.
      }
      { specialize (NEQ x).
        feed NEQ; [assumption | ].
        destruct NEQ as [b [ EV1 EV2]].
        apply in_map_iff in EL1; apply in_map_iff in EL2.
          destruct EL1 as [α1_tl [EQ1 _]], EL2 as [α2_tl [EQ2 _]]; subst α1 α2.
            inversion EV1; subst; auto.
            inversion EV2; subst; auto.
            }
            { apply in_map_iff in EL1; destruct EL1 as [β1 [EQ1 EL1]].
              apply in_map_iff in EL2; destruct EL2 as [β2 [EQ2 EL2]]; subst α1 α2.
              specialize (NE2 _ _ EL1 EL2).
              feed NE2; [intros C; apply EQ; rewrite C; reflexivity | ].
              apply NE2; clear NE2.
              apply todo28 with (vs_sub := leaves (ϕ [x ↦ F])) in NEQ;
                [assumption | apply admit_todo58 | apply admit_todo14].
            }
            }
    Qed.

    (* Note that it is not a brute-force. *)
    Lemma todo55:
      set_with_sat_assignments (ϕ [x ↦ T]) αs1 -> 
      set_with_sat_assignments (ϕ [x ↦ F]) αs2 -> 
      set_with_sat_assignments
        ϕ (map (cons (x, true)) αs1 ++ map (cons(x, false)) αs2).
    Proof.
      intros SAT1 SAT2; intros α ELt.
      apply admit_switch with x.
      apply in_app_or in ELt; destruct ELt as [EL|EL].
      { apply ev_disj_tl, ev_conj_t.
        { apply in_map_iff in EL.
          destruct EL as [mα [EQ1 MEM1]]; subst α; auto.
        } 
        { apply in_map_iff in EL.
          destruct EL as [mα [EQ MEM]]; subst α.
          apply admit_todo13.
          apply admit_todo12.
          apply SAT1; assumption.
        }
      }
      { apply ev_disj_tr, ev_conj_t.
        { apply in_map_iff in EL.
          destruct EL as [mα [EQ MEM]]; subst α; auto.
        }
        { apply in_map_iff in EL.
          destruct EL as [mα [EQ MEM]]; subst α.
          apply admit_todo13. apply admit_todo14.
          apply SAT2; assumption.
        }
      }
    Qed.
  
  Lemma admit_todo56:
      list_of_all_sat_assignments (ϕ [x ↦ T]) αs1 ->
      list_of_all_sat_assignments (ϕ [x ↦ F]) αs2 ->
      set_with_all_sat_assignments ϕ (map (cons (x, true)) αs1 ++ map (cons (x, false)) αs2).
  Proof.
    intros LAA1 LAA2.
    intros α [SETS SAT]; apply admit_switch with (x:=x) in SAT.
    assert (t: forall (α: assignment) (H: sets_all_variables ϕ α), sets_all_variables (ϕ [x ↦ T]) α ).
    { admit. }
    assert (f: forall (α: assignment) (H: sets_all_variables ϕ α), sets_all_variables (ϕ [x ↦ F]) α ).
    { admit. }

    
    
      
      inversion_clear SAT; inversion_clear H.
      

      
      {
        
        unfold list_of_all_sat_assignments in *.
        destruct LAA1 as [M1 [M2 M3]].
        unfold set_with_all_sat_assignments, set_with_all in M3.

      
        specialize (M3 α); feed M3. split. apply t; auto. auto. 
        destruct M3 as [β [EQ EL]].
        inversion_clear H0. 

        exists ((x,true)::β); split.
        { intros v ELl.
          decide (v = x) as [E|NEQ]; [subst | ].
          exists true; split; [assumption| constructor].
          specialize (EQ v).
          admit (* Todo: 4/10 *). }
        { apply in_app_iff; left.
          apply in_map_iff; exists β; easy.
        }
      }
      {


            unfold list_of_all_sat_assignments in *.
        destruct LAA2 as [M1 [M2 M3]].
        unfold set_with_all_sat_assignments, set_with_all in M3.

      
        specialize (M3 α); feed M3. split. apply f; auto. auto. 
        destruct M3 as [β [EQ EL]].

        inversion_clear H0. 
        exists ((x,false)::β); split.
        { admit (* Todo: 6/10 *). }
        apply in_app_iff; right.
        apply in_map_iff; exists β; easy.
      }


    Admitted.
    
      

  End Induc.
    
    Definition admit_algorithm2:
      forall (ϕ : formula), {n : nat | number_of_sat_assignments ϕ n}.
    Proof.
      apply size_recursion with formula_size; intros ϕ IHϕ. 
      destruct (formula_size_dec ϕ) as [Zero|Pos].
      { destruct (zero_size_formula_constant_dec ϕ Zero) as [Tr|Fl].
        - exists 1; apply admit_count5; assumption.
        - exists 0; apply admit_count6; assumption. } 
      { assert (V := get_var _ Pos).
        destruct V as [x IN]; clear Pos.
        assert (IH1 := IHϕ (ϕ[x ↦ T])); assert(IH2 := IHϕ (ϕ[x ↦ F])); clear IHϕ.
        specialize (IH1 (todo3 _ _ IN)); specialize (IH2 (todo5 _ _ IN)).
        destruct IH1 as [nl EQ1], IH2 as [nr EQ2].
        exists (nl + nr).
        destruct EQ1 as [αs1 [LAA1 LEN1]], EQ2 as [αs2 [LAA2 LEN2]].
        exists (map (fun α => (x, true)::α) αs1 ++ map (fun α => (x,false)::α) αs2).
        split; [split; [ | split] | ].
        { destruct LAA1 as [ND1 _], LAA2 as [ND2 _]; apply admit_todo54; auto. }
        { destruct LAA1 as [_ [SAT1 _]], LAA2 as [_ [SAT2 _]]; apply todo55; auto. }
        { apply admit_todo56; assumption. } 
        { rewrite app_length, map_length, map_length, <- LEN1, <- LEN2; reflexivity. } 
      } 
    Defined.

    (* => 32 *)
    Compute (proj1_sig (admit_algorithm2 (x1 ⊕ x2 ⊕ x3 ⊕ x4 ⊕ x5 ⊕ x6))).

End Algorithm2.

(** * Algorithm 3: *)
(** With certificates and DNF *)
Section Algorithm3.

  (* Algorithm
   1) Transform ϕ to dnf
   2) Map each monomial into a certificate1
   3) By construction, all these certificates are disjoint
   4) Calculate the number of sat. assignments
   *)


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
    Defined.


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
    Defined.

    Compute (proj1_sig (move_negations (¬ (x0 ∨ x1) ∧ (x2 ∨ x3)))).

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
    Defined.

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
    Defined.

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
    Defined.

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
    Defined.

    Section And.
      
      (* TODO: comment *)
      Definition flat_product {X: Type} (xs ys: list (list X)):list(list X) :=
        flat_map (fun (y:list X) =>
                    map (fun (x: list X) => x ++ y) xs) ys.

      (* => [[x0;x1; x4;x5]; [x2;x3; x4;x5]; [x0;x1; x6;x7]; [x2;x3; x6;x7]] *)
      Compute (flat_product ([[x0;x1];[x2;x3]]) ([[x4;x5];[x6;x7]])).

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
      Defined.

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
    Defined.

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
    Defined.

    Compute (proj1_sig (to_dnf ((x0 ∨ x1) ∧ (x0 ∨ x2)))).

    End FormulaToDNF.
    
  (* TODO: name *)
  (* TODO: comment *)
  Section Name1.

    (* TODO: comment *)
    Fixpoint monomial_to_certificate (m : monomial): assignment :=
      match m with
      | [] => []
      | Positive v :: m' => (v, true) :: monomial_to_certificate m'
      | Negative v :: m' => (v, false) :: monomial_to_certificate m'
      end.

    (* Note that [monomial_to_certificate] can fail on an unsatisfiable monomial. *)
    Example todo29:
      let var := V 0 in
      let mon := [Negative var; Positive var] in
      let α := monomial_to_certificate mon in 
      monomial_unsat_assignment mon α.
    Proof.
      intros; unfold monomial_unsat_assignment, mon in *; clear mon.
      constructor; exists (Positive var); split.
      - right; left; reflexivity.
      - simpl; constructor; constructor.
    Qed.
    
    Definition no_confl_literals (mon : monomial) :=
      ~ exists v, Positive v el mon /\ Negative v el mon.

    Lemma admit_todo30:
      forall (mon : monomial),
        no_confl_literals mon <-> monomial_satisfiable mon.
    Proof.
    Admitted.
    
    Lemma admit_todo31:
      forall (mon : monomial),
        monomial_satisfiable mon <->
        monomial_sat_assignment mon (monomial_to_certificate mon).
    Proof.
    Admitted.

    Definition admit_dec_mon_sat (m : monomial):
      {monomial_satisfiable m} + {monomial_unsatisfiable m}.
    Proof.
    Admitted.

    Definition all_monomials_satisfiable (ψ : dnf) :=
      forall (m : monomial), m el ψ -> monomial_satisfiable m.
    
    Definition admit_delete_unsat_monomials (ψ : dnf):
      {ψ_sm : dnf | equivalent_dnf ψ ψ_sm
                    /\ all_monomials_satisfiable ψ_sm}.
    Proof.
      exists (filter (fun m => if admit_dec_mon_sat m then true else false) ψ); split.
      { split; intros EV.
        - inversion_clear EV.
          + destruct H as [m [EL SAT]].
            constructor; exists m; split. admit. admit.
          + constructor; intros ? EV; exfalso.
            apply filter_In in EV; destruct EV as [EL EV].
            specialize (H _ EL).
            admit.
        - admit.
      } 
      { intros ? EL.
        admit.
      }
    Admitted.

  End Name1.

  (* TODO: comment *)
  (* TODO: name *)
  Section Name2.

    Definition comparable {X : Type} (xs ys : list X) :=
      incl xs ys \/ incl ys xs.

    Definition all_monomials_disjoint (ψ : dnf) :=
      dupfree_rel comparable ψ.

    Definition admit_delete_comparable_monomials (ψ : dnf):
      {ψ_disj : dnf | equivalent_dnf ψ ψ_disj
                      /\ all_monomials_disjoint ψ_disj}. 
    Proof.
    Admitted.

  End Name2.

  Section Name3.

      (* TODO: comment *)
(* Definition disjoint_assignments (vs : variables) (α1 α2 : assignment) :=
  exists (v : variable) (b : bool),
    v el vs /\
    v / α1 ↦ b /\
    v / α2 ↦ (negb b). *)

    
    Definition ext_assignment (α ext_α : assignment) :=
      forall (v : variable) (b : bool),
        v el vars_in α ->
        v / α ↦ b ->
        v / ext_α ↦ b.

    Definition certificate1 (ϕ : formula) (ξ : assignment) :=
      forall ext_α, ext_assignment ξ ext_α -> ℇ (ϕ) ext_α ≡ true.

    Definition certificate0 (ϕ : formula) (ξ : assignment) :=
      forall ext_α, ext_assignment ξ ext_α -> ℇ (ϕ) ext_α ≡ false.

    
    Definition sig_monomial_to_certificate1: 
      forall (ϕ : formula) (ψ : dnf) (m : monomial),
        dnf_representation ϕ ψ ->
        m el ψ -> 
        monomial_satisfiable m -> 
        { ξ:assignment | certificate1 ϕ ξ }.
    Proof.
    Admitted.
    
    
    Definition set_with_all_extensions_on (α: assignment) (vs: variables) (αs: assignments) :=
      set_with_all (equiv_assignments vs) (ext_assignment α) αs.

    Definition all_extensions_on (α: assignment) (vs: variables): assignments :=
      map (fun β => α ++ β) (all_assignments_on vs).
    
    Lemma size_of_list_of_all_extensions:
      forall (α : assignment) (vs : variables),
        length (all_extensions_on α vs) = Nat.pow 2 (length vs).
    Proof.
      induction vs; simpl. 
      { reflexivity. }
      { unfold all_extensions_on in *; simpl.
        rewrite !map_length in IHvs.
        rewrite !map_length, app_length, !map_length, <- plus_n_O, <- IHvs.
        reflexivity. } 
    Qed.
    
    Lemma list_of_all_extensions_dupfree:
      forall (α : assignment) (vs : variables),
        NoDup vs -> 
        disj_sets (vars_in α) vs ->
        dupfree vs (all_extensions_on α vs). 
    Proof.
      intros ? ? ND DISJ; split. 
      { clear ND DISJ; induction vs.
        - unfold all_extensions_on; simpl; constructor.
          intros C; inversion_clear C.
          constructor; intros C; inversion_clear C.
        - unfold all_extensions_on; simpl.
          apply todo40, dfnn_ext.
          + easy.
          + unfold all_extensions_on in IHvs.
            apply todo40 in IHvs. 
            assumption.
          + unfold all_extensions_on in IHvs.
            apply todo40 in IHvs. 
            assumption.
      }
      { intros α1 α2 EL1 EL2 NEQ EQ. 
        apply in_map_iff in EL1; apply in_map_iff in EL2.
        destruct EL1 as [α1_tl [EQ1 EL1]].
        destruct EL2 as [α2_tl [EQ2 EL2]].
        rewrite <-EQ1, <- EQ2 in NEQ, EQ; clear EQ1 EQ2 α1 α2. 
        apply app_disj in NEQ. 
        apply equiv_assign_disj_update in EQ.
        { refine (proj2 (list_of_all_assignments_dupfree _ ND) _ _ _ _ NEQ _); assumption. }
        { apply disj_sets_sym; assumption. }
      }        
    Qed.

    (* TODO: fix name *)
    Lemma admit_all_extensions_in_this_list:
      forall (vs: variables) (α: assignment), 
        set_with_all_extensions_on α vs (all_assignments_on vs).
    Proof.
      induction vs.
      { intros α ext_α EXT.
        exists []; simpl. admit (* Todo: 2/10 *). }
      { intros α ext_α EXT.
        simpl in *.
        admit (* Todo: 8/10 *).
      }
    Admitted.

    
  
    (* TODO: general form *)
    Fixpoint list_minus  (xs : variables) (ys : variables): variables :=
      match xs with
      | [] => []
      | h::tl => if decision (h el ys) then list_minus tl ys else h :: list_minus tl ys
      end.

    (* TODO: comment *)
    Definition cert_to_assigns (ϕ: formula) (ξ: assignment): assignments :=
      all_extensions_on ξ (list_minus (formula_vars ϕ) (vars_in ξ)).
    
    Definition certs_to_assigns (ϕ: formula) (ξs: assignments): assignments :=
      flat_map (cert_to_assigns ϕ) ξs.
    

    
    (* TODO: comment *)
    Definition dnf_to_certs (ψ: dnf): assignments := map monomial_to_certificate ψ.
(*
    
    
    Lemma admit_flat_map_nodup:
      forall (X : Type) (f : list X -> list (list X)) (xss: list (list X)),
        NoDup xss ->
        (forall xs, xs el xss -> NoDup (f xs)) ->
        NoDup (flat_map f xss).
    Proof.
      intros ? ? ? ND1 ND2.
    Admitted.

 *)
    
    Lemma admit_todo60:
      forall {X : Type} (l l' : list X),
        NoDup (l ++ l') <-> disj_sets l l' /\ NoDup l /\ NoDup l'.
    Proof.
      intros ? A B; split; intros ND.
      { repeat split.
        - intros ELA ELB. admit (* Ok *).
        - intros ELB ELA. admit (* Ok *).
        - admit (* Ok *).
        - admit (* Ok *).
          
      }
      { destruct ND as [DISJ [NDA NDB]].
        induction A.
        { simpl; assumption. }
        { 
          simpl. apply NoDup_cons_iff; split. 
          - intros EL.
            admit (* Ok *).
          - apply IHA. admit.  admit.
        }
      }
      (* Todo: 2/10 *)
    Admitted.

    Lemma todo59:
      forall (X : Type) (f : X -> list X) (xs : list X),
        (forall a, a el xs -> NoDup (f a)) ->
        (forall a b, a el xs -> b el xs -> intrs_sets (f a) (f b) -> a = b) -> 
        NoDup xs ->
        NoDup (flat_map f xs).
    Proof.
      intros ? ? ? ND INJ NDL.
      induction xs.
      { assumption. } 
      { apply NoDup_cons_iff in NDL; destruct NDL  as [NEL NDL].
        feed_n 3 IHxs; auto.
        { intros; apply ND; right; assumption. }
        { intros; apply INJ; try right; assumption. }
        simpl; apply admit_todo60; repeat split.
        { intros EL ELf.
          apply in_flat_map in ELf; destruct ELf as [b [ELb ELf]].
          specialize (INJ a b).
          feed_n 3 INJ.
          { left; reflexivity. }
          { right; assumption. }
          { exists x; split; assumption. }
          subst b; apply NEL; assumption.
        }
        { intros ELf EL.
          apply in_flat_map in ELf; destruct ELf as [b [ELb ELf]].
          specialize (INJ a b).
          feed_n 3 INJ.
          { left; reflexivity. }
          { right; assumption. }
          { exists x; split; assumption. }
          subst b; apply NEL; assumption.
        }
        { apply ND; left; reflexivity. }
        { assumption. }
      } 
    Qed.      

    Lemma admit_todo61:
      forall (ϕ : formula) (ψ : dnf) (α : assignment),
        dnf_representation ϕ ψ ->
        α el dnf_to_certs ψ ->
        NoDup (cert_to_assigns ϕ α).
    Proof.
      intros ϕ ψ α REP CERT.
    Admitted.
      
    Lemma admit_todo33:
      forall (ϕ : formula) (ψ : dnf),
        dnf_representation ϕ ψ ->
        all_monomials_disjoint ψ -> 
        dupfree (leaves ϕ) (certs_to_assigns ϕ (dnf_to_certs ψ)).
    Proof.
      intros ϕ ψ REP DISJ; split.
      { apply todo59.
        { intros α CERT; eapply admit_todo61; eauto. }
        { intros ξ1 ξ2 CE1 CE2 INT.
          destruct INT as [α [IN1 IN2]].
          apply in_map_iff in IN1; apply in_map_iff in IN2.
          destruct IN1 as [ext_ξ1 [EQ1 _]], IN2 as [ext_ξ2 [EQ2 _]]; subst α.
          decide (ξ1 = ξ2) as [EQ|NEQ]; [assumption | exfalso].
          destruct DISJ as [ND NE].
          admit (* Follows from disj of monomials. Todo: 7/10 *).
                                                              
          
          
                    
          
        }
        { 
          admit (* Assumption: 0/10 *). }
      } 
      { intros α1 α2 EL1 EL2 NEQ EQU.
        apply in_flat_map in EL1; apply in_flat_map in EL2.
        destruct EL1 as [ξ1 [EC1 EL1]], EL2 as [ξ2 [EC2 EL2]].
        apply in_map_iff in EC1; apply in_map_iff in EC2.

        admit (* Again, disj_monomials -> disj_assignments *).
        (* destruct EC1 as [m1 [EQ1 EM1]], EC2 as [m2 [EQ2 EM2]]; subst ξ1 ξ2.
        decide (m1 = m2) as [E|NEQ2].
        { subst m1; rename m2 into m.
          apply in_map_iff in EL1; apply in_map_iff in EL2.
          destruct EL1 as [ex1 [EQ1 EL1]], EL2 as [ex2 [EQ2 EL2]]; subst α1 α2.
          apply app_disj in NEQ.
          admit (* Todo: 6/10 *).
        }
        { (* NoDup (mons) -> α1 !≡ α2 *)
          admit (* Todo: 8/10 *).
        }  *)
        
      }            
    Admitted.

    Lemma admit_todo34:
      forall (ϕ : formula) (ψ : dnf),
        dnf_representation ϕ ψ -> 
        set_with_sat_assignments ϕ (certs_to_assigns ϕ (dnf_to_certs ψ)).
    Proof.
      intros ϕ ψ DNF α EL.
      apply in_flat_map in EL; destruct EL as [ξ [EL1 EL2]].
      apply in_map_iff in EL1; destruct EL1 as [m [MON EL1]].
      apply in_map_iff in EL2; destruct EL2 as [ξ_ex [EQ EL2]]; subst α.
      (* nodup in m -> valid cert -> done *)
      admit (* Todo: 8/10 *).
    Admitted.


    Lemma admit_todo35:
      forall (ϕ : formula) (ψ : dnf),
        dnf_representation ϕ ψ -> 
        set_with_all_sat_assignments ϕ (certs_to_assigns ϕ (dnf_to_certs ψ)).
    Proof.
      intros ϕ ψ DNF α [SETS SAT].
      apply DNF in SAT.
      inversion_clear SAT.
      destruct H as [m [EL SM]].

      
      assert(cert1 := sig_monomial_to_certificate1 _ _ _ DNF EL).
      feed cert1. exists α; auto.
(*
      destruct cert1 as [ξ CERT].

      assert(EX: exists n, length (list_minus (formula_vars ϕ) (vars_in ξ)) <= n). 
      { admit. }

      destruct EX as [n B].
      induction n.
      exists ξ.
      admit (* Todo: 9/10 *).
*)
      
      
      
      unfold dnf_to_certs, certs_to_assigns.
      unfold cert_to_assigns.
      
      exists α; split.
      { admit. }
      {
        apply in_flat_map. 
        unfold dnf_to_certs.
 
      
      unfold certs_to_assigns.
      
      
      admit (* Todo: 7/10 *).
    Admitted.


  End Name3.

    
    Definition admit_algorithm3': 
      forall (ϕ : formula) (ψ : dnf),
        dnf_representation ϕ ψ ->  
        {n: nat | number_of_sat_assignments ϕ n}.
    Proof.
      intros ? ? DNF.
      set (vars := formula_vars ϕ).
      set (n_vs := length vars). 
      exists (fold_right Nat.add 0 (map (fun n => Nat.pow 2 n) (map (fun m => n_vs - length m) ψ))).
      exists (certs_to_assigns ϕ (dnf_to_certs ψ)); repeat split.
      { apply admit_todo33; assumption. }
      { apply admit_todo33; assumption. }
      { apply admit_todo34; assumption. }
      { apply admit_todo35; assumption. }
      { clear DNF; induction ψ.
        { reflexivity. }
        { simpl; rewrite app_length, IHψ, Nat.add_cancel_r; clear IHψ.
          unfold cert_to_assigns.
          admit (* Todo: 4/10 *).
        }
      }     
    Admitted.
    

  Definition algorithm3 (ϕ : formula): {n : nat | number_of_sat_assignments ϕ n}.
  Proof.
    destruct (to_dnf ϕ) as [ψ REP].
    destruct (admit_delete_unsat_monomials ψ) as [ψ_sm [EQ1 SM]].
    destruct (admit_delete_comparable_monomials ψ_sm) as [ψ_sm_dm [EQ2 DM]].
    apply admit_algorithm3' with ψ_sm_dm.
    apply admit_tr_eq_rep_2 with ψ_sm; [assumption | ].
    apply admit_tr_eq_rep_2 with ψ; assumption.
  Defined.
 
  Compute (proj1_sig (algorithm3 (x1 ⊕ x2))).

End Algorithm3.




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
(* Lemma assignments_equiv_dec:
  forall vs α1 α2, dec (equiv_assignments vs α1 α2).
Proof.
Admitted. *)

(* There is a problem that is related to the fact that 
   two assignments can be equivalent, but not equal. 
   But we still need to consider a list of assignments and so on.
   So, I intrtoduce a new predicate for IN. 
 *)




(* Definition incl_a (vs: variables) (αs1 αs2: assignments): Prop :=
  incl_e (equiv_assignments vs) αs1 αs2.

Definition equiv_a (vs: variables) (αs1 αs2: assignments): Prop :=
  equiv_e (equiv_assignments vs) αs1 αs2. *)
  
