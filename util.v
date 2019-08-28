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
Ltac feed_n n H :=
  match constr:(n) with
  | O => idtac
  | (S ?m) => feed H ; [| feed_n m H]
  end.

(* TODO: *)
(** * Smolka's *)

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

Definition equi {X: Type} (A B: list X) : Prop :=
  incl A B /\ incl B A.

Hint Unfold equi.

Instance list_in_dec {T: Type} (x: T) (xs: list T): 
  eq_dec T -> dec (x el xs).
Proof.
  intros D; apply in_dec; exact D.
Defined. (* Todo: Qed? *)


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
Defined. (* Todo: Qed? *)




(** Qed. ~> Defined. *)

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
Defined. (* Todo: Qed? *)

Lemma singl_in {X: Type} (x y: X):
  x el [y] -> x = y.
Proof.
  intros.
  inversion_clear H; [subst; reflexivity | inversion_clear  H0].
Defined. (* Todo: Qed? *)

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
Defined. (* Todo: Qed? *)

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
Defined. (* Todo: Qed? *)

Lemma NoDup_nodup {A : Type} (decA: eq_dec A) l: NoDup (nodup decA l).
Proof.
  induction l as [|a l' Hrec]; simpl.
  - constructor.
  - destruct (in_dec decA a l'); simpl.
    * assumption.
    * constructor; [ now rewrite nodup_In | assumption].
Defined. (* Todo: Qed? *)

(** * ??? *)



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
Defined. (* Todo: Qed? *)





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
    NoDup xs ->
    (forall a, a el xs -> NoDup (f a)) ->
    (forall a b, a el xs -> b el xs -> intrs_sets (f a) (f b) -> a = b) -> 
    NoDup (flat_map f xs).
Proof.
  intros ? ? ? NDL ND INJ.
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


(** * TODO *)
(** * Predicates on lists with equivalence *)

(* TODO: name *)
Section Sec1. 

  Context {X : Type}.
  Hypothesis X_dec: eq_dec X.
  
  Variable R : X -> X -> Prop.

  Hypothesis R_refl: forall x, R x x.
  Hypothesis R_sym: forall x y, R x y -> R y x.

  Fixpoint mem_rel (x : X) (xs : list X): Prop :=
    match xs with
    | [] => False
    | h::tl => (R x h) \/ (mem_rel x tl)
    end.

  Instance admit_mem_rel_dec:
    forall (x : X) (xs : list X), dec (mem_rel x xs).
  Proof.
    induction xs.
    - right; intros C; destruct C.
    - admit.
  Admitted.
    
  
  Lemma todo36:
    forall (a x : X) (xs : list X),
      mem_rel a xs -> mem_rel a (x::xs).
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
  Defined. (* Todo: Qed? *)

  
  Lemma todo24:
    forall (a x : X) (xs : list X),
      ~ mem_rel a (x :: xs) -> ~ mem_rel a xs.
  Proof.
    intros a ax xs.
    assert (H: forall (A B: Prop), (A -> B) -> (~ B -> ~ A)).
    { clear; intros ? ? f nb a; auto. }
    apply H; apply todo36.
Defined. (* Todo: Qed? *)

        
  Lemma todo23:
    forall (a : X) (xs : list X),
      ~ mem_rel a xs -> forall x, x el xs -> ~ R a x. 
  Proof.
    intros a xs NM x EL NR.
    induction xs.
    { destruct EL. }
    { destruct EL as [EQ|EL]; subst.
      apply NM; left; assumption.
      apply todo24 in NM; feed IHxs; auto. }
Defined. (* Todo: Qed? *)


  Lemma todo26:
    forall (a : X) (xs : list X),
      mem_rel a xs -> exists x, x el xs /\ R a x.
  Proof.
    intros a xs MEM; induction xs.
    { inversion MEM. }
    { destruct MEM as [Ra|MEM].
      - exists a0; split; [left | ]; auto.
      - feed IHxs; auto. destruct IHxs as [x [EL Ra]].
        exists x; split; [right | ]; auto.
    } 
Defined. (* Todo: Qed? *)


  Lemma todo25:
    forall (x : X) (xs : list X), x el xs -> mem_rel x xs.
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
    | h::tl => (~ mem_rel h tl) /\ (dupfree_rel_classic tl)
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

  Fixpoint dupfree_comp (xs : list X): list X :=
    match xs with
    | [] => []
    | x::xs => if decision (mem_rel x xs)
              then dupfree_comp xs
              else x :: dupfree_comp xs
    end.

(*  Lemma admit_todo7:
    forall (x : X) (xs : list X),
      x el xs ->
      x nel dupfree_comp xs ->
      exists y, R x y /\ y el dupfree_comp xs. 
  Proof.
    intros ? ? EL NEL.
    
  Admitted. *)

  Lemma admit_75:
    forall (xs ys : list X),
      dupfree_rel xs ->
      dupfree_rel ys ->
      length xs > length ys ->
      exists x, x el xs /\ forall y, y el ys -> ~ R x y. 
  Proof.
    intros ? ? [ND1 DF1] [ND2 DF2] LT.
    assert(EX: exists n, length xs <= n). admit.
    destruct EX as [n LEN].
    generalize dependent ys; generalize dependent xs.
    induction n; intros; [admit| ].
    apply Nat.le_succ_r in LEN; destruct LEN as [LEN|LEN].
    - admit. 
    - 
      (* feed_n 3 IHys. admit. admit. admit. *)
      
      
      
  Admitted.
      
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
Defined. (* Todo: Qed? *)



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
Defined. (* Todo: Qed? *)

 
Corollary todo38:
  forall (X : Type) (xss : list (list X)) (x : X),
    NoDup xss <->  NoDup (map (fun xs => x :: xs) xss).
Proof.
  intros ? ? ?.
  apply todo39; auto.
  clear; intros; inversion H; reflexivity.
Defined. (* Todo: Qed? *)


  
Corollary todo40:
  forall (X : Type) (xss : list (list X)) (xsl: list X),
    NoDup xss <-> NoDup (map (fun xsr => xsl ++ xsr) xss).
Proof.
  intros.
  apply todo39. 
  clear; intros ? ? EQ.
  induction xsl; simpl in EQ; [assumption | inversion EQ]; auto.
Defined. (* Todo: Qed? *)



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
Defined. (* Todo: Qed? *)


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
Defined. (* Todo: Qed? *)

    
    
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
 