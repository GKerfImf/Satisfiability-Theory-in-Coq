Require Export List Omega.
Import ListNotations.

(** * Feed tactic. *)

Ltac feed H :=
  match type of H with
  | ?foo -> _ =>
    let FOO := fresh in
    assert foo as FOO; [|specialize (H FOO); clear FOO]
  end.

Ltac feed_n n H :=
  match constr:(n) with
  | O => idtac
  | (S ?m) => feed H ; [| feed_n m H]
  end.

(** * Base *)
(* (taken from http://www.ps.uni-saarland.de/~hofmann/bachelor/coq/toc.html) *)

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

Lemma size_recursion (X : Type) (σ : X -> nat) (p : X -> Type):
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

Definition equi {X : Type} (A B : list X) : Prop :=
  incl A B /\ incl B A.

Hint Unfold equi.
Notation "A ⊆ B" := (incl A B) (at level 70).

Instance list_eq_dec X:
  eq_dec X -> eq_dec (list X).
Proof.
  intros D; apply list_eq_dec; exact D.
Defined.

Instance list_in_dec {X : Type} (x : X) (xs : list X): 
  eq_dec X -> dec (x el xs).
Proof.
  intros D; apply in_dec; exact D.
Defined.

Instance inclusion_dec {X : Type} (xs1 xs2 : list X):
  eq_dec X -> dec (xs1 ⊆ xs2).
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
Qed. 

(** * Standard Library: Qed ⤳ Defined *)

Lemma app_length:
  forall {X : Type} (l l' : list X),
    length (l++l') = length l + length l'.
Proof.
  induction l; simpl; auto.
Defined.

Lemma plus_is_O n m:
  n + m = 0 -> n = 0 /\ m = 0.
Proof.
  destruct n; now split.
Defined.

(** * Misc *)

Definition set_with {X : Type} (p : X -> Prop) (xs : list X) : Prop :=
  forall x, x el xs -> p x.

Definition set_with_all {X : Type} (rel : X -> X -> Prop) (p : X -> Prop) (xs : list X) : Prop :=
  forall x, p x -> exists y, rel x y /\ y el xs.

Section Rem.

  Context {X : Type}.
  Hypothesis X_dec: eq_dec X.
  
  Fixpoint rem (xs : list X) (a : X) : list X :=
    match xs with
    | [] => []
    | x::xs => if decision (a = x) then rem xs a else x::rem xs a
    end.

  Lemma rem_neq:
    forall (xs : list X) (a b : X),
      a el xs ->
      a <> b ->
      a el rem xs b.
  Proof.
    induction xs as [ | x xs]; intros ? ? EL NEQ.
    - destruct EL.
    - destruct EL as [EQ|EL]; [subst| ].
      simpl; decide (b = a); [exfalso|left]; auto.      
      simpl; decide (b = x); [subst|right]; auto.
  Qed.

  Lemma rem_length_le:
    forall (a : X) (xs : list X),
      length (rem xs a) <= length xs.
  Proof.
    intros ? ?; induction xs.
    - simpl; auto.
    - simpl; decide (a = a0); simpl.
      apply Nat.le_trans with (length xs); auto.
      apply le_n_S; auto.
  Qed.

  Lemma rem_length_lt:
    forall (a : X) (xs : list X),
      a el xs -> 
      length (rem xs a) < length xs.
  Proof.
    intros ? ? EL; induction xs.
    - destruct EL.
    - destruct EL as [EQ|EL]; [subst a0| ]; simpl.
      + decide (a = a) as [_| ];[ | exfalso; auto]; clear IHxs.
        apply Nat.lt_succ_r, rem_length_le.
      + decide (a = a0).
        apply Nat.lt_succ_r, rem_length_le.
        simpl; apply le_n_S, lt_le_S; auto.
  Qed.

End Rem.

Lemma singl_in {X : Type} (x y : X):
  x el [y] -> x = y.
Proof.
  intros.
  inversion_clear H; [subst; reflexivity | inversion_clear  H0].
Qed.

Lemma in_cons_or_dec:
  forall {X : Type} (decX : eq_dec X) (l : list X) (a b : X),
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
Qed.

Lemma in_app_or_dec:
  forall {X : Type} (decX : eq_dec X) (l l' : list X) (a : X),
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
Qed.

Lemma inclusion_app {X : Type} (xs1 xs2 xs : list X): 
  (xs1 ++ xs2) ⊆ xs ->
  xs1 ⊆ xs /\ xs2 ⊆ xs.
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

Lemma incl_nodup:
  forall {X : Type} {decX : eq_dec X} (xs : list X),
    (nodup decX xs) ⊆ xs.
Proof.
  intros ? decX ? ? EL; apply nodup_In in EL; assumption.
Qed.

Lemma equi_cons:
  forall {X : Type} (xs ys : list X) (a : X),
    equi xs ys -> equi (a::xs) (a::ys).
Proof.
  intros ? ? ? ? EQU; split; intros b EL; destruct EQU as [IN1 IN2].
  destruct EL as [EQ|EL]; [subst| ]; [left|right]; auto.
  destruct EL as [EQ|EL]; [subst| ]; [left|right]; auto.
Qed.

Lemma neq_cons:
  forall {X : Type} (x : X) (xs1 xs2 : list X),
    x::xs1 <> x::xs2 <-> xs1 <> xs2.
Proof.
  intros ? ? ? ?; split; intros NEQ1 NEQ2.
  { apply NEQ1; rewrite NEQ2; reflexivity. }
  { inversion NEQ2; subst.
    apply NEQ1; reflexivity.
  }
Qed.

Lemma nel_cons:
  forall {X : Type} (x a : X) (xs : list X),
    x nel a::xs -> x nel xs. 
Proof.
  intros ? ? ? ? NEL EL; apply NEL; right; auto.   
Qed.

Lemma nel_cons_neq:
  forall {X : Type} (x a : X) (xs : list X),
    x nel a::xs -> x <> a. 
Proof.
  intros ? ? ? ? NEL EL; subst; apply NEL; left; auto.   
Qed.

Lemma nodup_length_le:
  forall {X : Type} (decX : eq_dec X) (xs : list X),
    length (nodup decX xs) <= length xs.
Proof.
  intros; apply NoDup_incl_length.
  apply NoDup_nodup.
  apply incl_nodup.
Qed.

Lemma nodup_map_injective_function:
  forall {X : Type} (f : X -> X) (xs : list X),
    (forall a b, a el xs -> b el xs -> f a = f b -> a = b) -> 
    NoDup xs <-> NoDup (map f xs).
Proof.
  intros ? ? ? INJ; split; intros ND.
  - induction xs; auto.
    apply NoDup_cons_iff in ND; destruct ND  as [NEL ND].
    feed IHxs. intros x1 x2 EL1 EL2 EQ; apply INJ; auto; right; auto.
    simpl; apply NoDup_cons_iff; split; [ | auto].
    intros EL; apply in_map_iff in EL; destruct EL as [a' [EQ NEL2]].
    apply INJ in EQ; subst; auto; [right|left]; auto.
  - induction xs; auto.
    simpl in ND; apply NoDup_cons_iff in ND; destruct ND  as [NEL ND].
    feed IHxs. intros ? ? EL1 EL2 EQ; apply INJ; auto; right; auto.
    simpl; apply NoDup_cons_iff; split; [ | auto].
    intros EL; apply NEL; clear NEL.
    apply in_map_iff; exists a; split; auto.
Qed.

Corollary nodup_map_cons:
  forall {X : Type} (xss : list (list X)) (x : X),
    NoDup xss <->  NoDup (map (cons x) xss).
Proof.
  intros ? ? ?.
  apply nodup_map_injective_function; auto.
  clear; intros ? ? _ _ H; inversion H; reflexivity.
Qed.

Lemma nodup_app_of_map_cons:
  forall {X : Type} (xs1 xs2 : list (list X)) (a b : X),
    a <> b ->
    NoDup xs1 ->
    NoDup xs2 -> 
    NoDup (map (cons a) xs1 ++ map (cons b) xs2).
Proof.
  intros T ? ? ? ? NEQ ND1 ND2.
  induction xs1. simpl.
  { eapply nodup_map_cons in ND2; eauto. }
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
Qed.

Lemma nodup_filter:
  forall {X : Type} (p : X -> bool) (vs : list X),
    NoDup vs ->
    NoDup (filter p vs).
Proof.
  intros T p; induction vs; intros ND.
  - simpl; constructor. 
  - apply NoDup_cons_iff in ND.
    destruct ND as [NEL ND].
    simpl; destruct (p a); auto using IHvs.
    constructor.
    intros IN; apply NEL; clear NEL.
    apply filter_In in IN; destruct IN as [IN _]; assumption.
    apply IHvs; assumption.
Qed.

(** Flat-product *)

Definition flat_product {X : Type} (xs ys : list (list X)) : list(list X) :=
  flat_map (fun y => map (fun x => x ++ y) xs) ys.
Notation "xs ×× ys" := (flat_product xs ys) (at level 40).

(* [[x0;x1];[x2;x3]] ×× [[x4;x5];[x6;x7]]
         => [[x0;x1; x4;x5]; [x2;x3; x4;x5]; [x0;x1; x6;x7]; [x2;x3; x6;x7]]. *)

Lemma app_in_flat_product:
  forall {X : Type} (xss yss : list (list X)) (xs ys : list X),
    xs el xss ->
    ys el yss ->
    xs ++ ys el xss ×× yss.
Proof.
  intros ? ? ? ? ? EL1 EL2.
  induction xss.
  - destruct EL1.
  - destruct EL1 as [EQ|EL1]; subst.
    + clear IHxss; apply in_flat_map.
      exists ys; split; [ | left]; auto.
    + feed IHxss; auto.
      apply in_flat_map in IHxss; destruct IHxss as [ys' [EL MAP]].
      apply in_flat_map; exists ys'; split; [ | right]; auto. 
Qed.

Lemma flat_product_contains_only_apps:
  forall {X : Type} (xss yss : list (list X)) (zs : list X),
    zs el xss ×× yss ->
    exists xs ys, xs ++ ys = zs /\ xs el xss /\ ys el yss.
Proof.
  intros ? ? ? ? EL.
  induction xss.
  - apply in_flat_map in EL; destruct EL as [? [? H]]; destruct H.
  - apply in_flat_map in EL; destruct EL as [ys [EL MAP]].
    destruct MAP as [EQ|MAP].
    + subst zs; exists a, ys; repeat split; [left | ]; auto.
    + feed IHxss; [apply in_flat_map; exists ys; split; assumption| ]. 
      destruct IHxss as [xs' [ys' [EQ [EL1 EL2]]]].
      exists xs', ys'; repeat split; [ |right| ]; auto.
Qed.

(** Range *)

Fixpoint iota (l r : nat): list nat :=
  match r with
  | 0 => [0 + l]
  | S r => iota l r ++ [S r + l]
  end.

Definition range (l r : nat): list nat := iota l (r - l).

(** * Dupfree lists over equivalence relation *)
Section DupfreeLists. 

  Context {X : Type}.
  Hypothesis X_dec: eq_dec X.
  
  Variable R: X -> X -> Prop.
  Hypothesis R_dec: forall x y, dec (R x y).
  Hypothesis R_refl: forall x, R x x.
  Hypothesis R_sym: forall x y, R x y -> R y x.
  Hypothesis R_trans: forall x y z, R x y -> R y z -> R x z.
    
  Fixpoint mem_rel (x : X) (xs : list X): Prop :=
    match xs with
    | [] => False
    | h::tl => (R x h) \/ (mem_rel x tl)
    end.
  
  Lemma mem_cons:
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
  Qed.

  Lemma not_mem_cons:
    forall (a x : X) (xs : list X),
      ~ mem_rel a (x :: xs) -> ~ mem_rel a xs.
  Proof.
    intros a ax xs.
    assert (H: forall (A B: Prop), (A -> B) -> (~ B -> ~ A)).
    { clear; intros ? ? f nb a; auto. }
    apply H; apply mem_cons.
  Qed. 

  Lemma not_mem_all_not_R:
    forall (a : X) (xs : list X),
      ~ mem_rel a xs -> forall x, x el xs -> ~ R a x. 
  Proof.
    intros a xs NM x EL NR.
    induction xs.
    - destruct EL.
    - destruct EL as [EQ|EL]; subst.
      apply NM; left; assumption.
      apply not_mem_cons in NM; feed IHxs; auto.
  Qed. 

  Lemma mem_has_R:
    forall (a : X) (xs : list X),
      mem_rel a xs -> exists x, x el xs /\ R a x.
  Proof.
    intros a xs MEM; induction xs.
    - inversion MEM.
    - destruct MEM as [Ra|MEM].
      + exists a0; split; [left | ]; auto.
      + feed IHxs; auto. destruct IHxs as [x [EL Ra]].
        exists x; split; [right | ]; auto.
  Qed. 

  Lemma in_mem:
    forall (x : X) (xs : list X),
      x el xs -> mem_rel x xs.
  Proof.
    intros a xs NEL.
    induction xs.
    - auto.
    - destruct NEL as [EQ|NEL]; subst; [left|right]; auto.
  Qed.    

  (** Two equivalent formulation of dupfree list. *)
  
  Definition dupfree_rel (xs : list X) : Prop :=
    NoDup xs /\ (forall x1 x2, x1 el xs -> x2 el xs -> x1 <> x2 -> ~ R x1 x2).
  
  Fixpoint dupfree_rel_classic (xs : list X) : Prop :=
    match xs with
    | [] => True
    | h::tl => (~ mem_rel h tl) /\ (dupfree_rel_classic tl)
    end.
  
  Lemma dupfrees_are_equivalent:
    forall (xs : list X),
      dupfree_rel xs <-> dupfree_rel_classic xs.
  Proof.
    intros; split; intros DUP; induction xs.
    - constructor.
    - feed IHxs.
      { destruct DUP as [ND DUP].
        apply List.NoDup_cons_iff in ND; destruct ND as [NEL ND].
        split.
        + assumption.
        + intros ? ? EL1 EL2 NEQ.
          apply DUP; [right | right | ]; assumption.
      }
      split; [ | assumption].
      intros MEM.
      apply mem_has_R in MEM; destruct MEM as [x [EL RAX]].
      destruct DUP as [ND DUP].
      decide (a = x).
      { subst; apply List.NoDup_cons_iff in ND; destruct ND as [ND _]; auto. }
      { specialize (DUP a x).
        apply DUP in RAX; [ |left|right| ]; try auto 2.
      }
    - split; [constructor | intros ? ? EL; inversion EL]. 
    - destruct DUP as [NM DUP].
      feed IHxs; [assumption | ].
      destruct IHxs as [DUP1 DUP2].
      split.
      { constructor; auto.
        intros NEL; apply NM; auto using in_mem. }
      { intros ? ? EL1 EL2 NEQ NR.
        destruct EL1 as [EQ1|IN1], EL2 as [EQ2|IN2]; subst.
        + exfalso; auto.
        + apply not_mem_all_not_R with (x := x2) in NM; auto.
        + apply not_mem_all_not_R with (x := x1) in NM; auto.
        + apply DUP2 with (x1 := x1) (x2 := x2); eauto 2.
      } 
  Qed.

  (** (Anti)-Pigeonhole Principle *)
  Section AntiPigeonholePrinciple.

    Let injective_relation_on (R : X -> X -> Prop) (xs ys : list X) :=
      forall x1 x2 y,
        x1 el xs -> x2 el xs -> y el ys -> 
        R x1 y -> R x2 y ->
        x1 = x2.

    Let injective_function_on (f : X -> X) (xs : list X) :=
      forall x1 x2, x1 el xs -> x2 el xs -> f x1 = f x2 -> x1 = x2.
    

    Let codomain_in (f : X -> X) (xs ys : list X) :=
      forall x, x el xs -> f x el ys.


    Lemma list_forall_exists_R_dec:
      forall (x : X) (ys : list X),
        {forall y, y el ys -> ~ R x y} +
        {exists y, y el ys /\ R x y }.
    Proof.
      intros; induction ys.
      - left; intros ? EL; destruct EL.
      - destruct IHys as [IH|IH].
        + decide (R x a) as [Rxa|NRxa].
          * right; exists a; split; [left| ]; auto.
          * left; intros ? EL; destruct EL as [EQ|EL]; [subst | ]; auto.
        + right; destruct IH as [y [EL Rxy]].
          exists y; split; [right | ]; auto.
    Qed.
    
    Lemma list_exists_forall_notR_forall_exists_R_dec:
      forall (xs ys : list X),
        {exists x, x el xs /\ forall y, y el ys -> ~ R x y} +
        {forall x, x el xs -> exists y, y el ys /\ R x y}.
    Proof.
      intros; induction xs.
      - right; intros x EL; destruct EL.
      - destruct IHxs as [IH|IH].
        + destruct (list_forall_exists_R_dec a ys) as [D|D].
          * left; exists a; split; [left | ]; auto.
          * left; destruct IH as [x [EL IH]]; clear D.
            exists x; split; [right | ]; auto.
        + destruct (list_forall_exists_R_dec a ys) as [D|D].
          * left; exists a; split; [left | ]; auto.
          * right; intros x [EQ|EL]; subst; auto.
    Qed.

    Lemma R_is_injective_on_dupfree_rel:
      forall (xs ys : list X),
        dupfree_rel xs ->
        dupfree_rel ys ->
        injective_relation_on R xs ys.
    Proof.
      intros ? ? [_ DFxs] [_ DFys] ? ? ? ELx1 ELx2 ELy R1 R2.
      decide (x1 = x2) as [EQ|NEQ]; [assumption|exfalso].
      apply R_sym in R2.
      specialize (R_trans _ _ _ R1 R2).
      specialize (DFxs _ _ ELx1 ELx2 NEQ R_trans); auto.
    Qed.

    Lemma function_from_relation:
      forall xs ys,
        (forall x, x el xs -> exists y, y el ys /\ R x y) ->
        exists f : X -> X, forall x, x el xs -> f x el ys /\ R x (f x). 
    Proof.
      intros; induction xs.
      - exists (fun x => x); intros ? EL; destruct EL.
      - feed IHxs.
        { intros ? EL; apply H; right; assumption. }
        destruct IHxs as [f EQU].
        specialize (H a (or_introl eq_refl)); destruct H as [y [ELy Ra]].
        exists (fun x => if decision (x=a) then y else f x).
        intros x EL.
        destruct EL as [EQ|EL]; [subst x| ].
        + decide (a = a) as [EQ|F]; [auto| exfalso; auto].
        + decide (x = a) as [EQ|NEQ]; [subst a | apply EQU]; auto.
    Qed.

    Lemma injective_function_from_injective_relation:
      forall xs ys,
        injective_relation_on R xs ys -> 
        (forall x, x el xs -> exists y, y el ys /\ R x y) ->
        exists f : X -> X,
          injective_function_on f xs /\
          (forall x, x el xs -> f x el ys /\ R x (f x)).
    Proof.
      intros ? ? INJ TODO.
      apply function_from_relation in TODO.
      destruct TODO as [f EQU].
      exists f; split; auto.
      intros x1 x2 ELx1 ELx2 EQ.
      assert(EQUx1 := EQU _ ELx1).
      assert(EQUx2 := EQU _ ELx2).
      clear EQU; destruct EQUx1 as [ELf1 Rx1], EQUx2 as [ELf2 Rx2].
      specialize (INJ x1 x2 (f x1)); apply INJ; auto.
      rewrite EQ; auto.
    Qed.    
   
    Lemma injective_function_codomain_size:
      forall (f : X -> X) (xs ys : list X),
        NoDup xs ->
        injective_function_on f xs ->
        codomain_in f xs ys ->
        length xs <= length ys.
    Proof.
      intros ? ? ? ND INJ COD.
      assert(NDf := proj1 (nodup_map_injective_function f xs INJ) ND); clear ND.
      assert(EX: exists n, length xs <= n).
      { exists (length xs); auto. }
      destruct EX as [n LE].
      apply not_lt; intros LEN.
      generalize dependent LEN; generalize dependent NDf;
        generalize dependent COD; generalize dependent INJ;
          generalize dependent LE; generalize dependent ys; generalize dependent xs.
      induction n; intros.
      { apply le_n_0_eq, eq_sym, length_zero_iff_nil in LE.
        subst xs; simpl in LEN; apply Nat.nlt_0_r in LEN; auto. }
      { destruct xs as [ |x xs].
        { simpl in LEN; apply Nat.nlt_0_r in LEN; auto. } 
        { specialize (IHn xs (rem _ ys (f x))).
          feed_n 5 IHn. 
          { apply le_S_n; auto. } 
          { intros x1 x2 EL1 EL2 EQ; apply INJ; try right; auto. }
          { intros a EL.
            assert(NEQ: a <> x).
            { intros EQ; simpl in NDf.
              apply NoDup_cons_iff in NDf; destruct NDf as [NEL NDf].
              apply NEL; subst a.
              apply in_map_iff; exists x; split; auto.
            }             
            specialize (COD a (or_intror EL)).
            apply rem_neq; auto.
            intros EQ; specialize (INJ a x (or_intror EL) (or_introl eq_refl) EQ); auto.
          }
          { simpl in NDf; apply NoDup_cons_iff, proj2 in NDf; auto. }
          { simpl in LE; apply le_S_n in LE.
            apply Nat.lt_le_trans with (length ys).
            apply rem_length_lt; apply COD; left; reflexivity.
            apply lt_n_Sm_le in LEN; auto.
          }
          auto.
        } 
      }         
    Qed.
    
    Lemma antipigeonhole:
      forall (xs ys : list X),
        dupfree_rel xs ->
        dupfree_rel ys ->
        length xs > length ys ->
        exists x, x el xs /\ forall y, y el ys -> ~ R x y. 
    Proof.
      intros ? ? [ND1 DF1] [ND2 DF2] LT.
      destruct (list_exists_forall_notR_forall_exists_R_dec xs ys) as [A|A]; [auto | exfalso].
      assert(INJ := R_is_injective_on_dupfree_rel xs ys).
      feed_n 2 INJ; try (split; eauto).
      assert(INJf := injective_function_from_injective_relation _ _ INJ A).
      destruct INJf as [f [INJf Af]].
      assert(LE := injective_function_codomain_size f xs ys ND1 INJf (fun x EL => proj1 (Af x EL))).
      apply Nat.le_ngt in LE; auto.
    Qed.

  End AntiPigeonholePrinciple.

End DupfreeLists.

