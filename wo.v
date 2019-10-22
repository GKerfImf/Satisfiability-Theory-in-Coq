Require Import Nat.

(** * Witness Operator *)
Section WO.

  Inductive G (f : nat -> bool) (n : nat) : Prop :=
  | g__intro : (f n = false -> G f (S n)) -> G f n.

  Lemma l1:
    forall (f : nat -> bool) (n : nat),
      f n = true -> G f n.
  Proof.
    intros ? ? EQ.
    constructor.
    intros C.
    rewrite EQ in C; discriminate.
  Defined.

  Lemma l2:
    forall (f : nat -> bool) (n : nat),
      G f n -> G f 0.
  Proof.
    induction n.
    - auto.
    - intros.
      apply IHn.
      constructor; auto.
  Defined.

  Lemma l3:
    forall (f : nat -> bool),
      (exists n, f n = true) -> G f 0.
  Proof.
    intros ? [n EQ].
    apply l1 in EQ.
    eapply l2; eauto.
  Defined.
  
  Lemma l4:
    forall (f : nat -> bool) (n : nat),
      G f n -> {n | f n = true}.
  Proof.
    intros f .
    induction 1 as [n _ IH].
    destruct (f n) eqn:EQ.
    - exists n; assumption.
    - apply IH; reflexivity.
  Defined.
  
  Definition wo : forall (f : nat -> bool), (exists n, f n = true) -> {n | f n = true} :=
    fun f TSAT => l4 f 0 (l3 f TSAT).

  Section Tests.
    
    Definition large (n : nat) : bool := 11 <=? n.

    Definition large__ex : exists n, large n = true.
    Proof.
      exists 123; reflexivity.
    Defined.

    Compute (proj1_sig (wo large large__ex)).


    Definition divided (n : nat) : bool :=
      andb (1 <=? n)
           (n mod 1 + n mod 2 + n mod 3 + n mod 4 + n mod 5 + n mod 6 + n mod 7 =? 0).

    Definition divided__ex : exists n, divided n = true.
    Proof.
      exists (1 * 2 * 3 * 4 * 5 * 6 * 7 (* = 5040 *)); reflexivity.
    Defined.     
    
    Compute (proj1_sig (wo divided divided__ex)).

  End Tests.
  
End WO.

(** * μ-Operator *)
Section Mu.

  Fixpoint μ (f : nat -> bool) (n : nat) : nat :=
    match n with
    | 0 => 0
    | S n => let k := μ f n in if f k then k else S n
    end.

  Definition sqrt (x : nat) : nat :=
    μ (fun y => x <=? y * y) x.

  Compute (sqrt 145).
  
End Mu.


