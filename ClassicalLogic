(* For those who like a challenge, here is an exercise taken from 
the Coq'Art book (p. 123). The following five statements are often 
considered as characterizations of classical logic (as opposed to 
constructive logic, which is what is "built in" to Coq). We can't 
prove them in Coq, but we can consistently add any one of them as 
an unproven axiom if we wish to work in classical logic. Prove that 
these five propositions are equivalent. *)


Definition peirce := ∀P Q: Prop,
  ((P → Q) → P) → P.
Definition classic := ∀P:Prop,
  ~~P → P.
Definition excluded_middle := ∀P:Prop,
  P ∨ ¬P.
Definition de_morgan_not_and_not := ∀P Q:Prop,
  ~(~P ∧ ¬Q) → P ∨ Q .
Definition implies_to_or := ∀P Q:Prop,
  (P → Q) → (¬P ∨ Q).
  
  
Theorem implies_to_or__excluded_middle : implies_to_or -> excluded_middle.
Proof. 
  intros. unfold excluded_middle. intros. unfold implies_to_or in H.
  destruct (H P P) as [HnP | HP].
  intros. apply H0. 
  right. apply HnP.
  left. apply HP. Qed.

Theorem peirce__classic : peirce -> classic.
Proof.
  unfold classic. unfold peirce. intros.
  unfold not in H0. apply (H P False). intros. apply H0 in H1. inversion H1. Qed.

Theorem classic__de_morgan_not_and_not : classic -> de_morgan_not_and_not.
  unfold classic. unfold de_morgan_not_and_not. unfold not. intros.
  apply H. intros.
  apply H1.
  left.
    apply H. intros. apply H0. split. apply H2. intros.  apply H1.
  right. apply H3. Qed.

Theorem de_morgan_not_and_not__implies_to_or : de_morgan_not_and_not -> implies_to_or.
Proof.
  unfold de_morgan_not_and_not. unfold implies_to_or. unfold not. intros.
  destruct (H (P->False) Q).
  intros.
  inversion H1.
  apply H2. intros.  apply H3. apply H0. apply H4.
  left. apply H1.
  right. apply H1. Qed.

Theorem excluded_middle__pierce : excluded_middle -> peirce.
Proof. 
  unfold excluded_middle. unfold peirce. unfold not. intros.
  destruct (H P).
  apply H1. 
  apply H0.
  intros.
  apply H1 in H2. inversion H2. Qed.
