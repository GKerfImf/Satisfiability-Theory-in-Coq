Require Import Coq.Init.Datatypes.
Set Implicit Arguments.

Module Functor.

  (* ?? *)
  Definition id {A} (x: A) := x.

  (* ??? *)
  Reserved Notation "f (.) g" (at level 70, right associativity). (* TODO: associativity *)
  Definition compose {A B C} (f: B -> C) (g: A -> B) := fun x => f (g x).
  Infix "(.)" := compose .

  (* ??? *)
  Reserved Notation "f [=] g" (at level 70, no associativity).
  Definition extensional_equality {A B} (f g: A -> B) := forall x, f x = g x.
  Infix "[=]" := extensional_equality. 

  Section Definitions.
    
    (* TODO: Comment *)
    Class Functor (F: Type -> Type) :=
      { fmap: forall {A B}, (A -> B) -> (F A -> F B)
        ; fmap_id: forall {A}, @fmap A _ id [=] id
        ; fmap_comp: forall {A B C} (f: B -> C) (g: A -> B),
            fmap (f (.) g) [=] ((fmap f) (.) (fmap g))
      }.

  End Definitions.

  Section Lemmas.
    
    Axiom EE: forall A B (f g: A -> B),
      (forall x, f x = g x) -> f = g.
                                          
    Lemma functor_property:
      forall (F: Type -> Type) `{! Functor F} (G: Type -> Type) `{! Functor G}
             (A B C: Type) (f: B -> C) (g: A -> B) (x: F (G A)),
        fmap (fmap (f (.) g)) x = fmap (fmap f) (fmap (fmap g) x).
    Proof. 
      intros.
      assert (Eq: fmap (f (.) g) = (fmap f (.) fmap g)).
      { clear x.
        destruct Functor1; unfold fmap.
        apply EE; intros x; apply fmap_comp0.
      } rewrite Eq; clear Eq.
      destruct Functor0; unfold fmap at 1.
      assert (Eq := fmap_comp0 _ _ _ (fmap f) (fmap g) x).
      rewrite Eq; clear Eq.
      reflexivity.
    Qed.

  End Lemmas.
  
End Functor.

