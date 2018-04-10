Require Import Init.Datatypes
               Logic.FunctionalExtensionality.
Set Implicit Arguments.

Module Functor.

  (* ?? *)
  Definition id {A} (x: A) := x.

  (* ??? *)
  Reserved Notation "f (.) g" (at level 30, right associativity). (* TODO: associativity *)
  Definition compose {A B C} (f: B -> C) (g: A -> B) := fun x => f (g x).
  Infix "(.)" := compose .

  Section Definitions.
    
    (* TODO: Comment *)
    Class Functor (F: Type -> Type) :=
      { fmap: forall {A B}, (A -> B) -> (F A -> F B)
        ; fmap_id: forall {A}, @fmap A _ id = id
        ; fmap_comp: forall {A B C} (f: B -> C) (g: A -> B),
            fmap (f (.) g) = (fmap f (.) fmap g)
      }.

  End Definitions.

  Section Lemmas.
                                          
    Lemma functor_property:
      forall (F: Type -> Type) `{! Functor F} (G: Type -> Type) `{! Functor G}
             (A B C: Type) (f: B -> C) (g: A -> B) (x: F (G A)),
        fmap (fmap (f (.) g)) x = fmap (fmap f) (fmap (fmap g) x).
    Proof. 
      intros.
      destruct Functor0, Functor1.
      unfold fmap; rewrite fmap_comp1, fmap_comp0.
      reflexivity.
    Qed.

  End Lemmas.
  
End Functor.

