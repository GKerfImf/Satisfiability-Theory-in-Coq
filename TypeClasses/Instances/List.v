Require Import Logic.FunctionalExtensionality.
Require Import List.
Require Import Functor.

Import ListNotations.

Module List.
  
  Import Functor. 
  
  Section List.

    Global Instance list_functor: (Functor list) :=
      { fmap A B f a := map f a }.
    Proof.
      { intros A; extensionality xs.
        induction xs.
        - reflexivity.
        - simpl; rewrite IHxs; compute; reflexivity.
      }
      { intros ? ? ? ? ?; apply functional_extensionality; intros xs.
        induction xs.
        - reflexivity.
        - simpl; rewrite IHxs; compute; reflexivity.
      }
    Defined.

  End List.
  
End List.