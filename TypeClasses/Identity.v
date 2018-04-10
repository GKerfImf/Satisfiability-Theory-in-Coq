Require Import Init.Datatypes
        Logic.FunctionalExtensionality.
Set Implicit Arguments. 

Require Import List.
Require Import Functor
        Applicative. 
Import ListNotations.

Module Identity.
  
  Import Functor Applicative. 
  
  Inductive identity {A: Type}: Type :=
    Ident: A -> @identity A.


  Instance identity_functor: (Functor (@identity)) :=
    { fmap A B f a := 
        match a with
        | Ident a => Ident (f a)
        end
    }.
  Proof.
    { intros A; apply functional_extensionality; intros x.
      destruct x; reflexivity. }
    { intros ? ? ? ? ?; apply functional_extensionality; intros x.
      destruct x; reflexivity. }
  Defined.

  Instance identity_applicative: (Applicative (@identity)) :=
    { pure A a := Ident a
      ; app A B f a :=
          match f, a with
          | Ident f, Ident a => Ident (f a)
          end
    }.
  Proof.
    { intros; destruct v; reflexivity. } 
    { intros; reflexivity. }
    { intros; destruct u; reflexivity.  }
    { intros; destruct u, v, w; reflexivity. }
  Defined.
  
End Identity.