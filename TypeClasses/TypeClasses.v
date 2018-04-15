Require Import Init.Datatypes Logic.FunctionalExtensionality.
Require Import Lists.List.
Require Import Functor Applicative Foldable Monoid Monad Comonad.
Require Import Identity Composition.
Require Import Coq.Arith.PeanoNat.

Set Implicit Arguments.


Module TypeClasses.

  Import ListNotations Functor Applicative Monoid Monad Comonad Foldable. 

  Section Definitions.

    
  End Definitions.

  Section Examples.


  End Examples.
  
  (* TODO: add compose *)

  (*  (* TOOD: comment *)
  Class Contravariant (F: Type -> Type) :=
    { cmap: forall {A B}, (A -> B) -> (F B -> F A)
      ; _: True
    }.

  (* Invariant Functor *)
  Class Invariant (F: Type -> Type) :=
    { imap: forall {A B}, (B -> A) -> (A -> B) -> (F A -> F B)
      ; _: True
    }.

  (* Profunctor *) (* Instance: (->) *)
  Class Profunctor (F: Type -> Type -> Type) :=
    { dimap: forall {A B C D}, (A -> B) -> (C -> D) -> (F B C) -> (F A D)
      ; _: True
    }.
   *)
  
(*  Section Transformers.

    Class MonadTrans (M: Type -> Type) (T: _) :=
      { monadM :> Monad M
        ; monadTM :> Monad (T M)
        ; lift: forall {A}, M A -> (T M) A
        ; _: (lift (.) unit) [=] unit
        ; _: True
      }.
    
  End Transformers. *)
  

End TypeClasses.