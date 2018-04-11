Require Import Logic.FunctionalExtensionality.
Require Import Functor Applicative Foldable Monoid Monad Traversable.
Require Import Identity Composition.

Module Option.
  
  Import Identity Composition Monoid Foldable Functor Applicative Monad Traversable. 
  
  Section Option.

    Instance option_functor: (Functor option) :=
      { fmap A B f a :=
          match a with
          | None => None
          | Some a => Some (f a)
          end
      }.
    Proof.
      intros. apply functional_extensionality. intros x. destruct x; reflexivity.
      intros. apply functional_extensionality. intros x. 
      compute. destruct x; reflexivity.
    Defined.
    
    Global Instance option_applicative: (Applicative option) :=
      { pure {A} (x: A) := Some x
        ; app {A B} f x :=
            match f, x with
            | Some f, Some x => Some (f x)
            | _, _ => None
            end
      }.
    Proof.
      - intros; destruct v; reflexivity.
      - intros; reflexivity. 
      - intros; destruct u; reflexivity.
      - intros; destruct u, v, w; reflexivity.
    Defined.

    Global Instance option_foldable: (Foldable option) :=
      { foldMap := _ }.
    Proof. 
      intros.
      destruct Monoid0, X0.
      apply X; assumption.
      apply mempty0.
    Defined.
    
    Global Instance option_traversable: (Traversable option) :=
      { traverse {A B} {F} _ (f: A -> F B) (some: option A) := 
          match some with
          | None => pure None : F (option B)
          | Some x => app (pure (Some ) ) (f x) : F (option B)
          end
      }.
    Proof.
      { intros ? ? ? ? ? ? ?; apply functional_extensionality; intros x.
        destruct x; unfold compose.
        - destruct ApplicativeTransformation0.
          rewrite H1, H0; reflexivity. 
        - destruct ApplicativeTransformation0; eauto.
      }
      { intros ?; apply functional_extensionality; intros x.
        destruct x; reflexivity. } 
      { intros ? ? ? ? ? x. 
        destruct x; unfold compose.
        - compute; destruct (f a), (g b); reflexivity.
        - compute; reflexivity.
      } 
    Defined.  

    Global Instance option_monad: (Monad option) :=
      { unit A a := Some a;
        bind A B a f :=
          match a with
          | Some a => f a
          | _ => None
          end
      }.
    Proof.
      all: intros.
      - reflexivity.
      - destruct m; reflexivity.
      - destruct m; try destruct (k a); reflexivity.
    Defined.
    
  End Option.
  
End Option.