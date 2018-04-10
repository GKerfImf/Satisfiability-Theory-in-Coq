Require Import Init.Datatypes
               Logic.FunctionalExtensionality.
Require Import List.
Require Import Functor
               Applicative.
Require Import Identity.

Set Implicit Arguments.

Import ListNotations.

Module TypeClasses.

  Import Identity Functor Applicative. 

  Inductive composition {F: Type -> Type} {G: Type -> Type} {A: Type}: Type :=
    Comp: (F (G A)) -> @composition F G A.

  
  (*  Notation ...
  Definition compose f g = ... *)
  
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
    
  Section Monad.

    Reserved Notation "x >>= y" (at level 70).
 
    Class Monad (M: Type -> Type) :=
      { applicative :> Applicative M
        ; unit: forall {A}, A -> M A
        ; bind: forall {A B}, (M A) -> (A -> M B) -> M B where "n >>= m" := (bind n m)
        ; _: forall {A B: Type} (a: A) (k: A -> M B),
            (unit a) >>= k = k a
        ; _: forall {A} (m: M A), m >>= unit = m
        ; _: forall  {A B C} (m: M A) (k: A -> M B) (h: B -> M C),
            (m >>= (fun x => k x >>= h)) = ((m >>= k) >>= h)
      }.
    
  End Monad.

(*  Section Transformers.

    Class MonadTrans (M: Type -> Type) (T: _) :=
      { monadM :> Monad M
        ; monadTM :> Monad (T M)
        ; lift: forall {A}, M A -> (T M) A
        ; _: (lift (.) unit) [=] unit
        ; _: True
      }.

    Instance j : (MonadTrans 2) := n.
    
  End Transformers. *)

  Section Monoid.

    Class Monoid (M: Type) :=
      { mempty: M
        ; mappend: M -> M -> M
        ; _: forall x, mappend mempty x = x
        ; _: forall x, mappend x mempty = x
        ; _: forall x y z, mappend (mappend x y) z = mappend x (mappend y z)
      }.
        
  End Monoid.
  
  Section Foldable.

    Class Foldable (T: Type -> Type) :=
      { foldMap: forall {M} `{! Monoid M} a,  (a -> M) -> T a -> M }.
    
  End Foldable.
  
  Section Traversable.

    Hypothesis EE: forall {A B: Type} (f g: A -> B), (forall x, f x = g x) -> f = g.

    Class ApplicativeTransformation
          {T} `{! Applicative T}
          {F} `{! Applicative F}
          (t: forall {A}, T A -> F A) :=
      { _: forall {A} (x: A), t (pure x) = pure x
        ; _: forall {A B: Type} (x:_ ) (y: _), t (app x y) = @app F _ A B (t x) (t y)
      }.
 

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

    
    Instance composition_functor:
      forall F `{! Functor F} G `{! Functor G}, Functor (@composition F G) :=
      { fmap A B f x:=
          match x with
          | Comp x => Comp (fmap (fmap f) x)
          end
      }.
    Proof.
      { intros A; apply functional_extensionality; intros x.
        destruct x; unfold fmap.
        destruct Functor0, Functor1.
        assert(Id: (fmap0 (G A) (G A) (fmap1 A A id) f) = f).
        { assert(AddId: f = id f) by auto.
          rewrite AddId at 2; clear AddId.
          assert(Id: fmap1 A A id = id). 
          { apply EE; intros; rewrite fmap_id1; reflexivity. }
          rewrite Id; clear Id.
          rewrite fmap_id0; reflexivity.
        } rewrite Id; reflexivity.
      }
      { intros ? ? ? ? ?; apply functional_extensionality; intros x.
        destruct x; unfold compose.
        assert (Eq: (fun x : A => f (g x)) = (f (.) g)) by reflexivity.
        rewrite Eq; rewrite functor_property; reflexivity. 
      } 
    Defined.
    
    Instance composition_applicative:
      forall F `{! Applicative F} G `{! Applicative G}, Applicative (@composition F G) :=
      { pure A a := Comp (pure (pure a)) 
        ; app _ _ f x :=
            match f, x with
            | Comp f, Comp x => Comp (app (app (pure app) f) x)
            end
      }.
    Proof.
      { intros; destruct v.
        rewrite ap_homomorphism.
        assert(Eq: (app (pure id): G A -> G A) = id ).
        { extensionality x; intros; rewrite ap_identity; reflexivity. } 
        rewrite Eq, ap_identity.
        reflexivity.
      }
      { intros; repeat rewrite ap_homomorphism; reflexivity. } 
      { intros; destruct u.
        rewrite ap_homomorphism.
        assert(Eq: (app (pure (fun f => f y)): G (A -> B) -> G B)
                   = (fun u => app u (pure y))).
        { intros.
          change (app (pure (fun x: A -> B => x y)))
            with (fun u => (app (pure (fun x: A -> B => x y))) u).
          extensionality H.
          rewrite <- ap_interchange.
          reflexivity.
        } 
        rewrite Eq; clear Eq.
        rewrite ap_interchange.
        rewrite ap_composition.
        rewrite ap_homomorphism.
        rewrite ap_interchange.
        rewrite ap_homomorphism.
        assert (Eq: (compose (fun x : G A -> G B => x (pure y)) app)
                    = ((fun u0 : G (A -> B) => app u0 (pure y)))).
        { unfold compose.
          extensionality fx.
          reflexivity. }
        elim Eq.
        reflexivity. 
      } 
      { intros.
        destruct u as [u], v as [v], w as [w].
        repeat (rewrite ap_homomorphism || rewrite ap_composition).
        rewrite ap_interchange.
        rewrite ap_composition.
        rewrite ap_homomorphism.
        unfold compose. 
        fold (@compose A B C).
        replace (fun (x : G (B -> C)) (x0 : G (A -> B))
                 => app (app (app (pure compose) x) x0))
          with (fun (x : G (B -> C)) (x0 : G (A -> B)) x1 => app x (app x0 x1)).
        rewrite ap_homomorphism.
        split.
        extensionality H. extensionality I. extensionality J.
        rewrite <- ap_composition.        
        reflexivity.
      }
    Defined.

    Class Traversable (T: Type -> Type) :=
      { functorTraversable :> Functor T 
        ; foldableTraversable :> Foldable T
        ; traverse: forall {A} {B} {F} `{! Applicative F},
            (A -> F B) -> T A -> F (T B)
        ; tr_naturality: forall (A B: Type) (F: Type -> Type) `{Applicative F} 
                             (f: A -> F B) (t: forall {A}, F A -> F A)
                             `{! ApplicativeTransformation (@t)},
            ((t (.) (traverse f))) = ((traverse (t (.) f))) 

        ; _: forall {A: Type}, (@traverse A _ _ _ (Ident)) = Ident

        (* Check this law *) 
        ; _: forall {A B C: Type} (f: A -> identity) (g: B -> identity) (x: T A),
            

            @traverse A _ _ _ ((@Comp _ _ B) (.) (@fmap _ _ _ _ g) (.) f) x
                      
            = 
            
            ((@Comp _ _ _ ) (.) fmap (@traverse _ _ _ _ g) (.) (@traverse _ _ _ _ f)) x
                      
      }.


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

    Instance list_functor: (Functor list) :=
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

    Instance option_foldable: (Foldable option) :=
      { foldMap := _ }.
    Proof. 
      intros.
      destruct Monoid0, X0.
      apply X; assumption.
      apply mempty0.
    Defined.
    
    Instance option_traversable: (Traversable option) :=
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
       
  End Traversable.
  
  Section Option.
    
    Instance option_monad: (Monad option) :=
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
  
End TypeClasses.