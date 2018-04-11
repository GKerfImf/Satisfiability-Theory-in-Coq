Require Import Init.Datatypes
        Logic.FunctionalExtensionality.
Require Import List.
Require Import Functor
        Applicative.
Require Import Identity.

Set Implicit Arguments.

Import ListNotations.

Module Composition.
  
  Import Functor Applicative. 

  Section Composition.
    
    Inductive composition {F: Type -> Type} {G: Type -> Type} {A: Type}: Type :=
      Comp: (F (G A)) -> @composition F G A.

    Global Instance composition_functor:
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
          { extensionality x; intros; rewrite fmap_id1; reflexivity. }
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
    
    Global Instance composition_applicative:
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

  End Composition.
  
End Composition.