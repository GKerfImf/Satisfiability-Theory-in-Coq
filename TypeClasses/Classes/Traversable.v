Require Import Functor Applicative Foldable.
Require Import Identity Composition.

Module Traversable.

  Import Identity Composition Functor Applicative Foldable.
  
  Section Traversable.

    Class ApplicativeTransformation
          {T} `{! Applicative T}
          {F} `{! Applicative F}
          (t: forall {A}, T A -> F A) :=
      { _: forall {A} (x: A), t (pure x) = pure x
        ; _: forall {A B: Type} (x:_ ) (y: _), t (app x y) = @app F _ A B (t x) (t y)
      }.

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
    
  End Traversable.

End Traversable.