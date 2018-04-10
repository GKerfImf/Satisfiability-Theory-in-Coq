Require Import Functor.

Module Applicative.
 
  Import Functor. 

  Section Applicative.
    
    Reserved Notation "x <*> y" (at level 50, left associativity). 
    
    Class Applicative (F: Type -> Type) :=
      { functor :> Functor F
        ; pure: forall {A}, A -> F A
        ; app: forall {A B: Type}, F (A -> B) -> F A -> F B where "n <*> m" := (app n m)
        ; ap_identity: forall {A} (v: F A), pure id <*> v = v
        ; ap_homomorphism: forall {A B} (f: A -> B) (x: A), pure f <*> pure x = pure (f x)
        ; ap_interchange: forall {A B} (u: F(A -> B)) (y: A),
            (u <*> pure y) = (pure (fun f => f y) <*> u)
        ; ap_composition: forall {A B C} (u: F (B -> C)) (v: F (A -> B)) w,
            u <*> (v <*> w) = pure compose <*> u <*> v <*> w
      }.
    
  End Applicative.

End Applicative.