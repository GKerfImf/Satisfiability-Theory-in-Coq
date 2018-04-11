Require Import Applicative.

Module Monad.

  Import Applicative. 
    
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

End Monad.