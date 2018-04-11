Require Import Functor.

Module Comonad.

  Import Functor.
    
  Section Comonad.

    Reserved Notation "x =>> y" (at level 70).
 
    Class Comonad (W: Type -> Type) :=
      { functorComonad :> Functor W
        ; coreturn: forall {A}, W A -> A
        ; cojoin: forall {A}, W A -> W (W A)
        ; extend {A B} (x: W A) (f: W A -> B) :=
            fmap f (cojoin x) where "x =>> f" := (extend x f)
        ; _: forall {A}, coreturn (.) cojoin = @id (W A)
        ; _: forall {A}, fmap coreturn (.) cojoin = @id (W A)
        ; _: forall {A}, (@cojoin (W A)) (.) cojoin = fmap cojoin (.) cojoin
      }.
    
  End Comonad.

End Comonad.