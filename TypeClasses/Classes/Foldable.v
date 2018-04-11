Require Import Monoid.

Set Implicit Arguments.

Module Foldable.

  Import Monoid.
    
  Section Foldable.

    Class Foldable (T: Type -> Type) :=
      { foldMap: forall {M} `{! Monoid M} a,  (a -> M) -> T a -> M }.
    
  End Foldable.

End Foldable.