Require Import Logic.FunctionalExtensionality.
Require Import Functor Comonad.

Module Prod.

  Import Functor Comonad. 
    
  Section Prod.

    Global Instance prod_functor {A}: Functor (prod A) :=
      { fmap _ _ f x := (fst x, f (snd x)) }.
    Proof.
      { intros B; extensionality x.
        destruct x; reflexivity. }
      { intros X1 X2 X3 f g.
        extensionality x; compute.
        reflexivity. } 
    Defined.
    
    Global Instance prod_comonad {A}: Comonad (prod A) :=
      { coreturn := @snd A;
        cojoin _ wx := (fst wx, wx)
      }.
    Proof.
      { intros B; extensionality x; reflexivity. }
      { intros B. extensionality x.
        destruct x; compute; reflexivity. }
      { intros B.
        extensionality x. reflexivity. }
    Defined.

  End Prod.

End Prod.