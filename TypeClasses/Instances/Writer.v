Require Import Init.Datatypes Logic.FunctionalExtensionality.
Require Import Functor Applicative Monoid Monad.

Set Implicit Arguments.

Module Writer.

  Import Functor Applicative Monoid Monad. 

  Section Definitions.

    Inductive writer {W A: Type} :=
      Write: (A * W) -> @writer W A.

    Instance writer_functor {W}: (Functor (@writer W)) :=
      { fmap _ _ f x :=
          match x with
          | Write (a, w) => Write (f a, w)
          end
      }.
    Proof.
      { intros; extensionality x.
        destruct x as [[a w]]; reflexivity. }
      { intros; extensionality x.
        destruct x as [[a w]]. reflexivity. }
    Defined.

    Instance writer_applicative {W} `{! Monoid W}: (Applicative (@writer W)) :=
      { pure _ x := Write (x, mempty)
        ; app _ _ f x :=
            match f, x with
            | Write (f, fm), Write (x, xm) => Write (f x, mappend fm xm)
            end 
      }.
    Proof.
      { intros; destruct v as [[a w]].
        rewrite mon_identity_r; reflexivity. }
      { intros; rewrite mon_identity_r; reflexivity. }
      { intros; destruct u as [[a w]].
        rewrite mon_identity_r, mon_identity_l; reflexivity. }
      { intros; destruct u as [[a1 w1]], v as [[a2 w2]], w as [[a3 w3]]. 
        rewrite mon_identity_r, mon_associativity; reflexivity. } 
    Defined. 

    Instance writer_monad {W} `{! Monoid W}: (Monad (@writer W)) :=
      { unit _ := pure
        ; bind _ _ x f :=
            let '(Write (a, w)) := x in
            let '(Write (fa, fam)) := f a in
            Write (fa, mappend w fam)
      }.
    Proof.
      { intros; simpl.
        destruct (k a) as [[b w]].
        rewrite mon_identity_r; reflexivity. }
      { intros; destruct m as [[a w]].
        simpl; rewrite mon_identity_l; reflexivity. }
      { intros.
        destruct m as [[a w1]], (k a) as [[b w2]], (h b) as [[c w3]].
        rewrite mon_associativity; reflexivity. }
    Defined.

  End Definitions.

End Writer.