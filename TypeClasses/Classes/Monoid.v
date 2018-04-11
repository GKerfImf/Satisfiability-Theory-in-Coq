Module Monoid.

  Section Monoid.

    Class Monoid (M: Type) :=
      { mempty: M
        ; mappend: M -> M -> M
        ; _: forall x, mappend mempty x = x
        ; _: forall x, mappend x mempty = x
        ; _: forall x y z, mappend (mappend x y) z = mappend x (mappend y z)
      }.
        
  End Monoid.

End Monoid.