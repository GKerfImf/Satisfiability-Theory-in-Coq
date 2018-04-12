Module Monoid.

  Section Monoid.

    Class Monoid (M: Type) :=
      { mempty: M
        ; mappend: M -> M -> M
        ; mon_identity_r: forall x, mappend mempty x = x
        ; mon_identity_l: forall x, mappend x mempty = x
        ; mon_associativity:
            forall x y z, mappend (mappend x y) z = mappend x (mappend y z)
      }.
        
  End Monoid.

End Monoid.