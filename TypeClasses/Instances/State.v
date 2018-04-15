Require Import Logic.FunctionalExtensionality.
Require Import Functor Applicative Monad.

Module State.

  Import Functor Applicative Monad. 

  Section Definitions.

    Inductive state {S A: Type} :=
      | State: (S -> (A * S)) -> @state S A.  

    Instance state_functor {S}: (Functor (@state S)) :=
      { fmap A B f x := 
          State
            match x with
            | State st =>
              fun s1 => let (a, s2):= st s1 in (f a, s2)
            end
      }.
    Proof.
      { intros.
        extensionality x.
        destruct x as [p]. 
        unfold id; apply f_equal.
        extensionality s; destruct (p s).
        reflexivity. }
      { intros.
        extensionality x.
        compute.
        apply f_equal.
        destruct x as [p].
        extensionality s1.
        destruct (p s1).
        reflexivity.  }
    Defined.        
     
    Instance state_applicative {S}: (Applicative (@state S)) :=
      { pure _ x := State (fun state => (x, state))
        ; app A B sf sx :=
            State
              match sf, sx with
              | State f, State x =>
                fun st =>
                  let '(valx, st1) := x st in
                  let '(valf, st2) := f st1 in
                  (valf valx, st2)
              end
      }.
    Proof.
      { intros A x.
        destruct x as [x].
        apply f_equal.
        extensionality st.
        destruct (x st) as [x0 st2].
        reflexivity. }
      { intros A B f x.
        apply f_equal.
        extensionality st.
        reflexivity. }
      { intros A B u y.
        destruct u as [u].
        apply f_equal.
        extensionality st.
        destruct (u st).
        reflexivity. }
      { intros A B C u v w.
        destruct u as [u], v as [v], w as [w].
        apply f_equal.
        extensionality st.        
        destruct (w st) as [x1 s1], (v s1) as [x2 s2], u as [x3 s3]. 
        compute; reflexivity.
      }
    Defined. 

    Global Instance state_monad {S}: (Monad (@state S)) :=
      { unit _ := pure
        ; bind A B x f :=
            State
              match x with
              | State x =>
                fun state =>
                  let '(val, state) := x state in
                  let '(State g) := f val in
                  g state
              end
      }.
    Proof.
      { intros; compute.
        destruct (k a).
        apply f_equal.
        extensionality st.
        reflexivity. }
      { intros; compute.
        destruct m.
        apply f_equal.
        extensionality st.
        destruct (p st).
        reflexivity. }
      { intros A B C m f h; compute.
        apply f_equal.
        destruct m as [m].
        extensionality st.
        destruct (m st), (f a).
        reflexivity.
      }
    Defined.
    
  End Definitions.

  Section Examples.

    (* TODO: del *)
    Notation "A >>= F" := (bind A F) (at level 42, left associativity).
    
    Let state := @state (nat * nat * nat) nat.

    Let set_x n: state := State (fun '(x, y, z) => (0, (n, y, z))).
    Let set_y n: state := State (fun '(x, y, z) => (0, (x, n, z))).

    Let get_x: state := State (fun '(x, y, z) => (x, (x, y, z))).
    Let get_y: state := State (fun '(x, y, z) => (y, (x, y, z))).

    Let example: state :=
      set_x 7 >>= (fun _ =>
      set_y 2 >>= (fun _ => 
      get_x >>= (fun x =>
      get_y >>= (fun y =>              
      unit (x + y)
    )))).

    Let run (ex: state) :=
      match ex with
      | State st => fst (st (0,0,0))
      end.

    Eval compute in (run example).

  End Examples.

End State.