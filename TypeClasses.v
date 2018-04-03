Require Import Coq.Init.Datatypes.
Set Implicit Arguments.

Module TypeClasses.

  Definition id {A} (x: A) := x.

  Reserved Notation "f (.) g" (at level 70, right associativity). (* TODO: associativity *)
  Definition compose {A B C} (f: B -> C) (g: A -> B) := fun x => f (g x).
  Infix "(.)" := compose .

  Reserved Notation "f [=] g" (at level 70, no associativity).
  Definition extensional_equivalence {A B} (f g: A -> B) := forall x, f x = g x.
  Infix "[=]" := extensional_equivalence.
  
(*  Notation ...
  Definition compose f g = ... *)
  
  (* TODO: add compose *)
  
  (* TODO: Comment *)
  Class Functor (F: Type -> Type) :=
    { fmap: forall {A B}, (A -> B) -> (F A -> F B)
      ; fmap_id: forall {A}, @fmap A _ id [=] id
      ; fmap_comp: forall {A B C} (f: B -> C) (g: A -> B),
          fmap (f(.) g) [=] ((fmap f) (.) (fmap g))
    }.

(*  (* TOOD: comment *)
  Class Contravariant (F: Type -> Type) :=
    { cmap: forall {A B}, (A -> B) -> (F B -> F A)
      ; _: True
    }.

  (* Invariant Functor *)
  Class Invariant (F: Type -> Type) :=
    { imap: forall {A B}, (B -> A) -> (A -> B) -> (F A -> F B)
      ; _: True
    }.

  (* Profunctor *) (* Instance: (->) *)
  Class Profunctor (F: Type -> Type -> Type) :=
    { dimap: forall {A B C D}, (A -> B) -> (C -> D) -> (F B C) -> (F A D)
      ; _: True
    }.
*)
  

  Section Applicative.
    
    Reserved Notation "x <*> y" (at level 50, left associativity). 
    
    Class Applicative (F: Type -> Type) :=
      { functor :> Functor F
        ; pure: forall {A}, A -> F A
        ; app: forall {A B}, F (A -> B) -> F A -> F B where "n <*> m" := (app n m)
        ; _: forall {A} (v: F A), pure id <*> v = v
        ; _: forall {A B} (f: A -> B) (x: A), pure f <*> pure x = pure (f x)
        ; _: forall {A B} (u: F(A -> B)) (y: A),
            (u <*> pure y) = (pure (fun f => f y) <*> u)
        ; _: forall {A B C} (u: F (B -> C)) (v: F (A -> B)) w,
            u <*> (v <*> w) = pure compose <*> u <*> v <*> w
      }.
    
  End Applicative.
  
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

  Section Transformers.

    Class MonadTrans (M: Type -> Type) (T: _) :=
      { monadM :> Monad M
        ; monadTM :> Monad (T M)
        ; lift: forall {A}, M A -> (T M) A
        ; _: (lift (.) unit) [=] unit
        ; _: True
      }.

    Instance j : (MonadTrans 2) := n.
  End Transformers.
  
  Section Option.
  
  Instance option_functor: (Functor option) :=
    { fmap A B f a :=
        match a with
        | None => None
        | Some a => Some (f a)
        end
    }.
  Proof.
    intros. intros x. destruct x; reflexivity.
    intros. intros x. 
    compute. destruct x; reflexivity.
    
  Defined.
 
  Instance option_applicative: (Applicative option) :=
    { pure {A} (x: A) := Some x
      ; app {A B} f x :=
          match f, x with
          | Some f, Some x => Some (f x)
          | _, _ => None
          end
    }.
  Proof.
    - intros; destruct v; reflexivity.
    - intros; reflexivity. 
    - intros; destruct u; reflexivity.
    - intros; destruct u, v, w; reflexivity.
  Qed.

  Instance option_monad: (Monad option) :=
    { unit A a := Some a;
      bind A B a f :=
        match a with
        | Some a => f a
        | _ => None
        end
    }.
  Proof.
    all: intros.
    - reflexivity.
    - destruct m; reflexivity.
    - destruct m; try destruct (k a); reflexivity.
  Defined.


  End Option.

  Goal
    forall m,
      Monad m ->
      Applicative m
  .
  Proof.
    intros. 
    destruct Monad.

    
End TypeClasses.