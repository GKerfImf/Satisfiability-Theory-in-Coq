# Model counting in Coq

## What is this?

This repository contains my solution to an optional project from the course on [Introduction to Computational Logic](https://courses.ps.uni-saarland.de/icl_19/). The goal was to implement a model counting algorithm in Coq and verify its correctness.

#### Description of the project:

A model for a formula $s$ is a mapping $\alpha$ from the variables in $s$ to the Boolean truth values, such that $\mathcal{E} \ a \ s = \top$. For example, $(x \mapsto \bot, y \mapsto \top)$ is a model for the formula $x \implies y$. Model counting is the problem of determining how many models exist for a given formula. To return to our previous example, $x \implies y$ has three models: $(x \mapsto \bot, y \mapsto \bot)$, $(x \mapsto \top, y \mapsto \top)$, and $(x \mapsto \bot, y \mapsto \top)$. This project will see you implementing and verifying a model counting algorithm.

#### How to run?

To generate the HTML documentation, run the following commands (tested with The Coq Proof Assistant, version 8.13.2):
```bash
  ./create_makefile.sh
  make gallinahtml
```

## Some highlights

#### Brute-force algorithm ([link](https://github.com/GKerfImf/Satisfiability-Theory-in-Coq/blob/5ee7c0eab9f17328c367188417cca070aa353620/project3.v#L175-L178))

```coq

  (* Generate all the possible assignments on a given set of variables. *)
  Fixpoint all_assignments_on (vs : variables) : assignments :=
    match vs with
    | [] => [[]] | v::vs =>
                  map (cons (v,false)) (all_assignments_on vs) ++
                      map (cons (v,true)) (all_assignments_on vs)
    end.

  <...>

  (* Given a function ϕ, the algorithm
     1) Generates the list of all assignments on ϕ's variables
     2) Keeps assignment such that ℇ ϕ α ≡ true.
     3) Counts the number of assignments in the list. *)
  Definition algorithm1 (ϕ : formula) : { n : nat | #sat ϕ ≃ n }.
  Proof. ... Defined.

  Section Tests.

    (* We define some variables and formulas for testing. *)
    Let x1 := [|V 1|].
    Let x2 := [|V 2|].
    Let x3 := [|V 3|].
    Let x4 := [|V 4|].
    Let x5 := [|V 5|].

    (* Compute (proj1_sig (algorithm1 x1)).                         => 1 : nat *)
    (* Compute (proj1_sig (algorithm1 (x1 ∨ x2 ∨ x3 ∨ x4 ∨ x5))).   => 31 : nat *)
    (* Compute (proj1_sig (algorithm1 (x1 ⊕ x2 ⊕ x3 ⊕ x4 ⊕ x5))).   => 16 : nat *)

    (* or_n n = x1 ∨ x2 ∨ ... ∨ xn *)
    Let or_n n := fold_left (fun ϕ x => ϕ ∨ [|V x|]) (range 1 n) F.

    (* Compute (proj1_sig (algorithm1 (or_n 8))).                   => 255 : nat *)

  End Tests.
```


#### "Divide-and-conquer" algorithm ([link](https://github.com/GKerfImf/Satisfiability-Theory-in-Coq/blob/master/project3.v#L639))

```coq

  (* The main idea of the algorithm is the following:
       #sat F = 0
       #sat T = 1
       #sat ϕ = #sat (x ∧ ϕ[x ↦ T] ∨ ¬x ∧ ϕ[x ↦ F])
              = #sat (x ∧ ϕ[x ↦ T]) + #sat (¬x ∧ ϕ[x ↦ F])
              = #sat (ϕ[x ↦ T]) + #sat (ϕ[x ↦ F]). *)
  Definition algorithm2 (ϕ : formula) : { n : nat | #sat ϕ ≃ n }.
  Proof. ... Defined.

  Section Tests.

    (* or_n n = x1 ∨ x2 ∨ ... ∨ xn *)
    Let or_n n := fold_left (fun ϕ x => ϕ ∨ [|V x|]) (range 1 n) F.

    (* xor_n n = x1 ⊕ x2 ⊕ ... ⊕ xn *)
    Let xor_n n := fold_left (fun ϕ x => ϕ ⊕ [|V x|]) (range 1 n) F.

    (* Compute (proj1_sig (algorithm1 (or_n 5))).   => 31 : nat *)
    (* Compute (proj1_sig (algorithm1 (or_n 8))).   => 255 : nat *)
    (* Compute (proj1_sig (algorithm1 (or_n 10))).  => 1023 : nat *)
    (* Compute (proj1_sig (algorithm1 (or_n 15))).  => 32767 : nat *)
    (* Compute (proj1_sig (algorithm1 (or_n 16))).  => Stack overflow. *)

    (* Compute (proj1_sig (algorithm1 (xor_n 5))).  => 16 : nat *)
    (* Compute (proj1_sig (algorithm1 (xor_n 8))).  => 128 : nat *)

  End Tests.
```


#### Counting $k$-cliques in a graph ([link](https://github.com/GKerfImf/Satisfiability-Theory-in-Coq/blob/master/project3.v#L1396-L1409))


```coq
  (* I'll use the problem of counting the k-cliques as a "generator" of
     nontrivial boolean formulas. *)

  (* A graph is a record with a list of vertices and a function
     that returns true if there is an edge between two vertices. *)
  Record graph :=
    { vtcs : list nat;
      edges : nat -> nat -> bool;
    }.

  <...>

  (* A graph with 4 vertices and 6 edges. *)
  Definition graph_4_clique :=
    {| vtcs := [1;2;3;4];
       edges v1 v2 :=
         match v1, v2 with
         | 1,2 | 2,1 => true
         | 1,3 | 3,1 => true
         | 1,4 | 4,1 => true
         | 2,3 | 3,2 => true
         | 2,4 | 4,2 => true
         | 3,4 | 4,3 => true
         | _, _ => false
         end;
    |}.

  <...>

  (* Given a natural number [k] and a graph [g], generate a formula
     that is true if and only if [g] contains a [k]-clique . *)
  Definition transform (k : nat) (g : graph) : formula := <...>

  (* Take ~10 sec. *)
  (* Compute (counting_k_cliques 1 graph_4_clique). => 4 : nat *)
  (* Compute (counting_k_cliques 2 graph_4_clique). => 6 : nat *)
  (* Compute (counting_k_cliques 3 graph_4_clique). => 4 : nat *)
  (* Takes ~240 sec. *)
  (* Compute (counting_k_cliques 4 graph_4_clique). => 1 : nat *)
```