(** * The direct translation: [+], [pow], [f]

    Every recursive call on an immediate subterm becomes the induction
    hypothesis, which mechanizes the terms written by hand for ℕ:
    - addition, by recursion on the first argument;
    - [pow], with the motive [λ_. Type₀ : ℕ → Type₁]: large elimination;
    - [f], with the motive [λn. Πb:ℕ. ℕ^n]: the result type changes with
      n, which Church's iterator could not do, and the argument b that
      changes in the recursive call sits in the motive under Π.

    Planned: the definitions through [compile_checked], and the traces of
    their conversions with the names of δ-constants and the steps that
    unfold them. *)

From DepTypes.PTS Require Import Syntax.
From IndTypes.Recursion Require Import Compile.
From IndTypes.Data Require Import Nat.
