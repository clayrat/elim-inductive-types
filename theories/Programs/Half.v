(** * Recursion two steps back: [half] and [isEven]

      half 0       = 0
      half 1       = 0
      half (n + 2) = succ (half n)

    In the branch [half (succ (succ n))] the history has the type
    [P (succ n) × (P n × Below P n)], and [half n] becomes [table.2.1].

    [isEven] is the same recursion returning a type: the motive
    [λ_. Type₀ : ℕ → Type₁], so j = ℓ = 1, the empty history is
    [Unit_1], [Below] goes through [elimNat[2]] and [build] through
    [elimNat[1]].  [isEven] itself returns the primitive [Unit] and
    [Void] of [Type₀], and [tt : isEven 4] is accepted by computation.
    Replacing [Unit_1] by the primitive [Unit : Type₀] in the empty
    history is rejected: there is no cumulativity.

    Planned: both definitions, their equations by conversion, the
    rejected replacement. *)

From DepTypes.PTS Require Import Syntax.
From IndTypes.Recursion Require Import Compile.
From IndTypes.Data Require Import Nat.
