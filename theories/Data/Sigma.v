(** * Dependent pairs

    Σ is native to the kernel: [Σx:A. B : Type_(max i j)], a pair checked
    against an expected Σ, the projections with their computation
    [Fst (Pair a b) ↝ a] and [Snd (Pair a b) ↝ b], and no η, as for Π.
    The type of the second projection depends on the first: the dependent
    [snd] that the Church encoding of lecture 6 lacked.  The
    product [A × B] is Σ over a constant family; products give [ℕ^n] and
    the history of [Below].

    Planned: the formation and its level, the dependent [snd], [A × B];
    [Σn:ℕ. Vec A n] once vectors exist (Data.Lists). *)

From DepTypes.PTS Require Import Syntax Check.
From DepTypes.Configs Require Import Predicative.
