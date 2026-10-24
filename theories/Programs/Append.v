(** * [append] and dependent splits of vectors

    [append : Vec A n → Vec A m → Vec A (n + m)] by recursion on the first
    vector, with the motive [λn xs. Vec A (n + m)] and [m], [ys]
    constant.  The history at level ℓ = max i j:

      Below P 0        nil          = Unit_ℓ
      Below P (succ n) (cons x xs)  = P n xs × Below P n xs

    The recursion is one step back: the access [table.1] is the
    hypothesis of the direct translation, and the history only shows how
    the indices enter its type.  The branch [nil] expects [Vec A (0 + m)]
    and [cons] [Vec A (succ n + m)]; with addition by recursion on its
    first argument both reduce to [Vec A m] and [Vec A (succ (n + m))].
    With addition on the second argument [0 + m] stays neutral, and the
    branch [nil] is rejected on [Vec A m ≡ Vec A (0 + m)]: the equality of
    indices is propositional there, not definitional.

    Also: a split of a vector under a hypothesis that depends on its
    length but not on the vector itself, which checks the generalization
    of the index and of the dependent tail of the context.

    Planned: [append] through [compile_checked], the rejected branch, the
    generalization. *)

From DepTypes.PTS Require Import Syntax.
From IndTypes.Recursion Require Import Compile.
From IndTypes.Data Require Import Nat Lists.
