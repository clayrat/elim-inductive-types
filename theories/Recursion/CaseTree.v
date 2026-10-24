(** * Annotated recursive functions and their case trees

    The input of algorithm 2: a function with an explicitly chosen
    structural argument [x : D Δ θ̄], its other arguments marked constant
    or varying in recursive calls, and the tree of dependent case splits
    written out.  A split is allowed only on a variable whose type has
    distinct variables as indices, so that the eliminator applies to it
    directly: [append], [half] and [isEven] qualify; [head : Vec A (succ n)
    → A] and [zip] need unification of indices and are out of scope.
    Nested splits uncover strict subterms of any depth, as in
    [succ (succ n)].

    Each pattern variable records its path from the structural argument:
    the choice of a field's component, the application to the positions
    ȳ, and the step to the history of the subterm.

    Planned: the syntax of annotated functions and case trees, their
    well-formedness, paths. *)

From DepTypes.PTS Require Import Syntax.
From IndTypes.Elim Require Import Decl.
