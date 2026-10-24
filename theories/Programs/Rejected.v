(** * Definitions the compiler rejects

    - [g (succ n) = g (pred n)] terminates but is rejected: [pred n] is
      not a path to a subterm, and the check is syntactic.
    - Ackermann's function as equations in two arguments is rejected for
      either choice of the structural argument: [ack (m + 1) n] does not
      decrease the first, [ack m (…)] not the second.  Nested
      higher-order structural recursion on m, as in the lecture on
      System T, does express it.
    - A recursion that changes a parameter, such as A in a recursion on
      [List A], is non-uniform and is rejected.

    Planned: the rejections with their diagnostics. *)

From DepTypes.PTS Require Import Syntax.
From IndTypes.Recursion Require Import Compile.
From IndTypes.Data Require Import Nat Lists.
