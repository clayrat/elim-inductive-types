(** * The layout of the binders of a method

    A method of [elim_D[j]] binds the fields of its constructor in order,
    each recursive field followed right away by its hypothesis.  Both
    algorithms build on this layout: algorithm 1 the method types
    (Elim.Generate), algorithm 2 the methods of the history
    (Recursion.Below) and the binders of the branches of case trees
    (Recursion.CaseTree).  [fold_slots] goes over the binders once, with
    an accumulator in which each of them builds its result directly; the
    positions it gives rename a field type of the description into the
    telescope of the method ([transport]) and the fields into variables
    there ([field_vars]).  The module depends only on the kernel's syntax
    and descriptions. *)

From Stdlib Require Import List.
Import ListNotations.
From DepTypes.PTS Require Import Syntax Signature.

(** ** Sizes *)

(** The number of recursive fields among [fs]. *)
Fixpoint nrecs (fs : list field) : nat :=
  match fs with
  | [] => 0
  | FArg _ :: fs' => nrecs fs'
  | FRec _ _ :: fs' => S (nrecs fs')
  end.

(** The number of binders of a method on [fs], in one pass: a field
    each, and a hypothesis after each recursive one. *)
Fixpoint nbinders (fs : list field) : nat :=
  match fs with
  | [] => 0
  | FArg _ :: fs' => S (nbinders fs')
  | FRec _ _ :: fs' => S (S (nbinders fs'))
  end.

(** ** The binders, from the outermost *)

(** With an accumulator: [f acc fd l k b rbs] for each field [fd], where
    [l] is its position among the fields, [k] the number of recursive
    fields before it, [b] the position of its binder and [rbs] the
    positions of the earlier fields, innermost first. *)
Section Slots.
  Context {A : Type}.
  Variable f : A -> field -> nat -> nat -> nat -> list nat -> A.

  Fixpoint slots_from (acc : A) (rbs : list nat) (b k l : nat) (fs : list field) : A * list nat * nat :=
    match fs with
    | [] => (acc, rbs, b)
    | fd :: fs' =>
        let acc' := f acc fd l k b rbs in
        match fd with
        | FArg _ => slots_from acc' (b :: rbs) (S b) k (S l) fs'
        | FRec _ _ => slots_from acc' (b :: rbs) (S (S b)) (S k) (S l) fs'
        end
    end.
End Slots.

(** The accumulator over the fields [fs], the positions of all the fields
    and the number of binders. *)
Definition fold_slots {A} (f : A -> field -> nat -> nat -> nat -> list nat -> A) (acc : A) (fs : list field)
  : A * list nat * nat :=
  slots_from f acc [] 0 0 0 fs.

(** ** Into the telescope of a method *)

(** From the context of the parameters and the earlier fields of a
    constructor into the telescope of its method: [rbs] are the positions
    of the earlier fields among the binders of the method, innermost
    first, [b] the number of those binders so far, and [g] the number of
    binders between the parameters and those of the method. *)
Definition transport_past (g : nat) (rbs : list nat) (b n : nat) : nat :=
  match nth_error rbs n with
  | Some bl => b - 1 - bl
  | None => n - length rbs + (b + g)
  end.

(** In the eliminator, the motive lies between. *)
Definition transport : list nat -> nat -> nat -> nat := transport_past 1.

(** The fields at [rbs], outermost first, as variables under the [b]
    binders of the method. *)
Definition field_vars (rbs : list nat) (b : nat) : list term :=
  map (fun bl => Var (b - 1 - bl)) (rev rbs).
