(** * Telescopes

    A telescope is a list of types, outermost first, each in the context
    of those before it, as [pis] of PTS.Syntax takes it.  Both algorithms
    take the domains off a type (Elim.Decl, Recursion.Compile), and
    rename (Elim.Generate, Recursion.Below) or substitute in
    (Recursion.CaseTree) a telescope entry by entry, each entry under
    those before it, and a term under the [m] binders of a telescope.
    The module depends only on the kernel's syntax. *)

From Stdlib Require Import List.
Import ListNotations.
From DepTypes.PTS Require Import Syntax.

(** ** Domains *)

(** The domains of a type and what is left after them. *)
Fixpoint split_pis (t : term) : list term * term :=
  match t with
  | Pi A B => let (As, H) := split_pis B in (A :: As, H)
  | _ => ([], t)
  end.

Lemma pis_split : forall t As H, split_pis t = (As, H) -> pis As H = t.
Proof.
  induction t; intros As H E; cbn in E; try (injection E as <- <-; reflexivity).
  destruct (split_pis t2) as [As' H'] eqn:E2. injection E as <- <-. cbn. f_equal. now apply IHt2.
Qed.

(** ** Renamings *)

Fixpoint upn_ren (m : nat) (r : nat -> nat) : nat -> nat :=
  match m with
  | 0 => r
  | S m' => up_ren (upn_ren m' r)
  end.

(** Renames a telescope: each entry under the entries before it. *)
Fixpoint rename_tele (r : nat -> nat) (As : list term) : list term :=
  match As with
  | [] => []
  | A :: As' => rename r A :: rename_tele (up_ren r) As'
  end.

(** ** Substitutions *)

(** Substitution under the [m] binders of a telescope, and in each entry
    of one. *)
Fixpoint upn_sub (m : nat) (sb : nat -> term) : nat -> term :=
  match m with
  | 0 => sb
  | S m' => up_sub (upn_sub m' sb)
  end.

Fixpoint subst_tele (sb : nat -> term) (As : list term) : list term :=
  match As with
  | [] => []
  | A :: As' => subst sb A :: subst_tele (up_sub sb) As'
  end.
