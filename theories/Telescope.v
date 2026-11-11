(** * Telescopes

    A telescope is a list of types, outermost first, each in the context
    of those before it, as [pis] of PTS.Syntax takes it.  Both algorithms
    take the domains off a type (Elim.Decl, Recursion.Compile), and
    rename (Elim.Generate, Recursion.Below) a telescope entry by entry,
    each entry under those before it, and a term under the [m] binders
    of a telescope.  Substitution in a telescope and under its binders,
    [subst_tele] and [upn], is the kernel's PTS.Telescope
    (Recursion.CaseTree).  The module depends only on the kernel's
    syntax. *)

From Stdlib Require Import List Lia.
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

Lemma upn_ren_lt : forall n r i, i < n -> upn_ren n r i = i.
Proof.
  induction n as [|n IH]; intros r i H; [lia | ].
  destruct i as [|i]; cbn [upn_ren up_ren]; [reflexivity | ]. rewrite IH by lia. reflexivity.
Qed.

Lemma upn_ren_ge : forall n r j, upn_ren n r (n + j) = n + r j.
Proof. induction n as [|n IH]; intros r j; [reflexivity | cbn [upn_ren up_ren Nat.add]; rewrite IH; reflexivity]. Qed.

(** Renames a telescope: each entry under the entries before it. *)
Fixpoint rename_tele (r : nat -> nat) (As : list term) : list term :=
  match As with
  | [] => []
  | A :: As' => rename r A :: rename_tele (up_ren r) As'
  end.

Lemma length_rename_tele : forall As r, length (rename_tele r As) = length As.
Proof. induction As as [|A As IH]; intros r; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.
