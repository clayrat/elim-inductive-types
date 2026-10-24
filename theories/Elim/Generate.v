(** * The dependent eliminator of a classified description

    For a classified declaration D and a chosen level j of the motive,
    the instance [elim_D[j]]:
    - the motive [P : Πθ̄:Θ̄. D Δ θ̄ → Type_j]: large elimination at any j
      (it is restricted only for Prop, in the next lecture);
    - for each constructor a method type: its fields, each recursive
      field [r : Πȳ:B̄. D Δ v̄] followed at once by its hypothesis
      [Πȳ:B̄. P v̄ (r ȳ)], and the result [P ū (c_k Δ ā)];
    - [elim_D[j] : Π(Δ). ΠP. M₁ → ⋯ → M_k → Πθ̄. Πx:D Δ θ̄. P θ̄ x];
    - the ι-rules [elim_D[j] Δ P m̄ ū (c_k Δ ā) ↝ m_k args(ā, ih̄)], with
      [ih := λȳ. elim_D[j] Δ P m̄ v̄ (r ȳ)] for a recursive field.

    The method type and the arguments [args] come from one left-to-right
    pass over the classified fields: a non-recursive field gives one
    argument, a recursive one the field and right after it its
    hypothesis, the order of [nat_rect].  For [node : Tree → Tree → Tree]
    the method takes [left, ih_left, right, ih_right], in the type and in
    the ι-rule alike.  The arguments of the right side of a rule are
    built by the kernel's own pass, [iota_args] of PTS.Signature, so the
    rules a registration checks are the ones the kernel runs.

    A field type of the description lives in the context of the
    parameters and the earlier fields; in the telescope of a method the
    motive comes after the parameters, and a hypothesis after every
    recursive field.  [transport] renames a field type into that
    telescope: an earlier field goes to its position among the binders of
    the method, a parameter past the motive and all those binders.

    The level j is part of the constant's name, [Elim D j]: every instance
    has one closed type with a concrete level.  There is no universe
    polymorphism and no cumulativity.

    The ι-rule of a constructor is given as data for its check: the
    context of the parameters, the motive, the methods and the fields,
    the two sides, and the type [P ū (c_k Δ ā)] they must both check
    against.  Registering an instance (Elim.Declare) checks them. *)

From Stdlib Require Import List Arith.
From Stdlib Require String.
Import ListNotations.
From DepTypes.PTS Require Import Syntax Signature.
From IndTypes.Elim Require Import Decl.

Local Notation string := String.string.

(** ** Renamings of telescopes *)

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

(** Entries of a telescope that do not depend on each other: the i-th is
    lifted past the i before it. *)
Fixpoint lifted (i : nat) (As : list term) : list term :=
  match As with
  | [] => []
  | A :: As' => lift i A :: lifted (S i) As'
  end.

(** From the context of the parameters and the earlier fields of a
    constructor into the telescope of its method: [rbs] are the positions
    of the earlier fields among the binders of the method, innermost
    first, and [b] the number of those binders so far. *)
Definition transport (rbs : list nat) (b : nat) (n : nat) : nat :=
  match nth_error rbs n with
  | Some bl => b - 1 - bl
  | None => n - length rbs + S b
  end.

(** ** Motive, methods, eliminator *)

Section Generate.
  Variable d : ind_desc.
  Variable j : nat.

  Let D := ind_name d.
  Let p := length (ind_params d).
  Let q := length (ind_indices d).
  Let k := length (ind_ctors d).

  (** [Πθ̄:Θ̄. D Δ θ̄ → Type_j], in the context of the parameters. *)
  Definition motive_type : term :=
    pis (ind_indices d) (Pi (apps (Const (Ind D)) (vars q p ++ vars 0 q)) (Srt (Univ j))).

  (** The hypothesis of a recursive field just bound: [r] renames its
      domains and indices to the binders before the field, [b] counts
      them; the motive lies past them and the field. *)
  Definition hyp_type (r : nat -> nat) (b : nat) (Bs vs : list term) : term :=
    let m := length Bs in
    let r' := fun n => S (r n) in
    pis (rename_tele r' Bs)
      (apps (Var (S b + m)) (map (rename (upn_ren m r')) vs ++ [apps (Var m) (vars 0 m)])).

  (** The method of the constructor [c] from its field at position [l] on,
      in the context of the parameters and the motive. *)
  Fixpoint method_from (c : string) (rbs : list nat) (b l : nat) (fs : list field) (us : list term)
    : term :=
    match fs with
    | [] =>
        apps (Var b) (map (rename (transport rbs b)) us ++
          [apps (Const (Ctor D c)) (vars (S b) p ++ map (fun bl => Var (b - 1 - bl)) (rev rbs))])
    | FArg A :: fs' =>
        Pi (rename (transport rbs b) A) (method_from c (b :: rbs) (S b) (S l) fs' us)
    | FRec Bs vs :: fs' =>
        Pi (rename (transport rbs b) (field_type D p l (FRec Bs vs)))
          (Pi (hyp_type (transport rbs b) b Bs vs)
             (method_from c (b :: rbs) (S (S b)) (S l) fs' us))
    end.

  Definition method_type (c : ctor_desc) : term :=
    method_from (ctor_name c) [] 0 0 (ctor_fields c) (ctor_indices c).

  (** [Π(Δ). ΠP. M₁ → ⋯ → M_k → Πθ̄:Θ̄. Πx:D Δ θ̄. P θ̄ x]. *)
  Definition elim_type : term :=
    pis (ind_params d)
      (Pi motive_type
         (pis (lifted 0 (map method_type (ind_ctors d)))
            (pis (rename_tele (Nat.add (S k)) (ind_indices d))
               (Pi (apps (Const (Ind D)) (vars (q + S k) p ++ vars 0 q))
                  (apps (Var (S (k + q))) (vars 1 q ++ [Var 0])))))).

  (** ** The ι-rules *)

  Record iota_rule : Type := {
    rule_ctor : string;
    rule_ctx : ctx;          (** the fields, the methods, the motive, the parameters *)
    rule_lhs : term;         (** [elim_D[j] Δ P m̄ ū (c Δ ā)] *)
    rule_rhs : term;         (** [m_c args(ā, ih̄)] *)
    rule_type : term;        (** [P ū (c Δ ā)] *)
  }.

  (** The rule of the [i]-th constructor [c]. *)
  Definition iota_rule_of (i : nat) (c : ctor_desc) : iota_rule :=
    let n := length (ctor_fields c) in
    let params := vars (n + S k) p in
    let pre := params ++ [Var (n + k)] ++ vars n k in
    let us := map (rename (upn_ren n (Nat.add (S k)))) (ctor_indices c) in
    let obj := apps (Const (Ctor D (ctor_name c))) (params ++ vars 0 n) in
    {| rule_ctor := ctor_name c;
       rule_ctx := rev (rename_tele (Nat.add (S k)) (field_types D p 0 (ctor_fields c))) ++
                   rev (lifted 0 (map method_type (ind_ctors d))) ++
                   [motive_type] ++ rev (ind_params d);
       rule_lhs := apps (Const (Elim D j)) (pre ++ us ++ [obj]);
       rule_rhs := apps (Var (n + k - 1 - i)) (iota_args D j pre (rev params) (ctor_fields c) (vars 0 n));
       rule_type := apps (Var (n + k)) (us ++ [obj]) |}.

  Fixpoint rules_from (i : nat) (cs : list ctor_desc) : list iota_rule :=
    match cs with
    | [] => []
    | c :: cs' => iota_rule_of i c :: rules_from (S i) cs'
    end.

  Definition iota_rules : list iota_rule := rules_from 0 (ind_ctors d).
End Generate.
