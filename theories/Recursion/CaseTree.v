(** * Annotated recursive functions and their case trees

    The input of algorithm 2: a function with an explicitly chosen
    structural argument [x : D Δ θ̄], its other arguments marked constant
    or varying in recursive calls, and the tree of dependent case splits
    written out, with named terms.  A split is allowed only on a variable
    whose type, as written, has distinct variables as indices, so that the
    eliminator applies to it directly, or is one of the primitive types
    Void, Unit and Bool, split by their own eliminators: [append], [half] and [isEven] qualify; [head :
    Vec A (succ n) → A] and [zip] need unification of indices and are out
    of scope.  Nested splits uncover strict subterms of any depth, as in
    [succ (succ n)].  The branches of a split name the fields of their
    constructor, in any order of constructors; a recursive call is the
    function's own constant [Const (Def f)] applied in a leaf.

    This module elaborates a case tree into the scopes and goals the
    compiler (Recursion.Compile) turns into terms, as a proof assistant
    does a [destruct] that generalizes what depends on the variable:

    - a scope is the context of the term being built, innermost first;
      each binder carries a name the user may write, or none, for a
      variable a split has replaced, or the tag of a binder of the
      compiler: the history, a hypothesis;
    - a split of [z : D Δ θ̄] in the goal [G ⊢ T] generalizes the indices,
      z and the dependent tail of the scope, the binders whose types
      mention them, directly or transitively, in their order: the motive
      is [λθ̄ z. Π(tail). T].  A binder the indices or z depend on cannot
      be generalized after them, and the parameters Δ must not mention
      what is generalized;
    - the branch of a constructor c binds its fields, each recursive one
      followed by its hypothesis as the method of the eliminator does,
      then the tail again, with [ū] for θ̄ and [c Δ ā] for z; its goal is
      T with the same substitution.  The binders replaced keep their
      place in the scope without their names;
    - the values of the function's arguments, the left side of its
      defining equation, follow every split.

    The same generalization makes the motive of the recursion itself
    (Recursion.Compile): there the varying arguments join the tail.

    Each pattern variable records its path from the structural argument:
    the index of its field among the recursive fields of the constructor
    at every split on the way, and their number, so that the result of a
    recursive call on it is found in the history.  Its application to the
    positions ȳ of a functional field is left to the call. *)

From Stdlib Require Import List Bool Arith.
From Stdlib Require String.
Import ListNotations.
Import (notations) String.StringSyntax.
Local Open Scope string_scope.
Local Open Scope list_scope.
From DepTypes.Common Require Import Result.
From DepTypes.PTS Require Import Syntax Named Signature.
From IndTypes Require Import Telescope MethodLayout.
From IndTypes.Elim Require Import Decl.
From IndTypes Require Import Diagnostics.

Local Notation string := String.string.

(** ** Annotated functions *)

Inductive mark : Type := Constant | Varying.

(** [Direct]: every recursive call is on a field of the split of the
    structural argument at the root and becomes its hypothesis, the terms
    written by hand for [+], [pow] and [f]; [History]: through
    [recBelow_D], a call on a subterm at any depth. *)
Inductive strategy : Type := Direct | History.

(** A leaf is the right side, a split names its variable and, for every
    constructor, the names of its fields and the subtree. *)
Inductive case_tree : Type :=
| Leaf : nterm -> case_tree
| Split : string -> list (string * list string * case_tree) -> case_tree.

Record fun_decl : Type := mk_fun {
  fn_name : string;
  fn_args : list (string * nterm * mark);   (** outermost first, each in the scope of the earlier *)
  fn_result : nterm;                        (** in the scope of the arguments *)
  fn_struct : string;
  fn_strategy : strategy;
  fn_tree : case_tree;
}.

(** ** Scopes *)

(** The steps from the structural argument to a subterm: at each split,
    the index of the field among the recursive fields of the constructor,
    and their number. *)
Definition path : Type := list (nat * nat).

Inductive tag : Type :=
| User : string -> option path -> tag   (** a name the user may write; its path if a subterm *)
| Anon : tag                            (** replaced by a split, or a hypothesis not used *)
| Aux : nat -> tag.                     (** a binder of the compiler *)

(** A binder's type lies in the scope behind it. *)
Record binder : Type := mk_binder { b_tag : tag; b_type : term }.

Definition scope : Type := list binder.     (** innermost first *)

Definition mem (n : nat) (l : list nat) : bool := existsb (Nat.eqb n) l.

Fixpoint position (n : nat) (l : list nat) : option nat :=
  match l with
  | [] => None
  | m :: l' => if Nat.eqb n m then Some 0 else option_map S (position n l')
  end.

Fixpoint distinct (l : list nat) : bool :=
  match l with
  | [] => true
  | n :: l' => negb (mem n l') && distinct l'
  end.

Fixpoint mapi_from {A B} (f : nat -> A -> B) (i : nat) (l : list A) : list B :=
  match l with
  | [] => []
  | a :: l' => f i a :: mapi_from f (S i) l'
  end.

(** The names the user may write, innermost first, and the index in the
    scope of the [i]-th of them. *)
Definition visible (G : scope) : list string :=
  flat_map (fun b => match b_tag b with User x _ => [x] | _ => [] end) G.

Fixpoint from_visible (G : scope) (i : nat) : nat :=
  match G with
  | [] => i
  | b :: G' =>
      match b_tag b, i with
      | User _ _, 0 => 0
      | User _ _, S i' => S (from_visible G' i')
      | _, _ => S (from_visible G' i)
      end
  end.

(** A named term in a scope. *)
Definition resolve_in (G : scope) (t : nterm) : result case_error term :=
  match resolve (visible G) t with
  | Ok u => Ok (rename (from_visible G) u)
  | Err x => Err (CUnbound x)
  end.

(** The nearest binder named [x]: its index, path and type. *)
Fixpoint lookup_user (x : string) (G : scope) : option (nat * option path * term) :=
  match G with
  | [] => None
  | b :: G' =>
      match b_tag b with
      | User y p =>
          if String.eqb x y then Some (0, p, b_type b)
          else option_map (fun '(v, p, A) => (S v, p, A)) (lookup_user x G')
      | _ => option_map (fun '(v, p, A) => (S v, p, A)) (lookup_user x G')
      end
  end.

(** The nearest binder of the compiler with the tag [Aux k]. *)
Fixpoint find_aux (k : nat) (G : scope) : option nat :=
  match G with
  | [] => None
  | b :: G' =>
      match b_tag b with
      | Aux k' => if Nat.eqb k k' then Some 0 else option_map S (find_aux k G')
      | _ => option_map S (find_aux k G')
      end
  end.

(** By levels, counted from the outermost binder: the binder at level [l]
    of a scope of [N] binders has the index [N - 1 - l], and its type the
    [l] binders before it. *)
Definition at_level (G : scope) (l : nat) : option binder := nth_error (rev G) l.

Definition level_type (G : scope) (l : nat) : term :=
  match at_level G l with Some b => b_type b | None => Void end.

Definition level_name (G : scope) (l : nat) : string :=
  match at_level G l with Some {| b_tag := User x _ |} => x | _ => "_" end.

(** Whether [A], in a context of [l] binders, mentions the binder at
    level [m]. *)
Definition mentions_level (l : nat) (A : term) (m : nat) : bool :=
  Nat.ltb m l && free_in (l - 1 - m) A.

(** ** Generalization *)

(** The binders a split generalizes beyond the seeds [ss] (the indices
    and the variable split): those in [extra], and those whose types
    mention a seed or a binder already in the tail; by levels, outermost
    first.  A binder without a name stays: nothing refers to a variable a
    split has replaced, or to a hypothesis not used. *)
Definition anonymous (b : binder) : bool := match b_tag b with Anon => true | _ => false end.

(** From the binders [bs] at the level [l] on, [acc] the tail so far. *)
Fixpoint tail_from (l : nat) (bs : list binder) (ss extra acc : list nat) : list nat :=
  match bs with
  | [] => acc
  | b :: bs' =>
      let joins := negb (anonymous b) && negb (mem l ss) &&
                   (mem l extra || existsb (mentions_level l (b_type b)) (ss ++ acc)) in
      tail_from (S l) bs' ss extra (if joins then acc ++ [l] else acc)
  end.

(** The tail of a split of the seeds [ss] in the scope [G]. *)
Definition split_tail (G : scope) (ss extra : list nat) : list nat := tail_from 0 (rev G) ss extra [].

(** In the motive, the seeds follow the scope of [N] binders and the tail
    follows them. *)
Definition moved (N : nat) (ss tail : list nat) (l : nat) : nat :=
  match position l ss with
  | Some i => N + i
  | None => match position l tail with Some k => N + length ss + k | None => l end
  end.

(** [A], in a context of [l] binders, into one of [n] binders, its free
    variables moved by levels. *)
Definition relevel (f : nat -> nat) (l n : nat) (A : term) : term :=
  rename (fun v => n - 1 - f (l - 1 - v)) A.

Record generalized : Type := {
  gn_seeds : list nat;          (** levels of θ̄ and the variable split *)
  gn_tail : list nat;           (** levels, outermost first *)
  gn_seed_types : list term;    (** after the scope, each after the seeds before it *)
  gn_tail_types : list term;    (** after the scope and the seeds, each after the tail before it *)
  gn_goal : term;               (** after the scope, the seeds and the tail *)
}.

(** The generalization of the goal [G ⊢ goal] over the seeds [ss] with
    the tail [tail] of the split.  The seeds must not depend on the
    tail. *)
Definition generalize_with (G : scope) (goal : term) (ss tail : list nat) : result case_error generalized :=
  let N := length G in
  let* _ := mapM (fun s =>
              match find (mentions_level s (level_type G s)) tail with
              | Some t => Err (CGeneralize (level_name G s) (level_name G t))
              | None => Ok tt
              end) ss in
  let mv := moved N ss tail in
  Ok {| gn_seeds := ss; gn_tail := tail;
        gn_seed_types := mapi_from (fun i s => relevel mv s (N + i) (level_type G s)) 0 ss;
        gn_tail_types := mapi_from (fun k t => relevel mv t (N + length ss + k) (level_type G t)) 0 tail;
        gn_goal := relevel mv N (N + length ss + length tail) goal |}.

(** With [extra] in the tail. *)
Definition generalize (G : scope) (goal : term) (ss extra : list nat) : result case_error generalized :=
  generalize_with G goal ss (split_tail G ss extra).

(** [λθ̄ z. Π(tail). T], in the scope. *)
Definition motive (gn : generalized) : term :=
  lams (length (gn_seeds gn)) (pis (gn_tail_types gn) (gn_goal gn)).

(** A term after a scope of [N] binders, the [s] seeds and [k] binders of
    the tail, into the scope with [b] binders after it and then the [k]
    binders: the seeds stand for [values], after the [b] binders. *)
Definition instantiate (N s b k : nat) (values : list term) (A : term) : term :=
  subst (fun v => let l := N + s + k - 1 - v in
                  if Nat.ltb l N then Var (v + b - s)
                  else if Nat.ltb l (N + s) then lift k (nth (l - N) values (Var 0))
                  else Var v) A.

(** The motive applied to [values], after [b] binders: [Π(tail). T] with
    the seeds standing for them. *)
Definition motive_at (N : nat) (gn : generalized) (b : nat) (values : list term) : term :=
  instantiate N (length (gn_seeds gn)) b 0 values (pis (gn_tail_types gn) (gn_goal gn)).

(** The scope after the new binders [B] (innermost first, as in a
    scope: each after the scope and those after it in [B]), with the
    seeds standing for [values] (in the scope with [B]) and the tail
    bound again after them: the scope, the goal, and the substitution
    from the old scope into the new one.  The binders of the seeds and of
    the old tail lose their names. *)
Definition introduce (G : scope) (gn : generalized) (B : list binder) (values : list term)
  : scope * term * (nat -> term) :=
  let N := length G in
  let s := length (gn_seeds gn) in
  let b := length B in
  let n := length (gn_tail gn) in
  let inst (k : nat) := instantiate N s b k values in
  let tail := mapi_from (fun k '(t, A) =>
                let tg := match at_level G t with Some bd => b_tag bd | None => Anon end in
                mk_binder tg (inst k A)) 0 (combine (gn_tail gn) (gn_tail_types gn)) in
  let gone := gn_seeds gn ++ gn_tail gn in
  let old := mapi_from (fun v bd => if mem (N - 1 - v) gone then mk_binder Anon (b_type bd) else bd) 0 G in
  let sb (v : nat) : term :=
    let l := N - 1 - v in
    match position l (gn_seeds gn) with
    | Some i => lift n (nth i values (Var 0))
    | None => match position l (gn_tail gn) with
              | Some k => Var (n - 1 - k)
              | None => Var (v + b + n)
              end
    end in
  (rev tail ++ B ++ old, inst n (gn_goal gn), sb).

(** ** Splits *)

(** The primitive types of lecture 6, split by their own eliminators: as
    families without parameters, indices or fields, whose constructors
    [tt], [true] and [false] stand for their values. *)
Inductive prim : Type := PVoid | PUnit | PBool.

Definition prim_of (A : term) : option prim :=
  match A with Void => Some PVoid | Unit => Some PUnit | Bool => Some PBool | _ => None end.

Definition prim_type (pr : prim) : term :=
  match pr with PVoid => Void | PUnit => Unit | PBool => Bool end.

Definition prim_name (pr : prim) : string :=
  match pr with PVoid => "Void" | PUnit => "Unit" | PBool => "Bool" end.

(** The constructors, each with its value. *)
Definition prim_ctors (pr : prim) : list (string * term) :=
  match pr with
  | PVoid => []
  | PUnit => [("tt", Tt)]
  | PBool => [("true", BTrue); ("false", BFalse)]
  end.

Definition prim_desc (pr : prim) : ind_desc :=
  {| ind_name := prim_name pr; ind_params := []; ind_indices := []; ind_level := 0;
     ind_ctors := map (fun '(c, _) => {| ctor_name := c; ctor_fields := []; ctor_indices := [] |})
                    (prim_ctors pr) |}.

(** The value of the constructor [c] of [pr]; a split asks only for the
    constructors of [prim_desc pr]. *)
Definition prim_value (pr : prim) (c : string) : term :=
  match find (fun cv => String.eqb (fst cv) c) (prim_ctors pr) with
  | Some (_, v) => v
  | None => Var 0
  end.

(** A variable to split and its type, as written: [D Δ θ̄] with
    distinct variables as indices, or a primitive type.  Its position and
    those of the indices are levels in the scope. *)
Record split_var : Type := {
  sv_name : string;
  sv_level : nat;            (** of the variable *)
  sv_path : option path;     (** from the structural argument, if a subterm *)
  sv_desc : ind_desc;
  sv_prim : option prim;     (** a primitive type, split by its eliminator *)
  sv_params : list term;     (** Δ, in the scope *)
  sv_indices : list nat;     (** the levels of θ̄ *)
}.

(** The variable at level [l] of a scope of [N] binders. *)
Definition var_at (N l : nat) : term := Var (N - 1 - l).

Definition family_of (sg : signature) (G : scope) (x : string) : result case_error split_var :=
  let* r := match lookup_user x G with Some r => Ok r | None => Err (CUnbound x) end in
  let '(v, p, A) := r in
  let zl := length G - 1 - v in
  match prim_of A with
  | Some pr =>
      Ok {| sv_name := x; sv_level := zl; sv_path := p; sv_desc := prim_desc pr; sv_prim := Some pr;
            sv_params := []; sv_indices := [] |}
  | None =>
      let* d := match spine_head A with
                | Const (Ind D) => match sig_ind sg D with Some d => Ok d | None => Err (CNotFamily x A) end
                | _ => Err (CNotFamily x A)
                end in
      let args := spine_args A in
      let np := length (ind_params d) in
      let* _ := require (Nat.eqb (length args) (np + length (ind_indices d))) (CNotFamily x A) in
      let* θ := mapM (fun t => match t with Var u => Ok (zl - 1 - u) | _ => Err (CIndices x A) end) (skipn np args) in
      let* _ := require (distinct θ) (CIndices x A) in
      Ok {| sv_name := x; sv_level := zl; sv_path := p; sv_desc := d; sv_prim := None;
            sv_params := map (lift (S v)) (firstn np args); sv_indices := θ |}
  end.

Section Fields.
  Variable D : string.
  Variable np : nat.
  Variable params : list term.     (** Δ, in the scope *)
  Variable N : nat.                (** the size of the scope *)
  Variable gn : generalized.
  Variable sub : option path.      (** the path of the variable split *)
  Variable nrec : nat.             (** the number of recursive fields *)
  Variable hyp_tag : nat -> tag.

  (** From the context of the parameters and the earlier fields, at [rbs]
      among [b] binders after the scope, innermost first. *)
  Definition field_sub (rbs : list nat) (b n : nat) : term :=
    match nth_error rbs n with
    | Some bl => Var (b - 1 - bl)
    | None => lift b (nth (np - 1 - (n - length rbs)) params (Var 0))
    end.

  (** The binders of the field [fd] named [x] at [l], its binder at [b]
      after the earlier fields at [rbs] with [k] recursive ones among them,
      on the binders [B] before it, innermost first: the field and, after
      a recursive one [r : Πȳ:B̄. D Δ v̄], its hypothesis [Πȳ:B̄. Π(tail). T]
      for [v̄] and [r ȳ]: the motive applied, reduced. *)
  Definition bind_field (x : string) (B : list binder) (fd : field) (l k b : nat) (rbs : list nat)
    : list binder :=
    let A := subst (field_sub rbs b) (field_type D np l fd) in
    match fd with
    | FArg _ => mk_binder (User x None) A :: B
    | FRec Bs vs =>
        let m := length Bs in
        let sb := field_sub rbs (S b) in
        let H := pis (subst_tele sb Bs)
                   (motive_at N gn (S b + m) (map (subst (upn_sub m sb)) vs ++ [apps (Var m) (vars 0 m)])) in
        let p := option_map (fun p => p ++ [(k, nrec)]) sub in
        mk_binder (hyp_tag k) H :: mk_binder (User x p) A :: B
    end.

  (** The fields [fs] named [xs], as [fold_slots] of MethodLayout lays
      them out after the scope: the binders, innermost first as in a
      scope, the positions of all the fields and the number of binders.
      The names are taken in order, with the binders. *)
  Definition field_binders (xs : list string) (fs : list field) : list binder * list nat * nat :=
    let '(xB, rbs, b) := fold_slots (fun '(xs, B) fd l k b rbs =>
                                       match xs with
                                       | x :: xs' => (xs', bind_field x B fd l k b rbs)
                                       | [] => ([], B)
                                       end) (xs, []) fs in
    (snd xB, rbs, b).
End Fields.

(** A split: the variable, and the generalization of the goal over its
    indices and itself, the seeds [sv_indices ++ [sv_level]]. *)
Record split_info : Type := { si_var : split_var; si_gen : generalized }.

Record branch : Type := {
  br_ctor : string;
  br_binders : nat;          (** fields and hypotheses *)
  br_scope : scope;
  br_goal : term;
  br_subst : nat -> term;    (** from the scope of the split *)
}.

Definition count_name (c : string) (names : list string) : nat :=
  length (filter (String.eqb c) names).

(** The variable [x] with its family, and the generalization of the goal
    over its indices and itself, with [extra] in the tail, computed once.
    First the parameters must not mention what is generalized: at the
    root, a varying parameter is non-uniform recursion. *)
Definition prepare_split (sg : signature) (G : scope) (goal : term) (x : string) (extra : list nat)
  : result case_error split_info :=
  let* sv := family_of sg G x in
  let N := length G in
  let ss := sv_indices sv ++ [sv_level sv] in
  let tail := split_tail G ss extra in
  let gone := ss ++ tail in
  let* _ := mapM (fun pa =>
              match find (mentions_level N pa) gone with
              | Some t => Err (CParams x (level_name G t))
              | None => Ok tt
              end) (sv_params sv) in
  let* gn := generalize_with G goal ss tail in
  Ok {| si_var := sv; si_gen := gn |}.

(** The split of [x] in the goal [G ⊢ goal], [extra] in the tail and the
    hypotheses of recursive fields tagged by [hyp_tag]; [bs] are the
    constructors of the branches with the names of their fields. *)
Definition split_node (sg : signature) (G : scope) (goal : term) (x : string) (extra : list nat)
    (hyp_tag : nat -> tag) (bs : list (string * list string)) : result case_error (split_info * list branch) :=
  let* si := prepare_split sg G goal x extra in
  let sv := si_var si in
  let gn := si_gen si in
  let d := sv_desc sv in
  let params := sv_params sv in
  let N := length G in
  let ctors := ind_ctors d in
  let* _ := require (Nat.eqb (length bs) (length ctors) &&
                     forallb (fun c => Nat.eqb (count_name (ctor_name c) (map fst bs)) 1) ctors)
              (CBranches x) in
  let generalized_names := map (level_name G) (gn_tail gn) in
  let D := ind_name d in
  let np := length (ind_params d) in
  let* brs := mapM (fun c =>
    let xs := match find (fun br => String.eqb (fst br) (ctor_name c)) bs with
              | Some br => snd br
              | None => []
              end in
    let* _ := require (Nat.eqb (length xs) (length (ctor_fields c))) (CFields (ctor_name c) (length (ctor_fields c))) in
    let* _ := match first_duplicate xs with Some y => Err (CFieldName (ctor_name c) y) | None => Ok tt end in
    let* _ := match find (fun y => existsb (String.eqb y) generalized_names) xs with
              | Some y => Err (CFieldName (ctor_name c) y)
              | None => Ok tt
              end in
    let '(B, rbs, b) := field_binders D np params N gn (sv_path sv) (nrecs (ctor_fields c)) hyp_tag xs (ctor_fields c) in
    let indices := map (subst (field_sub np params rbs b)) (ctor_indices c) in
    let obj := match sv_prim sv with
               | Some pr => prim_value pr (ctor_name c)
               | None => apps (Const (Ctor D (ctor_name c)))
                           (map (lift b) params ++ field_vars rbs b)
               end in
    let '(G', goal', sb) := introduce G gn B (indices ++ [obj]) in
    Ok {| br_ctor := ctor_name c; br_binders := b; br_scope := G'; br_goal := goal'; br_subst := sb |})
    ctors in
  Ok (si, brs).

(** ** Elaboration *)

(** A leaf: its scope, goal, the values of the function's arguments and
    the right side; a split: its scope, goal, the split, and for each
    constructor in the order of the declaration the number of its binders
    and the subtree. *)
Inductive elab : Type :=
| ELeaf : scope -> term -> list term -> term -> elab
| ESplit : scope -> term -> split_info -> list (nat * elab) -> elab.

(** The tree [t] in the goal [G ⊢ goal], [env] the values of the
    arguments; the split at the root with [extra] in its tail and its
    hypotheses tagged by [hyp_tag], every other split with neither. *)
Fixpoint elaborate_with (sg : signature) (extra : list nat) (hyp_tag : nat -> tag)
    (G : scope) (goal : term) (env : list term) (t : case_tree) {struct t} : result case_error elab :=
  match t with
  | Leaf rhs => let* u := resolve_in G rhs in Ok (ELeaf G goal env u)
  | Split x bs =>
      let* r := split_node sg G goal x extra hyp_tag (map (fun '(c, xs, _) => (c, xs)) bs) in
      let (si, brs) := r in
      let* es := (fix go (bs : list (string * list string * case_tree)) : result case_error (list (string * elab)) :=
                    match bs with
                    | [] => Ok []
                    | (c, _, t') :: bs' =>
                        match find (fun br => String.eqb (br_ctor br) c) brs with
                        | Some br =>
                            let* e := elaborate_with sg [] (fun _ => Anon) (br_scope br) (br_goal br)
                                        (map (subst (br_subst br)) env) t' in
                            let* es := go bs' in
                            Ok ((c, e) :: es)
                        | None => Err (CBranches x)
                        end
                    end) bs in
      let* ordered := mapM (fun br =>
                        match find (fun ce => String.eqb (fst ce) (br_ctor br)) es with
                        | Some ce => Ok (br_binders br, snd ce)
                        | None => Err (CBranches x)
                        end) brs in
      Ok (ESplit G goal si ordered)
  end.

Definition elaborate (sg : signature) : scope -> term -> list term -> case_tree -> result case_error elab :=
  elaborate_with sg [] (fun _ => Anon).

(** ** The arguments *)

Fixpoint push_args (s : string) (G : scope) (args : list (string * nterm * mark)) : result case_error scope :=
  match args with
  | [] => Ok G
  | (x, A, _) :: args' =>
      let* A' := resolve_in G A in
      push_args s (mk_binder (User x (if String.eqb x s then Some [] else None)) A' :: G) args'
  end.

(** The arguments as a scope, the structural one with the empty path; the
    result type as the goal; the values of the arguments, themselves. *)
Definition start (fn : fun_decl) : result case_error (scope * term * list term) :=
  let names := map (fun '(x, _, _) => x) (fn_args fn) in
  let* _ := match first_duplicate names with Some x => Err (CDuplicateArg x) | None => Ok tt end in
  let* _ := require (existsb (String.eqb (fn_struct fn)) names) (CNoStruct (fn_struct fn)) in
  let* G := push_args (fn_struct fn) [] (fn_args fn) in
  let* goal := resolve_in G (fn_result fn) in
  Ok (G, goal, vars 0 (length (fn_args fn))).

(** The levels of the varying arguments. *)
Definition varying (fn : fun_decl) : list nat :=
  flat_map (fun '(i, (_, _, mk)) => match mk with Varying => [i] | Constant => [] end)
    (combine (seq 0 (length (fn_args fn))) (fn_args fn)).
