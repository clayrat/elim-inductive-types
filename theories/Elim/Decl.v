(** * Declarations of inductive families and their classification

    The input of algorithm 1: a declaration after Dybjer's schema,
    [data D (Δ) : Πθ̄:Θ̄. Type_i where c₁ : con … c_k : con], with

      con ::= Π(x : A). con               non-recursive field: D not in A
            | Π(r : Πȳ:B̄. D Δ v̄). con     recursive field: D not in B̄, v̄
            | D Δ ū                        the result: D not in ū

    A raw declaration gives the parameters Δ and the indices Θ̄ as
    telescopes, outermost first, and every constructor type in the context
    of the parameters, with D written as the constant [Const (Ind D)]
    applied to the parameters and the indices.

    Classification walks the telescope of each constructor and sorts its
    fields into the two kinds of PTS.Signature, or rejects the field; it is
    the check of strict positivity.  A field is
    - non-recursive when D does not occur in it;
    - recursive when it is [Πȳ:B̄. D Δ' v̄] with D in neither B̄ nor v̄,
      [Δ'] exactly the parameters (uniformity) and as many indices as Θ̄;
    - rejected otherwise, with a diagnostic by the polarity of the
      occurrences of D: negative ([mk : (D → Void) → D], D in the domain
      of the field), only positive but not of the recursive form
      ([mk : ((D → Bool) → Bool) → D]: the codomain of the field is not D
      while D occurs in it), or nested under another former, such as an
      argument of another family, which the grammar leaves out.
    The result of a constructor must be [D Δ ū], uniform, with D not in ū.
    The parameters and indices may not mention D, every term must be
    closed in its telescope, and constructor names are distinct.  Nested
    and mutual declarations are outside the grammar.

    The levels of the fields, at most i, are checked when the declaration
    is registered (Elim.Declare): that needs the checker, and the
    recursive fields need D in the signature.

    A bypass mode classifies a field that fails strict positivity as
    non-recursive, for the demonstration of the negative field
    (Data.Positivity); it is outside the contract.

    Two theorems hold for every input.  [classify_decl_faithful]: the
    types of D and of its constructors rebuilt from the classified
    description (PTS.Signature) are exactly the declared ones, so typing
    the description is typing the declaration.
    [classify_decl_strictly_positive]: without the bypass, no part of the
    description mentions D, so D occurs in the constructor types exactly as
    the head of the recursive fields and of the results. *)

From Stdlib Require Import List Bool Arith Lia.
From Stdlib Require String.
Import ListNotations.
From DepTypes.Common Require Import Result.
From DepTypes.PTS Require Import Syntax Signature.

Local Notation string := String.string.

(** ** Raw declarations *)

Record raw_ctor : Type := mk_raw_ctor {
  rc_name : string;
  rc_type : term;     (** in the context of the parameters *)
}.

Record raw_decl : Type := mk_raw_decl {
  rd_name : string;
  rd_params : list term;
  rd_indices : list term;
  rd_level : nat;
  rd_ctors : list raw_ctor;
}.

(** ** Diagnostics *)

Inductive site : Type :=
| SField : nat -> site      (** a recursive field, by its position *)
| SResult : site.           (** the result [D Δ ū] *)

Inductive decl_error : Type :=
| EOpenParams : decl_error                  (** a parameter mentions a later variable *)
| EOpenIndices : decl_error
| ESelfReference : decl_error               (** D in its own parameters or indices *)
| EOpenCtor : string -> decl_error          (** a free variable past the parameters *)
| EDuplicateCtor : string -> decl_error
| ENegative : string -> nat -> term -> decl_error   (** constructor, field, its type *)
| ENonStrict : string -> nat -> term -> decl_error
| ENested : string -> nat -> term -> decl_error
| ENotFamily : string -> term -> decl_error         (** the result is not [D Δ ū] *)
| EArity : string -> site -> term -> decl_error     (** D with the wrong number of arguments *)
| ENonUniform : string -> site -> term -> decl_error  (** D applied to other parameters *)
| EInIndices : string -> site -> term -> decl_error.  (** D in the indices *)

(** ** Occurrences of D *)

Definition of_family (D : string) (g : gref) : bool :=
  match g with
  | Ind D' | Ctor D' _ | Elim D' _ => String.eqb D' D
  | Def _ => false
  end.

(** Whether D, one of its constructors or an instance of its eliminator
    occurs in [t]. *)
Fixpoint mentions (D : string) (t : term) : bool :=
  match t with
  | Const g => of_family D g
  | Srt _ | Var _ | Void | Unit | Tt | Bool | BTrue | BFalse => false
  | Pi A B | Sigma A B | App A B | Ann A B | ElimVoid A B | Pair A B => mentions D A || mentions D B
  | Lam b | Fst b | Snd b => mentions D b
  | ElimUnit C c u => mentions D C || mentions D c || mentions D u
  | ElimBool C t f b => mentions D C || mentions D t || mentions D f || mentions D b
  end.

Definition free_of (D : string) (t : term) : bool := negb (mentions D t).

(** [t] is a spine of D. *)
Definition family_spine (D : string) (t : term) : bool :=
  match spine_head t with
  | Const (Ind D') => String.eqb D' D
  | _ => false
  end.

(** The domains of a type and what is left after them. *)
Fixpoint split_pis (t : term) : list term * term :=
  match t with
  | Pi A B => let (As, H) := split_pis B in (A :: As, H)
  | _ => ([], t)
  end.

(** The occurrences of D in a type at a polarity: as the head of a spine
    at a positive or a negative position, or elsewhere. *)
Record occurrences : Type := { occ_pos : bool; occ_neg : bool; occ_other : bool }.

Definition join (o o' : occurrences) : occurrences :=
  {| occ_pos := occ_pos o || occ_pos o'; occ_neg := occ_neg o || occ_neg o';
     occ_other := occ_other o || occ_other o' |}.

Fixpoint occurrences_in (D : string) (positive : bool) (t : term) : occurrences :=
  match t with
  | Pi A B => join (occurrences_in D (negb positive) A) (occurrences_in D positive B)
  | _ =>
      if family_spine D t then
        {| occ_pos := positive; occ_neg := negb positive;
           occ_other := existsb (mentions D) (spine_args t) |}
      else {| occ_pos := false; occ_neg := false; occ_other := mentions D t |}
  end.

(** The first name that occurs twice. *)
Fixpoint first_duplicate (names : list string) : option string :=
  match names with
  | [] => None
  | x :: rest => if existsb (String.eqb x) rest then Some x else first_duplicate rest
  end.

(** ** Classification *)

Section Classify.
  Variable D : string.
  Variables p q : nat.        (** the numbers of parameters and of indices *)
  Variable bypass : bool.

  (** The indices of a spine of D at depth [k] above the parameters: D is
      applied to the parameters themselves, then to [q] terms free of D. *)
  Definition family_args (c : string) (s : site) (k : nat) (t : term)
    : result decl_error (list term) :=
    let a := spine_args t in
    let* _ := require (Nat.eqb (length a) (p + q)) (EArity c s t) in
    let* _ := require (if list_eq_dec term_eq_dec (firstn p a) (vars k p) then true else false)
                (ENonUniform c s t) in
    let* _ := require (forallb (free_of D) (skipn p a)) (EInIndices c s t) in
    Ok (skipn p a).

  (** The field at position [l] of the constructor [c], of type [A]. *)
  Definition classify_field (c : string) (l : nat) (A : term) : result decl_error field :=
    if free_of D A then Ok (FArg A) else
    let (Bs, H) := split_pis A in
    if forallb (free_of D) Bs && family_spine D H then
      let* vs := family_args c (SField l) (length Bs + l) H in
      Ok (FRec Bs vs)
    else if bypass then Ok (FArg A)
    else
      let o := occurrences_in D true A in
      Err (if occ_neg o then ENegative c l A
           else if occ_other o then ENested c l A
           else ENonStrict c l A).

  (** The fields from position [l] on, and the result indices. *)
  Fixpoint classify_con (c : string) (l : nat) (t : term)
    : result decl_error (list field * list term) :=
    match t with
    | Pi A B =>
        let* fd := classify_field c l A in
        let* r := classify_con c (S l) B in
        Ok (fd :: fst r, snd r)
    | _ =>
        let* _ := require (family_spine D t) (ENotFamily c t) in
        let* us := family_args c SResult l t in
        Ok ([], us)
    end.

  Definition classify_ctor (rc : raw_ctor) : result decl_error ctor_desc :=
    let* _ := require (closed_above p (rc_type rc)) (EOpenCtor (rc_name rc)) in
    let* r := classify_con (rc_name rc) 0 (rc_type rc) in
    Ok {| ctor_name := rc_name rc; ctor_fields := fst r; ctor_indices := snd r |}.
End Classify.

Definition classify_decl_with (bypass : bool) (d : raw_decl) : result decl_error ind_desc :=
  let p := length (rd_params d) in
  let q := length (rd_indices d) in
  let* _ := require (tele_closed 0 (rd_params d)) EOpenParams in
  let* _ := require (tele_closed p (rd_indices d)) EOpenIndices in
  let* _ := require (forallb (free_of (rd_name d)) (rd_params d ++ rd_indices d)) ESelfReference in
  let* cs := mapM (classify_ctor (rd_name d) p q bypass) (rd_ctors d) in
  let* _ := match first_duplicate (map ctor_name cs) with
            | Some c => Err (EDuplicateCtor c)
            | None => Ok tt
            end in
  Ok {| ind_name := rd_name d; ind_params := rd_params d; ind_indices := rd_indices d;
        ind_level := rd_level d; ind_ctors := cs |}.

Definition classify_decl : raw_decl -> result decl_error ind_desc := classify_decl_with false.

(** ** Faithfulness *)

Lemma apps_spine : forall t, apps (spine_head t) (spine_args t) = t.
Proof.
  induction t; try reflexivity.
  cbn [spine_head spine_args]. unfold apps in *. rewrite fold_left_app. cbn. now rewrite IHt1.
Qed.

Lemma pis_split : forall t As H, split_pis t = (As, H) -> pis As H = t.
Proof.
  induction t; intros As H E; cbn in E; try (injection E as <- <-; reflexivity).
  destruct (split_pis t2) as [As' H'] eqn:E2. injection E as <- <-. cbn. f_equal. now apply IHt2.
Qed.

Lemma pis_app : forall As Bs t, pis (As ++ Bs) t = pis As (pis Bs t).
Proof. induction As as [|A As IH]; intros Bs t; cbn; [reflexivity | now rewrite IH]. Qed.

Lemma family_spine_head : forall D t, family_spine D t = true -> spine_head t = Const (Ind D).
Proof.
  intros D t H. unfold family_spine in H.
  destruct (spine_head t); try discriminate H. destruct g; try discriminate H.
  apply String.eqb_eq in H. now subst.
Qed.

Lemma family_args_ok : forall D p q c s k t us,
  family_args D p q c s k t = Ok us ->
  spine_args t = vars k p ++ us /\ forallb (free_of D) us = true.
Proof.
  intros D p q c s k t us H. unfold family_args in H.
  bind_in H u1 H1. bind_in H u2 H2. apply require_ok in H2.
  bind_in H u3 H3. apply require_ok in H3. injection H as <-.
  destruct (list_eq_dec term_eq_dec _ _) as [E|]; [ | discriminate H2].
  split; [rewrite <- E; symmetry; apply firstn_skipn | exact H3].
Qed.

Section Rebuild.
  Variable D : string.
  Variables p q : nat.
  Variable bypass : bool.

  Lemma classify_field_rebuilds : forall c l A fd,
    classify_field D p q bypass c l A = Ok fd -> field_type D p l fd = A.
  Proof.
    intros c l A fd H. unfold classify_field in H.
    destruct (free_of D A); [injection H as <-; reflexivity | ].
    destruct (split_pis A) as [Bs H0] eqn:Es.
    destruct (forallb (free_of D) Bs && family_spine D H0) eqn:Ef.
    - bind_in H vs Hv. injection H as <-. apply andb_prop in Ef as [_ Ef].
      destruct (family_args_ok _ _ _ _ _ _ _ _ Hv) as [Ea _].
      cbn [field_type]. rewrite <- Ea, <- (family_spine_head _ _ Ef), apps_spine.
      now apply pis_split.
    - destruct bypass; [injection H as <-; reflexivity | discriminate H].
  Qed.

  Lemma classify_con_rebuilds : forall c t l fs us,
    classify_con D p q bypass c l t = Ok (fs, us) ->
    pis (field_types D p l fs) (apps (Const (Ind D)) (vars (l + length fs) p ++ us)) = t.
  Proof.
    intros c t. induction t; intros l fs us H; cbn [classify_con] in H.
    all: lazymatch goal with
         | |- _ = Pi ?A ?B =>
             bind_in H fd Hf; bind_in H r Hr; destruct r as [fs' us'];
             injection H as <- <-; cbn [field_types pis length];
             rewrite (classify_field_rebuilds _ _ _ _ Hf);
             replace (l + S (length fs')) with (S l + length fs') by lia;
             now rewrite (IHt2 _ _ _ Hr)
         | |- _ =>
             bind_in H u Hfam; apply require_ok in Hfam; bind_in H vs Hargs;
             injection H as <- <-; cbn [field_types pis length]; rewrite Nat.add_0_r;
             destruct (family_args_ok _ _ _ _ _ _ _ _ Hargs) as [Ea _];
             rewrite <- Ea, <- (family_spine_head _ _ Hfam); apply apps_spine
         end.
  Qed.
End Rebuild.

Lemma mapM_Forall2 : forall {E A B} (f : A -> result E B) l l',
  mapM f l = Ok l' -> Forall2 (fun a b => f a = Ok b) l l'.
Proof.
  intros E A B f l. induction l as [|a l IH]; intros l' H; cbn in H.
  - injection H as <-. constructor.
  - bind_in H b Hb. bind_in H bs Hbs. injection H as <-. constructor; [exact Hb | now apply IH].
Qed.

(** The types rebuilt from the description are the declared ones. *)
Theorem classify_decl_faithful : forall bypass d desc,
  classify_decl_with bypass d = Ok desc ->
  ind_name desc = rd_name d /\
  ind_type desc = pis (rd_params d ++ rd_indices d) (Srt (Univ (rd_level d))) /\
  Forall2 (fun rc cd => ctor_name cd = rc_name rc /\ ctor_type desc cd = pis (rd_params d) (rc_type rc))
    (rd_ctors d) (ind_ctors desc).
Proof.
  intros bypass d desc H. unfold classify_decl_with in H.
  bind_in H u1 H1. bind_in H u2 H2. bind_in H u3 H3. bind_in H cs Hcs. bind_in H u4 H4.
  clear H1 H2 H3 H4.
  injection H as <-. split; [reflexivity | split; [reflexivity | ]]. cbn [ind_ctors].
  apply mapM_Forall2 in Hcs. eapply Forall2_impl; [ | exact Hcs]. intros rc cd Hc.
  unfold classify_ctor in Hc. bind_in Hc u Hu. clear Hu. bind_in Hc r Hr. destruct r as [fs us].
  injection Hc as <-. split; [reflexivity | ].
  unfold ctor_type. cbn [ind_params ind_name ctor_fields ctor_indices fst snd].
  rewrite pis_app. f_equal. exact (classify_con_rebuilds _ _ _ _ _ _ _ _ _ Hr).
Qed.

(** ** Strict positivity *)

Definition field_free (D : string) (fd : field) : bool :=
  match fd with
  | FArg A => free_of D A
  | FRec Bs vs => forallb (free_of D) Bs && forallb (free_of D) vs
  end.

(** No part of the description mentions D. *)
Definition desc_free (d : ind_desc) : bool :=
  let D := ind_name d in
  forallb (free_of D) (ind_params d ++ ind_indices d) &&
  forallb (fun c => forallb (field_free D) (ctor_fields c) && forallb (free_of D) (ctor_indices c))
    (ind_ctors d).

Lemma classify_field_free : forall D p q c l A fd,
  classify_field D p q false c l A = Ok fd -> field_free D fd = true.
Proof.
  intros D p q c l A fd H. unfold classify_field in H.
  destruct (free_of D A) eqn:EA; [injection H as <-; exact EA | ].
  destruct (split_pis A) as [Bs H0].
  destruct (forallb (free_of D) Bs && family_spine D H0) eqn:Ef; [ | discriminate H].
  bind_in H vs Hv. injection H as <-. apply andb_prop in Ef as [EB _].
  cbn. rewrite EB. exact (proj2 (family_args_ok _ _ _ _ _ _ _ _ Hv)).
Qed.

Lemma classify_con_free : forall D p q c t l fs us,
  classify_con D p q false c l t = Ok (fs, us) ->
  forallb (field_free D) fs && forallb (free_of D) us = true.
Proof.
  intros D p q c t. induction t; intros l fs us H; cbn [classify_con] in H.
  all: first
    [ bind_in H fd Hf; bind_in H r Hr; destruct r as [fs' us'];
      injection H as <- <-; cbn [forallb];
      rewrite (classify_field_free _ _ _ _ _ _ _ Hf); exact (IHt2 _ _ _ Hr)
    | bind_in H u Hfam; bind_in H vs Hargs; injection H as <- <-;
      exact (proj2 (family_args_ok _ _ _ _ _ _ _ _ Hargs)) ].
Qed.

Theorem classify_decl_strictly_positive : forall d desc,
  classify_decl d = Ok desc -> desc_free desc = true.
Proof.
  intros d desc H. unfold classify_decl, classify_decl_with in H.
  bind_in H u1 H1. bind_in H u2 H2. bind_in H u3 H3. apply require_ok in H3.
  bind_in H cs Hcs. bind_in H u4 H4. clear H4. injection H as <-.
  unfold desc_free. cbn [ind_name ind_params ind_indices ind_ctors]. rewrite H3. cbn.
  apply mapM_Forall2 in Hcs. clear H1 H2 H3.
  induction Hcs as [|rc cd rcs cds Hc _ IH]; [reflexivity | ]. cbn [forallb]. rewrite IH.
  unfold classify_ctor in Hc. bind_in Hc v Hv. clear Hv. bind_in Hc r Hr. destruct r as [fs us].
  injection Hc as <-. cbn [ctor_fields ctor_indices fst snd].
  now rewrite (classify_con_free _ _ _ _ _ _ _ _ Hr).
Qed.
