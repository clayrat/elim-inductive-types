(** * [declare_checked]: registering a declaration and its eliminators

    The checked entry point of algorithm 1, as [translate_checked] in
    lecture 6.  A raw declaration is classified (Elim.Decl) and
    registered with its constructors once
    - the name D is free in the signature;
    - the type of D and the type of every constructor, rebuilt from the
      description, are types in the signature extended by D;
    - every field has a sort allowed in D, [within]: for [D : Type_i] a
      proof, in Prop, or a type of [Type_k] with k ≤ i, otherwise a type
      in [Type₀] could have a field in [Type₀] itself, and Type-in-Type
      would come back; for [D : Prop] a field of any sort, as Prop is
      impredicative.  Impredicativity lifts only this bound: positivity,
      uniformity and the types of the constructors are checked alike.
    The sorts of the fields give D its category of elimination,
    [elim_class_of]: data eliminates into every sort; a proposition only
    into Prop, unless it has no constructor or one whose fields are all
    proofs, the empty and the singleton propositions such as [False],
    [True], [eq] and [and].  Indices are no fields: [eq] is a singleton.
    The constructors are checked with D at the category of its sort, as
    Rocq checks them against the arity of D alone; the category they give
    enters the signature with the final entry of D.

    An instance [elim_D[s]] of its eliminator is then registered once its
    sort is allowed, by [allows_elimination] of the kernel: a sort of the
    table that the category of D admits, otherwise the refusal
    [RElimSort].  It is registered in stages:
    1. check the generated type of [elim_D[s]] in the signature with D and
       its constructors;
    2. add [elim_D[s]] with that type, without the flag of active
       ι-rules, to a temporary copy of the signature;
    3. there, check both sides of every generated ι-rule against
       [P ū (c_k Δ ā)] in the context of the parameters, motive, methods
       and fields: the eliminator is already a typed constant, but its
       unchecked rules take no part in evaluation and conversion;
    4. only when every check succeeds, register the instance in the main
       signature with the flag; on a rejection or running out of fuel the
       temporary extension is dropped.

    These checks are the local form of [signature_typed] of the kernel's
    PTS.Typing: the types of constants are types, δ-bodies have them, and
    each ι-rule keeps the type of its redex.  The checker itself never
    creates entries: a constant missing from the signature it is given is
    rejected.  Each instance is checked this way when it is generated;
    the general theorem for all descriptions and sorts is an obligation
    (Contracts.v).

    The mode [BypassElim] skips the check of the sort of the motive and
    only it: positivity and the rest are checked.  It registers, say, the
    elimination of a disjunction into Type, which observes which
    constructor built a proof (Data.Logic); its signatures are outside
    the contracts.

    [Unit_0] is the primitive Unit; for ℓ > 0, [data Unit_ℓ : Type_ℓ where
    tt_ℓ : Unit_ℓ] is declared by algorithm 1, its result exactly
    [Type_ℓ]: without cumulativity [Unit : Type₀] cannot stand for it.

    Every run of the checker is logged with the stage it belongs to, in
    the registration monad of Registration, which lies below both
    algorithms and which the compiler of algorithm 2 (Recursion.Compile)
    shares: it logs the sorts of its motives, its δ-constants and its
    defining equations in the same terms.  The monad and the diagnostics
    are exported with this module. *)

From Stdlib Require Import List Bool Arith.
From Stdlib Require String.
From Stdlib Require Import DecimalString.
Import ListNotations.
Import (notations) String.StringSyntax.
Local Open Scope string_scope.
From DepTypes.Common Require Import Result Traced.
From DepTypes.PTS Require Import Syntax Spec Signature Eval Check.
From IndTypes.Elim Require Import Decl Generate.
From IndTypes Require Export Registration.

Local Notation string := String.string.

(** ** Sorts of fields and categories *)

(** A field of sort [s] in a declaration of sort [sD]. *)
Definition within (s sD : sort) : bool :=
  match sD, s with
  | Prp, _ => true
  | Univ i, Prp => true
  | Univ i, Univ k => Nat.leb k i
  | _, _ => false
  end.

(** The category of a declaration of sort [s] whose constructors have
    fields of the sorts [fss]. *)
Definition elim_class_of (s : sort) (fss : list (list sort)) : elim_class :=
  match s, fss with
  | Prp, [] => AllSorts
  | Prp, [ss] => if forallb (sort_eqb Prp) ss then AllSorts else PropOnly
  | Prp, _ => PropOnly
  | _, _ => AllSorts
  end.

Definition with_elim (d : ind_desc) (cls : elim_class) : ind_desc :=
  {| ind_name := ind_name d; ind_params := ind_params d; ind_indices := ind_indices d;
     ind_sort := ind_sort d; ind_elim := cls; ind_ctors := ind_ctors d |}.

(** Whether the registration of an instance checks the sort of its
    motive against the category of D, or bypasses it. *)
Inductive elim_mode : Type := CheckElim | BypassElim.

Section Register.
  Variable Sp : spec.
  Variable fuel : nat.

  (** The fields of the constructor [c] of [d] from position [l] on, in
      the context [G] of the parameters and the earlier fields: each is a
      type of a sort allowed in D.  Their sorts. *)
  Fixpoint check_fields (sg : signature) (d : ind_desc) (c : string) (G : ctx) (l : nat)
      (fs : list field) : R (list sort) :=
    match fs with
    | [] => tret []
    | fd :: fs' =>
        let A := field_type (ind_name d) (length (ind_params d)) l fd in
        let! s := sort_of Sp fuel sg (AtField (ind_name d) c l) G A in
        let! _ := trequire (within s (ind_sort d)) (Refuse (RLevel c l s (ind_sort d))) in
        let! ss := check_fields sg d c (A :: G) (S l) fs' in
        tret (s :: ss)
    end.

  (** The type of every constructor of [d] among [cs], and the sorts of
      its fields. *)
  Fixpoint check_ctors (sg : signature) (d : ind_desc) (cs : list ctor_desc) : R (list (list sort)) :=
    match cs with
    | [] => tret []
    | c :: cs' =>
        let! _ := sort_of Sp fuel sg (AtCtorType (ind_name d) (ctor_name c)) [] (ctor_type d c) in
        let! ss := check_fields sg d (ctor_name c) (rev (ind_params d)) 0 (ctor_fields c) in
        let! fss := check_ctors sg d cs' in
        tret (ss :: fss)
    end.

  (** ** Registration *)

  (** The declaration with its constructors, classified in the [mode] of
      Elim.Decl: [Bypass], the demonstration mode, is outside the
      contract.  The checks run with D at the category of its sort; the
      entry registered has the category of its fields. *)
  Definition declare_ind_with (mode : positivity) (sg : signature) (raw : raw_decl)
    : R (signature * ind_desc) :=
    let D := rd_name raw in
    let! d0 := match classify_decl_with mode raw with Ok d => tret d | Err e => refuse (RClassify e) end in
    let! _ := match sig_ind sg D with Some _ => refuse (RTaken (Ind D)) | None => tret tt end in
    let! sg1 := add sg (EInd d0) in
    let! _ := sort_of Sp fuel sg1 (AtIndType D) [] (ind_type d0) in
    let! fss := check_ctors sg1 d0 (ind_ctors d0) in
    let d := with_elim d0 (elim_class_of (ind_sort d0) fss) in
    let! sg' := add sg (EInd d) in
    tret (sg', d).

  Definition declare_ind : signature -> raw_decl -> R (signature * ind_desc) := declare_ind_with Checked.

  (** Both sides of a rule against its type, in its context. *)
  Definition check_rule (sg : signature) (D : string) (s : sort) (r : iota_rule) : R unit :=
    let! _ := checked (AtRuleLhs D s (rule_ctor r))
                (run_check Sp sg fuel (rule_ctx r) (rule_lhs r) (rule_type r)) in
    checked (AtRuleRhs D s (rule_ctor r)) (run_check Sp sg fuel (rule_ctx r) (rule_rhs r) (rule_type r)).

  (** The instance [elim_D[s]], once its sort is allowed, in the four
      stages; the mode [BypassElim] does not check the sort. *)
  Definition declare_elim_with (em : elim_mode) (sg : signature) (D : string) (s : sort) : R signature :=
    let! d := match sig_ind sg D with Some d => tret d | None => refuse (RUndeclared D) end in
    let! _ := match sig_elim sg D s with Some _ => refuse (RTaken (Elim D s)) | None => tret tt end in
    let! _ := match em with
              | CheckElim => trequire (allows_elimination Sp (ind_elim d) s) (Refuse (RElimSort D s))
              | BypassElim => tret tt
              end in
    let T := elim_type d s in
    let! _ := sort_of Sp fuel sg (AtElimType D s) [] T in
    let! tmp := add sg (EElim D s T false) in
    let! _ := titer (check_rule tmp D s) (iota_rules d s) in
    add sg (EElim D s T true).

  Definition declare_elim : signature -> string -> sort -> R signature := declare_elim_with CheckElim.

  (** The declaration and the instances for the given sorts. *)
  Definition declare_with (mode : positivity) (em : elim_mode) (sg : signature) (raw : raw_decl)
      (sorts : list sort) : R signature :=
    let! r := declare_ind_with mode sg raw in
    tfold (fun sg s => declare_elim_with em sg (rd_name raw) s) (fst r) sorts.

  Definition declare : signature -> raw_decl -> list sort -> R signature := declare_with Checked CheckElim.

  (** The instance, unless it is registered already. *)
  Definition ensure_elim (sg : signature) (D : string) (s : sort) : R signature :=
    match sig_elim sg D s with
    | Some (_, true) => tret sg
    | _ => declare_elim sg D s
    end.

  (** ** [Unit_ℓ] *)

  Definition show_nat (n : nat) : string := NilZero.string_of_uint (Nat.to_uint n).

  Definition unit_name (l : nat) : string := String.append "Unit_" (show_nat l).
  Definition tt_name (l : nat) : string := String.append "tt_" (show_nat l).

  Definition unit_decl (l : nat) : raw_decl := {|
    rd_name := unit_name l; rd_params := []; rd_indices := []; rd_sort := Univ l;
    rd_ctors := [mk_raw_ctor (tt_name l) (Const (Ind (unit_name l)))] |}.

  (** The one-element type at level ℓ and its element. *)
  Definition unit_at (l : nat) : term :=
    match l with 0 => Unit | _ => Const (Ind (unit_name l)) end.
  Definition tt_at (l : nat) : term :=
    match l with 0 => Tt | _ => Const (Ctor (unit_name l) (tt_name l)) end.

  (** [Unit_ℓ], unless it is the primitive one or registered already. *)
  Definition ensure_unit (sg : signature) (l : nat) : R signature :=
    match l with
    | 0 => tret sg
    | _ =>
        match sig_ind sg (unit_name l) with
        | Some _ => tret sg
        | None => let! r := declare_ind sg (unit_decl l) in tret (fst r)
        end
    end.
End Register.

(** ** Entry points *)

Definition declare_checked (S : spec) (fuel : nat) (sg : signature) (raw : raw_decl) (sorts : list sort)
  : list (stage * list event) * registration :=
  run_registration (declare S fuel sg raw sorts).

(** The demonstration mode of Data.Positivity: strict positivity is not
    checked, the rest is. *)
Definition declare_bypassing (S : spec) (fuel : nat) (sg : signature) (raw : raw_decl) (sorts : list sort)
  : list (stage * list event) * registration :=
  run_registration (declare_with S fuel Bypass CheckElim sg raw sorts).

(** The demonstration mode of Data.Logic: the sorts of the motives are
    not checked against the category, the rest is. *)
Definition declare_bypassing_elim (S : spec) (fuel : nat) (sg : signature) (raw : raw_decl)
    (sorts : list sort) : list (stage * list event) * registration :=
  run_registration (declare_with S fuel Checked BypassElim sg raw sorts).

(** ** What a registration guarantees

    Whatever a registration returns has passed its checks, so by the
    soundness of the kernel's checker (PTS.CheckSound) it carries the
    judgments of the annotated kernel PTS.Bidir: the types of the new
    constants are types, every field has a sort allowed in D, the
    category of D is the one of the sorts of its fields, the sort of an
    instance is allowed by it, and both sides of every ι-rule check
    against its type in the signature where the instance has no active
    rules.  The resulting signature is the old one with the new entries.
    The judgments of a declaration hold in the signature where it was
    checked, with D at the category of its sort; the entry registered
    differs from it in the category alone.  For δ-constants, see
    [define_sound] of Registration. *)

From Stdlib Require Import Relations.
From DepTypes.PTS Require Import Reduction NormalOrder Bidir CheckSound.

Section Sound.
  Variable Sp : spec.
  Variable fuel : nat.

  (** ** Declarations *)

  (** The fields, of the sorts [ss]: each is a type of its sort, allowed
      in D, in the context of the parameters and the earlier fields. *)
  Fixpoint fields_typed (sg : signature) (d : ind_desc) (G : ctx) (l : nat) (fs : list field)
      (ss : list sort) : Prop :=
    match fs, ss with
    | [], [] => True
    | fd :: fs', s :: ss' =>
        let A := field_type (ind_name d) (length (ind_params d)) l fd in
        (is_type_of Sp sg G A s /\ within s (ind_sort d) = true) /\
        fields_typed sg d (A :: G) (S l) fs' ss'
    | _, _ => False
    end.

  Lemma check_fields_ok : forall sg d c fs G l log log' ss,
    check_fields Sp fuel sg d c G l fs log = (log', Ok ss) -> fields_typed sg d G l fs ss.
  Proof.
    intros sg d c fs. induction fs as [|fd fs IH]; intros G l log log' ss H.
    - apply tret_ok in H. subst ss. exact I.
    - cbn [check_fields] in H.
      tbind_in H s Hs. apply sort_of_ok in Hs as [_ Hs].
      tbind_in H v Hw. tbind_in H ss' Hss. apply tret_ok in H. subst ss.
      cbn [fields_typed]. split; [ | eapply IH; exact Hss].
      split; [exact Hs | ].
      destruct (within s (ind_sort d)); [reflexivity | discriminate Hw].
  Qed.

  Lemma check_ctors_ok : forall sg d cs log log' fss,
    check_ctors Sp fuel sg d cs log = (log', Ok fss) ->
    Forall2 (fun c ss => (exists s, is_type_of Sp sg [] (ctor_type d c) s) /\
                         fields_typed sg d (rev (ind_params d)) 0 (ctor_fields c) ss) cs fss.
  Proof.
    intros sg d cs. induction cs as [|c cs IH]; intros log log' fss H.
    - apply tret_ok in H. subst fss. constructor.
    - cbn [check_ctors] in H.
      tbind_in H s Hs. apply sort_of_ok in Hs as [_ Hs].
      tbind_in H ss Hss. tbind_in H fss' Hf. apply tret_ok in H. subst fss.
      constructor; [split; [now exists s | eapply check_fields_ok; exact Hss] | eapply IH; exact Hf].
  Qed.

  Theorem declare_ind_sound : forall mode sg raw log log' sg' d,
    declare_ind_with Sp fuel mode sg raw log = (log', Ok (sg', d)) ->
    exists d0 sg1 fss,
      classify_decl_with mode raw = Ok d0 /\ sig_ind sg (rd_name raw) = None /\
      sig_entries sg1 = EInd d0 :: sig_entries sg /\
      (exists s, is_type_of Sp sg1 [] (ind_type d0) s) /\
      Forall2 (fun c ss => (exists s, is_type_of Sp sg1 [] (ctor_type d0 c) s) /\
                           fields_typed sg1 d0 (rev (ind_params d0)) 0 (ctor_fields c) ss)
        (ind_ctors d0) fss /\
      d = with_elim d0 (elim_class_of (ind_sort d0) fss) /\
      sig_entries sg' = EInd d :: sig_entries sg.
  Proof.
    intros mode sg raw log log' sg' d H. unfold declare_ind_with in H.
    tbind_in H d0 Hd.
    destruct (classify_decl_with mode raw) as [d1|e] eqn:Ec; [ | discriminate Hd].
    apply tret_ok in Hd. subst d0.
    tbind_in H v Hf.
    destruct (sig_ind sg (rd_name raw)) eqn:Ef; [discriminate Hf | ].
    tbind_in H sg1 Ha. apply add_ok in Ha.
    tbind_in H s Hs. apply sort_of_ok in Hs as [_ Hs].
    tbind_in H fss Hcs. tbind_in H sg2 H2. apply add_ok in H2. apply tret_ok in H.
    injection H as -> ->.
    exists d1, sg1, fss.
    repeat split; [exact Ha | now exists s | eapply check_ctors_ok; exact Hcs | exact H2].
  Qed.

  (** ** Instances *)

  Theorem declare_elim_sound : forall sg D s log log' sg',
    declare_elim Sp fuel sg D s log = (log', Ok sg') ->
    exists d,
      sig_ind sg D = Some d /\ sig_elim sg D s = None /\
      allows_elimination Sp (ind_elim d) s = true /\
      (exists s', is_type_of Sp sg [] (elim_type d s) s') /\
      (exists tmp,
         sig_entries tmp = EElim D s (elim_type d s) false :: sig_entries sg /\
         forall r, In r (iota_rules d s) ->
           bwf_ctx Sp tmp (rule_ctx r) /\ btype Sp tmp (rule_ctx r) (rule_type r) /\
           chk Sp tmp (rule_ctx r) (rule_lhs r) (rule_type r) /\
           chk Sp tmp (rule_ctx r) (rule_rhs r) (rule_type r)) /\
      sig_entries sg' = EElim D s (elim_type d s) true :: sig_entries sg.
  Proof.
    intros sg D s log log' sg' H. unfold declare_elim, declare_elim_with in H.
    tbind_in H d Hd.
    destruct (sig_ind sg D) as [d0|] eqn:Ed; [ | discriminate Hd].
    apply tret_ok in Hd. subst d0. exists d.
    tbind_in H v Hf.
    destruct (sig_elim sg D s) eqn:Ef; [discriminate Hf | ].
    tbind_in H a Ha.
    assert (Hal : allows_elimination Sp (ind_elim d) s = true)
      by (destruct (allows_elimination Sp (ind_elim d) s); [reflexivity | discriminate Ha]).
    tbind_in H s' Hs. apply sort_of_ok in Hs as [_ Hs].
    tbind_in H tmp Ht. apply add_ok in Ht.
    tbind_in H w Hr. apply add_ok in H.
    split; [reflexivity | split; [reflexivity | split; [exact Hal | split; [now exists s' | split; [ | exact H]]]]].
    exists tmp. split; [exact Ht | ]. intros r Hin.
    apply titer_Forall in Hr. rewrite Forall_forall in Hr.
    destruct (Hr r Hin) as (l1 & l2 & u & Hc). unfold check_rule in Hc.
    tbind_in Hc u1 H1.
    apply checked_ok in H1. apply checked_ok in Hc.
    destruct (run_check_sound _ _ _ _ _ _ _ H1) as (Hctx & Hty & Hl).
    destruct (run_check_sound _ _ _ _ _ _ _ Hc) as (_ & _ & Hrhs).
    repeat split; assumption.
  Qed.

  (** ** What a registration adds

      Its entry and nothing else; read off the theorems above whatever
      else they state. *)

  Corollary declare_ind_extends : forall mode sg raw log log' sg' d,
    declare_ind_with Sp fuel mode sg raw log = (log', Ok (sg', d)) -> sig_entries sg' = EInd d :: sig_entries sg.
  Proof. intros * H. apply declare_ind_sound in H. decompose [ex and] H. assumption. Qed.

  Corollary declare_elim_extends : forall sg D s log log' sg',
    declare_elim Sp fuel sg D s log = (log', Ok sg') ->
    exists d, sig_ind sg D = Some d /\ sig_entries sg' = EElim D s (elim_type d s) true :: sig_entries sg.
  Proof. intros * H. apply declare_elim_sound in H. decompose [ex and] H. eexists; split; eassumption. Qed.
End Sound.
