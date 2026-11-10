(** * Propositions: declarations in Prop and their sorts of elimination

    Algorithm 1 on the hierarchy with Prop, [predicative_prop] of the
    kernel.  A declaration [data D (Δ) : Πθ̄. Prop] takes fields of any
    sort: Prop is impredicative, so [ex] may hold a witness of a type in
    [Type₁], while the same field in a declaration of [Type₀] is refused
    by its level.  Impredicativity lifts only this bound: positivity,
    uniformity and the types of the constructors are checked alike, and a
    negative field of a proposition is refused as before.

    The sorts of the fields give D its category of elimination
    (Elim.Declare, [elim_class_of]):

    | declaration                         | constructors      | fields             | motives in |
    |-------------------------------------|-------------------|--------------------|------------|
    | [True : Prop]                       | [I]               | none               | every sort |
    | [False : Prop]                      | none              |                    | every sort |
    | [eq (A : Type₀) (a : A) : A → Prop] | [refl : eq A a a] | none: [b] is an index | every sort |
    | [and (A B : Prop) : Prop]           | [conj]            | two proofs         | every sort |
    | [AccP (A : Prop) (R) : A → Prop]    | [introP]          | proofs, one of them recursive | every sort |
    | [or (A B : Prop) : Prop]            | two               |                    | Prop only  |
    | [ex (A : Type₀) (P) : Prop]         | [ex_intro]        | a witness in Type₀ | Prop only  |
    | [BoolP : Prop]                      | two               |                    | Prop only  |
    | [ℕ], [sig A P] in [Type₀]           |                   | data and proofs    | every sort |

    An empty or singleton proposition has nothing a proof could tell
    apart: eliminating it into Type computes on no data of the proof, as
    [eq_rect] transports along [refl] and [False_rect] has no case.  A
    proof of [or] or of [BoolP] records which constructor built it, and a
    proof of [ex] its witness; eliminating them into Type would make
    proofs observable, and their erasure unsound.  So the registration
    of [elim_or[Type₀]], [elim_ex[Type₀]] or [elim_BoolP[Type₀]] is
    refused with [RElimSort], while their eliminators into Prop, and
    those of data into Prop, the induction principles, are registered.
    The witness of [ex] stays a proof's: extracting it into Type is
    refused, unlike [fst] of the native Σ, which lives in Type.

    The mode [BypassElim] registers [elim_BoolP[Type₀]] all the same,
    with its type and ι-rules checked.  There the two proofs [trueP] and
    [falseP] of the same proposition are observed as [true] and [false]:
    after erasure both would be □, and nothing could choose the branch.
    Its signatures are outside the contracts. *)

From Stdlib Require Import String List.
Import ListNotations.
From DepTypes.Common Require Import Result Traced.
From DepTypes.PTS Require Import Syntax Named Build Signature Eval Check.
From DepTypes.Configs Require Import Predicative.
From DepTypes.MLTT Require Import Constants.
From IndTypes.Elim Require Import Decl Generate Declare.
From IndTypes.Data Require Import Nat.

Open Scope string_scope.
Open Scope nterm_scope.

Definition logic_fuel : nat := 300.

Definition NProp : nterm := NSrt Prp.

(** The category of D in a signature. *)
Definition category (sg : signature) (D : string) : option elim_class :=
  option_map ind_elim (sig_ind sg D).

(** ** Declarations *)

Definition True_ : nterm := NConst (Ind "True").
Definition I_ : nterm := NConst (Ctor "True" "I").

Definition raw_true : raw_decl := {|
  rd_name := "True"; rd_params := []; rd_indices := []; rd_sort := Prp;
  rd_ctors := [mk_raw_ctor "I" (build [] True_)] |}.

Definition False_ : nterm := NConst (Ind "False").

Definition raw_false : raw_decl := {|
  rd_name := "False"; rd_params := []; rd_indices := []; rd_sort := Prp; rd_ctors := [] |}.

(** The left side [a] is a parameter, the right side an index. *)
Definition Eq (A a b : nterm) : nterm := NConst (Ind "eq") A a b.
Definition refl (A a : nterm) : nterm := NConst (Ctor "eq" "refl") A a.

Definition raw_eq : raw_decl := {|
  rd_name := "eq"; rd_params := [Srt (Univ 0); build ["A"] "A"]; rd_indices := [build ["a"; "A"] "A"];
  rd_sort := Prp;
  rd_ctors := [mk_raw_ctor "refl" (build ["a"; "A"] (Eq "A" "a" "a"))] |}.

Definition And (A B : nterm) : nterm := NConst (Ind "and") A B.

Definition raw_and : raw_decl := {|
  rd_name := "and"; rd_params := [Srt Prp; Srt Prp]; rd_indices := []; rd_sort := Prp;
  rd_ctors := [mk_raw_ctor "conj" (build ["B"; "A"] ("A" ~> "B" ~> And "A" "B"))] |}.

Definition Or (A B : nterm) : nterm := NConst (Ind "or") A B.

Definition raw_or : raw_decl := {|
  rd_name := "or"; rd_params := [Srt Prp; Srt Prp]; rd_indices := []; rd_sort := Prp;
  rd_ctors := [mk_raw_ctor "or_introl" (build ["B"; "A"] ("A" ~> Or "A" "B"));
               mk_raw_ctor "or_intror" (build ["B"; "A"] ("B" ~> Or "A" "B"))] |}.

(** [ex A P] over a type [A] of the level [i]: [ex] at [Type₀], [ex1] at
    [Type₁], whose witness may itself be a type. *)
Definition raw_ex_at (D c : string) (i : nat) : raw_decl := {|
  rd_name := D; rd_params := [Srt (Univ i); build ["A"] ("A" ~> NProp)]; rd_indices := []; rd_sort := Prp;
  rd_ctors := [mk_raw_ctor c (build ["P"; "A"] (Π "x" : "A", "P" "x" ~> NConst (Ind D) "A" "P"))] |}.

Definition raw_ex : raw_decl := raw_ex_at "ex" "ex_intro" 0.
Definition raw_ex1 : raw_decl := raw_ex_at "ex1" "ex1_intro" 1.

(** Accessibility over a proposition [A]: the parameter [x] of Rocq's
    [Acc] varies in the recursive field, so it is an index here and the
    constructor binds it as a field; with [A : Prop] that field is a
    proof, and the declaration is a singleton. *)
Definition AccP (A R x : nterm) : nterm := NConst (Ind "AccP") A R x.

Definition raw_accp : raw_decl := {|
  rd_name := "AccP"; rd_params := [Srt Prp; build ["A"] ("A" ~> "A" ~> NProp)];
  rd_indices := [build ["R"; "A"] "A"]; rd_sort := Prp;
  rd_ctors := [mk_raw_ctor "introP"
                 (build ["R"; "A"] (Π "x" : "A", (Π "y" : "A", "R" "y" "x" ~> AccP "A" "R" "y") ~>
                                     AccP "A" "R" "x"))] |}.

Definition BoolP : nterm := NConst (Ind "BoolP").
Definition trueP : nterm := NConst (Ctor "BoolP" "trueP").
Definition falseP : nterm := NConst (Ctor "BoolP" "falseP").

Definition raw_boolp : raw_decl := {|
  rd_name := "BoolP"; rd_params := []; rd_indices := []; rd_sort := Prp;
  rd_ctors := [mk_raw_ctor "trueP" (build [] BoolP); mk_raw_ctor "falseP" (build [] BoolP)] |}.

(** Data with a proof: [sig A P : Type₀] with [exist : Πx:A. P x → sig A P]. *)
Definition raw_sig : raw_decl := {|
  rd_name := "sig"; rd_params := [Srt (Univ 0); build ["A"] ("A" ~> NProp)]; rd_indices := [];
  rd_sort := Univ 0;
  rd_ctors := [mk_raw_ctor "exist" (build ["P"; "A"] (Π "x" : "A", "P" "x" ~> NConst (Ind "sig") "A" "P"))] |}.

(** The shape of [ex1] in [Type₀]: its witness in [Type₁] is above it. *)
Definition raw_sigT0 : raw_decl := {|
  rd_name := "sigT0"; rd_params := [Srt (Univ 1); build ["A"] ("A" ~> NProp)]; rd_indices := [];
  rd_sort := Univ 0;
  rd_ctors := [mk_raw_ctor "existT0"
                 (build ["P"; "A"] (Π "x" : "A", "P" "x" ~> NConst (Ind "sigT0") "A" "P"))] |}.

(** A negative proposition, [mkBad : (BadP → False) → BadP]. *)
Definition BadP : nterm := NConst (Ind "BadP").

Definition raw_badp : raw_decl := {|
  rd_name := "BadP"; rd_params := []; rd_indices := []; rd_sort := Prp;
  rd_ctors := [mk_raw_ctor "mkBad" (build [] ((BadP ~> False_) ~> BadP))] |}.

(** ** Registration *)

(** The logic, each declaration with the instances its category allows:
    into Prop always, into [Type₀] for the empty and singleton ones. *)
Definition logic_run : list (stage * list event) * registration :=
  run_registration (
    let! s1 := declare predicative_prop logic_fuel ∅ raw_true [Prp; Univ 0] in
    let! s2 := declare predicative_prop logic_fuel s1 raw_false [Prp; Univ 0] in
    let! s3 := declare predicative_prop logic_fuel s2 raw_eq [Prp; Univ 0] in
    let! s4 := declare predicative_prop logic_fuel s3 raw_and [Prp; Univ 0] in
    let! s5 := declare predicative_prop logic_fuel s4 raw_or [Prp] in
    let! s6 := declare predicative_prop logic_fuel s5 raw_ex [Prp] in
    declare predicative_prop logic_fuel s6 raw_accp [Prp; Univ 0]).

Definition sg_logic : signature := sg_of logic_run.

Example categories :
  map (category sg_logic) ["True"; "False"; "eq"; "and"; "AccP"; "or"; "ex"]
  = [Some AllSorts; Some AllSorts; Some AllSorts; Some AllSorts; Some AllSorts; Some PropOnly; Some PropOnly].
Proof. vm_compute. reflexivity. Qed.

(** Every instance registered, with its ι-rules checked and active. *)
Example instances_registered :
  map (fun '(D, s) => match sig_elim sg_logic D s with Some (_, true) => true | _ => false end)
    [("True", Prp); ("True", Univ 0); ("False", Prp); ("False", Univ 0); ("eq", Prp); ("eq", Univ 0);
     ("and", Prp); ("and", Univ 0); ("or", Prp); ("ex", Prp); ("AccP", Prp); ("AccP", Univ 0)]
  = repeat true 12.
Proof. vm_compute. reflexivity. Qed.

(** Classification gives a proposition the category of its sort; the
    registration lifts [eq] by the sorts of its fields, of which it has
    none: the index is no field. *)
Example eq_lifted :
  option_map ind_elim (match classify_decl raw_eq with Ok d => Some d | Err _ => None end) = Some PropOnly /\
  category sg_logic "eq" = Some AllSorts.
Proof. split; vm_compute; reflexivity. Qed.

(** [elim_eq[Type₀]] is the dependent eliminator J, Rocq's [eq_rect]
    with the dependency on the proof. *)
Example eq_rect_type :
  option_map (fun d => elim_type d (Univ 0)) (sig_ind sg_logic "eq")
  = Some (build [] (Π "A" : Type@ 0, Π "a" : "A",
                    Π "P" : (Π "b" : "A", Eq "A" "a" "b" ~> Type@ 0),
                    "P" "a" (refl "A" "a") ~> Π "b" : "A", Π "e" : Eq "A" "a" "b", "P" "b" "e")).
Proof. vm_compute. reflexivity. Qed.

(** The induction principle: data eliminates into Prop as well. *)
Example nat_induction :
  elim_type nat_desc Prp =
    build [] (Π "P" : (Nat ~> NProp), "P" zero ~> (Π "n" : Nat, "P" "n" ~> "P" (succ "n")) ~>
              Π "n" : Nat, "P" "n") /\
  option_map (fun sg => sig_elim sg "Nat" Prp)
    (registered (declare_checked predicative_prop logic_fuel ∅ raw_nat [Prp; Univ 0]))
  = Some (Some (elim_type nat_desc Prp, true)).
Proof. split; vm_compute; reflexivity. Qed.

(** ** Refusals *)

(** [or] and [ex] into Type: a proof would be observed. *)
Example large_elimination_refused :
  refusal (run_registration (declare_elim predicative_prop logic_fuel sg_logic "or" (Univ 0)))
    = Some (RElimSort "or" (Univ 0)) /\
  refusal (run_registration (declare_elim predicative_prop logic_fuel sg_logic "ex" (Univ 0)))
    = Some (RElimSort "ex" (Univ 0)).
Proof. split; vm_compute; reflexivity. Qed.

(** The kernel's [match] asks the same [allows_elimination]: on [or] a
    match into Prop, the commutativity of [or], is accepted, and one into
    Type₀ is refused by the category the registration computed. *)
Definition or_ctx : list (string * nterm) := [("p", Or "A" "B"); ("B", NProp); ("A", NProp)].

Definition or_comm : nterm :=
  NCase "or" Prp (λ "_", Or "B" "A") "p"
    [λ "a", NConst (Ctor "or" "or_intror") "B" "A" "a"; λ "b", NConst (Ctor "or" "or_introl") "B" "A" "b"].

Definition or_to_bool : nterm := NCase "or" (Univ 0) (λ "_", NBool) "p" [λ "a", NTrue; λ "b", NFalse].

Example match_on_or :
  snd (run_check predicative_prop sg_logic logic_fuel (in_ctx or_ctx) (term_in or_ctx or_comm)
         (term_in or_ctx (Or "B" "A"))) = Accepted tt /\
  snd (run_infer predicative_prop sg_logic logic_fuel (in_ctx or_ctx) (term_in or_ctx or_to_bool))
  = Rejected (EElimSort "or" (Univ 0)).
Proof. vm_compute. split; reflexivity. Qed.

(** [BoolP] is registered and eliminated into Prop; into Type it is
    refused. *)
Example boolp_into_prop_only :
  category (sg_of (declare_checked predicative_prop logic_fuel ∅ raw_boolp [Prp])) "BoolP" = Some PropOnly /\
  refusal (declare_checked predicative_prop logic_fuel ∅ raw_boolp [Prp; Univ 0])
    = Some (RElimSort "BoolP" (Univ 0)).
Proof. split; vm_compute; reflexivity. Qed.

(** The witness of [ex1] lives in [Type₁]: the proposition is registered,
    the extraction of its witness into [Type₁] is refused.  The same
    shape in [Type₀] is refused by the level of the witness. *)
Definition sg_ex1 : signature := sg_of (declare_checked predicative_prop logic_fuel ∅ raw_ex1 [Prp]).

Example big_witness :
  category sg_ex1 "ex1" = Some PropOnly /\
  refusal (run_registration (declare_elim predicative_prop logic_fuel sg_ex1 "ex1" (Univ 1)))
    = Some (RElimSort "ex1" (Univ 1)) /\
  refusal (declare_checked predicative_prop logic_fuel ∅ raw_sigT0 [])
    = Some (RLevel "existT0" 0 (Univ 1) (Univ 0)).
Proof. repeat split; vm_compute; reflexivity. Qed.

(** The native Σ lives in Type: its first projection is the witness, a
    type of [Type₀] taken out of [ΣX:Type₀. P X]. *)
Definition sigma_ctx : list (string * nterm) :=
  [("s", Σ "X" : Type@ 0, "P" "X"); ("P", Type@ 0 ~> NProp)].

Example sigma_witness :
  snd (run_infer predicative_prop ∅ logic_fuel (in_ctx sigma_ctx) (term_in sigma_ctx (NFst "s")))
  = Accepted (Srt (Univ 0)).
Proof. vm_compute. reflexivity. Qed.

(** A proof as a field of data: [sig A P] is registered in [Type₀] and
    eliminates into every sort. *)
Example proof_field_in_data :
  category (sg_of (declare_checked predicative_prop logic_fuel ∅ raw_sig [Univ 0; Prp])) "sig"
  = Some AllSorts.
Proof. vm_compute. reflexivity. Qed.

(** Impredicativity does not lift positivity; and without Prop in the
    table no proposition is declared. *)
Example prop_checks_kept :
  refusal (declare_checked predicative_prop logic_fuel ∅ raw_badp [])
    = Some (RClassify (ENegative "mkBad" 0 (build [] (BadP ~> False_)))) /\
  refusal (declare_checked predicative logic_fuel ∅ raw_true [])
    = Some (RRejected (AtIndType "True") (ENotInSystem Prp)).
Proof. split; vm_compute; reflexivity. Qed.

(** ** Bypassing the restriction *)

(** [BoolP] with [elim_BoolP[Type₀]], its type and ι-rules checked. *)
Definition boolp_bypassed : list (stage * list event) * registration :=
  declare_bypassing_elim predicative_prop logic_fuel ∅ raw_boolp [Univ 0].

Definition sg_bypass : signature := sg_of boolp_bypassed.

(** [observe_proof p := elim_BoolP[Type₀] (λ_. Bool) true false p]. *)
Definition observe_proof (p : nterm) : nterm :=
  NConst (Elim "BoolP" (Univ 0)) (λ "_", NBool) NTrue NFalse p.

(** Two proofs of one proposition, told apart. *)
Example proofs_observed :
  map (fun p => snd (run_check predicative_prop sg_bypass logic_fuel [] (build [] (observe_proof p)) Bool))
    [trueP; falseP] = [Accepted tt; Accepted tt] /\
  map (fun p => normalize sg_bypass logic_fuel (build [] (observe_proof p))) [trueP; falseP]
    = [NormalForm BTrue; NormalForm BFalse].
Proof. split; vm_compute; reflexivity. Qed.

(** Without the bypass the instance is not there. *)
Example observation_needs_the_bypass :
  snd (run_check predicative_prop (sg_of (declare_checked predicative_prop logic_fuel ∅ raw_boolp [Prp]))
         logic_fuel [] (build [] (observe_proof trueP)) Bool)
  = Rejected (EUnknownConst (Elim "BoolP" (Univ 0))).
Proof. vm_compute. reflexivity. Qed.
