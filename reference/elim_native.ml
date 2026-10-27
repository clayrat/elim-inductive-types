(* Algorithm 1, native: the classification of raw declarations
   (Elim/Decl.v), the generated eliminators and ι-rules (Elim/Generate.v)
   and staged registration (Elim/Declare.v), on top of the kernel's native
   reference.  Written by hand from the lecture; the differential test
   compares it with the extract. *)

open Pts_native

let ( let* ) = Result.bind
let require ok error = if ok then Ok () else Error error

let rec map_ok f = function
  | [] -> Ok []
  | x :: xs -> let* y = f x in let* ys = map_ok f xs in Ok (y :: ys)

let rec iter_ok f = function
  | [] -> Ok ()
  | x :: xs -> let* () = f x in iter_ok f xs

let rec fold_ok f acc = function
  | [] -> Ok acc
  | x :: xs -> let* acc = f acc x in fold_ok f acc xs

(* ** Classification *)

type raw_ctor = { rc_name : string; rc_type : term }

type raw_decl = {
  rd_name : string;
  rd_params : term list;
  rd_indices : term list;
  rd_level : int;
  rd_ctors : raw_ctor list;
}

type site = SField of int | SResult

type decl_error =
  | EOpenParams | EOpenIndices | ESelfReference
  | EOpenCtor of string | EDuplicateCtor of string
  | ENegative of string * int * term
  | ENonStrict of string * int * term
  | ENested of string * int * term
  | ENotFamily of string * term
  | EArity of string * site * term
  | ENonUniform of string * site * term
  | EInIndices of string * site * term

(* Whether D, one of its constructors or an instance of its eliminator
   occurs in a term. *)
let rec mentions name = function
  | Const (Ind d | Ctor (d, _) | Elim (d, _)) -> d = name
  | Const (Def _) | Srt _ | Var _ | Void | Unit | Tt | Bool | BTrue | BFalse -> false
  | Pi (a, b) | Sigma (a, b) | App (a, b) | Ann (a, b) | ElimVoid (a, b) | Pair (a, b) ->
      mentions name a || mentions name b
  | Lam b | Fst b | Snd b -> mentions name b
  | ElimUnit (c, branch, u) -> mentions name c || mentions name branch || mentions name u
  | ElimBool (c, yes, no, b) ->
      mentions name c || mentions name yes || mentions name no || mentions name b

let free_of name t = not (mentions name t)

let family_spine name t = match spine t with Const (Ind d), _ -> d = name | _ -> false

let rec split_pis = function
  | Pi (a, b) -> let domains, body = split_pis b in (a :: domains, body)
  | t -> ([], t)

(* Where D occurs in a type outside the grammar: as the head of a spine at
   a negative position, or anywhere but the head of a spine.  A product
   flips the polarity of its domain. *)
type occurrences = { negative : bool; nested : bool }

let rec occurrences name positive = function
  | Pi (a, b) ->
      let o = occurrences name (not positive) a and o' = occurrences name positive b in
      { negative = o.negative || o'.negative; nested = o.nested || o'.nested }
  | t when family_spine name t ->
      { negative = not positive; nested = List.exists (mentions name) (snd (spine t)) }
  | t -> { negative = false; nested = mentions name t }

let rec first_duplicate = function
  | [] -> None
  | x :: rest -> if List.mem x rest then Some x else first_duplicate rest

let classify_decl_with bypass d =
  let name = d.rd_name in
  let p = List.length d.rd_params and q = List.length d.rd_indices in
  (* The indices of a spine of D [k] binders above the parameters: D is
     applied to the parameters themselves, then to q terms free of D. *)
  let family_args c site k t =
    let args = snd (spine t) in
    let* () = require (List.length args = p + q) (EArity (c, site, t)) in
    let* () = require (take p args = vars k p) (ENonUniform (c, site, t)) in
    let indices = drop p args in
    let* () = require (List.for_all (free_of name) indices) (EInIndices (c, site, t)) in
    Ok indices
  in
  (* A field free of D is non-recursive; [Πȳ:B̄. D Δ v̄] with B̄ free of D
     is recursive; anything else is refused by where D occurs. *)
  let classify_field c l a =
    if free_of name a then Ok (FArg a) else
    let domains, body = split_pis a in
    if List.for_all (free_of name) domains && family_spine name body then
      let* indices = family_args c (SField l) (List.length domains + l) body in
      Ok (FRec (domains, indices))
    else if bypass then Ok (FArg a)
    else
      let o = occurrences name true a in
      Error (if o.negative then ENegative (c, l, a)
             else if o.nested then ENested (c, l, a)
             else ENonStrict (c, l, a))
  in
  let rec classify_con c l = function
    | Pi (a, b) ->
        let* field = classify_field c l a in
        let* fields, indices = classify_con c (l + 1) b in
        Ok (field :: fields, indices)
    | t ->
        let* () = require (family_spine name t) (ENotFamily (c, t)) in
        let* indices = family_args c SResult l t in
        Ok ([], indices)
  in
  let classify_ctor rc =
    let* () = require (closed_above p rc.rc_type) (EOpenCtor rc.rc_name) in
    let* fields, indices = classify_con rc.rc_name 0 rc.rc_type in
    Ok { ctor_name = rc.rc_name; ctor_fields = fields; ctor_indices = indices }
  in
  let* () = require (telescope_closed 0 d.rd_params) EOpenParams in
  let* () = require (telescope_closed p d.rd_indices) EOpenIndices in
  let* () = require (List.for_all (free_of name) (d.rd_params @ d.rd_indices)) ESelfReference in
  let* ctors = map_ok classify_ctor d.rd_ctors in
  let* () = match first_duplicate (List.map (fun c -> c.ctor_name) ctors) with
    | Some c -> Error (EDuplicateCtor c)
    | None -> Ok ()
  in
  Ok { ind_name = name; ind_params = d.rd_params; ind_indices = d.rd_indices;
       ind_level = d.rd_level; ind_ctors = ctors }

let classify_decl = classify_decl_with false

(* ** Generation *)

let rename r t = subst (fun n -> Var (r n)) t
let up_ren r n = if n = 0 then 0 else r (n - 1) + 1
let rec upn_ren m r = if m = 0 then r else up_ren (upn_ren (m - 1) r)

(* Each entry of a telescope under the entries before it. *)
let rec rename_tele r = function
  | [] -> []
  | a :: rest -> rename r a :: rename_tele (up_ren r) rest

(* Entries independent of each other: the i-th lifted past the i before it. *)
let lifted i tys = List.mapi (fun k a -> lift (i + k) a) tys

(* From the context of the parameters and the earlier fields into the
   telescope of a method: [positions] of the earlier fields among its b
   binders so far, innermost first; a parameter lies past them all and
   the motive. *)
let transport positions b n =
  match List.nth_opt positions n with
  | Some position -> b - 1 - position
  | None -> n - List.length positions + b + 1

let motive_type d j =
  let p = List.length d.ind_params and q = List.length d.ind_indices in
  pis d.ind_indices (Pi (apps (Const (Ind d.ind_name)) (vars q p @ vars 0 q), Srt (Univ j)))

(* [Πȳ:B̄. P v̄ (r ȳ)] for the recursive field just bound: [r] renames
   the domains and indices to the b binders before the field. *)
let hyp_type r b domains indices =
  let m = List.length domains in
  let r' n = r n + 1 in
  pis (rename_tele r' domains)
    (apps (Var (b + 1 + m)) (List.map (rename (upn_ren m r')) indices @ [apps (Var m) (vars 0 m)]))

(* Each field, a recursive one followed by its hypothesis, then
   [P ū (c Δ ā)]. *)
let method_type d c =
  let name = d.ind_name and p = List.length d.ind_params in
  let rec go positions b l = function
    | [] ->
        let fields = List.rev_map (fun position -> Var (b - 1 - position)) positions in
        apps (Var b)
          (List.map (rename (transport positions b)) c.ctor_indices
           @ [apps (Const (Ctor (name, c.ctor_name))) (vars (b + 1) p @ fields)])
    | fd :: rest ->
        let r = transport positions b in
        let field = rename r (field_type name p l fd) in
        (match fd with
         | FArg _ -> Pi (field, go (b :: positions) (b + 1) (l + 1) rest)
         | FRec (domains, indices) ->
             Pi (field, Pi (hyp_type r b domains indices, go (b :: positions) (b + 2) (l + 1) rest)))
  in
  go [] 0 0 c.ctor_fields

let methods d = lifted 0 (List.map (method_type d) d.ind_ctors)

(* [Π(Δ). ΠP. M₁ → ⋯ → M_k → Πθ̄. Πx:D Δ θ̄. P θ̄ x]. *)
let elim_type d j =
  let p = List.length d.ind_params and q = List.length d.ind_indices in
  let k = List.length d.ind_ctors in
  pis d.ind_params
    (Pi (motive_type d j,
         pis (methods d)
           (pis (rename_tele (fun n -> n + k + 1) d.ind_indices)
              (Pi (apps (Const (Ind d.ind_name)) (vars (q + k + 1) p @ vars 0 q),
                   apps (Var (k + q + 1)) (vars 1 q @ [Var 0]))))))

type iota_rule = {
  rule_ctor : string;
  rule_ctx : ctx;
  rule_lhs : term;
  rule_rhs : term;
  rule_type : term;
}

(* [elim_D[j] Δ P m̄ ū (c Δ ā) ↝ m_c args(ā, ih̄)] against [P ū (c Δ ā)],
   in the context of the parameters, P, the methods and the fields; the
   arguments are the kernel's own. *)
let iota_rules d j =
  let name = d.ind_name in
  let p = List.length d.ind_params and k = List.length d.ind_ctors in
  let past_methods n = n + k + 1 in
  List.mapi (fun i c ->
      let n = List.length c.ctor_fields in
      let params = vars (n + k + 1) p in
      let pre = params @ [Var (n + k)] @ vars n k in
      let indices = List.map (rename (upn_ren n past_methods)) c.ctor_indices in
      let obj = apps (Const (Ctor (name, c.ctor_name))) (params @ vars 0 n) in
      { rule_ctor = c.ctor_name;
        rule_ctx = List.rev (rename_tele past_methods (List.mapi (field_type name p) c.ctor_fields))
                   @ List.rev (methods d) @ [motive_type d j] @ List.rev d.ind_params;
        rule_lhs = apps (Const (Elim (name, j))) (pre @ indices @ [obj]);
        rule_rhs = apps (Var (n + k - 1 - i))
                     (method_args name j pre (List.rev params) c.ctor_fields (vars 0 n));
        rule_type = apps (Var (n + k)) (indices @ [obj]) })
    d.ind_ctors

(* ** Registration *)

type stage =
  | AtIndType of string
  | AtCtorType of string * string
  | AtField of string * string * int
  | AtElimType of string * int
  | AtRuleLhs of string * int * string
  | AtRuleRhs of string * int * string
  | AtDefType of string
  | AtDefBody of string

type reg_error =
  | RClassify of decl_error
  | RTaken of gref
  | RUndeclared of string
  | RLevel of string * int * sort * int
  | RNotAType of stage * term
  | RRejected of stage * error
  | ROpen

type failure = Refuse of reg_error | NoFuelAt of stage * term

type registration =
  | Registered of signature
  | Refused of reg_error
  | OutOfFuelAt of stage * term

type log = (stage * event list) list

(* Every checker run of a registration goes to its log with the stage, as
   the run of the native checker keeps its events in a queue. *)
type registrar = { spec : spec; fuel : int; log : (stage * event list) Queue.t }

let run_steps spec fuel task =
  let r = { spec; fuel; log = Queue.create () } in
  let result = task r in
  (List.of_seq (Queue.to_seq r.log), result)

let run spec fuel task =
  let log, result = run_steps spec fuel task in
  (log, match result with
        | Ok sg -> Registered sg
        | Error (Refuse e) -> Refused e
        | Error (NoFuelAt (st, t)) -> OutOfFuelAt (st, t))

let refuse e = Error (Refuse e)

let add sg entry = match sig_add sg entry with Some sg -> Ok sg | None -> refuse ROpen

(* A checker run at a stage: its events go to the log, its answer becomes
   the value, the refusal or the lack of fuel of the stage. *)
let checked r st (events, answer) =
  Queue.add (st, events) r.log;
  match answer with
  | Accepted a -> Ok a
  | Rejected e -> refuse (RRejected (st, e))
  | Undecided t -> Error (NoFuelAt (st, t))

(* [a] is a type in [gamma]: its type unfolds to a sort. *)
let sort_of r sg st gamma a =
  let* ty = checked r st (run_infer ~sg r.spec r.fuel gamma a) in
  match whnf ~sg r.fuel ty with
  | HeadForm (Srt s) -> Ok s
  | HeadForm other -> refuse (RNotAType (st, other))
  | HeadOutOfFuel _ -> Error (NoFuelAt (st, a))

let within s level = match s with Univ i -> i <= level | _ -> false

(* Each field is a type of level at most that of D, in the context of the
   parameters and the earlier fields. *)
let rec check_fields r sg d c gamma l = function
  | [] -> Ok ()
  | fd :: rest ->
      let a = field_type d.ind_name (List.length d.ind_params) l fd in
      let* s = sort_of r sg (AtField (d.ind_name, c, l)) gamma a in
      let* () = if within s d.ind_level then Ok () else refuse (RLevel (c, l, s, d.ind_level)) in
      check_fields r sg d c (a :: gamma) (l + 1) rest

let declare_ind_with r bypass sg raw =
  let name = raw.rd_name in
  let* d = Result.map_error (fun e -> Refuse (RClassify e)) (classify_decl_with bypass raw) in
  let* () = if Option.is_some (find_ind sg name) then refuse (RTaken (Ind name)) else Ok () in
  let* sg1 = add sg (EInd d) in
  let* _ = sort_of r sg1 (AtIndType name) [] (ind_type d) in
  let* () = iter_ok (fun c ->
      let* _ = sort_of r sg1 (AtCtorType (name, c.ctor_name)) [] (ctor_type d c) in
      check_fields r sg1 d c.ctor_name (List.rev d.ind_params) 0 c.ctor_fields)
    d.ind_ctors in
  Ok (sg1, d)

let check_rule r sg name j rule =
  let* () = checked r (AtRuleLhs (name, j, rule.rule_ctor))
      (run_check ~sg r.spec r.fuel rule.rule_ctx rule.rule_lhs rule.rule_type) in
  checked r (AtRuleRhs (name, j, rule.rule_ctor))
    (run_check ~sg r.spec r.fuel rule.rule_ctx rule.rule_rhs rule.rule_type)

(* The type of the instance; its rules, in a signature where it has none
   active; the instance with active rules. *)
let declare_elim r sg name j =
  let* d = match find_ind sg name with Some d -> Ok d | None -> refuse (RUndeclared name) in
  let* () = if Option.is_some (find_elim sg name j) then refuse (RTaken (Elim (name, j))) else Ok () in
  let ty = elim_type d j in
  let* _ = sort_of r sg (AtElimType (name, j)) [] ty in
  let* tmp = add sg (EElim (name, j, ty, false)) in
  let* () = iter_ok (check_rule r tmp name j) (iota_rules d j) in
  add sg (EElim (name, j, ty, true))

let declare_with r bypass sg raw levels =
  let* sg, _ = declare_ind_with r bypass sg raw in
  fold_ok (fun sg j -> declare_elim r sg raw.rd_name j) sg levels

let declare r = declare_with r false

let ensure_elim r sg name j =
  match find_elim sg name j with
  | Some (_, true) -> Ok sg
  | _ -> declare_elim r sg name j

(* A δ-constant, checked in the signature without it. *)
let define r sg f ty body =
  let* () = if Option.is_some (find_def sg f) then refuse (RTaken (Def f)) else Ok () in
  let* _ = sort_of r sg (AtDefType f) [] ty in
  let* () = checked r (AtDefBody f) (run_check ~sg r.spec r.fuel [] body ty) in
  add sg (EDef (f, ty, body))

(* [Unit_ℓ]: the primitive at level 0, a declaration above. *)
let unit_name l = "Unit_" ^ string_of_int l
let tt_name l = "tt_" ^ string_of_int l

let unit_decl l = {
  rd_name = unit_name l; rd_params = []; rd_indices = []; rd_level = l;
  rd_ctors = [ { rc_name = tt_name l; rc_type = Const (Ind (unit_name l)) } ] }

let unit_at l = if l = 0 then Unit else Const (Ind (unit_name l))
let tt_at l = if l = 0 then Tt else Const (Ctor (unit_name l, tt_name l))

let ensure_unit r sg l =
  if l = 0 || Option.is_some (find_ind sg (unit_name l)) then Ok sg
  else let* sg, _ = declare_ind_with r false sg (unit_decl l) in Ok sg

let declare_checked spec fuel sg raw levels = run spec fuel (fun r -> declare r sg raw levels)
let declare_bypassing spec fuel sg raw levels = run spec fuel (fun r -> declare_with r true sg raw levels)
let define_checked spec fuel sg f ty body = run spec fuel (fun r -> define r sg f ty body)
