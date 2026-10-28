(* Algorithm 2, native: the history of results (Recursion/Below.v), the
   elaboration of case trees (Recursion/CaseTree.v) and the compiler of
   structural recursion through it (Recursion/Compile.v), on top of the
   native algorithm 1 and the kernel's native reference.  Written by hand
   from the lecture; the differential test compares it with the extract.

   Indices and levels are natural numbers in Rocq, where subtraction
   stops at 0, and a missing element of a list has a default.  [-!],
   [nth_or] and the truncating [combine] do the same where a term or a
   description given as input, or the caller of an exported function,
   decides the bound; where the code itself guarantees it, the
   subtraction is plain and a lookup that cannot miss raises. *)

open Pts_native
open Telescope_native
open Method_layout_native
open Common_native
open Diagnostics_native
module E = Elim_native
module Reg = Registration_native
module L = Looping

let ( -! ) a b = max 0 (a - b)

(* Rocq's [combine]: the pairs up to the shorter list. *)
let rec combine xs ys = match xs, ys with x :: xs, y :: ys -> (x, y) :: combine xs ys | _ -> []

(* Rocq's [nth i l default]. *)
let nth_or default l i = Option.value (List.nth_opt l i) ~default

(* ** Terms *)

let times a b = Sigma (a, lift 1 b)

(* Whether the variable [i] occurs free. *)
let rec occurs i = function
  | Var n -> n = i
  | Srt _ | Void | Unit | Tt | Bool | BTrue | BFalse | Const _ -> false
  | Pi (a, b) | Sigma (a, b) -> occurs i a || occurs (i + 1) b
  | Lam b -> occurs (i + 1) b
  | Fst p | Snd p -> occurs i p
  | App (a, b) | Ann (a, b) | ElimVoid (a, b) | Pair (a, b) -> occurs i a || occurs i b
  | ElimUnit (c, m, u) -> occurs i c || occurs i m || occurs i u
  | ElimBool (c, x, y, b) -> occurs i c || occurs i x || occurs i y || occurs i b

(* ** The history *)

let below_name d j = "Below_" ^ d ^ "_" ^ string_of_int j
let build_name d j = "build_" ^ d ^ "_" ^ string_of_int j
let recbelow_name d j = "recBelow_" ^ d ^ "_" ^ string_of_int j

(* The level of the history of D for a motive in [Type_j]. *)
let history_level d j = max d.ind_level j

(* Tuples at the level ℓ: [Unit_ℓ] when empty, a single component alone,
   more nested to the right. *)
let rec tuple_type l = function
  | [] -> E.unit_at l
  | [ a ] -> a
  | a :: rest -> times a (tuple_type l rest)

let rec tuple l = function
  | [] -> E.tt_at l
  | [ t ] -> t
  | t :: rest -> Pair (t, tuple l rest)

(* [Πθ̄. Πx:D Δ θ̄. F], [e] binders between the parameters and θ̄. *)
let over_family d e f =
  let p = nparams d and q = nindices d in
  pis (rename_tele (fun n -> n + e) d.ind_indices)
    (Pi (apps (Const (Ind d.ind_name)) (vars (q + e) p @ vars 0 q), f))

(* [P θ̄ x] and [Below_D Δ P θ̄ x]: the parameters at [params], P at
   [motive] and θ̄ x at [base]. *)
let motive_at_base d ~motive ~base = apps (Var motive) (vars base (nindices d + 1))

let below_at d j ~params ~motive ~base =
  apps (Const (Def (below_name d.ind_name j)))
    (vars params (nparams d) @ [ Var motive ] @ vars base (nindices d + 1))

(* [Π(Δ). ΠP:(Πθ̄. D Δ θ̄ → Type_j). Πθ̄. D Δ θ̄ → Type_ℓ]. *)
let below_type d j =
  pis d.ind_params (Pi (E.motive_type d j, over_family d 1 (Srt (Univ (history_level d j)))))

(* [Πȳ:B̄. P v̄ (r ȳ) × ih ȳ] for a recursive field [r] at [bl], after the
   earlier fields at [rbs], with its hypothesis [ih], among [b] binders
   after the parameters and P. *)
let component b bl rbs domains indices =
  let m = List.length domains in
  let r = transport rbs b in
  pis (rename_tele r domains)
    (times
       (apps (Var (b + m))
          (List.map (rename (upn_ren m r)) indices @ [ apps (Var (b - 1 - bl + m)) (vars 0 m) ]))
       (apps (Var (b - 2 - bl + m)) (vars 0 m)))

(* The tuple of the components, built in the accumulator innermost
   first. *)
let below_method l c =
  let b = nbinders c.ctor_fields in
  let cs, _, _ =
    fold_slots (fun cs fd _ _ bl rbs ->
        match fd with
        | FRec (domains, indices) -> component b bl rbs domains indices :: cs
        | FArg _ -> cs)
      [] c.ctor_fields
  in
  lams b (tuple_type l (List.rev cs))

(* [λΔ P. elim_D[ℓ+1] Δ (λθ̄ x. Type_ℓ) m̄]. *)
let below_body d j =
  let p = nparams d and q = nindices d and l = history_level d j in
  lams p (Lam (apps (Const (Elim (d.ind_name, l + 1)))
                 (vars 1 p @ [ lams (q + 1) (Srt (Univ l)) ] @ List.map (below_method l) d.ind_ctors)))

(* [P θ̄ x × Below_D Δ P θ̄ x], after P, step, θ̄ and x. *)
let motive_and_below d j =
  let q = nindices d in
  times (motive_at_base d ~motive:(q + 2) ~base:0) (below_at d j ~params:(q + 3) ~motive:(q + 2) ~base:0)

(* [step : Πθ̄. Πx. Below_D Δ P θ̄ x → P θ̄ x], after P. *)
let step_type d j =
  let q = nindices d in
  over_family d 1
    (Pi (below_at d j ~params:(q + 2) ~motive:(q + 1) ~base:0, motive_at_base d ~motive:(q + 2) ~base:1))

(* [Π(Δ). ΠP. Πstep. Πθ̄. Πx. P θ̄ x × Below_D Δ P θ̄ x]. *)
let build_type d j =
  pis d.ind_params (Pi (E.motive_type d j, Pi (step_type d j, over_family d 2 (motive_and_below d j))))

(* [Π(Δ). ΠP. Πstep. Πθ̄. Πx. P θ̄ x]. *)
let recbelow_type d j =
  let q = nindices d in
  pis d.ind_params
    (Pi (E.motive_type d j, Pi (step_type d j, over_family d 2 (motive_at_base d ~motive:(q + 2) ~base:0))))

(* On [c Δ ā] with the tuple [h] of the hypotheses: [(step ū (c Δ ā) h, h)];
   [step] lies right before the binders of the method. *)
let build_method d l c =
  let b = nbinders c.ctor_fields in
  let hs, rbs, _ =
    fold_slots (fun hs fd _ _ bl _ -> match fd with FRec _ -> Var (b - 2 - bl) :: hs | FArg _ -> hs)
      [] c.ctor_fields
  in
  let h = tuple l (List.rev hs) in
  let obj = apps (Const (Ctor (d.ind_name, c.ctor_name))) (vars (b + 2) (nparams d) @ field_vars rbs b) in
  lams b (Pair (apps (Var b) (List.map (rename (transport_past 2 rbs b)) c.ctor_indices @ [ obj; h ]), h))

(* [λΔ P step. elim_D[ℓ] Δ (λθ̄ x. P θ̄ x × Below_D Δ P θ̄ x) m̄]. *)
let build_body d j =
  let p = nparams d and q = nindices d and l = history_level d j in
  lams p (Lam (Lam (apps (Const (Elim (d.ind_name, l)))
                      (vars 2 p @ [ lams (q + 1) (motive_and_below d j) ]
                       @ List.map (build_method d l) d.ind_ctors))))

(* [λΔ P step θ̄ x. fst (build_D Δ P step θ̄ x)]. *)
let recbelow_body d j =
  let p = nparams d and q = nindices d in
  lams (p + 2 + q + 1)
    (Fst (apps (Const (Def (build_name d.ind_name j)))
            (vars (q + 3) p @ [ Var (q + 2); Var (q + 1) ] @ vars 0 (q + 1))))

(* The three δ-constants of (D, j) with [Unit_ℓ], [elim_D[ℓ+1]] and
   [elim_D[ℓ]], unless [recBelow_D] is registered already. *)
let ensure_below r sg name j =
  match find_def sg (recbelow_name name j) with
  | Some _ -> Ok sg
  | None ->
      let* d = match find_ind sg name with Some d -> Ok d | None -> Reg.refuse (RUndeclared name) in
      let l = history_level d j in
      let* sg = E.ensure_unit r sg l in
      let* sg = E.ensure_elim r sg name (l + 1) in
      let* sg = E.ensure_elim r sg name l in
      let* sg = Reg.define r sg (below_name name j) (below_type d j) (below_body d j) in
      let* sg = Reg.define r sg (build_name name j) (build_type d j) (build_body d j) in
      Reg.define r sg (recbelow_name name j) (recbelow_type d j) (recbelow_body d j)

(* ** Case trees *)

type mark = Constant | Varying
type strategy = Direct | History

type case_tree = Leaf of L.named | Split of string * (string * string list * case_tree) list

type fun_decl = {
  fn_name : string;
  fn_args : (string * L.named * mark) list;
  fn_result : L.named;
  fn_struct : string;
  fn_strategy : strategy;
  fn_tree : case_tree;
}

type path = (int * int) list
type tag = User of string * path option | Anon | Aux of int
type binder = { b_tag : tag; b_type : term }
type scope = binder list                    (* innermost first *)

let rec position n = function
  | [] -> None
  | m :: rest -> if n = m then Some 0 else Option.map succ (position n rest)

let rec distinct = function [] -> true | n :: rest -> not (List.mem n rest) && distinct rest

(* The names the user may write, and the index in the scope of the i-th. *)
let visible g = List.concat_map (fun b -> match b.b_tag with User (x, _) -> [ x ] | _ -> []) g

let rec from_visible g i =
  match g with
  | [] -> i
  | b :: g' ->
      (match b.b_tag with
       | User _ -> if i = 0 then 0 else 1 + from_visible g' (i - 1)
       | _ -> 1 + from_visible g' i)

let resolve_in g t =
  match L.resolve (visible g) t with
  | Ok u -> Ok (rename (from_visible g) u)
  | Error x -> Error (CUnbound x)

let rec lookup_user x = function
  | [] -> None
  | b :: g ->
      (match b.b_tag with
       | User (y, p) when y = x -> Some (0, p, b.b_type)
       | _ -> Option.map (fun (v, p, a) -> (v + 1, p, a)) (lookup_user x g))

let rec find_aux k = function
  | [] -> None
  | b :: g ->
      (match b.b_tag with
       | Aux k' when k' = k -> Some 0
       | _ -> Option.map succ (find_aux k g))

(* By levels, from the outermost binder.  [generalize] takes its seeds
   from its caller: as in Rocq, a level outside the scope has the type
   [Void] and the name [_].  The tails and the seeds of the splits are
   levels of the scope, which [level] takes. *)
let at_level g l = List.nth_opt (List.rev g) l
let level g l = List.nth (List.rev g) l
let level_type g l = match at_level g l with Some b -> b.b_type | None -> Void
let level_name g l = match at_level g l with Some { b_tag = User (x, _); _ } -> x | _ -> "_"

(* Whether [a], in a context of [l] binders, mentions the binder at level [m]. *)
let mentions_level l a m = m < l && occurs (l - 1 - m) a

(* ** Generalization *)

let anonymous b = b.b_tag = Anon

(* The binders of [g] a split generalizes beyond the seeds [ss]: those in
   [extra], and those whose types mention a seed or one already in the
   tail; by levels, outermost first.  A binder without a name stays. *)
let split_tail g ss extra =
  (* [tail_from] of CaseTree.v: from the binders [bs] at the level [l]
     on; [acc_rev] is the tail so far, in reverse. *)
  let rec go l bs acc_rev =
    match bs with
    | [] -> List.rev acc_rev
    | b :: bs' ->
        let mentions = mentions_level l b.b_type in
        let joins = (not (anonymous b)) && (not (List.mem l ss))
                    && (List.mem l extra || List.exists mentions ss || List.exists mentions acc_rev) in
        go (l + 1) bs' (if joins then l :: acc_rev else acc_rev)
  in
  go 0 (List.rev g) []

let moved n ss tail l =
  match position l ss with
  | Some i -> n + i
  | None -> (match position l tail with Some k -> n + List.length ss + k | None -> l)

(* [a], in a context of [from] binders, in one of [into] binders, where
   the binder at level [v] moves to the level [f v]. *)
let relevel f ~from:l ~into:n a = rename (fun v -> n -! 1 -! f (l -! 1 -! v)) a

type generalized = {
  gn_seeds : int list;
  gn_tail : int list;
  gn_seed_types : term list;
  gn_tail_types : term list;
  gn_goal : term;
}

(* Over the seeds [ss] with the tail [tail] of the split; the seeds must
   not depend on the tail. *)
let generalize_with g goal ss tail =
  let n = List.length g in
  let* () = iter_ok (fun s ->
      match List.find_opt (mentions_level s (level_type g s)) tail with
      | Some t -> Error (CGeneralize (level_name g s, level_name g t))
      | None -> Ok ()) ss in
  let mv = moved n ss tail and ns = List.length ss in
  Ok { gn_seeds = ss; gn_tail = tail;
       gn_seed_types = List.mapi (fun i s -> relevel mv ~from:s ~into:(n + i) (level_type g s)) ss;
       gn_tail_types = List.mapi (fun k t -> relevel mv ~from:t ~into:(n + ns + k) (level_type g t)) tail;
       gn_goal = relevel mv ~from:n ~into:(n + ns + List.length tail) goal }

(* With [extra] in the tail. *)
let generalize g goal ss extra = generalize_with g goal ss (split_tail g ss extra)

(* [λθ̄ z. Π(tail). T]. *)
let motive gn = lams (List.length gn.gn_seeds) (pis gn.gn_tail_types gn.gn_goal)

(* From after the [scope] binders of the scope, the [seeds] binders of
   the seeds and [tail] binders of the tail, into the scope with
   [binders] binders after it and the same [tail] binders; the seeds
   stand for [values]. *)
let instantiate ~scope:n ~seeds:s ~binders:b ~tail:k values a =
  subst (fun v ->
      let l = (n + s + k) -! 1 -! v in
      if l < n then Var (v + b - s)
      else if l < n + s then lift k (nth_or (Var 0) values (l - n))
      else Var v) a

(* [Π(tail). T] after [binders] binders after the scope, the seeds
   standing for [values]. *)
let motive_at ~scope gn ~binders values =
  instantiate ~scope ~seeds:(List.length gn.gn_seeds) ~binders ~tail:0 values
    (pis gn.gn_tail_types gn.gn_goal)

(* The scope after the binders [bs], innermost first, the seeds standing
   for [values] and the tail bound again; its goal; the substitution from
   the old scope. *)
let introduce g gn bs values =
  let n = List.length g and s = List.length gn.gn_seeds and b = List.length bs in
  let nt = List.length gn.gn_tail in
  let inst k = instantiate ~scope:n ~seeds:s ~binders:b ~tail:k values in
  let tail = List.mapi (fun k (t, a) ->
      { b_tag = (level g t).b_tag; b_type = inst k a }) (List.combine gn.gn_tail gn.gn_tail_types) in
  let gone = gn.gn_seeds @ gn.gn_tail in
  let old = List.mapi (fun v bd -> if List.mem (n - 1 - v) gone then { bd with b_tag = Anon } else bd) g in
  let sb v =
    let l = n -! 1 -! v in
    match position l gn.gn_seeds with
    | Some i -> lift nt (nth_or (Var 0) values i)
    | None ->
        (match position l gn.gn_tail with
         | Some k -> Var (nt - 1 - k)
         | None -> Var (v + b + nt))
  in
  (List.rev tail @ bs @ old, inst nt gn.gn_goal, sb)

(* ** Splits *)

type prim = PVoid | PUnit | PBool

let prim_of = function Void -> Some PVoid | Unit -> Some PUnit | Bool -> Some PBool | _ -> None
let prim_type = function PVoid -> Void | PUnit -> Unit | PBool -> Bool

let prim_name = function PVoid -> "Void" | PUnit -> "Unit" | PBool -> "Bool"

(* The constructors, each with its value. *)
let prim_ctors = function
  | PVoid -> []
  | PUnit -> [ ("tt", Tt) ]
  | PBool -> [ ("true", BTrue); ("false", BFalse) ]

let prim_desc pr =
  { ind_name = prim_name pr; ind_params = []; ind_indices = []; ind_level = 0;
    ind_ctors = List.map (fun (c, _) -> { ctor_name = c; ctor_fields = []; ctor_indices = [] }) (prim_ctors pr) }

(* The value of the constructor [c] of [pr]: a split asks only for the
   constructors of [prim_desc pr]. *)
let prim_value pr c = List.assoc c (prim_ctors pr)

type split_var = {
  sv_name : string;
  sv_level : int;
  sv_path : path option;
  sv_desc : ind_desc;
  sv_prim : prim option;
  sv_params : term list;
  sv_indices : int list;          (* levels *)
}

let var_at n l = Var (n - 1 - l)

let family_of sg g x =
  let* v, p, a = match lookup_user x g with Some r -> Ok r | None -> Error (CUnbound x) in
  let zl = List.length g - 1 - v in
  match prim_of a with
  | Some pr ->
      Ok { sv_name = x; sv_level = zl; sv_path = p; sv_desc = prim_desc pr; sv_prim = Some pr;
           sv_params = []; sv_indices = [] }
  | None ->
      let head, args = spine a in
      let* d = match head with
        | Const (Ind name) -> (match find_ind sg name with Some d -> Ok d | None -> Error (CNotFamily (x, a)))
        | _ -> Error (CNotFamily (x, a)) in
      let np = nparams d in
      let* () = require (List.length args = np + nindices d) (CNotFamily (x, a)) in
      let* theta = map_ok (function Var u -> Ok (zl -! 1 -! u) | _ -> Error (CIndices (x, a))) (drop np args) in
      let* () = require (distinct theta) (CIndices (x, a)) in
      Ok { sv_name = x; sv_level = zl; sv_path = p; sv_desc = d; sv_prim = None;
           sv_params = List.map (lift (v + 1)) (take np args); sv_indices = theta }

(* From the context of the [np] parameters [params] (Δ, in the scope) and
   the earlier fields, at [rbs] among [b] binders after the scope. *)
let field_sub ~np ~params rbs b n =
  match List.nth_opt rbs n with
  | Some bl -> Var (b - 1 - bl)
  | None -> lift b (nth_or (Var 0) params (np -! 1 -! (n - List.length rbs)))

(* The fields [fields] of a constructor of [name], named [xs], as
   [fold_slots] lays them out after a scope of [scope] binders generalized
   by [gn]: the binders, innermost first as in a scope, the positions of
   the fields and the number of binders.  [path] is that of the variable split, whose
   constructor has [nrec] recursive fields. *)
let field_binders ~name ~np ~params ~scope ~gn ~path ~nrec ~hyp_tag xs fields =
  (* The field [fd] named [x] at [l], its binder at [b] after the earlier
     fields at [rbs] with [k] recursive ones among them, on the binders
     [bs] before it, innermost first: the field and, after a recursive one
     [r : Πȳ:B̄. D Δ v̄], its hypothesis [Πȳ:B̄. Π(tail). T] at [v̄] and
     [r ȳ], tagged by [hyp_tag]. *)
  let bind_field x bs fd l k b rbs =
    let a = subst (field_sub ~np ~params rbs b) (field_type name np l fd) in
    match fd with
    | FArg _ -> { b_tag = User (x, None); b_type = a } :: bs
    | FRec (domains, indices) ->
        let m = List.length domains in
        let sb = field_sub ~np ~params rbs (b + 1) in
        let h = pis (subst_tele sb domains)
            (motive_at ~scope gn ~binders:(b + 1 + m)
               (List.map (subst (upn_sub m sb)) indices @ [ apps (Var m) (vars 0 m) ])) in
        let p = Option.map (fun p -> p @ [ (k, nrec) ]) path in
        { b_tag = hyp_tag k; b_type = h } :: { b_tag = User (x, p); b_type = a } :: bs
  in
  (* The names are taken in order, with the binders; a split names every
     field. *)
  let (_, bs), rbs, b =
    fold_slots (fun (xs, bs) fd l k b rbs ->
        match xs with
        | x :: xs' -> (xs', bind_field x bs fd l k b rbs)
        | [] -> invalid_arg "field_binders: a name for each field")
      (xs, []) fields
  in
  (bs, rbs, b)

type split_info = { si_var : split_var; si_gen : generalized }

type branch = {
  br_ctor : string;
  br_binders : int;
  br_scope : scope;
  br_goal : term;
  br_subst : int -> term;
}

let count_name c names = List.length (List.filter (( = ) c) names)

(* The variable with its family and the generalization over its indices
   and itself, with [extra] in the tail, computed once; first the
   parameters must not mention what is generalized. *)
let prepare_split sg g goal x extra =
  let* sv = family_of sg g x in
  let n = List.length g in
  let ss = sv.sv_indices @ [ sv.sv_level ] in
  let tail = split_tail g ss extra in
  let gone = ss @ tail in
  let* () = iter_ok (fun pa ->
      match List.find_opt (mentions_level n pa) gone with
      | Some t -> Error (CParams (x, level_name g t))
      | None -> Ok ()) sv.sv_params in
  let* gn = generalize_with g goal ss tail in
  Ok { si_var = sv; si_gen = gn }

let split_node sg g goal x extra hyp_tag bs =
  let* si = prepare_split sg g goal x extra in
  let sv = si.si_var and gn = si.si_gen in
  let d = sv.sv_desc and params = sv.sv_params and n = List.length g in
  let ctors = d.ind_ctors in
  let* () = require (List.length bs = List.length ctors
                     && List.for_all (fun c -> count_name c.ctor_name (List.map fst bs) = 1) ctors)
      (CBranches x) in
  let generalized_names = List.map (level_name g) gn.gn_tail in
  let name = d.ind_name and np = nparams d in
  let* brs = map_ok (fun c ->
      let xs = List.assoc c.ctor_name bs in
      let nf = List.length c.ctor_fields in
      let* () = require (List.length xs = nf) (CFields (c.ctor_name, nf)) in
      let* () = match first_duplicate xs with Some y -> Error (CFieldName (c.ctor_name, y)) | None -> Ok () in
      let* () = match List.find_opt (fun y -> List.mem y generalized_names) xs with
        | Some y -> Error (CFieldName (c.ctor_name, y))
        | None -> Ok () in
      let binders, rbs, b =
        field_binders ~name ~np ~params ~scope:n ~gn ~path:sv.sv_path ~nrec:(nrecs c.ctor_fields) ~hyp_tag
          xs c.ctor_fields in
      let indices = List.map (subst (field_sub ~np ~params rbs b)) c.ctor_indices in
      let obj = match sv.sv_prim with
        | Some pr -> prim_value pr c.ctor_name
        | None -> apps (Const (Ctor (name, c.ctor_name)))
                    (List.map (lift b) params @ field_vars rbs b) in
      let g', goal', sb = introduce g gn binders (indices @ [ obj ]) in
      Ok { br_ctor = c.ctor_name; br_binders = b; br_scope = g'; br_goal = goal'; br_subst = sb })
      ctors in
  Ok (si, brs)

(* ** Elaboration *)

type elab =
  | ELeaf of { scope : scope; goal : term; env : term list; rhs : term }
  | ESplit of { scope : scope; goal : term; split : split_info; branches : (int * elab) list }

let rec elaborate_with sg extra hyp_tag g goal env = function
  | Leaf rhs -> let* u = resolve_in g rhs in Ok (ELeaf { scope = g; goal; env; rhs = u })
  | Split (x, bs) ->
      let* si, brs = split_node sg g goal x extra hyp_tag (List.map (fun (c, xs, _) -> (c, xs)) bs) in
      let* es = map_ok (fun (c, _, t) ->
          match List.find_opt (fun br -> br.br_ctor = c) brs with
          | Some br ->
              let* e = elaborate_with sg [] (fun _ -> Anon) br.br_scope br.br_goal
                  (List.map (subst br.br_subst) env) t in
              Ok (c, e)
          | None -> Error (CBranches x)) bs in
      let* ordered = map_ok (fun br ->
          match List.assoc_opt br.br_ctor es with
          | Some e -> Ok (br.br_binders, e)
          | None -> Error (CBranches x)) brs in
      Ok (ESplit { scope = g; goal; split = si; branches = ordered })

let elaborate sg = elaborate_with sg [] (fun _ -> Anon)

(* The arguments as a scope, the structural one with the empty path; the
   result type as the goal; the values of the arguments. *)
let start fn =
  let names = List.map (fun (x, _, _) -> x) fn.fn_args in
  let* () = match first_duplicate names with Some x -> Error (CDuplicateArg x) | None -> Ok () in
  let* () = require (List.mem fn.fn_struct names) (CNoStruct fn.fn_struct) in
  let* g = fold_ok (fun g (x, a, _) ->
      let* a' = resolve_in g a in
      Ok ({ b_tag = User (x, if x = fn.fn_struct then Some [] else None); b_type = a' } :: g)) [] fn.fn_args in
  let* goal = resolve_in g fn.fn_result in
  Ok (g, goal, vars 0 (List.length fn.fn_args))

(* The levels of the varying arguments. *)
let varying fn =
  List.concat (List.mapi (fun i (_, _, mk) -> match mk with Varying -> [ i ] | Constant -> []) fn.fn_args)

(* ** Recursive calls *)

type recursion = {
  rec_name : string;
  rec_arity : int;
  rec_struct : int;
  rec_params : int;
  rec_indices : int list;
  rec_tail : int list;
  rec_names : string list;
  rec_strategy : strategy;
}

(* The component [k] of a tuple of [n] nested to the right, as [tuple]
   builds it ([component] of Recursion/Compile.v). *)
let tuple_component k n h =
  let rec snds k h = if k = 0 then h else snds (k - 1) (Snd h) in
  let h' = snds k h in
  if k + 1 = n then h' else Fst h'

(* The result of the subterm at the path from the history, applied to its
   positions. *)
let rec access h p ys =
  match p with
  | [] -> h
  | [ (k, n) ] -> Fst (apps (tuple_component k n h) ys)
  | (k, n) :: p' -> access (Snd (tuple_component k n h)) p' ys

(* The subterm of the structural argument of a call, under [d] binders
   of the right side: its index in the scope, its path and its type. *)
let subterm g d s =
  match fst (spine s) with
  | Var w when d <= w ->
      (match List.nth_opt g (w - d) with
       | Some { b_tag = User (_, Some (_ :: _ as p)); b_type = a } -> Some (w - d, p, a)
       | _ -> None)
  | _ -> None

(* The indices of [r ys], [r : Πȳ:B̄. D Δ v̄] at [u] in the scope. *)
let subterm_indices rc d u a ys =
  let domains, body = split_pis a in
  let m = List.length domains in
  List.map (subst (fun i ->
      if i < m then List.nth ys (m - 1 - i)
      else Var (i - m + u + 1 + d)))
    (drop rc.rec_params (snd (spine body)))

(* A call [f args] under [d] binders, its arguments translated already. *)
let call rc g env d t args =
  let n = rc.rec_arity in
  let* () = require (n <= List.length args) (CCallArity t) in
  let arg = List.nth (take n args) and name = List.nth rc.rec_names in
  let s = arg rc.rec_struct in
  let* u, p, a = match subterm g d s with Some r -> Ok r | None -> Error (CNotStructural t) in
  let ys = snd (spine s) in
  let* () = require (List.length ys = List.length (fst (split_pis a))) (CNotStructural t) in
  let* () = iter_ok (fun (i, v) -> if arg i = v then Ok () else Error (CIndexChanged (name i, t)))
      (combine rc.rec_indices (subterm_indices rc d u a ys)) in
  let* () = iter_ok (fun i ->
      if List.mem i rc.rec_tail || List.mem i rc.rec_indices || i = rc.rec_struct
         || arg i = lift d (List.nth env i)
      then Ok () else Error (CConstantChanged (name i, t)))
      (List.init n Fun.id) in
  let* acc = match rc.rec_strategy, p with
    | Direct, [ (k, _) ] ->
        (match find_aux (k + 1) g with Some h -> Ok (apps (Var (h + d)) ys) | None -> Error (CNotStructural t))
    | Direct, _ -> Error (CNotImmediate t)
    | History, _ ->
        (match find_aux 0 g with Some h -> Ok (access (Var (h + d)) p ys) | None -> Error (CNotStructural t))
  in
  Ok (apps acc (List.map arg rc.rec_tail @ drop n args))

(* A term in translation: done, or the function with its arguments so far. *)
type part = Done of term | Pending of term list

let done_ rc = function
  | Done u -> Ok u
  | Pending args -> Error (CCallArity (apps (Const (Def rc.rec_name)) args))

let rec calls_in rc g env d t =
  let sub d' u = let* r = calls_in rc g env d' u in done_ rc r in
  match t with
  | Const (Def f) -> if f = rc.rec_name then Ok (Pending []) else Ok (Done t)
  | App (u, a) ->
      let* ru = calls_in rc g env d u in
      let* a' = sub d a in
      (match ru with
       | Pending args ->
           let args' = args @ [ a' ] in
           if List.length args' = rc.rec_arity then
             let* c = call rc g env d (apps (Const (Def rc.rec_name)) args') args' in Ok (Done c)
           else Ok (Pending args')
       | Done u' -> Ok (Done (App (u', a'))))
  | Pi (a, b) -> let* a' = sub d a in let* b' = sub (d + 1) b in Ok (Done (Pi (a', b')))
  | Lam b -> let* b' = sub (d + 1) b in Ok (Done (Lam b'))
  | Ann (u, a) -> let* u' = sub d u in let* a' = sub d a in Ok (Done (Ann (u', a')))
  | ElimVoid (c, e) -> let* c' = sub d c in let* e' = sub d e in Ok (Done (ElimVoid (c', e')))
  | ElimUnit (c, m, u) ->
      let* c' = sub d c in let* m' = sub d m in let* u' = sub d u in Ok (Done (ElimUnit (c', m', u')))
  | ElimBool (c, x, y, b) ->
      let* c' = sub d c in let* x' = sub d x in let* y' = sub d y in let* b' = sub d b in
      Ok (Done (ElimBool (c', x', y', b')))
  | Sigma (a, b) -> let* a' = sub d a in let* b' = sub (d + 1) b in Ok (Done (Sigma (a', b')))
  | Pair (a, b) -> let* a' = sub d a in let* b' = sub d b in Ok (Done (Pair (a', b')))
  | Fst u -> let* u' = sub d u in Ok (Done (Fst u'))
  | Snd u -> let* u' = sub d u in Ok (Done (Snd u'))
  | Srt _ | Var _ | Void | Unit | Tt | Bool | BTrue | BFalse | Const _ -> Ok (Done t)

let calls rc g env t = let* r = calls_in rc g env 0 t in done_ rc r

(* ** Translation *)

let case = function Ok a -> Ok a | Error e -> Reg.refuse (RCase e)

let level_of x = function Univ k -> Ok k | s -> Reg.refuse (RCase (CMotiveSort (x, s)))

(* The eliminator of a primitive type, its motive annotated. *)
let prim_elim pr c ms z =
  match pr, ms with
  | PUnit, [ m ] -> ElimUnit (c, m, z)
  | PBool, [ mt; mf ] -> ElimBool (c, mt, mf, z)
  | PVoid, [] -> ElimVoid (c, z)
  | _ -> invalid_arg "prim_elim: a method for each constructor"

(* The level of [Π(tail). T] after the scope and the seeds. *)
let motive_level r sg rc g x gn =
  let* s = Reg.sort_of r sg (AtMotive (rc.rec_name, x))
      (List.rev gn.gn_seed_types @ List.map (fun b -> b.b_type) g) (pis gn.gn_tail_types gn.gn_goal) in
  level_of x s

(* The term of an elaborated tree in its scope, and the instances of
   eliminators it uses. *)
let rec translate r sg rc = function
  | ELeaf { scope = g; env; rhs; _ } -> let* t = case (calls rc g env rhs) in Ok (t, [])
  | ESplit { scope = g; split = si; branches = brs; _ } ->
      let sv = si.si_var and gn = si.si_gen in
      let n = List.length g in
      let* k = motive_level r sg rc g sv.sv_name gn in
      (* The method of each branch, with the instances it uses. *)
      let* branches = map_ok (fun (b, e) ->
          let* t, needed = translate r sg rc e in
          Ok (lams b (lams (List.length gn.gn_tail) t), needed)) brs in
      let ms = List.map fst branches and needed = List.concat_map snd branches in
      let name = sv.sv_desc.ind_name in
      let seeds = List.map (var_at n) gn.gn_seeds and tail = List.map (var_at n) gn.gn_tail in
      (match sv.sv_prim with
       | None -> Ok (apps (Const (Elim (name, k))) (sv.sv_params @ [ motive gn ] @ ms @ seeds @ tail), (name, k) :: needed)
       | Some pr ->
           let c = Ann (motive gn, Pi (prim_type pr, Srt (Univ k))) in
           Ok (apps (prim_elim pr c ms (var_at n sv.sv_level)) tail, needed))

(* ** The defining equations *)

(* Every leaf is reached through a split of the structural argument. *)
let rec splits_struct = function
  | ELeaf { scope; _ } ->
      not (List.exists (fun b -> match b.b_tag with User (_, Some []) -> true | _ -> false) scope)
  | ESplit { branches; _ } -> List.for_all (fun (_, e) -> splits_struct e) branches

let rec equations f = function
  | ELeaf { env; rhs; _ } -> [ (apps (Const (Def f)) env, rhs) ]
  | ESplit { branches; _ } -> List.concat_map (fun (_, e) -> equations f e) branches

(* ** Compilation *)

let check_equation r sg f (i, (lhs, rhs)) =
  match convert ~sg (Reg.fuel_of r) lhs rhs with
  | ConvEqual u -> Reg.emit r (AtEquation (f, i)) [ EvConv (lhs, rhs, u) ]; Ok ()
  | ConvOutOfFuel -> Reg.emit r (AtEquation (f, i)) []; Error (NoFuelAt (AtEquation (f, i), lhs))
  | _ -> Reg.emit r (AtEquation (f, i)) []; Reg.refuse (REquation (f, i, lhs, rhs))

(* The direct translation, in the scope [g] of the arguments with the goal
   [goal] and their values [env]: the tree splits the structural argument
   at its root, and a call is the hypothesis of a field.  The signature,
   the body in that scope, the instances of eliminators it uses, and the
   elaborated tree. *)
let compile_direct r sg fn rc g goal env =
  let x = fn.fn_struct in
  let* () = match fn.fn_tree with
    | Split (y, _) when y = x -> Ok ()
    | _ -> Reg.refuse (RCase (CRoot x)) in
  let* e = case (elaborate_with sg (varying fn) (fun k -> Aux (k + 1)) g goal env fn.fn_tree) in
  let* t, needed = translate r sg rc e in
  Ok (sg, t, needed, e)

(* The translation through the history, the root split [si] of the scope
   [g] (its goal is that of [si]): the motive of the structural argument
   at its level, the history of its family registered for it, and
   [recBelow_D] applied to the step, the tree elaborated with the table
   [Below_D] as [Aux 0]. *)
let compile_history r sg fn rc si g env =
  let sv = si.si_var and gn = si.si_gen in
  let name = sv.sv_desc.ind_name and params = sv.sv_params and q = List.length sv.sv_indices in
  let* j = motive_level r sg rc g fn.fn_struct gn in
  let* sg1 = ensure_below r sg name j in
  let p = motive gn in
  let seeds = List.map (fun (l, a) -> { b_tag = (level g l).b_tag; b_type = a })
      (List.combine gn.gn_seeds gn.gn_seed_types) in
  let table = apps (Const (Def (below_name name j)))
      (List.map (lift (q + 1)) params @ [ lift (q + 1) p ] @ vars 0 (q + 1)) in
  let g1, goal1, sb = introduce g gn ({ b_tag = Aux 0; b_type = table } :: List.rev seeds) (vars 1 (q + 1)) in
  let* e = case (elaborate sg1 g1 goal1 (List.map (subst sb) env) fn.fn_tree) in
  let* t, needed = translate r sg1 rc e in
  let step = lams (q + 1) (Lam (lams (List.length gn.gn_tail) t)) in
  Ok (sg1, apps (Const (Def (recbelow_name name j)))
             (params @ [ p; step ] @ List.map (var_at (List.length g)) (gn.gn_seeds @ gn.gn_tail)), needed, e)

(* The signature with the history and the instances the function needs,
   its type, its body, and what [out] reads off the elaborated tree. *)
let compile_with r out sg fn =
  let x = fn.fn_struct in
  let* g0, goal0, env0 = case (start fn) in
  let* si = case (prepare_split sg g0 goal0 x (varying fn)) in
  let sv = si.si_var and gn = si.si_gen in
  let* () = match sv.sv_prim with Some pr -> Reg.refuse (RCase (CNotFamily (x, prim_type pr))) | None -> Ok () in
  let n = List.length g0 in
  let rc = { rec_name = fn.fn_name; rec_arity = n; rec_struct = sv.sv_level; rec_params = nparams sv.sv_desc;
             rec_indices = sv.sv_indices; rec_tail = gn.gn_tail; rec_names = List.map (fun (y, _, _) -> y) fn.fn_args;
             rec_strategy = fn.fn_strategy } in
  let* sg1, root, needed, e =
    match fn.fn_strategy with
    | Direct -> compile_direct r sg fn rc g0 goal0 env0
    | History -> compile_history r sg fn rc si g0 env0
  in
  let* () = if splits_struct e then Ok () else Reg.refuse (RCase (CUnsplit x)) in
  let* sg2 = fold_ok (fun sg (d, k) -> E.ensure_elim r sg d k) sg1 needed in
  Ok (sg2, pis (List.map (fun b -> b.b_type) (List.rev g0)) goal0, lams n root, out e)

let compile_term r sg fn = compile_with r (equations fn.fn_name) sg fn

(* The function as a δ-constant, then its equations by conversion. *)
let compile r sg fn =
  let* sg0, a, b, eqs = compile_term r sg fn in
  let* sg' = Reg.define r sg0 fn.fn_name a b in
  let* () = iter_ok (check_equation r sg' fn.fn_name) (List.mapi (fun i e -> (i, e)) eqs) in
  Ok sg'

let compile_checked spec fuel sg fn = Reg.run spec fuel (fun r -> compile r sg fn)

(* Several functions in turn, each in the signature of those before. *)
let compile_all spec fuel sg fns = Reg.run spec fuel (fun r -> fold_ok (fun sg fn -> compile r sg fn) sg fns)
