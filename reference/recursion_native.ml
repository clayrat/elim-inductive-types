(* Algorithm 2, native: the history of results (Recursion/Below.v), the
   elaboration of case trees (Recursion/CaseTree.v) and the compiler of
   structural recursion through it (Recursion/Compile.v), on top of the
   native algorithm 1 and the kernel's native reference.  Written by hand
   from the lecture; the differential test compares it with the extract.

   Indices and levels are natural numbers in Rocq, where subtraction
   stops at 0; [-!] does the same here. *)

open Pts_native
open Diagnostics_native
module E = Elim_native
module L = Looping

let ( let* ) = Result.bind
let require ok error = if ok then Ok () else Error error
let ( -! ) a b = max 0 (a - b)

let rec map_ok f = function
  | [] -> Ok []
  | x :: xs -> let* y = f x in let* ys = map_ok f xs in Ok (y :: ys)

let rec iter_ok f = function
  | [] -> Ok ()
  | x :: xs -> let* () = f x in iter_ok f xs

let rec fold_ok f acc = function
  | [] -> Ok acc
  | x :: xs -> let* acc = f acc x in fold_ok f acc xs

let rec combine xs ys = match xs, ys with x :: xs, y :: ys -> (x, y) :: combine xs ys | _ -> []

let rec first_duplicate = function
  | [] -> None
  | x :: rest -> if List.mem x rest then Some x else first_duplicate rest

(* ** Terms *)

let rename r t = subst (fun n -> Var (r n)) t
let up_ren r n = if n = 0 then 0 else r (n - 1) + 1
let rec upn_ren m r = if m = 0 then r else up_ren (upn_ren (m - 1) r)

let rec rename_tele r = function
  | [] -> []
  | a :: rest -> rename r a :: rename_tele (up_ren r) rest

let up_sub sb n = if n = 0 then Var 0 else lift 1 (sb (n - 1))
let rec upn_sub m sb = if m = 0 then sb else up_sub (upn_sub (m - 1) sb)

let rec subst_tele sb = function
  | [] -> []
  | a :: rest -> subst sb a :: subst_tele (up_sub sb) rest

let rec lams n t = if n = 0 then t else Lam (lams (n - 1) t)
let times a b = Sigma (a, lift 1 b)

let rec split_pis = function
  | Pi (a, b) -> let domains, body = split_pis b in (a :: domains, body)
  | t -> ([], t)

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

(* As the transport of Elim_native, with [g] binders between the
   parameters and those of the method. *)
let transport_past g rbs b n =
  match List.nth_opt rbs n with
  | Some bl -> b -! 1 -! bl
  | None -> (n -! List.length rbs) + (b + g)

(* A recursive field among the binders of a method: its position, the
   positions of the earlier fields, innermost first, its domains and
   indices; its hypothesis follows it. *)
type rec_binder = { rb_pos : int; rb_before : int list; rb_domains : term list; rb_indices : term list }

(* The positions of all the fields, the number of binders and the
   recursive fields. *)
let rec method_binders rbs b = function
  | [] -> (rbs, b, [])
  | FArg _ :: fs -> method_binders (b :: rbs) (b + 1) fs
  | FRec (domains, indices) :: fs ->
      let rbs', b', rs = method_binders (b :: rbs) (b + 2) fs in
      (rbs', b', { rb_pos = b; rb_before = rbs; rb_domains = domains; rb_indices = indices } :: rs)

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

(* The name, the numbers of parameters and indices, and the level of the
   history of (D, j). *)
let dims d j = (d.ind_name, List.length d.ind_params, List.length d.ind_indices, history_level d j)

(* [Πθ̄. Πx:D Δ θ̄. F], [e] binders between the parameters and θ̄. *)
let over_family d e f =
  let name, p, q, _ = dims d 0 in
  pis (rename_tele (fun n -> n + e) d.ind_indices)
    (Pi (apps (Const (Ind name)) (vars (q + e) p @ vars 0 q), f))

(* [P θ̄ x] and [Below_D Δ P θ̄ x], with θ̄ x at [base]. *)
let motive_at_base d pv base = apps (Var pv) (vars base (List.length d.ind_indices + 1))

let below_at d j params pv base =
  let name, p, q, _ = dims d j in
  apps (Const (Def (below_name name j))) (vars params p @ [ Var pv ] @ vars base (q + 1))

(* [Π(Δ). ΠP:(Πθ̄. D Δ θ̄ → Type_j). Πθ̄. D Δ θ̄ → Type_ℓ]. *)
let below_type d j =
  let _, _, _, l = dims d j in
  pis d.ind_params (Pi (E.motive_type d j, over_family d 1 (Srt (Univ l))))

(* [Πȳ:B̄. P v̄ (r ȳ) × ih ȳ] for a recursive field [r] with its
   hypothesis [ih], among [b] binders after the parameters and P. *)
let component b rb =
  let m = List.length rb.rb_domains in
  let r = transport_past 1 rb.rb_before b in
  pis (rename_tele r rb.rb_domains)
    (times
       (apps (Var (b + m))
          (List.map (rename (upn_ren m r)) rb.rb_indices
           @ [ apps (Var ((b -! 1 -! rb.rb_pos) + m)) (vars 0 m) ]))
       (apps (Var ((b -! 2 -! rb.rb_pos) + m)) (vars 0 m)))

let below_method l c =
  let _, b, rs = method_binders [] 0 c.ctor_fields in
  lams b (tuple_type l (List.map (component b) rs))

(* [λΔ P. elim_D[ℓ+1] Δ (λθ̄ x. Type_ℓ) m̄]. *)
let below_body d j =
  let name, p, q, l = dims d j in
  lams p (Lam (apps (Const (Elim (name, l + 1)))
                 (vars 1 p @ [ lams (q + 1) (Srt (Univ l)) ] @ List.map (below_method l) d.ind_ctors)))

(* [step : Πθ̄. Πx. Below_D Δ P θ̄ x → P θ̄ x], after P. *)
let step_type d j =
  let q = List.length d.ind_indices in
  over_family d 1 (Pi (below_at d j (q + 2) (q + 1) 0, motive_at_base d (q + 2) 1))

(* [Π(Δ). ΠP. Πstep. Πθ̄. Πx. P θ̄ x × Below_D Δ P θ̄ x]. *)
let build_type d j =
  let q = List.length d.ind_indices in
  pis d.ind_params
    (Pi (E.motive_type d j,
         Pi (step_type d j,
             over_family d 2 (times (motive_at_base d (q + 2) 0) (below_at d j (q + 3) (q + 2) 0)))))

(* [Π(Δ). ΠP. Πstep. Πθ̄. Πx. P θ̄ x]. *)
let recbelow_type d j =
  let q = List.length d.ind_indices in
  pis d.ind_params (Pi (E.motive_type d j, Pi (step_type d j, over_family d 2 (motive_at_base d (q + 2) 0))))

(* On [c Δ ā] with the tuple [h] of the hypotheses: [(step ū (c Δ ā) h, h)];
   [step] lies right before the binders of the method. *)
let build_method d l c =
  let name, p, _, _ = dims d 0 in
  let rbs, b, rs = method_binders [] 0 c.ctor_fields in
  let h = tuple l (List.map (fun rb -> Var (b -! 2 -! rb.rb_pos)) rs) in
  let obj = apps (Const (Ctor (name, c.ctor_name)))
      (vars (b + 2) p @ List.map (fun bl -> Var (b -! 1 -! bl)) (List.rev rbs)) in
  lams b (Pair (apps (Var b) (List.map (rename (transport_past 2 rbs b)) c.ctor_indices @ [ obj; h ]), h))

(* [λΔ P step. elim_D[ℓ] Δ (λθ̄ x. P θ̄ x × Below_D Δ P θ̄ x) m̄]. *)
let build_body d j =
  let name, p, q, l = dims d j in
  lams p (Lam (Lam (apps (Const (Elim (name, l)))
                      (vars 2 p
                       @ [ lams (q + 1) (times (motive_at_base d (q + 2) 0) (below_at d j (q + 3) (q + 2) 0)) ]
                       @ List.map (build_method d l) d.ind_ctors))))

(* [λΔ P step θ̄ x. fst (build_D Δ P step θ̄ x)]. *)
let recbelow_body d j =
  let name, p, q, _ = dims d j in
  lams (p + 2 + q + 1)
    (Fst (apps (Const (Def (build_name name j)))
            (vars (q + 3) p @ [ Var (q + 2); Var (q + 1) ] @ vars 0 (q + 1))))

(* The three δ-constants of (D, j) with [Unit_ℓ], [elim_D[ℓ+1]] and
   [elim_D[ℓ]], unless [recBelow_D] is registered already. *)
let ensure_below r sg name j =
  match find_def sg (recbelow_name name j) with
  | Some _ -> Ok sg
  | None ->
      let* d = match find_ind sg name with Some d -> Ok d | None -> E.refuse (RUndeclared name) in
      let l = history_level d j in
      let* sg1 = E.ensure_unit r sg l in
      let* sg2 = E.ensure_elim r sg1 name (l + 1) in
      let* sg3 = E.ensure_elim r sg2 name l in
      let* sg4 = E.define r sg3 (below_name name j) (below_type d j) (below_body d j) in
      let* sg5 = E.define r sg4 (build_name name j) (build_type d j) (build_body d j) in
      E.define r sg5 (recbelow_name name j) (recbelow_type d j) (recbelow_body d j)

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
      let further = Option.map (fun (v, p, a) -> (v + 1, p, a)) (lookup_user x g) in
      (match b.b_tag with User (y, p) when y = x -> Some (0, p, b.b_type) | _ -> further)

let rec find_aux k = function
  | [] -> None
  | b :: g ->
      (match b.b_tag with
       | Aux k' when k' = k -> Some 0
       | _ -> Option.map succ (find_aux k g))

(* By levels, from the outermost binder. *)
let at_level g l = List.nth_opt (List.rev g) l
let level_type g l = match at_level g l with Some b -> b.b_type | None -> Void
let level_name g l = match at_level g l with Some { b_tag = User (x, _); _ } -> x | _ -> "_"

(* Whether [a], in a context of [l] binders, mentions the binder at level [m]. *)
let mentions_level l a m = m < l && occurs (l -! 1 -! m) a

(* ** Generalization *)

let anonymous b = b.b_tag = Anon

(* The binders a split generalizes beyond the seeds: those in [extra],
   and those whose types mention a seed or one already in the tail; by
   levels, outermost first.  A binder without a name stays.  [acc_rev]
   is the tail so far, in reverse. *)
let rec tail_from l bs ss extra acc_rev =
  match bs with
  | [] -> List.rev acc_rev
  | b :: bs' ->
      let mentions = mentions_level l b.b_type in
      let joins = (not (anonymous b)) && (not (List.mem l ss))
                  && (List.mem l extra || List.exists mentions ss || List.exists mentions acc_rev) in
      tail_from (l + 1) bs' ss extra (if joins then l :: acc_rev else acc_rev)

let moved n ss tail l =
  match position l ss with
  | Some i -> n + i
  | None -> (match position l tail with Some k -> n + List.length ss + k | None -> l)

let relevel f l n a = rename (fun v -> n -! 1 -! f (l -! 1 -! v)) a

type generalized = {
  gn_seeds : int list;
  gn_tail : int list;
  gn_seed_types : term list;
  gn_tail_types : term list;
  gn_goal : term;
}

let generalize g goal ss extra =
  let n = List.length g in
  let tail = tail_from 0 (List.rev g) ss extra [] in
  let* () = iter_ok (fun s ->
      match List.find_opt (mentions_level s (level_type g s)) tail with
      | Some t -> Error (CGeneralize (level_name g s, level_name g t))
      | None -> Ok ()) ss in
  let mv = moved n ss tail in
  Ok { gn_seeds = ss; gn_tail = tail;
       gn_seed_types = List.mapi (fun i s -> relevel mv s (n + i) (level_type g s)) ss;
       gn_tail_types = List.mapi (fun k t -> relevel mv t (n + List.length ss + k) (level_type g t)) tail;
       gn_goal = relevel mv n (n + List.length ss + List.length tail) goal }

(* [λθ̄ z. Π(tail). T]. *)
let motive gn = lams (List.length gn.gn_seeds) (pis gn.gn_tail_types gn.gn_goal)

(* From after the scope, the seeds and [k] binders of the tail, into the
   scope with [b] binders after it and the [k] binders, the seeds
   standing for [values]. *)
let instantiate n s b k values a =
  subst (fun v ->
      let l = (n + s + k) -! 1 -! v in
      if l < n then Var ((v + b) -! s)
      else if l < n + s then lift k (Option.value (List.nth_opt values (l -! n)) ~default:(Var 0))
      else Var v) a

let motive_at n gn b values = instantiate n (List.length gn.gn_seeds) b 0 values (pis gn.gn_tail_types gn.gn_goal)

(* The scope after the binders [bs], the seeds standing for [values] and
   the tail bound again; its goal; the substitution from the old scope. *)
let introduce g gn bs values =
  let n = List.length g and s = List.length gn.gn_seeds and b = List.length bs in
  let nt = List.length gn.gn_tail in
  let inst k = instantiate n s b k values in
  let tail = List.mapi (fun k (t, a) ->
      let tg = match at_level g t with Some bd -> bd.b_tag | None -> Anon in
      { b_tag = tg; b_type = inst k a }) (combine gn.gn_tail gn.gn_tail_types) in
  let gone = gn.gn_seeds @ gn.gn_tail in
  let old = List.mapi (fun v bd -> if List.mem (n -! 1 -! v) gone then { bd with b_tag = Anon } else bd) g in
  let sb v =
    let l = n -! 1 -! v in
    match position l gn.gn_seeds with
    | Some i -> lift nt (Option.value (List.nth_opt values i) ~default:(Var 0))
    | None ->
        (match position l gn.gn_tail with
         | Some k -> Var (nt -! 1 -! k)
         | None -> Var (v + b + nt))
  in
  (List.rev tail @ List.rev bs @ old, inst nt gn.gn_goal, sb)

(* ** Splits *)

type prim = PVoid | PUnit | PBool

let prim_of = function Void -> Some PVoid | Unit -> Some PUnit | Bool -> Some PBool | _ -> None
let prim_type = function PVoid -> Void | PUnit -> Unit | PBool -> Bool

let prim_desc pr =
  let ctor c = { ctor_name = c; ctor_fields = []; ctor_indices = [] } in
  let desc name ctors = { ind_name = name; ind_params = []; ind_indices = []; ind_level = 0; ind_ctors = ctors } in
  match pr with
  | PVoid -> desc "Void" []
  | PUnit -> desc "Unit" [ ctor "tt" ]
  | PBool -> desc "Bool" [ ctor "true"; ctor "false" ]

let prim_value c = if c = "tt" then Tt else if c = "true" then BTrue else BFalse

type split_var = {
  sv_name : string;
  sv_level : int;
  sv_path : path option;
  sv_desc : ind_desc;
  sv_prim : prim option;
  sv_params : term list;
  sv_indices : int list;          (* levels *)
}

let var_at n l = Var (n -! 1 -! l)

let family_of sg g x =
  let* v, p, a = match lookup_user x g with Some r -> Ok r | None -> Error (CUnbound x) in
  let zl = List.length g -! 1 -! v in
  match prim_of a with
  | Some pr ->
      Ok { sv_name = x; sv_level = zl; sv_path = p; sv_desc = prim_desc pr; sv_prim = Some pr;
           sv_params = []; sv_indices = [] }
  | None ->
      let head, args = spine a in
      let* d = match head with
        | Const (Ind name) -> (match find_ind sg name with Some d -> Ok d | None -> Error (CNotFamily (x, a)))
        | _ -> Error (CNotFamily (x, a)) in
      let np = List.length d.ind_params in
      let* () = require (List.length args = np + List.length d.ind_indices) (CNotFamily (x, a)) in
      let* theta = map_ok (function Var u -> Ok (zl -! 1 -! u) | _ -> Error (CIndices (x, a))) (drop np args) in
      let* () = require (distinct theta) (CIndices (x, a)) in
      Ok { sv_name = x; sv_level = zl; sv_path = p; sv_desc = d; sv_prim = None;
           sv_params = List.map (lift (v + 1)) (take np args); sv_indices = theta }

(* From the context of the parameters and the earlier fields, at [rbs]
   among [b] binders after the scope. *)
let field_sub np params rbs b n =
  match List.nth_opt rbs n with
  | Some bl -> Var (b -! 1 -! bl)
  | None -> lift b (Option.value (List.nth_opt params (np -! 1 -! (n -! List.length rbs))) ~default:(Var 0))

(* The fields named [xs]: the binders, outermost first, each recursive
   field followed by its hypothesis [Πȳ:B̄. Π(tail). T] at [v̄] and [r ȳ];
   the positions of the fields and the number of binders. *)
let field_binders name np params n gn sub nrec hyp_tag =
  let rec go xs rbs b k l fs =
    match fs, xs with
    | fd :: fs', x :: xs' ->
        let a = subst (field_sub np params rbs b) (field_type name np l fd) in
        (match fd with
         | FArg _ ->
             let bs, rbs', b' = go xs' (b :: rbs) (b + 1) k (l + 1) fs' in
             ({ b_tag = User (x, None); b_type = a } :: bs, rbs', b')
         | FRec (domains, indices) ->
             let m = List.length domains in
             let sb = field_sub np params rbs (b + 1) in
             let h = pis (subst_tele sb domains)
                 (motive_at n gn (b + 1 + m)
                    (List.map (subst (upn_sub m sb)) indices @ [ apps (Var m) (vars 0 m) ])) in
             let p = Option.map (fun p -> p @ [ (k, nrec) ]) sub in
             let bs, rbs', b' = go xs' (b :: rbs) (b + 2) (k + 1) (l + 1) fs' in
             ({ b_tag = User (x, p); b_type = a } :: { b_tag = hyp_tag k; b_type = h } :: bs, rbs', b'))
    | _ -> ([], rbs, b)
  in
  go

type split_info = { si_var : split_var; si_gen : generalized }

type branch = {
  br_ctor : string;
  br_binders : int;
  br_scope : scope;
  br_goal : term;
  br_subst : int -> term;
}

let count_name c names = List.length (List.filter (( = ) c) names)
let rec_count c = List.length (List.filter (function FRec _ -> true | FArg _ -> false) c.ctor_fields)

(* The variable with its family and the generalization over its indices
   and itself; first the parameters must not mention what is generalized. *)
let prepare_split sg g goal x extra =
  let* sv = family_of sg g x in
  let ss = sv.sv_indices @ [ sv.sv_level ] in
  let* () = iter_ok (fun pa ->
      match List.find_opt (mentions_level (List.length g) pa) (ss @ tail_from 0 (List.rev g) ss extra []) with
      | Some t -> Error (CParams (x, level_name g t))
      | None -> Ok ()) sv.sv_params in
  let* gn = generalize g goal ss extra in
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
  let name = d.ind_name and np = List.length d.ind_params in
  let* brs = map_ok (fun c ->
      let xs = match List.find_opt (fun (c', _) -> c' = c.ctor_name) bs with Some (_, xs) -> xs | None -> [] in
      let nf = List.length c.ctor_fields in
      let* () = require (List.length xs = nf) (CFields (c.ctor_name, nf)) in
      let* () = match first_duplicate xs with Some y -> Error (CFieldName (c.ctor_name, y)) | None -> Ok () in
      let* () = match List.find_opt (fun y -> List.mem y generalized_names) xs with
        | Some y -> Error (CFieldName (c.ctor_name, y))
        | None -> Ok () in
      let binders, rbs, b =
        field_binders name np params n gn sv.sv_path (rec_count c) hyp_tag xs [] 0 0 0 c.ctor_fields in
      let indices = List.map (subst (field_sub np params rbs b)) c.ctor_indices in
      let obj = match sv.sv_prim with
        | Some _ -> prim_value c.ctor_name
        | None -> apps (Const (Ctor (name, c.ctor_name)))
                    (List.map (lift b) params @ List.map (fun bl -> Var (b -! 1 -! bl)) (List.rev rbs)) in
      let g', goal', sb = introduce g gn binders (indices @ [ obj ]) in
      Ok { br_ctor = c.ctor_name; br_binders = b; br_scope = g'; br_goal = goal'; br_subst = sb })
      ctors in
  Ok (si, brs)

(* ** Elaboration *)

type elab =
  | ELeaf of scope * term * term list * term       (* scope, goal, values of the arguments, right side *)
  | ESplit of scope * term * split_info * (int * elab) list

let rec elaborate_with sg extra hyp_tag g goal env = function
  | Leaf rhs -> let* u = resolve_in g rhs in Ok (ELeaf (g, goal, env, u))
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
      Ok (ESplit (g, goal, si, ordered))

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

(* The component [k] of a tuple of [n] nested to the right. *)
let component k n h =
  let rec snds k h = if k = 0 then h else snds (k - 1) (Snd h) in
  let h' = snds k h in
  if k + 1 = n then h' else Fst h'

(* The result of the subterm at the path from the history, applied to its
   positions. *)
let rec access h p ys =
  match p with
  | [] -> h
  | [ (k, n) ] -> Fst (apps (component k n h) ys)
  | (k, n) :: p' -> access (Snd (component k n h)) p' ys

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
      if i < m then Option.value (List.nth_opt ys (m -! 1 -! i)) ~default:(Var 0)
      else Var ((i -! m) + (u + 1) + d)))
    (drop rc.rec_params (snd (spine body)))

let nth_or l i = Option.value (List.nth_opt l i) ~default:(Var 0)

(* A call [f args] under [d] binders, its arguments translated already. *)
let call rc g env d t args =
  let n = rc.rec_arity in
  let* () = require (n <= List.length args) (CCallArity t) in
  let cargs = take n args in
  let s = nth_or cargs rc.rec_struct in
  let* u, p, a = match subterm g d s with Some r -> Ok r | None -> Error (CNotStructural t) in
  let ys = snd (spine s) in
  let* () = require (List.length ys = List.length (fst (split_pis a))) (CNotStructural t) in
  let name i = Option.value (List.nth_opt rc.rec_names i) ~default:"" in
  let* () = iter_ok (fun (i, v) -> if nth_or cargs i = v then Ok () else Error (CIndexChanged (name i, t)))
      (combine rc.rec_indices (subterm_indices rc d u a ys)) in
  let* () = iter_ok (fun i ->
      if List.mem i rc.rec_tail || List.mem i rc.rec_indices || i = rc.rec_struct
         || nth_or cargs i = lift d (nth_or env i)
      then Ok () else Error (CConstantChanged (name i, t)))
      (List.init n Fun.id) in
  let* acc = match rc.rec_strategy, p with
    | Direct, [ (k, _) ] ->
        (match find_aux (k + 1) g with Some h -> Ok (apps (Var (h + d)) ys) | None -> Error (CNotStructural t))
    | Direct, _ -> Error (CNotImmediate t)
    | History, _ ->
        (match find_aux 0 g with Some h -> Ok (access (Var (h + d)) p ys) | None -> Error (CNotStructural t))
  in
  Ok (apps acc (List.map (nth_or cargs) rc.rec_tail @ drop n args))

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
  | _ -> Ok (Done t)

let calls rc g env t = let* r = calls_in rc g env 0 t in done_ rc r

(* ** Translation *)

let case = function Ok a -> Ok a | Error e -> E.refuse (RCase e)

let level_of x = function Univ k -> Ok k | s -> E.refuse (RCase (CMotiveSort (x, s)))

(* The eliminator of a primitive type, its motive annotated. *)
let prim_elim pr c ms z =
  match pr, ms with
  | PUnit, [ m ] -> ElimUnit (c, m, z)
  | PBool, [ mt; mf ] -> ElimBool (c, mt, mf, z)
  | _ -> ElimVoid (c, z)

(* The level of [Π(tail). T] after the scope and the seeds. *)
let motive_level r sg rc g x gn =
  let* s = E.sort_of r sg (AtMotive (rc.rec_name, x))
      (List.rev gn.gn_seed_types @ List.map (fun b -> b.b_type) g) (pis gn.gn_tail_types gn.gn_goal) in
  level_of x s

(* The term of an elaborated tree in its scope, and the instances of
   eliminators it uses. *)
let rec translate r sg rc = function
  | ELeaf (g, _, env, rhs) -> let* t = case (calls rc g env rhs) in Ok (t, [])
  | ESplit (g, _, si, brs) ->
      let sv = si.si_var and gn = si.si_gen in
      let n = List.length g in
      let* k = motive_level r sg rc g sv.sv_name gn in
      (* The methods and the instances of the branches, in reverse. *)
      let* ms_rev, needed_rev = fold_ok (fun (ms_rev, needed_rev) (b, e) ->
          let* t, needed' = translate r sg rc e in
          Ok (lams b (lams (List.length gn.gn_tail) t) :: ms_rev, List.rev_append needed' needed_rev)) ([], []) brs in
      let ms = List.rev ms_rev and needed = List.rev needed_rev in
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
  | ELeaf (g, _, _, _) -> not (List.exists (fun b -> match b.b_tag with User (_, Some []) -> true | _ -> false) g)
  | ESplit (_, _, _, brs) -> List.for_all (fun (_, e) -> splits_struct e) brs

let rec equations f = function
  | ELeaf (_, _, env, rhs) -> [ (apps (Const (Def f)) env, rhs) ]
  | ESplit (_, _, _, brs) -> List.concat_map (fun (_, e) -> equations f e) brs

(* ** Compilation *)

let check_equation r sg f (i, (lhs, rhs)) =
  match convert ~sg (E.fuel_of r) lhs rhs with
  | ConvEqual u -> E.emit r (AtEquation (f, i)) [ EvConv (lhs, rhs, u) ]; Ok ()
  | ConvOutOfFuel -> E.emit r (AtEquation (f, i)) []; Error (NoFuelAt (AtEquation (f, i), lhs))
  | _ -> E.emit r (AtEquation (f, i)) []; E.refuse (REquation (f, i, lhs, rhs))

(* The signature with the history and the instances the function needs,
   its type, its body, and what [out] reads off the elaborated tree. *)
let compile_with r out sg fn =
  let f = fn.fn_name and x = fn.fn_struct in
  let* g0, goal0, env0 = case (start fn) in
  let* si = case (prepare_split sg g0 goal0 x (varying fn)) in
  let sv = si.si_var and gn = si.si_gen in
  let d = sv.sv_desc and params = sv.sv_params and theta = sv.sv_indices in
  let* () = match sv.sv_prim with Some pr -> E.refuse (RCase (CNotFamily (x, prim_type pr))) | None -> Ok () in
  let n = List.length g0 in
  let rc = { rec_name = f; rec_arity = n; rec_struct = sv.sv_level; rec_params = List.length d.ind_params;
             rec_indices = theta; rec_tail = gn.gn_tail; rec_names = List.map (fun (y, _, _) -> y) fn.fn_args;
             rec_strategy = fn.fn_strategy } in
  let name = d.ind_name in
  let* sg1, root, needed, e =
    match fn.fn_strategy with
    | Direct ->
        let* () = match fn.fn_tree with
          | Split (y, _) when y = x -> Ok ()
          | _ -> E.refuse (RCase (CRoot x)) in
        let* e = case (elaborate_with sg (varying fn) (fun k -> Aux (k + 1)) g0 goal0 env0 fn.fn_tree) in
        let* t, needed = translate r sg rc e in
        Ok (sg, t, needed, e)
    | History ->
        let q = List.length theta in
        let* j = motive_level r sg rc g0 x gn in
        let* sg1 = ensure_below r sg name j in
        let p = motive gn in
        let seeds = List.map (fun (l, a) ->
            { b_tag = (match at_level g0 l with Some b -> b.b_tag | None -> Anon); b_type = a })
            (combine gn.gn_seeds gn.gn_seed_types) in
        let table = apps (Const (Def (below_name name j)))
            (List.map (lift (q + 1)) params @ [ lift (q + 1) p ] @ vars 0 (q + 1)) in
        let g1, goal1, sb = introduce g0 gn (seeds @ [ { b_tag = Aux 0; b_type = table } ]) (vars 1 (q + 1)) in
        let* e = case (elaborate sg1 g1 goal1 (List.map (subst sb) env0) fn.fn_tree) in
        let* t, needed = translate r sg1 rc e in
        let step = lams (q + 1) (Lam (lams (List.length gn.gn_tail) t)) in
        Ok (sg1, apps (Const (Def (recbelow_name name j)))
                   (params @ [ p; step ] @ List.map (var_at n) (gn.gn_seeds @ gn.gn_tail)), needed, e)
  in
  let* () = if splits_struct e then Ok () else E.refuse (RCase (CUnsplit x)) in
  let* sg2 = fold_ok (fun sg (d, k) -> E.ensure_elim r sg d k) sg1 needed in
  Ok (sg2, pis (List.map (fun b -> b.b_type) (List.rev g0)) goal0, lams n root, out e)

let compile_term r sg fn = compile_with r (equations fn.fn_name) sg fn

(* The function as a δ-constant, then its equations by conversion. *)
let compile r sg fn =
  let* sg0, a, b, eqs = compile_term r sg fn in
  let* sg' = E.define r sg0 fn.fn_name a b in
  let* () = iter_ok (check_equation r sg' fn.fn_name) (List.mapi (fun i e -> (i, e)) eqs) in
  Ok sg'

let compile_checked spec fuel sg fn = E.run spec fuel (fun r -> compile r sg fn)

(* Several functions in turn, each in the signature of those before. *)
let compile_all spec fuel sg fns = E.run spec fuel (fun r -> fold_ok (fun sg fn -> compile r sg fn) sg fns)
