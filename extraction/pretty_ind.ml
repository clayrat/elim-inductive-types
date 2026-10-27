(* Printing for algorithms 1 and 2, on top of the kernel's printer:
   descriptions, eliminator types with the motive named P, ι-rules with
   the variables of their context named, the diagnostics, stages and
   answers of classification, registration and compilation, the defining
   equations of compiled functions with their pattern variables named,
   and the redexes of normal-order traces.

   The extract defines its own [length], [map], [nth] and [rev]; this file
   uses the ones of [List] qualified. *)
open Deptypes
open Pretty

let plural n word = string_of_int n ^ " " ^ word ^ if n = 1 then "" else "s"

(* A binder whose type ends in a sort, such as a family [B : A → Type₀],
   is named like a type. *)
let rec ends_in_sort = function Pi (_, b) -> ends_in_sort b | Srt _ -> true | _ -> false

let name_for a names = fresh (if ends_in_sort a then type_names else term_names) names

(* Prints [t] with its first binders named by [given]: [Some x] names one,
   [None] chooses a name by its type; the rest of [t] is named by the
   printer. *)
let pp_binders ?(depth = max_int) ?(names = []) given t =
  let rec go names acc given t =
    match given, t with
    | g :: rest, Pi (a, b) ->
        let x = match g with Some x -> x | None -> name_for a names in
        go (x :: names) (acc ^ "Π" ^ x ^ ":" ^ pp_term ~depth ~names a ^ ". ") rest b
    | _ -> acc ^ pp_term ~depth ~names t
  in
  go names "" given t

(* The names of the parameters of [d], innermost first. *)
let param_names d = List.fold_left (fun names a -> name_for a names :: names) [] d.ind_params

let params_given d = List.map (fun _ -> None) d.ind_params

(* ** Descriptions *)

let pp_field_kind = function
  | FArg _ -> "non-recursive"
  | FRec ([], _) -> "recursive"
  | FRec (bs, _) -> "recursive with " ^ plural (List.length bs) "position"

(* [D : Π(Δ). Πθ̄. Type_i], then each constructor at its type rebuilt from
   the description, with the kinds of its fields. *)
let pp_desc ?(depth = max_int) d =
  let ctor c =
    let kinds = match c.ctor_fields with
      | [] -> ""
      | fs -> "    [" ^ String.concat ", " (List.map pp_field_kind fs) ^ "]" in
    c.ctor_name ^ " : " ^ pp_binders ~depth (params_given d) (ctor_type d c) ^ kinds in
  (d.ind_name ^ " : " ^ pp_term ~depth (ind_type d)) :: List.map ctor d.ind_ctors

let elim_name d j = pp_gref (Elim (d.ind_name, j))

(* The type of [elim_D[j]], its motive named P. *)
let pp_elim_type ?(depth = max_int) d j =
  pp_binders ~depth (params_given d @ [ Some "P" ]) (elim_type d j)

(* The method of [c], in the context of the parameters and P. *)
let pp_method ?(depth = max_int) d c =
  pp_term ~depth ~names:("P" :: param_names d) (method_type d c)

(* The names of the context of a rule, innermost first: the fields, fresh
   for the rest, the methods named after their constructors, P, the
   parameters. *)
let rule_names d r =
  let c = List.find (fun c -> c.ctor_name = r.rule_ctor) d.ind_ctors in
  let outer = List.rev_map (fun c -> "m_" ^ c.ctor_name) d.ind_ctors @ [ "P" ] @ param_names d in
  List.fold_left (fun names _ -> fresh term_names names :: names) outer c.ctor_fields

(* [lhs ⇝ rhs], both of the type of the rule. *)
let pp_rule ?(depth = max_int) d r =
  let names = rule_names d r in
  pp_term ~depth ~names r.rule_lhs ^ "  ⇝  " ^ pp_term ~depth ~names r.rule_rhs

(* ** Diagnostics *)

let pp_site = function SField i -> "field " ^ string_of_int i | SResult -> "the result"

let pp_decl_error ?(depth = max_int) e =
  let pp = pp_term ~depth in
  let field c i a = c ^ ", field " ^ string_of_int i ^ " : " ^ pp a ^ ": " in
  match e with
  | EOpenParams -> "a parameter mentions a variable bound after it"
  | EOpenIndices -> "an index mentions a variable bound after it"
  | ESelfReference -> "the parameters or indices mention the type declared"
  | EOpenCtor c -> c ^ ": a free variable past the parameters"
  | EDuplicateCtor c -> "two constructors named " ^ c
  | ENegative (c, i, a) -> field c i a ^ "the type occurs in a negative position"
  | ENonStrict (c, i, a) ->
      field c i a ^ "the type occurs positively, but the field is not Πȳ. D Δ v̄"
  | ENested (c, i, a) -> field c i a ^ "the type occurs nested under another former"
  | ENotFamily (c, t) -> c ^ ": the result " ^ pp t ^ " is not the type declared"
  | EArity (c, s, t) -> c ^ ", " ^ pp_site s ^ ": " ^ pp t ^ " has the wrong number of arguments"
  | ENonUniform (c, s, t) -> c ^ ", " ^ pp_site s ^ ": " ^ pp t ^ " changes the parameters"
  | EInIndices (c, s, t) -> c ^ ", " ^ pp_site s ^ ": the type occurs in the indices of " ^ pp t

let pp_stage = function
  | AtIndType d -> "the type of " ^ d
  | AtCtorType (_, c) -> "the type of " ^ c
  | AtField (_, c, i) -> "the level of field " ^ string_of_int i ^ " of " ^ c
  | AtElimType (d, j) -> "the type of " ^ pp_gref (Elim (d, j))
  | AtRuleLhs (_, _, c) -> "the ι-rule of " ^ c ^ ", left side"
  | AtRuleRhs (_, _, c) -> "the ι-rule of " ^ c ^ ", right side"
  | AtDefType f -> "the type of " ^ f
  | AtDefBody f -> "the body of " ^ f
  | AtMotive (f, x) -> "the motive of the split of " ^ x ^ " in " ^ f
  | AtEquation (f, i) -> "equation " ^ string_of_int i ^ " of " ^ f

(* The diagnostics of case trees and calls of algorithm 2; their terms lie
   in the scope of the tree, printed with de Bruijn indices. *)
let pp_case_error ?(depth = max_int) e =
  let pp = pp_term ~depth in
  match e with
  | CDuplicateArg x -> "two arguments named " ^ x
  | CNoStruct x -> "the structural argument " ^ x ^ " is no argument"
  | CUnbound x -> x ^ " is not in scope"
  | CNotFamily (x, t) -> "the type " ^ pp t ^ " of " ^ x ^ " is no declared family"
  | CIndices (x, t) -> "the indices of the type " ^ pp t ^ " of " ^ x ^ " are not distinct variables"
  | CGeneralize (x, y) -> x ^ " depends on " ^ y ^ ", which the split generalizes"
  | CParams (x, y) -> "the parameters of the type of " ^ x ^ " mention " ^ y ^ ", which varies: non-uniform recursion"
  | CBranches x -> "the branches of the split of " ^ x ^ " are not its constructors, each once"
  | CFields (c, n) -> c ^ " has " ^ plural n "field"
  | CFieldName (c, x) -> "the field " ^ x ^ " of " ^ c ^ " is named twice or like a generalized variable"
  | CRoot x -> "the root is no split of " ^ x
  | CUnsplit x -> "a leaf is reached without a split of the structural argument " ^ x
  | CMotiveSort (x, s) -> "the motive of the split of " ^ x ^ " lives in " ^ pp_sort s ^ ", no universe"
  | CCallArity t -> "a call not applied to all the arguments: " ^ pp t
  | CNotStructural t -> "a call on no strict subterm of the structural argument: " ^ pp t
  | CNotImmediate t -> "a call on a subterm deeper than a field, without the history: " ^ pp t
  | CIndexChanged (x, t) -> "the index " ^ x ^ " is not that of the subterm: " ^ pp t
  | CConstantChanged (x, t) -> "the constant argument " ^ x ^ " changes: " ^ pp t

let pp_reg_error ?(depth = max_int) = function
  | RClassify e -> "not in the grammar: " ^ pp_decl_error ~depth e
  | RTaken g -> pp_gref g ^ " is in the signature already"
  | RUndeclared d -> d ^ " is not declared"
  | RLevel (c, i, s, l) ->
      "field " ^ string_of_int i ^ " of " ^ c ^ " lives in " ^ pp_sort s ^ ", above "
      ^ pp_sort (Univ l)
  | RNotAType (st, t) -> pp_stage st ^ ": its type unfolds to " ^ pp_term ~depth t ^ ", not a sort"
  | RRejected (st, e) -> pp_stage st ^ ": " ^ pp_error ~depth e
  | ROpen -> "an entry with a free variable"
  | RCase e -> pp_case_error ~depth e
  | REquation (f, i, l, r) ->
      "equation " ^ string_of_int i ^ " of " ^ f ^ " does not hold: " ^ pp_term ~depth l ^ " ≢ "
      ^ pp_term ~depth r

let pp_entry = function
  | EInd d -> d.ind_name
  | EElim (d, j, _, active) -> pp_gref (Elim (d, j)) ^ if active then "" else " (rules not active)"
  | EDef (f, _, _) -> f

let pp_registration ?(depth = max_int) = function
  | Registered sg -> "registered; the signature: " ^ String.concat ", " (List.map pp_entry sg)
  | Refused e -> "refused: " ^ pp_reg_error ~depth e
  | OutOfFuelAt (st, t) ->
      "undecided at " ^ pp_stage st ^ ": out of fuel while typing " ^ pp_term ~depth t

(* A registration log: each stage with the number of its checker events. *)
let pp_log log =
  List.map (fun (st, evs) -> pp_stage st ^ ": " ^ plural (List.length evs) "event") log

(* ** Algorithm 2 *)

let pp_strategy = function Direct -> "directly" | History -> "through the history"

(* The equations of [fn], each with the names of its scope, innermost
   first, from one run of the translation; [sg] is the signature it was
   compiled in, or one extending it. *)
let compiled_equations sg fn =
  match named_equations predicative prog_fuel sg fn with
  | None -> []
  | Some nes -> List.map (fun (names, (l, r)) -> (names, l, r)) nes

let pp_equation ?(depth = max_int) (names, l, r) =
  pp_term ~depth ~names l ^ " ≡ " ^ pp_term ~depth ~names r

(* The redexes of the kernel's [contract], by name. *)
let redex sg t =
  match t with
  | App (Lam _, _) -> Some "β"
  | App _ -> (
      match iota sg t with
      | Some _ -> Some (match spine_head t with Const g -> "ι " ^ pp_gref g | _ -> "ι")
      | None -> None)
  | Ann _ -> Some "∷"
  | ElimUnit (_, _, Tt) -> Some "ι elimUnit"
  | ElimBool (_, _, _, (BTrue | BFalse)) -> Some "ι elimBool"
  | Fst (Pair _) -> Some "fst"
  | Snd (Pair _) -> Some "snd"
  | Const g -> Option.map (fun _ -> "δ " ^ pp_gref g) (sig_delta sg g)
  | _ -> None

let components t t' =
  match (t, t') with
  | Pi (a, b), Pi (a', b') | Sigma (a, b), Sigma (a', b') | App (a, b), App (a', b')
  | Pair (a, b), Pair (a', b') | ElimVoid (a, b), ElimVoid (a', b') ->
      [ (a, a'); (b, b') ]
  | Lam b, Lam b' | Fst b, Fst b' | Snd b, Snd b' -> [ (b, b') ]
  | ElimUnit (c, m, u), ElimUnit (c', m', u') -> [ (c, c'); (m, m'); (u, u') ]
  | ElimBool (c, x, y, b), ElimBool (c', x', y', b') -> [ (c, c'); (x, x'); (y, y'); (b, b') ]
  | _ -> []

(* The redex a step [t ⇝ t'] of normal order contracts.  Normal order
   contracts a redex where it finds one, and descends otherwise, so the
   first redex on the path to the one component the step changes is
   it.  "?" if there is none. *)
let rec step_redex sg t t' =
  match redex sg t with
  | Some r -> r
  | None -> (
      match List.filter (fun (a, b) -> not (term_eqb a b)) (components t t') with
      | [ (a, b) ] -> step_redex sg a b
      | _ -> "?")

let rec trace_redexes sg = function
  | a :: (b :: _ as rest) -> step_redex sg a b :: trace_redexes sg rest
  | _ -> []

(* The redexes of a trace, consecutive repeats counted. *)
let pp_redexes rs =
  let rec group = function
    | [] -> []
    | r :: rest ->
        let rec count n = function r' :: rest' when r' = r -> count (n + 1) rest' | rest' -> (n, rest') in
        let n, rest' = count 1 rest in
        (if n = 1 then r else r ^ " ×" ^ string_of_int n) :: group rest'
  in
  String.concat " · " (group rs)
