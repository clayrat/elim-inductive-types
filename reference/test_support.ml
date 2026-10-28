(* The infrastructure of the differential tests of both algorithms
   against the extract: the counter of comparisons; comparisons of
   values, of lists and of registrations with their logs; runs of
   registration scripts, of the checker and of normalization by both
   sides; and the specifications and budgets they run in.  The suites of
   algorithm 1 (diff.ml) and algorithm 2 (diff_recursion.ml) build on it,
   with the conversions of conversions.ml. *)

module X = Deptypes
module N = Pts_native
module En = Elim_native

open Extracted
open Conversions

(* ** Counting *)

let assertions = ref 0

(* The comparisons made from now on: each suite reports its own, in
   whatever order the suites run. *)
let counter () =
  let before = !assertions in
  fun () -> !assertions - before

(* ** Comparisons *)

let differs label detail = failwith ("reference differs from extraction: " ^ label ^ detail)

let equal label native extracted =
  incr assertions;
  if native <> extracted then differs label ""

(* Two lists compared entry by entry: on a difference, the first entry
   that differs, and what [describe] says of the native one. *)
let equal_list ?(describe = fun _ -> "") label native extracted =
  incr assertions;
  if native <> extracted then
    let rec first i = function a :: l, b :: l' when a = b -> first (i + 1) (l, l') | _ -> i in
    let i = first 0 (native, extracted) in
    differs label
      (Printf.sprintf " (entry %d of %d native and %d extracted%s)"
         i (List.length native) (List.length extracted) (describe i))

(* The native side against the kernel's hand-written terms. *)
let expect label actual expected =
  incr assertions;
  if actual <> expected then failwith ("native reference differs from the kernel's terms: " ^ label)

(* ** Registrations *)

let show_stage = function
  | En.AtIndType d -> Printf.sprintf "AtIndType %s" d
  | En.AtCtorType (d, c) -> Printf.sprintf "AtCtorType (%s, %s)" d c
  | En.AtField (d, c, l) -> Printf.sprintf "AtField (%s, %s, %d)" d c l
  | En.AtElimType (d, j) -> Printf.sprintf "AtElimType (%s, %d)" d j
  | En.AtRuleLhs (d, j, c) -> Printf.sprintf "AtRuleLhs (%s, %d, %s)" d j c
  | En.AtRuleRhs (d, j, c) -> Printf.sprintf "AtRuleRhs (%s, %d, %s)" d j c
  | En.AtDefType f -> Printf.sprintf "AtDefType %s" f
  | En.AtDefBody f -> Printf.sprintf "AtDefBody %s" f
  | En.AtMotive (f, x) -> Printf.sprintf "AtMotive (%s, %s)" f x
  | En.AtEquation (f, i) -> Printf.sprintf "AtEquation (%s, %d)" f i

(* The stage of the [i]-th entry of a native log. *)
let log_entry nlog i =
  match List.nth_opt nlog i with Some (st, _) -> ", native " ^ show_stage st | None -> ""

let compare_run label (nlog, nanswer) (xlog, xanswer) =
  equal_list ~describe:(log_entry nlog) (label ^ "/log") (log_to_extracted nlog) xlog;
  equal (label ^ "/answer") (registration_to_extracted nanswer) xanswer

(* A registration as a script of steps, run by both sides from the same
   signature. *)
type step =
  | Declare of En.raw_decl * int list            (* the declaration, the levels *)
  | DeclareBypassing of En.raw_decl * int list   (* in the demonstration mode *)
  | DeclareElim of string * int
  | EnsureElim of string * int
  | Define of string * N.term * N.term
  | EnsureUnit of int

let native_step r sg = function
  | Declare (raw, js) -> En.declare_with r En.Checked sg raw js
  | DeclareBypassing (raw, js) -> En.declare_with r En.Bypass sg raw js
  | DeclareElim (d, j) -> En.declare_elim r sg d j
  | EnsureElim (d, j) -> En.ensure_elim r sg d j
  | Define (f, ty, body) -> En.define r sg f ty body
  | EnsureUnit l -> En.ensure_unit r sg l

let extracted_step spec fuel sg = function
  | Declare (raw, js) -> X.declare_with spec fuel X.Checked sg (raw_to_extracted raw) js
  | DeclareBypassing (raw, js) -> X.declare_with spec fuel X.Bypass sg (raw_to_extracted raw) js
  | DeclareElim (d, j) -> X.declare_elim spec fuel sg d j
  | EnsureElim (d, j) -> X.ensure_elim spec fuel sg d j
  | Define (f, ty, body) -> X.define spec fuel sg f (term_to_extracted ty) (term_to_extracted body)
  | EnsureUnit l -> X.ensure_unit spec fuel sg l

let empty = (N.empty_signature, X.sig_empty)

(* Returns the two signatures registered, if both are. *)
let compare_script ?(sg = empty) label (xspec, nspec) fuel steps =
  let nsg, xsg = sg in
  let native = En.run nspec fuel (fun r -> Common_native.fold_ok (native_step r) nsg steps) in
  let extracted =
    X.run_registration
      (List.fold_left (fun m step -> X.tbind m (fun sg -> extracted_step xspec fuel sg step))
         (X.tret xsg) steps) in
  compare_run label native extracted;
  match snd native, snd extracted with
  | En.Registered nsg, X.Registered xsg -> Some (nsg, xsg)
  | _ -> None

let registered label = function
  | Some sgs -> sgs
  | None -> failwith ("not registered: " ^ label)

(* ** Runs of the kernel *)

let compare_check label (nsg, xsg) (xspec, nspec) fuel gamma term expected =
  let events, answer = N.run_check ~sg:nsg nspec fuel gamma term expected in
  equal label
    (List.map event_to_extracted events, answer_to_extracted Fun.id answer)
    (X.run_check xspec xsg fuel (List.map term_to_extracted gamma) (term_to_extracted term)
       (term_to_extracted expected))

let compare_normalize label (nsg, xsg) fuel term =
  let trace, result = N.normalize_trace ~sg:nsg fuel term in
  equal label (List.map term_to_extracted trace, eval_to_extracted result)
    (X.normalize_trace xsg fuel (term_to_extracted term))

(* ** Specifications and budgets *)

let predicative = (X.predicative, N.predicative)

let specs = [
  "predicative", predicative;
  "pure predicative", (X.pure_predicative, N.pure_predicative);
  "U-", (X.system_u_minus, N.system_u_minus);
  "U", (X.system_u, N.system_u);
  "λ*", (X.lambda_star, N.lambda_star);
]

let fuels = [ 0; 1; 2; 3; 5; 8; 13; 21; 34 ]
let levels = [ 0; 1; 2 ]

