(* Compare the native algorithm 1 with the Rocq extract: classification
   answers and diagnostics, generated motives, methods, eliminator types
   and ι-rules, and registrations with their complete logs (every stage
   with its checker events) and answers.  The native side also meets the
   kernel's hand-written descriptions and signatures. *)

module X = Deptypes
module N = Pts_native
module En = Elim_native
module L = Looping
module Co = Constants
module Fa = Families
module Da = Data

open Extracted

(* ** Conversions of algorithm 1 *)

let raw_to_extracted raw = {
  X.rd_name = raw.En.rd_name;
  rd_params = List.map term_to_extracted raw.En.rd_params;
  rd_indices = List.map term_to_extracted raw.En.rd_indices;
  rd_level = raw.En.rd_level;
  rd_ctors = List.map (fun c -> { X.rc_name = c.En.rc_name; rc_type = term_to_extracted c.En.rc_type })
               raw.En.rd_ctors }

let site_to_extracted = function En.SField l -> X.SField l | En.SResult -> X.SResult

let decl_error_to_extracted = function
  | En.EOpenParams -> X.EOpenParams
  | En.EOpenIndices -> X.EOpenIndices
  | En.ESelfReference -> X.ESelfReference
  | En.EOpenCtor c -> X.EOpenCtor c
  | En.EDuplicateCtor c -> X.EDuplicateCtor c
  | En.ENegative (c, l, a) -> X.ENegative (c, l, term_to_extracted a)
  | En.ENonStrict (c, l, a) -> X.ENonStrict (c, l, term_to_extracted a)
  | En.ENested (c, l, a) -> X.ENested (c, l, term_to_extracted a)
  | En.ENotFamily (c, t) -> X.ENotFamily (c, term_to_extracted t)
  | En.EArity (c, s, t) -> X.EArity (c, site_to_extracted s, term_to_extracted t)
  | En.ENonUniform (c, s, t) -> X.ENonUniform (c, site_to_extracted s, term_to_extracted t)
  | En.EInIndices (c, s, t) -> X.EInIndices (c, site_to_extracted s, term_to_extracted t)

let result_to_extracted value error = function
  | Ok a -> X.Ok (value a)
  | Error e -> X.Err (error e)

let rule_to_extracted r = {
  X.rule_ctor = r.En.rule_ctor;
  rule_ctx = List.map term_to_extracted r.En.rule_ctx;
  rule_lhs = term_to_extracted r.En.rule_lhs;
  rule_rhs = term_to_extracted r.En.rule_rhs;
  rule_type = term_to_extracted r.En.rule_type }

let stage_to_extracted = function
  | En.AtIndType d -> X.AtIndType d
  | En.AtCtorType (d, c) -> X.AtCtorType (d, c)
  | En.AtField (d, c, l) -> X.AtField (d, c, l)
  | En.AtElimType (d, j) -> X.AtElimType (d, j)
  | En.AtRuleLhs (d, j, c) -> X.AtRuleLhs (d, j, c)
  | En.AtRuleRhs (d, j, c) -> X.AtRuleRhs (d, j, c)
  | En.AtDefType f -> X.AtDefType f
  | En.AtDefBody f -> X.AtDefBody f

let reg_error_to_extracted = function
  | En.RClassify e -> X.RClassify (decl_error_to_extracted e)
  | En.RTaken g -> X.RTaken (gref_to_extracted g)
  | En.RUndeclared d -> X.RUndeclared d
  | En.RLevel (c, l, s, i) -> X.RLevel (c, l, sort_to_extracted s, i)
  | En.RNotAType (st, t) -> X.RNotAType (stage_to_extracted st, term_to_extracted t)
  | En.RRejected (st, e) -> X.RRejected (stage_to_extracted st, error_to_extracted e)
  | En.ROpen -> X.ROpen

let failure_to_extracted = function
  | En.Refuse e -> X.Refuse (reg_error_to_extracted e)
  | En.NoFuelAt (st, t) -> X.NoFuelAt (stage_to_extracted st, term_to_extracted t)

let registration_to_extracted = function
  | En.Registered sg -> X.Registered (List.map entry_to_extracted sg)
  | En.Refused e -> X.Refused (reg_error_to_extracted e)
  | En.OutOfFuelAt (st, t) -> X.OutOfFuelAt (stage_to_extracted st, term_to_extracted t)

let log_to_extracted =
  List.map (fun (st, events) -> (stage_to_extracted st, List.map event_to_extracted events))

(* ** Comparisons *)

let assertions = ref 0

let equal label native extracted =
  incr assertions;
  if native <> extracted then failwith ("reference differs from extraction: " ^ label)

(* The native side against the kernel's hand-written terms. *)
let expect label actual expected =
  incr assertions;
  if actual <> expected then failwith ("native reference differs from the kernel's terms: " ^ label)

let levels = [ 0; 1; 2 ]

(* The answer of classification in both modes and, for a description, its
   motives, methods, eliminator types and ι-rules at every level. *)
let compare_declaration label raw =
  let xraw = raw_to_extracted raw in
  List.iter (fun bypass ->
      let mode = if bypass then label ^ "/bypass" else label in
      let native = En.classify_decl_with bypass raw in
      equal (mode ^ "/classify")
        (result_to_extracted desc_to_extracted decl_error_to_extracted native)
        (X.classify_decl_with bypass xraw);
      match native with
      | Error _ -> ()
      | Ok d ->
          let xd = desc_to_extracted d in
          List.iter (fun c ->
              equal (mode ^ "/method/" ^ c.N.ctor_name)
                (term_to_extracted (En.method_type d c)) (X.method_type xd (ctor_to_extracted c)))
            d.N.ind_ctors;
          List.iter (fun j ->
              let at = Printf.sprintf "%s/%d" mode j in
              equal (at ^ "/motive") (term_to_extracted (En.motive_type d j)) (X.motive_type xd j);
              equal (at ^ "/elim") (term_to_extracted (En.elim_type d j)) (X.elim_type xd j);
              equal (at ^ "/rules") (List.map rule_to_extracted (En.iota_rules d j)) (X.iota_rules xd j))
            levels)
    [ false; true ]

let compare_run label (nlog, nanswer) (xlog, xanswer) =
  equal (label ^ "/log") (log_to_extracted nlog) xlog;
  equal (label ^ "/answer") (registration_to_extracted nanswer) xanswer

(* A registration as a script of steps, run by both sides from the same
   signature. *)
type step =
  | Declare of bool * En.raw_decl * int list     (* bypass, the declaration, the levels *)
  | DeclareElim of string * int
  | EnsureElim of string * int
  | Define of string * N.term * N.term
  | EnsureUnit of int

let native_step r sg = function
  | Declare (bypass, raw, js) -> En.declare_with r bypass sg raw js
  | DeclareElim (d, j) -> En.declare_elim r sg d j
  | EnsureElim (d, j) -> En.ensure_elim r sg d j
  | Define (f, ty, body) -> En.define r sg f ty body
  | EnsureUnit l -> En.ensure_unit r sg l

let extracted_step spec fuel sg = function
  | Declare (bypass, raw, js) -> X.declare_with spec fuel bypass sg (raw_to_extracted raw) js
  | DeclareElim (d, j) -> X.declare_elim spec fuel sg d j
  | EnsureElim (d, j) -> X.ensure_elim spec fuel sg d j
  | Define (f, ty, body) -> X.define spec fuel sg f (term_to_extracted ty) (term_to_extracted body)
  | EnsureUnit l -> X.ensure_unit spec fuel sg l

let empty = (N.empty_signature, X.sig_empty)

(* Returns the two signatures registered, if both are. *)
let compare_script ?(sg = empty) label (xspec, nspec) fuel steps =
  let nsg, xsg = sg in
  let native =
    En.run nspec fuel (fun r ->
        List.fold_left (fun acc step -> Result.bind acc (fun sg -> native_step r sg step)) (Ok nsg) steps) in
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

let predicative = (X.predicative, N.predicative)

let specs = [
  "predicative", predicative;
  "pure predicative", (X.pure_predicative, N.pure_predicative);
  "U-", (X.system_u_minus, N.system_u_minus);
  "U", (X.system_u, N.system_u);
  "λ*", (X.lambda_star, N.lambda_star);
]

let fuel = 300
let fuels = [ 0; 1; 2; 3; 5; 8; 13; 21; 34 ]

(* Vectors indexed by [(λX. X) Nat] and a constant of type [(λX. X) Nat]:
   their stages convert through a β-redex, so they run out of fuel at a
   small enough budget.  A constant [T : (λX. X) Type₀] has its type from
   the signature: as the type of another constant it is accepted without
   reduction, and only unfolding its type to a sort needs fuel. *)
let redex ?(level = 0) t =
  L.Apply (L.ann (L.abs [ "X" ] (L.name "X")) (L.arrow (Da.universe level) (Da.universe level)), t)

let raw_rvec =
  let rvec a i = L.call (Da.k (N.Ind "RVec")) [ a; i ] in
  Da.decl "RVec" ~params:[ Da.type0 ] ~indices:[ L.build [ "A" ] (redex Co.nat) ]
    [ Da.ctor "nil" [ "A" ] (rvec (L.name "A") Co.zero);
      Da.ctor "cons" [ "A" ]
        (L.pi "n" (redex Co.nat) (L.pi "x" (L.name "A") (L.pi "xs" (rvec (L.name "A") (L.name "n"))
           (rvec (L.name "A") (Co.succ (L.name "n")))))) ]

(* ** Constructors across the grammar

   E (A : Type₀) : Nat → Type₀ with nil : E A zero and
   c : Πn:Nat. F₁ → F₂ → R: up to two fields drawn from a pool of field
   types inside the grammar and outside it, the result from another pool.
   Every field and result may mention A and n. *)
let e_of a i = L.call (Da.k (N.Ind "E")) [ a; i ]
let a = L.name "A" and n = L.name "n"

let field_pool = [
  a; Co.nat; Da.universe 0; L.Const N.Tt;
  e_of a Co.zero; e_of a n; e_of a (Co.succ n);
  L.pi "y" Co.nat (e_of a (L.name "y"));
  L.pi "y" a (L.pi "z" Co.nat (e_of a (Co.succ (L.name "z"))));
  L.arrow (e_of a Co.zero) Da.void;
  L.arrow (L.arrow (e_of a Co.zero) Da.bool) Da.bool;
  L.pi "y" (e_of a Co.zero) (e_of a Co.zero);
  e_of Da.bool Co.zero;
  e_of a (e_of a Co.zero);
  e_of a (L.Apply (Da.k (N.Ctor ("E", "nil")), a));
  L.Apply (Da.k (N.Ind "E"), a);
  L.Times (e_of a Co.zero, Co.nat);
  L.arrow (L.arrow (e_of a (e_of a Co.zero)) Da.bool) Da.bool;
  L.arrow (e_of a Co.zero) (L.Times (e_of a Co.zero, Co.nat));
  L.Apply (Da.k (N.Elim ("E", 0)), a);
  Da.k (N.Def "E");
]

let result_pool = [
  e_of a Co.zero; e_of a (Co.succ n); e_of Da.bool Co.zero; Co.nat;
  L.Apply (Da.k (N.Ind "E"), a); e_of a (e_of a Co.zero);
]

let rec sequences len pool =
  if len = 0 then [ [] ]
  else [] :: List.concat_map (fun f -> List.map (fun fs -> f :: fs) (sequences (len - 1) pool)) pool

let enumerated =
  List.concat_map (fun fields ->
      List.map (fun result ->
          let body = List.fold_right (fun (i, f) body -> L.pi ("x" ^ string_of_int i) f body)
              (List.mapi (fun i f -> (i, f)) fields) result in
          Da.decl "E" ~params:[ Da.type0 ] ~indices:[ L.build [ "A" ] Co.nat ]
            [ Da.ctor "nil" [ "A" ] (e_of a Co.zero); Da.ctor "c" [ "A" ] (L.pi "n" Co.nat body) ])
        result_pool)
    (sequences 2 field_pool)

let () =
  (* The declarations agree with the extract's. *)
  List.iter (fun (label, raw, xraw) -> equal ("data/" ^ label) (raw_to_extracted raw) xraw) [
    "Nat", Da.raw_nat, X.raw_nat; "List", Da.raw_list, X.raw_list; "Vec", Da.raw_vec, X.raw_vec;
    "Tree", Da.raw_tree, X.raw_tree; "W", Da.raw_w, X.raw_w;
    "Void", Da.raw_void, X.raw_void; "Unit", Da.raw_unit, X.raw_unit; "Bool", Da.raw_bool, X.raw_bool;
    "negative", Da.raw_negative, X.raw_negative; "negative Bool", Da.raw_negative_bool, X.raw_negative_bool;
    "non-strict", Da.raw_non_strict, X.raw_non_strict;
  ];
  equal "data/List desc" (desc_to_extracted Da.list_desc) X.list_desc;
  equal "data/Tree desc" (desc_to_extracted Da.tree_desc) X.tree_desc;

  (* Classification and generation. *)
  let declarations = [
    "Nat", Da.raw_nat; "List", Da.raw_list; "Vec", Da.raw_vec; "Tree", Da.raw_tree; "W", Da.raw_w;
    "Tr", Da.raw_tr; "Void", Da.raw_void; "Unit", Da.raw_unit; "Bool", Da.raw_bool;
    "negative", Da.raw_negative; "negative Bool", Da.raw_negative_bool; "non-strict", Da.raw_non_strict;
  ] @ Da.diagnostics in
  List.iter (fun (label, raw) -> compare_declaration label raw) declarations;

  (* The native descriptions and eliminators are the kernel's. *)
  let classified raw = match En.classify_decl raw with Ok d -> d | Error _ -> failwith raw.En.rd_name in
  List.iter (fun (label, raw, desc) -> expect ("desc/" ^ label) (classified raw) desc) [
    "Nat", Da.raw_nat, Co.nat_desc; "List", Da.raw_list, Da.list_desc; "Vec", Da.raw_vec, Fa.vec_desc;
    "Tree", Da.raw_tree, Da.tree_desc; "W", Da.raw_w, Fa.w_desc; "Tr", Da.raw_tr, Fa.tr_desc;
  ];
  List.iter (fun (label, desc, ty) -> expect ("elim/" ^ label) (En.elim_type desc 0) (L.build [] ty)) [
    "Nat", Co.nat_desc, Co.elim_nat_ty; "Vec", Fa.vec_desc, Fa.elim_vec_ty;
    "W", Fa.w_desc, Fa.elim_w_ty; "Tr", Fa.tr_desc, Fa.elim_tr_ty;
  ];
  (* The kernel contracts the left side of every rule to its right side. *)
  List.iter (fun (sg, desc) ->
      List.iter (fun r -> expect ("rule/" ^ r.En.rule_ctor) (N.iota sg r.En.rule_lhs) (Some r.En.rule_rhs))
        (En.iota_rules desc 0))
    [ Co.signature true, Co.nat_desc; Fa.signature, Fa.vec_desc; Fa.signature, Fa.w_desc;
      Fa.signature, Fa.tr_desc ];

  (* Registration. *)
  let nat = registered "Nat" (compare_script "Nat" predicative fuel [ Declare (false, Da.raw_nat, [ 0 ]) ]) in
  expect "sig/Nat" (fst nat) (Co.base_signature true);
  let double_type = L.build [] (L.arrow Co.nat Co.nat) and double_body = L.build [] Co.double_body in
  let double = registered "double"
      (compare_script ~sg:nat "double" predicative fuel [ Define ("double", double_type, double_body) ]) in
  expect "sig/double" (fst double) (Co.signature true);
  let chain = [ Da.raw_nat; Da.raw_vec; Da.raw_w; Da.raw_tr ] in
  let families = registered "families"
      (compare_script "families" predicative fuel (List.map (fun raw -> Declare (false, raw, [ 0 ])) chain)) in
  expect "sig/families" (fst families) Fa.signature;
  let self_body = L.build [] (L.abs [ "n" ] (Co.double (L.name "n"))) in
  let diagonal_steps b diagonal = [
    Declare (true, Da.with_mk (L.arrow Da.d b), [ 0 ]);
    Define ("unmk", Da.unmk_type b, Da.unmk_body b);
    Define ("delta", L.build [] (L.arrow Da.d b), L.build [] diagonal);
  ] in
  (* The signature of ℕ with an instance whose rules are not active, as
     the one in which a registration checks them. *)
  let nat_desc = classified Da.raw_nat in
  let nat_elim = N.EElim ("Nat", 0, En.elim_type nat_desc 0, false) in
  let tmp =
    (Option.get (N.sig_add (fst nat) nat_elim), Option.get (X.sig_add (snd nat) (entry_to_extracted nat_elim))) in
  (* Constants whose types are redexes. *)
  let one_sg = registered "one"
      (compare_script ~sg:nat "one" predicative fuel
         [ Define ("one", L.build [] (redex Co.nat), L.build [] (Co.succ Co.zero)) ]) in
  let t_sg = registered "T"
      (compare_script "T" predicative fuel [ Define ("T", L.build [] (redex ~level:1 (Da.universe 0)), N.Bool) ]) in
  List.iter (fun (label, sg, steps) -> ignore (compare_script ~sg label predicative fuel steps)) [
    "Nat at three levels", empty, [ Declare (false, Da.raw_nat, levels) ];
    "Nat twice", nat, [ Declare (false, Da.raw_nat, [ 0 ]) ];
    "elimNat twice", nat, [ DeclareElim ("Nat", 0) ];
    "undeclared", nat, [ DeclareElim ("Foo", 0) ];
    "ensure elimNat[0]", nat, [ EnsureElim ("Nat", 0) ];
    "ensure elimNat[1]", nat, [ EnsureElim ("Nat", 1); EnsureElim ("Nat", 1) ];
    "Nat without instances", empty, [ Declare (false, Da.raw_nat, []); EnsureElim ("Nat", 0) ];
    "List", empty, [ Declare (false, Da.raw_list, levels) ];
    "Tree", empty, [ Declare (false, Da.raw_tree, [ 0 ]) ];
    "W", empty, [ Declare (false, Da.raw_w, [ 0; 1 ]) ];
    "Vec without Nat", empty, [ Declare (false, Da.raw_vec, [ 0 ]) ];
    "Vec over Nat", nat, [ Declare (false, Da.raw_vec, [ 0; 1 ]) ];
    "Tr over Nat", nat, [ Declare (false, Da.raw_tr, [ 0 ]) ];
    "Void Unit Bool", empty,
      [ Declare (false, Da.raw_void, [ 0; 1 ]); Declare (false, Da.raw_unit, [ 0 ]);
        Declare (false, Da.raw_bool, levels) ];
    "negative", empty, [ Declare (false, Da.raw_negative, [ 0 ]) ];
    "non-strict", empty, [ Declare (false, Da.raw_non_strict, [ 0 ]) ];
    "non-strict bypassed", empty, [ Declare (true, Da.raw_non_strict, [ 0 ]) ];
    "double twice", double, [ Define ("double", double_type, double_body) ];
    "double self-referring", nat, [ Define ("double", double_type, self_body) ];
    "double no type", nat, [ Define ("double", L.build [] Co.zero, double_body) ];
    "double ill-typed", nat, [ Define ("double", double_type, L.build [] Co.zero) ];
    "Unit_1", empty, [ EnsureUnit 1; EnsureUnit 1; EnsureUnit 0; EnsureUnit 2 ];
    "ensure an inactive instance", tmp, [ EnsureElim ("Nat", 0) ];
    "a type of a type through a redex", one_sg, [ Define ("f", N.Const (N.Def "one"), N.BTrue) ];
  ];
  List.iter (fun (label, raw) ->
      ignore (compare_script ("register/" ^ label) predicative fuel [ Declare (false, raw, [ 0 ]) ]))
    Da.diagnostics;

  (* The diagonal of the bypass mode and what checks in its signature. *)
  let void_sg = registered "void diagonal"
      (compare_script "void diagonal" predicative fuel (diagonal_steps Da.void Da.void_diagonal)) in
  let bool_sg = registered "bool diagonal"
      (compare_script "bool diagonal" predicative fuel (diagonal_steps Da.bool Da.bool_diagonal)) in
  compare_check "δ (mk δ) : Void" void_sg predicative fuel [] Da.diagonal N.Void;
  compare_normalize "δ (mk δ) evaluated" void_sg 6 Da.diagonal;
  compare_check "tt : IsTrue (δ (mk δ))" bool_sg predicative fuel [] N.Tt
    (L.build [] (Da.is_true (L.Const Da.diagonal)));
  compare_normalize "double 1" double fuel (N.App (N.Const (N.Def "double"), L.build [] (Co.succ Co.zero)));
  let unit1 = registered "Unit_1" (compare_script "Unit_1 alone" predicative fuel [ EnsureUnit 1 ]) in
  equal "unit_at" (List.map (fun l -> term_to_extracted (En.unit_at l)) levels) (List.map X.unit_at levels);
  equal "tt_at" (List.map (fun l -> term_to_extracted (En.tt_at l)) levels) (List.map X.tt_at levels);
  equal "unit_name" (List.map En.unit_name levels) (List.map X.unit_name levels);
  compare_check "tt_1 : Unit_1" unit1 predicative fuel [] (En.tt_at 1) (En.unit_at 1);
  compare_check "tt : Unit_1" unit1 predicative fuel [] N.Tt (En.unit_at 1);

  (* The entry points. *)
  compare_run "declare_checked" (En.declare_checked N.predicative fuel [] Da.raw_nat [ 0 ])
    (X.declare_checked X.predicative fuel [] X.raw_nat [ 0 ]);
  compare_run "declare_bypassing" (En.declare_bypassing N.predicative fuel [] Da.raw_negative [ 0 ])
    (X.declare_bypassing X.predicative fuel [] X.raw_negative [ 0 ]);
  compare_run "define_checked" (En.define_checked N.predicative fuel (fst nat) "double" double_type double_body)
    (X.define_checked X.predicative fuel (snd nat) "double" (term_to_extracted double_type)
       (term_to_extracted double_body));

  (* A rule with the hypothesis dropped from its right side, checked where
     the instance has no active rules. *)
  let succ_rule = List.nth (En.iota_rules nat_desc 0) 1 in
  let broken = { succ_rule with En.rule_rhs = (match succ_rule.En.rule_rhs with N.App (f, _) -> f | t -> t) } in
  List.iter (fun (label, rule) ->
      let nlog, nresult = En.run_steps N.predicative fuel (fun r -> En.check_rule r (fst tmp) "Nat" 0 rule) in
      equal label (log_to_extracted nlog, result_to_extracted Fun.id failure_to_extracted nresult)
        (X.run_traced (X.check_rule X.predicative fuel (snd tmp) "Nat" 0 (rule_to_extracted rule))))
    [ "rule of succ", succ_rule; "broken rule of succ", broken ];

  (* Other specifications, and every stage short of fuel. *)
  List.iter (fun (spec_name, spec) ->
      List.iter (fun (label, sg, steps) -> ignore (compare_script ~sg (label ^ "/" ^ spec_name) spec fuel steps)) [
        "Nat", empty, [ Declare (false, Da.raw_nat, [ 0; 1 ]) ];
        "Vec", nat, [ Declare (false, Da.raw_vec, [ 0 ]) ];
        "Tr", empty, [ Declare (false, Da.raw_tr, [ 0 ]) ];
        "Unit_1", empty, [ EnsureUnit 1 ];
        "diagonal", empty, diagonal_steps Da.void Da.void_diagonal;
      ]) specs;
  List.iter (fun f ->
      List.iter (fun (label, sg, steps) ->
          ignore (compare_script ~sg (Printf.sprintf "%s/fuel %d" label f) predicative f steps)) [
        "Nat", empty, [ Declare (false, Da.raw_nat, [ 0; 1 ]) ];
        "Vec", nat, [ Declare (false, Da.raw_vec, [ 0 ]) ];
        "families", empty, List.map (fun raw -> Declare (false, raw, [ 0 ])) chain;
        "diagonal", empty, diagonal_steps Da.bool Da.bool_diagonal;
        "double", nat, [ Define ("double", double_type, double_body) ];
        "RVec", nat, [ Declare (false, raw_rvec, [ 0 ]) ];
        "one", nat, [ Define ("one", L.build [] (redex Co.nat), L.build [] (Co.succ Co.zero)) ];
        "T as a type", t_sg, [ Define ("b", N.Const (N.Def "T"), N.BTrue) ];
      ]) fuels;

  (* Constructors across the grammar, registered over ℕ. *)
  List.iteri (fun i raw ->
      let label = "grammar/" ^ string_of_int i in
      compare_declaration label raw;
      ignore (compare_script ~sg:nat label predicative fuel [ Declare (false, raw, [ 0 ]) ]))
    enumerated;

  Printf.printf "reference: %d comparisons with extraction passed (%d declarations across the grammar)\n"
    !assertions (List.length enumerated)
