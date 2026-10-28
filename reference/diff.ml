(* Compare the native algorithm 1 with the Rocq extract: classification
   answers and diagnostics, generated motives, methods, eliminator types
   and ι-rules, and registrations with their complete logs (every stage
   with its checker events) and answers.  The native side also meets the
   kernel's hand-written descriptions and signatures.  The comparisons,
   runs and counter it shares with algorithm 2 are in test_support.ml. *)

module X = Deptypes
module N = Pts_native
module En = Elim_native
module L = Looping
module Co = Constants
module Fa = Families
module Da = Data

open Extracted
open Conversions
open Test_support

(* ** Comparisons *)

(* The answer of classification in both modes and, for a description, its
   motives, methods, eliminator types and ι-rules at every level. *)
let compare_declaration label raw =
  let xraw = raw_to_extracted raw in
  List.iter (fun positivity ->
      let mode = match positivity with En.Checked -> label | En.Bypass -> label ^ "/bypass" in
      let native = En.classify_decl_with positivity raw in
      equal (mode ^ "/classify")
        (result_to_extracted desc_to_extracted decl_error_to_extracted native)
        (X.classify_decl_with (positivity_to_extracted positivity) xraw);
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
              let rules = En.iota_rules d j in
              equal_list (at ^ "/rules")
                ~describe:(fun i -> match List.nth_opt rules i with Some r -> ", " ^ r.En.rule_ctor | None -> "")
                (List.map rule_to_extracted rules) (X.iota_rules xd j))
            levels)
    [ En.Checked; En.Bypass ]

let fuel = 300

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

(* The suite of algorithm 1. *)
let run () =
  let count = counter () in
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
  let nat = registered "Nat" (compare_script "Nat" predicative fuel [ Declare (Da.raw_nat, [ 0 ]) ]) in
  expect "sig/Nat" (fst nat) (Co.base_signature true);
  let double_type = L.build [] (L.arrow Co.nat Co.nat) and double_body = L.build [] Co.double_body in
  let double = registered "double"
      (compare_script ~sg:nat "double" predicative fuel [ Define ("double", double_type, double_body) ]) in
  expect "sig/double" (fst double) (Co.signature true);
  let chain = [ Da.raw_nat; Da.raw_vec; Da.raw_w; Da.raw_tr ] in
  let families = registered "families"
      (compare_script "families" predicative fuel (List.map (fun raw -> Declare (raw, [ 0 ])) chain)) in
  expect "sig/families" (fst families) Fa.signature;
  let self_body = L.build [] (L.abs [ "n" ] (Co.double (L.name "n"))) in
  let diagonal_steps b diagonal = [
    DeclareBypassing (Da.with_mk (L.arrow Da.d b), [ 0 ]);
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
    "Nat at three levels", empty, [ Declare (Da.raw_nat, levels) ];
    "Nat twice", nat, [ Declare (Da.raw_nat, [ 0 ]) ];
    "elimNat twice", nat, [ DeclareElim ("Nat", 0) ];
    "undeclared", nat, [ DeclareElim ("Foo", 0) ];
    "ensure elimNat[0]", nat, [ EnsureElim ("Nat", 0) ];
    "ensure elimNat[1]", nat, [ EnsureElim ("Nat", 1); EnsureElim ("Nat", 1) ];
    "Nat without instances", empty, [ Declare (Da.raw_nat, []); EnsureElim ("Nat", 0) ];
    "List", empty, [ Declare (Da.raw_list, levels) ];
    "Tree", empty, [ Declare (Da.raw_tree, [ 0 ]) ];
    "W", empty, [ Declare (Da.raw_w, [ 0; 1 ]) ];
    "Vec without Nat", empty, [ Declare (Da.raw_vec, [ 0 ]) ];
    "Vec over Nat", nat, [ Declare (Da.raw_vec, [ 0; 1 ]) ];
    "Tr over Nat", nat, [ Declare (Da.raw_tr, [ 0 ]) ];
    "Void Unit Bool", empty,
      [ Declare (Da.raw_void, [ 0; 1 ]); Declare (Da.raw_unit, [ 0 ]);
        Declare (Da.raw_bool, levels) ];
    "negative", empty, [ Declare (Da.raw_negative, [ 0 ]) ];
    "non-strict", empty, [ Declare (Da.raw_non_strict, [ 0 ]) ];
    "non-strict bypassed", empty, [ DeclareBypassing (Da.raw_non_strict, [ 0 ]) ];
    "double twice", double, [ Define ("double", double_type, double_body) ];
    "double self-referring", nat, [ Define ("double", double_type, self_body) ];
    "double no type", nat, [ Define ("double", L.build [] Co.zero, double_body) ];
    "double ill-typed", nat, [ Define ("double", double_type, L.build [] Co.zero) ];
    "Unit_1", empty, [ EnsureUnit 1; EnsureUnit 1; EnsureUnit 0; EnsureUnit 2 ];
    "ensure an inactive instance", tmp, [ EnsureElim ("Nat", 0) ];
    "a type of a type through a redex", one_sg, [ Define ("f", N.Const (N.Def "one"), N.BTrue) ];
  ];
  List.iter (fun (label, raw) ->
      ignore (compare_script ("register/" ^ label) predicative fuel [ Declare (raw, [ 0 ]) ]))
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
        "Nat", empty, [ Declare (Da.raw_nat, [ 0; 1 ]) ];
        "Vec", nat, [ Declare (Da.raw_vec, [ 0 ]) ];
        "Tr", empty, [ Declare (Da.raw_tr, [ 0 ]) ];
        "Unit_1", empty, [ EnsureUnit 1 ];
        "diagonal", empty, diagonal_steps Da.void Da.void_diagonal;
      ]) specs;
  List.iter (fun f ->
      List.iter (fun (label, sg, steps) ->
          ignore (compare_script ~sg (Printf.sprintf "%s/fuel %d" label f) predicative f steps)) [
        "Nat", empty, [ Declare (Da.raw_nat, [ 0; 1 ]) ];
        "Vec", nat, [ Declare (Da.raw_vec, [ 0 ]) ];
        "families", empty, List.map (fun raw -> Declare (raw, [ 0 ])) chain;
        "diagonal", empty, diagonal_steps Da.bool Da.bool_diagonal;
        "double", nat, [ Define ("double", double_type, double_body) ];
        "RVec", nat, [ Declare (raw_rvec, [ 0 ]) ];
        "one", nat, [ Define ("one", L.build [] (redex Co.nat), L.build [] (Co.succ Co.zero)) ];
        "T as a type", t_sg, [ Define ("b", N.Const (N.Def "T"), N.BTrue) ];
      ]) fuels;

  (* Constructors across the grammar, registered over ℕ. *)
  List.iteri (fun i raw ->
      let label = "grammar/" ^ string_of_int i in
      compare_declaration label raw;
      ignore (compare_script ~sg:nat label predicative fuel [ Declare (raw, [ 0 ]) ]))
    enumerated;

  Printf.printf "reference: %d comparisons with extraction passed (%d declarations across the grammar)\n"
    (count ()) (List.length enumerated)
