(* Compare the native algorithm 2 with the Rocq extract: the history of
   every description at every level and its registration; the elaboration
   of case trees, scope by scope, with every diagnostic; the translation
   with its elaborated tree; and compilations with their complete logs
   (every stage with its checker events, every equation with its common
   normal form) and answers, in the specifications of the kernel and
   short of fuel.  Then programs enumerated across the grammar of case
   trees over ℕ, vectors, binary trees and W-types. *)

module X = Deptypes
module N = Pts_native
module En = Elim_native
module R = Recursion_native
module L = Looping
module Co = Constants
module Fa = Families
module Da = Data
module Pr = Programs

open Extracted

(* ** Conversions of algorithm 2 *)

let atom_to_extracted = function
  | N.Void -> X.NVoid | N.Unit -> X.NUnit | N.Tt -> X.NTt
  | N.Bool -> X.NBool | N.BTrue -> X.NTrue | N.BFalse -> X.NFalse
  | N.Srt s -> X.NSrt (sort_to_extracted s)
  | N.Const g -> X.NConst (gref_to_extracted g)
  | _ -> failwith "a named term with a compound atom"

let rec named_to_extracted = function
  | L.Sort s -> X.NSrt (sort_to_extracted s)
  | L.Name x -> X.NVar x
  | L.Product (x, a, b) -> X.NPi (x, named_to_extracted a, named_to_extracted b)
  | L.Lambda (x, b) -> X.NLam (x, named_to_extracted b)
  | L.Apply (f, a) -> X.NApp (named_to_extracted f, named_to_extracted a)
  | L.Annotate (t, a) -> X.NAnn (named_to_extracted t, named_to_extracted a)
  | L.Arrow (a, b) -> X.NArrow (named_to_extracted a, named_to_extracted b)
  | L.Const t -> atom_to_extracted t
  | L.ElimVoid (c, e) -> X.NElimVoid (named_to_extracted c, named_to_extracted e)
  | L.ElimUnit (c, m, u) -> X.NElimUnit (named_to_extracted c, named_to_extracted m, named_to_extracted u)
  | L.ElimBool (c, x, y, b) ->
      X.NElimBool (named_to_extracted c, named_to_extracted x, named_to_extracted y, named_to_extracted b)
  | L.Sum (x, a, b) -> X.NSigma (x, named_to_extracted a, named_to_extracted b)
  | L.Times (a, b) -> X.NTimes (named_to_extracted a, named_to_extracted b)
  | L.Pairing (a, b) -> X.NPair (named_to_extracted a, named_to_extracted b)
  | L.First t -> X.NFst (named_to_extracted t)
  | L.Second t -> X.NSnd (named_to_extracted t)

let mark_to_extracted = function R.Constant -> X.Constant | R.Varying -> X.Varying
let strategy_to_extracted = function R.Direct -> X.Direct | R.History -> X.History

let rec tree_to_extracted = function
  | R.Leaf t -> X.Leaf (named_to_extracted t)
  | R.Split (x, bs) -> X.Split (x, List.map (fun (c, xs, t) -> ((c, xs), tree_to_extracted t)) bs)

let fun_decl_to_extracted fn = {
  X.fn_name = fn.R.fn_name;
  fn_args = List.map (fun (x, a, mk) -> ((x, named_to_extracted a), mark_to_extracted mk)) fn.R.fn_args;
  fn_result = named_to_extracted fn.R.fn_result;
  fn_struct = fn.R.fn_struct;
  fn_strategy = strategy_to_extracted fn.R.fn_strategy;
  fn_tree = tree_to_extracted fn.R.fn_tree }

let tag_to_extracted = function R.User (x, p) -> X.User (x, p) | R.Anon -> X.Anon | R.Aux k -> X.Aux k
let native_tag = function X.User (x, p) -> R.User (x, p) | X.Anon -> R.Anon | X.Aux k -> R.Aux k

let scope_to_extracted =
  List.map (fun b -> { X.b_tag = tag_to_extracted b.R.b_tag; b_type = term_to_extracted b.R.b_type })

let terms = List.map term_to_extracted

let generalized_to_extracted g = {
  X.gn_seeds = g.R.gn_seeds; gn_tail = g.R.gn_tail; gn_seed_types = terms g.R.gn_seed_types;
  gn_tail_types = terms g.R.gn_tail_types; gn_goal = term_to_extracted g.R.gn_goal }

let prim_to_extracted = function R.PVoid -> X.PVoid | R.PUnit -> X.PUnit | R.PBool -> X.PBool

let split_info_to_extracted si =
  let sv = si.R.si_var in
  { X.si_var = { X.sv_name = sv.R.sv_name; sv_level = sv.R.sv_level; sv_path = sv.R.sv_path;
                 sv_desc = desc_to_extracted sv.R.sv_desc; sv_prim = Option.map prim_to_extracted sv.R.sv_prim;
                 sv_params = terms sv.R.sv_params; sv_indices = sv.R.sv_indices };
    si_gen = generalized_to_extracted si.R.si_gen }

let rec elab_to_extracted = function
  | R.ELeaf (g, goal, env, rhs) -> X.ELeaf (scope_to_extracted g, term_to_extracted goal, terms env, term_to_extracted rhs)
  | R.ESplit (g, goal, si, brs) ->
      X.ESplit (scope_to_extracted g, term_to_extracted goal, split_info_to_extracted si,
                List.map (fun (b, e) -> (b, elab_to_extracted e)) brs)

let case_result value = Diff.result_to_extracted value Diff.case_error_to_extracted
let signature_to_extracted = List.map entry_to_extracted

(* ** Comparisons *)

let assertions_before = !Diff.assertions
let fuel = 1000
let equal = Diff.equal
let predicative = Diff.predicative

let declare raw = Diff.Declare (false, raw, [ 0 ])

(* A compilation of [fns] in turn by both sides from the same signature;
   the two signatures, if both register. *)
let compare_compile ?(spec = predicative) ?(fuel = fuel) label (nsg, xsg) fns =
  let xspec, nspec = spec in
  let native = R.compile_all nspec fuel nsg fns in
  let extracted = X.compile_all xspec fuel xsg (List.map fun_decl_to_extracted fns) in
  Diff.compare_run label native extracted;
  match snd native, snd extracted with
  | En.Registered n, X.Registered x -> Some (n, x)
  | _ -> None

(* The translation with its elaborated tree: the log, the signature, the
   type, the body and the tree. *)
let compare_translation label (nsg, xsg) fn =
  let nlog, nresult = En.run_steps N.predicative fuel (fun r -> R.compile_with r Fun.id nsg fn) in
  equal label
    (Diff.log_to_extracted nlog,
     Diff.result_to_extracted
       (fun (sg, a, b, e) -> (((signature_to_extracted sg, term_to_extracted a), term_to_extracted b), elab_to_extracted e))
       Diff.failure_to_extracted nresult)
    (X.run_traced (X.compile_with X.predicative fuel (fun e -> e) xsg (fun_decl_to_extracted fn)))

(* [start], and the elaboration of its tree in [sg] with [extra] at the
   root, its hypotheses tagged by [tag]. *)
let compare_elaboration ?(extra = []) ?(tag = fun _ -> X.Anon) label (nsg, xsg) fn =
  let nstart = R.start fn and xfn = fun_decl_to_extracted fn in
  let xstart = X.start xfn in
  equal (label ^ "/start")
    (case_result (fun (g, goal, env) -> ((scope_to_extracted g, term_to_extracted goal), terms env)) nstart) xstart;
  match nstart, xstart with
  | Ok (g, goal, env), X.Ok ((xg, xgoal), xenv) ->
      equal (label ^ "/elaborate")
        (case_result elab_to_extracted
           (R.elaborate_with nsg extra (fun k -> native_tag (tag k)) g goal env fn.R.fn_tree))
        (X.elaborate_with xsg extra tag xg xgoal xenv xfn.X.fn_tree)
  | _ -> ()

(* The registration of histories in turn. *)
let compare_below ?(spec = predicative) ?(fuel = fuel) label (nsg, xsg) steps =
  let xspec, nspec = spec in
  let native = En.run nspec fuel (fun r ->
      List.fold_left (fun acc (d, j) -> Result.bind acc (fun sg -> R.ensure_below r sg d j)) (Ok nsg) steps) in
  let extracted =
    X.run_registration
      (List.fold_left (fun m (d, j) -> X.tbind m (fun sg -> X.ensure_below xspec fuel sg d j)) (X.tret xsg) steps) in
  Diff.compare_run label native extracted

let registered = Diff.registered

(* ** Programs enumerated across the grammar of case trees

   Each family of programs: its signature, its arguments with the mark of
   the one that may vary, the strategy, and trees from a pool of leaves.
   The leaves mix calls on fields and deeper subterms, calls on the
   structural argument itself, with an index or a constant changed, not
   applied to all arguments, names out of scope and ill-typed sides. *)
let name = L.name
let app = Pr.app

let over_nat mk strategy tree =
  Pr.fn ~strategy "e" [ Pr.c "n" Co.nat; ("b", Co.nat, mk) ] Co.nat "n" tree

(* Trees of one split with the leaves [l1] of the first constructor and
   [l2] of the second, and of two, the second constructor split again:
   every combination of the pools of their branches. *)
let one_split x (c1, f1) (c2, f2) pool1 pool2 =
  List.concat_map (fun l1 ->
      List.map (fun l2 -> Pr.split x [ Pr.br c1 f1 (Pr.leaf l1); Pr.br c2 f2 (Pr.leaf l2) ]) pool2) pool1

let two_splits x (c1, f1) (c2, f2) y (d1, g1) (d2, g2) pool1 pool2 pool3 =
  List.concat_map (fun l1 ->
      List.concat_map (fun l2 ->
          List.map (fun l3 ->
              Pr.split x
                [ Pr.br c1 f1 (Pr.leaf l1);
                  Pr.br c2 f2 (Pr.split y [ Pr.br d1 g1 (Pr.leaf l2); Pr.br d2 g2 (Pr.leaf l3) ]) ]) pool3) pool2) pool1

let e_nat x y = app "e" [ x; y ]
let n = name "n" and m = name "m" and k = name "k" and b = name "b"

let nat_trees =
  let zero = [ Co.zero; b; e_nat Co.zero b; app "e" [ b ] ] in
  let succ = [
    Co.zero; b; Co.succ (e_nat m b); e_nat m (Co.succ b); e_nat b b; e_nat (Co.succ m) b; app "e" [ m ];
    Pr.plus (e_nat m b) b; Co.succ m; e_nat m m; e_nat k b ] in
  let succ_succ = [
    Co.zero; Co.succ (e_nat k b); e_nat k (Co.succ b); Pr.plus (e_nat k b) b; e_nat (Co.succ k) b;
    e_nat k k; app "e" [ k ]; e_nat m b ] in
  one_split "n" ("zero", []) ("succ", [ "m" ]) zero succ
  @ two_splits "n" ("zero", []) ("succ", [ "m" ]) "m" ("zero", []) ("succ", [ "k" ])
      [ Co.zero; b ] [ Co.zero; b; e_nat Co.zero b ] succ_succ
  @ [ Pr.leaf Co.zero; Pr.split "b" []; Pr.split "m" [];
      Pr.split "n" [ Pr.br "succ" [ "m" ] (Pr.leaf Co.zero); Pr.br "zero" [] (Pr.leaf Co.zero) ];
      Pr.split "n" [ Pr.br "zero" [] (Pr.leaf Co.zero); Pr.br "succ" [ "m" ] (Pr.split "n" []) ];
      Pr.split "n" [ Pr.br "zero" [] (Pr.leaf Co.zero); Pr.br "succ" [ "n" ] (Pr.leaf (e_nat n b)) ] ]

let over_vec mk strategy tree =
  let a = name "A" in
  Pr.fn ~strategy "e" [ Pr.c "A" Pr.type0; Pr.c "n" Co.nat; Pr.c "xs" (Fa.vec a (name "n")); ("c", Co.nat, mk) ]
    Co.nat "xs" tree

let e_vec a n xs c = app "e" [ a; n; xs; c ]
let a = name "A" and c = name "c" and xs' = name "xs'" and ys = name "ys" and j = name "j"

let vec_trees =
  let nil = [ Co.zero; c; e_vec a Co.zero (Fa.vnil a) c ] in
  let cons = [
    Co.zero; c; e_vec a k xs' c; e_vec a (Co.succ k) xs' c; e_vec a k xs' (Co.succ c); e_vec Co.nat k xs' c;
    Co.succ (e_vec a k xs' c); name "x"; app "e" [ a; k; xs' ] ]
  and cons_cons = [
    Co.zero; e_vec a j ys c; Pr.plus (e_vec a j ys c) c; e_vec a (Co.succ j) ys c; e_vec Co.nat j ys c;
    e_vec a j ys (Co.succ c) ] in
  one_split "xs" ("nil", []) ("cons", [ "k"; "x"; "xs'" ]) nil cons
  @ two_splits "xs" ("nil", []) ("cons", [ "k"; "x"; "xs'" ]) "xs'" ("nil", []) ("cons", [ "j"; "y"; "ys" ])
      [ Co.zero ] [ Co.zero; c ] cons_cons

let over_tree mk strategy tree =
  Pr.fn ~strategy "e" [ Pr.c "t" Pr.tree; ("c", Co.nat, mk) ] Co.nat "t" tree

let e_tree t c = app "e" [ t; c ]
let l = name "l" and r = name "r"

let tree_trees =
  let node = [
    Co.zero; c; Pr.plus (e_tree l c) (e_tree r c); e_tree (Pr.node l r) c; Co.succ (e_tree r (Co.succ c));
    e_tree l (e_tree r c) ]
  and node_node = [
    Co.zero; Pr.plus (e_tree (name "r1") c) (e_tree r c); e_tree (name "l1") (e_tree r c); e_tree r c;
    app "e" [ name "l1" ] ] in
  one_split "t" ("leaf", []) ("node", [ "l"; "r" ]) [ Co.zero; c ] node
  @ two_splits "t" ("leaf", []) ("node", [ "l"; "r" ]) "l" ("leaf", []) ("node", [ "l1"; "r1" ])
      [ Co.zero ] [ e_tree r c ] node_node

let over_w mk strategy tree =
  let a = name "A" and b = name "B" in
  Pr.fn ~strategy "e" [ ("A", Pr.type0, mk); Pr.c "B" (L.arrow a Pr.type0); Pr.c "w" (Fa.w a b) ] (Fa.w a b) "w" tree

let w_leaves =
  let a = name "A" and b = name "B" in
  let e x = app "e" [ a; b; x ] in
  [ Fa.sup a b (name "a") (L.abs [ "y" ] (e (L.Apply (name "f", name "y"))));
    Fa.sup a b (name "a") (name "f"); e (name "w");
    Fa.sup a b (name "a") (L.abs [ "y" ] (e (name "f")));
    Fa.sup a b (name "a") (L.abs [ "y" ] (app "e" [ b; a; L.Apply (name "f", name "y") ]));
    Fa.sup a b (name "a") (L.abs [ "y" ] (e (L.Apply (name "f", name "a"))));
    L.abs [ "y" ] (e (L.Apply (name "f", name "y"))) ]

let w_trees = List.map (fun l -> Pr.split "w" [ Pr.br "sup" [ "a"; "f" ] (Pr.leaf l) ]) w_leaves

let enumerate make trees =
  List.concat_map (fun mk ->
      List.concat_map (fun strategy -> List.map (make mk strategy) trees) [ R.Direct; R.History ])
    [ R.Constant; R.Varying ]

let () =
  (* The programs agree with the extract's. *)
  let plus = Pr.def "plus" and plus2 = Pr.def "plus2" in
  List.iter (fun (label, fn, xfn) -> equal ("programs/" ^ label) (fun_decl_to_extracted fn) xfn) [
    "plus", Pr.plus_fn, X.plus_fn; "pow", Pr.pow_fn, X.pow_fn; "f", Pr.f_fn, X.f_fn;
    "half", Pr.half_fn R.History, X.half_fn X.History; "half direct", Pr.half_fn R.Direct, X.half_fn X.Direct;
    "isEven", Pr.even_fn, X.even_fn;
    "append", Pr.append_fn "append" plus, X.append_fn "append" (X.NConst (X.Def "plus"));
    "append2", Pr.append_fn "append2" plus2, X.append_fn "append2" (X.NConst (X.Def "plus2"));
    "plus2", Pr.plus2_fn, X.plus2_fn; "sumv", Pr.sumv_fn, X.sumv_fn;
    "pred", Pr.pred_fn, X.pred_fn; "g", Pr.g_fn, X.g_fn; "ack m", Pr.ack_fn "m", X.ack_fn "m";
    "ack n", Pr.ack_fn "n", X.ack_fn "n";
    "len varying", Pr.len_fn R.Varying (name "A"), X.len_fn X.Varying (X.NVar "A");
    "len Nat", Pr.len_fn R.Constant Co.nat, X.len_fn X.Constant (X.NConst (X.Ind "Nat"));
    "iter", Pr.iter_fn, X.iter_fn; "ack higher", Pr.ack_ho_fn, X.ack_ho_fn;
    "copy", Pr.copy_fn "copy" R.Direct, X.copy_fn "copy" X.Direct;
    "copy_h", Pr.copy_fn "copy_h" R.History, X.copy_fn "copy_h" X.History;
  ];

  (* Signatures, built by both sides. *)
  let script label ?sg steps = registered label (Diff.compare_script ?sg ("rec/" ^ label) predicative 300 steps) in
  let nat = script "Nat" [ declare Da.raw_nat ] in
  let raw_tel =
    { (Da.decl "Tel" [ Da.ctor "tnil" [] (Da.k (N.Ind "Tel"));
                       Da.ctor "tcons" [] (L.arrow Pr.type0 (L.arrow (Da.k (N.Ind "Tel")) (Da.k (N.Ind "Tel")))) ])
      with En.rd_level = 1 } in
  let families =
    script "families" (List.map declare [ Da.raw_nat; Da.raw_vec; Da.raw_tree; Da.raw_w; Da.raw_tr ]
                       @ [ Diff.Declare (false, raw_tel, []) ]) in
  let list = script "List" [ declare Da.raw_list ] in
  let two = script "Two" ~sg:families [ declare Pr.raw_two ] in

  (* The history: its terms for every description at every level. *)
  let classified raw = match En.classify_decl raw with Ok d -> d | Error _ -> failwith raw.En.rd_name in
  let unit_1 = classified { (Da.decl "Unit_1" [ Da.ctor "tt_1" [] (Da.k (N.Ind "Unit_1")) ]) with En.rd_level = 1 } in
  let descriptions = List.map (fun raw -> (raw.En.rd_name, classified raw))
      [ Da.raw_nat; Da.raw_list; Da.raw_vec; Da.raw_tree; Da.raw_w; Da.raw_tr; Da.raw_void; Da.raw_unit;
        Da.raw_bool; raw_tel ] @ [ "Unit_1", unit_1 ] in
  List.iter (fun (label, d) ->
      let xd = desc_to_extracted d in
      List.iter (fun j ->
          let at = Printf.sprintf "history/%s/%d" label j in
          equal (at ^ "/level") (R.history_level d j) (X.history_level xd j);
          equal (at ^ "/names") (R.below_name label j, R.build_name label j, R.recbelow_name label j)
            (X.below_name label j, X.build_name label j, X.recbelow_name label j);
          List.iter (fun (part, native, extracted) ->
              equal (at ^ "/" ^ part) (term_to_extracted (native d j)) (extracted xd j))
            [ "Below type", R.below_type, X.below_type; "Below body", R.below_body, X.below_body;
              "build type", R.build_type, X.build_type; "build body", R.build_body, X.build_body;
              "recBelow type", R.recbelow_type, X.recbelow_type; "recBelow body", R.recbelow_body, X.recbelow_body ])
        Diff.levels)
    descriptions;

  (* Its registration, again, at three levels, without its type. *)
  List.iter (fun (label, sg, steps) -> compare_below ("below/" ^ label) sg steps) [
    "Nat", nat, [ ("Nat", 0); ("Nat", 0); ("Nat", 1); ("Nat", 2) ];
    "families", families, [ ("Vec", 0); ("Tree", 0); ("W", 0); ("W", 1); ("Tr", 0); ("Tel", 0); ("Tel", 1) ];
    "List", list, [ ("List", 0); ("List", 2) ];
    "undeclared", nat, [ ("Vec", 0) ];
  ];
  List.iter (fun (spec_name, spec) ->
      compare_below ~spec ("below/Nat/" ^ spec_name) nat [ ("Nat", 0); ("Nat", 1) ]) Diff.specs;
  List.iter (fun f ->
      compare_below ~fuel:f (Printf.sprintf "below/fuel %d" f) families [ ("Vec", 0); ("Tel", 1) ])
    (Diff.fuels @ [ 55; 89; 144 ]);

  (* Elaboration: the trees of the tests and the programs, and every
     diagnostic. *)
  let elaborations = [
    "half", Pr.half_fn R.History; "append", Pr.append_fn "append" plus; "append swapped", Pr.append_swapped;
    "on length", Pr.on_length Pr.on_length_tree; "W", Pr.w_id; "Tree", Pr.tree_id; "Tr", Pr.tr_id;
    "with varying", Pr.with_varying; "pick", Pr.pick_fn (Pr.on_b (name "n")); "pick rec", Pr.pick_rec;
    "void", Pr.void_fn; "unit", Pr.unit_fn Pr.on_n_u; "Bool structural", Pr.bool_struct;
    "copy", Pr.copy_fn "copy" R.Direct; "sumv", Pr.sumv_fn; "ack", Pr.ack_fn "m";
  ] in
  List.iter (fun (label, fn) -> compare_elaboration ("elaborate/" ^ label) families fn) elaborations;
  List.iter (fun (label, fn) -> compare_elaboration ("elaborate/" ^ label) two fn) [
    "shadowing", Pr.shadowing; "poly", Pr.poly R.History; "pick varying", Pr.pick_varying R.History;
    "indices twice", Pr.two_twice; "indices distinct", Pr.two_distinct ];
  compare_elaboration ~extra:[ 1 ] "elaborate/poly at the root" two (Pr.poly R.History);
  compare_elaboration ~extra:[ 1 ] "elaborate/pick varying at the root" two (Pr.pick_varying R.History);
  compare_elaboration "elaborate/len" list (Pr.len_fn R.Constant (name "A"));
  compare_elaboration "elaborate/len varying" list (Pr.len_fn R.Varying (name "A"));
  compare_elaboration ~extra:[ 1 ] ~tag:(fun k -> X.Aux k) "elaborate/root tail" families Pr.with_varying;
  compare_elaboration ~extra:[ 1 ] ~tag:(fun k -> X.Aux (k + 1)) "elaborate/f" families Pr.f_fn;
  List.iter (fun (label, extra, fn) -> compare_elaboration ~extra ("elaborate/" ^ label) families fn)
    Pr.elaboration_errors;

  (* The lecture's programs, compiled, and their translations. *)
  let direct = registered "direct" (compare_compile "compile/direct" nat [ Pr.plus_fn; Pr.pow_fn; Pr.f_fn ]) in
  let vec = script "Vec over direct" ~sg:direct [ declare Da.raw_vec ] in
  let list_direct = script "List over direct" ~sg:direct [ declare Da.raw_list ] in
  let tree = script "Tree over direct" ~sg:direct [ declare Da.raw_tree ] in
  let w = script "W over direct" ~sg:direct [ declare Da.raw_w ] in
  let half = registered "half" (compare_compile "compile/half" nat [ Pr.half_fn R.History ]) in
  let _even = registered "isEven" (compare_compile "compile/isEven" nat [ Pr.even_fn ]) in
  let append = registered "append" (compare_compile "compile/append" vec [ Pr.append_fn "append" plus; Pr.sumv_fn ]) in
  let _copy = registered "copy"
      (compare_compile "compile/copy" w [ Pr.copy_fn "copy" R.Direct; Pr.copy_fn "copy_h" R.History ]) in
  let _ack = registered "ack" (compare_compile "compile/ack" direct [ Pr.iter_fn; Pr.ack_ho_fn ]) in
  let _pick = registered "pick"
      (compare_compile "compile/pick" nat [ Pr.pick_rec; Pr.void_fn; Pr.unit_fn Pr.on_n_u ]) in
  List.iter (fun (label, sg, fns) -> ignore (compare_compile ("compile/" ^ label) sg fns)) [
    "half directly", nat, [ Pr.half_fn R.Direct ];
    "half twice", half, [ Pr.half_fn R.History ];
    "append2", vec, [ Pr.plus2_fn; Pr.append_fn "append2" plus2 ];
    "g", direct, [ Pr.pred_fn; Pr.g_fn ];
    "ack in m", direct, [ Pr.ack_fn "m" ];
    "ack in n", direct, [ Pr.ack_fn "n" ];
    "len varying", list_direct, [ Pr.len_fn R.Varying (name "A") ];
    "len changed", list_direct, [ Pr.len_fn R.Constant Co.nat ];
    "len", list_direct, [ Pr.len_fn R.Constant (name "A") ];
    "index changed", vec, [ Pr.index_changed ];
    "unsplit", nat, [ Pr.unit_fn (Pr.split "u" [ Pr.br "tt" [] (Pr.leaf (name "n")) ]) ];
    "Bool structural", nat, [ Pr.bool_struct ];
    "sumv reusing the history", append, [ { Pr.sumv_fn with R.fn_name = "sumv2" } ];
    "tree", tree, [ Pr.tree_id ];
    "shadowing", nat, [ Pr.shadowing ];
    "poly", nat, [ Pr.poly R.History ];
    "poly directly", nat, [ Pr.poly R.Direct ];
    "pick varying", nat, [ Pr.pick_varying R.History ];
    "pick varying directly", nat, [ Pr.pick_varying R.Direct ];
    "indices twice", two, [ Pr.two_twice ];
    "indices distinct", two, [ Pr.two_distinct ];
  ];
  List.iter (fun (label, fn) -> ignore (compare_compile ("compile/" ^ label) direct [ fn ])) Pr.call_errors;
  List.iter (fun (label, sg, fn) -> compare_translation ("translate/" ^ label) sg fn) [
    "plus", nat, Pr.plus_fn; "f", nat, Pr.f_fn; "half", nat, Pr.half_fn R.History; "isEven", nat, Pr.even_fn;
    "append", vec, Pr.append_fn "append" plus; "sumv", vec, Pr.sumv_fn; "append2", vec, Pr.append_fn "append2" plus;
    "copy", w, Pr.copy_fn "copy" R.Direct; "copy_h", w, Pr.copy_fn "copy_h" R.History;
    "pick", nat, Pr.pick_rec; "unit", nat, Pr.unit_fn Pr.on_n_u; "ack", direct, Pr.ack_fn "m";
    "half directly", nat, Pr.half_fn R.Direct; "tree", tree, Pr.tree_id;
    "shadowing", nat, Pr.shadowing; "poly", nat, Pr.poly R.History; "poly directly", nat, Pr.poly R.Direct;
    "pick varying", nat, Pr.pick_varying R.History; "indices distinct", two, Pr.two_distinct;
  ];

  (* Other specifications, and every stage short of fuel. *)
  List.iter (fun (spec_name, spec) ->
      List.iter (fun (label, sg, fns) -> ignore (compare_compile ~spec ("compile/" ^ label ^ "/" ^ spec_name) sg fns)) [
        "half", nat, [ Pr.half_fn R.History ]; "plus", nat, [ Pr.plus_fn ]; "copy", w, [ Pr.copy_fn "copy" R.Direct ];
      ]) Diff.specs;
  List.iter (fun f ->
      List.iter (fun (label, sg, fns) ->
          ignore (compare_compile ~fuel:f (Printf.sprintf "compile/%s/fuel %d" label f) sg fns)) [
        "half", nat, [ Pr.half_fn R.History ];
        "isEven", nat, [ Pr.even_fn ];
        "f", nat, [ Pr.plus_fn; Pr.pow_fn; Pr.f_fn ];
        "append", vec, [ Pr.append_fn "append" plus ];
        "copy_h", w, [ Pr.copy_fn "copy_h" R.History ];
        "pick", nat, [ Pr.pick_rec ];
      ]) (Diff.fuels @ [ 55; 89; 144; 233 ]);

  (* Across the grammar of case trees. *)
  let programs =
    List.map (fun fn -> (direct, fn)) (enumerate over_nat nat_trees)
    @ List.map (fun fn -> (vec, fn)) (enumerate over_vec vec_trees)
    @ List.map (fun fn -> (tree, fn)) (enumerate over_tree tree_trees)
    @ List.map (fun fn -> (w, fn)) (enumerate over_w w_trees) in
  List.iteri (fun i (sg, fn) ->
      let label = "grammar/" ^ string_of_int i in
      compare_elaboration label families fn;
      ignore (compare_compile label sg [ fn ]))
    programs;

  Printf.printf "reference: algorithm 2: %d comparisons with extraction passed (%d programs across the grammar)\n"
    (!Diff.assertions - assertions_before) (List.length programs)
