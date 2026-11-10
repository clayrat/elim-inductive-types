(* The raw declarations of theories/Data and theories/Tests.v, assembled
   independently with the kernel's named builder: ℕ, lists, vectors,
   binary trees, W-types, the family Tr, Void, Unit and Bool, the
   declarations outside the grammar with the diagonal of the bypass mode,
   and one declaration for every diagnostic. *)

open Named
open Elim_native
module P = Pts_native
module Co = Constants
module Fa = Families

let k g = Const (P.Const g)
let universe i = Sort (P.Univ i)
let type0 = P.Srt (P.Univ 0)
let void = Const P.Void and unit = Const P.Unit and bool = Const P.Bool

let ctor c names t = { rc_name = c; rc_type = build names t }

let decl ?(params = []) ?(indices = []) ?(sort = P.Univ 0) name ctors =
  { rd_name = name; rd_params = params; rd_indices = indices; rd_sort = sort; rd_ctors = ctors }

(* ℕ, lists, vectors over ℕ, binary trees, W-types. *)
let raw_nat = decl "Nat" [ ctor "zero" [] Co.nat; ctor "succ" [] (arrow Co.nat Co.nat) ]

let list a = Apply (k (P.Ind "List"), a)

let raw_list =
  decl "List" ~params:[ type0 ]
    [ ctor "nil" [ "A" ] (list (name "A"));
      ctor "cons" [ "A" ] (arrows [ name "A"; list (name "A") ] (list (name "A"))) ]

let list_desc = {
  P.ind_name = "List"; ind_params = [ type0 ]; ind_indices = []; ind_sort = P.Univ 0; ind_elim = P.AllSorts;
  ind_ctors = [
    { P.ctor_name = "nil"; ctor_fields = []; ctor_indices = [] };
    { P.ctor_name = "cons"; ctor_fields = [ P.FArg (P.Var 0); P.FRec ([], []) ]; ctor_indices = [] };
  ];
}

let raw_vec =
  decl "Vec" ~params:[ type0 ] ~indices:[ build [ "A" ] Co.nat ]
    [ ctor "nil" [ "A" ] (Fa.vec (name "A") Co.zero);
      ctor "cons" [ "A" ]
        (pi "n" Co.nat (pi "x" (name "A") (pi "xs" (Fa.vec (name "A") (name "n"))
           (Fa.vec (name "A") (Co.succ (name "n")))))) ]

let tree = k (P.Ind "Tree")

let raw_tree = decl "Tree" [ ctor "leaf" [] tree; ctor "node" [] (arrows [ tree; tree ] tree) ]

let tree_desc = {
  P.ind_name = "Tree"; ind_params = []; ind_indices = []; ind_sort = P.Univ 0; ind_elim = P.AllSorts;
  ind_ctors = [
    { P.ctor_name = "leaf"; ctor_fields = []; ctor_indices = [] };
    { P.ctor_name = "node"; ctor_fields = [ P.FRec ([], []); P.FRec ([], []) ]; ctor_indices = [] };
  ];
}

let raw_w =
  decl "W" ~params:[ type0; build [ "A" ] (arrow (name "A") (universe 0)) ]
    [ ctor "sup" [ "B"; "A" ]
        (pi "a" (name "A")
           (arrow (arrow (Apply (name "B", name "a")) (Fa.w (name "A") (name "B")))
              (Fa.w (name "A") (name "B")))) ]

(* Tr A h x: a recursive field whose index mentions its position, an
   earlier field and a parameter; two positions; a field after a recursive
   one. *)
let raw_tr =
  let tr = Fa.tr (name "A") (name "h") and ps = [ "h"; "A" ] in
  decl "Tr" ~params:[ type0; build [ "A" ] (Fa.binary (name "A")) ] ~indices:[ build ps (name "A") ]
    [ ctor "leaf" ps (pi "a" (name "A") (tr (name "a")));
      ctor "node" ps (pi "a" (name "A") (pi "f" (pi "y" (name "A") (tr Fa.h_a_y)) (tr (name "a"))));
      ctor "fork" ps
        (pi "a" (name "A")
           (pi "f" (pi "y" (name "A") (pi "z" (name "A") (tr Fa.h_a_y_z))) (tr (name "a"))));
      ctor "twin" ps
        (pi "a" (name "A") (pi "l" (pi "y" (name "A") (tr Fa.h_a_y))
           (pi "b" (name "A") (pi "r" (pi "y" (name "A") (tr Fa.h_b_y)) (tr Fa.h_a_b))))) ]

(* Void, Unit and Bool as declarations. *)
let simple name cs = decl name (List.map (fun c -> { rc_name = c; rc_type = P.Const (P.Ind name) }) cs)
let raw_void = simple "Void" []
let raw_unit = simple "Unit" [ "tt" ]
let raw_bool = simple "Bool" [ "true"; "false" ]

(* D with mk : field → D; outside the grammar, the diagonal in the bypass
   mode: unmk (mk g) ↝ g and δ := λd. unmk d d. *)
let d = k (P.Ind "D")
let with_mk field = decl "D" [ ctor "mk" [] (arrow field d) ]
let raw_negative = with_mk (arrow d void)
let raw_negative_bool = with_mk (arrow d bool)
let raw_non_strict = with_mk (arrow (arrow d bool) bool)

let mk = k (P.Ctor ("D", "mk"))
let unmk = k (P.Def "unmk")
let delta = k (P.Def "delta")

let unmk_type b = build [] (arrows [ d; d ] b)
let unmk_body b =
  build []
    (abs [ "d" ]
       (call (k (P.Elim ("D", P.Univ 0)))
          [ ann (abs [ "_" ] (arrow d b)) (arrow d (universe 0)); abs [ "g" ] (name "g"); name "d" ]))

let bnot x = ElimBool (ann (abs [ "_" ] bool) (arrow bool (universe 0)), Const P.BFalse, Const P.BTrue, x)
let is_true b = ElimBool (ann (abs [ "_" ] (universe 0)) (arrow bool (universe 1)), unit, void, b)
let void_diagonal = abs [ "d" ] (call unmk [ name "d"; name "d" ])
let bool_diagonal = abs [ "d" ] (bnot (call unmk [ name "d"; name "d" ]))
let diagonal = build [] (Apply (delta, Apply (mk, delta)))

(* The propositions of Data/Logic.v, in the sort Prop, and data with a
   proof field. *)
let prop = Sort P.Prp
let prp = P.Srt P.Prp
let false_ = k (P.Ind "False")
let raw_true = decl ~sort:P.Prp "True" [ ctor "I" [] (k (P.Ind "True")) ]
let raw_false = decl ~sort:P.Prp "False" []

let raw_eq =
  let eq a x y = call (k (P.Ind "eq")) [ a; x; y ] in
  decl ~sort:P.Prp "eq" ~params:[ type0; build [ "A" ] (name "A") ] ~indices:[ build [ "a"; "A" ] (name "A") ]
    [ ctor "refl" [ "a"; "A" ] (eq (name "A") (name "a") (name "a")) ]

let connective d ctors =
  let c = call (k (P.Ind d)) [ name "A"; name "B" ] in
  decl ~sort:P.Prp d ~params:[ prp; prp ] (List.map (fun (n, fields) -> ctor n [ "B"; "A" ] (arrows fields c)) ctors)

let raw_and = connective "and" [ "conj", [ name "A"; name "B" ] ]
let raw_or = connective "or" [ "or_introl", [ name "A" ]; "or_intror", [ name "B" ] ]

(* [D A P] with [c : Πx:A. P x → D A P], A at the level [i]. *)
let exists_at ?(sort = P.Prp) d c i =
  decl ~sort d ~params:[ P.Srt (P.Univ i); build [ "A" ] (arrow (name "A") prop) ]
    [ ctor c [ "P"; "A" ]
        (pi "x" (name "A") (arrow (Apply (name "P", name "x")) (call (k (P.Ind d)) [ name "A"; name "P" ]))) ]

let raw_ex = exists_at "ex" "ex_intro" 0
let raw_ex1 = exists_at "ex1" "ex1_intro" 1
let raw_sig = exists_at ~sort:(P.Univ 0) "sig" "exist" 0
let raw_sigT0 = exists_at ~sort:(P.Univ 0) "sigT0" "existT0" 1

let raw_accp =
  let accp x = call (k (P.Ind "AccP")) [ name "A"; name "R"; x ] in
  decl ~sort:P.Prp "AccP" ~params:[ prp; build [ "A" ] (arrows [ name "A"; name "A" ] prop) ]
    ~indices:[ build [ "R"; "A" ] (name "A") ]
    [ ctor "introP" [ "R"; "A" ]
        (pi "x" (name "A")
           (arrow (pi "y" (name "A") (arrow (call (name "R") [ name "y"; name "x" ]) (accp (name "y"))))
              (accp (name "x")))) ]

let boolp = k (P.Ind "BoolP")
let raw_boolp = decl ~sort:P.Prp "BoolP" [ ctor "trueP" [] boolp; ctor "falseP" [] boolp ]
let raw_badp =
  let badp = k (P.Ind "BadP") in
  decl ~sort:P.Prp "BadP" [ ctor "mkBad" [] (arrow (arrow badp false_) badp) ]

(* [mkBigP : (Type₀ → BigP) → BigP] of Tests.v: a recursive field over
   [Type₀], so its history is one level above its motive. *)
let raw_bigp =
  let bigp = k (P.Ind "BigP") in
  decl ~sort:P.Prp "BigP" [ ctor "mkBigP" [] (arrow (arrow (universe 0) bigp) bigp) ]

(* [observe_proof p := elim_BoolP[Type₀] (λ_. Bool) true false p]. *)
let observe_proof p =
  build [] (call (k (P.Elim ("BoolP", P.Univ 0))) [ abs [ "_" ] bool; Const P.BTrue; Const P.BFalse; p ])

(* A declaration of E with the one constructor c, as in Tests.v. *)
let e = k (P.Ind "E")
let one ?params ?indices c = decl "E" ?params ?indices [ { rc_name = "c"; rc_type = c } ]

let diagnostics = [
  "negative domain", one (build [] (arrow (arrow e e) e));
  "nested", one (build [] (arrow (list e) e));
  "non-uniform field", one ~params:[ type0 ] (build [ "A" ] (arrow (Apply (e, bool)) (Apply (e, name "A"))));
  "non-uniform result", one ~params:[ type0 ] (build [ "A" ] (Apply (e, bool)));
  "in the indices of a field",
    one ~indices:[ type0 ] (build [] (arrow (Apply (e, Apply (e, unit))) (Apply (e, unit))));
  "in the indices of the result", one ~indices:[ type0 ] (build [] (Apply (e, Apply (e, unit))));
  "arity", one (build [] (Apply (e, bool)));
  "not a family", one (build [] (arrow bool bool));
  "open parameters", one ~params:[ P.Var 0 ] (build [] e);
  "open indices", one ~indices:[ P.Var 0 ] (build [] e);
  "open parameters and indices", one ~params:[ P.Var 0 ] ~indices:[ P.Var 1 ] (build [ "x" ] e);
  "open constructor", one (P.Pi (P.Var 0, P.Const (P.Ind "E")));
  "self-reference", one ~params:[ build [] e ] (build [ "x" ] e);
  "self-reference in the indices", one ~indices:[ build [] e ] (build [] (Apply (e, unit)));
  "a constructor in the parameters", one ~params:[ build [] (k (P.Ctor ("E", "c"))) ] (build [ "x" ] e);
  "duplicate constructor", decl "E" [ ctor "c" [] e; ctor "c" [] e ];
  "a field in Type₀", one (build [] (arrow (universe 0) e));
  "a field that is no type", one (build [] (arrow (Const P.Tt) e));
]
