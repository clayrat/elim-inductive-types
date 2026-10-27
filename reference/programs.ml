(* The programs of theories/Programs and the case trees of
   theories/Tests.v, assembled independently with the kernel's named
   builder: the direct translation of [+], [pow] and [f]; [half] and
   [isEven] through the history; [append], [plus2] and [sumv]; the
   rejected [g] and Ackermann's equations, [len], and Ackermann's
   function of higher order; [copy] on W; and the trees of the tests,
   among them one for every diagnostic of elaboration and the splits of
   the primitive types. *)

open Looping
open Recursion_native
module P = Pts_native
module Co = Constants
module Fa = Families
module Da = Data

let def f = Da.k (P.Def f)
let app f args = call (def f) args
let type0 = Da.universe 0
let nat = Co.nat and zero = Co.zero and succ = Co.succ
let tt = Const P.Tt

let fn ?(strategy = History) name args result struct_ tree =
  { fn_name = name; fn_args = args; fn_result = result; fn_struct = struct_; fn_strategy = strategy;
    fn_tree = tree }

let c x a = (x, a, Constant)
let v x a = (x, a, Varying)
let split x branches = Split (x, branches)
let br ctor fields t = (ctor, fields, t)
let leaf t = Leaf t

let rec num n = if n = 0 then zero else succ (num (n - 1))

(* ** Programs.Direct *)

let plus a b = app "plus" [ a; b ]
let pow n = app "pow" [ n ]

let plus_fn =
  fn ~strategy:Direct "plus" [ c "n" nat; c "m" nat ] nat "n"
    (split "n" [ br "zero" [] (leaf (name "m")); br "succ" [ "k" ] (leaf (succ (plus (name "k") (name "m")))) ])

let pow_fn =
  fn ~strategy:Direct "pow" [ c "n" nat ] type0 "n"
    (split "n" [ br "zero" [] (leaf Da.unit); br "succ" [ "k" ] (leaf (Times (nat, pow (name "k")))) ])

let f_fn =
  fn ~strategy:Direct "f" [ c "n" nat; v "b" nat ] (pow (name "n")) "n"
    (split "n"
       [ br "zero" [] (leaf tt);
         br "succ" [ "k" ] (leaf (Pairing (name "b", app "f" [ name "k"; succ (name "b") ]))) ])

(* ** Programs.Half *)

let half_fn strategy =
  fn ~strategy "half" [ c "n" nat ] nat "n"
    (split "n"
       [ br "zero" [] (leaf zero);
         br "succ" [ "m" ]
           (split "m" [ br "zero" [] (leaf zero); br "succ" [ "k" ] (leaf (succ (app "half" [ name "k" ]))) ]) ])

let even_fn =
  fn "isEven" [ c "n" nat ] type0 "n"
    (split "n"
       [ br "zero" [] (leaf Da.unit);
         br "succ" [ "m" ]
           (split "m" [ br "zero" [] (leaf Da.void); br "succ" [ "k" ] (leaf (app "isEven" [ name "k" ])) ]) ])

(* ** Programs.Append *)

let vec = Fa.vec

let append_fn nm add =
  let a = name "A" in
  fn nm [ c "A" type0; c "n" nat; c "m" nat; c "xs" (vec a (name "n")); c "ys" (vec a (name "m")) ]
    (vec a (call add [ name "n"; name "m" ])) "xs"
    (split "xs"
       [ br "nil" [] (leaf (name "ys"));
         br "cons" [ "k"; "x"; "xs'" ]
           (leaf (Fa.vcons a (call add [ name "k"; name "m" ]) (name "x")
                    (app nm [ a; name "k"; name "m"; name "xs'"; name "ys" ]))) ])

let plus2_fn =
  fn ~strategy:Direct "plus2" [ c "n" nat; c "m" nat ] nat "m"
    (split "m" [ br "zero" [] (leaf (name "n")); br "succ" [ "k" ] (leaf (succ (app "plus2" [ name "n"; name "k" ]))) ])

let sumv_fn =
  fn "sumv" [ c "n" nat; c "v" (vec nat (name "n")); c "w" (pow (name "n")) ] nat "v"
    (split "v"
       [ br "nil" [] (leaf zero);
         br "cons" [ "k"; "x"; "v'" ]
           (leaf (plus (name "x")
                    (plus (First (name "w")) (app "sumv" [ name "k"; name "v'"; Second (name "w") ])))) ])

(* ** Programs.Rejected *)

let pred_fn =
  fn ~strategy:Direct "pred" [ c "n" nat ] nat "n"
    (split "n" [ br "zero" [] (leaf zero); br "succ" [ "k" ] (leaf (name "k")) ])

let g_fn =
  fn "g" [ c "n" nat ] nat "n"
    (split "n" [ br "zero" [] (leaf zero); br "succ" [ "k" ] (leaf (app "g" [ app "pred" [ name "k" ] ])) ])

let ack_fn x =
  let mk y = if y = x then Constant else Varying in
  let ack a b = app "ack" [ a; b ] in
  fn "ack" [ ("m", nat, mk "m"); ("n", nat, mk "n") ] nat x
    (split "m"
       [ br "zero" [] (leaf (succ (name "n")));
         br "succ" [ "k" ]
           (split "n"
              [ br "zero" [] (leaf (ack (name "k") (succ zero)));
                br "succ" [ "l" ] (leaf (ack (name "k") (ack (succ (name "k")) (name "l")))) ]) ])

let list a = Da.list a

let len_fn mk a' =
  fn "len" [ ("A", type0, mk); c "xs" (list (name "A")) ] nat "xs"
    (split "xs" [ br "nil" [] (leaf zero); br "cons" [ "x"; "ys" ] (leaf (succ (app "len" [ a'; name "ys" ]))) ])

let iter_fn =
  fn ~strategy:Direct "iter" [ c "g" (arrow nat nat); c "n" nat ] nat "n"
    (split "n"
       [ br "zero" [] (leaf (Apply (name "g", succ zero)));
         br "succ" [ "k" ] (leaf (Apply (name "g", app "iter" [ name "g"; name "k" ]))) ])

let ack_ho_fn =
  fn ~strategy:Direct "ack" [ c "m" nat ] (arrow nat nat) "m"
    (split "m"
       [ br "zero" [] (leaf (abs [ "n" ] (succ (name "n"))));
         br "succ" [ "k" ] (leaf (abs [ "n" ] (app "iter" [ app "ack" [ name "k" ]; name "n" ]))) ])

(* ** Programs.Copy *)

let copy_fn nm strategy =
  let a = name "A" and b = name "B" in
  fn ~strategy nm [ c "A" type0; c "B" (arrow a type0); c "w" (Fa.w a b) ] (Fa.w a b) "w"
    (split "w"
       [ br "sup" [ "a"; "f" ]
           (leaf (Fa.sup a b (name "a") (abs [ "b" ] (app nm [ a; b; Apply (name "f", name "b") ])))) ])

(* ** Tests.v: case trees *)

(* [append] with its branches in the other order. *)
let append_swapped =
  let a = name "A" in
  { (append_fn "append" (def "plus")) with
    fn_tree =
      split "xs"
        [ br "cons" [ "n'"; "x"; "xs'" ]
            (leaf (Fa.vcons a (plus (name "n'") (name "m")) (name "x")
                     (app "append" [ a; name "n'"; name "m"; name "xs'"; name "ys" ])));
          br "nil" [] (leaf (name "ys")) ] }

(* A hypothesis on the length of the vector split. *)
let on_length t =
  fn "g"
    [ c "A" type0; c "P" (arrow nat type0); c "n" nat; c "h" (Apply (name "P", name "n"));
      c "v" (vec (name "A") (name "n")) ]
    (Apply (name "P", name "n")) "v" t

let on_length_tree =
  split "v" [ br "nil" [] (leaf (name "h")); br "cons" [ "k"; "x"; "w" ] (leaf (name "h")) ]

let rebuild args result x t = fn "id" args result x t

let w_id =
  let a = name "A" and b = name "B" in
  rebuild [ c "A" type0; c "B" (arrow a type0); c "w" (Fa.w a b) ] (Fa.w a b) "w"
    (split "w" [ br "sup" [ "a"; "f" ] (leaf (Fa.sup a b (name "a") (name "f"))) ])

let tree = Da.tree
let node l r = call (Da.k (P.Ctor ("Tree", "node"))) [ l; r ]

let tree_id =
  rebuild [ c "t" tree ] tree "t"
    (split "t" [ br "leaf" [] (leaf (Da.k (P.Ctor ("Tree", "leaf")))); br "node" [ "l"; "r" ] (leaf (node (name "l") (name "r"))) ])

let tr_id =
  let a = name "A" and h = name "h" in
  rebuild [ c "A" type0; c "h" (Fa.binary a); c "x" a; c "t" (Fa.tr a h (name "x")) ] (Fa.tr a h (name "x")) "t"
    (split "t"
       [ br "twin" [ "a"; "l"; "b"; "r" ] (leaf (Fa.twin a h (name "a") (name "l") (name "b") (name "r")));
         br "leaf" [ "a" ] (leaf (Fa.leaf a h (name "a")));
         br "fork" [ "a"; "f" ] (leaf (Fa.fork a h (name "a") (name "f")));
         br "node" [ "a"; "f" ] (leaf (Fa.node a h (name "a") (name "f"))) ])

let with_varying =
  rebuild [ c "n" nat; v "b" nat ] nat "n" (split "n" [ br "zero" [] (leaf (name "b")); br "succ" [ "m" ] (leaf (name "b")) ])

(* One tree for every diagnostic of elaboration, with the [extra] tail of
   its root. *)
let elaboration_errors = [
  "unbound split", [], on_length (split "q" []);
  "split of a type", [], on_length (split "A" []);
  "missing branch", [], on_length (split "v" [ br "nil" [] (leaf (name "h")) ]);
  "fields", [], on_length (split "v" [ br "nil" [] (leaf (name "h")); br "cons" [ "k"; "x" ] (leaf (name "h")) ]);
  "field twice", [],
    on_length (split "v" [ br "nil" [] (leaf (name "h")); br "cons" [ "k"; "k"; "w" ] (leaf (name "h")) ]);
  "field generalized", [],
    on_length (split "v" [ br "nil" [] (leaf (name "h")); br "cons" [ "k"; "h"; "w" ] (leaf (name "h")) ]);
  "unbound leaf", [],
    on_length (split "v" [ br "nil" [] (leaf (name "nope")); br "cons" [ "k"; "x"; "w" ] (leaf (name "h")) ]);
  "parameters generalized", [],
    rebuild [ c "P" (arrow nat type0); c "n" nat; c "v" (vec (Apply (name "P", name "n")) (name "n")) ] nat "v"
      (split "v" [ br "nil" [] (leaf zero); br "cons" [ "k"; "x"; "w" ] (leaf zero) ]);
  "indices", [], rebuild [ c "A" type0; c "n" nat; c "v" (vec (name "A") (succ (name "n"))) ] nat "v" (split "v" []);
  "duplicate argument", [], rebuild [ c "n" nat; c "n" nat ] nat "n" (leaf zero);
  "no structural argument", [], rebuild [ c "n" nat ] nat "m" (leaf zero);
  "varying parameter", [ 0 ], on_length on_length_tree;
  "index on a varying argument", [ 2 ],
    rebuild [ c "A" type0; c "h" (Fa.binary (name "A")); v "b" type0; c "x" (name "b");
              c "t" (Fa.tr (name "A") (name "h") (name "x")) ] nat "t" (split "t" []);
  "branches twice", [],
    on_length (split "v" [ br "nil" [] (leaf (name "h")); br "nil" [] (leaf (name "h")) ]);
  "unknown branch", [],
    on_length (split "v" [ br "nil" [] (leaf (name "h")); br "snoc" [ "k"; "x"; "w" ] (leaf (name "h")) ]);
]

(* ** Tests.v: the compiler *)

let plus_with t = { plus_fn with fn_tree = split "n" [ br "zero" [] (leaf (name "m")); br "succ" [ "k" ] (leaf t) ] }

let call_errors = [
  "root no split", { plus_fn with fn_tree = leaf (name "m") };
  "call arity", plus_with (succ (app "plus" [ name "k" ]));
  "constant changed", plus_with (succ (plus (name "k") zero));
]

(* [append] whose call changes the index [n]. *)
let index_changed =
  let a = name "A" in
  { (append_fn "append" (def "plus")) with
    fn_tree =
      split "xs"
        [ br "nil" [] (leaf (name "ys"));
          br "cons" [ "k"; "x"; "xs'" ]
            (leaf (Fa.vcons a (plus (name "k") (name "m")) (name "x")
                     (app "append" [ a; name "m"; name "m"; name "xs'"; name "ys" ]))) ] }

(* ** Tests.v: splits of the primitive types *)

let is_true b = Da.is_true b
let absurd_nat x = ElimVoid (ann (abs [ "_" ] nat) (arrow Da.void type0), x)

let pick_args = [ c "n" nat; c "b" Da.bool; c "c" (is_true (name "b")) ]
let on_b t = split "b" [ br "false" [] (leaf (absurd_nat (name "c"))); br "true" [] (leaf t) ]

let pick_fn t = rebuild pick_args nat "n" t

let pick_rec =
  fn "pick" pick_args nat "n"
    (split "n"
       [ br "zero" [] (on_b zero);
         br "succ" [ "k" ] (leaf (succ (app "pick" [ name "k"; name "b"; name "c" ]))) ])

let void_fn = fn "absurd" [ c "n" nat; c "v" Da.void ] nat "n" (split "v" [])

let unit_fn t = fn "unit_id" [ c "n" nat; c "u" Da.unit ] nat "n" t

let on_n_u =
  split "n"
    [ br "zero" [] (split "u" [ br "tt" [] (leaf zero) ]);
      br "succ" [ "k" ] (split "u" [ br "tt" [] (leaf (succ (app "unit_id" [ name "k"; tt ]))) ]) ]

let bool_struct =
  rebuild [ c "b" Da.bool ] nat "b" (split "b" [ br "true" [] (leaf zero); br "false" [] (leaf zero) ])

(* ** Beyond the tests of Rocq *)

(* A field named like an argument: the split of [m] in the branch of
   [succ m] splits the field, and in its branch of [zero] the name [m] is
   the argument again. *)
let shadowing =
  rebuild [ c "n" nat; c "m" nat ] nat "n"
    (split "n"
       [ br "zero" [] (leaf (name "m"));
         br "succ" [ "m" ] (split "m" [ br "zero" [] (leaf (name "m")); br "succ" [ "k" ] (leaf (name "k")) ]) ])

(* A varying type [B] and [x : B]: [x] joins the tail through [B], and the
   goal mentions the tail. *)
let poly strategy =
  fn ~strategy "poly" [ c "n" nat; v "B" type0; c "x" (name "B") ] (name "B") "n"
    (split "n"
       [ br "zero" [] (leaf (name "x"));
         br "succ" [ "m" ] (leaf (app "poly" [ name "m"; name "B"; name "x" ])) ])

(* [pick] with [b] varying: [c : IsTrue b] follows it into the tail. *)
let pick_varying strategy =
  fn ~strategy "pick" [ c "n" nat; v "b" Da.bool; c "c" (is_true (name "b")) ] nat "n"
    (split "n"
       [ br "zero" [] (on_b zero);
         br "succ" [ "k" ] (leaf (succ (app "pick" [ name "k"; name "b"; name "c" ]))) ])

(* A family with two indices, [two : Πn:Nat. Two n n]; a split of
   [p : Two n n] has the index [n] twice. *)
let two a b = call (Da.k (P.Ind "Two")) [ a; b ]

let raw_two =
  Da.decl "Two" ~indices:[ build [] nat; build [] nat ] [ Da.ctor "two" [] (pi "n" nat (two (name "n") (name "n"))) ]

let two_twice = rebuild [ c "n" nat; c "p" (two (name "n") (name "n")) ] nat "p" (split "p" [])

let two_distinct =
  rebuild [ c "n" nat; c "m" nat; c "p" (two (name "n") (name "m")) ] nat "p"
    (split "p" [ br "two" [ "k" ] (leaf (name "k")) ])
