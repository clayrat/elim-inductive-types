(* The layout of the binders of a method, native (MethodLayout.v): each
   field of the constructor in order, a recursive one followed right away
   by its hypothesis.  Algorithm 1 builds the method types on it, algorithm
   2 the methods of the history and the binders of the branches of case
   trees, each in the accumulator of [fold_slots].  It depends only on the
   kernel's syntax and descriptions. *)

open Pts_native

(* ** Sizes *)

let rec nrecs = function
  | [] -> 0
  | FArg _ :: fs -> nrecs fs
  | FRec _ :: fs -> nrecs fs + 1

(* A field each, and a hypothesis after each recursive one, in one pass. *)
let nbinders fields =
  let rec go n = function [] -> n | FArg _ :: fs -> go (n + 1) fs | FRec _ :: fs -> go (n + 2) fs in
  go 0 fields

(* ** The binders, from the outermost

   With an accumulator: [f acc fd l k b rbs] for each field [fd], where [l]
   is its position among the fields, [k] the number of recursive fields
   before it, [b] the position of its binder and [rbs] the positions of the
   earlier fields, innermost first.  The accumulator, the positions of all
   the fields and the number of binders. *)
let fold_slots f acc fields =
  let rec go acc rbs b k l = function
    | [] -> (acc, rbs, b)
    | fd :: fs ->
        let acc = f acc fd l k b rbs in
        (match fd with
         | FArg _ -> go acc (b :: rbs) (b + 1) k (l + 1) fs
         | FRec _ -> go acc (b :: rbs) (b + 2) (k + 1) (l + 1) fs)
  in
  go acc [] 0 0 0 fields

(* ** Into the telescope of a method *)

(* From the context of the parameters and the earlier fields into the
   telescope of a method: [rbs] are the positions of the earlier fields
   among its [b] binders so far, innermost first, and [g] binders lie
   between the parameters and those of the method. *)
let transport_past g rbs b n =
  match List.nth_opt rbs n with
  | Some bl -> b - 1 - bl
  | None -> n - List.length rbs + b + g

(* In the eliminator, the motive lies between. *)
let transport = transport_past 1

(* The fields at [rbs], outermost first, as variables under the [b]
   binders of the method. *)
let field_vars rbs b = List.rev_map (fun bl -> Var (b - 1 - bl)) rbs
