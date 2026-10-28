(* What both native algorithms share: the combinators of results (the
   kernel's Common/Result.v, and for [iter_ok] and [fold_ok] the [titer]
   and [tfold] of its Common/Traced.v, the log being the registrar's
   here), the first duplicate (Elim/Decl.v) and the sizes of a
   description, which the sections of Rocq bind with [Let].  The
   telescopes are in Telescope_native, the binders of a method in
   Method_layout_native. *)

open Pts_native

(* ** Results *)

let ( let* ) = Result.bind
let require ok error = if ok then Ok () else Error error

let rec map_ok f = function
  | [] -> Ok []
  | x :: xs -> let* y = f x in let* ys = map_ok f xs in Ok (y :: ys)

let rec iter_ok f = function
  | [] -> Ok ()
  | x :: xs -> let* () = f x in iter_ok f xs

let rec fold_ok f acc = function
  | [] -> Ok acc
  | x :: xs -> let* acc = f acc x in fold_ok f acc xs

(* ** Lists *)

let rec first_duplicate = function
  | [] -> None
  | x :: rest -> if List.mem x rest then Some x else first_duplicate rest

(* ** Descriptions *)

let nparams d = List.length d.ind_params
let nindices d = List.length d.ind_indices
let nctors d = List.length d.ind_ctors
