(* Telescopes, native (Telescope.v): the domains of a type, and renamings
   and substitutions of a telescope entry by entry, each entry under those
   before it, and of a term under the binders of one.  It depends only on
   the kernel's syntax; [rename], [up_ren] and [up_sub], which Rocq takes
   from PTS/Syntax.v, the native kernel does not export. *)

open Pts_native

(* ** Domains *)

(* The domains of a type and what is left after them. *)
let rec split_pis = function
  | Pi (a, b) -> let domains, body = split_pis b in (a :: domains, body)
  | t -> ([], t)

(* ** Renamings *)

let rename r t = subst (fun n -> Var (r n)) t
let up_ren r n = if n = 0 then 0 else r (n - 1) + 1
let rec upn_ren m r = if m = 0 then r else up_ren (upn_ren (m - 1) r)

(* Each entry of a telescope under the entries before it. *)
let rec rename_tele r = function
  | [] -> []
  | a :: rest -> rename r a :: rename_tele (up_ren r) rest

(* ** Substitutions *)

(* Under the [m] binders of a telescope, and in each entry of one. *)
let up_sub sb n = if n = 0 then Var 0 else lift 1 (sb (n - 1))
let rec upn_sub m sb = if m = 0 then sb else up_sub (upn_sub (m - 1) sb)

let rec subst_tele sb = function
  | [] -> []
  | a :: rest -> subst sb a :: subst_tele (up_sub sb) rest
