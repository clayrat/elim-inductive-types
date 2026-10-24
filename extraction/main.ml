(* Lecture demonstrations: the generator of eliminators and the compiler of
   structural recursion, on the kernel of lecture 6.

   Each demo prints the input, the trace of the run and the answer, as the
   kernel's demos do.  Until the generator exists, the only demo shows that
   the kernel is linked. *)
open Deptypes
open Pretty

let fuel = 100
let depth = 8

let header title =
  print_newline ();
  print_endline ("== " ^ title)

let print_trace g events = List.iter (fun ev -> print_endline (pp_event ~depth ~ctx:g ev)) events

let demo_infer title spec g t =
  header title;
  print_endline ("  " ^ pp_ctx g ^ " ⊢ " ^ pp_term ~names:(ctx_names g) t ^ " ⇑ ?");
  let events, answer = run_infer spec sig_empty fuel g t in
  print_trace g events;
  print_endline (pp_answer ~depth (pp_term ~names:(ctx_names g)) answer)

let () = demo_infer "The kernel of lecture 6: Type₀ : Type₁" predicative [] (Srt (Univ 0))
