(* Regression tests of the extracted generator, compiler and printer. *)
open Deptypes
open Pretty

let failures = ref 0

let expect name actual expected =
  if actual <> expected then begin
    incr failures;
    Printf.printf "FAIL %s\n  expected: %s\n  actual:   %s\n" name expected actual
  end

let answer_term g (_, a) = pp_answer (pp_term ~names:(ctx_names g)) a

let () =
  expect "kernel linked" (answer_term [] (run_infer predicative sig_empty 100 [] (Srt (Univ 0)))) "accepted: Type₁";
  if !failures > 0 then exit 1 else print_endline "regress: all tests passed"
