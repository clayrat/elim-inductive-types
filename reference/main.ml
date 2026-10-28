(* The differential tests of the native algorithms against the extract:
   both suites, or those named on the command line. *)

let suites = [ ("elim", Diff.run); ("recursion", Diff_recursion.run) ]

let () =
  let names =
    match Array.to_list Sys.argv with
    | _ :: (_ :: _ as names) -> names
    | _ -> List.map fst suites
  in
  List.iter (fun name ->
      match List.assoc_opt name suites with
      | Some run -> run ()
      | None -> failwith ("unknown suite " ^ name ^ ": elim or recursion"))
    names
