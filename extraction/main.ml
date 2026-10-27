(* Lecture demonstrations of algorithm 1: the classification of
   declarations, the generated eliminators and their ι-rules, and their
   registration, in the order of the lecture.

   An eliminator type prints its motive as P; an ι-rule names the methods
   after their constructors (m_zero, m_succ, …) and the fields x, y, z, …
   Registration logs list the stages of the plan with the number of
   checker events of each; one ι-rule is traced in full.  Terms deeper
   than the bound print as "…". *)
open Deptypes
open Pretty
open Pretty_ind

let fuel = 300
let depth = 12

let header title =
  print_newline ();
  print_endline ("== " ^ title)

let line s = print_endline ("  " ^ s)

let classified raw =
  match classify_decl raw with
  | Ok d -> d
  | Err e -> failwith ("not classified: " ^ pp_decl_error e)

(* The description, the eliminator at the given levels, the method types
   and the ι-rules at level 0. *)
let show_declaration ?(levels = [ 0 ]) raw =
  let d = classified raw in
  List.iter line (pp_desc ~depth d);
  List.iter (fun j -> line (elim_name d j ^ " : " ^ pp_elim_type ~depth d j)) levels;
  line "methods:";
  List.iter (fun c -> line ("  " ^ c.ctor_name ^ ": " ^ pp_method ~depth d c)) d.ind_ctors;
  line "ι-rules:";
  List.iter (fun r -> line ("  " ^ pp_rule ~depth d r)) (iota_rules d 0)

let show_registration (log, answer) =
  List.iter (fun s -> line ("  " ^ s)) (pp_log log);
  line (pp_registration ~depth answer)

let trace_check g t ty sg =
  let events, answer = run_check predicative sg fuel g t ty in
  List.iter (fun ev -> line (pp_event ~depth ~ctx:g ev)) events;
  line (pp_answer ~depth (fun () -> "") answer)

let sg_of = function _, Registered sg -> sg | _ -> failwith "not registered"

let () =
  print_endline "Algorithm 1: declarations, their eliminators and their registration.";
  print_endline "In events, #k is the free variable with de Bruijn index k.";

  (* ℕ *)
  header "ℕ as the first declaration: the motive in place of the result type";
  show_declaration ~levels:[ 0; 1 ] raw_nat;
  header "ℕ registered: the stages of the plan";
  let nat_run = declare_checked predicative fuel [] raw_nat [ 0 ] in
  show_registration nat_run;
  let d = classified raw_nat in
  let succ_rule = List.nth (iota_rules d 0) 1 in
  header "The ι-rule of succ, right side, checked where elimNat[0] has no active rules";
  line (pp_rule ~depth d succ_rule);
  (* After the context and the expected type are validated: the term. *)
  let rec from_term = function EvTerm _ :: _ as evs -> evs | _ :: evs -> from_term evs | [] -> [] in
  (match List.assoc_opt (AtRuleRhs ("Nat", 0, "succ")) (fst nat_run) with
   | Some events ->
       List.iter
         (fun ev -> line (pp_event ~depth ~ctx:succ_rule.rule_ctx ~names:(rule_names d succ_rule) ev))
         (from_term events)
   | None -> line "no such stage");

  (* Lists and vectors *)
  header "Lists";
  show_declaration raw_list;
  header "Vectors: the parameter A against the index n";
  show_declaration raw_vec;
  header "Vectors registered over ℕ";
  show_registration (declare_checked predicative fuel sg_nat0 raw_vec [ 0 ]);

  (* Binary trees *)
  header "Binary trees: left, ih_left, right, ih_right";
  show_declaration raw_tree;

  (* Positivity *)
  header "Why the restrictions: the negative field mk : (D → Void) → D";
  line (pp_registration ~depth (snd (declare_checked predicative fuel [] raw_negative [ 0 ])));
  header "The non-strictly positive field mk : ((D → Bool) → Bool) → D";
  line (pp_registration ~depth (snd (declare_checked predicative fuel [] raw_non_strict [ 0 ])));
  header "In the bypass mode: D, its eliminator, unmk and δ := λd. unmk d d";
  show_registration void_diagonal;
  let delta = Const (Def "delta") and mk = Const (Ctor ("D", "mk")) in
  let diagonal = App (delta, App (mk, delta)) in
  header "δ (mk δ) : Void, a closed proof of Void without fix";
  trace_check [] diagonal Void sg_void;
  header "δ (mk δ) under normal order, 6 steps";
  let trace, _ = normalize_trace sg_void 6 diagonal in
  List.iteri (fun i t -> line (string_of_int i ^ ". " ^ pp_term ~depth t)) trace;
  header "With Bool: δ := λd. not (unmk d d), and tt : IsTrue (δ (mk δ))";
  let is_true b = ElimBool (Ann (Lam (Srt (Univ 0)), Pi (Bool, Srt (Univ 1))), Unit, Void, b) in
  line (pp_answer ~depth (fun () -> "")
          (snd (run_check predicative sg_bool fuel [] Tt (is_true diagonal))));

  (* W-types *)
  header "W-types: a recursive field with a position";
  show_declaration raw_w;

  (* The primitives *)
  header "Void, Unit and Bool against the primitives of lecture 6";
  List.iter (fun (name, desc, schema) ->
      line (name ^ ": " ^ pp_binders ~depth [ Some "P" ] (to_prim (elim_type desc 0)));
      line ("  the schema: " ^ pp_binders ~depth [ Some "P" ] (build [] schema)))
    [ "Void", void_desc, void_schema 0; "Unit", unit_desc, unit_schema 0; "Bool", bool_desc, bool_schema 0 ];

  (* Levels *)
  header "Levels: Unit_1 for a history in Type₁, and no cumulativity";
  let sg1 = sg_of (run_registration (ensure_unit predicative fuel [] 1)) in
  line ("declared: " ^ unit_name 1);
  trace_check [] (tt_at 1) (unit_at 1) sg1;
  line ("Unit against Type₁: "
        ^ pp_answer ~depth (fun () -> "") (snd (run_check predicative sg1 fuel [] Unit (Srt (Univ 1)))));
  line ("tt against Unit_1: "
        ^ pp_answer ~depth (fun () -> "") (snd (run_check predicative sg1 fuel [] Tt (unit_at 1))));

  (* δ-constants *)
  header "A δ-constant: double, checked in the signature without it";
  let double_ty = Pi (Const (Ind "Nat"), Const (Ind "Nat")) in
  let double_run = define_checked predicative fuel sg_nat0 "double" double_ty (build [] double_body) in
  show_registration double_run;
  header "double 1 under normal order: δ, then β and ι";
  let one = App (Const (Ctor ("Nat", "succ")), Const (Ctor ("Nat", "zero"))) in
  let trace, result = normalize_trace (sg_of double_run) fuel (App (Const (Def "double"), one)) in
  List.iteri (fun i t -> line (string_of_int i ^ ". " ^ pp_term ~depth t)) trace;
  line (pp_eval_result ~depth result)
