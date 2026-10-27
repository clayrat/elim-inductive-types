(* Lecture demonstrations, in the order of the lecture.  Algorithm 1: the
   classification of declarations, the generated eliminators and their
   ι-rules, and their registration.  Algorithm 2: the history, the
   programs compiled directly and through it, with their equations and
   the conversions that prove them, and the refusals.  Then W-types: copy,
   whose call is on a functional field, and the refused transfer of
   induction to ℕ_W.

   An eliminator type prints its motive as P; an ι-rule names the methods
   after their constructors (m_zero, m_succ, …) and the fields x, y, z, …
   Registration logs list the stages of the plan with the number of
   checker events of each; one ι-rule is traced in full, and so is the
   refused body of the transfer of induction to ℕ_W.  A conversion lists
   the redexes of the normal-order trace of each side, δ with the name of
   the constant it unfolds.  Terms deeper than the bound print as "…". *)
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

let refused run = line (pp_registration ~depth (snd run))

let def_of sg f =
  match (sig_type sg (Def f), sig_delta sg (Def f)) with
  | Some a, Some b -> (a, b)
  | _ -> failwith ("no constant " ^ f)

let show_def sg f =
  let a, b = def_of sg f in
  line (f ^ " : " ^ pp_term ~depth a);
  line ("  := " ^ pp_term ~depth b)

(* A compiled function: its type with the names of its arguments, how it
   is compiled, its body and its equations. *)
let show_function ?(body = true) ?(body_depth = depth) run fn =
  let sg = sg_of run in
  let a, b = def_of sg fn.fn_name in
  let given = List.map (fun ((x, _), _) -> Some x) fn.fn_args in
  line (fn.fn_name ^ " : " ^ pp_binders ~depth given a);
  line ("  by recursion on " ^ fn.fn_struct ^ ", " ^ pp_strategy fn.fn_strategy);
  if body then line ("  := " ^ pp_term ~depth:body_depth b);
  List.iter (fun e -> line ("  " ^ pp_equation ~depth e)) (compiled_equations sg fn)

let equation run fn i = List.nth (compiled_equations (sg_of run) fn) i

(* An equation by conversion: both sides under normal order to their
   common normal form, with the redexes of each trace; with [terms] the
   terms of the trace of each side as well. *)
let show_conversion ?(terms = false) run ((names, l, r) as e) =
  let sg = sg_of run in
  line (pp_equation ~depth e);
  let side label t =
    let trace, result = normalize_trace sg prog_fuel t in
    let rs = trace_redexes sg trace in
    (match rs with
     | [] -> line ("  " ^ label ^ ": normal")
     | _ -> line ("  " ^ label ^ ", " ^ plural (List.length rs) "step" ^ ": " ^ pp_redexes rs));
    if terms && rs <> [] then begin
      line ("    " ^ pp_term ~depth ~names t);
      List.iter2 (fun r t -> line ("    ⇝ " ^ r ^ ":  " ^ pp_term ~depth ~names t)) rs (List.tl trace)
    end;
    result
  in
  let result = side "left" l in
  ignore (side "right" r);
  line ("  both reach " ^ pp_eval_result ~depth ~names result)

let applied f args = List.fold_left (fun t a -> NApp (t, a)) (NConst (Def f)) args
let eval sg t = pp_eval_result ~depth (normalize sg prog_fuel (build [] t))

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
  line (pp_eval_result ~depth result);

  (* Algorithm 2 *)
  print_newline ();
  print_endline "Algorithm 2: structural recursion compiled through the eliminators.";
  print_endline "Equations name their pattern variables.";

  header "The direct translation: a call on a field becomes its hypothesis";
  show_registration direct_run;
  List.iter (show_function direct_run) [ plus_fn; pow_fn; f_fn ];
  header "pow (succ k) ≡ Nat × pow k by conversion: δ, β and ι";
  show_conversion ~terms:true direct_run (equation direct_run pow_fn 1);
  header "f (succ k) b ≡ ⟨b, f k (succ b)⟩: the motive λn. Πb:Nat. pow n";
  show_conversion ~terms:true direct_run (equation direct_run f_fn 1);
  line ("f 2 0: " ^ eval sg_direct (applied "f" [ num 2; num 0 ]));

  header "The history of ℕ for motives in Type₀: Below, build and recBelow";
  List.iter (show_def sg_half) [ below_name "Nat" 0; build_name "Nat" 0; recbelow_name "Nat" 0 ];
  header "half directly: its call is two fields down";
  refused (compile_all predicative prog_fuel sg_nat0 [ half_fn Direct ]);
  header "half through the history: half k becomes table.2.1";
  show_registration half_run;
  show_function ~body_depth:max_int half_run (half_fn History);
  header "half (succ (succ k)) ≡ succ (half k) by conversion";
  show_conversion half_run (equation half_run (half_fn History) 2);
  line ("half 5: " ^ eval sg_half (applied "half" [ num 5 ]));

  header "isEven: a motive in Type₁, so the history needs Unit_1, elimNat[2] and elimNat[1]";
  show_registration even_run;
  show_function ~body:false even_run even_fn;
  header "isEven (succ (succ k)) ≡ isEven k by conversion";
  show_conversion even_run (equation even_run even_fn 2);
  List.iter (fun n ->
      line ("tt : isEven " ^ string_of_int n ^ ": "
            ^ pp_answer ~depth (fun () -> "")
                (snd (run_check predicative sg_even prog_fuel [] Tt (build [] (applied "isEven" [ num n ]))))))
    [ 4; 3 ];
  header "The empty history Unit : Type₀ in place of Unit_1";
  refused unit_history_run;

  header "The history of vectors: the indices of the fields";
  show_def sg_append (below_name "Vec" 0);
  header "append through the history, with addition on the first argument";
  show_registration append_run;
  show_function ~body:false append_run (append_fn "append" (NConst (Def "plus")));
  header "The equation of cons by conversion: Vec A (succ k + m) ⇝ Vec A (succ (k + m))";
  show_conversion append_run (equation append_run (append_fn "append" (NConst (Def "plus"))) 1);
  header "With addition on the second argument the branch nil is refused";
  let sg_plus2 = sg_of (compile_all predicative prog_fuel sg_vec [ plus2_fn ]) in
  let append2 = append_fn "append2" (NConst (Def "plus2")) in
  (* The body checks the leaf of nil in its scope, that of equation 0. *)
  (match (refusal (compile_all predicative prog_fuel sg_plus2 [ append2 ]),
          named_equations predicative prog_fuel sg_plus2 append2) with
   | Some (RRejected (st, e)), Some ((names, _) :: _) ->
       line ("refused: " ^ pp_stage st ^ ", in the branch nil: " ^ pp_error ~depth ~names e)
   | _ -> line "not refused in the branch nil");
  header "sumv: the constant w : pow n depends on the length, and is generalized with it";
  show_function ~body:false append_run sumv_fn;
  (match snd (def_of sg_append "sumv") with
   | Lam (Lam (Lam s)) -> line ("the motive: " ^ pp_term ~depth (List.nth (spine_args s) 1))
   | _ -> line "no motive");

  header "Refused: g (succ n) = g (pred n), pred n is no path to a subterm";
  refused (compile_all predicative prog_fuel sg_direct [ pred_fn; g_fn ]);
  header "Refused: Ackermann's equations, structural in m, or in n";
  List.iter (fun x -> refused (compile_all predicative prog_fuel sg_direct [ ack_fn x ])) [ "m"; "n" ];
  header "Refused: len with the parameter A varying, and with A changed in the call";
  refused (compile_all predicative prog_fuel sg_list [ len_fn Varying (NVar "A") ]);
  refused (compile_all predicative prog_fuel sg_list [ len_fn Constant (NConst (Ind "Nat")) ]);
  header "Accepted: Ackermann's function by higher-order structural recursion";
  let ack_run = compile_all predicative prog_fuel sg_direct [ iter_fn; ack_ho_fn ] in
  show_function ~body:false ack_run iter_fn;
  show_function ~body:false ack_run ack_ho_fn;
  line ("ack 2 2: " ^ eval sg_ack (applied "ack" [ num 2; num 2 ]));

  (* W-types *)
  print_newline ();
  print_endline "W-types: a functional recursive field, and ℕ_W.";

  header "copy on W: the call copy A B (f b) on the child at the position b";
  let copy_direct = copy_fn "copy" Direct and copy_history = copy_fn "copy_h" History in
  show_function ~body_depth:max_int copy_run copy_direct;
  show_def sg_copy (below_name "W" 0);
  show_function ~body:false copy_run copy_history;
  header "copy is the identity only extensionally: the child of zero_W is stuck";
  let zero_w = NConst (Def "zero_W") in
  let copy_zero = applied "copy" [ NBool; NConst (Def "IsTrue"); zero_w ] in
  line ("copy Bool IsTrue zero_W ≡ zero_W: "
        ^ (match convert sg_copy prog_fuel (build [] copy_zero) (build [] zero_w) with
           | ConvEqual _ -> "convertible"
           | ConvDifferent -> "different"
           | _ -> "undecided"));
  line ("copy Bool IsTrue zero_W: " ^ eval sg_copy copy_zero);

  header "ℕ_W: the transfer of dependent induction through elimW[0], refused";
  show_registration ind_w_run;
  header "The body from the match on the label: elimBool checks the branch true first";
  line "#k counts binders outward: at the match #4 = s, #6 = P;";
  line "in the branch, past its f and h, #0 = h, #1 = f, #6 = s, #8 = P";
  let rec from_match = function EvFamily _ :: _ as evs -> evs | _ :: evs -> from_match evs | [] -> [] in
  (match List.assoc_opt (AtDefBody "ind_W") (fst ind_w_run), refusal ind_w_run with
   | Some events, Some (RRejected (_, e)) ->
       List.iter (fun ev -> line (pp_event ~depth ev)) (from_match events);
       line ("refused: " ^ pp_error ~depth ~names:[ "h"; "f"; "h"; "f"; "a"; "w"; "s"; "z"; "P" ] e)
   | _ -> line "not refused in the body");
  header "The branch false on its own, against P (sup false f) for any f : Void → ℕ_W";
  line "#0 = s, #1 = z, #2 = P, each one more past the binder f";
  let names = [ "s"; "z"; "P" ] in
  List.iter (fun ev -> line (pp_event ~depth ~names ev)) (from_term (fst ind_false_run));
  line (pp_answer ~depth ~names:("h" :: "f" :: names) (fun () -> "") (snd ind_false_run))
