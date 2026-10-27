(* Regression tests of the extracted algorithms 1 and 2 and of their
   printer: the generated eliminators and rules, the diagnostics and the
   answers of registration, the equations of the compiled programs, the
   redexes of their conversions, and the refusals, as the demos print
   them. *)
open Deptypes
open Pretty
open Pretty_ind

let failures = ref 0

let expect name actual expected =
  if actual <> expected then begin
    incr failures;
    Printf.printf "FAIL %s\n  expected: %s\n  actual:   %s\n" name expected actual
  end

let fuel = 300
let answer_term g (_, a) = pp_answer (pp_term ~names:(ctx_names g)) a
let answer_unit (_, a) = pp_answer (fun () -> "") a

let classified raw = match classify_decl raw with Ok d -> d | Err _ -> failwith "not classified"
let rule d c = pp_rule d (List.find (fun r -> r.rule_ctor = c) (iota_rules d 0))
let method_of d c = pp_method d (List.find (fun k -> k.ctor_name = c) d.ind_ctors)
let sg_of = function _, Registered sg -> sg | _ -> failwith "not registered"

let () =
  expect "kernel linked" (answer_term [] (run_infer predicative sig_empty 100 [] (Srt (Univ 0)))) "accepted: Type₁";

  (* generation *)
  let nat = classified raw_nat and tree = classified raw_tree and vec = classified raw_vec in
  let w = classified raw_w in
  expect "elimNat" (pp_elim_type nat 0)
    "ΠP:Nat → Type₀. P zero → (Πx:Nat. P x → P (succ x)) → Πx:Nat. P x";
  expect "elimNat[1]" (pp_elim_type nat 1)
    "ΠP:Nat → Type₁. P zero → (Πx:Nat. P x → P (succ x)) → Πx:Nat. P x";
  expect "succ rule" (rule nat "succ")
    "elimNat[0] P m_zero m_succ (succ x)  ⇝  m_succ x (elimNat[0] P m_zero m_succ x)";
  expect "node method" (method_of tree "node") "Πx:Tree. P x → Πy:Tree. P y → P (node x y)";
  expect "node rule" (rule tree "node")
    "elimTree[0] P m_leaf m_node (node x y)  ⇝  m_node x (elimTree[0] P m_leaf m_node x) y (elimTree[0] P m_leaf m_node y)";
  expect "vec description" (String.concat " | " (pp_desc vec))
    "Vec : Type₀ → Nat → Type₀ | nil : ΠA:Type₀. Vec A zero | cons : ΠA:Type₀. Πx:Nat. A → Vec A x → Vec A (succ x)    [non-recursive, non-recursive, recursive]";
  expect "vec cons rule" (rule vec "cons")
    "elimVec[0] A P m_nil m_cons (succ x) (cons A x y z)  ⇝  m_cons x y z (elimVec[0] A P m_nil m_cons x z)";
  expect "W" (pp_elim_type w 0)
    "ΠA:Type₀. ΠB:A → Type₀. ΠP:W A B → Type₀. (Πx:A. Πy:B x → W A B. (Πz:B x. P (y z)) → P (sup A B x y)) → Πx:W A B. P x";
  expect "W rule" (rule w "sup")
    "elimW[0] A B P m_sup (sup A B x y)  ⇝  m_sup x y (λz. elimW[0] A B P m_sup (y z))";
  List.iter (fun (name, desc, schema) ->
      expect ("primitive " ^ name) (pp_term (to_prim (elim_type desc 0))) (pp_term (build [] schema)))
    [ "Void", void_desc, void_schema 0; "Unit", unit_desc, unit_schema 0; "Bool", bool_desc, bool_schema 0 ];

  (* registration *)
  let nat_run = declare_checked predicative fuel [] raw_nat [ 0 ] in
  expect "nat registered" (pp_registration (snd nat_run)) "registered; the signature: elimNat[0], Nat";
  expect "nat stages" (String.concat ", " (List.map (fun (st, _) -> pp_stage st) (fst nat_run)))
    "the type of Nat, the type of zero, the type of succ, the level of field 0 of succ, the type of elimNat[0], the ι-rule of zero, left side, the ι-rule of zero, right side, the ι-rule of succ, left side, the ι-rule of succ, right side";
  expect "nat twice" (pp_registration (snd (declare_checked predicative fuel (sg_of nat_run) raw_nat [ 0 ])))
    "refused: Nat is in the signature already";
  expect "vec without nat" (pp_registration (snd (declare_checked predicative fuel [] raw_vec [ 0 ])))
    "refused: the type of Vec: the constant Nat is not in the signature";
  expect "negative" (pp_registration (snd (declare_checked predicative fuel [] raw_negative [ 0 ])))
    "refused: not in the grammar: mk, field 0 : D → Void: the type occurs in a negative position";
  expect "non-strict" (pp_registration (snd (declare_checked predicative fuel [] raw_non_strict [ 0 ])))
    "refused: not in the grammar: mk, field 0 : (D → Bool) → Bool: the type occurs positively, but the field is not Πȳ. D Δ v̄";

  (* the diagonal *)
  let delta = Const (Def "delta") and mk = Const (Ctor ("D", "mk")) in
  let diagonal = App (delta, App (mk, delta)) in
  expect "diagonal registered" (pp_registration (snd void_diagonal))
    "registered; the signature: delta, unmk, elimD[0], D";
  expect "δ (mk δ) : Void" (answer_unit (run_check predicative sg_void fuel [] diagonal Void)) "accepted";
  let is_true b = ElimBool (Ann (Lam (Srt (Univ 0)), Pi (Bool, Srt (Univ 1))), Unit, Void, b) in
  expect "Bool diagonal" (answer_unit (run_check predicative sg_bool fuel [] Tt (is_true diagonal)))
    "undecided: out of fuel while typing tt";

  (* levels and δ-constants *)
  let sg1 = sg_of (run_registration (ensure_unit predicative fuel [] 1)) in
  expect "Unit_1" (answer_unit (run_check predicative sg1 fuel [] (tt_at 1) (unit_at 1))) "accepted";
  expect "no cumulativity" (answer_unit (run_check predicative sg1 fuel [] Unit (Srt (Univ 1))))
    "rejected: Unit has type Type₀, expected Type₁";
  let double_ty = Pi (Const (Ind "Nat"), Const (Ind "Nat")) in
  let double_run = define_checked predicative fuel sg_nat0 "double" double_ty (build [] double_body) in
  expect "double registered" (pp_registration (snd double_run)) "registered; the signature: double, elimNat[0], Nat";
  let one = App (Const (Ctor ("Nat", "succ")), Const (Ctor ("Nat", "zero"))) in
  expect "double 1" (pp_eval_result (normalize (sg_of double_run) fuel (App (Const (Def "double"), one))))
    "normal form succ (succ zero)";
  expect "double itself"
    (pp_registration (snd (define_checked predicative fuel sg_nat0 "double" double_ty
                              (Lam (App (Const (Def "double"), Var 0))))))
    "refused: the body of double: the constant double is not in the signature";

  (* ℕ_W *)
  expect "ind_W refused" (pp_registration (snd ind_w_run))
    "refused: the body of ind_W: #6 (#1 tt) (#0 tt) has type #8 (succ_W (#1 tt)), expected #8 (sup Bool IsTrue true #1)";
  expect "ind_W branch false"
    (pp_answer ~names:[ "h"; "f"; "s"; "z"; "P" ] (fun () -> "") (snd ind_false_run))
    "rejected: z has type P zero_W, expected P (sup Bool IsTrue false f)";

  (* algorithm 2 *)
  let applied f args = List.fold_left (fun t a -> NApp (t, a)) (NConst (Def f)) args in
  let eval sg t = pp_eval_result (normalize sg prog_fuel (build [] t)) in
  let refused_with run = pp_registration (snd run) in
  let equations run fn = String.concat " | " (List.map pp_equation (compiled_equations (sg_of run) fn)) in
  let redexes run t = pp_redexes (trace_redexes (sg_of run) (fst (normalize_trace (sg_of run) prog_fuel t))) in
  let plus = NConst (Def "plus") in
  let programs =
    [ direct_run, plus_fn; direct_run, pow_fn; direct_run, f_fn; half_run, half_fn History; even_run, even_fn;
      append_run, append_fn "append" plus; append_run, sumv_fn;
      copy_run, copy_fn "copy" Direct; copy_run, copy_fn "copy_h" History ] in
  List.iter (fun (run, fn) ->
      List.iteri (fun i (_, l, r) ->
          List.iter (fun t ->
              if List.mem "?" (trace_redexes (sg_of run) (fst (normalize_trace (sg_of run) prog_fuel t))) then
                expect (Printf.sprintf "%s equation %d: every step a redex" fn.fn_name i) "?" "no ?")
            [ l; r ])
        (compiled_equations (sg_of run) fn))
    programs;
  expect "plus equations" (equations direct_run plus_fn) "plus zero m ≡ m | plus (succ k) m ≡ succ (plus k m)";
  expect "f equations" (equations direct_run f_fn) "f zero b ≡ tt | f (succ k) b ≡ ⟨b, f k (succ b)⟩";
  expect "pow (succ k)" (match compiled_equations sg_direct pow_fn with
      | [ _; (_, l, _) ] -> redexes direct_run l | _ -> "")
    "δ pow · β · ι elimNat[1] · β ×2";
  expect "f 2 0" (eval sg_direct (applied "f" [ num 2; num 0 ])) "normal form ⟨zero, ⟨succ zero, tt⟩⟩";
  expect "Below_Nat_0" (match sig_delta sg_half (Def "Below_Nat_0") with Some b -> pp_term b | None -> "")
    "λx. elimNat[1] (λy. Type₀) Unit (λy. λz. x y × z)";
  expect "half directly" (refused_with (compile_all predicative prog_fuel sg_nat0 [ half_fn Direct ]))
    "refused: a call on a subterm deeper than a field, without the history: half #1";
  expect "half equations" (equations half_run (half_fn History))
    "half zero ≡ zero | half (succ zero) ≡ zero | half (succ (succ k)) ≡ succ (half k)";
  expect "half access" (match sig_delta sg_half (Def "half") with Some b -> pp_term b | None -> "")
    "λx. recBelow_Nat_0 (λy. Nat) (λy. λz. elimNat[0] (λu. Below_Nat_0 (λv. Nat) u → Nat) (λu. zero) (λu. λv. λw. elimNat[0] (λx'. Below_Nat_0 (λy'. Nat) (succ x') → Nat) (λx'. zero) (λx'. λy'. λz'. succ (fst (snd z'))) u w) y z) x";
  expect "half 5" (eval sg_half (applied "half" [ num 5 ])) "normal form succ (succ zero)";
  expect "isEven equations" (equations even_run even_fn)
    "isEven zero ≡ Unit | isEven (succ zero) ≡ Void | isEven (succ (succ k)) ≡ isEven k";
  expect "tt : isEven 4"
    (answer_unit (run_check predicative sg_even prog_fuel [] Tt (build [] (applied "isEven" [ num 4 ])))) "accepted";
  expect "tt : isEven 3"
    (answer_unit (run_check predicative sg_even prog_fuel [] Tt (build [] (applied "isEven" [ num 3 ]))))
    "rejected: tt has type Unit, expected isEven (succ (succ (succ zero)))";
  expect "Unit for Unit_1" (refused_with unit_history_run)
    "refused: the body of Below_Nat_1: Unit has type Type₀, expected (λx. Type₁) zero";
  expect "append equations" (equations append_run (append_fn "append" plus))
    "append A zero m (nil A) ys ≡ ys | append A (succ k) m (cons A k x xs') ys ≡ cons A (plus k m) x (append A k m xs' ys)";
  let sg_plus2 = sg_of (compile_all predicative prog_fuel sg_vec [ plus2_fn ]) in
  let append2 = append_fn "append2" (NConst (Def "plus2")) in
  expect "append2 nil"
    (match (refusal (compile_all predicative prog_fuel sg_plus2 [ append2 ]),
            named_equations predicative prog_fuel sg_plus2 append2) with
     | Some (RRejected (_, e)), Some ((names, _) :: _) -> pp_error ~names e
     | _ -> "")
    "ys has type Vec A m, expected Vec A (plus2 zero m)";
  expect "sumv motive" (match sig_delta sg_append (Def "sumv") with
      | Some (Lam (Lam (Lam s))) -> pp_term (List.nth (spine_args s) 1) | _ -> "")
    "λx. λy. pow x → Nat";
  expect "g" (refused_with (compile_all predicative prog_fuel sg_direct [ pred_fn; g_fn ]))
    "refused: a call on no strict subterm of the structural argument: g (pred #2)";
  expect "ack in m" (refused_with (compile_all predicative prog_fuel sg_direct [ ack_fn "m" ]))
    "refused: a call on no strict subterm of the structural argument: ack (succ #4) #1";
  expect "ack in n" (refused_with (compile_all predicative prog_fuel sg_direct [ ack_fn "n" ]))
    "refused: a call on no strict subterm of the structural argument: ack #2 (succ zero)";
  expect "len varying" (refused_with (compile_all predicative prog_fuel sg_list [ len_fn Varying (NVar "A") ]))
    "refused: the parameters of the type of xs mention A, which varies: non-uniform recursion";
  expect "len changed"
    (refused_with (compile_all predicative prog_fuel sg_list [ len_fn Constant (NConst (Ind "Nat")) ]))
    "refused: the constant argument A changes: len Nat #2";
  expect "ack 2 2" (eval sg_ack (applied "ack" [ num 2; num 2 ]))
    "normal form succ (succ (succ (succ (succ (succ (succ zero))))))";
  expect "copy equations" (equations copy_run (copy_fn "copy" Direct))
    "copy A B (sup A B a f) ≡ sup A B a (λx. copy A B (f x))";
  let zero_w = NConst (Def "zero_W") in
  expect "copy zero_W"
    (match convert sg_copy prog_fuel (build [] (applied "copy" [ NBool; NConst (Def "IsTrue"); zero_w ])) (build [] zero_w)
     with ConvDifferent -> "different" | _ -> "not different")
    "different";

  if !failures > 0 then exit 1 else print_endline "regress: all tests passed"
