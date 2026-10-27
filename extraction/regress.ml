(* Regression tests of the extracted algorithm 1 and of its printer: the
   generated eliminators and rules, the diagnostics and the answers of
   registration, as the demos print them. *)
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

  if !failures > 0 then exit 1 else print_endline "regress: all tests passed"
