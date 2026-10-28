(* The conversions of the native algorithms to the extract, for the
   differential tests: the declarations, rules, diagnostics,
   registrations and logs of algorithm 1, and the case trees, programs,
   scopes and elaborated trees of algorithm 2.  The kernel's syntax
   converts by [Extracted]. *)

module X = Deptypes
module N = Pts_native
module En = Elim_native
module R = Recursion_native
module L = Looping

open Extracted

(* ** Conversions of algorithm 1, and of the diagnostics it shares with
   algorithm 2 *)

let raw_to_extracted raw = {
  X.rd_name = raw.En.rd_name;
  rd_params = List.map term_to_extracted raw.En.rd_params;
  rd_indices = List.map term_to_extracted raw.En.rd_indices;
  rd_level = raw.En.rd_level;
  rd_ctors = List.map (fun c -> { X.rc_name = c.En.rc_name; rc_type = term_to_extracted c.En.rc_type })
               raw.En.rd_ctors }

let positivity_to_extracted = function En.Checked -> X.Checked | En.Bypass -> X.Bypass

let site_to_extracted = function En.SField l -> X.SField l | En.SResult -> X.SResult

let decl_error_to_extracted = function
  | En.EOpenParams -> X.EOpenParams
  | En.EOpenIndices -> X.EOpenIndices
  | En.ESelfReference -> X.ESelfReference
  | En.EOpenCtor c -> X.EOpenCtor c
  | En.EDuplicateCtor c -> X.EDuplicateCtor c
  | En.ENegative (c, l, a) -> X.ENegative (c, l, term_to_extracted a)
  | En.ENonStrict (c, l, a) -> X.ENonStrict (c, l, term_to_extracted a)
  | En.ENested (c, l, a) -> X.ENested (c, l, term_to_extracted a)
  | En.ENotFamily (c, t) -> X.ENotFamily (c, term_to_extracted t)
  | En.EArity (c, s, t) -> X.EArity (c, site_to_extracted s, term_to_extracted t)
  | En.ENonUniform (c, s, t) -> X.ENonUniform (c, site_to_extracted s, term_to_extracted t)
  | En.EInIndices (c, s, t) -> X.EInIndices (c, site_to_extracted s, term_to_extracted t)

let result_to_extracted value error = function
  | Ok a -> X.Ok (value a)
  | Error e -> X.Err (error e)

let rule_to_extracted r = {
  X.rule_ctor = r.En.rule_ctor;
  rule_ctx = List.map term_to_extracted r.En.rule_ctx;
  rule_lhs = term_to_extracted r.En.rule_lhs;
  rule_rhs = term_to_extracted r.En.rule_rhs;
  rule_type = term_to_extracted r.En.rule_type }

let stage_to_extracted = function
  | En.AtIndType d -> X.AtIndType d
  | En.AtCtorType (d, c) -> X.AtCtorType (d, c)
  | En.AtField (d, c, l) -> X.AtField (d, c, l)
  | En.AtElimType (d, j) -> X.AtElimType (d, j)
  | En.AtRuleLhs (d, j, c) -> X.AtRuleLhs (d, j, c)
  | En.AtRuleRhs (d, j, c) -> X.AtRuleRhs (d, j, c)
  | En.AtDefType f -> X.AtDefType f
  | En.AtDefBody f -> X.AtDefBody f
  | En.AtMotive (f, x) -> X.AtMotive (f, x)
  | En.AtEquation (f, i) -> X.AtEquation (f, i)

let case_error_to_extracted = function
  | En.CDuplicateArg x -> X.CDuplicateArg x
  | En.CNoStruct x -> X.CNoStruct x
  | En.CUnbound x -> X.CUnbound x
  | En.CNotFamily (x, t) -> X.CNotFamily (x, term_to_extracted t)
  | En.CIndices (x, t) -> X.CIndices (x, term_to_extracted t)
  | En.CGeneralize (x, y) -> X.CGeneralize (x, y)
  | En.CParams (x, y) -> X.CParams (x, y)
  | En.CBranches x -> X.CBranches x
  | En.CFields (c, n) -> X.CFields (c, n)
  | En.CFieldName (c, x) -> X.CFieldName (c, x)
  | En.CRoot x -> X.CRoot x
  | En.CUnsplit x -> X.CUnsplit x
  | En.CMotiveSort (x, s) -> X.CMotiveSort (x, sort_to_extracted s)
  | En.CCallArity t -> X.CCallArity (term_to_extracted t)
  | En.CNotStructural t -> X.CNotStructural (term_to_extracted t)
  | En.CNotImmediate t -> X.CNotImmediate (term_to_extracted t)
  | En.CIndexChanged (x, t) -> X.CIndexChanged (x, term_to_extracted t)
  | En.CConstantChanged (x, t) -> X.CConstantChanged (x, term_to_extracted t)

let reg_error_to_extracted = function
  | En.RClassify e -> X.RClassify (decl_error_to_extracted e)
  | En.RTaken g -> X.RTaken (gref_to_extracted g)
  | En.RUndeclared d -> X.RUndeclared d
  | En.RLevel (c, l, s, i) -> X.RLevel (c, l, sort_to_extracted s, i)
  | En.RNotAType (st, t) -> X.RNotAType (stage_to_extracted st, term_to_extracted t)
  | En.RRejected (st, e) -> X.RRejected (stage_to_extracted st, error_to_extracted e)
  | En.ROpen -> X.ROpen
  | En.RCase e -> X.RCase (case_error_to_extracted e)
  | En.REquation (f, i, l, r) -> X.REquation (f, i, term_to_extracted l, term_to_extracted r)

let failure_to_extracted = function
  | En.Refuse e -> X.Refuse (reg_error_to_extracted e)
  | En.NoFuelAt (st, t) -> X.NoFuelAt (stage_to_extracted st, term_to_extracted t)

let registration_to_extracted = function
  | En.Registered sg -> X.Registered (List.map entry_to_extracted sg)
  | En.Refused e -> X.Refused (reg_error_to_extracted e)
  | En.OutOfFuelAt (st, t) -> X.OutOfFuelAt (stage_to_extracted st, term_to_extracted t)

let log_to_extracted =
  List.map (fun (st, events) -> (stage_to_extracted st, List.map event_to_extracted events))

(* ** Conversions of algorithm 2 *)

let atom_to_extracted = function
  | N.Void -> X.NVoid | N.Unit -> X.NUnit | N.Tt -> X.NTt
  | N.Bool -> X.NBool | N.BTrue -> X.NTrue | N.BFalse -> X.NFalse
  | N.Srt s -> X.NSrt (sort_to_extracted s)
  | N.Const g -> X.NConst (gref_to_extracted g)
  | _ -> failwith "a named term with a compound atom"

let rec named_to_extracted = function
  | L.Sort s -> X.NSrt (sort_to_extracted s)
  | L.Name x -> X.NVar x
  | L.Product (x, a, b) -> X.NPi (x, named_to_extracted a, named_to_extracted b)
  | L.Lambda (x, b) -> X.NLam (x, named_to_extracted b)
  | L.Apply (f, a) -> X.NApp (named_to_extracted f, named_to_extracted a)
  | L.Annotate (t, a) -> X.NAnn (named_to_extracted t, named_to_extracted a)
  | L.Arrow (a, b) -> X.NArrow (named_to_extracted a, named_to_extracted b)
  | L.Const t -> atom_to_extracted t
  | L.ElimVoid (c, e) -> X.NElimVoid (named_to_extracted c, named_to_extracted e)
  | L.ElimUnit (c, m, u) -> X.NElimUnit (named_to_extracted c, named_to_extracted m, named_to_extracted u)
  | L.ElimBool (c, x, y, b) ->
      X.NElimBool (named_to_extracted c, named_to_extracted x, named_to_extracted y, named_to_extracted b)
  | L.Sum (x, a, b) -> X.NSigma (x, named_to_extracted a, named_to_extracted b)
  | L.Times (a, b) -> X.NTimes (named_to_extracted a, named_to_extracted b)
  | L.Pairing (a, b) -> X.NPair (named_to_extracted a, named_to_extracted b)
  | L.First t -> X.NFst (named_to_extracted t)
  | L.Second t -> X.NSnd (named_to_extracted t)

let mark_to_extracted = function R.Constant -> X.Constant | R.Varying -> X.Varying
let strategy_to_extracted = function R.Direct -> X.Direct | R.History -> X.History

let rec tree_to_extracted = function
  | R.Leaf t -> X.Leaf (named_to_extracted t)
  | R.Split (x, bs) -> X.Split (x, List.map (fun (c, xs, t) -> ((c, xs), tree_to_extracted t)) bs)

let fun_decl_to_extracted fn = {
  X.fn_name = fn.R.fn_name;
  fn_args = List.map (fun (x, a, mk) -> ((x, named_to_extracted a), mark_to_extracted mk)) fn.R.fn_args;
  fn_result = named_to_extracted fn.R.fn_result;
  fn_struct = fn.R.fn_struct;
  fn_strategy = strategy_to_extracted fn.R.fn_strategy;
  fn_tree = tree_to_extracted fn.R.fn_tree }

let tag_to_extracted = function R.User (x, p) -> X.User (x, p) | R.Anon -> X.Anon | R.Aux k -> X.Aux k
let native_tag = function X.User (x, p) -> R.User (x, p) | X.Anon -> R.Anon | X.Aux k -> R.Aux k

let scope_to_extracted =
  List.map (fun b -> { X.b_tag = tag_to_extracted b.R.b_tag; b_type = term_to_extracted b.R.b_type })

let terms = List.map term_to_extracted

let generalized_to_extracted g = {
  X.gn_seeds = g.R.gn_seeds; gn_tail = g.R.gn_tail; gn_seed_types = terms g.R.gn_seed_types;
  gn_tail_types = terms g.R.gn_tail_types; gn_goal = term_to_extracted g.R.gn_goal }

let prim_to_extracted = function R.PVoid -> X.PVoid | R.PUnit -> X.PUnit | R.PBool -> X.PBool

let split_info_to_extracted si =
  let sv = si.R.si_var in
  { X.si_var = { X.sv_name = sv.R.sv_name; sv_level = sv.R.sv_level; sv_path = sv.R.sv_path;
                 sv_desc = desc_to_extracted sv.R.sv_desc; sv_prim = Option.map prim_to_extracted sv.R.sv_prim;
                 sv_params = terms sv.R.sv_params; sv_indices = sv.R.sv_indices };
    si_gen = generalized_to_extracted si.R.si_gen }

let rec elab_to_extracted = function
  | R.ELeaf { scope; goal; env; rhs } ->
      X.ELeaf (scope_to_extracted scope, term_to_extracted goal, terms env, term_to_extracted rhs)
  | R.ESplit { scope; goal; split; branches } ->
      X.ESplit (scope_to_extracted scope, term_to_extracted goal, split_info_to_extracted split,
                List.map (fun (b, e) -> (b, elab_to_extracted e)) branches)

let case_result value = result_to_extracted value case_error_to_extracted
let signature_to_extracted = List.map entry_to_extracted
