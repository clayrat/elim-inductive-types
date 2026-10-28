(* The registration monad, native (Registration.v): both algorithms
   register through it, every checker run going to the log of the
   registration with its stage, as the run of the native checker keeps
   its events in a queue, and both register their δ-constants with
   [define].  It lies below both algorithms; the diagnostics are
   re-exported, as Registration.v exports Diagnostics.v. *)

open Pts_native
open Common_native
include Diagnostics_native

type registrar = { spec : spec; fuel : int; log : (stage * event list) Queue.t }

let run_steps spec fuel task =
  let r = { spec; fuel; log = Queue.create () } in
  let result = task r in
  (List.of_seq (Queue.to_seq r.log), result)

let run spec fuel task =
  let log, result = run_steps spec fuel task in
  (log, match result with
        | Ok sg -> Registered sg
        | Error (Refuse e) -> Refused e
        | Error (NoFuelAt (st, t)) -> OutOfFuelAt (st, t))

let refuse e = Error (Refuse e)

let emit r st events = Queue.add (st, events) r.log
let spec_of r = r.spec
let fuel_of r = r.fuel

let add sg entry = match sig_add sg entry with Some sg -> Ok sg | None -> refuse ROpen

(* A checker run at a stage: its events go to the log, its answer becomes
   the value, the refusal or the lack of fuel of the stage. *)
let checked r st (events, answer) =
  emit r st events;
  match answer with
  | Accepted a -> Ok a
  | Rejected e -> refuse (RRejected (st, e))
  | Undecided t -> Error (NoFuelAt (st, t))

(* [a] is a type in [gamma]: its type unfolds to a sort. *)
let sort_of r sg st gamma a =
  let* ty = checked r st (run_infer ~sg r.spec r.fuel gamma a) in
  match whnf ~sg r.fuel ty with
  | HeadForm (Srt s) -> Ok s
  | HeadForm other -> refuse (RNotAType (st, other))
  | HeadOutOfFuel _ -> Error (NoFuelAt (st, a))

(* ** δ-constants *)

(* A δ-constant, once its name is free, its type is a type and its body
   checks against it in the signature without it. *)
let define r sg f ty body =
  let* () = if Option.is_some (find_def sg f) then refuse (RTaken (Def f)) else Ok () in
  let* _ = sort_of r sg (AtDefType f) [] ty in
  let* () = checked r (AtDefBody f) (run_check ~sg r.spec r.fuel [] body ty) in
  add sg (EDef (f, ty, body))

let define_checked spec fuel sg f ty body = run spec fuel (fun r -> define r sg f ty body)
