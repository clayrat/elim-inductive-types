(** Interface of the native registration monad (Registration.v), below
    both algorithms, and of the registration of δ-constants.  The steps
    of a registration share a log; [run] starts one and returns its log
    with the answer. *)

open Pts_native

(** The diagnostics, re-exported as Registration.v exports Diagnostics.v. *)
include module type of struct include Diagnostics_native end

(** The specification, the fuel of every checker run and the log of a
    registration. *)
type registrar

val run : spec -> int -> (registrar -> (signature, failure) result) -> log * registration
val run_steps : spec -> int -> (registrar -> ('a, failure) result) -> log * ('a, failure) result
val refuse : reg_error -> ('a, failure) result

(** A stage without a checker run. *)
val emit : registrar -> stage -> event list -> unit

val spec_of : registrar -> spec
val fuel_of : registrar -> int

(** The signature with the entry, refused when the entry is not closed. *)
val add : signature -> entry -> (signature, failure) result

(** A checker run at a stage: its events go to the log, its answer becomes
    the value, the refusal or the lack of fuel of the stage. *)
val checked : registrar -> stage -> event list * 'a answer -> ('a, failure) result

(** [sort_of r sg st gamma a]: the sort [a] has in [gamma], its checker
    run logged at [st]. *)
val sort_of : registrar -> signature -> stage -> ctx -> term -> (sort, failure) result

(** {1 δ-constants} *)

(** [define r sg f ty body]: the δ-constant [f : ty := body], once [f] is
    free, [ty] is a type and [body] checks against it in [sg]. *)
val define : registrar -> signature -> string -> term -> term -> (signature, failure) result

val define_checked : spec -> int -> signature -> string -> term -> term -> log * registration
