(** * Diagnostics of registration

    The stages of a registration log, the diagnostics of both algorithms
    and the answers of a registration: declarations, instances of
    eliminators and δ-constants (Elim.Declare), histories
    (Recursion.Below) and compiled functions (Recursion.Compile).  The
    diagnostics of case trees and of recursive calls are defined here,
    below both algorithms, so that algorithm 2 depends on algorithm 1 and
    not the converse. *)

From Stdlib Require String.
From DepTypes.PTS Require Import Syntax Signature Check.
From IndTypes.Elim Require Import Decl.

Local Notation string := String.string.

(** ** Stages *)

Inductive stage : Type :=
| AtIndType : string -> stage                     (** the type of D *)
| AtCtorType : string -> string -> stage          (** D, the constructor *)
| AtField : string -> string -> nat -> stage      (** D, the constructor, the field *)
| AtElimType : string -> nat -> stage             (** D, j *)
| AtRuleLhs : string -> nat -> string -> stage    (** D, j, the constructor *)
| AtRuleRhs : string -> nat -> string -> stage
| AtDefType : string -> stage
| AtDefBody : string -> stage
| AtMotive : string -> string -> stage          (** f, the variable split: the sort of the motive *)
| AtEquation : string -> nat -> stage.          (** f, the leaf: its defining equation *)

(** ** Case trees and recursive calls (algorithm 2) *)

Inductive case_error : Type :=
| CDuplicateArg : string -> case_error            (** two arguments with one name *)
| CNoStruct : string -> case_error                (** the structural argument is no argument *)
| CUnbound : string -> case_error                 (** a name not in scope *)
| CNotFamily : string -> term -> case_error       (** a split on a variable of no declared family *)
| CIndices : string -> term -> case_error         (** its indices are not distinct variables *)
| CGeneralize : string -> string -> case_error    (** an index or the variable depends on what the split generalizes *)
| CParams : string -> string -> case_error        (** the parameters mention what the split generalizes *)
| CBranches : string -> case_error                (** the branches are not the constructors, each once *)
| CFields : string -> nat -> case_error           (** a constructor, the number of its fields *)
| CFieldName : string -> string -> case_error     (** a constructor, a field name repeated or generalized *)
(** The translation (Recursion.Compile): *)
| CRoot : string -> case_error                    (** [Direct], and the root is no split of the structural argument *)
| CUnsplit : string -> case_error                 (** a leaf reached without a split of the structural argument *)
| CMotiveSort : string -> sort -> case_error      (** the motive of a split on a variable, no universe *)
| CCallArity : term -> case_error                 (** the function, not applied to all its arguments *)
| CNotStructural : term -> case_error             (** a call on no strict subterm of the structural argument *)
| CNotImmediate : term -> case_error              (** [Direct], and a call on a subterm deeper than a field *)
| CIndexChanged : string -> term -> case_error    (** an index of the call, not that of the subterm *)
| CConstantChanged : string -> term -> case_error.  (** a constant argument changed in the call *)

(** ** Refusals and answers *)

Inductive reg_error : Type :=
| RClassify : decl_error -> reg_error
| RTaken : gref -> reg_error                      (** the name is in the signature already *)
| RUndeclared : string -> reg_error               (** an instance of a type not declared *)
| RLevel : string -> nat -> sort -> nat -> reg_error
    (** the constructor, the field, its sort, the level of D *)
| RNotAType : stage -> term -> reg_error          (** the type of the term does not unfold to a sort *)
| RRejected : stage -> error -> reg_error         (** the checker rejected the input of the stage *)
| ROpen : reg_error                               (** an entry with a free variable *)
| RCase : case_error -> reg_error        (** the case tree of a recursive function, or its calls *)
| REquation : string -> nat -> term -> term -> reg_error.
    (** f, the leaf, the two sides of its equation: not convertible *)

Inductive reg_failure : Type :=
| Refuse : reg_error -> reg_failure
| NoFuelAt : stage -> term -> reg_failure.

Inductive registration : Type :=
| Registered : signature -> registration
| Refused : reg_error -> registration
| OutOfFuelAt : stage -> term -> registration.
