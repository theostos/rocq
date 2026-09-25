(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constr
open Environ
open Esubst
open RedFlags

(** Lazy reduction. *)

(** [fconstr] is the type of frozen constr *)

type fconstr
(** [fconstr] can be accessed by using the function [fterm_of] and by
   matching on type [fterm] *)

val fconstr_hash : fconstr -> int
(** Unique identity of a cell, stable across reduction updates. *)

val min_free_rel : fconstr -> int
(** Minimum free de Bruijn index of the denoted term ([max_int] if closed);
    bounded, 1 when unknown. *)

type finvert

type evar_repack

type subs_content
type usubs = subs_content subs UVars.puniverses

type table_key = Constant.t UVars.puniverses tableKey

(** Arbitrary-precision natural held by an [FPeanoNat] cell *)
module PeanoNatValue : sig
  type t
  val equal : t -> t -> bool
end

type compact_peano = {
  peano_ind : inductive;
  peano_zero : constructor;
  peano_succ : constructor;
  peano_double : Constant.t;
  peano_value : PeanoNatValue.t;
}

(** Relevances (eg in binder_annot or case_info) have NOT been substituted
    when there is a usubs field *)
type fterm =
  | FRel of int
  | FAtom of constr (** Metas and Sorts *)
  | FFlex of table_key
  | FInd of pinductive
  | FConstruct of pconstructor * fconstr array
  | FApp of fconstr * fconstr array
  | FProj of Projection.t * Sorts.relevance * fconstr
  | FFix of fixpoint * usubs
  | FCoFix of cofixpoint * usubs
  | FCaseT of case_info * UVars.Instance.t * constr array * case_return * fconstr * case_branch array * usubs (* predicate and branches are closures *)
  | FCaseInvert of case_info * UVars.Instance.t * constr array * case_return * finvert * fconstr * case_branch array * usubs
  | FLambda of int * (Name.t binder_annot * constr) list * constr * usubs
  | FProd of Name.t binder_annot * fconstr * constr * usubs
  | FLetIn of Name.t binder_annot * fconstr * fconstr * constr * usubs
  | FEvar of Evar.t * constr list * usubs * evar_repack
  | FInt of Uint63.t
  | FFloat of Float64.t
  | FString of Pstring.t
  | FArray of UVars.Instance.t * fconstr Parray.t * fconstr
  | FPeanoNat of compact_peano
  | FLIFT of int * fconstr
  | FCLOS of constr * usubs
  | FIrrelevant
  | FLOCKED

(** The value as [zero] or [succ] of a compact value *)
val peano_constructor_view : compact_peano -> fconstr

(** Syntax-node cost of quoting a compact numeral, [None] above [limit]. *)
val peano_quotation_cost : limit:int -> compact_peano -> int option

(***********************************************************************
  s A [stack] is a context of arguments, arguments are pushed by
   [append_stack] one array at a time *)
type 'a next_native_args = (CPrimitives.arg_kind * 'a) list

type stack_member =
  | Zapp of fconstr array
  | ZcaseT of case_info * UVars.Instance.t * constr array * case_return * case_branch array * usubs
  | Zproj of Projection.Repr.t * Sorts.relevance
  | Zfix of fconstr * stack
  | Zprimitive of CPrimitives.t * pconstant * fconstr list * fconstr next_native_args
       (* operator, constr def, arguments already seen (in rev order), next arguments *)
  | Zshift of int
  | Zupdate of fconstr

and stack = stack_member list

val empty_stack : stack
val append_stack : fconstr array -> stack -> stack

val check_native_args : CPrimitives.t -> stack -> bool
val get_native_args1 : CPrimitives.t -> pconstant -> stack ->
  fconstr list * fconstr * fconstr next_native_args * stack

val get_invert : finvert -> fconstr array

val stack_args_size : stack -> int

val inductive_subst : Declarations.mutual_inductive_body
  -> UVars.Instance.t
  -> fconstr array
  -> usubs

val usubs_lift : usubs -> usubs
val usubs_liftn : int -> usubs -> usubs
val usubs_cons : fconstr -> usubs -> usubs

(** The value of a substituted variable without its lift, for inspections
    invariant under lifting; [None] for unsubstituted and higher-order ones. *)
val inspect_substituted_rel : usubs -> int -> fconstr option

(** identity if the first instance is empty *)
val usubst_instance : 'a UVars.puniverses -> UVars.Instance.t -> UVars.Instance.t

val usubst_binder : _ UVars.puniverses -> 'a binder_annot -> 'a binder_annot

(** To lazy reduce a constr, create a [clos_infos] with
   [create_clos_infos], inject the term to reduce with [inject]; then use
   a reduction function *)

val inject : constr -> fconstr

val mk_clos      : usubs -> constr -> fconstr
val mk_clos_vect : usubs -> constr array -> fconstr array

val zip : fconstr -> stack -> fconstr

val fterm_of : fconstr -> fterm

(** The spine a shared cell had before its reduction (or the cell itself),
    when it is headed by a flex. Nothing is certified: the two are convertible,
    not equal. *)
val symbolic_view : fconstr -> fconstr option
val term_of_fconstr : fconstr -> constr
val term_of_process : fconstr -> stack -> constr
val destFLambda :
  (usubs -> constr -> fconstr) -> fconstr -> Name.t binder_annot * fconstr * fconstr

(** Global and local constant cache *)
type clos_infos
type clos_tab

type 'a evar_expansion =
| EvarDefined of 'a
| EvarUndefined of Evar.t * 'a list

type evar_handler = {
  evar_expand : constr pexistential -> constr evar_expansion;
  evar_repack : Evar.t * constr list -> constr;
  evar_irrelevant : constr pexistential -> bool;
  qvar_irrelevant : Sorts.QVar.t -> bool;
  qual_equal : Sorts.Quality.t -> Sorts.Quality.t -> bool;
  abstr_const : Constant.t -> (unit, (unit -> Vmemitcodes.to_patch) Vmemitcodes.pbody_code) Declarations.pconstant_body;
}

val default_evar_handler : env -> evar_handler
val lookup_constant_handler : env -> evar_handler -> Constant.t ->
  (unit, (unit -> Vmemitcodes.to_patch) Vmemitcodes.pbody_code) Declarations.pconstant_body

val create_conv_infos :
  ?univs:UGraph.t -> ?evars:evar_handler -> reds -> env -> clos_infos
val create_clos_infos :
  ?univs:UGraph.t -> ?evars:evar_handler -> reds -> env -> clos_infos
val oracle_of_infos : clos_infos -> Conv_oracle.oracle

val create_tab : ?shared:bool -> unit -> clos_tab
(** With [shared], structurally identical cells built while reducing with the
    table are one cell: for the tables of a conversion problem. *)

val with_sharing : clos_infos -> clos_tab -> (unit -> 'a) -> 'a
(** Run a closure construction with the sharing of [whd_stack] on this table. *)

val info_env : clos_infos -> env
val info_flags: clos_infos -> reds
val info_univs : clos_infos -> UGraph.t
val unfold_projection : clos_infos -> Projection.t -> Sorts.relevance -> stack_member option

val push_relevance : clos_infos -> 'b binder_annot -> clos_infos
val push_relevances : clos_infos -> 'b binder_annot array -> clos_infos
val set_info_relevances : clos_infos -> Sorts.relevance Range.t -> clos_infos

val info_relevances : clos_infos -> Sorts.relevance Range.t

val is_irrelevant : clos_infos -> Sorts.relevance -> bool

(** Relevance of the arguments of a term of the given type; [false] entries
    are not compared by the conversion. *)
val relevance_mask : clos_infos -> UVars.Instance.t -> constr -> bool array
val eq_quality : clos_infos -> Sorts.Quality.t -> Sorts.Quality.t -> bool

val infos_with_reds : clos_infos -> reds -> clos_infos

(** Symbolic reduction: the head reduction of a conversion reads the spines
    the shared cells had before they were reduced, and does not invert cases.
    A search policy only, the caller converts as usual on a failure. *)
val infos_with_symbolic_views : clos_infos -> clos_infos

(** [with_private_closure_query ~steps infos roots inspect] runs [inspect]
    on copies of [roots] in a private call-by-need view: cells are copied when
    reduction first visits them and the caller's cells are never updated.
    Head steps and cell visits share the [steps] budget; [None] when it runs
    out or reduction meets an unsupported construct (cofixpoints, case
    inversion, primitives, symbols, evars, higher-order substitutions).
    [inspect] must reduce with the infos it receives and fresh tables. *)
val with_private_closure_query : steps:int -> clos_infos -> fconstr list ->
  (clos_infos -> fconstr list -> 'a option) -> 'a option

(** A private call-by-need view: cells are copied when first visited and the
    caller's cells are never updated. Start from an empty stack. *)
val infos_with_private_reduction : clos_infos -> clos_infos

(** The same, with [reduce] run under a bound on the cells visited; [None]
    when the bound is exhausted. Compact naturals are supported. *)
val with_bounded_private_reduction : steps:int -> clos_infos -> (clos_infos -> 'a) -> 'a option

(** Reduction function *)

(** [norm_val] is for strong normalization *)
val norm_val : clos_infos -> clos_tab -> fconstr -> constr

(** Same as [norm_val] but for terms *)
val norm_term : clos_infos -> clos_tab -> usubs -> Constr.constr -> Constr.constr

(** [whd_val] is for weak head normalization *)
val whd_val : clos_infos -> clos_tab -> fconstr -> constr

(** [whd_stack] performs weak head normalization in a given stack. It
   stops whenever a reduction is blocked. *)
val whd_stack :
  clos_infos -> clos_tab -> fconstr -> stack -> fconstr * stack

val skip_irrelevant_stack : clos_infos -> stack -> stack

val eta_expand_stack : clos_infos -> Name.t binder_annot -> stack -> stack

(** [eta_expand_ind_stack env ind args t] computes stacks corresponding
    to the conversion of the eta expansion of t, considered as an inhabitant
    of ind, and the constructor of this inductive type applied to arguments args.
    @assumes [t] is a rigid term, and not a constructor;
    that [args] are valid arguments for the constructor of inductive [ind].
    @raise Not_found if the inductive is not a primitive record, or if the
    constructor is partially applied.
 *)
val eta_expand_ind_stack : env -> pinductive -> fconstr array ->
   (fconstr * stack) -> stack * stack

val esubst_of_context : constr option list -> usubs -> usubs -> int * usubs

(** Conversion auxiliary functions to do step by step normalisation *)

(** Like [unfold_reference], but handles primitives: if there are not
    enough arguments, return [None]. Otherwise return [Some] with
    [ZPrimitive] added to the stack. Produces a [FIrrelevant] when the
    reference is irrelevant and the infos was created with
    [create_conv_infos]. *)
val unfold_ref_with_args
  : clos_infos
  -> clos_tab
  -> table_key
  -> stack
  -> (fconstr * stack) option

val get_ref_mask : clos_infos -> clos_tab -> table_key -> bool array

(** Hook for Reduction *)
val set_conv : (clos_infos -> clos_tab -> fconstr -> fconstr -> bool) -> unit
