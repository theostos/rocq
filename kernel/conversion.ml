(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Created under Benjamin Werner account by Bruno Barras to implement
   a call-by-value conversion algorithm and a lazy reduction machine
   with sharing, Nov 1996 *)
(* Addition of zeta-reduction (let-in contraction) by Hugo Herbelin, Oct 2000 *)
(* Irreversibility of opacity by Bruno Barras *)
(* Cleaning and lightening of the kernel by Bruno Barras, Nov 2001 *)
(* Equal inductive types by Jacek Chrzaszcz as part of the module
   system, Aug 2002 *)

open CErrors
open Util
open Names
open Constr
open Declarations
open Environ
open CClosure
open Esubst

let rec is_empty_stack = function
  [] -> true
  | Zupdate _::s -> is_empty_stack s
  | Zshift _::s -> is_empty_stack s
  | _ -> false

(* Compute the lift to be performed on a term placed in a given stack *)
let el_stack el stk =
  let n =
    List.fold_left
      (fun i z ->
        match z with
            Zshift n -> i+n
          | _ -> i)
      0
      stk in
  el_shft n el

let compare_stack_shape ?(check_projections = false) stk1 stk2 =
  let rec compare_rec bal stk1 stk2 =
  match (stk1,stk2) with
      ([],[]) -> Int.equal bal 0
    | ((Zupdate _|Zshift _)::s1, _) -> compare_rec bal s1 stk2
    | (_, (Zupdate _|Zshift _)::s2) -> compare_rec bal stk1 s2
    | (Zapp l1::s1, _) -> compare_rec (bal+Array.length l1) s1 stk2
    | (_, Zapp l2::s2) -> compare_rec (bal-Array.length l2) stk1 s2
    | (Zproj (p1, _)::s1, Zproj (p2, _)::s2) ->
        Int.equal bal 0 &&
        (not check_projections || Projection.Repr.CanOrd.equal p1 p2) &&
        compare_rec 0 s1 s2
    | (ZcaseT(_c1,_,_,_,_,_)::s1, ZcaseT(_c2,_,_,_,_,_)::s2) ->
        Int.equal bal 0 (* && c1.ci_ind  = c2.ci_ind *) && compare_rec 0 s1 s2
    | (Zfix(_,a1)::s1, Zfix(_,a2)::s2) ->
        Int.equal bal 0 && compare_rec 0 a1 a2 && compare_rec 0 s1 s2
    | Zprimitive(op1,_,rargs1, _kargs1)::s1, Zprimitive(op2,_,rargs2, _kargs2)::s2 ->
        bal=0 && op1=op2 && List.length rargs1=List.length rargs2 &&
        compare_rec 0 s1 s2
    | [], _ :: _
    | (Zproj _ | ZcaseT _ | Zfix _ | Zprimitive _) :: _, _ -> false
  in
  compare_rec 0 stk1 stk2

type lft_fconstr = lift * fconstr

type lft_constr_stack_elt =
    Zlapp of (lift * fconstr) array
  | Zlproj of Projection.Repr.t * lift
  | Zlfix of (lift * fconstr) * lft_constr_stack
  | Zlcase of case_info * lift * UVars.Instance.t * constr array * case_return * case_branch array * usubs
  | Zlprimitive of
     CPrimitives.t * pconstant * lft_fconstr list * lft_fconstr next_native_args
and lft_constr_stack = lft_constr_stack_elt list

let rec zlapp v = function
    Zlapp v2 :: s -> zlapp (Array.append v v2) s
  | s -> Zlapp v :: s

(** Hand-unrolling of the map function to bypass the call to the generic array
    allocation. Type annotation is required to tell OCaml that the array does
    not contain floats. *)
let map_lift (l : lift) (v : fconstr array) = match v with
| [||] -> assert false
| [|c0|] -> [|(l, c0)|]
| [|c0; c1|] -> [|(l, c0); (l, c1)|]
| [|c0; c1; c2|] -> [|(l, c0); (l, c1); (l, c2)|]
| [|c0; c1; c2; c3|] -> [|(l, c0); (l, c1); (l, c2); (l, c3)|]
| v -> Array.Fun1.map (fun l t -> (l, t)) l v

let pure_stack lfts stk =
  let rec pure_rec lfts stk =
    match stk with
        [] -> (lfts,[])
      | zi::s ->
          (match (zi,pure_rec lfts s) with
              (Zupdate _,lpstk)  -> lpstk
            | (Zshift n,(l,pstk)) -> (el_shft n l, pstk)
            | (Zapp a, (l,pstk)) ->
                (l,zlapp (map_lift l a) pstk)
            | (Zproj (p,_), (l,pstk)) ->
                (l, Zlproj (p,l)::pstk)
            | (Zfix(fx,a),(l,pstk)) ->
                let (lfx,pa) = pure_rec l a in
                (l, Zlfix((lfx,fx),pa)::pstk)
            | (ZcaseT(ci,u,pms,p,br,e),(l,pstk)) ->
                (l,Zlcase(ci,l,u,pms,p,br,e)::pstk)
            | (Zprimitive(op,c,rargs,kargs),(l,pstk)) ->
                (l,Zlprimitive(op,c,List.map (fun t -> (l,t)) rargs,
                            List.map (fun (k,t) -> (k,(l,t))) kargs)::pstk))
  in
  snd (pure_rec lfts stk)

(********************************************************************)
(*                         Conversion                               *)
(********************************************************************)

(* Conversion utility functions *)

(* functions of this type are called from the kernel *)
type 'a kernel_conversion_function = env -> 'a -> 'a -> (unit, unit) result

(* functions of this type can be called from outside the kernel *)
type 'a extended_conversion_function =
  ?l2r:bool -> ?reds:TransparentState.t -> env ->
  ?evars:evar_handler ->
  'a -> 'a -> (unit, unit) result

type payload = ..

exception NotConvertible
exception NotConvertibleTrace of payload

(* Convertibility of sorts *)

(* The sort cumulativity is

    Prop <= Set <= Type 1 <= ... <= Type i <= ...

    and this holds whatever Set is predicative or impredicative
*)

type conv_pb =
  | CONV
  | CUMUL

type ('a, 'err) universe_compare = {
  compare_sorts : conv_pb -> Sorts.t -> Sorts.t -> 'a -> ('a, 'err option) result;
  compare_instances: flex:bool -> UVars.Instance.t -> UVars.Instance.t -> 'a -> ('a, 'err option) result;
  compare_cumul_instances : conv_pb -> UVars.Variance.t array ->
    UVars.Instance.t -> UVars.Instance.t -> 'a -> ('a, 'err option) result;
}

type ('a, 'err) universe_state = 'a * ('a, 'err) universe_compare

type ('a, 'err) generic_conversion_function = ('a, 'err) universe_state -> constr -> constr -> ('a, 'err option) result

let sort_cmp_universes pb s0 s1 (u, check) =
  (check.compare_sorts pb s0 s1 u, check)

(* [flex] should be true for constants, false for inductive types and
   constructors. *)
let convert_instances ~flex u u' (s, check) =
  (check.compare_instances ~flex u u' s, check)

exception MustExpand

let convert_instances_cumul pb var u u' (s, check) =
  (check.compare_cumul_instances pb var u u' s, check)

let get_cumulativity_constraints cv_pb variance u u' =
  match cv_pb with
  | CONV ->
    UVars.enforce_eq_variance_instances variance u u' (UVars.QPairSet.empty, Univ.UnivConstraints.empty)
  | CUMUL ->
    UVars.enforce_leq_variance_instances variance u u' (UVars.QPairSet.empty, Univ.UnivConstraints.empty)

let inductive_cumulativity_arguments (mind,ind) =
  mind.Declarations.mind_nparams +
  mind.Declarations.mind_packets.(ind).Declarations.mind_nrealargs

let convert_inductives_gen cmp_instances cmp_cumul cv_pb (mind,ind) nargs u1 u2 s =
  match mind.Declarations.mind_variance with
  | None -> cmp_instances u1 u2 s
  | Some variances ->
    let num_param_arity = inductive_cumulativity_arguments (mind,ind) in
    if not (Int.equal num_param_arity nargs) then
      (* shortcut, not sure if worth doing, could use perf data *)
      if UVars.Instance.equal u1 u2 then Result.Ok s else raise MustExpand
    else
      cmp_cumul cv_pb variances u1 u2 s

type projection_conversion = {
  projection_left_lift : lift;
  projection_left_term : fconstr;
  projection_right_lift : lift;
  projection_right_term : fconstr;
  projection_relevances : Sorts.relevance Range.t;
  projection_rel_types : fconstr option Range.t;
  projection_rel_type_lifts : lift Range.t;
}

type successful_conversion = {
  conversion_problem : conv_pb;
  conversion_left_lift : lift;
  conversion_right_lift : lift;
  conversion_relevances : Sorts.relevance Range.t;
  conversion_rel_types : fconstr option Range.t;
  conversion_rel_type_lifts : lift Range.t;
}

module ConversionPairs = Hashtbl.Make (struct
  type t = fconstr * fconstr

  let equal (left1, right1) (left2, right2) =
    left1 == left2 && right1 == right2

  let hash (left, right) =
    Hashtbl.hash (fconstr_hash left, fconstr_hash right)
end)

(* A record may be compared through many different projections. Cache only
   completed source comparisons, with bounded total retention and bounded
   context variants per pair. Eviction merely repeats ordinary conversion. *)
type projection_conversion_cache = {
  projection_table : projection_conversion list ConversionPairs.t;
  mutable projection_size : int;
}

let make_projection_conversion_cache () =
  { projection_table = ConversionPairs.create 17; projection_size = 0 }

let projection_conversion_cached cache ~relevances ~rel_types ~rel_type_lifts
    left_lift left right_lift right =
  match ConversionPairs.find_opt cache.projection_table (left, right) with
  | None -> false
  | Some entries -> List.exists (fun entry ->
      eq_lift entry.projection_left_lift left_lift &&
      eq_lift entry.projection_right_lift right_lift &&
      entry.projection_relevances == relevances &&
      entry.projection_rel_types == rel_types &&
      entry.projection_rel_type_lifts == rel_type_lifts) entries

let remember_projection_conversion cache entry =
  if cache.projection_size >= 4096 then begin
    ConversionPairs.clear cache.projection_table;
    cache.projection_size <- 0
  end;
  let key = entry.projection_left_term, entry.projection_right_term in
  let previous = Option.default [] (ConversionPairs.find_opt cache.projection_table key) in
  let length = List.length previous in
  let previous = if length >= 8 then begin
    cache.projection_size <- cache.projection_size - length;
    []
  end else previous in
  ConversionPairs.replace cache.projection_table key (entry :: previous);
  cache.projection_size <- cache.projection_size + 1

(* Reuse equality of suspended syntax across reconstructed closure cells.
   The immutable templates are keys; substitutions are checked read-only in
   the same local context before reusing a completed comparison. *)
type suspended_template =
  | SuspendedTerm of constr
  | SuspendedLambda of (Name.t Constr.binder_annot * constr) list * constr

let equal_suspended_template a b = match a, b with
  | SuspendedTerm a, SuspendedTerm b -> a == b
  | SuspendedLambda (ds, body), SuspendedLambda (es, other) ->
    body == other && List.equal (fun (na, ty) (nb, other_ty) ->
      na == nb && ty == other_ty) ds es
  | _ -> false

let hash_suspended_template = function
  | SuspendedTerm body -> Hashtbl.hash (0, Hashtbl.hash_param 8 32 body)
  | SuspendedLambda (ds, body) ->
    List.fold_left (fun h (_, ty) ->
      Hashtbl.hash (h, Hashtbl.hash_param 8 32 ty))
      (Hashtbl.hash (1, Hashtbl.hash_param 8 32 body)) ds

module SuspendedPairs = Hashtbl.Make (struct
  type t = suspended_template * suspended_template
  let equal (a,b) (c,d) = equal_suspended_template a c && equal_suspended_template b d
  let hash (a,b) = Hashtbl.hash (hash_suspended_template a, hash_suspended_template b)
end)

type suspended_conversion = successful_conversion * usubs * usubs

type successful_conversion_cache = {
  suspended_table : suspended_conversion list SuspendedPairs.t;
  mutable suspended_size : int;
  successful_conversion_table :
    successful_conversion list ConversionPairs.t;
  successful_conversion_limit : int;
  mutable successful_conversion_size : int;
  mutable successful_conversion_peak : int;
  mutable successful_conversion_clears : int;
}

let successful_conversion_limit () =
  match Sys.getenv_opt "ROCQ_DIAGNOSTIC_CONVERSION_MEMO_LIMIT" with
  | None -> 32_768
  | Some value ->
    (match int_of_string_opt value with
    | Some limit when limit > 0 -> limit
    | Some _ | None -> 32_768)

let make_successful_conversion_cache limit =
  {
    suspended_table = SuspendedPairs.create 251;
    suspended_size = 0;
    successful_conversion_table =
      ConversionPairs.create (if limit > 0 then min limit 251 else 0);
    successful_conversion_limit = limit;
    successful_conversion_size = 0;
    successful_conversion_peak = 0;
    successful_conversion_clears = 0;
  }

module ConstructorMasks = Hashtbl.Make (struct
  type t = pconstructor

  let equal (constructor1, instance1) (constructor2, instance2) =
    Construct.UserOrd.equal constructor1 constructor2 &&
    UVars.Instance.equal instance1 instance2

  let hash (constructor, instance) =
    Hashtbl.hash
      (Construct.UserOrd.hash constructor, UVars.Instance.hash instance)
end)

type congruence_frame =
  | CongruenceArgument of fconstr
  | CongruenceShift of int
  | CongruenceProjection of Projection.Repr.t * Sorts.relevance

type failed_congruence = {
  failed_left_lift : lift;
  failed_right_lift : lift;
  failed_left_frames : congruence_frame list;
  failed_right_frames : congruence_frame list;
  failed_relevances : Sorts.relevance Range.t;
  failed_rel_types : fconstr option Range.t;
  failed_rel_type_lifts : lift Range.t;
}

let congruence_frames stack =
  let rec collect fuel acc = function
    | [] -> Some (List.rev acc)
    | _ when fuel <= 0 -> None
    | Zapp args :: rest when Array.length args < fuel ->
      collect (fuel - Array.length args - 1)
        (Array.fold_left (fun acc arg -> CongruenceArgument arg :: acc) acc args) rest
    | Zshift n :: rest -> collect (fuel - 1) (CongruenceShift n :: acc) rest
    | Zproj (p,r) :: rest -> collect (fuel - 1) (CongruenceProjection (p,r) :: acc) rest
    | Zupdate _ :: rest -> collect (fuel - 1) acc rest
    | (Zapp _ | Zfix _ | ZcaseT _ | Zprimitive _) :: _ -> None
  in collect 128 [] stack

let equal_congruence_frame left right = match left, right with
  | CongruenceArgument a, CongruenceArgument b -> a == b
  | CongruenceShift n, CongruenceShift m -> Int.equal n m
  | CongruenceProjection (p,r), CongruenceProjection (q,s) ->
    Projection.Repr.UserOrd.equal p q && r = s
  | (CongruenceArgument _ | CongruenceShift _ | CongruenceProjection _), _ -> false

let equal_application_context a b =
    eq_lift a.failed_left_lift b.failed_left_lift &&
    eq_lift a.failed_right_lift b.failed_right_lift &&
    a.failed_relevances == b.failed_relevances &&
    a.failed_rel_types == b.failed_rel_types &&
    a.failed_rel_type_lifts == b.failed_rel_type_lifts &&
    List.equal equal_congruence_frame a.failed_left_frames b.failed_left_frames &&
    List.equal equal_congruence_frame a.failed_right_frames b.failed_right_frames

(* Key the complete bounded process, not merely its constant names. Otherwise
   common heads such as equality continually evict unrelated argument pairs.
   Mutable closure contents must never participate in hashing: their stable
   identities do. Context equality remains physical and is checked separately. *)
module ApplicationKeys = Hashtbl.Make (struct
  type t = (pconstant * pconstant) * failed_congruence
  let equal (((c,u),(d,v)),a) (((c',u'),(d',v')),b) =
    Constant.UserOrd.equal c c' && Constant.UserOrd.equal d d' &&
    UVars.Instance.equal u u' && UVars.Instance.equal v v' &&
    equal_application_context a b
  let hash_frame h = function
    | CongruenceArgument term -> Hashtbl.hash (h, 0, fconstr_hash term)
    | CongruenceShift n -> Hashtbl.hash (h, 1, n)
    | CongruenceProjection (p,r) ->
      Hashtbl.hash (h, 2, Projection.Repr.UserOrd.hash p, r)
  let hash (((c,u),(d,v)),entry) =
    let h = Hashtbl.hash (Constant.UserOrd.hash c, UVars.Instance.hash u,
      Constant.UserOrd.hash d, UVars.Instance.hash v) in
    let left = List.fold_left hash_frame h entry.failed_left_frames in
    let right = List.fold_left hash_frame h entry.failed_right_frames in
    Hashtbl.hash (left, right, entry.failed_left_lift, entry.failed_right_lift)
end)

type failed_congruence_cache = {
  failed_table : unit ApplicationKeys.t;
  mutable failed_size : int;
  mutable failed_hits : int;
}

let make_failed_congruence_cache () =
  { failed_table = ApplicationKeys.create 17; failed_size = 0; failed_hits = 0 }

type successful_application_cache = {
  applications : conv_pb list ApplicationKeys.t;
  mutable applications_size : int;
  mutable applications_hits : int;
}

let make_successful_application_cache () =
  { applications = ApplicationKeys.create 17;
    applications_size = 0; applications_hits = 0 }

type 'e conv_tab = {
  cnv_inf : clos_infos;
  cnv_typ : bool; (* true if the input terms were well-typed *)
  cnv_rel_types : fconstr option Range.t;
  cnv_rel_type_lifts : lift Range.t;
  (* Remaining depth, shared within one speculative congruence check. *)
  cnv_probe_budget : int ref option;
  cnv_strategy_budget : int ref option;
  cnv_symbolic_budget : int ref option;
  cnv_symbolic_remaining : int ref;
  cnv_failed_symbolic : projection_conversion_cache;
  cnv_projection_conversions : projection_conversion_cache;
  cnv_successful_conversions : successful_conversion_cache;
  cnv_memoize_successful_conversions : bool;
  cnv_projection_congruence : bool;
  cnv_dependency_preference : bool;
  cnv_constructor_relevance : bool;
  cnv_constructor_masks : bool array ConstructorMasks.t;
  cnv_failed_congruences : failed_congruence_cache;
  cnv_successful_applications : successful_application_cache;
  lft_tab : clos_tab;
  rgt_tab : clos_tab;
  err_ret : 'e -> payload;
}
(** Invariant: for any tl ∈ lft_tab and tr ∈ rgt_tab, there is no mutable memory
    location contained both in tl and in tr. *)

let fail_check (infos : 'err conv_tab) (state, check) = match state with
| Result.Ok state -> (state, check)
| Result.Error None -> raise NotConvertible
| Result.Error (Some err) -> raise (NotConvertibleTrace (infos.err_ret err))

exception Probe_budget_exhausted
exception Strategy_budget_exhausted
exception Symbolic_budget_exhausted

(* Congruence can compare branches that evaluation of the actual application
   would discard. Limit its nesting depth, not ordinary conversion:
   the owner of the budget turns exhaustion into the usual unfolding fallback.
   Nested comparisons share the counter and must not catch exhaustion. *)
let with_congruence_budget infos compare =
  if Option.has_some infos.cnv_probe_budget ||
     not (Environ.typing_flags (info_env infos.cnv_inf)).unfold_dep_heuristic
  then compare infos
  else
    try compare { infos with cnv_probe_budget = Some (ref 256) }
    with Probe_budget_exhausted -> raise NotConvertible

(* This is a failed SHORTCUT cache, never a negative conversion cache. A hit
   only selects the ordinary unfolding fallback for transparent definitions.
   No entry can certify equality, bypass an opaque head, or reject a term. *)
let application_key infos lft1 lft2 fl1 stk1 fl2 stk2 =
  match fl1, fl2, congruence_frames stk1, congruence_frames stk2 with
    | ConstKey c, ConstKey d, Some left, Some right when infos.cnv_typ ->
      Some ((c,d), {
        failed_left_lift = lft1; failed_right_lift = lft2;
        failed_left_frames = left; failed_right_frames = right;
        failed_relevances = info_relevances infos.cnv_inf;
        failed_rel_types = infos.cnv_rel_types;
        failed_rel_type_lifts = infos.cnv_rel_type_lifts })
    | _ -> None

let try_congruence infos lft1 lft2 fl1 stk1 fl2 stk2 compare =
  let key = application_key infos lft1 lft2 fl1 stk1 fl2 stk2 in
  let cache = infos.cnv_failed_congruences in
  let hit = match key with
    | Some key -> ApplicationKeys.mem cache.failed_table key
    | None -> false in
  if hit then begin
    cache.failed_hits <- cache.failed_hits + 1;
    if Option.has_some (Sys.getenv_opt "ROCQ_DIAGNOSTIC_CONVERSION_ENTRIES") &&
       cache.failed_hits land (cache.failed_hits - 1) = 0 then
      Printf.eprintf "[failed congruence] hits=%d entries=%d\n%!"
        cache.failed_hits cache.failed_size;
    raise NotConvertible
  end;
  try with_congruence_budget infos compare with
  | (NotConvertible | NotConvertibleTrace _) as error ->
    begin match key with
    | None -> ()
    | Some key ->
      if cache.failed_size >= 4096 then begin
        ApplicationKeys.clear cache.failed_table; cache.failed_size <- 0 end;
      if not (ApplicationKeys.mem cache.failed_table key) then begin
        ApplicationKeys.add cache.failed_table key ();
        cache.failed_size <- cache.failed_size + 1
      end
    end;
    raise error

let completed_application infos problem key =
  let cache = infos.cnv_successful_applications in
  match key with
  | None -> false
  | Some key ->
    let hit = List.mem problem
      (Option.default [] (ApplicationKeys.find_opt cache.applications key)) in
    if hit then begin
      cache.applications_hits <- cache.applications_hits + 1;
      if Option.has_some (Sys.getenv_opt "ROCQ_DIAGNOSTIC_CONVERSION_ENTRIES") &&
         cache.applications_hits land (cache.applications_hits - 1) = 0 then
        Printf.eprintf "[completed application] hits=%d entries=%d\n%!"
          cache.applications_hits cache.applications_size
    end;
    hit

let remember_application infos problem key =
  match key with
  | None -> ()
  | Some key ->
    let cache = infos.cnv_successful_applications in
    if cache.applications_size >= 32768 then begin
      ApplicationKeys.clear cache.applications; cache.applications_size <- 0 end;
    let old = Option.default [] (ApplicationKeys.find_opt cache.applications key) in
    if not (List.mem problem old) then begin
      ApplicationKeys.replace cache.applications key (problem :: old);
      cache.applications_size <- cache.applications_size + 1
    end

let convert_inductives cv_pb ind nargs u1 u2 (s, check) =
  convert_inductives_gen (check.compare_instances ~flex:false) check.compare_cumul_instances
    cv_pb ind nargs u1 u2 s, check

let constructor_cumulativity_arguments (mind, ind, ctor) =
  mind.Declarations.mind_nparams +
  mind.Declarations.mind_packets.(ind).Declarations.mind_consnrealargs.(ctor - 1)

let convert_constructors_gen cmp_instances cmp_cumul (mind, ind, cns) nargs u1 u2 s =
  match mind.Declarations.mind_variance with
  | None -> cmp_instances u1 u2 s
  | Some _ ->
    let num_cnstr_args = constructor_cumulativity_arguments (mind,ind,cns) in
    if not (Int.equal num_cnstr_args nargs) then
      if UVars.Instance.equal u1 u2 then Result.Ok s else raise MustExpand
    else
      (** By invariant, both constructors have a common supertype,
          so they are convertible _at that type_. *)
      (* NB: no variance for qualities *)
      let variance = Array.make (snd (UVars.Instance.length u1)) UVars.Variance.Irrelevant in
      cmp_cumul CONV variance u1 u2 s

let convert_constructors ctor nargs u1 u2 (s, check) =
  convert_constructors_gen (check.compare_instances ~flex:false) check.compare_cumul_instances
    ctor nargs u1 u2 s, check

let conv_table_key infos ~nargs k1 k2 cuniv =
  if k1 == k2 then cuniv else
  match k1, k2 with
  | ConstKey (cst, u), ConstKey (cst', u') when Constant.CanOrd.equal cst cst' ->
    if UVars.Instance.equal u u' then cuniv
    else if Int.equal nargs 1 && is_array_type (info_env infos.cnv_inf) cst then cuniv
    else
      let flex = evaluable_constant cst (info_env infos.cnv_inf)
        && RedFlags.red_set (info_flags infos.cnv_inf) (RedFlags.fCONST cst)
      in fail_check infos @@ convert_instances ~flex u u' cuniv
  | VarKey id, VarKey id' when Id.equal id id' -> cuniv
  | RelKey n, RelKey n' when Int.equal n n' -> cuniv
  | _ -> raise NotConvertible

let same_args_size sk1 sk2 =
  let n = CClosure.stack_args_size sk1 in
  if Int.equal n (CClosure.stack_args_size sk2) then n
  else raise NotConvertible

(* Lean's primitive recursors compute before lazy delta/congruence. Generated
   Rocq eliminators instead have an ordinary constant around a Fix or Case.
   Recognize a constructor at the actual major premise, including LocalDef
   aliases, so discarded branches or the other operand are not forced first.
   This bounded, read-only observation only selects ordinary unfolding: it
   neither contracts the eliminator nor establishes a conversion judgment. *)
let visible_constructor_head env term =
  let rec local_constructor fuel index =
    if fuel = 0 || index <= 0 || index > 4096 then false else
    match Environ.lookup_rel index env with
    | Context.Rel.Declaration.LocalAssum _ -> false
    | Context.Rel.Declaration.LocalDef (_, body, _) ->
      (* [body] lives in the context below this declaration. Track its lift
         arithmetically; do not quote, copy or lift a possibly large body. *)
      raw_constructor (fuel - 1) index body
    | exception Not_found -> false
  and raw_constructor fuel offset body =
    if fuel = 0 then false else match Constr.kind body with
    | Construct _ -> true
    | App (head, _) -> (match Constr.kind head with Construct _ -> true | _ -> false)
    | Rel index when index > 0 && index <= 4096 - offset ->
      local_constructor (fuel - 1) (index + offset)
    | _ -> false
  and constructor fuel term =
    if fuel = 0 then false else match fterm_of term with
    | FConstruct _ | FPeanoNat _ -> true
    | FFlex (RelKey index) -> local_constructor (fuel - 1) index
    | FLIFT (_, term) -> constructor (fuel - 1) term
    | FCLOS (body, subst) -> begin match Constr.kind body with
      | Construct _ -> true
      | App (head, _) -> (match Constr.kind head with Construct _ -> true | _ -> false)
      | Rel index -> (match inspect_substituted_rel subst index with
        | Some term -> constructor (fuel - 1) term
        | None -> (match expand_rel index (fst subst) with
          | Inr (_, Some index) -> local_constructor (fuel - 1) index
          | Inr (_, None) | Inl _ -> false))
      | _ -> false end
    | _ -> false in
  constructor 16 term

(* This is demanded reduction, not a speculative type or equality query.
   Lean's [whnf_core(..., cheap_rec=false)] computes a recursor's major using
   [whnf] before selecting its branch. Generated Rocq recursors are ordinary
   definitions, so do the same when their structural argument is available.
   Use a private call-by-need view of the ordinary reduction machine and its
   compact natural operations, with the current transparency. A stuck demand
   must retain the original symbolic call, as Lean's immutable expressions do.
   Do not abandon this dependency
   after an arbitrary number of steps and expand the other operand instead.
   Ordinary conversion remains responsible for the resulting judgment. *)
let reduce_constructor_major ?(tab = create_tab ()) infos term =
  let reds = RedFlags.(red_add_transparent all (red_transparent (info_flags infos))) in
  let head, stack = whd_stack
    (infos_with_private_reduction (infos_with_reds infos reds)) tab term [] in
  if is_empty_stack stack then
    (match fterm_of head with FConstruct _ | FPeanoNat _ -> Some head | _ -> None)
  else None

let constructor_eliminator_major infos reference =
  let env = info_env infos.cnv_inf in
  if not infos.cnv_typ || not (Environ.typing_flags env).unfold_dep_heuristic
  then None else
  let rec major parameters body =
    match Constr.kind body with
    | Lambda (_, _, body) -> major (parameters + 1) body
    | Fix ((indices, selected), _) when
        selected >= 0 && selected < Array.length indices ->
      let index = indices.(selected) in
      if index >= 0 then Some (parameters + index) else None
    | Case (_, _, _, _, _, subject, _) ->
      (match Constr.kind subject with
       | Rel index when index > 0 && index <= parameters -> Some (parameters - index)
       | _ -> None)
    | _ -> None in
  match reference with
  | ConstKey (constant, instance) when
      not (is_irrelevant infos.cnv_inf
        (UVars.subst_instance_relevance instance (Environ.constant_relevance constant env))) &&
      RedFlags.red_set (info_flags infos.cnv_inf) (RedFlags.fCONST constant) &&
      Conv_oracle.is_transparent (Conv_oracle.get_strategy
        (oracle_of_infos infos.cnv_inf) (Conv_oracle.EvalConstRef constant)) ->
    begin match (Environ.lookup_constant constant (info_env infos.cnv_inf)).const_body with
    | Def body -> major 0 body
    | _ -> None end
  | _ -> None

let constructor_eliminator_application infos reference stack =
  let rec argument index = function
    | Zapp args :: rest ->
      if index < Array.length args then
        visible_constructor_head (info_env infos.cnv_inf) args.(index)
      else argument (index - Array.length args) rest
    | (Zshift _ | Zupdate _) :: rest -> argument index rest
    | _ -> false in
  match constructor_eliminator_major infos reference with
  | Some index -> argument index stack
  | None -> false

(* Carry a reduced major into ordinary iota conversion. Merely
   observing it and then unfolding the wrapper can get stuck on the original
   projection again, causing congruence to compare discarded Fix/Case branches.
   Reduction uses private, demand-copied cells; putting its reduced root
   into a copied application frame does not overwrite the caller's cells or arrays.
   Keep all application suffixes, shifts and update frames in place. *)
let expose_eliminator_major ?tab infos reference stack =
  let rec replace prefix index = function
    | Zapp args :: rest when index < Array.length args ->
      (match reduce_constructor_major ?tab infos.cnv_inf args.(index) with
       | None -> None
       | Some major ->
         let args = Array.copy args in
         args.(index) <- major;
         Some (List.rev_append prefix (Zapp args :: rest)))
    | (Zapp args as frame) :: rest ->
      replace (frame :: prefix) (index - Array.length args) rest
    | ((Zshift _ | Zupdate _) as frame) :: rest ->
      replace (frame :: prefix) index rest
    | _ -> None in
  match constructor_eliminator_major infos reference with
  | Some index -> Option.default stack (replace [] index stack)
  | None -> stack

(* A direct head alias exposes the other symbolic call without evaluating it.
   This observation only schedules delta, and is used when both references
   have already been found unfoldable. Do not traverse argument trees or
   follow a transitive dependency graph for this cheap preference. *)
let direct_head_alias env source target =
  let rec head target fuel body =
    if fuel = 0 then false else match Constr.kind body with
    | Lambda (_, _, body) | Cast (body, _, _) | App (body, _) ->
      head target (fuel - 1) body
    | Const (constant, _) -> Constant.UserOrd.equal constant target
    | _ -> false
  in
  match source, target with
  | ConstKey (source, _), ConstKey (target, _)
    when not (Constant.UserOrd.equal source target) ->
    (match (Environ.lookup_constant source env).const_body with
     | Def body -> head target 64 body
     | _ -> false)
  | _ -> false

(* Unfold syntactic constructor and projection wrappers before eta adds
   projections that may force the implementation of their fields. Keep eta
   first for other definitions: fully unfolding a record-producing computation
   can expand a large stuck elimination. This is only an unfolding preference;
   the exposed terms still undergo ordinary conversion. Follow a bounded
   number of transparent head aliases, including named primitive projections. *)
let record_wrapper infos reference stack =
  let env = info_env infos.cnv_inf in
  let transparent constant =
    RedFlags.red_set (info_flags infos.cnv_inf) (RedFlags.fCONST constant)
  in
  let rec wrapper_head fuel term =
    match Constr.kind term with
    | Lambda (_, _, body) -> wrapper_head fuel body
    | App (head, _) -> wrapper_head fuel head
    | Construct _ | Proj _ -> true
    | Const (constant, _) when fuel > 0 && transparent constant ->
      begin match (Environ.lookup_constant constant env).Declarations.const_body with
      | Def body -> wrapper_head (fuel - 1) body
      | Undef _ | OpaqueDef _ | Primitive _ | Symbol _ -> false
      end
    | _ -> false
  in
  let applications_only = List.for_all (function
    | Zapp _ | Zupdate _ | Zshift _ -> true
    | Zproj _ | Zfix _ | ZcaseT _ | Zprimitive _ -> false)
  in
  match reference with
  | ConstKey (constant, _) when applications_only stack && transparent constant ->
    begin match (Environ.lookup_constant constant env).Declarations.const_body with
    | Def body -> wrapper_head 32 body
    | Undef _ | OpaqueDef _ | Primitive _ | Symbol _ -> false
    end
  | ConstKey _ | RelKey _ | VarKey _ -> false

(* After direct occurrences have been checked, a decisive declared priority
   does not require searching transitive dependencies. Direct occurrences must
   remain stronger: the opposing head can occur inside a projected record field,
   which Lean's projection step exposes before consulting delta hints. The
   translated closure machine instead sees a constant with a projection stack.
   For a tie, retain the fallback's probe evaluation order: constructor
   inspection may update closures seen by the dependency query. *)
type unfolding_action = Unfold_left | Unfold_right | Unfold_both

let unfolding_side left = if left then Unfold_left else Unfold_right

let choose_unfolding_action ~order ~l2r ~heuristic ~compact1 ~compact2
    ~direct_dependency ~dependency ~constructor =
  let fallback () =
    if compact1 <> compact2 then unfolding_side compact2 else
    match order with
    | Conv_oracle.Left -> Unfold_left
    | Conv_oracle.Right -> Unfold_right
    | Conv_oracle.Same -> if heuristic then Unfold_both else unfolding_side l2r
  in
  if not heuristic then fallback () else
  match order with
  | Conv_oracle.Left | Conv_oracle.Right ->
    (match direct_dependency () with
     | Some left -> unfolding_side left
     | None -> unfolding_side (order = Conv_oracle.Left))
  | Conv_oracle.Same ->
    let constructor = constructor () in
    match dependency (), constructor with
    | Some left, _ | None, Some left -> unfolding_side left
    | None, None -> fallback ()

(* No application or other elimination follows the first projection. *)
let bare_projection_stack stack =
  let rec inspect projected = function
    | [] -> projected
    | (Zshift _ | Zupdate _) :: rest -> inspect projected rest
    | Zapp args :: rest when not projected || Array.is_empty args -> inspect projected rest
    | Zproj _ :: rest -> inspect true rest
    | (Zapp _ | Zfix _ | ZcaseT _ | Zprimitive _) :: _ -> false
  in inspect false stack

(* A function application whose head is a projection must expose that field
   before congruence compares the arguments of its record source. In particular,
   transparent aliases of instance constructors need the same treatment as
   constructor wrappers themselves. This is Lean's non-cheap projection WHNF
   phase before application congruence; bare projections retain their separate
   lazy source comparison below. No equality is concluded by this preference. *)
let applied_projection_source infos reference stack =
  let rec inspect arguments projected = function
    | (Zshift _ | Zupdate _) :: rest -> inspect arguments projected rest
    | Zapp args :: rest when Array.is_empty args -> inspect arguments projected rest
    | Zapp _ :: _ when projected -> arguments
    | Zapp _ :: rest -> inspect true projected rest
    | Zproj _ :: rest -> inspect arguments true rest
    | [] | (Zfix _ | ZcaseT _ | Zprimitive _) :: _ -> false
  in
  let env = info_env infos.cnv_inf in
  (Environ.typing_flags env).unfold_dep_heuristic &&
  inspect false false stack &&
  match reference with
  | ConstKey (constant, _) when
      RedFlags.red_set (info_flags infos.cnv_inf) (RedFlags.fCONST constant) ->
    begin match (Environ.lookup_constant constant env).Declarations.const_body with
    | Def _ -> true
    | Undef _ | OpaqueDef _ | Primitive _ | Symbol _ -> false
    end
  | ConstKey _ | RelKey _ | VarKey _ -> false

(* Project function-valued or forwarded fields before comparing the parameters
   of their transparent constructor wrapper. Do not extend this preference to
   arbitrary computed fields: those can start expensive arithmetic. *)
let projected_record_wrapper infos reference stack =
  let env = info_env infos.cnv_inf in
  let rec projections fuel stack =
    if fuel = 0 then None else match stack with
    | (Zshift _ | Zupdate _) :: stack -> projections (fuel - 1) stack
    | Zproj (projection, _) :: stack ->
      Option.map (fun rest -> projection :: rest) (projections (fuel - 1) stack)
    | _ -> Some []
  in
  (* Only arguments BEFORE the first projection belong to the wrapper.
     With no such arguments there is nothing to discard: keep the common
     projected method head for ordinary congruence instead of expanding its
     implementation merely because it is stored in a constant record. *)
  let rec projection fuel has_arguments stack =
    if fuel = 0 then None else
    match stack with
    | Zapp arguments :: stack ->
      projection (fuel - 1) (has_arguments || not (Array.is_empty arguments)) stack
    | (Zshift _ | Zupdate _) :: stack -> projection (fuel - 1) has_arguments stack
    | Zproj (projection, _) :: stack when has_arguments ->
      Option.map (fun rest -> projection :: rest) (projections (fuel - 1) stack)
    | [] | (Zproj _ | Zfix _ | ZcaseT _ | Zprimitive _) :: _ -> None
  in
  (* Bypassing argument congruence is a separate decision from choosing an
     unfolding side. Only the established forwarding/function-field shapes
     justify trying wrapper exposure before comparing its arguments. *)
  let rec forwarded fuel term = match Constr.kind term with
    | Rel _ | Lambda _ -> true
    | Proj (_, _, source) when fuel > 0 -> forwarded (fuel - 1) source
    | (Const _ | App _) when fuel > 0 ->
      let head, args = Constr.decompose_app term in
      begin match Constr.kind head with
      | Const (constant, _) when
          RedFlags.red_set (info_flags infos.cnv_inf) (RedFlags.fCONST constant) ->
        begin match (Environ.lookup_constant constant env).Declarations.const_body with
        | Def body ->
          let binders, body = Term.decompose_lambda body in
          let arity = List.length binders in
          if Array.length args < arity && forwarded (fuel - 1) body then true else
          begin match Constr.kind body with
          | Proj (_, _, source) when isRel source ->
            let index = arity - destRel source in
            index >= 0 && index < arity &&
            (Array.length args <= index || forwarded (fuel - 1) args.(index)) &&
            Array.for_all_i (fun i arg -> i < arity || isRel arg) 0 args
          | _ -> false
          end
        | Undef _ | OpaqueDef _ | Primitive _ | Symbol _ -> false
        end
      | Rel _ | Proj _ ->
        forwarded (fuel - 1) head && Array.for_all (forwarded (fuel - 1)) args
      | _ -> false
      end
    | _ -> false
  in
  let rec selects_field fuel method_field projections body =
    if fuel = 0 then false else
    match projections, Constr.kind body with
    | [], _ -> false
    | _, Lambda (_, _, body) -> selects_field (fuel - 1) method_field projections body
    | _, LetIn (_, _, _, body) when method_field ->
      selects_field (fuel - 1) method_field projections body
    | projection :: rest, _ ->
      let head, arguments = Constr.decompose_app body in
      begin match Constr.kind head with
      | Construct ((ind, 1), _)
        when Environ.QInd.equal env ind (Projection.Repr.inductive projection) ->
        let field = Projection.Repr.npars projection + Projection.Repr.arg projection in
        field >= 0 && field < Array.length arguments &&
        (forwarded 32 arguments.(field) ||
          selects_field (fuel - 1) method_field rest arguments.(field))
      | _ -> false
      end
  in
  (* This only chooses a delta-reduction order; it never establishes equality
     or erases an argument itself. It is therefore useful on the conservative
     API too (notably the independent checker's final type comparison). *)
  if not (Environ.typing_flags env).unfold_dep_heuristic
  then false
  else match reference, projection 1024 false stack with
  | ConstKey (constant, _), Some projections
    when RedFlags.red_set (info_flags infos.cnv_inf) (RedFlags.fCONST constant) ->
    begin match (Environ.lookup_constant constant env).Declarations.const_body with
    | Def body ->
      let method_field =
        let last = Projection.make (List.last projections) false in
        let _, ty = Environ.lookup_projection last env in
        isProd ty
      in
      selects_field 1024 method_field projections body
    | Undef _ | OpaqueDef _ | Primitive _ | Symbol _ -> false
    end
  | _ -> false

(** The same heap separation invariant must hold for the fconstr arguments
    passed to each respective side of the conversion function below. *)

let rec direct_inductive typ =
  match fterm_of typ with
  | FInd (ind, _) -> Some ind
  | FApp (head, _) | FLIFT (_, head) -> direct_inductive head
  | FCLOS (term, _) ->
    let head, _ = Constr.decompose_app term in
    begin match Constr.kind head with
    | Constr.Ind (ind, _) -> Some ind
    | _ -> None
    end
  | _ -> None

let unit_like_index = ref ([], Indset_env.empty)

let is_registered_unit_like env ind =
  let registered = (Environ.retroknowledge env).Retroknowledge.retro_unit_like in
  let previous, index = !unit_like_index in
  let index =
    if registered == previous then index
    else begin
      let index = Indset_env.of_list registered in
      unit_like_index := registered, index;
      index
    end
  in
  Indset_env.mem ind index

let direct_registered_unit_like infos typ =
  let env = info_env infos.cnv_inf in
  match direct_inductive typ with
  | Some ind when is_registered_unit_like env ind -> Some ind
  | Some _ | None -> None

let constructor_relevance_mask infos (((ind, _), instance) as constructor) =
  match ConstructorMasks.find_opt infos.cnv_constructor_masks constructor with
  | Some mask -> mask
  | None ->
    let env = info_env infos.cnv_inf in
    let spec = Inductive.lookup_mind_specif env ind in
    let constructor_type =
      Inductive.type_of_constructor constructor spec
    in
    let binders, _ = Term.decompose_prod constructor_type in
    let mask_arguments =
      binders
      |> List.rev
      |> List.map (fun (binder, _) ->
           let relevance =
             UVars.subst_instance_relevance instance
               binder.Context.binder_relevance
           in
           not (is_irrelevant infos.cnv_inf relevance))
      |> Array.of_list
    in
    let mask_arguments =
      if Array.exists (fun compare -> not compare) mask_arguments
      then mask_arguments
      else [||]
    in
    ConstructorMasks.add infos.cnv_constructor_masks constructor mask_arguments;
    mask_arguments

let rel_type infos n =
  let local_depth = Range.length infos.cnv_rel_types in
  if n <= local_depth then Range.get infos.cnv_rel_types (n - 1)
  else
    let env = info_env infos.cnv_inf in
    try
      let decl = Environ.lookup_rel (n - local_depth) env in
      Some (inject (Context.Rel.Declaration.get_type decl))
    with Not_found -> None

let rel_type_lifted infos n =
  Option.map (fun typ ->
    let depth = Range.length infos.cnv_rel_types in
    let lift = if n <= depth then Range.get infos.cnv_rel_type_lifts (n - 1)
      else el_id in
    (* First interpret the domain in its binder's original context, then
       weaken through that binder and all subsequently introduced binders. *)
    el_shft n (el_liftn n lift), typ) (rel_type infos n)

let push_relevance ?(typ = None) ?(type_lift = el_id) infos r =
  { infos with
    cnv_inf = CClosure.push_relevance infos.cnv_inf r;
    cnv_rel_types = Range.cons typ infos.cnv_rel_types;
    cnv_rel_type_lifts = Range.cons type_lift infos.cnv_rel_type_lifts }

let push_relevances infos nas =
  { infos with
    cnv_inf = CClosure.push_relevances infos.cnv_inf nas;
    cnv_rel_types =
      Array.fold_left (fun types _ -> Range.cons None types)
        infos.cnv_rel_types nas;
    cnv_rel_type_lifts =
      Array.fold_left (fun lifts _ -> Range.cons el_id lifts)
        infos.cnv_rel_type_lifts nas }

let identity_of_ctx (ctx:Constr.rel_context) =
  Context.Rel.instance mkRel 0 ctx

let get_template_instance mib u = match mib.mind_template with
| None -> u
| Some templ ->
  let () = assert (UVars.Instance.is_empty u) in
  templ.template_defaults

(* ind -> fun args => ind args *)
let eta_expand_ind env (ind,u as pind) =
  let mib = Environ.lookup_mind (fst ind) env in
  let mip = mib.mind_packets.(snd ind) in
  let ctx = Vars.subst_instance_context (get_template_instance mib u) mip.mind_arity_ctxt in
  let args = identity_of_ctx ctx in
  let c = mkApp (mkIndU pind, args) in
  let c = Term.it_mkLambda_or_LetIn c ctx in
  inject c

let eta_expand_constructor env ((ind,ctor),u as pctor) =
  let mib = Environ.lookup_mind (fst ind) env in
  let mip = mib.mind_packets.(snd ind) in
  let ctx = Vars.subst_instance_context (get_template_instance mib u) (fst mip.mind_nf_lc.(ctor-1)) in
  let args = identity_of_ctx ctx in
  let c = mkApp (mkConstructU pctor, args) in
  let c = Term.it_mkLambda_or_LetIn c ctx in
  inject c

let irr_flex infos = function
  | ConstKey (con,u) -> is_irrelevant infos @@ UVars.subst_instance_relevance u @@ Environ.constant_relevance con (info_env infos)
  | VarKey x -> is_irrelevant infos @@ Context.Named.Declaration.get_relevance (Environ.lookup_named x (info_env infos))
  | RelKey x -> is_irrelevant infos @@ Context.Rel.Declaration.get_relevance (Environ.lookup_rel x (info_env infos))

let eq_universes (_,e1) (_,e2) u1 u2 =
  let subst e u = if UVars.Instance.is_empty e then u else UVars.subst_instance_instance e u in
  UVars.Instance.equal (subst e1 u1) (subst e2 u2)

let eq_usubs_fast (s1, u1) (s2, u2) =
  (s1 == s2 || (Esubst.is_subs_id s1 && Esubst.is_subs_id s2)) &&
  (u1 == u2 || UVars.Instance.equal u1 u2)

(* A read-only syntactic shortcut, including regular suspended substitutions.
   Exhausting the shared node budget is inconclusive: ordinary conversion
   remains responsible for reduction, higher-order substitutions and any
   remaining equality checks. *)
(* One read-only syntactic probe owns this memo. It remembers only completed
   structural equalities; substitutions and relocations remain part of every
   key. Every visit, including a hit, consumes the existing node allowance.
   Thus separately allocated DAGs are compared with sharing, not expanded as
   trees. No result crosses a probe or survives a reduction of its operands. *)
type syntax_pair =
  | SyntaxPair of constr * usubs * constr * usubs
  | ClosurePair of fconstr * lift * fconstr * lift

module SyntaxPairs = Hashtbl.Make (struct
  type t = syntax_pair
  let equal left right = match left, right with
    | SyntaxPair (a,e,b,f), SyntaxPair (c,g,d,h) ->
      (* FCLOS inspection rebuilds the (substitution, universe-instance)
         wrapper. Its allocation is not part of the substitution's meaning:
         retain the same component equality used by the identity shortcut. *)
      a == c && b == d && eq_usubs_fast e g && eq_usubs_fast f h
    | ClosurePair (a,e,b,f), ClosurePair (c,g,d,h) ->
      a == c && b == d && eq_lift e g && eq_lift f h
    | _ -> false
  let hash = function
    | SyntaxPair (a,_,b,_) -> Hashtbl.hash_param 8 32 (0,a,b)
    | ClosurePair (a,_,b,_) ->
      (* Keep relocation equality exact. Hashing only stable closure identities
         is sufficient; collisions are checked with [eq_lift]. *)
      Hashtbl.hash (1, fconstr_hash a, fconstr_hash b)
end)

let syntax_cached memo = function
  | None -> false
  | Some key -> Lazy.is_val memo && SyntaxPairs.mem (Lazy.force memo) key

let remember_syntax memo = function
  | None -> ()
  | Some key -> SyntaxPairs.replace (Lazy.force memo) key ()

let rec compare_under ?(symbolic=false) ?(memo=lazy (SyntaxPairs.create 17)) budget e1 c1 e2 c2 =
  if !budget <= 0 then false else begin
  decr budget;
  if c1 == c2 && eq_usubs_fast e1 e2 then true else
  let key = match Constr.kind c1 with
    | App _ | Lambda _ | Prod _ | LetIn _ | Proj _ | Cast _ | Fix _ | CoFix _ | Array _ ->
      Some (SyntaxPair (c1, e1, c2, e2))
    | _ -> None in
  if syntax_cached memo key then true else
  let equal = match Constr.kind c1, Constr.kind c2 with
  | Cast (c1, _, _), _ -> compare_under ~symbolic ~memo budget e1 c1 e2 c2
  | _, Cast (c2, _, _) -> compare_under ~symbolic ~memo budget e1 c1 e2 c2
  | Rel i, Rel j -> begin
      match Esubst.expand_rel i (fst e1), Esubst.expand_rel j (fst e2) with
      | Inl (shift1, _), Inl (shift2, _) ->
        (* Carry the relocations instead of using [mk_clos] on the variables:
           the latter can eagerly copy a whole lifted constructor tree before
           this bounded comparison even starts. The inspector deliberately
           declines higher-order substitutions, whose lifts differ. *)
        (match CClosure.inspect_substituted_rel e1 i,
               CClosure.inspect_substituted_rel e2 j with
        | Some term1, Some term2 ->
          fast_test_under ~symbolic ~memo budget (el_shft shift1 el_id) term1
            (el_shft shift2 el_id) term2
        | _ -> false)
      | Inr (k, _), Inr (k', _) -> Int.equal k k'
      | (Inl _ | Inr _), _ -> false
    end
  | Meta m1, Meta m2 -> Int.equal m1 m2
  | Var id1, Var id2 -> Id.equal id1 id2
  | Int i1, Int i2 -> Uint63.equal i1 i2
  | Float f1, Float f2 -> Float64.equal f1 f2
  | String s1, String s2 -> Pstring.equal s1 s2
  | Sort s1, Sort s2 ->
    let subst_instance_sort u s =
      if UVars.Instance.is_empty u then s else UVars.subst_instance_sort u s
    in
    let s1 = subst_instance_sort (snd e1) s1
    and s2 = subst_instance_sort (snd e2) s2 in
    Sorts.equal s1 s2
  | Prod (_,t1,c1), Prod (_,t2,c2) ->
    compare_under ~symbolic ~memo budget e1 t1 e2 t2
    && compare_under ~symbolic ~memo budget (usubs_lift e1) c1 (usubs_lift e2) c2
  | Lambda (_,t1,c1), Lambda (_,t2,c2) ->
    compare_under ~symbolic ~memo budget e1 t1 e2 t2
    && compare_under ~symbolic ~memo budget (usubs_lift e1) c1 (usubs_lift e2) c2
  | LetIn (_,b1,_,c1), LetIn (_,b2,_,c2) ->
    (* don't care about types when bodies are equal *)
    compare_under ~symbolic ~memo budget e1 b1 e2 b2
    && compare_under ~symbolic ~memo budget (usubs_lift e1) c1 (usubs_lift e2) c2
  | App (c1, l1), App (c2, l2) ->
    let len = Array.length l1 in
    Int.equal len (Array.length l2)
    && compare_under ~symbolic ~memo budget e1 c1 e2 c2
    && Array.equal_norefl (fun c1 c2 -> compare_under ~symbolic ~memo budget e1 c1 e2 c2) l1 l2
  | Proj (p1,_,c1), Proj (p2,_,c2) ->
    Projection.UserOrd.equal p1 p2 && compare_under ~symbolic ~memo budget e1 c1 e2 c2
  | Evar _, Evar _ -> false
  | Const (c1,u1), Const (c2,u2) ->
    (* The args length currently isn't used but may as well pass it. *)
    Constant.UserOrd.equal c1 c2 && eq_universes e1 e2 u1 u2
  | Ind (c1,u1), Ind (c2,u2) -> Ind.UserOrd.equal c1 c2 && eq_universes e1 e2 u1 u2
  | Construct (c1,u1), Construct (c2,u2) ->
    Construct.UserOrd.equal c1 c2 && eq_universes e1 e2 u1 u2
  | Case (ci1, u1, pms1, ((nas1, p1), _), _, s1, br1),
    Case (ci2, u2, pms2, ((nas2, p2), _), _, s2, br2)
    when Option.has_some (Sys.getenv_opt "ROCQ_EXPERIMENTAL_DEEP_FAST_TEST") ->
    Ind.UserOrd.equal ci1.ci_ind ci2.ci_ind
    && eq_universes e1 e2 u1 u2
    && Array.equal_norefl (fun c1 c2 -> compare_under ~symbolic ~memo budget e1 c1 e2 c2) pms1 pms2
    && Int.equal (Array.length nas1) (Array.length nas2)
    && compare_under ~symbolic ~memo budget (usubs_liftn (Array.length nas1) e1) p1
         (usubs_liftn (Array.length nas2) e2) p2
    && compare_under ~symbolic ~memo budget e1 s1 e2 s2
    && Array.equal_norefl (fun (nas1, b1) (nas2, b2) ->
         Int.equal (Array.length nas1) (Array.length nas2)
         && compare_under ~symbolic ~memo budget (usubs_liftn (Array.length nas1) e1) b1
              (usubs_liftn (Array.length nas2) e2) b2) br1 br2
  | Fix ((ln1, i1), (_, tl1, bl1)), Fix ((ln2, i2), (_, tl2, bl2))
    when Option.has_some (Sys.getenv_opt "ROCQ_EXPERIMENTAL_DEEP_FAST_TEST") ->
    Int.equal i1 i2 && Array.equal Int.equal ln1 ln2
    && Array.equal_norefl (fun c1 c2 -> compare_under ~symbolic ~memo budget e1 c1 e2 c2) tl1 tl2
    && (let n = Array.length tl1 in
        Array.equal_norefl (fun c1 c2 ->
          compare_under ~symbolic ~memo budget (usubs_liftn n e1) c1 (usubs_liftn n e2) c2) bl1 bl2)
  | CoFix (i1, (_, tl1, bl1)), CoFix (i2, (_, tl2, bl2))
    when Option.has_some (Sys.getenv_opt "ROCQ_EXPERIMENTAL_DEEP_FAST_TEST") ->
    Int.equal i1 i2
    && Array.equal_norefl (fun c1 c2 -> compare_under ~symbolic ~memo budget e1 c1 e2 c2) tl1 tl2
    && (let n = Array.length tl1 in
        Array.equal_norefl (fun c1 c2 ->
          compare_under ~symbolic ~memo budget (usubs_liftn n e1) c1 (usubs_liftn n e2) c2) bl1 bl2)
  | Array(_,t1,def1,ty1), Array(_,t2,def2,ty2) ->
    Array.equal_norefl (fun c1 c2 -> compare_under ~symbolic ~memo budget e1 c1 e2 c2) t1 t2
    && compare_under ~symbolic ~memo budget e1 def1 e2 def2
    && compare_under ~symbolic ~memo budget e1 ty1 e2 ty2
  | (Rel _ | Meta _ | Var _ | Sort _ | Prod _ | Lambda _ | LetIn _ | App _
    | Proj _ | Evar _ | Const _ | Ind _ | Construct _ | Case _ | Fix _
    | CoFix _ | Int _ | Float _ | String _ | Array _), _ -> false in
  if equal then remember_syntax memo key;
  equal
  end

and fast_test_under ?(symbolic=false) ?(memo=lazy (SyntaxPairs.create 17)) budget lft1 term1 lft2 term2 =
  if !budget <= 0 then false else begin
  decr budget;
  (* The same closure under the same relocation denotes the same term, even
     when it is a large shared constructor/application graph. Do this before
     recursive inspection: revisiting its children can exhaust the syntactic
     budget and unnecessarily send reflexive comparisons through reduction.
     Identity alone is insufficient for open terms under different lifts. *)
  if term1 == term2 && eq_lift lft1 lft2 then true else
  let key = match fterm_of term1 with
    | FCLOS _ | FApp _ | FLambda _ | FProj _ | FFix _ | FCoFix _ | FLIFT _ ->
      Some (ClosurePair (term1, lft1, term2, lft2))
    | FConstruct (_, args) when not (Array.is_empty args) ->
      Some (ClosurePair (term1, lft1, term2, lft2))
    | _ -> None in
  if syntax_cached memo key then true else
  let equal =
  (* Cache identity belongs to the original expression, before its shared
     reduction cell is expanded. Do not exhaust the lookup budget traversing
     a large reduced value before considering that original expression. *)
  let same_original =
    if not symbolic then false else
    let original term = Option.default term (CClosure.symbolic_view term) in
    let original1 = original term1 and original2 = original term2 in
    (original1 != term1 || original2 != term2) &&
    fast_test_under ~symbolic ~memo budget lft1 original1 lft2 original2
  in
  if same_original then true else
  match fterm_of term1, fterm_of term2 with
  | FLIFT (i, term1), _ -> fast_test_under ~symbolic ~memo budget (el_shft i lft1) term1 lft2 term2
  | _, FLIFT (j, term2) -> fast_test_under ~symbolic ~memo budget lft1 term1 (el_shft j lft2) term2
  | FCLOS (c1, (e1,u1)), FCLOS (c2, (e2,u2)) ->
    eq_lift lft1 lft2 &&
    compare_under ~symbolic ~memo budget (e1, u1) c1 (e2, u2) c2
  | FFix (fix1, e1), FFix (fix2, e2) ->
    eq_lift lft1 lft2 &&
    compare_under ~symbolic ~memo budget e1 (mkFix fix1) e2 (mkFix fix2)
  | FCoFix (fix1, e1), FCoFix (fix2, e2) ->
    eq_lift lft1 lft2 &&
    compare_under ~symbolic ~memo budget e1 (mkCoFix fix1) e2 (mkCoFix fix2)
  | FRel n1, FRel n2 ->
    Int.equal (reloc_rel n1 lft1) (reloc_rel n2 lft2)
  | FFlex (ConstKey (c1, u1)), FFlex (ConstKey (c2, u2)) ->
    Constant.UserOrd.equal c1 c2 && UVars.Instance.equal u1 u2
  | FFlex (VarKey x1), FFlex (VarKey x2) -> Id.equal x1 x2
  | FFlex (RelKey n1), FFlex (RelKey n2) ->
    Int.equal n1 n2 && eq_lift lft1 lft2
  | FAtom a1, FAtom a2 -> Constr.equal a1 a2
  | FInd (ind1, u1), FInd (ind2, u2) ->
    Ind.UserOrd.equal ind1 ind2 && UVars.Instance.equal u1 u2
  | FConstruct ((ctor1, u1), a1), FConstruct ((ctor2, u2), a2) ->
    Construct.UserOrd.equal ctor1 ctor2 && UVars.Instance.equal u1 u2 &&
    Array.equal_norefl (fun t1 t2 ->
      fast_test_under ~symbolic ~memo budget lft1 t1 lft2 t2) a1 a2
  | FApp (f1, a1), FApp (f2, a2) ->
    fast_test_under ~symbolic ~memo budget lft1 f1 lft2 f2 &&
    Array.equal_norefl (fun t1 t2 ->
      fast_test_under ~symbolic ~memo budget lft1 t1 lft2 t2) a1 a2
  | FProj (p1, _, c1), FProj (p2, _, c2) ->
    Projection.UserOrd.equal p1 p2 &&
    fast_test_under ~symbolic ~memo budget lft1 c1 lft2 c2
  | FLambda (n1, ds1, b1, e1), FLambda (n2, ds2, b2, e2) ->
    Int.equal n1 n2 && eq_lift lft1 lft2 &&
    (* Bound allocation before reconstructing the lambda syntax, not only
       its later comparison. Long binder lists must leave this probe unknown. *)
    let rec charge = function
      | [] -> true
      | _ :: rest -> if !budget <= 0 then false else (decr budget; charge rest)
    in
    charge ds1 && charge ds2 &&
    let lambda ds body =
      List.fold_right (fun (na, ty) body -> mkLambda (na, ty, body)) ds body
    in compare_under ~symbolic ~memo budget e1 (lambda ds1 b1) e2 (lambda ds2 b2)
  | FInt n1, FInt n2 -> Uint63.equal n1 n2
  | FFloat n1, FFloat n2 -> Float64.equal n1 n2
  | FString s1, FString s2 -> Pstring.equal s1 s2
  | FPeanoNat n1, FPeanoNat n2 ->
    Ind.UserOrd.equal n1.peano_ind n2.peano_ind &&
    CClosure.PeanoNatValue.equal n1.peano_value n2.peano_value
  | FIrrelevant, FIrrelevant -> true
  | _ -> false in
  if equal then remember_syntax memo key;
  equal
  end

let fast_test lft1 term1 lft2 term2 =
  fast_test_under (ref 1024) lft1 term1 lft2 term2

(* A bare field of a constructor wrapper can forward one source argument and
   discard other parameters. Prefer exposing it when that forwarded source is
   already syntactically the same on both sides. Exposing every wrapper instead
   loses useful congruence between different algebraic inheritance paths.
   This read-only test never computes arguments or certifies equality: it only
   selects ordinary delta/projection reduction, which checks the entire result. *)
let same_forwarded_projection_source infos lft1 reference1 stack1 lft2 reference2 stack2 =
  let env = info_env infos.cnv_inf in
  let rec first_projection nargs = function
    | Zapp args :: rest -> first_projection (nargs + Array.length args) rest
    | (Zshift _ | Zupdate _) :: rest -> first_projection nargs rest
    | Zproj (projection, _) :: _ -> Some (nargs, projection)
    | [] | (Zfix _ | ZcaseT _ | Zprimitive _) :: _ -> None in
  let rec source_variable term = match Constr.kind term with
    | Rel index -> Some index
    | Proj (_, _, source) -> source_variable source
    | _ -> None in
  let rec argument lift index = function
    | Zapp args :: rest ->
      if index < Array.length args then Some (el_stack lift rest, args.(index))
      else argument lift (index - Array.length args) rest
    | (Zshift _ | Zupdate _) :: rest -> argument lift index rest
    | [] | (Zproj _ | Zfix _ | ZcaseT _ | Zprimitive _) :: _ -> None in
  if not (Environ.typing_flags env).unfold_dep_heuristic then false else
  match reference1, reference2, first_projection 0 stack1, first_projection 0 stack2 with
  | ConstKey (c1, u1), ConstKey (c2, u2), Some (n1, p1), Some (n2, p2)
      when Constant.UserOrd.equal c1 c2 && UVars.Instance.equal u1 u2 && n1 = n2 &&
           Projection.Repr.CanOrd.equal p1 p2 &&
           RedFlags.red_set (info_flags infos.cnv_inf) (RedFlags.fCONST c1) ->
    begin match (Environ.lookup_constant c1 env).Declarations.const_body with
    | Def body ->
      let binders, body = Term.decompose_lambda body in
      let arity = List.length binders in
      if n1 <> arity then false else
      let head, fields = Constr.decompose_app body in
      begin match Constr.kind head with
      | Construct ((ind, 1), _) when Environ.QInd.equal env ind (Projection.Repr.inductive p1) ->
        let field = Projection.Repr.npars p1 + Projection.Repr.arg p1 in
        if field < 0 || field >= Array.length fields then false else
        begin match source_variable fields.(field) with
        | Some index when index > 0 && index <= arity ->
          begin match argument lft1 (arity - index) stack1, argument lft2 (arity - index) stack2 with
          | Some (lift1, arg1), Some (lift2, arg2) -> fast_test lift1 arg1 lift2 arg2
          | _ -> false end
        | _ -> false end
      | _ -> false end
    | Undef _ | OpaqueDef _ | Primitive _ | Symbol _ -> false end
  | _ -> false

(* Read-only, bounded argument reflexivity for an unfolding preference. After
   delta exposes a common eliminator, identical arguments must not force its
   recursive computation merely because its major premise is a constructor.
   Account for shifts from the tail, as [pure_stack] does, but neither quote
   closures nor concatenate application arrays. Unsupported frames or an
   exhausted shared budget are inconclusive. Ordinary conversion still checks
   the head, universes and complete stacks. *)
let syntactically_same_arguments lft1 stack1 lft2 stack2 =
  let budget = ref 1024 in
  (* A constructor argument may already have been exposed on only one side.
     Compare that view with suspended constructor syntax without reducing
     either operand. In particular, do not use [mk_clos] on substituted Rel:
     that can eagerly lift an arbitrarily large constructor graph. *)
  let rec same_term lift1 term1 lift2 term2 =
    if !budget <= 0 then false else begin
    decr budget;
    if term1 == term2 && eq_lift lift1 lift2 then true else
    match fterm_of term1, fterm_of term2 with
    | FLIFT (shift, term1), _ -> same_term (el_shft shift lift1) term1 lift2 term2
    | _, FLIFT (shift, term2) -> same_term lift1 term1 (el_shft shift lift2) term2
    | FConstruct ((c1, u1), args1), FConstruct ((c2, u2), args2) ->
      Construct.UserOrd.equal c1 c2 && UVars.Instance.equal u1 u2 &&
      same_array lift1 args1 lift2 args2
    | FApp (head1, args1), FApp (head2, args2) ->
      same_term lift1 head1 lift2 head2 && same_array lift1 args1 lift2 args2
    | FCLOS (body, subst), FConstruct (constructor, args) ->
      constructor_syntax lift1 subst body lift2 constructor args
    | FConstruct (constructor, args), FCLOS (body, subst) ->
      constructor_syntax lift2 subst body lift1 constructor args
    | _ -> fast_test_under budget lift1 term1 lift2 term2
    end
  and same_array lift1 args1 lift2 args2 =
    Array.length args1 = Array.length args2 && Array.length args1 <= !budget &&
    (let rec loop index = index = Array.length args1 ||
       (same_term lift1 args1.(index) lift2 args2.(index) && loop (index + 1))
     in loop 0)
  and raw_term lift1 subst body lift2 term2 =
    if !budget <= 0 then false else begin
      decr budget;
      match Constr.kind body with
      | Rel index -> begin match expand_rel index (fst subst) with
        | Inl (shift, _) ->
          (match inspect_substituted_rel subst index with
           | Some term -> same_term (el_shft shift lift1) term lift2 term2
           | None -> false)
        | Inr _ -> same_term lift1 (mk_clos subst body) lift2 term2
        end
      | _ -> same_term lift1 (mk_clos subst body) lift2 term2
    end
  and constructor_syntax lift1 subst body lift2 (constructor2, u2) args2 =
    if !budget <= 0 then false else begin
      decr budget;
      let head, args1 = Constr.decompose_app body in
      match Constr.kind head with
      | Construct (constructor1, u1) ->
        Construct.UserOrd.equal constructor1 constructor2 &&
        UVars.Instance.equal (CClosure.usubst_instance subst u1) u2 &&
        Array.length args1 = Array.length args2 &&
        Array.length args1 <= !budget &&
        (let rec loop index =
           index = Array.length args1 ||
           (raw_term lift1 subst args1.(index) lift2 args2.(index) && loop (index + 1))
         in loop 0)
      | _ -> false
    end
  in
  let rec collect reversed = function
    | [] -> Some reversed
    | frame :: rest ->
      let cost = match frame with Zapp args -> 1 + Array.length args | _ -> 1 in
      if cost > !budget then None else begin
        budget := !budget - cost;
        match frame with
        | Zapp _ | Zshift _ | Zupdate _ -> collect (frame :: reversed) rest
        | Zproj _ | Zfix _ | ZcaseT _ | Zprimitive _ -> None
      end
  in
  let arguments lift reversed =
    snd (List.fold_left (fun (lift, args) -> function
      | Zshift n -> el_shft n lift, args
      | Zapp terms ->
        lift, Array.fold_right (fun term args -> (lift, term) :: args) terms args
      | Zupdate _ -> lift, args
      | Zproj _ | Zfix _ | ZcaseT _ | Zprimitive _ -> assert false)
      (lift, []) reversed)
  in
  let rec compare left right = match left, right with
    | [], [] -> true
    | (lift1, term1) :: left, (lift2, term2) :: right ->
      same_term lift1 term1 lift2 term2 && compare left right
    | _ -> false
  in
  match collect [] stack1, collect [] stack2 with
  | Some left, Some right -> compare (arguments lft1 left) (arguments lft2 right)
  | _ -> false

let assert_reduced_constructor s =
  if not @@ CList.is_empty s then
    CErrors.anomaly Pp.(str "conversion was given unreduced term (FConstruct).")

let is_eta_record env (ind, u) =
  Declareops.is_record_with_eta (Inductive.lookup_mind_specif env ind) u

let rec application_args arrays = function
  | Zapp args :: stack -> application_args (args :: arrays) stack
  | (Zshift _ | Zupdate _) :: stack -> application_args arrays stack
  | [] -> Some (Array.concat (List.rev arrays))
  | (ZcaseT _ | Zproj _ | Zfix _ | Zprimitive _) :: _ -> None

(* Instantiate a checked case's return predicate, without evaluating its
   scrutinee or quoting its branches. Indices are actual inhabitants from the
   scrutinee's type (or the kernel-checked inversion annotation), never dummy
   variables. Let-bound parameters/indices use the inductive's own context. *)
let case_predicate_type infos ci u params ((names, body), _) indices subject subst =
  let env = info_env infos in
  let mib, mip = Inductive.lookup_mind_specif env ci.ci_ind in
  if ci.ci_npar <> mib.mind_nparams ||
     Array.length params <> mib.mind_nparams ||
     Array.length indices <> mip.mind_nrealargs ||
     Array.length names <> mip.mind_nrealdecls + 1 ||
     List.length mib.mind_params_ctxt + mip.mind_nrealdecls > 4096
  then None
  else
    let instantiate ctx args type_subst result_subst =
      let _, _, result = List.fold_left
          (fun (index, type_subst, result_subst) decl ->
            let index, value = match decl with
              | Context.Rel.Declaration.LocalAssum _ -> index + 1, args.(index)
              | Context.Rel.Declaration.LocalDef (_, value, _) ->
                index, mk_clos type_subst value in
            index, usubs_cons value type_subst, usubs_cons value result_subst)
          (0, type_subst, result_subst) (List.rev ctx) in
      result in
    let u = usubst_instance subst u in
    let params = Array.map (mk_clos subst) params in
    let initial = subs_id 0, u in
    let param_subst = instantiate mib.mind_params_ctxt params initial initial in
    let index_context, _ = List.chop mip.mind_nrealdecls mip.mind_arity_ctxt in
    let result_subst = instantiate index_context indices param_subst subst in
    Some (mk_clos (usubs_cons subject result_subst) body)

let inductive_after_eliminating ?(expand_aliases = false)
    ?subject
    ?(classify = direct_inductive)
    ?alias_infos
    reduction_infos tab typ stack =
  let env = info_env reduction_infos in
  let alias_infos = Option.default reduction_infos alias_infos in
  (* Type-head reduction can deliberately disable delta. Explicit alias
     inspection retains the caller's transparency, with a separate table so
     negative entries from a different reduction policy cannot leak across. *)
  let alias_tab = lazy (create_tab ()) in
  let rec apply_args typ args index =
    if Int.equal index (Array.length args) then Some typ
    else
      let typ, stack = whd_stack reduction_infos tab typ empty_stack in
      match fterm_of (zip typ stack) with
      | FProd (_, _, body, subst) ->
        let subst = usubs_cons args.(index) subst in
        apply_args (mk_clos subst body) args (index + 1)
      | _ -> None
  in
  let rec final fuel typ =
    let typ, stack = whd_stack reduction_infos tab typ empty_stack in
    match classify (zip typ stack) with
    | Some _ as inductive -> inductive
    | None when expand_aliases && fuel > 0 ->
      begin match fterm_of typ, stack with
      | FFlex (ConstKey (constant, _) as flex), [] ->
            let oracle = CClosure.oracle_of_infos alias_infos in
            begin match
              Conv_oracle.get_strategy oracle
                (Conv_oracle.EvalConstRef constant)
            with
            | Conv_oracle.Expand ->
              begin match
                unfold_ref_with_args alias_infos (Lazy.force alias_tab) flex stack
              with
              | Some (typ, stack) -> final (fuel - 1) (zip typ stack)
              | None -> None
              end
            | Conv_oracle.Level _ | Conv_oracle.Opaque -> None
            end
      | _ -> None
      end
    | None -> None
  in
  let rec projection_type fuel typ stack =
    match fterm_of typ with
    | FFlex (ConstKey (constant, _) as flex) when expand_aliases && fuel > 0 ->
      let oracle = CClosure.oracle_of_infos alias_infos in
      begin match Conv_oracle.get_strategy oracle (Conv_oracle.EvalConstRef constant) with
      | Conv_oracle.Opaque -> typ, stack
      | Conv_oracle.Expand | Conv_oracle.Level _ ->
        begin match unfold_ref_with_args alias_infos (Lazy.force alias_tab) flex stack with
        | None -> typ, stack
        | Some (body, stack) ->
          (* Follow aliases without evaluating matches or fixpoints. *)
          let alias_infos = infos_with_reds reduction_infos RedFlags.betazeta in
          let typ, stack = whd_stack alias_infos tab body stack in
          projection_type (fuel - 1) typ stack
        end
      end
    | _ -> typ, stack
  in
  let rec eliminate typ subject = function
    | [] ->
      final 32 typ
    | Zupdate _ :: stack -> eliminate typ subject stack
    | Zshift _ :: stack ->
      (* A supplied subject must already be in the common context. *)
      if Option.has_some subject then None else eliminate typ None stack
    | Zapp args :: stack ->
      Option.bind (apply_args typ args 0) (fun typ ->
        let subject = Option.map (fun term -> zip term [Zapp args]) subject in
        eliminate typ subject stack)
    | Zproj (repr, relevance) :: stack ->
      let typ, typ_stack =
        whd_stack reduction_infos tab typ empty_stack
      in
      let typ, typ_stack = projection_type 32 typ typ_stack in
      begin match fterm_of typ, application_args [] typ_stack with
      | FInd ((current, u)), Some args
        when Environ.QInd.equal env current (Projection.Repr.inductive repr) ->
        begin match
          try Some (Environ.lookup_projection (Projection.make repr true) env)
          with Not_found -> None
        with
        | Some (_, projection_type)
          when Option.has_some subject || Vars.noccurn 1 projection_type ->
          (* Parameters are conversion closures, not necessarily quotable
             terms: a proof argument may already be [FIrrelevant]. Substitute
             lazily, so unused parameters are neither reified nor forced. *)
          let subst =
            Array.fold_left (fun subst arg -> usubs_cons arg subst)
              (subs_id 0, u) args
          in
          let record = match subject with
            | Some record -> record
            | None -> inject (mkRel 1) in
          let subst = usubs_cons record subst in
          let subject = Option.map
              (fun term -> zip term [Zproj (repr, relevance)]) subject in
          eliminate (mk_clos subst projection_type) subject stack
        | Some _ | None -> None
        end
      | _ -> None
      end
    | ZcaseT (ci, u, params, predicate, _, subst) as frame :: stack ->
      Option.bind subject (fun subject ->
        let typ, typ_stack = whd_stack reduction_infos tab typ empty_stack in
        match fterm_of typ, application_args [] typ_stack with
        | FInd (ind, _), Some args when Environ.QInd.equal env ind ci.ci_ind ->
          let mib, mip = Inductive.lookup_mind_specif env ci.ci_ind in
          if Array.length args <> mib.mind_nparams + mip.mind_nrealargs then None
          else
            let indices = Array.sub args mib.mind_nparams mip.mind_nrealargs in
            Option.bind
              (case_predicate_type reduction_infos ci u params predicate indices subject subst)
              (fun typ -> eliminate typ (Some (zip subject [frame])) stack)
        | _ -> None)
    | (Zfix _ | Zprimitive _) :: _ -> None
  in
  eliminate typ subject stack

(* Bound expanded syntax before the uncommon type-witness interface needs
   quotation and relocation. General unit/eta classification does not quote. *)
let small_reification remaining root =
  let exception Too_large in
  let visit () =
    if !remaining <= 0 then raise Too_large;
    decr remaining
  in
  let binder depth = visit (); depth + 1 in
  let rec syntax subst depth term =
    visit ();
    match Constr.kind term with
    | Rel index when index > depth ->
      (match subst with
      | None -> ()
      | Some subst ->
        match expand_rel (index - depth) (fst subst) with
        | Inr _ -> ()
        | Inl _ ->
          match inspect_substituted_rel subst (index - depth) with
          | Some term -> closure term
          | None -> raise Too_large)
    | _ -> Constr.iter_with_binders binder (syntax subst) depth term
  and context subst (names, body) =
    let depth = Array.fold_left (fun depth _ -> binder depth) 0 names in
    syntax (Some subst) depth body
  and closure term =
    visit ();
    match fterm_of term with
    | FRel _ | FFlex _ | FInd _ | FInt _ | FFloat _ | FString _ -> ()
    | FAtom term -> syntax None 0 term
    | FLIFT (_, term) | FProj (_, _, term) -> closure term
    | FConstruct (_, args) -> Array.iter closure args
    | FApp (head, args) -> closure head; Array.iter closure args
    | FCLOS (term, subst) -> syntax (Some subst) 0 term
    | FFix (fix, subst) -> syntax (Some subst) 0 (mkFix fix)
    | FCoFix (fix, subst) -> syntax (Some subst) 0 (mkCoFix fix)
    | FLambda (len, domains, body, subst) ->
      let depth = List.fold_left (fun depth (_, domain) ->
        syntax (Some subst) depth domain; binder depth) 0 domains in
      if not (Int.equal depth len) then raise Too_large;
      syntax (Some subst) depth body
    | FProd (_, domain, body, subst) ->
      closure domain; syntax (Some subst) (binder 0) body
    | FLetIn (_, value, typ, body, subst) ->
      closure value; closure typ; syntax (Some subst) (binder 0) body
    | FCaseT (_, _, params, (predicate, _), discr, branches, subst) ->
      Array.iter (syntax (Some subst) 0) params;
      context subst predicate;
      closure discr;
      Array.iter (context subst) branches
    | FCaseInvert (_, _, params, (predicate, _), indices, discr, branches, subst) ->
      Array.iter (syntax (Some subst) 0) params;
      context subst predicate;
      Array.iter closure (get_invert indices);
      closure discr;
      Array.iter (context subst) branches
    | FArray (_, values, typ) ->
      closure typ;
      closure (Parray.default values);
      for i = 0 to Parray.length_int values - 1 do
        closure (Parray.get values (Uint63.of_int i))
      done
    | FPeanoNat n ->
      (match peano_quotation_cost ~limit:!remaining n with
       | None -> raise Too_large
       | Some cost -> remaining := !remaining - cost)
    | FEvar _ | FIrrelevant | FLOCKED -> raise Too_large
  in
  try closure root; true with Too_large -> false

(* Application prefixes contain executable definitions, unlike the small
   type-witness interface. Permit a larger but still finite expanded quotation;
   one allowance is shared by all four operands of a congruence attempt. *)
let application_quotation_budget = 65_536

(* Unit/eta inspection borrows immutable syntax and deferred environments.
   Only demanded closure cells get private copies. Caller-owned update frames
   are excluded; private-cell visits and head steps share the query allowance. *)
let with_type_snapshot_subject infos typ stack subject inspect =
  let limit = 4096 in
  let rec collect size arrays = function
    | [] -> Some (List.concat (List.rev arrays))
    | _ when size >= limit -> None
    | Zapp args :: rest ->
      let size = size + Array.length args + 1 in
      if size > limit then None
      else collect size (Array.to_list args :: arrays) rest
    | (Zshift _ | Zupdate _ | Zproj _) :: rest -> collect (size + 1) arrays rest
    | ZcaseT _ as frame :: rest ->
      (* Store the suspended frame as a root of the private view. Its captured
         environment stays lazy. The placeholder is not used for typing. *)
      collect (size + 1) ([zip (inject (mkRel 1)) [frame]] :: arrays) rest
    | (Zfix _ | Zprimitive _) :: _ -> None
  in
  Option.bind (collect (if Option.has_some subject then 2 else 1) [] stack) (fun arguments ->
    let roots = typ :: (match subject with
      | None -> arguments | Some term -> term :: arguments) in
    with_private_closure_query ~steps:limit infos.cnv_inf roots
      (fun cnv_inf copies ->
        let typ, copies = match copies with
          | typ :: copies -> typ, copies
          | [] -> assert false in
        let subject, copies = match subject, copies with
          | None, _ -> None, copies
          | Some _, term :: copies -> Some term, copies
          | Some _, [] -> assert false in
        let rec rebuild copies = function
          | [] -> assert (List.is_empty copies); []
          | Zupdate _ :: rest -> rebuild copies rest
          | Zapp args :: rest ->
            let args, copies = List.chop (Array.length args) copies in
            Zapp (Array.of_list args) :: rebuild copies rest
          | (Zshift _ | Zproj _) as frame :: rest -> frame :: rebuild copies rest
          | ZcaseT _ :: rest ->
            (match copies with
             | case :: copies ->
               (match fterm_of case with
                | FCaseT (ci, u, params, predicate, _, branches, subst) ->
                  ZcaseT (ci, u, params, predicate, branches, subst) :: rebuild copies rest
                | _ -> assert false)
             | [] -> assert false)
          | (Zfix _ | Zprimitive _) :: _ -> assert false
        in
        inspect { infos with cnv_inf } typ (rebuild copies stack) subject))

let with_type_snapshot infos typ stack inspect =
  with_type_snapshot_subject infos typ stack None
    (fun infos typ stack _ -> inspect infos typ stack)

let transparent_inductive_after_applying infos typ stack =
  try with_type_snapshot infos typ stack (fun infos typ stack ->
    let all = RedFlags.(red_add_transparent all
      (red_transparent (info_flags infos.cnv_inf))) in
    let type_infos = infos_with_reds infos.cnv_inf all in
    inductive_after_eliminating type_infos (create_tab ()) typ stack)
  with Not_found -> None

(** Unit eta can also apply after projecting a field. Reject cases and other
    eliminations before inspecting a possibly large local type. *)
let rec unit_like_stack = function
  | [] -> true
  | (Zapp _ | Zproj _ | Zshift _ | Zupdate _) :: stack -> unit_like_stack stack
  | (ZcaseT _ | Zfix _ | Zprimitive _) :: _ -> false

(* Singleton classification, like its final type witness, needs the WHNF of
   the type. Beta/iota/zeta alone can stop at a transparent definition in the
   discriminant of a type-level match (e.g. [family (bool_alias true)]).
   Use the ordinary reducer with the caller's and oracle's transparency;
   the enclosing private query still owns and bounds all reduction work. *)
let unit_type_reduction_infos infos =
  let allowed = RedFlags.red_transparent (info_flags infos.cnv_inf) in
  let oracle = Conv_oracle.get_transp_state (oracle_of_infos infos.cnv_inf) in
  let transparency = TransparentState.{
    tr_var = Id.Pred.inter allowed.tr_var oracle.tr_var;
    tr_cst = Cpred.inter allowed.tr_cst oracle.tr_cst;
    tr_prj = PRpred.inter allowed.tr_prj oracle.tr_prj;
  } in
  let reds = RedFlags.red_add_transparent RedFlags.all transparency in
  infos_with_reds infos.cnv_inf reds

(* Primitive-record eta also makes a record unit-like at an instantiation
   where every field is irrelevant or unit-like. For example, ULift (PLift P)
   has this property, but ULift nat does not. Inspect only field types, never
   record values, with a bounded traversal and an isolated reduction table. *)
let unit_like_type infos typ =
  let env = info_env infos.cnv_inf in
  let tab = create_tab () in
  let type_infos = unit_type_reduction_infos infos in
  let remaining = ref 32 in
  let rec head typ stack =
    if !remaining = 0 then None
    else begin
      decr remaining;
      let typ, stack = whd_stack type_infos tab typ stack in
      (* Type-head reduction may use shared argument closures. Do not write the extra
         alias/projection reductions below back into their update nodes. *)
      let stack = List.filter (function Zupdate _ -> false | _ -> true) stack in
      if not (unit_like_stack stack) then None
      else match fterm_of typ with
      | FFlex (ConstKey (constant, _) as flex) ->
        let oracle = CClosure.oracle_of_infos infos.cnv_inf in
        begin match Conv_oracle.get_strategy oracle (Conv_oracle.EvalConstRef constant) with
        | Conv_oracle.Opaque -> None
        | Conv_oracle.Expand | Conv_oracle.Level _ ->
          if not (RedFlags.red_set (info_flags infos.cnv_inf) (RedFlags.fCONST constant))
          then None
          else Option.bind (unfold_ref_with_args infos.cnv_inf tab flex stack)
            (fun (body, stack) -> head body stack)
        end
      | FProj (projection, relevance, record) ->
        Option.bind (unfold_projection infos.cnv_inf projection relevance)
          (fun projection -> head record (projection :: stack))
      | FConstruct (((ind, _), _), args) ->
        let rec project shift = function
          | Zshift n :: stack -> project (shift + n) stack
          | Zproj (projection, _) :: stack
            when Environ.QInd.equal env ind (Projection.Repr.inductive projection) ->
            let index = Projection.Repr.npars projection + Projection.Repr.arg projection in
            if index >= Array.length args then None
            else
              let arg = if shift = 0 then args.(index)
                else zip args.(index) [Zshift shift] in
              head arg stack
          | _ -> None
        in
        project 0 stack
      | _ -> Some (typ, stack)
    end
  in
  let rec inspect typ =
    match direct_registered_unit_like infos typ with
    | Some _ as result -> result
    | None when !remaining = 0 -> None
    | None ->
      Option.bind (head typ empty_stack) (fun (typ, stack) ->
      match fterm_of typ, application_args [] stack with
      | FInd ((ind, u) as pind), Some args ->
        if is_registered_unit_like env ind then Some ind
        else
        let mib, mip as spec = Inductive.lookup_mind_specif env ind in
        if not (Declareops.is_record_with_eta spec u) ||
           Array.length args <> mib.Declarations.mind_nparams
        then None
        else
          let rec fields index =
            if index = mip.Declarations.mind_consnrealargs.(0) then true
            else
              let repr, relevance =
                Declareops.inductive_make_projection ind mib ~proj_arg:index
              in
              let relevance = UVars.subst_instance_relevance u relevance in
              if is_irrelevant infos.cnv_inf relevance then fields (index + 1)
              else
                let _, field_type =
                  Environ.lookup_projection (Projection.make repr true) env
                in
                (* Do not substitute a dummy record into a dependent field. *)
                Vars.noccurn 1 field_type &&
                let subst = Array.fold_left
                    (fun subst arg -> usubs_cons arg subst) (subs_id 0, snd pind) args in
                let subst = usubs_cons (inject (mkRel 1)) subst in
                Option.has_some (inspect (mk_clos subst field_type)) &&
                fields (index + 1)
          in
          if fields 0 then Some ind else None
      | _ -> None)
  in
  inspect typ

let shallow_unit_like_after_applying infos typ stack =
  with_type_snapshot infos typ stack (fun infos typ stack ->
    if not (unit_like_stack stack) then None
    else
      let type_infos =
        infos_with_reds infos.cnv_inf RedFlags.betaiotazeta
      in
      let tab = create_tab () in
      (* The type-only projection traversal substitutes a dummy scrutinee.
         Only use it for fields whose type does not depend on that scrutinee. *)
      inductive_after_eliminating ~expand_aliases:true
        ~classify:(unit_like_type infos)
        ~alias_infos:infos.cnv_inf
        type_infos tab typ stack)

let unit_like_of_rel infos _tab lft stack n =
  if not (unit_like_stack stack) then None
  else
    let n = reloc_rel n (el_stack lft stack) in
    Option.bind (rel_type infos n) (fun typ ->
      shallow_unit_like_after_applying infos typ stack)

let rel_has_unit_like infos tab lft (hd, stack) ind =
  match fterm_of hd with
  | FRel n -> begin match unit_like_of_rel infos tab lft stack n with
    | Some rel_ind -> Ind.UserOrd.equal ind rel_ind
    | None -> false
    end
  | _ -> false

let unit_like_of_flex infos _tab lft stack fl =
  if not (unit_like_stack stack) then None
  else
    let env = info_env infos.cnv_inf in
    let typ = match fl with
    | RelKey n ->
      let n = reloc_rel n (el_stack lft stack) in
      rel_type infos n
    | VarKey id ->
      Some (inject (Context.Named.Declaration.get_type (Environ.lookup_named id env)))
    | ConstKey (c, u) ->
      Some (mk_clos (subs_id 0, u) (Environ.lookup_constant c env).Declarations.const_type)
    in
    Option.bind typ (fun typ ->
      shallow_unit_like_after_applying infos typ stack)

let flex_has_unit_like infos tab lft stack fl ind =
  match unit_like_of_flex infos tab lft stack fl with
  | Some flex_ind -> Ind.UserOrd.equal ind flex_ind
  | None -> false

let same_unit_like_flexes infos lft1 v1 fl1 lft2 v2 fl2 =
  match unit_like_of_flex infos infos.lft_tab lft1 v1 fl1 with
  | None -> false
  | Some ind1 ->
    match unit_like_of_flex infos infos.rgt_tab lft2 v2 fl2 with
    | Some ind2 -> Ind.UserOrd.equal ind1 ind2
    | None -> false

let same_unit_like_flex_rel infos flex_tab flex_lift flex_stack flex
    rel_tab rel_lift rel_stack rel =
  match unit_like_of_flex infos flex_tab flex_lift flex_stack flex,
        unit_like_of_rel infos rel_tab rel_lift rel_stack rel with
  | Some flex_ind, Some rel_ind -> Ind.UserOrd.equal flex_ind rel_ind
  | _ -> false

(* Uniform weakening can stay suspended when quotation is unavailable. For a
   syntax closure, shift its substitution rather than wrapping the type head in
   FLIFT: type-head inspection needs to see its application spine. An inversion
   subject is opaque data here, so the ordinary O(1) FLIFT wrapper is sufficient.
   Neither operation evaluates a proof or walks the expanded term. Other shapes
   and non-uniform relocations remain inconclusive; in particular this is not a
   general-purpose, unbounded constructor lift. The caller still snapshots and
   bounds every subsequent type inspection. *)
let delayed_unit_type_shift lift term =
  match lift, fterm_of term with
  | ELSHFT (ELID, n), FCLOS (body, (subst, u)) ->
    Some (mk_clos (subs_shft (n, subst), u) body)
  | ELSHFT (ELID, n), FCaseInvert _ ->
    Some (zip term [Zshift n])
  | _ -> None

(* A unit certificate identifies a family, not an instantiated type. Normalize
   the small type/argument interface into the common conversion context before
   accepting equality of neutral inhabitants. Large interfaces are never quoted
   without an occurrence bound; a uniform shift of delayed data can stay lazy.
   Head reduction of the resulting type remains a bounded, isolated query. *)
let relocate_unit_type infos remaining lift term =
  if is_lift_id lift then Some term
  else if small_reification remaining term then
    Some (mk_clos (subs_id (Range.length infos.cnv_rel_types), UVars.Instance.empty)
      (Vars.exliftn lift (term_of_fconstr term)))
  else delayed_unit_type_shift lift term

let unit_type_after_stack infos lift type_lift typ stack subject =
  let remaining = ref 4096 in
  (* An identity relocation needs no syntax. In particular, already-erased
     proof arguments remain valid closure data but cannot be quoted. Keep the
     single shared quotation allowance separate from the stack/interface bound:
     exhausting quotation must not veto an O(1) delayed shift or an unchanged
     argument. Snapshot copying and head reduction retain their own shared cap. *)
  let quote = relocate_unit_type infos (ref 4096) in
  let rec arguments lift = function
    | [] -> Some (lift, [])
    | _ when !remaining <= 0 -> None
    | frame :: rest ->
      decr remaining;
      Option.bind (arguments lift rest) (fun (lift, rest) ->
        match frame with
        | Zshift n -> Some (el_shft n lift, rest)
        | Zupdate _ -> Some (lift, rest)
        | Zapp args ->
          if Array.length args > !remaining then None else
          let () = remaining := !remaining - Array.length args in
          let rec copy index copied =
            if index = Array.length args then Some (Array.of_list (List.rev copied))
            else Option.bind (quote lift args.(index))
              (fun arg -> copy (index + 1) (arg :: copied)) in
          Option.map (fun args -> lift, Zapp args :: rest) (copy 0 [])
        | Zproj _ -> Some (lift, frame :: rest)
        | ZcaseT _ when is_lift_id lift -> Some (lift, frame :: rest)
        | ZcaseT _ | Zfix _ | Zprimitive _ -> None)
  in
  Option.bind (quote type_lift typ) (fun typ ->
    Option.bind (arguments lift stack) (fun (_, stack) ->
      with_type_snapshot_subject infos typ stack (Some subject) (fun infos typ stack subject ->
        let result = ref None in
        let _ = inductive_after_eliminating ?subject
          ~classify:(fun typ -> result := Some typ; None)
          (unit_type_reduction_infos infos) (create_tab ()) typ stack in
        !result)))

let neutral_type_witness infos lift stack flex =
  let local_subst = subs_id (Range.length infos.cnv_rel_types), UVars.Instance.empty in
  let env = info_env infos.cnv_inf in
  let typ = match flex with
    | RelKey n -> rel_type_lifted infos (reloc_rel n (el_stack lift stack))
    | VarKey id -> Some (el_id, inject
        (Context.Named.Declaration.get_type (Environ.lookup_named id env)))
    | ConstKey (c, u) -> Some (el_id, mk_clos (subs_id 0, u)
        (Environ.lookup_constant c env).const_type)
  in
  let subject = match flex with
    | RelKey n -> mkRel (reloc_rel n (el_stack lift stack))
    | VarKey id -> mkVar id
    | ConstKey constant -> mkConstU constant in
  let subject = mk_clos local_subst subject in
  Option.bind typ (fun (type_lift, typ) ->
    unit_type_after_stack infos lift type_lift typ stack subject)

let unit_operand_type infos lift (head, stack) =
  let type_of_head infos head stack = match fterm_of head with
  | FFlex flex -> neutral_type_witness infos lift stack flex
  | FRel n -> neutral_type_witness infos lift stack (RelKey n)
  | FConstruct (((ind, constructor), u), args)
    when is_registered_unit_like (info_env infos.cnv_inf) ind ->
    let mib = Environ.lookup_mind (fst ind) (info_env infos.cnv_inf) in
    let nparams = mib.mind_nparams in
    let nfields = mib.mind_packets.(snd ind).mind_consnrealargs.(0) in
    (* A partial constructor is still a function, even if every remaining
       field is irrelevant. It cannot witness an inhabitant of the result. *)
    if constructor <> 1 || Array.length args <> nparams + nfields ||
       not (is_empty_stack stack) then None
    else
      let typ = zip (inject (mkIndU (ind, u)))
        [Zapp (Array.sub args 0 nparams)] in
      relocate_unit_type infos (ref 4096) (el_stack lift stack) typ
  | FCaseInvert (ci, u, params, predicate, indices, discr, _, subst) ->
    Option.bind (case_predicate_type infos.cnv_inf ci u params predicate
      (get_invert indices) discr subst) (fun typ ->
      Option.bind (relocate_unit_type infos (ref 4096) (el_stack lift stack) head)
        (fun subject ->
          unit_type_after_stack infos lift (el_stack lift stack) typ stack subject))
  | FConstruct _ | FInd _ | FApp _ | FProj _ | FFix _ | FCoFix _ | FCaseT _
  | FLambda _ | FProd _ | FLetIn _ | FEvar _ | FAtom _ | FInt _
  | FFloat _ | FString _ | FArray _ | FPeanoNat _ | FLIFT _ | FCLOS _
  | FIrrelevant | FLOCKED -> None
  in
  match fterm_of head with
  | FProj _ ->
    (* Projection opacity controls computation, not access to its declared
       field type. Expose the neutral source on an isolated, bounded snapshot,
       preserving projections for type reconstruction rather than reducing
       their values. Source closures may still contain delayed substitutions. *)
    with_type_snapshot infos head stack (fun infos head stack ->
      let reds = infos_with_reds infos.cnv_inf RedFlags.betazeta in
      let tab = create_tab () in
      let rec spine fuel head stack =
        if fuel = 0 then None else
        (* A stuck inversion already carries its checked predicate/indices.
           Reading them is not permission to execute the case in a probe. *)
        match fterm_of head with
        | FCaseInvert _ -> type_of_head infos head stack
        | _ ->
        let head, arguments = whd_stack reds tab head empty_stack in
        let stack = arguments @ stack in
        match fterm_of head with
        | FProj (projection, relevance, record) ->
          spine (fuel - 1) record (Zproj (Projection.repr projection, relevance) :: stack)
        | _ -> type_of_head infos head stack
      in
      spine 4096 head stack)
  | _ -> type_of_head infos head stack

let has_type_elimination_stack stack =
  (* Dependent projections and stuck cases need the full witness with an
     actual subject. A family-only classification is not a prerequisite and
     this test grants no equality itself. *)
  let rec inspect remaining = function
    | [] -> false
    | _ when remaining = 0 -> false
    | (Zproj _ | ZcaseT _) :: _ -> true
    | _ :: rest -> inspect (remaining - 1) rest in
  inspect 4096 stack

let witness_after_complete_inspection inspect matches =
  (* [inspect] must establish every mandatory eligibility condition before
     any potentially costly dependency query runs. Preserve occurrence order
     and short-circuit the witness search exactly as before. The caller bounds
     inspection, and thus the temporary candidate list. *)
  let candidates = ref [] in
  inspect (fun candidate -> candidates := candidate :: !candidates);
  List.exists matches (List.rev !candidates)

let matches_registered_compact_peano_operation infos matches =
  let retroknowledge =
    Environ.retroknowledge (CClosure.info_env infos)
  in
  let matches_optional = function
    | Some operation -> matches operation
    | None -> false
  in
  List.exists
    (fun scheme ->
      matches_optional scheme.Retroknowledge.peano_double ||
      matches_optional scheme.peano_add || matches_optional scheme.peano_mul ||
      matches_optional scheme.peano_pow || matches_optional scheme.peano_sub ||
      List.exists matches scheme.peano_div_go ||
      List.exists matches scheme.peano_mod_go ||
      List.exists
        (fun decoder ->
          matches decoder.Retroknowledge.decoder_constant)
        scheme.peano_decoders)
    retroknowledge.Retroknowledge.retro_peano_nat ||
  List.exists
    (fun operation ->
      matches operation.Retroknowledge.bool_op_constant)
    retroknowledge.retro_peano_nat_beq ||
  List.exists
    (fun operation ->
      matches operation.Retroknowledge.bool_op_constant)
    retroknowledge.retro_peano_nat_ble

let is_registered_compact_peano_operation infos constant =
  matches_registered_compact_peano_operation infos
    (Constant.UserOrd.equal constant)

let depends_on_registered_compact_peano_operation ~fuel infos constant =
  let env = CClosure.info_env infos in
  matches_registered_compact_peano_operation infos (fun operation ->
    Constant.UserOrd.equal constant operation ||
    (* An exhausted search is not evidence of compact backing. *)
    Environ.constant_depends_on ~fuel env constant operation = Some true)

let is_compact_peano_wrapper env ind =
  let retroknowledge = Environ.retroknowledge env in
  let is_peano_type typ =
    let head, _ = Constr.decompose_app typ in
    match Constr.kind head with
    | Ind (candidate, _) ->
      List.exists
        (fun scheme ->
          Ind.UserOrd.equal candidate
            scheme.Retroknowledge.peano_inductive)
        retroknowledge.Retroknowledge.retro_peano_nat
    | _ -> false
  in
  try
    let mib, mip = Inductive.lookup_mind_specif env ind in
    Int.equal (Array.length mib.Declarations.mind_packets) 1 &&
    Int.equal mib.mind_nparams 0 &&
    Int.equal (Array.length mip.mind_consnames) 2 &&
    Array.for_all (Int.equal 1) mip.mind_consnrealargs &&
    Array.for_all
      (fun (context, _) ->
        match context with
        | [declaration] ->
          is_peano_type (Context.Rel.Declaration.get_type declaration)
        | _ -> false)
      mip.mind_nf_lc
  with Not_found -> false

let flex_result_inductive infos _tab lft stack fl =
  let env = info_env infos.cnv_inf in
  let typ = match fl with
  | RelKey n ->
    let n = reloc_rel n (el_stack lft stack) in
    rel_type infos n
  | VarKey id ->
    Some (inject
      (Context.Named.Declaration.get_type (Environ.lookup_named id env)))
  | ConstKey (c, u) ->
    Some (mk_clos (subs_id 0, u) (Environ.lookup_constant c env).const_type)
  in
  let flex_ind = Option.bind typ (fun typ ->
    try transparent_inductive_after_applying infos typ stack
    with Not_found | Assert_failure _ -> None)
  in
  flex_ind

let flex_has_inductive infos tab lft stack fl ind =
  match flex_result_inductive infos tab lft stack fl with
  | Some flex_ind -> Ind.UserOrd.equal ind flex_ind
  | None -> false

let diagnostic_conversion_calls = ref 0
(* Temporary one-factor controls for the checkpoint performance regression. *)
let diagnostic_no_direct_arguments =
  Option.has_some (Sys.getenv_opt "ROCQ_DIAGNOSTIC_NO_DIRECT_ARGUMENTS")
let diagnostic_no_dependency_first =
  Option.has_some (Sys.getenv_opt "ROCQ_DIAGNOSTIC_NO_DEPENDENCY_FIRST")
let diagnostic_projection_first =
  Option.has_some (Sys.getenv_opt "ROCQ_DIAGNOSTIC_PROJECTION_FIRST")
let diagnostic_dependency_stats =
  Option.has_some (Sys.getenv_opt "ROCQ_DIAGNOSTIC_DEPENDENCY_STATS")
let diagnostic_indirect_calls = ref 0
let diagnostic_indirect_cpu = ref 0.

let diagnostic_time_indirect f =
  if not diagnostic_dependency_stats then f ()
  else
    let started = Sys.time () in
    Fun.protect f ~finally:(fun () ->
      incr diagnostic_indirect_calls;
      diagnostic_indirect_cpu := !diagnostic_indirect_cpu +. Sys.time () -. started;
      let calls = !diagnostic_indirect_calls in
      if Int.equal (calls land (calls - 1)) 0 then
        Printf.eprintf "[indirect dependency] calls=%d cpu=%.3f\n%!"
          calls !diagnostic_indirect_cpu)

let diagnostic_conversion_trace = ref false
let diagnostic_conversion_trace_steps = ref 0
(* Pair tracking retains closures and is unsafe for memory profiles. Keep it
   separate from the scalar trace, with an explicit opt-in. *)
let diagnostic_conversion_trace_pairs_enabled =
  Option.has_some (Sys.getenv_opt "ROCQ_DIAGNOSTIC_CONVERSION_TRACE_PAIRS")

module DiagnosticConversionPairs = Hashtbl.Make (struct
  type t = fconstr * fconstr
  let equal (left1, right1) (left2, right2) =
    left1 == left2 && right1 == right2
  let hash (left, right) =
    Hashtbl.hash (fconstr_hash left, fconstr_hash right)
end)
let diagnostic_conversion_trace_pairs = DiagnosticConversionPairs.create 251
let diagnostic_conversion_trace_repeats = ref 0
let diagnostic_conversion_trace_memo_hits = ref 0
let diagnostic_conversion_trace_memo_stores = ref 0
let diagnostic_conversion_trace_memo_size = ref 0
let diagnostic_conversion_trace_memo_peak = ref 0
let diagnostic_conversion_trace_memo_clears = ref 0

let diagnostic_constr_head term =
  let head, arguments = Constr.decompose_app term in
  let head =
    match Constr.kind head with
    | Const (constant, _) -> Constant.to_string constant
    | Ind (inductive, _) -> MutInd.to_string (fst inductive) ^ ".<ind>"
    | Construct (constructor, _) ->
      MutInd.to_string (fst (fst constructor)) ^ ".<ctor>"
    | Rel index -> Printf.sprintf "rel(%d)" index
    | Var id -> Id.to_string id
    | Sort _ -> "sort" | Prod _ -> "product" | Lambda _ -> "lambda"
    | LetIn _ -> "let" | Case _ -> "case" | Fix _ -> "fix"
    | CoFix _ -> "cofix" | Proj _ -> "projection" | Evar _ -> "evar"
    | Meta _ -> "meta" | Cast _ -> "cast" | Int _ -> "int"
    | Float _ -> "float" | String _ -> "string" | Array _ -> "array"
    | App _ -> "app"
  in
  Printf.sprintf "%s/%d" head (Array.length arguments)

let diagnostic_fterm_tag term =
  match fterm_of term with
  | FRel index -> Printf.sprintf "rel(%d)" index
  | FAtom atom ->
    begin match Constr.kind atom with
    | Sort _ -> "sort" | Meta _ -> "meta" | _ -> "atom"
    end
  | FFlex (ConstKey (constant, _)) -> Constant.to_string constant
  | FFlex (VarKey id) -> Id.to_string id
  | FFlex (RelKey index) -> Printf.sprintf "rel-key(%d)" index
  | FInd (inductive, _) -> MutInd.to_string (fst inductive) ^ ".<ind>"
  | FConstruct ((constructor, _), _) ->
    MutInd.to_string (fst (fst constructor)) ^ ".<ctor>"
  | FApp _ -> "app" | FProj _ -> "projection" | FFix _ -> "fix"
  | FCoFix _ -> "cofix" | FCaseT _ -> "case" | FCaseInvert _ -> "case-invert"
  | FLambda _ -> "lambda" | FProd _ -> "product" | FLetIn _ -> "let"
  | FEvar _ -> "evar" | FInt _ -> "int" | FFloat _ -> "float"
  | FString _ -> "string" | FArray _ -> "array" | FPeanoNat _ -> "peano"
  | FLIFT _ -> "lift" | FCLOS _ -> "closure" | FIrrelevant -> "irrelevant"
  | FLOCKED -> "locked"

let diagnostic_stack_tag stack =
  let rec tags remaining = function
    | [] -> []
    | _ when remaining = 0 -> [ "..." ]
    | frame :: rest ->
      let tag = match frame with
        | Zapp arguments -> Printf.sprintf "app(%d)" (Array.length arguments)
        | Zproj _ -> "projection" | Zfix _ -> "fix" | ZcaseT _ -> "case"
        | Zprimitive _ -> "primitive" | Zshift _ -> "shift"
        | Zupdate _ -> "update"
      in
      tag :: tags (remaining - 1) rest
  in
  String.concat "/" (tags 16 stack)

let diagnostic_trace_pair phase (left_head, left_stack)
    (right_head, right_stack) =
  if !diagnostic_conversion_trace then begin
    incr diagnostic_conversion_trace_steps;
    let step = !diagnostic_conversion_trace_steps in
    if step <= 64 || (step >= 430 && step <= 512) ||
       Int.equal (step land (step - 1)) 0
    then begin
      let stat = Gc.quick_stat () in
      Printf.eprintf
        "[conversion trace] %s step=%d pairs=%d repeats=%d memo_hits=%d memo_stores=%d memo_size=%d memo_peak=%d memo_clears=%d heap_words=%d major_collections=%d %s[%s] <> %s[%s]\n%!"
        phase step
        (DiagnosticConversionPairs.length diagnostic_conversion_trace_pairs)
        !diagnostic_conversion_trace_repeats
        !diagnostic_conversion_trace_memo_hits
        !diagnostic_conversion_trace_memo_stores
        !diagnostic_conversion_trace_memo_size
        !diagnostic_conversion_trace_memo_peak
        !diagnostic_conversion_trace_memo_clears
        stat.Gc.heap_words stat.Gc.major_collections
        (diagnostic_fterm_tag left_head) (diagnostic_stack_tag left_stack)
        (diagnostic_fterm_tag right_head) (diagnostic_stack_tag right_stack)
    end
  end

let successful_conversion_cached infos cv_pb lft1 lft2 term1 term2 =
  infos.cnv_memoize_successful_conversions &&
  match ConversionPairs.find_opt
          infos.cnv_successful_conversions.successful_conversion_table
          (term1, term2) with
  | None -> false
  | Some conversions ->
    let relevances = info_relevances infos.cnv_inf in
    let cached = List.exists (fun conversion ->
      conversion.conversion_problem = cv_pb &&
      eq_lift conversion.conversion_left_lift lft1 &&
      eq_lift conversion.conversion_right_lift lft2 &&
      conversion.conversion_relevances == relevances &&
      conversion.conversion_rel_types == infos.cnv_rel_types &&
      conversion.conversion_rel_type_lifts == infos.cnv_rel_type_lifts)
      conversions in
    if cached && !diagnostic_conversion_trace then
      incr diagnostic_conversion_trace_memo_hits;
    cached

(* Both indexes share the original retention allowance. Eviction changes only
   performance: the next miss repeats the ordinary checked conversion. *)
let reserve_successful_conversion cache =
  if cache.successful_conversion_size + cache.suspended_size >=
      cache.successful_conversion_limit then begin
    ConversionPairs.clear cache.successful_conversion_table;
    SuspendedPairs.clear cache.suspended_table;
    cache.successful_conversion_size <- 0;
    cache.suspended_size <- 0;
    cache.successful_conversion_clears <- cache.successful_conversion_clears + 1;
    if !diagnostic_conversion_trace then begin
      diagnostic_conversion_trace_memo_size := 0;
      incr diagnostic_conversion_trace_memo_clears
    end
  end

let record_successful_conversion_size cache =
  let size = cache.successful_conversion_size + cache.suspended_size in
  cache.successful_conversion_peak <- max cache.successful_conversion_peak size;
  if !diagnostic_conversion_trace then begin
    incr diagnostic_conversion_trace_memo_stores;
    diagnostic_conversion_trace_memo_size := size;
    diagnostic_conversion_trace_memo_peak :=
      max !diagnostic_conversion_trace_memo_peak cache.successful_conversion_peak
  end

let remember_successful_conversion infos cv_pb lft1 lft2 term1 term2 =
  if infos.cnv_memoize_successful_conversions then begin
    let cache = infos.cnv_successful_conversions in
    reserve_successful_conversion cache;
    let key = term1, term2 in
    let previous =
      Option.default []
        (ConversionPairs.find_opt cache.successful_conversion_table key)
    in
    let previous =
      let length = List.length previous in
      if length < 8 then previous
      else begin
        cache.successful_conversion_size <- cache.successful_conversion_size - length;
        []
      end
    in
    ConversionPairs.replace cache.successful_conversion_table key
      ({
        conversion_problem = cv_pb;
        conversion_left_lift = lft1;
        conversion_right_lift = lft2;
        conversion_relevances = info_relevances infos.cnv_inf;
        conversion_rel_types = infos.cnv_rel_types;
        conversion_rel_type_lifts = infos.cnv_rel_type_lifts;
      } :: previous);
    cache.successful_conversion_size <- cache.successful_conversion_size + 1;
    record_successful_conversion_size cache
  end

(* Only completed comparisons at a fixed universe graph enter this cache.
   No closure is quoted, unfolded or mutated to look up an entry. A syntactic
   check that runs out of its usual budget is simply a miss. *)
let suspended_key infos term1 term2 =
  if not infos.cnv_memoize_successful_conversions then None else
  let original term = Option.default term (CClosure.symbolic_view term) in
  let capture term = match fterm_of (original term) with
    | FCLOS (body, subst) -> Some (SuspendedTerm body, subst)
    | FLambda (n, ds, body, subst) when n <= 1024 ->
      Some (SuspendedLambda (ds, body), subst)
    | _ -> None in
  match capture term1, capture term2 with
  | Some (body1, subst1), Some (body2, subst2) ->
    Some ((body1, body2), subst1, subst2)
  | _ -> None

let same_suspended_instance budget subst template old =
  match template with
  | SuspendedTerm body -> compare_under ~symbolic:true budget subst body old body
  | SuspendedLambda (domains, body) ->
    let rec under_domains subst old = function
      | [] -> compare_under ~symbolic:true budget subst body old body
      | (_, domain) :: rest ->
        compare_under ~symbolic:true budget subst domain old domain &&
        under_domains (usubs_lift subst) (usubs_lift old) rest
    in under_domains subst old domains

let suspended_cached infos problem lft1 lft2 = function
  | None -> false
  | Some ((body1, body2) as key, subst1, subst2) ->
    let cache = infos.cnv_successful_conversions in
    match SuspendedPairs.find_opt cache.suspended_table key with
    | None -> false
    | Some entries ->
      let budget = ref 1024 in
      let hit = List.exists (fun (entry, old1, old2) ->
        entry.conversion_problem = problem &&
        eq_lift entry.conversion_left_lift lft1 &&
        eq_lift entry.conversion_right_lift lft2 &&
        entry.conversion_relevances == info_relevances infos.cnv_inf &&
        entry.conversion_rel_types == infos.cnv_rel_types &&
        entry.conversion_rel_type_lifts == infos.cnv_rel_type_lifts &&
        same_suspended_instance budget subst1 body1 old1 &&
        same_suspended_instance budget subst2 body2 old2) entries in
      if hit && !diagnostic_conversion_trace then
        incr diagnostic_conversion_trace_memo_hits;
      hit

let remember_suspended infos problem lft1 lft2 = function
  | None -> ()
  | Some (key, subst1, subst2) ->
    let cache = infos.cnv_successful_conversions in
    reserve_successful_conversion cache;
    let entries = Option.default [] (SuspendedPairs.find_opt cache.suspended_table key) in
    let count = List.length entries in
    let entries = if count < 8 then entries else begin
      cache.suspended_size <- cache.suspended_size - count; [] end in
    let entry = {
      conversion_problem = problem;
      conversion_left_lift = lft1; conversion_right_lift = lft2;
      conversion_relevances = info_relevances infos.cnv_inf;
      conversion_rel_types = infos.cnv_rel_types;
      conversion_rel_type_lifts = infos.cnv_rel_type_lifts } in
    SuspendedPairs.replace cache.suspended_table key ((entry, subst1, subst2) :: entries);
    cache.suspended_size <- cache.suspended_size + 1;
    record_successful_conversion_size cache

(* For [f args .field more_args], Lean compares the source [f args] before
   the arguments of the projected method. If source congruence fails, delta
   may expose a method that discards [more_args]. Keep the usual right-to-left
   comparison within each application segment, but do not cross a projection
   boundary before its source segment has succeeded. This merely orders the
   existing checks; every segment and projection is still checked on success.
   Non-projection eliminations retain the original stack traversal. *)
let compare_projection_segments compare compared nargs stack1 stack2 cuniv =
  let rec split left right stack1 stack2 =
    match stack1, stack2 with
    | (Zlapp _ as a) :: rest1, (Zlapp _ as b) :: rest2 ->
      split (a :: left) (b :: right) rest1 rest2
    | Zlproj (p, _) :: rest1, Zlproj (q, _) :: rest2 ->
      Some (List.rev left, List.rev right, p, q, rest1, rest2)
    | _ -> None
  in
  let rec segments compared nargs stack1 stack2 cuniv =
    match split [] [] stack1 stack2 with
    | None -> compare compared nargs stack1 stack2 cuniv
    | Some (prefix1, prefix2, p, q, rest1, rest2) ->
      if not (Projection.Repr.CanOrd.equal p q) then raise NotConvertible;
      let cuniv = compare compared nargs prefix1 prefix2 cuniv in
      segments [||] (-1) rest1 rest2 cuniv
  in
  segments compared nargs stack1 stack2 cuniv

(* Conversion between  [lft1]term1 and [lft2]term2 *)
let rec ccnv cv_pb l2r infos lft1 lft2 term1 term2 cuniv =
  let () =
    if !diagnostic_conversion_trace &&
       diagnostic_conversion_trace_pairs_enabled
    then
      if DiagnosticConversionPairs.mem diagnostic_conversion_trace_pairs
           (term1, term2)
      then incr diagnostic_conversion_trace_repeats
      else DiagnosticConversionPairs.add diagnostic_conversion_trace_pairs
             (term1, term2) ()
  in
  let fast = fast_test lft1 term1 lft2 term2 in
  let suspended = if fast then None else suspended_key infos term1 term2 in
  if fast || successful_conversion_cached infos cv_pb lft1 lft2 term1 term2 ||
     suspended_cached infos cv_pb lft1 lft2 suspended
  then cuniv
  else begin
    let result =
      let compare () =
        let symbolic_congruence () =
          if not infos.cnv_typ || !(infos.cnv_symbolic_remaining) = 0 ||
             Option.has_some infos.cnv_symbolic_budget ||
             not (Environ.typing_flags (info_env infos.cnv_inf)).unfold_dep_heuristic
          then None else
          if projection_conversion_cached infos.cnv_failed_symbolic
              ~relevances:(info_relevances infos.cnv_inf)
              ~rel_types:infos.cnv_rel_types
              ~rel_type_lifts:infos.cnv_rel_type_lifts
              lft1 term1 lft2 term2 then None else
          match symbolic_view term1, symbolic_view term2 with
          | Some left, Some right when left != term1 || right != term2 ->
            let recovery = { infos with
              cnv_inf = infos_with_symbolic_views infos.cnv_inf;
              cnv_symbolic_budget = Some (ref 4096) } in
            begin try Some (eqappr cv_pb l2r recovery
                (lft1, (left, [])) (lft2, (right, [])) cuniv)
            with Symbolic_budget_exhausted | NotConvertible | NotConvertibleTrace _ ->
              (* A failed optimization hint, not a negative equality result.
                 Exhaustion falls back to shared reduction below. *)
              remember_projection_conversion infos.cnv_failed_symbolic {
                projection_left_lift = lft1; projection_left_term = term1;
                projection_right_lift = lft2; projection_right_term = term2;
                projection_relevances = info_relevances infos.cnv_inf;
                projection_rel_types = infos.cnv_rel_types;
                projection_rel_type_lifts = infos.cnv_rel_type_lifts };
              None end
          | _ -> None in
        match symbolic_congruence () with
        | Some cu -> cu
        | None -> eqappr cv_pb l2r infos
            (lft1, (term1,[])) (lft2, (term2,[])) cuniv
      in
      match infos.cnv_probe_budget with
      | None -> compare ()
      | Some remaining ->
        if Int.equal !remaining 0 then raise Probe_budget_exhausted;
        decr remaining;
        Fun.protect compare ~finally:(fun () -> incr remaining)
    in
    remember_successful_conversion infos cv_pb lft1 lft2 term1 term2;
    remember_suspended infos cv_pb lft1 lft2 suspended;
    result
  end

(* Conversion between [lft1](hd1 v1) and [lft2](hd2 v2) *)
and eqappr cv_pb l2r infos (lft1,st1) (lft2,st2) cuniv =
  diagnostic_trace_pair "eqappr" st1 st2;
  Control.check_for_interrupt ();
  (* First head reduce both terms *)
  let ninfos = infos_with_reds infos.cnv_inf RedFlags.betaiotazeta in
  let appr1 = whd_stack ninfos infos.lft_tab
    (fst st1) (snd st1) in
  let appr2 = whd_stack ninfos infos.rgt_tab
    (fst st2) (snd st2) in
  eqwhnf cv_pb l2r infos (lft1, appr1) (lft2, appr2) cuniv

(* Lean's lazy_delta_proj_reduction: compare symbolic sources while they are
   delta applications, but select the requested fields when a constructor is
   exposed. Comparing entire exposed records would inspect unrelated fields.
   This helper is only used for bare projections. Argument masks remain
   restricted to the well-typed checking API; generic universe inference
   compares every argument and threads its constraint state normally. *)
and lazy_projection_sources cv_pb l2r infos lft1 p1 r1 c1 lft2 p2 r2 c2 cuniv =
  let ninfos = infos_with_reds infos.cnv_inf RedFlags.betaiotazeta in
  let oracle = oracle_of_infos infos.cnv_inf in
  let application_stack = List.for_all (function
    | Zapp _ | Zshift _ | Zupdate _ -> true
    | Zproj _ | ZcaseT _ | Zfix _ | Zprimitive _ -> false) in
  let reference = function
    | ConstKey (c, _) -> Some (Conv_oracle.EvalConstRef c)
    | VarKey x -> Some (Conv_oracle.EvalVarRef x)
    | RelKey _ -> None in
  let regular = function
    | ConstKey (c, _) ->
      (match Conv_oracle.get_strategy oracle (Conv_oracle.EvalConstRef c) with
       | Conv_oracle.Expand -> false | Conv_oracle.Level _ | Conv_oracle.Opaque -> true)
    | VarKey _ | RelKey _ -> true in
  let same_forwarded_source reference1 stack1 reference2 stack2 =
    match unfold_projection infos.cnv_inf p1 r1, unfold_projection infos.cnv_inf p2 r2 with
    | Some frame1, Some frame2 ->
      same_forwarded_projection_source infos lft1 reference1 (stack1 @ [frame1])
        lft2 reference2 (stack2 @ [frame2])
    | _ -> false in
  let charge () =
    Control.check_for_interrupt ();
    (match infos.cnv_strategy_budget with
     | None -> ()
     | Some remaining ->
       if !remaining = 0 then raise Strategy_budget_exhausted;
       decr remaining);
    (match infos.cnv_symbolic_budget with
     | None -> ()
     | Some remaining ->
       if !remaining = 0 || !(infos.cnv_symbolic_remaining) = 0 then
         raise Symbolic_budget_exhausted;
       decr remaining; decr infos.cnv_symbolic_remaining)
  in
  let rec drive source1 source2 =
    charge ();
    let h1, s1 = whd_stack ninfos infos.lft_tab (fst source1) (snd source1) in
    let h2, s2 = whd_stack ninfos infos.rgt_tab (fst source2) (snd source2) in
    let selected_fields () =
      match unfold_projection infos.cnv_inf p1 r1,
            unfold_projection infos.cnv_inf p2 r2 with
      | Some frame1, Some frame2 ->
        Some (eqappr cv_pb l2r infos
          (lft1, (h1, s1 @ [frame1])) (lft2, (h2, s2 @ [frame2])) cuniv)
      | _ -> None in
    let remaining_sources () =
      try Some (eqappr CONV l2r infos (lft1, (h1, s1)) (lft2, (h2, s2)) cuniv)
      with NotConvertible | NotConvertibleTrace _ -> None in
    match fterm_of h1, fterm_of h2 with
    | FFlex fl1, FFlex fl2 when application_stack s1 && application_stack s2 ->
      let congruence () =
        if not (regular fl1 && regular fl2) ||
           same_forwarded_source fl1 s1 fl2 s2
        then None else
        try
          let nargs = same_args_size s1 s2 in
          let cu = conv_table_key infos ~nargs fl1 fl2 cuniv in
          let mask = if not infos.cnv_typ then [||] else match fl1 with
            | ConstKey _ -> get_ref_mask infos.cnv_inf infos.lft_tab fl1
            | VarKey _ | RelKey _ -> [||] in
          Some (try_congruence infos lft1 lft2 fl1 s1 fl2 s2 (fun infos ->
            convert_stacks ~mask l2r infos lft1 lft2 s1 s2 cu))
        with NotConvertible | NotConvertibleTrace _ -> None
      in
      begin match congruence () with
      | Some cu -> Some cu
      | None ->
        match unfold_ref_with_args infos.cnv_inf infos.lft_tab fl1 s1,
              unfold_ref_with_args infos.cnv_inf infos.rgt_tab fl2 s2 with
        | None, None -> None
        | Some left, None -> drive left (h2, s2)
        | None, Some right -> drive (h1, s1) right
        | Some left, Some right ->
          match Conv_oracle.oracle_compare oracle (reference fl1) (reference fl2) with
          | Conv_oracle.Left -> drive left (h2, s2)
          | Conv_oracle.Right -> drive (h1, s1) right
          | Conv_oracle.Same -> drive left right
      end
    | FConstruct _, _ | _, FConstruct _ -> selected_fields ()
    | FFlex fl1, _ when application_stack s1 ->
      (match unfold_ref_with_args infos.cnv_inf infos.lft_tab fl1 s1 with
       | Some left -> drive left (h2, s2)
       | None -> remaining_sources ())
    | _, FFlex fl2 when application_stack s2 ->
      (match unfold_ref_with_args infos.cnv_inf infos.rgt_tab fl2 s2 with
       | Some right -> drive (h1, s1) right
       | None -> remaining_sources ())
    | _ -> remaining_sources ()
  in
  drive (c1, []) (c2, [])

(* assumes that appr1 and appr2 are in whnf *)
and eqwhnf cv_pb l2r infos (lft1, (hd1, v1) as appr1) (lft2, (hd2, v2) as appr2) cuniv =
  let () = match infos.cnv_symbolic_budget with
    | None -> ()
    | Some remaining ->
      if !remaining = 0 || !(infos.cnv_symbolic_remaining) = 0 then
        raise Symbolic_budget_exhausted;
      decr infos.cnv_symbolic_remaining;
      decr remaining in
  let checked_unit_equality () =
    Option.bind (unit_operand_type infos lft1 (hd1, v1)) (fun typ1 ->
        (* Earlier classifications are only search hints: local domains can
           still use their original binder context. Certify singleton status
           again on the complete type relocated into the common context. *)
        Option.bind (shallow_unit_like_after_applying infos typ1 []) (fun _ ->
          Option.bind (unit_operand_type infos lft2 (hd2, v2)) (fun typ2 ->
          try Some (ccnv CONV l2r infos el_id el_id typ1 typ2 cuniv)
          with NotConvertible | NotConvertibleTrace _ -> None)))
  in
  let () = match infos.cnv_strategy_budget with
    | None -> ()
    | Some remaining ->
      if !remaining = 0 then raise Strategy_budget_exhausted;
      decr remaining
  in
  diagnostic_trace_pair "eqwhnf" (hd1, v1) (hd2, v2);
  (** We delay the computation of the lifts that apply to the head of the term
      with [el_stack] inside the branches where they are actually used. *)
  (** Irrelevant terms are guaranteed to be [FIrrelevant], except for [FFlex],
      [FRel] and [FLambda]. Those ones are handled specifically below. *)
  match (fterm_of hd1, fterm_of hd2) with
    (* case of leaves *)
    | (FAtom a1, FAtom a2) ->
        (match kind a1, kind a2 with
           | (Sort s1, Sort s2) ->
               if not (is_empty_stack v1 && is_empty_stack v2) then
                 (* May happen because we convert application right to left *)
                 raise NotConvertible;
              fail_check infos @@ sort_cmp_universes cv_pb s1 s2 cuniv
           | (Meta n, Meta m) ->
               if Int.equal n m
               then convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
               else raise NotConvertible
           | _ -> raise NotConvertible)
    | (FEvar (ev1, args1, env1, _), FEvar (ev2, args2, env2, _)) ->
        if Evar.equal ev1 ev2 then
          let el1 = el_stack lft1 v1 in
          let el2 = el_stack lft2 v2 in
          let cuniv = convert_stacks l2r infos lft1 lft2 v1 v2 cuniv in
          convert_list l2r infos el1 el2
            (List.map (mk_clos env1) args1)
            (List.map (mk_clos env2) args2) cuniv
        else raise NotConvertible

    (* 2 index known to be bound to no constant *)
    | (FRel n, FRel m) ->
        let trace_rel stage =
          if !diagnostic_conversion_trace &&
             !(diagnostic_conversion_trace_steps) >= 450 &&
             !(diagnostic_conversion_trace_steps) <= 512
          then Printf.eprintf "[rel trace] %s\n%!" stage
        in
        let () = trace_rel "start" in
        let original_n = n in
        let original_m = m in
        let el1 = el_stack lft1 v1 in
        let el2 = el_stack lft2 v2 in
        let () = trace_rel "after lifts" in
        let n = reloc_rel n el1 in
        let m = reloc_rel m el2 in
        let () = trace_rel "after relocation" in
        let rn = Range.get (info_relevances infos.cnv_inf) (n - 1) in
        let rm = Range.get (info_relevances infos.cnv_inf) (m - 1) in
        let () = trace_rel "after relevance lookup" in
        if is_irrelevant infos.cnv_inf rn && is_irrelevant infos.cnv_inf rm then
          let v1 = CClosure.skip_irrelevant_stack infos.cnv_inf v1 in
          let v2 = CClosure.skip_irrelevant_stack infos.cnv_inf v2 in
          convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
        else
          let same_unit_like () =
            if has_type_elimination_stack v1 || has_type_elimination_stack v2 then
              checked_unit_equality ()
            else
            let () = trace_rel "unit-like start" in
            let unit1 =
              unit_like_of_rel infos infos.lft_tab lft1 v1 original_n
            in
            let () = trace_rel "after left unit-like" in
            let unit2 =
              unit_like_of_rel infos infos.rgt_tab lft2 v2 original_m
            in
            let () = trace_rel "after right unit-like" in
            match unit1, unit2 with
            | Some ind1, Some ind2 when Ind.UserOrd.equal ind1 ind2 ->
              checked_unit_equality ()
            | _ -> None
          in
          if Int.equal n m then
            try convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
            with (NotConvertible | NotConvertibleTrace _) as error ->
              (match same_unit_like () with Some cu -> cu | None -> raise error)
          else
            (match same_unit_like () with Some cu -> cu | None -> raise NotConvertible)

    (* 2 constants, 2 local defined vars or 2 defined rels *)
    | (FFlex fl1, FFlex fl2) ->
      let key = if infos.cnv_memoize_successful_conversions then
        application_key infos lft1 lft2 fl1 v1 fl2 v2 else None in
      if completed_application infos cv_pb key then cuniv else
      let result =
      let preserve_symbolic_arguments =
        let env = info_env infos.cnv_inf in
        direct_head_alias env fl1 fl2 || direct_head_alias env fl2 fl1 ||
        (match fl1, fl2 with
         | ConstKey (c1, _), ConstKey (c2, _) when Constant.UserOrd.equal c1 c2 ->
           syntactically_same_arguments lft1 v1 lft2 v2
         | _ -> false) in
      let v1, v2 = if preserve_symbolic_arguments then v1, v2 else
        expose_eliminator_major ~tab:infos.lft_tab infos fl1 v1,
        expose_eliminator_major ~tab:infos.rgt_tab infos fl2 v2 in
      let appr1 = lft1, (hd1, v1) in
      let appr2 = lft2, (hd2, v2) in
      let trace_flex stage =
        if !diagnostic_conversion_trace &&
           !(diagnostic_conversion_trace_steps) >= 450 &&
           !(diagnostic_conversion_trace_steps) <= 512
        then Printf.eprintf "[flex trace] %s\n%!" stage
      in
      let () = trace_flex "start" in
      (try
         (* Lean's same-definition argument shortcut is for regular hints,
            not abbreviations. An expandable recursor wrapper must expose its
            scrutinee before comparing potentially discarded branch functions.
            Do not suppress congruence when transparency prevents unfolding. *)
         let expand_before_arguments =
           infos.cnv_typ &&
           (Environ.typing_flags (info_env infos.cnv_inf)).unfold_dep_heuristic &&
           match fl1 with
           | ConstKey (c, _) when
               RedFlags.red_set (info_flags infos.cnv_inf) (RedFlags.fCONST c) ->
             begin match Conv_oracle.get_strategy (oracle_of_infos infos.cnv_inf)
                 (Conv_oracle.EvalConstRef c),
                 (Environ.lookup_constant c (info_env infos.cnv_inf)).const_body with
             | Conv_oracle.Expand, Def _ -> true
             | _ -> false end
           | _ -> false
         in
         if expand_before_arguments then raise NotConvertible;
         (* A projection of a transparent constructor wrapper may discard
            parameters of that wrapper. Expose the constructor before trying
            to compare all those parameters. *)
         if applied_projection_source infos fl1 v1 ||
            applied_projection_source infos fl2 v2 ||
            (not (bare_projection_stack v1) && projected_record_wrapper infos fl1 v1) ||
            (not (bare_projection_stack v2) && projected_record_wrapper infos fl2 v2) ||
            (bare_projection_stack v1 && bare_projection_stack v2 &&
             same_forwarded_projection_source infos lft1 fl1 v1 lft2 fl2 v2)
         then raise NotConvertible;
         let nargs = same_args_size v1 v2 in
         let () = trace_flex "after argument sizes" in
         let cuniv = conv_table_key infos ~nargs fl1 fl2 cuniv in
         let () = trace_flex "after key" in
         if (constructor_eliminator_application infos fl1 v1 ||
             constructor_eliminator_application infos fl2 v2) &&
            not (syntactically_same_arguments lft1 v1 lft2 v2)
         then raise NotConvertible;
         let irrelevant1 = irr_flex infos.cnv_inf fl1 in
         let () = trace_flex "after relevance" in
         let () = if irrelevant1 then raise NotConvertible (* trigger the fallback *) in
         let mask = if infos.cnv_typ then match fl1 with
         | ConstKey _ -> get_ref_mask infos.cnv_inf infos.lft_tab fl1
         | RelKey _ | VarKey _ -> [||]
         else [||]
         in
         let constructor_first =
           not diagnostic_no_direct_arguments &&
           infos.cnv_typ && infos.cnv_dependency_preference &&
           (Environ.typing_flags (info_env infos.cnv_inf)).unfold_dep_heuristic &&
           (match fl1 with ConstKey _ -> true | RelKey _ | VarKey _ -> false)
         in
         let compare infos =
           convert_stacks ~mask ~constructor_first
             ~projection_prefix_first:(infos.cnv_typ &&
               (Environ.typing_flags (info_env infos.cnv_inf)).unfold_dep_heuristic)
             l2r infos lft1 lft2 v1 v2 cuniv
         in
         let can_unfold = match fl1 with
           | ConstKey (c, _) when
               RedFlags.red_set (info_flags infos.cnv_inf) (RedFlags.fCONST c) ->
             (match (Environ.lookup_constant c (info_env infos.cnv_inf)).const_body with
              | Def _ -> true
              | Undef _ | OpaqueDef _ | Primitive _ | Symbol _ -> false)
           | ConstKey _ | RelKey _ | VarKey _ -> false
         in
         if can_unfold then try_congruence infos lft1 lft2 fl1 v1 fl2 v2 compare
         else compare infos
       with NotConvertible | NotConvertibleTrace _ ->
        let () = trace_flex "fallback" in
        (* A projection alone is not evidence that its result is singleton-like.
           Keep the early shortcut for classified unit types; otherwise try
           ordinary unfolding before reconstructing complete operand types. *)
        match (if same_unit_like_flexes infos lft1 v1 fl1 lft2 v2 fl2
               then checked_unit_equality () else None) with
        | Some cu -> cu
        | None ->
          let () = trace_flex "after unit-like" in
          let r1 = unfold_ref_with_args infos.cnv_inf infos.lft_tab fl1 v1 in
          let () = trace_flex "after left unfold" in
          let r2 = unfold_ref_with_args infos.cnv_inf infos.rgt_tab fl2 v2 in
          let () = trace_flex "after right unfold" in
          match r1, r2 with
          | None, None ->
            (match checked_unit_equality () with
             | Some cu -> cu | None -> raise NotConvertible)
          | Some (t1, v1), Some (t2, v2) ->
          let () = trace_flex "both unfolded" in
          (* else the oracle tells which constant is to be expanded *)
          let oracle = CClosure.oracle_of_infos infos.cnv_inf in
          let to_er fl =
            match fl with
            | ConstKey (c, _) -> Some (Conv_oracle.EvalConstRef c)
            | VarKey id -> Some (Conv_oracle.EvalVarRef id)
            | RelKey _ -> None
          in
          let ninfos = infos_with_reds infos.cnv_inf RedFlags.betaiotazeta in
          let is_compact_peano_elimination tab term stack =
            let symbolic_infos =
              infos_with_reds infos.cnv_inf RedFlags.betazeta
            in
            let head, stack = whd_stack symbolic_infos tab term stack in
            match fterm_of head, stack with
            | FPeanoNat _, Zfix _ :: _ -> true
            | _ -> false
          in
          let compact_elimination1 =
            is_compact_peano_elimination infos.lft_tab t1 v1
          in
          let () = trace_flex "after left compact-elimination probe" in
          let compact_elimination2 =
            is_compact_peano_elimination infos.rgt_tab t2 v2
          in
          let () = trace_flex "after right compact-elimination probe" in
          let () = trace_flex (Printf.sprintf "compact eliminations: %b %b"
            compact_elimination1 compact_elimination2) in
          (** Before forcing an elimination over a compact Peano natural, try
              ordinary congruence on its outermost application.  The function
              prefixes can be convertible even when reducing either complete
              application would traverse a large recursion certificate.

              Reify the probe into fresh closures so it cannot mutate the
              sharing updates of the main conversion. Apply each side's lift
              and retain the current binder depth. Bound expanded syntax
              before quotation, sharing one allowance across both sides.
              Both the peeled
              argument and the prefixes are checked normally; on failure, use
              the standard delta-reduction path below. *)
          let common_application_congruence () =
            let env = CClosure.info_env infos.cnv_inf in
            if not (Environ.typing_flags env).unfold_dep_heuristic ||
               not (compact_elimination1 || compact_elimination2)
            then None
            else match v1, v2 with
            | Zapp args1 :: rest1, Zapp args2 :: rest2
              when Int.equal (Array.length args1) (Array.length args2) &&
                   List.for_all (function Zupdate _ -> true | _ -> false) rest1 &&
                   List.for_all (function Zupdate _ -> true | _ -> false) rest2 ->
              let argument_count = Array.length args1 in
              if Int.equal argument_count 0 || argument_count > 2047 then None
              else
                let prefix_length = argument_count - 1 in
                let subst = subs_id (Range.length (info_relevances infos.cnv_inf)),
                  UVars.Instance.empty in
                let fresh_term lift term = mk_clos subst (Vars.exliftn lift term) in
                let remaining = ref application_quotation_budget in
                let reify term =
                  if not (small_reification remaining term) then raise NotConvertible;
                  term_of_fconstr term in
                let fresh_argument lift argument =
                  fresh_term lift (reify argument) in
                let fresh_prefix lift head args =
                  let stack =
                    if Int.equal prefix_length 0 then []
                    else [Zapp (Array.sub args 0 prefix_length)]
                  in
                  fresh_term lift (reify (zip head stack))
                in
                (try
                   Some (with_congruence_budget infos (fun infos ->
                   let cuniv =
                     ccnv CONV l2r infos el_id el_id
                       (fresh_argument lft1 args1.(prefix_length))
                       (fresh_argument lft2 args2.(prefix_length)) cuniv
                   in
                   ccnv cv_pb l2r infos el_id el_id
                     (fresh_prefix lft1 hd1 args1) (fresh_prefix lft2 hd2 args2) cuniv))
                 with NotConvertible | NotConvertibleTrace _ -> None)
            | _ -> None
          in
          let () = trace_flex "before application-congruence probe" in
          begin match common_application_congruence () with
          | Some cuniv -> cuniv
          | None ->
          let () = trace_flex "after application-congruence probe" in
          let () = Control.check_for_interrupt () in
          let same_reference =
            match fl1, fl2 with
            | ConstKey (constant1, _), ConstKey (constant2, _) ->
              Constant.UserOrd.equal constant1 constant2
            | VarKey id1, VarKey id2 -> Id.equal id1 id2
            | RelKey index1, RelKey index2 -> Int.equal index1 index2
            | (ConstKey _ | VarKey _ | RelKey _), _ -> false
          in
          let has_constructor_argument tab stack =
            let symbolic_infos =
              infos_with_reds infos.cnv_inf RedFlags.betazeta
            in
            let constructor argument =
              let head, _ = whd_stack symbolic_infos tab argument [] in
              match fterm_of head with
              | FConstruct _ | FPeanoNat _ -> true
              | _ -> false
            in
            List.exists
              (function
                | Zapp arguments -> Array.exists constructor arguments
                | Zupdate _ | Zshift _ | Zproj _ | Zfix _ | ZcaseT _
                | Zprimitive _ -> false)
              stack
          in
          let indirectly_depends_on ?(transitive = true) term stack target =
            diagnostic_time_indirect (fun () ->
              (* This only guides unfolding. Reifying a shared closure can
                 expand a large proof merely to inspect its constants. Probe
                 supported forms directly, with one budget for the whole
                 process; unknown results leave the usual strategy available.
                 Lifts and universe substitution do not change constant names.
                 Inspect referenced term substitutions without reifying or
                 reducing them. Never reduce or mutate the input. *)
              let exception Found_dependency in
              let exception Unknown_dependency of string in
              let remaining = ref 1024 in
              let update_targets = ref [] in
              let visit () =
                if Int.equal !remaining 0 then
                  raise (Unknown_dependency "budget-exhausted");
                decr remaining
              in
              let inspect_constant constant =
                (* A direct occurrence is already a dependency witness. The
                   environment query only follows the constant's body. *)
                if Constant.UserOrd.equal constant target then raise Found_dependency;
                if transitive then
                  (* Graph traversal is part of this optional probe's work,
                     not a separate allowance multiplied at every closure. *)
                  match Environ.constant_depends_on ~fuel:remaining
                    (CClosure.info_env infos.cnv_inf) constant target with
                  | Some true -> raise Found_dependency
                  | Some false -> ()
                  | None -> raise (Unknown_dependency "graph-budget-exhausted")
              in
              let enter_binder depth =
                visit ();
                depth + 1
              in
              let rec inspect_constr ~aliases_only substitution depth term =
                visit ();
                match Constr.kind term with
                | Rel index when index > depth ->
                  (match substitution with
                  | None -> ()
                  | Some substitution ->
                    (match inspect_substituted_rel substitution (index - depth) with
                    | Some term -> inspect_closure ~aliases_only term
                    | None ->
                      raise (Unknown_dependency "constr:unresolved-substitution")))
                | Const (constant, _) ->
                  if not aliases_only then inspect_constant constant
                | _ ->
                  Constr.iter_with_binders enter_binder
                    (inspect_constr ~aliases_only substitution) depth term
              and inspect_closure ~aliases_only term =
                visit ();
                if aliases_only &&
                   List.exists (fun target -> target == term) !update_targets
                then raise (Unknown_dependency "closure:update-alias");
                match fterm_of term with
                | FFlex (ConstKey (constant, _)) ->
                  if not aliases_only then inspect_constant constant
                | FRel _ | FFlex (RelKey _ | VarKey _) | FInd _
                | FInt _ | FFloat _ | FString _ -> ()
                | FAtom term ->
                  if not aliases_only then inspect_constr ~aliases_only None 0 term
                | FConstruct (_, arguments) ->
                  Array.iter (inspect_closure ~aliases_only) arguments
                | FApp (head, arguments) ->
                  inspect_closure ~aliases_only head;
                  Array.iter (inspect_closure ~aliases_only) arguments
                | FProj (_, _, term) | FLIFT (_, term) ->
                  inspect_closure ~aliases_only term
                | FCLOS (term, substitution) when is_subs_id (fst substitution) ->
                  (* Raw terms cannot contain mutable closure cells. *)
                  if not aliases_only then inspect_constr ~aliases_only None 0 term
                | FCLOS (term, substitution) ->
                  inspect_constr ~aliases_only (Some substitution) 0 term
                | FLambda (len, domains, body, substitution) ->
                  let substitution =
                    if is_subs_id (fst substitution) then None
                    else Some substitution
                  in
                  if not aliases_only || Option.has_some substitution then begin
                    (* Domains are outermost first; only references outside
                       the binders belong to the saved substitution. *)
                    let rec inspect_domains depth = function
                      | [] ->
                        if not (Int.equal depth len) then
                          raise (Unknown_dependency "lambda:arity");
                        inspect_constr ~aliases_only substitution len body
                      | (_, domain) :: rest ->
                        visit ();
                        inspect_constr ~aliases_only substitution depth domain;
                        inspect_domains (enter_binder depth) rest
                    in
                    inspect_domains 0 domains
                  end
                | FFix _ -> raise (Unknown_dependency "closure:fix")
                | FCoFix _ -> raise (Unknown_dependency "closure:cofix")
                | FCaseT _ -> raise (Unknown_dependency "closure:case")
                | FCaseInvert _ -> raise (Unknown_dependency "closure:case-invert")
                | FProd _ -> raise (Unknown_dependency "closure:product")
                | FLetIn _ -> raise (Unknown_dependency "closure:let")
                | FEvar _ -> raise (Unknown_dependency "closure:evar")
                | FArray _ -> raise (Unknown_dependency "closure:array")
                | FPeanoNat _ -> raise (Unknown_dependency "closure:peano")
                | FIrrelevant -> raise (Unknown_dependency "closure:irrelevant")
                | FLOCKED -> raise (Unknown_dependency "closure:locked")
              in
              let rec inspect_stack ~aliases_only = function
                | [] -> ()
                | frame :: rest ->
                  visit ();
                  (match frame with
                  | Zapp arguments ->
                    Array.iter (inspect_closure ~aliases_only) arguments
                  | Zproj _ | Zshift _ | Zupdate _ -> ()
                  | Zfix _ -> raise (Unknown_dependency "stack:fix")
                  | ZcaseT _ -> raise (Unknown_dependency "stack:case")
                  | Zprimitive _ -> raise (Unknown_dependency "stack:primitive"));
                  inspect_stack ~aliases_only rest
              in
              let rec check_stack = function
                | [] -> ()
                | frame :: rest ->
                  visit ();
                  (match frame with
                  | Zapp _ | Zproj _ | Zshift _ -> check_stack rest
                  | Zupdate target ->
                    if List.exists (fun previous -> previous == target)
                        !update_targets
                    then raise (Unknown_dependency "stack:repeated-update");
                    update_targets := target :: !update_targets;
                    check_stack rest
                  | Zfix _ -> raise (Unknown_dependency "stack:fix")
                  | ZcaseT _ -> raise (Unknown_dependency "stack:case")
                  | Zprimitive _ -> raise (Unknown_dependency "stack:primitive"))
              in
              let () = trace_flex "before bounded dependency probe" in
              let result, reason =
                try
                  (* An update can change a cell aliased by a later argument.
                     Complete the alias check before accepting any early
                     dependency witness; neither pass mutates the process. *)
                  check_stack stack;
                  if not (CList.is_empty !update_targets) then begin
                    inspect_closure ~aliases_only:true term;
                    inspect_stack ~aliases_only:true stack
                  end;
                  inspect_closure ~aliases_only:false term;
                  inspect_stack ~aliases_only:false stack;
                  Some false, "complete"
                with
                | Found_dependency -> Some true, "witness"
                | Unknown_dependency reason -> None, reason
                | Assert_failure _ -> None, "assertion"
              in
              let () =
                if !diagnostic_conversion_trace &&
                   !diagnostic_conversion_trace_steps <= 512
                then
                  let outcome = match result with
                    | Some true -> "true" | Some false -> "false"
                    | None -> "unknown"
                  in
                  Printf.eprintf
                    "[conversion trace] indirect dependency step=%d result=%s reason=%s remaining=%d\n%!"
                    !diagnostic_conversion_trace_steps outcome reason !remaining
              in
              let () = trace_flex "after bounded dependency probe" in
              result)
          in
          (** Applications can be reduced independently to weak-head form.
              This avoids alternating delta steps between algebraically equal
              computations (for example [2 * 2^31] and [2^32]) until the
              conversion stack overflows. *)
          let reduce_applications_to_whnf () =
            let env = CClosure.info_env infos.cnv_inf in
            let compact_backed_closed_process term stack =
              (* Eligibility must not expand shared closures just to inspect
                 them. Unknown forms or exhausted fuel decline this optional
                 strategy. A compact witness never skips the remaining
                 closedness checks. *)
              let exception Unknown_eligibility of string in
              let remaining = ref 1024 in
              let dependency_fuel = ref 16_384 in
              let backed = ref false in
              let update_targets = ref [] in
              let trace_rejection reason =
                if !diagnostic_conversion_trace &&
                   !diagnostic_conversion_trace_steps <= 512
                then
                  Printf.eprintf
                    "[conversion trace] compact eligibility rejected step=%d reason=%s remaining=%d compact_witness=%b\n%!"
                    !diagnostic_conversion_trace_steps reason !remaining !backed
              in
              let visit () =
                if Int.equal !remaining 0 then
                  raise (Unknown_eligibility "budget-exhausted");
                decr remaining
              in
              let enter_binder depth =
                visit ();
                depth + 1
              in
              let inspect inspect_constant =
              let rec inspect_constr substitution depth term =
                visit ();
                match Constr.kind term with
                | Rel index ->
                  if index > depth then begin
                    (* Resolve only referenced substitution entries. Ignoring
                       their lifts preserves closedness and avoids copying
                       shared constructor spines during this bounded probe. *)
                    match Option.bind substitution (fun substitution ->
                        inspect_substituted_rel substitution (index - depth)) with
                    | Some term -> inspect_closure term
                    | None -> raise (Unknown_eligibility "free-rel:constr")
                  end
                | Const (constant, _) -> inspect_constant constant
                | Evar _ -> raise (Unknown_eligibility "constr:evar")
                | _ ->
                  Constr.iter_with_binders enter_binder
                    (inspect_constr substitution) depth term
              and inspect_closure term =
                visit ();
                if List.exists (fun target -> target == term) !update_targets
                then raise (Unknown_eligibility "closure:update-alias");
                match fterm_of term with
                | FFlex (ConstKey (constant, _)) -> inspect_constant constant
                | FFlex (VarKey _) | FInd _ | FInt _ | FFloat _ | FString _
                | FPeanoNat _ -> ()
                | FAtom term -> inspect_constr None 0 term
                | FConstruct (_, arguments) -> Array.iter inspect_closure arguments
                | FApp (head, arguments) ->
                  inspect_closure head;
                  Array.iter inspect_closure arguments
                | FProj (_, _, term) | FLIFT (_, term) -> inspect_closure term
                | FCLOS (term, substitution) ->
                  inspect_constr (Some substitution) 0 term
                | FLambda (len, domains, body, substitution) ->
                  (* Domains are ordered outermost first, as in [to_constr]'s
                     [List.mapi]; the body is under all [len] binders. *)
                  let rec inspect_domains depth = function
                    | [] ->
                      if not (Int.equal depth len) then
                        raise (Unknown_eligibility "lambda:arity");
                      inspect_constr (Some substitution) len body
                    | (_, domain) :: rest ->
                      visit ();
                      inspect_constr (Some substitution) depth domain;
                      inspect_domains (enter_binder depth) rest
                  in
                  inspect_domains 0 domains
                | FRel _ -> raise (Unknown_eligibility "free-rel:closure")
                | FFlex (RelKey _) ->
                  raise (Unknown_eligibility "free-rel:relative-key")
                | FFix _ -> raise (Unknown_eligibility "closure:fix")
                | FCoFix _ -> raise (Unknown_eligibility "closure:cofix")
                | FCaseT _ -> raise (Unknown_eligibility "closure:case")
                | FCaseInvert _ -> raise (Unknown_eligibility "closure:case-invert")
                | FProd _ -> raise (Unknown_eligibility "closure:product")
                | FLetIn _ -> raise (Unknown_eligibility "closure:let")
                | FEvar _ -> raise (Unknown_eligibility "closure:evar")
                | FArray _ -> raise (Unknown_eligibility "closure:array")
                | FIrrelevant -> raise (Unknown_eligibility "closure:irrelevant")
                | FLOCKED -> raise (Unknown_eligibility "closure:locked")
              in
              let rec check_stack = function
                | [] -> ()
                | frame :: rest ->
                  visit ();
                  (match frame with
                  | Zapp _ | Zproj _ | Zshift _ -> check_stack rest
                  | Zupdate target ->
                    if List.exists (fun previous -> previous == target)
                        !update_targets
                    then raise (Unknown_eligibility "stack:repeated-update");
                    update_targets := target :: !update_targets;
                    check_stack rest
                  | Zfix _ -> raise (Unknown_eligibility "stack:fix")
                  | ZcaseT _ -> raise (Unknown_eligibility "stack:case")
                  | Zprimitive _ -> raise (Unknown_eligibility "stack:primitive"))
              in
              let rec inspect_stack = function
                | [] -> ()
                | frame :: rest ->
                  visit ();
                  (match frame with
                  | Zapp arguments -> Array.iter inspect_closure arguments
                  | Zproj _ | Zshift _ | Zupdate _ -> ()
                  | Zfix _ -> raise (Unknown_eligibility "stack:fix")
                  | ZcaseT _ -> raise (Unknown_eligibility "stack:case")
                  | Zprimitive _ -> raise (Unknown_eligibility "stack:primitive"));
                  inspect_stack rest
              in
              (* Distinct update targets may name growing prefixes, but must
                 not alias any inspected subtree. Establish closedness and
                 this alias condition before seeking a dependency witness. *)
              check_stack stack;
              inspect_closure term;
              inspect_stack stack
              in
              let () = trace_flex "before bounded compact eligibility" in
              let eligible =
                try
                  backed := witness_after_complete_inspection inspect
                    (depends_on_registered_compact_peano_operation
                       ~fuel:dependency_fuel infos.cnv_inf);
                  if not !backed then trace_rejection "no-compact-witness";
                  !backed
                with
                | Unknown_eligibility reason -> trace_rejection reason; false
                | Assert_failure _ -> trace_rejection "assertion"; false
              in
              let () = trace_flex "after bounded compact eligibility" in
              eligible
            in
            let closed_applications () =
              (* Typeclass operations can remain behind primitive projections
                 until their closed application is reduced. Check the bounded
                 process eligibility before querying their result types. *)
              if not (compact_backed_closed_process t1 v1 &&
                      compact_backed_closed_process t2 v2)
              then false
              else
              let compact_wrapper_result =
                match
                  (let () = trace_flex "before left wrapper result type" in
                   let result =
                     flex_result_inductive infos infos.lft_tab lft1 v1 fl1
                   in
                   let () = trace_flex "after left wrapper result type" in
                   result),
                  (let () = trace_flex "before right wrapper result type" in
                   let result =
                     flex_result_inductive infos infos.rgt_tab lft2 v2 fl2
                   in
                   let () = trace_flex "after right wrapper result type" in
                   result)
                with
                | Some inductive1, Some inductive2
                  when Ind.UserOrd.equal inductive1 inductive2 ->
                  is_compact_peano_wrapper env inductive1
                | _ -> false
              in
              compact_wrapper_result
            in
            if not (Environ.typing_flags env).unfold_dep_heuristic then
              None
            else if same_reference then
              (** Congruence is the natural first strategy for two calls to
                  the same definition.  If an argument comparison fails, do
                  not weak-head normalize both complete applications here:
                  recursive functions can duplicate a large amount of work.
                  The regular delta path below can still unfold the common
                  reference when conversion genuinely requires it. *)
              None
            else if
              match fl1, fl2 with
              | ConstKey (constant1, _), ConstKey (constant2, _) ->
                not (is_registered_compact_peano_operation
                     infos.cnv_inf constant1 &&
                   is_registered_compact_peano_operation
                     infos.cnv_inf constant2) &&
                not (closed_applications ())
              | (ConstKey _ | VarKey _ | RelKey _), _ -> true
            then
              (** Full weak-head normalization is reserved for validated
                  compact Peano computations.  Applying it to arbitrary closed
                  programs can duplicate their complete evaluation. *)
              None
            else if
              compact_elimination1 || compact_elimination2
            then None
            else if
              match fl1, fl2 with
              | ConstKey (cst1, _), ConstKey (cst2, _) ->
                let fuel = ref 16_384 in
                (match Environ.constant_depends_on ~fuel env cst1 cst2,
                       Environ.constant_depends_on ~fuel env cst2 cst1 with
                | Some false, Some false -> false
                | _ -> true)
              | _ -> false
            then
              (* When one definition uses the other, or the bounded query is
                 inconclusive, retain ordinary delta conversion rather than
                 triggering full evaluation of both applications. *)
              None
            else
              let all =
                RedFlags.(red_add_transparent all
                  (red_transparent (info_flags infos.cnv_inf)))
              in
              let full_infos = infos_with_reds infos.cnv_inf all in
              let () = trace_flex "before left complete-application whd" in
              let appr1 = whd_stack full_infos infos.lft_tab t1 v1 in
              let () = trace_flex "after left complete-application whd" in
              let () = trace_flex "before right complete-application whd" in
              let appr2 = whd_stack full_infos infos.rgt_tab t2 v2 in
              let () = trace_flex "after right complete-application whd" in
              Some (eqwhnf cv_pb l2r infos
                (lft1, appr1) (lft2, appr2) cuniv)
          in
          let () = trace_flex "before complete-application reduction probe" in
          begin match reduce_applications_to_whnf () with
          | Some cuniv -> cuniv
          | None ->
          let () = trace_flex "after complete-application reduction probe" in
          (* Determine which constant to unfold first *)
          let unfolding_action =
            let env = info_env infos.cnv_inf in
            (* Preserve constructor-driven Fix and Case elimination, but
               expose a direct alias before evaluating the call it wraps.
               Same-head reflexivity above then avoids needless recursion.
               Inspect the original applications: compact arithmetic may
               already have consumed arguments in [r1] or [r2]. *)
            let constructor1 = constructor_eliminator_application
                infos fl1 (snd (snd appr1)) in
            let constructor2 = constructor_eliminator_application
                infos fl2 (snd (snd appr2)) in
            if constructor1 <> constructor2 then
              if constructor1 && direct_head_alias env fl2 fl1 then Unfold_right
              else if constructor2 && direct_head_alias env fl1 fl2 then Unfold_left
              else unfolding_side constructor1
            else
            let wrapper1 = projected_record_wrapper infos fl1 v1 in
            let wrapper2 = projected_record_wrapper infos fl2 v2 in
            if wrapper1 <> wrapper2 then unfolding_side wrapper1 else
            let order = Conv_oracle.oracle_compare oracle (to_er fl1) (to_er fl2) in
            let constructor_argument_preference () =
              if infos.cnv_constructor_relevance && not same_reference
              then None
              else
                let constructor1 =
                  has_constructor_argument infos.lft_tab v1
                in
                let () = trace_flex "after left constructor-argument probe" in
                let constructor2 =
                  has_constructor_argument infos.rgt_tab v2
                in
                let () = trace_flex "after right constructor-argument probe" in
                if constructor1 <> constructor2 then Some constructor1
                else if not constructor1 || not same_reference then None
                else
                let rec application_prefix arrays = function
                  | Zapp arguments :: stack ->
                    application_prefix (arguments :: arrays) stack
                  | (Zshift _ | Zupdate _) :: stack ->
                    application_prefix arrays stack
                  | _ -> Array.concat (List.rev arrays)
                in
                let arguments1 = application_prefix [] v1 in
                let arguments2 = application_prefix [] v2 in
                if not (Array.is_empty arguments1) &&
                   Int.equal (Array.length arguments1)
                     (Array.length arguments2)
                then
                  let symbolic_infos =
                    infos_with_reds infos.cnv_inf RedFlags.betazeta
                  in
                  let is_constructor tab argument =
                    let head, _ =
                      whd_stack symbolic_infos tab argument empty_stack
                    in
                    match fterm_of head with
                    | FConstruct _ | FPeanoNat _ -> true
                    | _ -> false
                  in
                  let rec rightmost_difference index =
                    if index < 0 then None
                    else
                      let left =
                        is_constructor infos.lft_tab arguments1.(index)
                      in
                      let right =
                        is_constructor infos.rgt_tab arguments2.(index)
                      in
                      if left <> right then Some left
                      else rightmost_difference (index - 1)
                  in
                  rightmost_difference (Array.length arguments1 - 1)
                else None
            in
            let global_constants =
              match fl1, fl2 with
              | ConstKey _, ConstKey _ -> true
              | _ -> false
            in
            let dependency_preference ~transitive () =
              if not infos.cnv_dependency_preference then None
              else match fl1, fl2 with
              | ConstKey (constant1, _), ConstKey (constant2, _) ->
                let () = trace_flex "before left indirect dependency" in
                let left = indirectly_depends_on ~transitive t1 v1 constant2 in
                let () = trace_flex "after left indirect dependency" in
                let () = trace_flex "before right indirect dependency" in
                let right = indirectly_depends_on ~transitive t2 v2 constant1 in
                let () = trace_flex "after right indirect dependency" in
                (match left, right with
                | Some left, Some right when not (Bool.equal left right) -> Some left
                (* When the reverse probe is unknown, require an actual
                   occurrence in the process. A transitive dependency through
                   an unrelated definition can otherwise divert conversion
                   into expensive arithmetic instead of the wrapper. *)
                | Some true, None when
                    indirectly_depends_on ~transitive:false t1 v1 constant2 = Some true ->
                  Some true
                | None, Some true when
                    indirectly_depends_on ~transitive:false t2 v2 constant1 = Some true ->
                  Some false
                | _ -> None)
              | (ConstKey _ | VarKey _ | RelKey _), _ -> None
            in
            choose_unfolding_action ~order ~l2r
              ~heuristic:(global_constants &&
                (Environ.typing_flags (info_env infos.cnv_inf)).unfold_dep_heuristic)
              ~compact1:compact_elimination1 ~compact2:compact_elimination2
              ~direct_dependency:(dependency_preference ~transitive:false)
              ~dependency:(dependency_preference ~transitive:true)
              ~constructor:constructor_argument_preference
          in
          match unfolding_action with
          | Unfold_left ->
            let appr1 = whd_stack ninfos infos.lft_tab t1 v1 in
            eqwhnf cv_pb l2r infos (lft1, appr1) appr2 cuniv
          | Unfold_right ->
            let appr2 = whd_stack ninfos infos.rgt_tab t2 v2 in
            eqwhnf cv_pb l2r infos appr1 (lft2, appr2) cuniv
          | Unfold_both ->
            (* Equal delta priorities: expose both definitions, as in Lean's
               lazy_delta_reduction_step. This performs a single delta step
               on each side, followed only by beta/iota/zeta reduction; it is
               not full normalization of the two applications. *)
            let appr1 = whd_stack ninfos infos.lft_tab t1 v1 in
            let appr2 = whd_stack ninfos infos.rgt_tab t2 v2 in
            eqwhnf cv_pb l2r infos (lft1, appr1) (lft2, appr2) cuniv
          end
          end
          | Some (t1, v1), None ->
          let all = RedFlags.(red_add_transparent all (red_transparent (info_flags infos.cnv_inf))) in
          let t1 = whd_stack (infos_with_reds infos.cnv_inf all) infos.lft_tab t1 v1 in
          eqwhnf cv_pb l2r infos (lft1, t1) appr2 cuniv
          | None, Some (t2, v2) ->
          let all = RedFlags.(red_add_transparent all (red_transparent (info_flags infos.cnv_inf))) in
          let t2 = whd_stack (infos_with_reds infos.cnv_inf all) infos.rgt_tab t2 v2 in
          eqwhnf cv_pb l2r infos appr1 (lft2, t2) cuniv
        )
      in
      remember_application infos cv_pb key;
      result

    | (FProj (p1, r1, c1), FConstruct (((ind2, 1), u2), args2))
      when infos.cnv_typ &&
           is_eta_record (info_env infos.cnv_inf) (ind2, u2) ->
      let () = assert_reduced_constructor v2 in
      begin match unfold_projection infos.cnv_inf p1 r1 with
      | Some s1 ->
        eqappr cv_pb l2r infos (lft1, (c1, s1 :: v1)) appr2 cuniv
      | None ->
        if is_registered_unit_like (info_env infos.cnv_inf) ind2 then
          (match checked_unit_equality () with
           | Some cu -> cu | None -> raise NotConvertible)
        else
          begin match
            try Some (eta_expand_ind_stack (info_env infos.cnv_inf) (ind2, u2)
              args2 (snd appr1))
            with Not_found -> None
          with
          | Some (v2, v1) ->
            convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
          | None -> raise NotConvertible
          end
      end

    | (FConstruct (((ind1, 1), u1), args1), FProj (p2, r2, c2))
      when infos.cnv_typ &&
           is_eta_record (info_env infos.cnv_inf) (ind1, u1) ->
      let () = assert_reduced_constructor v1 in
      begin match unfold_projection infos.cnv_inf p2 r2 with
      | Some s2 ->
        eqappr cv_pb l2r infos appr1 (lft2, (c2, s2 :: v2)) cuniv
      | None ->
        if is_registered_unit_like (info_env infos.cnv_inf) ind1 then
          (match checked_unit_equality () with
           | Some cu -> cu | None -> raise NotConvertible)
        else
          begin match
            try Some (eta_expand_ind_stack (info_env infos.cnv_inf) (ind1, u1)
              args1 (snd appr2))
            with Not_found -> None
          with
          | Some (v1, v2) ->
            convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
          | None -> raise NotConvertible
          end
      end

    | (FProj (p1,r1,c1), FProj (p2, r2, c2)) ->
      let same_projections =
        Projection.Repr.CanOrd.equal
          (Projection.repr p1) (Projection.repr p2) &&
        compare_stack_shape v1 v2
      in
      let congruence_first () =
        let env = CClosure.info_env infos.cnv_inf in
        let unit_like_projection =
          is_registered_unit_like env
            (Projection.Repr.inductive (Projection.repr p1))
        in
        let projection_of_constructor =
          match fterm_of c1, fterm_of c2 with
          | FConstruct _, _ | _, FConstruct _ -> true
          | _ -> false
        in
        if not infos.cnv_typ ||
           not (Environ.typing_flags env).unfold_dep_heuristic ||
           not (unit_like_projection ||
                (infos.cnv_projection_congruence &&
                 not projection_of_constructor)) ||
           not same_projections
        then None
        else
          try
            let el1 = el_stack lft1 v1 in
            let el2 = el_stack lft2 v2 in
            let relevances = info_relevances infos.cnv_inf in
            (** Several fields can project the same shared record value.  A
                first conversion may update that shared closure, so remember
                successful source comparisons for the duration of this
                well-typed conversion.  The lifts and local relevance context
                are part of the key; well-typed kernel conversion only checks
                the fixed universe graph and therefore has no constraints to
                replay on a cache hit. *)
            let cached =
              projection_conversion_cached infos.cnv_projection_conversions
                ~relevances ~rel_types:infos.cnv_rel_types
                ~rel_type_lifts:infos.cnv_rel_type_lifts el1 c1 el2 c2
            in
            let cuniv =
              if cached then cuniv
              else ccnv CONV l2r infos el1 el2 c1 c2 cuniv
            in
            let () =
              if not cached then
                remember_projection_conversion infos.cnv_projection_conversions {
                  projection_left_lift = el1;
                  projection_left_term = c1;
                  projection_right_lift = el2;
                  projection_right_term = c2;
                  projection_relevances = relevances;
                  projection_rel_types = infos.cnv_rel_types;
                  projection_rel_type_lifts = infos.cnv_rel_type_lifts;
                }
            in
            Some (convert_stacks l2r infos lft1 lft2 v1 v2 cuniv)
          with NotConvertible | NotConvertibleTrace _ -> None
      in
      let lazy_projection () =
        if (Environ.typing_flags (info_env infos.cnv_inf)).unfold_dep_heuristic &&
           same_projections && is_empty_stack v1 && is_empty_stack v2
        then
          lazy_projection_sources cv_pb l2r infos
            (el_stack lft1 v1) p1 r1 c1 (el_stack lft2 v2) p2 r2 c2 cuniv
        else None
      in
      begin match (match lazy_projection () with
        | Some _ as result -> result
        | None -> congruence_first ()) with
      | Some cuniv -> cuniv
      | None ->
      (* Projections normally unfold before first-order unification. *)
      match unfold_projection infos.cnv_inf p1 r1 with
      | Some s1 ->
        eqappr cv_pb l2r infos (lft1, (c1, (s1 :: v1))) appr2 cuniv
      | None ->
        match unfold_projection infos.cnv_inf p2 r2 with
        | Some s2 ->
          eqappr cv_pb l2r infos appr1 (lft2, (c2, (s2 :: v2))) cuniv
        | None ->
          if same_projections then
            let el1 = el_stack lft1 v1 in
            let el2 = el_stack lft2 v2 in
            let u1 = ccnv CONV l2r infos el1 el2 c1 c2 cuniv in
              convert_stacks l2r infos lft1 lft2 v1 v2 u1
          else (* Two projections in WHNF: unfold *)
            raise NotConvertible
      end

    | (FProj _, FFlex (ConstKey (c2, _) as fl2))
      when (match Conv_oracle.get_strategy
        (CClosure.oracle_of_infos infos.cnv_inf) (Conv_oracle.EvalConstRef c2) with
        | Conv_oracle.Expand -> true
        | Conv_oracle.Level _ | Conv_oracle.Opaque -> false) ->
      begin match unfold_ref_with_args infos.cnv_inf infos.rgt_tab fl2 v2 with
      | Some t2 -> eqappr cv_pb l2r infos appr1 (lft2, t2) cuniv
      | None -> raise NotConvertible
      end

    | (FFlex (ConstKey (c1, _) as fl1), FProj _)
      when (match Conv_oracle.get_strategy
        (CClosure.oracle_of_infos infos.cnv_inf) (Conv_oracle.EvalConstRef c1) with
        | Conv_oracle.Expand -> true
        | Conv_oracle.Level _ | Conv_oracle.Opaque -> false) ->
      begin match unfold_ref_with_args infos.cnv_inf infos.lft_tab fl1 v1 with
      | Some t1 -> eqappr cv_pb l2r infos (lft1, t1) appr2 cuniv
      | None -> raise NotConvertible
      end

    | (FProj (p1,r1,c1), t2) ->
      begin match unfold_projection infos.cnv_inf p1 r1 with
       | Some s1 ->
         eqappr cv_pb l2r infos (lft1, (c1, (s1 :: v1))) appr2 cuniv
       | None ->
         begin match t2 with
          | FFlex fl2 ->
            begin match unfold_ref_with_args infos.cnv_inf infos.rgt_tab fl2 v2 with
             | Some t2 ->
               eqappr cv_pb l2r infos appr1 (lft2, t2) cuniv
             | None -> raise NotConvertible
            end
          | _ -> raise NotConvertible
         end
      end

    | (t1, FProj (p2,r2,c2)) ->
      begin match unfold_projection infos.cnv_inf p2 r2 with
       | Some s2 ->
         eqappr cv_pb l2r infos appr1 (lft2, (c2, (s2 :: v2))) cuniv
       | None ->
         begin match t1 with
          | FFlex fl1 ->
            begin match unfold_ref_with_args infos.cnv_inf infos.lft_tab fl1 v1 with
             | Some t1 ->
               eqappr cv_pb l2r infos (lft1, t1) appr2 cuniv
             | None -> raise NotConvertible
            end
          | _ -> raise NotConvertible
         end
      end

    (* other constructors *)
    | (FLambda _, FLambda _) ->
        (* Inconsistency: we tolerate that v1, v2 contain shift and update but
           we throw them away *)
        if not (is_empty_stack v1 && is_empty_stack v2) then
          anomaly (Pp.str "conversion was given ill-typed terms (FLambda).");
        let (x1,ty1,bd1) = destFLambda mk_clos hd1 in
        let (_,ty2,bd2) = destFLambda mk_clos hd2 in
        let el1 = el_stack lft1 v1 in
        let el2 = el_stack lft2 v2 in
        let cuniv = ccnv CONV l2r infos el1 el2 ty1 ty2 cuniv in
        ccnv CONV l2r (push_relevance ~typ:(Some ty1) ~type_lift:el1 infos x1)
          (el_lift el1) (el_lift el2) bd1 bd2 cuniv

    | (FProd (x1, c1, c2, e), FProd (_, c'1, c'2, e')) ->
        if not (is_empty_stack v1 && is_empty_stack v2) then
          (* May happen because we convert application right to left *)
          raise NotConvertible;
        (* Luo's system *)
        let el1 = el_stack lft1 v1 in
        let el2 = el_stack lft2 v2 in
        let cuniv = ccnv CONV l2r infos el1 el2 c1 c'1 cuniv in
        let x1 = usubst_binder e x1 in
        ccnv cv_pb l2r (push_relevance ~typ:(Some c1) ~type_lift:el1 infos x1)
          (el_lift el1) (el_lift el2)
          (mk_clos (usubs_lift e) c2) (mk_clos (usubs_lift e') c'2) cuniv

    (* Eta-expansion on the fly *)
    | (FLambda _, _) ->
        let () = match v1 with
        | [] -> ()
        | _ ->
          anomaly (Pp.str ("conversion was given unreduced term (FLambda left; stack=" ^
            diagnostic_stack_tag v1 ^ ")."))
        in
        let (x1,ty1,bd1) = destFLambda mk_clos hd1 in
        let infos = push_relevance ~typ:(Some ty1) ~type_lift:lft1 infos x1 in
        eqappr CONV l2r infos
          (el_lift lft1, (bd1, [])) (el_lift lft2, (hd2, eta_expand_stack infos.cnv_inf x1 v2)) cuniv
    | (_, FLambda _) ->
        let () = match v2 with
        | [] -> ()
        | _ ->
          anomaly (Pp.str ("conversion was given unreduced term (FLambda right; stack=" ^
            diagnostic_stack_tag v2 ^ ")."))
        in
        let (x2,ty2,bd2) = destFLambda mk_clos hd2 in
        let infos = push_relevance ~typ:(Some ty2) ~type_lift:lft2 infos x2 in
        eqappr CONV l2r infos
          (el_lift lft1, (hd1, eta_expand_stack infos.cnv_inf x2 v1)) (el_lift lft2, (bd2, [])) cuniv

    | FCaseInvert _, FRel _ | FRel _, FCaseInvert _ ->
      (match checked_unit_equality () with
       | Some cu -> cu | None -> raise NotConvertible)

    (* only one constant, defined var or defined rel *)
    | (FFlex fl1, c2)      ->
      let unit_comparison = if
        match c2 with
        | FRel rel ->
          has_type_elimination_stack v1 || has_type_elimination_stack v2 ||
          same_unit_like_flex_rel infos infos.lft_tab lft1 v1 fl1
            infos.rgt_tab lft2 v2 rel
        | FCaseInvert _ -> true
        | _ -> false
      then checked_unit_equality () else None in
      begin match unit_comparison with
      | Some cu -> cu
      | None ->
      let eta_before_unfolding () =
        match c2 with
        | FConstruct (((ind2, 1), u2), args2)
          when not (record_wrapper infos fl1 v1) ->
          let () = assert_reduced_constructor v2 in
          if not (flex_has_inductive infos infos.lft_tab lft1 v1 fl1 ind2)
          then None
          else if is_registered_unit_like (info_env infos.cnv_inf) ind2 &&
             (infos.cnv_typ ||
              flex_has_unit_like infos infos.lft_tab lft1 v1 fl1 ind2)
          then checked_unit_equality ()
          else
            (try
               let v2, v1 =
                 eta_expand_ind_stack (info_env infos.cnv_inf) (ind2, u2)
                   args2 (snd appr1)
               in
               Some (convert_stacks l2r infos lft1 lft2 v1 v2 cuniv)
             with Not_found | NotConvertible | NotConvertibleTrace _ -> None)
        | _ -> None
      in
      begin match eta_before_unfolding () with
      | Some cuniv -> cuniv
      | None ->
        match unfold_ref_with_args infos.cnv_inf infos.lft_tab fl1 v1 with
        | Some (def1,v1) ->
          (** By virtue of the previous case analyses, we know [c2] is rigid.
              Conversion check to rigid terms eventually implies full weak-head
              reduction, so instead of repeatedly performing small-step
              unfoldings, we perform reduction with all flags on. *)
            let all = RedFlags.(red_add_transparent all (red_transparent (info_flags infos.cnv_inf))) in
            let r1 = whd_stack (infos_with_reds infos.cnv_inf all) infos.lft_tab def1 v1 in
            eqwhnf cv_pb l2r infos (lft1, r1) appr2 cuniv
        | None ->
          (* The early eta probe is incomplete for stuck eliminations.
             Preserve ordinary record eta when no unfolding is possible. *)
          (match c2 with
           | FConstruct (((ind2, 1), u2), args2) ->
             let () = assert_reduced_constructor v2 in
             if is_registered_unit_like (info_env infos.cnv_inf) ind2 then
               (match checked_unit_equality () with
                | Some cu -> cu | None -> raise NotConvertible)
             else
             (try
                let v2, v1 =
                  eta_expand_ind_stack (info_env infos.cnv_inf)
                    (ind2, u2) args2 (snd appr1)
                in
                convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
              with Not_found -> raise NotConvertible)
           | _ -> raise NotConvertible)
      end
      end

    | (c1, FFlex fl2)      ->
      let unit_comparison = if
        match c1 with
        | FRel rel ->
          has_type_elimination_stack v1 || has_type_elimination_stack v2 ||
          same_unit_like_flex_rel infos infos.rgt_tab lft2 v2 fl2
            infos.lft_tab lft1 v1 rel
        | FCaseInvert _ -> true
        | _ -> false
      then checked_unit_equality () else None in
      begin match unit_comparison with
      | Some cu -> cu
      | None ->
       let eta_before_unfolding () =
         match c1 with
         | FConstruct (((ind1, 1), u1), args1)
           when not (record_wrapper infos fl2 v2) ->
           let () = assert_reduced_constructor v1 in
           if not (flex_has_inductive infos infos.rgt_tab lft2 v2 fl2 ind1)
           then None
           else if is_registered_unit_like (info_env infos.cnv_inf) ind1 &&
              (infos.cnv_typ ||
               flex_has_unit_like infos infos.rgt_tab lft2 v2 fl2 ind1)
           then checked_unit_equality ()
           else
             (try
                let v1, v2 =
                  eta_expand_ind_stack (info_env infos.cnv_inf) (ind1, u1)
                    args1 (snd appr2)
                in
                Some (convert_stacks l2r infos lft1 lft2 v1 v2 cuniv)
              with Not_found | NotConvertible | NotConvertibleTrace _ -> None)
         | _ -> None
       in
       begin match eta_before_unfolding () with
       | Some cuniv -> cuniv
       | None ->
         match unfold_ref_with_args infos.cnv_inf infos.rgt_tab fl2 v2 with
        | Some (def2, v2) ->
          (** Symmetrical case of above. *)
          let all = RedFlags.(red_add_transparent all (red_transparent (info_flags infos.cnv_inf))) in
          let r2 = whd_stack (infos_with_reds infos.cnv_inf all) infos.rgt_tab def2 v2 in
          eqwhnf cv_pb l2r infos appr1 (lft2, r2) cuniv
        | None ->
          (* Symmetric record-eta fallback, as above. *)
          match c1 with
           | FConstruct (((ind1, 1), u1), args1) ->
             let () = assert_reduced_constructor v1 in
             if is_registered_unit_like (info_env infos.cnv_inf) ind1 then
               (match checked_unit_equality () with
                | Some cu -> cu | None -> raise NotConvertible)
             else
            (try
               let v1, v2 =
                 eta_expand_ind_stack (info_env infos.cnv_inf)
                   (ind1, u1) args1 (snd appr2)
               in
               convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
             with Not_found -> raise NotConvertible)
          | _ -> raise NotConvertible
       end
       end

    (* Inductive types:  MutInd MutConstruct Fix Cofix *)
    | (FInd (ind1,u1 as pind1), FInd (ind2,u2 as pind2)) ->
      if Ind.CanOrd.equal ind1 ind2 then
        if UVars.Instance.is_empty u1 || UVars.Instance.is_empty u2 then
          let cuniv = fail_check infos @@ convert_instances ~flex:false u1 u2 cuniv in
          convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
        else
          let mind = Environ.lookup_mind (fst ind1) (info_env infos.cnv_inf) in
          let nargs = same_args_size v1 v2 in
          match fail_check infos @@ convert_inductives cv_pb (mind, snd ind1) nargs u1 u2 cuniv with
          | cuniv -> convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
          | exception MustExpand ->
            let env = info_env infos.cnv_inf in
            let hd1 = eta_expand_ind env pind1 in
            let hd2 = eta_expand_ind env pind2 in
            eqappr cv_pb l2r infos (lft1,(hd1,v1)) (lft2,(hd2,v2)) cuniv
      else raise NotConvertible

    | FPeanoNat n1, FPeanoNat n2 ->
       if Ind.UserOrd.equal n1.peano_ind n2.peano_ind &&
          CClosure.PeanoNatValue.equal n1.peano_value n2.peano_value
       then convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
       else raise NotConvertible

    | FPeanoNat n1, _ ->
       eqwhnf cv_pb l2r infos
         (lft1, (CClosure.peano_constructor_view n1, v1)) appr2 cuniv

    | _, FPeanoNat n2 ->
       eqwhnf cv_pb l2r infos
         appr1 (lft2, (CClosure.peano_constructor_view n2, v2)) cuniv

    | (FConstruct (((ind1,j1),u1 as pctor1,args1)), FConstruct (((ind2,j2),u2 as pctor2),args2)) ->
      let () = assert_reduced_constructor v1 in
      let () = assert_reduced_constructor v2 in
      let nargs = Array.length args1 in
      let () = if not @@ Int.equal nargs (Array.length args2) then raise NotConvertible in
      let v1 = append_stack args1 v1 in
      let v2 = append_stack args2 v2 in
      if Int.equal j1 j2 && Ind.CanOrd.equal ind1 ind2 then
        let mask =
          if infos.cnv_typ && infos.cnv_constructor_relevance
          then constructor_relevance_mask infos pctor1
          else [||]
        in
        if UVars.Instance.is_empty u1 || UVars.Instance.is_empty u2 then
          let cuniv = fail_check infos @@ convert_instances ~flex:false u1 u2 cuniv in
          convert_stacks ~mask l2r infos lft1 lft2 v1 v2 cuniv
        else
          let mind = Environ.lookup_mind (fst ind1) (info_env infos.cnv_inf) in
          match fail_check infos @@ convert_constructors (mind, snd ind1, j1) nargs u1 u2 cuniv with
          | cuniv -> convert_stacks ~mask l2r infos lft1 lft2 v1 v2 cuniv
          | exception MustExpand ->
            let env = info_env infos.cnv_inf in
            let hd1 = eta_expand_constructor env pctor1 in
            let hd2 = eta_expand_constructor env pctor2 in
            eqappr cv_pb l2r infos (lft1,(hd1,v1)) (lft2,(hd2,v2)) cuniv
      else raise NotConvertible

    (* Eta expansion of records *)
    | (FConstruct (((ind1, j1), u1), args1), _) ->
      let () = assert_reduced_constructor v1 in
      (* records only have 1 constructor *)
      let () = if not @@ Int.equal j1 1 then raise NotConvertible in
      (* The generic API also reaches locally bound stuck cases. A failed
         family-only hint must not prevent checking their full result types. *)
      if is_registered_unit_like (info_env infos.cnv_inf) ind1 &&
         (infos.cnv_typ ||
          has_type_elimination_stack v2 ||
          (match fterm_of hd2 with FCaseInvert _ -> true | _ -> false) ||
          rel_has_unit_like infos infos.rgt_tab lft2 (hd2, v2) ind1)
      then (match checked_unit_equality () with
        | Some cu -> cu | None -> raise NotConvertible)
      else (try
         let v1, v2 =
            eta_expand_ind_stack (info_env infos.cnv_inf) (ind1,u1) args1 (snd appr2)
         in
         convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
       with Not_found -> raise NotConvertible)

    | (_, FConstruct (((ind2, j2), u2), args2)) ->
      let () = assert_reduced_constructor v2 in
      (* records only have 1 constructor *)
      let () = if not @@ Int.equal j2 1 then raise NotConvertible in
      if is_registered_unit_like (info_env infos.cnv_inf) ind2 &&
         (infos.cnv_typ ||
          has_type_elimination_stack v1 ||
          (match fterm_of hd1 with FCaseInvert _ -> true | _ -> false) ||
          rel_has_unit_like infos infos.lft_tab lft1 (hd1, v1) ind2)
      then (match checked_unit_equality () with
        | Some cu -> cu | None -> raise NotConvertible)
      else (try
         let v2, v1 =
            eta_expand_ind_stack (info_env infos.cnv_inf) (ind2,u2) args2 (snd appr1)
         in
         convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
       with Not_found -> raise NotConvertible)

    | (FFix (((op1, i1),(na1,tys1,cl1)),e1), FFix(((op2, i2),(_,tys2,cl2)),e2)) ->
        if Int.equal i1 i2 && Array.equal Int.equal op1 op2
        then
          let n = Array.length cl1 in
          let fty1 = Array.map (mk_clos e1) tys1 in
          let fty2 = Array.map (mk_clos e2) tys2 in
          let fcl1 = Array.map (mk_clos (usubs_liftn n e1)) cl1 in
          let fcl2 = Array.map (mk_clos (usubs_liftn n e2)) cl2 in
          let el1 = el_stack lft1 v1 in
          let el2 = el_stack lft2 v2 in
          let cuniv = convert_vect l2r infos el1 el2 fty1 fty2 cuniv in
          let cuniv =
            let na1 = Array.map (usubst_binder e1) na1 in
            let infos = push_relevances infos na1 in
            convert_vect l2r infos
                         (el_liftn n el1) (el_liftn n el2) fcl1 fcl2 cuniv
          in
          convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
        else raise NotConvertible

    | (FCoFix ((op1,(na1,tys1,cl1)),e1), FCoFix((op2,(_,tys2,cl2)),e2)) ->
        if Int.equal op1 op2
        then
          let n = Array.length cl1 in
          let fty1 = Array.map (mk_clos e1) tys1 in
          let fty2 = Array.map (mk_clos e2) tys2 in
          let fcl1 = Array.map (mk_clos (usubs_liftn n e1)) cl1 in
          let fcl2 = Array.map (mk_clos (usubs_liftn n e2)) cl2 in
          let el1 = el_stack lft1 v1 in
          let el2 = el_stack lft2 v2 in
          let cuniv = convert_vect l2r infos el1 el2 fty1 fty2 cuniv in
          let cuniv =
            let na1 = Array.map (usubst_binder e1) na1 in
            let infos = push_relevances infos na1 in
            convert_vect l2r infos
                         (el_liftn n el1) (el_liftn n el2) fcl1 fcl2 cuniv
          in
          convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
        else raise NotConvertible

    | FInt i1, FInt i2 ->
       if Uint63.equal i1 i2 then convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
       else raise NotConvertible

    | FFloat f1, FFloat f2 ->
        if Float64.equal f1 f2 then convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
        else raise NotConvertible

    | FString s1, FString s2 ->
        if Pstring.equal s1 s2 then convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
        else raise NotConvertible

    | FCaseInvert (ci1,u1,pms1,p1,iv1,_,br1,e1), FCaseInvert (ci2,u2,pms2,p2,iv2,_,br2,e2) ->
      (if not (Ind.CanOrd.equal ci1.ci_ind ci2.ci_ind) then raise NotConvertible);
      let el1 = el_stack lft1 v1 and el2 = el_stack lft2 v2 in
      let fold c1 c2 cuniv = ccnv CONV l2r infos el1 el2 c1 c2 cuniv in
      (** FIXME: cache the presence of let-bindings in the case_info *)
      let mind = Environ.lookup_mind (fst ci1.ci_ind) (info_env infos.cnv_inf) in
      let mip = mind.Declarations.mind_packets.(snd ci1.ci_ind) in
      let cuniv =
        let ind = (mind,snd ci1.ci_ind) in
        let nargs = inductive_cumulativity_arguments ind in
        let u1 = CClosure.usubst_instance e1 u1 in
        let u2 = CClosure.usubst_instance e2 u2 in
        fail_check infos @@ convert_inductives CONV ind nargs u1 u2 cuniv
      in
      let pms1 = mk_clos_vect e1 pms1 in
      let pms2 = mk_clos_vect e2 pms2 in
      let cuniv = Array.fold_right2 fold pms1 pms2 cuniv in
      let cuniv = Array.fold_right2 fold (get_invert iv1) (get_invert iv2) cuniv in
      let cuniv = convert_return_clause mind mip l2r infos e1 e2 el1 el2 u1 u2 pms1 pms2 p1 p2 cuniv in
      (* not clear if we need to pass both u1 and u2 as
         convert_inductives should have enforced that they are
         equivalent when used to instantiate this inductive's
         components, but we may as well *)
      let cuniv = convert_branches mind mip l2r infos e1 e2 el1 el2 u1 u2 pms1 pms2 br1 br2 cuniv in
      convert_stacks l2r infos lft1 lft2 v1 v2 cuniv

    | FArray (u1,t1,ty1), FArray (u2,t2,ty2) ->
      let len = Parray.length_int t1 in
      if not (Int.equal len (Parray.length_int t2)) then raise NotConvertible;
      let cuniv = fail_check infos @@ convert_instances_cumul CONV [|UVars.Variance.Irrelevant|] u1 u2 cuniv in
      let el1 = el_stack lft1 v1 in
      let el2 = el_stack lft2 v2 in
      let cuniv = ccnv CONV l2r infos el1 el2 ty1 ty2 cuniv in
      let cuniv = Parray.fold_left2 (fun u v1 v2 -> ccnv CONV l2r infos el1 el2 v1 v2 u) cuniv t1 t2 in
      convert_stacks l2r infos lft1 lft2 v1 v2 cuniv

    | (FRel n1, FIrrelevant) ->
      let n1 = reloc_rel n1 (el_stack lft1 v1) in
      let r1 = Range.get (info_relevances infos.cnv_inf) (n1 - 1) in
      if is_irrelevant infos.cnv_inf r1 then
        let v1 = CClosure.skip_irrelevant_stack infos.cnv_inf v1 in
        convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
      else raise NotConvertible

    | (FIrrelevant, FRel n2) ->
      let n2 = reloc_rel n2 (el_stack lft2 v2) in
      let r2 = Range.get (info_relevances infos.cnv_inf) (n2 - 1) in
      if is_irrelevant infos.cnv_inf r2 then
        let v2 = CClosure.skip_irrelevant_stack infos.cnv_inf v2 in
        convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
      else raise NotConvertible

    | FIrrelevant, FIrrelevant ->
      convert_stacks l2r infos lft1 lft2 v1 v2 cuniv

     (* Should not happen because both (hd1,v1) and (hd2,v2) are in whnf *)
     | ( (FLetIn _, _) | (FCaseT _,_) | (FApp _,_) | (FCLOS _,_) | (FLIFT _,_)
       | (_, FLetIn _) | (_,FCaseT _) | (_,FApp _) | (_,FCLOS _) | (_,FLIFT _)
       | (FLOCKED,_) | (_,FLOCKED) ) -> assert false

     | (FRel _ | FAtom _ | FInd _ | FFix _ | FCoFix _ | FCaseInvert _
       | FProd _ | FEvar _ | FInt _ | FFloat _ | FString _
       | FArray _ | FIrrelevant), _ -> raise NotConvertible

and convert_stacks ?(mask = [||]) ?(constructor_first = false)
    ?(projection_prefix_first = false)
    l2r infos lft1 lft2 stk1 stk2 cuniv =
  let f (l1, t1) (l2, t2) cuniv = ccnv CONV l2r infos l1 l2 t1 t2 cuniv in
  let relevant nargs i =
    nargs < 0 || nargs + i >= Array.length mask || mask.(nargs + i)
  in
  let fold_arguments selected nargs a1 a2 cuniv =
    let rec loop i cu =
      if i < 0 then cu
      else
        let cu =
          if relevant nargs i && selected i then f a1.(i) a2.(i) cu
          else cu
        in
        loop (i - 1) cu
    in
    loop (Array.length a1 - 1) cuniv
  in
  let rec cmp_rec compared nargs pstk1 pstk2 cuniv =
    match (pstk1,pstk2) with
      | (z1::s1, z2::s2) ->
          (* Stacks are known to have the same argument size *)
          let rnargs = match z1 with
          | Zlapp a -> if nargs < 0 then -1 else nargs + Array.length a
          | Zlproj _ | Zlfix _ | Zlcase _ | Zlprimitive _ -> -1
          in
          let cu1 = cmp_rec [||] rnargs s1 s2 cuniv in
          (match (z1,z2) with
            | (Zlapp a1,Zlapp a2) ->
              fold_arguments
                (fun i -> Array.is_empty compared || not compared.(i))
                nargs a1 a2 cu1
            | (Zlproj (c1,_l1),Zlproj (c2,_l2)) ->
              if not (Projection.Repr.CanOrd.equal c1 c2) then
                raise NotConvertible
              else cu1
            | (Zlfix(fx1,a1),Zlfix(fx2,a2)) ->
                let cu2 = f fx1 fx2 cu1 in
                cmp_rec [||] (-1) a1 a2 cu2
            | (Zlcase(ci1,l1,u1,pms1,p1,br1,e1),Zlcase(ci2,l2,u2,pms2,p2,br2,e2)) ->
                if not (Ind.CanOrd.equal ci1.ci_ind ci2.ci_ind) then
                  raise NotConvertible;
                let cu = cu1 in
                (** FIXME: cache the presence of let-bindings in the case_info *)
                let mind = Environ.lookup_mind (fst ci1.ci_ind) (info_env infos.cnv_inf) in
                let mip = mind.Declarations.mind_packets.(snd ci1.ci_ind) in
                let cu =
                  if UVars.Instance.is_empty u1 || UVars.Instance.is_empty u2 then
                    convert_instances ~flex:false u1 u2 cu
                  else
                    let u1 = CClosure.usubst_instance e1 u1 in
                    let u2 = CClosure.usubst_instance e2 u2 in
                    match mind.Declarations.mind_variance with
                    | None -> convert_instances ~flex:false u1 u2 cu
                    | Some variances -> convert_instances_cumul CONV variances u1 u2 cu
                in
                let cu = fail_check infos cu in
                let pms1 = mk_clos_vect e1 pms1 in
                let pms2 = mk_clos_vect e2 pms2 in
                let fold_params c1 c2 accu = f (l1, c1) (l2, c2) accu in
                let cu = Array.fold_right2 fold_params pms1 pms2 cu in
                let cu = convert_return_clause mind mip l2r infos e1 e2 l1 l2 u1 u2 pms1 pms2 p1 p2 cu in
                convert_branches mind mip l2r infos e1 e2 l1 l2 u1 u2 pms1 pms2 br1 br2 cu
            | (Zlprimitive(op1,_,rargs1,kargs1),Zlprimitive(op2,_,rargs2,kargs2)) ->
              if not (CPrimitives.equal op1 op2) then raise NotConvertible else
                let cu2 = List.fold_right2 f rargs1 rargs2 cu1 in
                let fk (_,a1) (_,a2) cu = f a1 a2 cu in
                List.fold_right2 fk kargs1 kargs2 cu2
            | ((Zlapp _ | Zlproj _ | Zlfix _| Zlcase _| Zlprimitive _), _) -> assert false)
      | _ -> cuniv in
  (* A mismatch in any projected field rejects this congruence shortcut
     before inspecting source arguments, including constructors prioritized
     below. Otherwise prefix-first order could normalize a large discarded
     source argument before discovering a different outer field. *)
  let same_shape = compare_stack_shape
      ~check_projections:projection_prefix_first stk1 stk2 in
  if same_shape then
    let nargs = if Array.is_empty mask then -1 else 0 in
    let stack1 = pure_stack lft1 stk1 in
    let stack2 = pure_stack lft2 stk2 in
    let compared, cuniv = match stack1, stack2 with
    | Zlapp a1 :: _, Zlapp a2 :: _ when constructor_first ->
      (* Probe only the constant's direct arguments, before arguments after
         projections or other eliminations. A constructor/nonconstructor
         mismatch can reject congruence without comparing large step functions
         or accumulators; the ordinary unfolding fallback then applies. *)
      let symbolic_infos = infos_with_reds infos.cnv_inf RedFlags.betazeta in
      let constructor tab (_, term) =
        let head, _ = whd_stack symbolic_infos tab term empty_stack in
        match fterm_of head with FConstruct _ | FPeanoNat _ -> true | _ -> false
      in
      let priority = Array.init (Array.length a1) (fun i ->
        relevant nargs i &&
        constructor infos.lft_tab a1.(i) <> constructor infos.rgt_tab a2.(i))
      in
      priority, fold_arguments (fun i -> priority.(i)) nargs a1 a2 cuniv
    | _ -> [||], cuniv
    in
    if projection_prefix_first then
      compare_projection_segments cmp_rec compared nargs stack1 stack2 cuniv
    else cmp_rec compared nargs stack1 stack2 cuniv
  else raise NotConvertible

and convert_vect l2r infos lft1 lft2 v1 v2 cuniv =
  let lv1 = Array.length v1 in
  let lv2 = Array.length v2 in
  if Int.equal lv1 lv2
  then
    let rec fold n cuniv =
      if n >= lv1 then cuniv
      else
        let cuniv = ccnv CONV l2r infos lft1 lft2 v1.(n) v2.(n) cuniv in
        fold (n+1) cuniv in
    fold 0 cuniv
  else raise NotConvertible

and convert_under_context l2r infos e1 e2 lft1 lft2 ctx (nas1, c1) (nas2, c2) cu =
  let n = Array.length nas1 in
  let () = assert (Int.equal n (Array.length nas2)) in
  let n, e1, e2 = match ctx with
  | None -> (* nolet *)
    let e1 = usubs_liftn n e1 in
    let e2 = usubs_liftn n e2 in
    (n, e1, e2)
  | Some (ctx, args1, args2) ->
    let n1, e1 = esubst_of_context ctx args1 e1 in
    let n2, e2 = esubst_of_context ctx args2 e2 in
    let () = assert (Int.equal n1 n2) in
    n1, e1, e2
  in
  let lft1 = el_liftn n lft1 in
  let lft2 = el_liftn n lft2 in
  let infos = push_relevances infos (Array.map (usubst_binder e1) nas1) in
  ccnv CONV l2r infos lft1 lft2 (mk_clos e1 c1) (mk_clos e2 c2) cu

and convert_return_clause mib mip l2r infos e1 e2 l1 l2 u1 u2 pms1 pms2 p1 p2 cu =
  let ctx =
    if Int.equal mip.mind_nrealargs mip.mind_nrealdecls then None
    else
      let ctx, _ = List.chop mip.mind_nrealdecls mip.mind_arity_ctxt in
      let pms1 = inductive_subst mib u1 pms1 in
      let pms2 = inductive_subst mib u2 pms2 in
      let open Context.Rel.Declaration in
      (* Add the inductive binder *)
      let ctx = None :: List.map get_value ctx in
      Some (ctx, pms1, pms2)
  in
  convert_under_context l2r infos e1 e2 l1 l2 ctx (fst p1) (fst p2) cu

and convert_branches mib mip l2r infos e1 e2 lft1 lft2 u1 u2 pms1 pms2 br1 br2 cuniv =
  let fold i (ctx, _) cuniv =
    let ctx =
      if Int.equal mip.mind_consnrealdecls.(i) mip.mind_consnrealargs.(i) then None
      else
        let ctx, _ = List.chop mip.mind_consnrealdecls.(i) ctx in
        let ctx = List.map Context.Rel.Declaration.get_value ctx in
        let pms1 = inductive_subst mib u1 pms1 in
        let pms2 = inductive_subst mib u2 pms2 in
        Some (ctx, pms1, pms2)
    in
    let c1 = br1.(i) in
    let c2 = br2.(i) in
    convert_under_context l2r infos e1 e2 lft1 lft2 ctx c1 c2 cuniv
  in
  Array.fold_right_i fold mip.mind_nf_lc cuniv

and convert_list l2r infos lft1 lft2 v1 v2 cuniv = match v1, v2 with
| [], [] -> cuniv
| c1 :: v1, c2 :: v2 ->
  let cuniv = ccnv CONV l2r infos lft1 lft2 c1 c2 cuniv in
  convert_list l2r infos lft1 lft2 v1 v2 cuniv
| _, _ -> raise NotConvertible

let clos_gen_conv (type err) ?work_limit ~typed ~constructor_relevance
    ~projection_congruence ~dependency_preference trans cv_pb l2r evars env
    graph univs t1 t2 =
  NewProfile.profile "Conversion" begin fun () ->
      incr diagnostic_conversion_calls;
      let diagnostic_call = !diagnostic_conversion_calls in
      let () =
        if Option.has_some (Sys.getenv_opt "ROCQ_DIAGNOSTIC_CONVERSION_ENTRIES")
        then
          let gc = Gc.quick_stat () in
          Printf.eprintf "[conversion entry] %d cpu=%.3f major=%d typed=%b relevance=%b projection=%b dependency=%b %s <> %s\n%!"
            diagnostic_call (Sys.time ()) gc.Gc.major_collections
            typed constructor_relevance projection_congruence dependency_preference
            (diagnostic_constr_head t1) (diagnostic_constr_head t2)
      in
      let () =
        match Sys.getenv_opt "ROCQ_DIAGNOSTIC_CONVERSION_CALL" with
        | Some call when Int.equal diagnostic_call (int_of_string call) ->
          let rec describe_shallow depth term =
            if depth <= 0 then "..."
            else match Constr.kind term with
            | Const (constant, _) -> Constant.to_string constant
            | Rel index -> Printf.sprintf "rel(%d)" index
            | App (function_, arguments) ->
              Printf.sprintf "app(%s,%d)"
                (describe_shallow (depth - 1) function_)
                (Array.length arguments)
            | Proj (projection, _, source) ->
              let inductive = Projection.inductive projection in
              Printf.sprintf "projection(%s[%d],%s)"
                (MutInd.to_string (fst inductive)) (Projection.arg projection)
                (describe_shallow (depth - 1) source)
            | Lambda _ -> "lambda" | Prod _ -> "product" | LetIn _ -> "let"
            | Case _ -> "case" | Fix _ -> "fix" | CoFix _ -> "cofix"
            | Construct _ -> "constructor" | Ind _ -> "inductive"
            | Var id -> Id.to_string id | Sort _ -> "sort" | Evar _ -> "evar"
            | Meta _ -> "meta" | Cast _ -> "cast" | Int _ -> "int"
            | Float _ -> "float" | String _ -> "string" | Array _ -> "array"
          in
          let projection_view term =
            let head, arguments = Constr.decompose_app term in
            match Constr.kind head with
            | Proj (projection, _, _source) ->
              Some (projection, _source, arguments)
            | _ -> None
          in
          begin match projection_view t1, projection_view t2 with
          | Some (projection1, source1, arguments1),
            Some (projection2, source2, arguments2) ->
            let argument_descriptions =
              Array.to_list
                (Array.mapi (fun index argument1 ->
                   let argument2 = arguments2.(index) in
                   Printf.sprintf
                     "arg %d: physical=%b; %s <> %s"
                     index (argument1 == argument2)
                     (describe_shallow 4 argument1)
                     (describe_shallow 4 argument2)) arguments1)
              |> String.concat "\n"
            in
            let inductive1 = Projection.inductive projection1 in
            let inductive2 = Projection.inductive projection2 in
            CErrors.user_err
              Pp.(str (Printf.sprintf "Conversion call %d" diagnostic_call)
                  ++ fnl () ++ str
                    (Printf.sprintf "Left projection: %s[%d]"
                      (MutInd.to_string (fst inductive1))
                      (Projection.arg projection1))
                  ++ fnl () ++ str
                    (Printf.sprintf "Right projection: %s[%d]"
                      (MutInd.to_string (fst inductive2))
                      (Projection.arg projection2))
                  ++ fnl () ++ str
                    (Printf.sprintf "Sources: physical=%b; %s <> %s"
                      (source1 == source2) (describe_shallow 4 source1)
                      (describe_shallow 4 source2))
                  ++ fnl () ++ str argument_descriptions)
          | _ ->
            CErrors.user_err
              Pp.(str (Printf.sprintf "Conversion call %d: %s <> %s"
                   diagnostic_call (diagnostic_constr_head t1)
                   (diagnostic_constr_head t2)))
          end
        | Some _ | None -> ()
      in
      let reds = RedFlags.red_add_transparent RedFlags.betaiotazeta trans in
      let infos = create_conv_infos ~univs:graph ~evars reds env in
      let work = Option.map ref work_limit in
      let infos = infos_with_conversion_work infos work in
      let module Error = struct type payload += Error of err end in
      let box e = Error.Error e in
      let infos = {
        cnv_inf = infos;
        cnv_typ = typed;
        cnv_rel_types = Range.empty;
        cnv_rel_type_lifts = Range.empty;
        cnv_probe_budget = None;
        cnv_strategy_budget = work;
        cnv_symbolic_budget = None;
        (* A strategy already bounded as a whole shares that allowance with
           symbolic recovery. Only the unbounded ordinary path needs a
           separate aggregate allowance for optional recovery. *)
        cnv_symbolic_remaining = ref (Option.default 16_384 work_limit);
        cnv_failed_symbolic = make_projection_conversion_cache ();
        cnv_projection_conversions = make_projection_conversion_cache ();
        cnv_successful_conversions =
          make_successful_conversion_cache (successful_conversion_limit ());
        cnv_memoize_successful_conversions =
          typed &&
          (Environ.typing_flags env).unfold_dep_heuristic &&
          (match Sys.getenv_opt
                   "ROCQ_DIAGNOSTIC_MEMOIZE_CONVERSION_CALL" with
           | None -> true
           | Some call -> Int.equal diagnostic_call (int_of_string call));
        cnv_projection_congruence = projection_congruence;
        cnv_dependency_preference = dependency_preference;
        cnv_constructor_relevance = constructor_relevance;
        cnv_constructor_masks = ConstructorMasks.create 17;
        cnv_failed_congruences = make_failed_congruence_cache ();
        cnv_successful_applications = make_successful_application_cache ();
        lft_tab = create_tab ();
        rgt_tab = create_tab ();
        err_ret = box;
      } in
      let trace_this_call =
        match Sys.getenv_opt "ROCQ_DIAGNOSTIC_CONVERSION_TRACE_CALL",
              Sys.getenv_opt "ROCQ_DIAGNOSTIC_CONVERSION_TRACE_FROM" with
        | Some call, _ -> Int.equal diagnostic_call (int_of_string call)
        | None, Some first ->
          let first = int_of_string first in
          diagnostic_call >= first && diagnostic_call < first + 4
        | None, None ->
          (* Observation only: select an ordinary fallback by its cheap root
             description, without relying on call numbers that change when
             an optimization eliminates earlier comparisons. *)
          match Sys.getenv_opt "ROCQ_DIAGNOSTIC_CONVERSION_TRACE_HEAD" with
          | Some head when not dependency_preference ->
            String.equal head (diagnostic_constr_head t1) ||
            String.equal head (diagnostic_constr_head t2)
          | Some _ | None -> false
      in
      let () =
        if trace_this_call then begin
          Printf.eprintf "[conversion trace] call=%d start\n%!" diagnostic_call;
          diagnostic_conversion_trace := true;
          diagnostic_conversion_trace_steps := 0;
          diagnostic_conversion_trace_repeats := 0;
          diagnostic_conversion_trace_memo_hits := 0;
          diagnostic_conversion_trace_memo_stores := 0;
          diagnostic_conversion_trace_memo_size := 0;
          diagnostic_conversion_trace_memo_peak := 0;
          diagnostic_conversion_trace_memo_clears := 0;
          DiagnosticConversionPairs.clear diagnostic_conversion_trace_pairs
        end
      in
      let run_conversion () =
        try
          let result =
            ccnv cv_pb l2r infos el_id el_id (inject t1) (inject t2) univs
          in
          if trace_this_call then
            Printf.eprintf "[conversion trace] call=%d success\n%!"
              diagnostic_call;
          Result.Ok result
        with
        | NotConvertible ->
          if trace_this_call then
            Printf.eprintf "[conversion trace] call=%d failure\n%!"
              diagnostic_call;
          Result.Error None
        | NotConvertibleTrace (Error.Error e) -> Result.Error (Some e)
        | NotConvertibleTrace _ -> assert false
      in
      Fun.protect
        ~finally:(fun () ->
          if trace_this_call then begin
            diagnostic_conversion_trace := false;
            DiagnosticConversionPairs.clear diagnostic_conversion_trace_pairs
          end)
        run_conversion
  end ()

let check_eq qeq state u u' =
  if UGraph.check_eq_sort qeq state u u'
  then Result.Ok state
  else Result.Error None

let check_leq qeq state u u' =
  if UGraph.check_leq_sort qeq state u u'
  then Result.Ok state
  else Result.Error None

let checked_sort_cmp_universes qeq = (); fun pb s0 s1 state ->
  match pb with
  | CUMUL -> check_leq qeq state s0 s1
  | CONV -> check_eq qeq state s0 s1

let check_convert_instances qeq = (); fun ~flex:_ u u' state ->
  if UGraph.check_eq_instances qeq state u u' then Result.Ok state
  else Result.Error None

(* general conversion and inference functions *)
let check_inductive_instances qeq = (); fun cv_pb variance u1 u2 state ->
  let qcsts, ucsts = get_cumulativity_constraints cv_pb variance u1 u2 in
  let check_quality (q1, q2) = qeq q1 q2 in
  if UVars.QPairSet.for_all check_quality qcsts && UGraph.check_constraints ucsts state
  then Result.Ok state
  else Result.Error None

let checked_universes_gen qeq =
  { compare_sorts = checked_sort_cmp_universes qeq;
    compare_instances = check_convert_instances qeq;
    compare_cumul_instances = check_inductive_instances qeq; }

let checked_universes = checked_universes_gen Sorts.Quality.equal

let () =
  let conv infos tab a b =
    try
      let box = Empty.abort in
      let state = info_univs infos in
      let qual_equal q1 q2 = CClosure.eq_quality infos q1 q2 in
      let infos = {
        cnv_inf = infos;
        cnv_typ = true;
        cnv_rel_types = Range.empty;
        cnv_rel_type_lifts = Range.empty;
        cnv_probe_budget = None;
        cnv_strategy_budget = info_conversion_work infos;
        cnv_symbolic_budget = None;
        cnv_symbolic_remaining = ref 16_384;
        cnv_failed_symbolic = make_projection_conversion_cache ();
        cnv_projection_conversions = make_projection_conversion_cache ();
        cnv_successful_conversions = make_successful_conversion_cache 0;
        cnv_memoize_successful_conversions = false;
        cnv_projection_congruence = false;
        cnv_dependency_preference = false;
        cnv_constructor_relevance = false;
        cnv_constructor_masks = ConstructorMasks.create 17;
        cnv_failed_congruences = make_failed_congruence_cache ();
        cnv_successful_applications = make_successful_application_cache ();
        lft_tab = tab;
        rgt_tab = tab;
        err_ret = box;
      } in
      let state', _ = ccnv CONV false infos el_id el_id a b (state, checked_universes_gen qual_equal) in
      assert (state==state');
      true
    with
    | NotConvertible -> false
    | NotConvertibleTrace _ -> assert false
  in
  CClosure.set_conv conv

(* The initial alpha test must preserve DAG sharing too: otherwise it can
   expand an exponential tree before the closure-based probe is reached.
   This is only a bounded shortcut. A miss or exhausted budget delegates to
   ordinary conversion; universe checks use the unchanged fixed graph. *)
module AlphaPairs = Hashtbl.Make (struct
  type t = conv_pb * int * constr * constr
  let equal (p,n,a,b) (q,m,c,d) = p=q && n=m && a==c && b==d
  let hash (p,n,a,b) = Hashtbl.hash (p,n,
    Hashtbl.hash_param 8 32 a, Hashtbl.hash_param 8 32 b)
end)

let quick_constr_univs problem univs left right =
  let budget = ref 1024 in
  let memo = lazy (AlphaPairs.create 17) in
  let eq_universes _ = UGraph.check_eq_instances Sorts.Quality.equal univs in
  let eq_sorts a b = a == b || UGraph.check_eq_sort Sorts.Quality.equal univs a b in
  let leq_sorts a b = a == b || UGraph.check_leq_sort Sorts.Quality.equal univs a b in
  let rec compare problem nargs left right =
    if !budget <= 0 then false else begin
      decr budget;
      if left == right then true else
      (* Charge casts explicitly; compare_head's cast stripping would otherwise
         bypass the bound. Existentials are left to ordinary conversion. *)
      match Constr.kind left, Constr.kind right with
      | Cast (body, _, _), _ -> compare problem nargs body right
      | _, Cast (body, _, _) -> compare problem nargs left body
      | (Evar _ | Meta _), _ | _, (Evar _ | Meta _) -> false
      | _ ->
        let key = problem, nargs, left, right in
        if Lazy.is_val memo && AlphaPairs.mem (Lazy.force memo) key then true else
        let sorts = if problem = CONV then eq_sorts else leq_sorts in
        let equal = Constr.compare_head_gen_leq eq_universes sorts
          (fun _ _ -> false) (compare CONV) (compare problem) nargs left right in
        if equal then AlphaPairs.replace (Lazy.force memo) key ();
        equal
    end
  in compare problem 0 left right

let gen_conv ~typed cv_pb ?(l2r=false) ?(reds=TransparentState.full) env ?(evars=default_evar_handler env) t1 t2 =
  let univs = Environ.universes env in
  let state = univs in
  let b = quick_constr_univs cv_pb univs t1 t2 in
    if b then Result.Ok ()
    else
      let convert ?work_limit constructor_relevance projection_congruence
          dependency_preference =
        clos_gen_conv ?work_limit ~typed ~constructor_relevance ~projection_congruence
          ~dependency_preference reds cv_pb l2r evars env univs
          (state, checked_universes) t1 t2
      in
      let conversion () =
        match convert typed false false with
        | Result.Ok (_ : 'a * ('a, Empty.t) universe_compare) -> Result.Ok ()
        | Result.Error None when typed -> begin
            match convert true true false with
            | Result.Ok (_ : 'a * ('a, Empty.t) universe_compare) -> Result.Ok ()
            | Result.Error None -> begin
              match convert true true true with
              | Result.Ok (_ : 'a * ('a, Empty.t) universe_compare) -> Result.Ok ()
              | Result.Error None -> Result.Error ()
              | Result.Error (Some e) -> Empty.abort e
              end
            | Result.Error (Some e) -> Empty.abort e
          end
        | Result.Error None -> Result.Error ()
        | Result.Error (Some e) -> Empty.abort e
      in
      if not diagnostic_no_dependency_first &&
         typed && (Environ.typing_flags env).unfold_dep_heuristic then
        (* Try dependency-guided conversion with bounded work, first without
           and then with constructor proof-field masking. The latter can align
           different inheritance paths without comparing irrelevant fields.
           Exhaustion selects ordinary conversion; it never certifies a
           conversion result. These limits count conversion steps, not WHNF
           work or elapsed time. All attempts retain reduction sharing. *)
        let first =
          try convert ~work_limit:256 false diagnostic_projection_first true
          with Strategy_budget_exhausted -> Result.Error None
        in
        let result = match first with
          | Result.Error None ->
            begin try convert ~work_limit:262_144 true diagnostic_projection_first true
            with Strategy_budget_exhausted -> Result.Error None end
          | result -> result
        in
        match result with
        | Result.Ok (_ : 'a * ('a, Empty.t) universe_compare) -> Result.Ok ()
        | Result.Error None -> conversion ()
        | Result.Error (Some e) -> Empty.abort e
      else conversion ()

let conv = gen_conv ~typed:false CONV
let conv_leq = gen_conv ~typed:false CUMUL

let generic_conv cv_pb ~l2r reds env ?(evars=default_evar_handler env) state t1 t2 =
  let graph = Environ.universes env in
  match clos_gen_conv ~typed:false ~constructor_relevance:false
    ~projection_congruence:false ~dependency_preference:false
    reds cv_pb l2r evars env graph state t1 t2 with
  | Result.Ok (s, _) -> Result.Ok s
  | Result.Error e -> Result.Error e

let default_conv cv_pb env t1 t2 =
    gen_conv ~typed:true cv_pb env t1 t2

let default_conv_leq = default_conv CUMUL

type graph_inconsistency = Univ of UGraph.univ_inconsistency | Qual of QGraph.elimination_error
