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

(* Binder contexts crossed by a conversion are numbered: two contexts get the
   same number exactly when they were built by the same pushes (relevance,
   type cell, type lift) from the empty context, so that memo entries can be
   keyed on it rather than on the physical context ranges. *)
type ctx_step = { parent : int; relevance : Sorts.relevance; typ : int; lift : lift }

module CtxSteps = Hashtbl.Make (struct
  type t = ctx_step
  let equal a b =
    Int.equal a.parent b.parent && Sorts.relevance_equal a.relevance b.relevance &&
    Int.equal a.typ b.typ && eq_lift a.lift b.lift
  let hash a = Hashtbl.hash (a.parent, Hashtbl.hash a.relevance, a.typ, a.lift)
end)

(* Numbers are unique for the whole process; the step table belongs to one
   conversion call. *)
let next_ctx = ref 1

let ctx_push steps parent relevance typ lift =
  let key = { parent; relevance; typ; lift } in
  match CtxSteps.find_opt steps key with
  | Some id -> id
  | None ->
    let id = !next_ctx in
    incr next_ctx;
    CtxSteps.add steps key id;
    id

(* Where a comparison took place: the lifts of its sides and the context. *)
type site = { left_lift : lift; right_lift : lift; ctx : int }

let same_site a b =
  eq_lift a.left_lift b.left_lift && eq_lift a.right_lift b.right_lift &&
  Int.equal a.ctx b.ctx

(* A memo table of one conversion call: an insertion into a full table
   ([limit] entries) first clears it, so that a miss only repeats work. *)
module Bounded (H : Hashtbl.HashedType) = struct
  module T = Hashtbl.Make (H)
  type 'a t = { table : 'a T.t; mutable size : int; limit : int }
  let create ?(limit = 4096) () = { table = T.create 17; size = 0; limit }
  let find t key = T.find_opt t.table key
  let mem t key = T.mem t.table key
  let reserve t = if t.size >= t.limit then begin T.clear t.table; t.size <- 0 end
  let add t key value =
    reserve t;
    T.replace t.table key value;
    t.size <- t.size + 1
end

(* Sites where two cells were compared, keyed by the cells (a comparison may
   have updated them); at most 8 sites per pair. *)
module Sites = struct
  include Bounded (struct
    type t = fconstr * fconstr
    let equal (a, b) (c, d) = a == c && b == d
    let hash (a, b) = Hashtbl.hash (fconstr_hash a, fconstr_hash b)
  end)
  let cached t c1 c2 site = match find t (c1, c2) with
    | Some sites -> List.exists (same_site site) sites
    | None -> false
  let remember t c1 c2 site =
    let sites = match find t (c1, c2) with
      | Some sites when List.length sites < 8 -> sites
      | Some sites -> t.size <- t.size - List.length sites; []
      | None -> [] in
    add t (c1, c2) (site :: sites)
end

(* Applications of two constants, keyed by the heads, the argument frames
   and the site. *)
type frame = Karg of fconstr | Kshift of int | Kproj of Projection.Repr.t * Sorts.relevance

let congruence_frames stack =
  let rec collect fuel acc = function
    | [] -> Some (List.rev acc)
    | _ when fuel <= 0 -> None
    | Zapp args :: rest when Array.length args < fuel ->
      collect (fuel - Array.length args - 1)
        (Array.fold_left (fun acc arg -> Karg arg :: acc) acc args) rest
    | Zshift n :: rest -> collect (fuel - 1) (Kshift n :: acc) rest
    | Zproj (p, r) :: rest -> collect (fuel - 1) (Kproj (p, r) :: acc) rest
    | Zupdate _ :: rest -> collect (fuel - 1) acc rest
    | (Zapp _ | Zfix _ | ZcaseT _ | Zprimitive _) :: _ -> None
  in collect 128 [] stack

module Applications = Bounded (struct
  type t = (pconstant * pconstant) * frame list * frame list * site
  let equal_frame a b = match a, b with
    | Karg a, Karg b -> a == b
    | Kshift n, Kshift m -> Int.equal n m
    | Kproj (p, r), Kproj (q, s) -> Projection.Repr.UserOrd.equal p q && r = s
    | (Karg _ | Kshift _ | Kproj _), _ -> false
  let equal (((c, u), (d, v)), l, r, s) (((c', u'), (d', v')), l', r', s') =
    Constant.UserOrd.equal c c' && Constant.UserOrd.equal d d' &&
    UVars.Instance.equal u u' && UVars.Instance.equal v v' &&
    same_site s s' && List.equal equal_frame l l' && List.equal equal_frame r r'
  (* cells are hashed by identity, never by their mutable contents *)
  let hash_frame h = function
    | Karg term -> Hashtbl.hash (h, 0, fconstr_hash term)
    | Kshift n -> Hashtbl.hash (h, 1, n)
    | Kproj (p, r) -> Hashtbl.hash (h, 2, Projection.Repr.UserOrd.hash p, r)
  let hash (((c, u), (d, v)), l, r, s) =
    let h = Hashtbl.hash (Constant.UserOrd.hash c, UVars.Instance.hash u,
      Constant.UserOrd.hash d, UVars.Instance.hash v) in
    Hashtbl.hash (List.fold_left hash_frame h l, List.fold_left hash_frame h r,
      s.left_lift, s.right_lift)
end)

(* Cells probed for a constructor major with a negative or exhausted answer,
   with the term they had at the time. *)
module MajorProbes = Hashtbl.Make (struct
  type t = fconstr
  let equal = (==)
  let hash = fconstr_hash
end)

(* Successful comparisons of one conversion call. Cells are keyed by identity
   (sharing makes repeated comparisons of the same cells common), suspended
   closures also by their syntax (the same body under substitutions found to
   give the same instance). Both tables count towards one limit of 4_000_000
   entries and are cleared together; 64 entries per key. Completed same-head
   applications are keyed like the failed congruences. *)
module Memo = struct
  type entry = conv_pb * site

  type template = Term of constr | Lambda of (Name.t binder_annot * constr) list * constr

  module Cells = Hashtbl.Make (struct
    type t = fconstr * fconstr
    let equal (a, b) (c, d) = a == c && b == d
    let hash (a, b) = Hashtbl.hash (fconstr_hash a, fconstr_hash b)
  end)

  module Suspended = Hashtbl.Make (struct
    type t = template * template
    let equal_template a b = match a, b with
      | Term a, Term b -> a == b
      | Lambda (ds, a), Lambda (es, b) ->
        a == b && List.equal (fun (na, t) (nb, u) -> na == nb && t == u) ds es
      | (Term _ | Lambda _), _ -> false
    let hash_template = function
      | Term body -> Hashtbl.hash (0, Hashtbl.hash_param 8 32 body)
      | Lambda (ds, body) ->
        List.fold_left (fun h (_, ty) -> Hashtbl.hash (h, Hashtbl.hash_param 8 32 ty))
          (Hashtbl.hash (1, Hashtbl.hash_param 8 32 body)) ds
    let equal (a, b) (c, d) = equal_template a c && equal_template b d
    let hash (a, b) = Hashtbl.hash (hash_template a, hash_template b)
  end)

  type t = {
    cells : entry list Cells.t;
    suspended : (entry * usubs * usubs) list Suspended.t;
    mutable size : int;
    applications : conv_pb list Applications.t;
  }

  let create () =
    { cells = Cells.create 251; suspended = Suspended.create 251; size = 0;
      applications = Applications.create ~limit:32_768 () }

  let reserve t =
    if t.size >= 4_000_000 then begin
      Cells.clear t.cells; Suspended.clear t.suspended; t.size <- 0 end

  (* the entries of a full key are dropped *)
  let entries t = function
    | Some entries when List.length entries < 64 -> entries
    | Some entries -> t.size <- t.size - List.length entries; []
    | None -> []

  let cached t cv_pb site c1 c2 =
    match Cells.find_opt t.cells (c1, c2) with
    | Some entries -> List.exists (fun (pb, s) -> pb = cv_pb && same_site s site) entries
    | None -> false

  let remember t cv_pb site c1 c2 =
    reserve t;
    Cells.replace t.cells (c1, c2) ((cv_pb, site) :: entries t (Cells.find_opt t.cells (c1, c2)));
    t.size <- t.size + 1

  (* The suspended syntax of two cells (their saved spines first): the body of
     a closure, or the domains and body of a lambda. *)
  let suspended_key c1 c2 =
    let capture c = match [@ocaml.warning "-4"] fterm_of (Option.default c (symbolic_view c)) with
      | FCLOS (body, subst) -> Some (Term body, subst)
      | FLambda (n, domains, body, subst) when n <= 1024 -> Some (Lambda (domains, body), subst)
      | _ -> None in
    match capture c1, capture c2 with
    | Some (t1, subst1), Some (t2, subst2) -> Some ((t1, t2), subst1, subst2)
    | _ -> None

  let suspended t key = Option.default [] (Suspended.find_opt t.suspended key)

  let remember_suspended t cv_pb site (key, subst1, subst2) =
    reserve t;
    Suspended.replace t.suspended key
      (((cv_pb, site), subst1, subst2) :: entries t (Suspended.find_opt t.suspended key));
    t.size <- t.size + 1

  let completed t cv_pb key =
    List.mem cv_pb (Option.default [] (Applications.find t.applications key))

  let complete t cv_pb key =
    Applications.reserve t.applications;
    let problems = Option.default [] (Applications.find t.applications key) in
    if not (List.mem cv_pb problems) then Applications.add t.applications key (cv_pb :: problems)
end

module ConstructorMasks = Hashtbl.Make (struct
  type t = pconstructor
  let equal (c, u) (d, v) = Construct.UserOrd.equal c d && UVars.Instance.equal u v
  let hash (c, u) = Hashtbl.hash (Construct.UserOrd.hash c, UVars.Instance.hash u)
end)

(* Settings of one attempt of a typed conversion, see [gen_conv]. *)
type strategy = {
  steps : int option; (* step allowance, [None] for an unbounded attempt *)
  constructor_relevance : bool; (* skip the irrelevant fields of constructors *)
  projection_congruence : bool; (* compare same-field projections by congruence first *)
  dependency_preference : bool; (* unfold the side that depends on the other head *)
}

let plain_strategy = {
  steps = None; constructor_relevance = false;
  projection_congruence = false; dependency_preference = false;
}

(* Remaining depth and work of the enclosing bounded congruence check. *)
type probe = { depth : int ref; work : int ref }

type 'e conv_tab = {
  cnv_inf : clos_infos;
  cnv_typ : bool; (* true if the input terms were well-typed *)
  cnv_rel_types : fconstr option Range.t;
  cnv_rel_type_lifts : lift Range.t;
  cnv_ctx : int;
  cnv_ctx_steps : int CtxSteps.t;
  cnv_strategy : strategy;
  cnv_steps : int ref option; (* remaining steps of a bounded attempt *)
  cnv_probe : probe option;
  cnv_symbolic : int ref option; (* remaining steps of a symbolic recovery *)
  cnv_symbolic_total : int ref; (* remaining steps of all symbolic recoveries *)
  cnv_symbolic_misses : site list Sites.t; (* pairs whose recovery failed *)
  cnv_projections : site list Sites.t; (* sources of projections found convertible *)
  cnv_failed : unit Applications.t; (* congruence failed: the retry unfolds *)
  cnv_memo : Memo.t option; (* of a typed conversion under the heuristic *)
  cnv_masks : bool array ConstructorMasks.t;
  cnv_major_misses : fterm MajorProbes.t;
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

let dep_heuristic infos = (Environ.typing_flags (info_env infos.cnv_inf)).unfold_dep_heuristic

(* The closures of a side are built with the cells of its table. *)
let lft_cells infos f = with_sharing infos.cnv_inf infos.lft_tab f
let rgt_cells infos f = with_sharing infos.cnv_inf infos.rgt_tab f

exception Probe_budget_exhausted
exception Strategy_budget_exhausted
exception Symbolic_budget_exhausted

let charge_step infos =
  Option.iter (fun remaining ->
    if !remaining = 0 then raise Strategy_budget_exhausted;
    decr remaining) infos.cnv_steps;
  Option.iter (fun remaining ->
    if !remaining = 0 || !(infos.cnv_symbolic_total) = 0 then raise Symbolic_budget_exhausted;
    decr remaining; decr infos.cnv_symbolic_total) infos.cnv_symbolic

(* Congruence may compare branches that evaluating the application would
   discard: bound its depth and total work, unless it already runs inside a
   bounded check. Exhaustion is inconclusive and falls back to unfolding. *)
let bounded_congruence infos compare =
  if Option.has_some infos.cnv_probe || not (dep_heuristic infos) then compare infos
  else
    try compare { infos with cnv_probe = Some { depth = ref 256; work = ref 4096 } }
    with Probe_budget_exhausted -> raise NotConvertible

let application_key infos lft1 lft2 fl1 stk1 fl2 stk2 =
  match fl1, fl2, congruence_frames stk1, congruence_frames stk2 with
  | ConstKey c, ConstKey d, Some left, Some right when infos.cnv_typ ->
    Some ((c, d), left, right, { left_lift = lft1; right_lift = lft2; ctx = infos.cnv_ctx })
  | _ -> None

(* A failed congruence is remembered; a hit certifies nothing. *)
let try_congruence infos lft1 lft2 fl1 stk1 fl2 stk2 compare =
  let key = application_key infos lft1 lft2 fl1 stk1 fl2 stk2 in
  if Option.cata (Applications.mem infos.cnv_failed) false key then raise NotConvertible;
  try bounded_congruence infos compare
  with (NotConvertible | NotConvertibleTrace _) as error ->
    Option.iter (fun key ->
      if not (Applications.mem infos.cnv_failed key) then
        Applications.add infos.cnv_failed key ()) key;
    raise error

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

(** The same heap separation invariant must hold for the fconstr arguments
    passed to each respective side of the conversion function below. *)

(* Unfolding preferences. Generated eliminators are ordinary constants around
   a fixpoint or a case, and their major premise is compared, or evaluated,
   before delta; the read-only tests below only choose the side to unfold
   and never establish an equality. *)

let transparent infos constant =
  RedFlags.red_set (info_flags infos.cnv_inf) (RedFlags.fCONST constant)

let definition_body infos constant =
  match (Environ.lookup_constant constant (info_env infos.cnv_inf)).const_body with
  | Def body when transparent infos constant -> Some body
  | Def _ | Undef _ | OpaqueDef _ | Primitive _ | Symbol _ -> None

let oracle_expands infos constant =
  let strategy = Conv_oracle.get_strategy (oracle_of_infos infos.cnv_inf) in
  match strategy (Conv_oracle.EvalConstRef constant) with
  | Conv_oracle.Expand -> true
  | Conv_oracle.Level _ | Conv_oracle.Opaque -> false

(* A constructor at [term], through let-bound variables, without quoting or
   lifting a possibly large body. *)
let visible_constructor_head env term =
  let rec local_constructor fuel index =
    if fuel = 0 || index <= 0 || index > 4096 then false else
    match Environ.lookup_rel index env with
    | Context.Rel.Declaration.LocalAssum _ -> false
    | Context.Rel.Declaration.LocalDef (_, body, _) -> raw_constructor (fuel - 1) index body
    | exception Not_found -> false
  and raw_constructor fuel offset body =
    if fuel = 0 then false else match Constr.kind body with
    | Construct _ -> true
    | App (head, _) -> isConstruct head
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
      | App (head, _) -> isConstruct head
      | Rel index -> (match inspect_substituted_rel subst index with
        | Some term -> constructor (fuel - 1) term
        | None -> (match expand_rel index (fst subst) with
          | Inr (_, Some index) -> local_constructor (fuel - 1) index
          | Inr (_, None) | Inl _ -> false))
      | _ -> false end
    | _ -> false in
  constructor 16 term

let major_reds infos = RedFlags.(red_add_transparent all (red_transparent (info_flags infos)))

(* A constructor at the head of [term] reduced in the private view [infos]
   with the caller's transparency, [None] when the demand is stuck. *)
let constructor_major infos tab term =
  let head, stack = whd_stack infos tab term [] in
  if is_empty_stack stack then
    (match fterm_of head with FConstruct _ | FPeanoNat _ -> Some head | _ -> None)
  else None

let reduce_constructor_major ?(tab = create_tab ()) infos term =
  let infos = infos_with_private_reduction (infos_with_reds infos (major_reds infos)) in
  constructor_major infos tab term

(* Index of the argument a transparent, relevant constant eliminates: the
   recursive argument of its fixpoint or the subject of its case. *)
let eliminator_major infos reference =
  let env = info_env infos.cnv_inf in
  if not infos.cnv_typ || not (dep_heuristic infos) then None else
  let rec major parameters body =
    match Constr.kind body with
    | Lambda (_, _, body) -> major (parameters + 1) body
    | Fix ((indices, selected), _) when selected >= 0 && selected < Array.length indices ->
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
      Conv_oracle.is_transparent (Conv_oracle.get_strategy
        (oracle_of_infos infos.cnv_inf) (Conv_oracle.EvalConstRef constant)) ->
    Option.bind (definition_body infos constant) (major 0)
  | _ -> None

(* Argument [index] of a stack, with the lift of its position. *)
let rec stack_argument lift index = function
  | Zapp args :: rest ->
    if index < Array.length args then Some (el_stack lift rest, args.(index))
    else stack_argument lift (index - Array.length args) rest
  | (Zshift _ | Zupdate _) :: rest -> stack_argument lift index rest
  | [] | (Zproj _ | Zfix _ | ZcaseT _ | Zprimitive _) :: _ -> None

let eliminates_constructor infos reference stack =
  match eliminator_major infos reference with
  | Some index ->
    Option.cata (fun (_, major) -> visible_constructor_head (info_env infos.cnv_inf) major)
      false (stack_argument el_id index stack)
  | None -> false

(* Iota before delta: an eliminator whose major computes to a constructor
   within 512 visits of a private reduction is unfolded first, as by Lean's
   whnf_core. A negative or exhausted probe is remembered with the cell's
   term, so that an unchanged cell is probed once per conversion. *)
let probed_constructor_major ?tab infos reference stack =
  match eliminator_major infos reference with
  | None -> false
  | Some index ->
    match stack_argument el_id index stack with
    | None -> false
    | Some (_, major) ->
      let misses = infos.cnv_major_misses in
      let current = fterm_of major in
      match MajorProbes.find_opt misses major with
      | Some term when term == current -> false
      | _ ->
        let tab = match tab with Some tab -> tab | None -> create_tab () in
        let infos = infos_with_reds infos.cnv_inf (major_reds infos.cnv_inf) in
        match with_bounded_private_reduction ~steps:512 infos (fun infos ->
            Option.has_some (constructor_major infos tab major)) with
        | Some true -> true
        | Some false | None ->
          if MajorProbes.length misses >= 1_000_000 then MajorProbes.reset misses;
          MajorProbes.replace misses major current;
          false

(* The stack with the eliminated major replaced by its reduced value, so that
   iota follows the unfolding instead of getting stuck on the original
   projection; the application frame is copied, the other cells are not. *)
let expose_major ?tab infos reference stack =
  let rec replace prefix index = function
    | Zapp args :: rest when index < Array.length args ->
      Option.map (fun major ->
        let args = Array.copy args in
        args.(index) <- major;
        List.rev_append prefix (Zapp args :: rest))
        (reduce_constructor_major ?tab infos.cnv_inf args.(index))
    | (Zapp args as frame) :: rest -> replace (frame :: prefix) (index - Array.length args) rest
    | ((Zshift _ | Zupdate _) as frame) :: rest -> replace (frame :: prefix) index rest
    | [] | (Zproj _ | Zfix _ | ZcaseT _ | Zprimitive _) :: _ -> None in
  match eliminator_major infos reference with
  | Some index -> Option.default stack (replace [] index stack)
  | None -> stack

(* [source] is defined as [target] applied, under binders. *)
let direct_head_alias env source target =
  let rec head target fuel body =
    fuel > 0 && match Constr.kind body with
    | Lambda (_, _, body) | Cast (body, _, _) | App (body, _) -> head target (fuel - 1) body
    | Const (constant, _) -> Constant.UserOrd.equal constant target
    | _ -> false
  in
  match source, target with
  | ConstKey (source, _), ConstKey (target, _) when not (Constant.UserOrd.equal source target) ->
    (match (Environ.lookup_constant source env).const_body with
     | Def body -> head target 64 body
     | _ -> false)
  | _ -> false

(* An applied transparent constant whose body is a constructor or a projection
   through a bounded number of transparent aliases: unfolded before record
   eta adds projections that may force the implementation of its fields. *)
let record_wrapper infos reference stack =
  let rec wrapper_head fuel term =
    match Constr.kind term with
    | Lambda (_, _, body) -> wrapper_head fuel body
    | App (head, _) -> wrapper_head fuel head
    | Construct _ | Proj _ -> true
    | Const (constant, _) when fuel > 0 ->
      Option.cata (wrapper_head (fuel - 1)) false (definition_body infos constant)
    | _ -> false
  in
  let applications_only = List.for_all (function
    | Zapp _ | Zupdate _ | Zshift _ -> true
    | Zproj _ | Zfix _ | ZcaseT _ | Zprimitive _ -> false)
  in
  match reference with
  | ConstKey (constant, _) when applications_only stack ->
    Option.cata (wrapper_head 32) false (definition_body infos constant)
  | ConstKey _ | RelKey _ | VarKey _ -> false

(* Which side to unfold when both can be: a decisive oracle priority is only
   overridden by a direct occurrence of the other head (Lean exposes a
   projected field before consulting delta hints); on a tie, the dependency
   graph, then a constructor argument, then the fallback: the side that is
   not an elimination over a compact natural, else the oracle. *)
type unfolding_action = Unfold_left | Unfold_right | Unfold_both

let unfolding_side left = if left then Unfold_left else Unfold_right

let choose_unfolding_action ~order ~l2r ~heuristic ~compact:(compact1, compact2)
    ~direct_dependency ~dependency ~constructor =
  let fallback () =
    (* an elimination over a compact natural stays closed *)
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
    (* the constructor test may update closures seen by the dependency test *)
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

(* A transparent definition applied, projected and applied again: the field
   is exposed before congruence compares the arguments of the record. *)
let applied_projection_source infos reference stack =
  let rec inspect arguments projected = function
    | (Zshift _ | Zupdate _) :: rest -> inspect arguments projected rest
    | Zapp args :: rest when Array.is_empty args -> inspect arguments projected rest
    | Zapp _ :: _ when projected -> arguments
    | Zapp _ :: rest -> inspect true projected rest
    | Zproj _ :: rest -> inspect arguments true rest
    | [] | (Zfix _ | ZcaseT _ | Zprimitive _) :: _ -> false
  in
  dep_heuristic infos && inspect false false stack &&
  match reference with
  | ConstKey (constant, _) -> Option.has_some (definition_body infos constant)
  | RelKey _ | VarKey _ -> false

(* A projected application of a transparent constructor wrapper whose
   selected field is function-valued or forwards an argument: projected
   before the wrapper's arguments are compared. Other computed fields are
   not, as they may start expensive arithmetic. *)
let projected_record_wrapper infos reference stack =
  let env = info_env infos.cnv_inf in
  let rec projections fuel stack =
    if fuel = 0 then None else match stack with
    | (Zshift _ | Zupdate _) :: stack -> projections (fuel - 1) stack
    | Zproj (projection, _) :: stack ->
      Option.map (fun rest -> projection :: rest) (projections (fuel - 1) stack)
    | _ -> Some []
  in
  (* only arguments before the first projection belong to the wrapper *)
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
  let rec forwarded fuel term = match Constr.kind term with
    | Rel _ | Lambda _ -> true
    | Proj (_, _, source) when fuel > 0 -> forwarded (fuel - 1) source
    | (Const _ | App _) when fuel > 0 ->
      let head, args = Constr.decompose_app term in
      begin match Constr.kind head with
      | Const (constant, _) ->
        begin match definition_body infos constant with
        | Some body ->
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
        | None -> false
        end
      | Rel _ | Proj _ -> forwarded (fuel - 1) head && Array.for_all (forwarded (fuel - 1)) args
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
  dep_heuristic infos &&
  match reference, projection 1024 false stack with
  | ConstKey (constant, _), Some projections ->
    begin match definition_body infos constant with
    | Some body ->
      let method_field =
        let last = Projection.make (List.last projections) false in
        isProd (snd (Environ.lookup_projection last env))
      in
      selects_field 1024 method_field projections body
    | None -> false
    end
  | _ -> false

(* Unit-like types. A registered inductive (one constructor, no relevant
   field) has definitionally equal inhabitants, and so does a record with eta
   whose fields are all irrelevant or unit-like at its parameters. Two neutral
   terms of such a type are convertible once their types are. Types are only
   inspected in bounded private views, see [with_type_snapshot]. *)

let rec direct_inductive typ =
  match fterm_of typ with
  | FInd (ind, _) -> Some ind
  | FApp (head, _) | FLIFT (_, head) -> direct_inductive head
  | FCLOS (term, _) ->
    begin match Constr.kind (fst (Constr.decompose_app term)) with
    | Constr.Ind (ind, _) -> Some ind
    | _ -> None
    end
  | _ -> None

(* The registered unit-like inductives, as a set built once per retroknowledge. *)
let unit_like_index = ref ([], Indset_env.empty)

let is_registered_unit_like env ind =
  let registered = (Environ.retroknowledge env).Retroknowledge.retro_unit_like in
  let previous, index = !unit_like_index in
  let index = if registered == previous then index else begin
    let index = Indset_env.of_list registered in
    unit_like_index := registered, index;
    index
  end in
  Indset_env.mem ind index

let direct_registered_unit_like infos typ =
  match direct_inductive typ with
  | Some ind when is_registered_unit_like (info_env infos.cnv_inf) ind -> Some ind
  | Some _ | None -> None

(* Relevance mask of the arguments of a constructor, empty when all are
   relevant. *)
let constructor_mask infos (((ind, _), instance) as constructor) =
  match ConstructorMasks.find_opt infos.cnv_masks constructor with
  | Some mask -> mask
  | None ->
    let env = info_env infos.cnv_inf in
    let typ = Inductive.type_of_constructor constructor (Inductive.lookup_mind_specif env ind) in
    let mask = relevance_mask infos.cnv_inf instance typ in
    let mask = if Array.for_all (fun relevant -> relevant) mask then [||] else mask in
    ConstructorMasks.add infos.cnv_masks constructor mask;
    mask

(* Type of the variable [n]: the domain of a binder crossed by this conversion
   (kept in [cnv_rel_types] with the lift of its side) or its declaration in
   the environment. *)
let rel_type infos n =
  let depth = Range.length infos.cnv_rel_types in
  if n <= depth then Range.get infos.cnv_rel_types (n - 1)
  else
    try
      let decl = Environ.lookup_rel (n - depth) (info_env infos.cnv_inf) in
      Some (inject (Context.Rel.Declaration.get_type decl))
    with Not_found -> None

(* The same, with its relocation into the current context. *)
let rel_type_lifted infos n =
  let depth = Range.length infos.cnv_rel_types in
  if n <= depth then
    Option.map (fun typ ->
      let lift = Range.get infos.cnv_rel_type_lifts (n - 1) in
      el_shft n (el_liftn n lift), typ) (rel_type infos n)
  else
    try
      let decl = Environ.lookup_rel (n - depth) (info_env infos.cnv_inf) in
      (* The declaration's type lives below it: lift the syntax, a closure
         shift would turn its RelKey k into the other entry RelKey (k+n). *)
      let typ = Vars.lift n (Context.Rel.Declaration.get_type decl) in
      Some (el_id, mk_clos (subs_id depth, UVars.Instance.empty) typ)
    with Not_found -> None

let push_relevance ?typ ?(type_lift = el_id) infos r =
  let typ_id = match typ with None -> -1 | Some t -> fconstr_hash t in
  { infos with
    cnv_inf = CClosure.push_relevance infos.cnv_inf r;
    cnv_rel_types = Range.cons typ infos.cnv_rel_types;
    cnv_rel_type_lifts = Range.cons type_lift infos.cnv_rel_type_lifts;
    cnv_ctx =
      ctx_push infos.cnv_ctx_steps infos.cnv_ctx r.Context.binder_relevance typ_id type_lift }

let push_relevances infos nas =
  { infos with
    cnv_inf = CClosure.push_relevances infos.cnv_inf nas;
    cnv_rel_types =
      Array.fold_left (fun types _ -> Range.cons None types) infos.cnv_rel_types nas;
    cnv_rel_type_lifts =
      Array.fold_left (fun lifts _ -> Range.cons el_id lifts) infos.cnv_rel_type_lifts nas;
    cnv_ctx = Array.fold_left (fun ctx na ->
        ctx_push infos.cnv_ctx_steps ctx na.Context.binder_relevance (-1) el_id)
        infos.cnv_ctx nas }

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

(* Bounded syntactic test of two closures, read-only: running out of budget is
   inconclusive. Pairs already found equal are memoised for the duration of
   one test, so that shared DAGs are compared with sharing; every visit,
   including a hit, is charged. *)
type syntax_pair =
  | SyntaxPair of constr * usubs * constr * usubs
  | ClosurePair of fconstr * lift * fconstr * lift

module SyntaxPairs = Hashtbl.Make (struct
  type t = syntax_pair
  let equal left right = match left, right with
    | SyntaxPair (a, e, b, f), SyntaxPair (c, g, d, h) ->
      a == c && b == d && eq_usubs_fast e g && eq_usubs_fast f h
    | ClosurePair (a, e, b, f), ClosurePair (c, g, d, h) ->
      a == c && b == d && eq_lift e g && eq_lift f h
    | _ -> false
  let hash = function
    | SyntaxPair (a, _, b, _) -> Hashtbl.hash_param 8 32 (0, a, b)
    | ClosurePair (a, _, b, _) -> Hashtbl.hash (1, fconstr_hash a, fconstr_hash b)
end)

(* The memo of one test; [symbolic] compares the saved spines of two cells
   before their values. *)
type syntax_memo = { pairs : unit SyntaxPairs.t Lazy.t; symbolic : bool }

let syntax_memo ?(symbolic = false) () = { pairs = lazy (SyntaxPairs.create 17); symbolic }

let syntax_cached memo = function
  | None -> false
  | Some key -> Lazy.is_val memo.pairs && SyntaxPairs.mem (Lazy.force memo.pairs) key

let remember_syntax memo = function
  | None -> ()
  | Some key -> SyntaxPairs.replace (Lazy.force memo.pairs) key ()

let rec compare_under memo budget e1 c1 e2 c2 =
  if !budget <= 0 then false else begin
  decr budget;
  if c1 == c2 && eq_usubs_fast e1 e2 then true else
  let key = match Constr.kind c1 with
    | App _ | Lambda _ | Prod _ | LetIn _ | Proj _ | Cast _ | Fix _ | CoFix _ | Array _ ->
      Some (SyntaxPair (c1, e1, c2, e2))
    | _ -> None in
  if syntax_cached memo key then true else
  let equal = match Constr.kind c1, Constr.kind c2 with
  | Cast (c1, _, _), _ -> compare_under memo budget e1 c1 e2 c2
  | _, Cast (c2, _, _) -> compare_under memo budget e1 c1 e2 c2
  | Rel i, Rel j -> begin
      match Esubst.expand_rel i (fst e1), Esubst.expand_rel j (fst e2) with
      | Inl (shift1, _), Inl (shift2, _) ->
        (* carry the relocations: [mk_clos] would copy a lifted constructor tree *)
        (match inspect_substituted_rel e1 i, inspect_substituted_rel e2 j with
        | Some term1, Some term2 ->
          fast_test_under memo budget (el_shft shift1 el_id) term1 (el_shft shift2 el_id) term2
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
    compare_under memo budget e1 t1 e2 t2
    && compare_under memo budget (usubs_lift e1) c1 (usubs_lift e2) c2
  | Lambda (_,t1,c1), Lambda (_,t2,c2) ->
    compare_under memo budget e1 t1 e2 t2
    && compare_under memo budget (usubs_lift e1) c1 (usubs_lift e2) c2
  | LetIn (_,b1,_,c1), LetIn (_,b2,_,c2) ->
    (* don't care about types when bodies are equal *)
    compare_under memo budget e1 b1 e2 b2
    && compare_under memo budget (usubs_lift e1) c1 (usubs_lift e2) c2
  | App (c1, l1), App (c2, l2) ->
    let len = Array.length l1 in
    Int.equal len (Array.length l2)
    && compare_under memo budget e1 c1 e2 c2
    && Array.equal_norefl (fun c1 c2 -> compare_under memo budget e1 c1 e2 c2) l1 l2
  | Proj (p1,_,c1), Proj (p2,_,c2) ->
    Projection.UserOrd.equal p1 p2 && compare_under memo budget e1 c1 e2 c2
  | Evar _, Evar _ -> false
  | Const (c1,u1), Const (c2,u2) ->
    (* The args length currently isn't used but may as well pass it. *)
    Constant.UserOrd.equal c1 c2 && eq_universes e1 e2 u1 u2
  | Ind (c1,u1), Ind (c2,u2) -> Ind.UserOrd.equal c1 c2 && eq_universes e1 e2 u1 u2
  | Construct (c1,u1), Construct (c2,u2) ->
    Construct.UserOrd.equal c1 c2 && eq_universes e1 e2 u1 u2
  | Array(_,t1,def1,ty1), Array(_,t2,def2,ty2) ->
    Array.equal_norefl (fun c1 c2 -> compare_under memo budget e1 c1 e2 c2) t1 t2
    && compare_under memo budget e1 def1 e2 def2
    && compare_under memo budget e1 ty1 e2 ty2
  | (Rel _ | Meta _ | Var _ | Sort _ | Prod _ | Lambda _ | LetIn _ | App _
    | Proj _ | Evar _ | Const _ | Ind _ | Construct _ | Case _ | Fix _
    | CoFix _ | Int _ | Float _ | String _ | Array _), _ -> false in
  if equal then remember_syntax memo key;
  equal
  end

and fast_test_under memo budget lft1 term1 lft2 term2 =
  if !budget <= 0 then false else begin
  decr budget;
  (* the same cell under the same lift, before its children are revisited *)
  if term1 == term2 && eq_lift lft1 lft2 then true else
  let key = match fterm_of term1 with
    | FCLOS _ | FApp _ | FLambda _ | FProj _ | FFix _ | FCoFix _ | FLIFT _ ->
      Some (ClosurePair (term1, lft1, term2, lft2))
    | FConstruct (_, args) when not (Array.is_empty args) ->
      Some (ClosurePair (term1, lft1, term2, lft2))
    | _ -> None in
  if syntax_cached memo key then true else
  let same_spines =
    memo.symbolic &&
    let spine term = Option.default term (symbolic_view term) in
    let spine1 = spine term1 and spine2 = spine term2 in
    (spine1 != term1 || spine2 != term2) &&
    fast_test_under memo budget lft1 spine1 lft2 spine2 in
  let equal = same_spines ||
  match fterm_of term1, fterm_of term2 with
  | FLIFT (i, term1), _ -> fast_test_under memo budget (el_shft i lft1) term1 lft2 term2
  | _, FLIFT (j, term2) -> fast_test_under memo budget lft1 term1 (el_shft j lft2) term2
  | FCLOS (c1, (e1,u1)), FCLOS (c2, (e2,u2)) ->
    eq_lift lft1 lft2 &&
    compare_under memo budget (e1, u1) c1 (e2, u2) c2
  | FFix (fix1, e1), FFix (fix2, e2) ->
    eq_lift lft1 lft2 &&
    compare_under memo budget e1 (mkFix fix1) e2 (mkFix fix2)
  | FCoFix (fix1, e1), FCoFix (fix2, e2) ->
    eq_lift lft1 lft2 &&
    compare_under memo budget e1 (mkCoFix fix1) e2 (mkCoFix fix2)
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
    Array.equal_norefl (fun t1 t2 -> fast_test_under memo budget lft1 t1 lft2 t2) a1 a2
  | FApp (f1, a1), FApp (f2, a2) ->
    fast_test_under memo budget lft1 f1 lft2 f2 &&
    Array.equal_norefl (fun t1 t2 -> fast_test_under memo budget lft1 t1 lft2 t2) a1 a2
  | FProj (p1, _, c1), FProj (p2, _, c2) ->
    Projection.UserOrd.equal p1 p2 &&
    fast_test_under memo budget lft1 c1 lft2 c2
  | FLambda (n1, ds1, b1, e1), FLambda (n2, ds2, b2, e2) ->
    Int.equal n1 n2 && eq_lift lft1 lft2 &&
    (* the binders are charged before the lambda syntax is rebuilt *)
    let rec charge = function
      | [] -> true
      | _ :: rest -> if !budget <= 0 then false else (decr budget; charge rest)
    in
    charge ds1 && charge ds2 &&
    let lambda ds body =
      List.fold_right (fun (na, ty) body -> mkLambda (na, ty, body)) ds body
    in compare_under memo budget e1 (lambda ds1 b1) e2 (lambda ds2 b2)
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
  fast_test_under (syntax_memo ()) (ref 1024) lft1 term1 lft2 term2

(* A suspended entry of the memo is reused when its substitutions and the
   present ones give the same instance of the templates, by a read-only
   syntactic test; one budget of 1024 for all the entries of a key. *)
let suspended_cached memo cv_pb site ((template1, template2) as key, subst1, subst2) =
  let budget = ref 1024 in
  let same template subst old =
    let instance subst old body =
      compare_under (syntax_memo ~symbolic:true ()) budget subst body old body in
    match template with
    | Memo.Term body -> instance subst old body
    | Memo.Lambda (domains, body) ->
      let rec under subst old = function
        | [] -> instance subst old body
        | (_, domain) :: rest ->
          instance subst old domain && under (usubs_lift subst) (usubs_lift old) rest
      in under subst old domains
  in
  List.exists (fun ((pb, s), old1, old2) ->
    pb = cv_pb && same_site s site && same template1 subst1 old1 && same template2 subst2 old2)
    (Memo.suspended memo key)

(* Two bare projections of the same constructor wrapper whose selected field
   forwards an argument that is syntactically the same on both sides: the
   wrapper is unfolded rather than compared by congruence. *)
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
  dep_heuristic infos &&
  match reference1, reference2, first_projection 0 stack1, first_projection 0 stack2 with
  | ConstKey (c1, u1), ConstKey (c2, u2), Some (n1, p1), Some (n2, p2)
      when Constant.UserOrd.equal c1 c2 && UVars.Instance.equal u1 u2 && n1 = n2 &&
           Projection.Repr.CanOrd.equal p1 p2 ->
    begin match definition_body infos c1 with
    | Some body ->
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
          begin match stack_argument lft1 (arity - index) stack1,
                      stack_argument lft2 (arity - index) stack2 with
          | Some (lift1, arg1), Some (lift2, arg2) -> fast_test lift1 arg1 lift2 arg2
          | _ -> false end
        | _ -> false end
      | _ -> false end
    | None -> false end
  | _ -> false

(* The arguments of two application stacks are syntactically the same, where
   a constructor exposed on one side is compared with suspended constructor
   syntax on the other without reducing either. Read-only and bounded; an
   unsupported frame is inconclusive. *)
let syntactically_same_arguments lft1 stack1 lft2 stack2 =
  let budget = ref 1024 in
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
    | _ -> fast_test_under (syntax_memo ()) budget lift1 term1 lift2 term2
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
          (* a substituted variable is inspected, [mk_clos] would lift its value *)
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
        UVars.Instance.equal (usubst_instance subst u1) u2 &&
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
  (* the lift of each argument accounts for the shifts after it, as in [pure_stack] *)
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

(* The arguments of a stack, [None] when it eliminates. *)
let rec application_args arrays = function
  | Zapp args :: stack -> application_args (args :: arrays) stack
  | (Zshift _ | Zupdate _) :: stack -> application_args arrays stack
  | [] -> Some (Array.concat (List.rev arrays))
  | (ZcaseT _ | Zproj _ | Zfix _ | Zprimitive _) :: _ -> None

(* Return type of a case at [indices] and [subject], without evaluating the
   subject or quoting the branches; let-bound parameters and indices come
   from the inductive's own contexts. *)
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

(* Type of a head of type [typ] under [stack] (arguments, projections and
   cases), reduced with [infos] and handed to [classify]. The head itself is
   [subject] when known: a case or a dependent projection needs it. With
   [aliases], constants the oracle marks Expand are unfolded (with the
   caller's transparency, in a separate table) when [classify] fails. *)
let type_after_stack ?aliases ?subject ~classify infos tab typ stack =
  let env = info_env infos in
  let alias_tab = lazy (create_tab ()) in
  let strategy alias_infos constant =
    Conv_oracle.get_strategy (oracle_of_infos alias_infos) (Conv_oracle.EvalConstRef constant) in
  let rec apply_args typ args index =
    if Int.equal index (Array.length args) then Some typ
    else
      let typ, stack = whd_stack infos tab typ empty_stack in
      match fterm_of (zip typ stack) with
      | FProd (_, _, body, subst) ->
        apply_args (mk_clos (usubs_cons args.(index) subst) body) args (index + 1)
      | _ -> None
  in
  let rec final fuel typ =
    let typ, stack = whd_stack infos tab typ empty_stack in
    match classify (zip typ stack), aliases, fterm_of typ, stack with
    | Some _ as result, _, _, _ -> result
    | None, Some alias_infos, FFlex (ConstKey (constant, _) as flex), [] when fuel > 0 ->
      begin match strategy alias_infos constant with
      | Conv_oracle.Expand ->
        Option.bind (unfold_ref_with_args alias_infos (Lazy.force alias_tab) flex stack)
          (fun (typ, stack) -> final (fuel - 1) (zip typ stack))
      | Conv_oracle.Level _ | Conv_oracle.Opaque -> None
      end
    | None, _, _, _ -> None
  in
  let rec projection_type fuel typ stack =
    match aliases, fterm_of typ with
    | Some alias_infos, FFlex (ConstKey (constant, _) as flex) when fuel > 0 ->
      begin match strategy alias_infos constant with
      | Conv_oracle.Opaque -> typ, stack
      | Conv_oracle.Expand | Conv_oracle.Level _ ->
        begin match unfold_ref_with_args alias_infos (Lazy.force alias_tab) flex stack with
        | None -> typ, stack
        | Some (body, stack) ->
          (* follow the alias without evaluating matches or fixpoints *)
          let typ, stack = whd_stack (infos_with_reds infos RedFlags.betazeta) tab body stack in
          projection_type (fuel - 1) typ stack
        end
      end
    | _ -> typ, stack
  in
  let rec eliminate typ subject = function
    | [] -> final 32 typ
    | Zupdate _ :: stack -> eliminate typ subject stack
    | Zshift _ :: stack ->
      (* a supplied subject is already in the common context *)
      if Option.has_some subject then None else eliminate typ None stack
    | Zapp args :: stack ->
      Option.bind (apply_args typ args 0) (fun typ ->
        let subject = Option.map (fun term -> zip term [Zapp args]) subject in
        eliminate typ subject stack)
    | Zproj (repr, relevance) :: stack ->
      let typ, typ_stack = whd_stack infos tab typ empty_stack in
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
          (* Parameters are closures, not necessarily quotable (a proof may
             already be [FIrrelevant]): substitute them lazily. *)
          let subst =
            Array.fold_left (fun subst arg -> usubs_cons arg subst) (subs_id 0, u) args in
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
        let typ, typ_stack = whd_stack infos tab typ empty_stack in
        match fterm_of typ, application_args [] typ_stack with
        | FInd (ind, _), Some args when Environ.QInd.equal env ind ci.ci_ind ->
          let mib, mip = Inductive.lookup_mind_specif env ci.ci_ind in
          if Array.length args <> mib.mind_nparams + mip.mind_nrealargs then None
          else
            let indices = Array.sub args mib.mind_nparams mip.mind_nrealargs in
            Option.bind
              (case_predicate_type infos ci u params predicate indices subject subst)
              (fun typ -> eliminate typ (Some (zip subject [frame])) stack)
        | _ -> None)
    | (Zfix _ | Zprimitive _) :: _ -> None
  in
  eliminate typ subject stack

(* Whether quoting [root] takes fewer than [remaining] syntax nodes (charged
   as it goes), so that a type witness is only quoted when small. *)
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

(* Run [inspect] on private copies of [typ], [stack] and [subject]: no cell of
   the caller is forced or updated, and copying and head steps share one
   budget. Update frames are dropped; a suspended case frame becomes a root of
   the view (its placeholder subject is never typed). *)
let with_type_snapshot ?subject infos typ stack inspect =
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
      collect (size + 1) ([zip (inject (mkRel 1)) [frame]] :: arrays) rest
    | (Zfix _ | Zprimitive _) :: _ -> None
  in
  Option.bind (collect (if Option.has_some subject then 2 else 1) [] stack) (fun arguments ->
    let roots = typ :: Option.List.cons subject arguments in
    with_private_closure_query ~steps:limit infos.cnv_inf roots (fun cnv_inf copies ->
      let typ, subject, copies = match subject, copies with
        | None, typ :: copies -> typ, None, copies
        | Some _, typ :: subject :: copies -> typ, Some subject, copies
        | _, [] | Some _, [_] -> assert false in
      let rec rebuild copies = function
        | [] -> assert (List.is_empty copies); []
        | Zupdate _ :: rest -> rebuild copies rest
        | Zapp args :: rest ->
          let args, copies = List.chop (Array.length args) copies in
          Zapp (Array.of_list args) :: rebuild copies rest
        | (Zshift _ | Zproj _) as frame :: rest -> frame :: rebuild copies rest
        | ZcaseT _ :: rest ->
          begin match copies with
          | case :: copies ->
            begin match fterm_of case with
            | FCaseT (ci, u, params, predicate, _, branches, subst) ->
              ZcaseT (ci, u, params, predicate, branches, subst) :: rebuild copies rest
            | _ -> assert false
            end
          | [] -> assert false
          end
        | (Zfix _ | Zprimitive _) :: _ -> assert false
      in
      inspect { infos with cnv_inf } typ (rebuild copies stack) subject))

(* Unit eta also applies under projections, not under cases and fixpoints. *)
let rec unit_like_stack = function
  | [] -> true
  | (Zapp _ | Zproj _ | Zshift _ | Zupdate _) :: stack -> unit_like_stack stack
  | (ZcaseT _ | Zfix _ | Zprimitive _) :: _ -> false

(* Reduction of a type with the caller's and the oracle's transparency:
   beta/iota/zeta alone stops at a transparent constant in the discriminant
   of a type-level match. *)
let unit_type_reduction_infos infos =
  let allowed = RedFlags.red_transparent (info_flags infos.cnv_inf) in
  let oracle = Conv_oracle.get_transp_state (oracle_of_infos infos.cnv_inf) in
  let transparency = TransparentState.{
    tr_var = Id.Pred.inter allowed.tr_var oracle.tr_var;
    tr_cst = Cpred.inter allowed.tr_cst oracle.tr_cst;
    tr_prj = PRpred.inter allowed.tr_prj oracle.tr_prj;
  } in
  infos_with_reds infos.cnv_inf (RedFlags.red_add_transparent RedFlags.all transparency)

(* The unit-like inductive of a type: a registered one, or a record with eta
   whose fields are all irrelevant or unit-like at these parameters (ULift
   (PLift P) is, ULift nat is not). Only field types are inspected, with a
   bounded number of head reductions and a separate table. *)
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
      (* the alias and projection steps below must not update shared cells *)
      let stack = List.filter (function Zupdate _ -> false | _ -> true) stack in
      if not (unit_like_stack stack) then None
      else match fterm_of typ with
      | FFlex (ConstKey (constant, _) as flex) ->
        let oracle = oracle_of_infos infos.cnv_inf in
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
                (* a dependent field would see a dummy record *)
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

(* The unit-like inductive of the type of a head of type [typ] under [stack]. *)
let unit_like_after_stack infos typ stack =
  with_type_snapshot infos typ stack (fun infos typ stack _ ->
    if not (unit_like_stack stack) then None
    else
      type_after_stack ~aliases:infos.cnv_inf ~classify:(unit_like_type infos)
        (infos_with_reds infos.cnv_inf RedFlags.betaiotazeta) (create_tab ()) typ stack)

(* Declared type of a flex; the index of a RelKey is already relocated. *)
let flex_type infos = function
  | RelKey n -> rel_type infos n
  | VarKey id ->
    let decl = Environ.lookup_named id (info_env infos.cnv_inf) in
    Some (inject (Context.Named.Declaration.get_type decl))
  | ConstKey (c, u) ->
    let cb = Environ.lookup_constant c (info_env infos.cnv_inf) in
    Some (mk_clos (subs_id 0, u) cb.const_type)

let unit_like_of_rel infos n stack =
  if not (unit_like_stack stack) then None
  else Option.bind (rel_type infos n) (fun typ -> unit_like_after_stack infos typ stack)

let unit_like_of_flex infos lft stack fl =
  if not (unit_like_stack stack) then None
  else
    let fl = match fl with
      | RelKey n -> RelKey (reloc_rel n (el_stack lft stack))
      | VarKey _ | ConstKey _ -> fl in
    Option.bind (flex_type infos fl) (fun typ -> unit_like_after_stack infos typ stack)

(* Both operands classified in the same unit-like family. *)
let same_unit_like ind1 ind2 = match ind1 with
  | Some ind1 -> Option.cata (Ind.UserOrd.equal ind1) false (ind2 ())
  | None -> false

let rel_has_unit_like infos lft (hd, stack) ind =
  match fterm_of hd with
  | FRel n ->
    let n = reloc_rel n (el_stack lft stack) in
    Option.cata (Ind.UserOrd.equal ind) false (unit_like_of_rel infos n stack)
  | _ -> false

(* Relocate a type or an argument by [lift] into the current context: quoted
   when its syntax is small (charged to [remaining]); a uniform shift of a
   closure or of an inversion subject stays lazy; anything else is
   inconclusive. *)
let relocate_unit_type infos remaining lift term =
  if is_lift_id lift then Some term
  else if small_reification remaining term then
    Some (mk_clos (subs_id (Range.length infos.cnv_rel_types), UVars.Instance.empty)
      (Vars.exliftn lift (term_of_fconstr term)))
  else match lift, fterm_of term with
    | ELSHFT (ELID, n), FCLOS (body, (subst, u)) ->
      Some (mk_clos (subs_shft (n, subst), u) body)
    | ELSHFT (ELID, n), FCaseInvert _ -> Some (zip term [Zshift n])
    | _ -> None

(* The type of [subject] (of type [typ] under [type_lift]) applied to [stack]
   under [lift], in the current context; [None] when the interface is too
   large to relocate. The quotation budget is separate from the stack budget:
   an unchanged argument or a delayed shift must not depend on it. *)
let unit_type_after_stack infos lift type_lift typ stack subject =
  let remaining = ref 4096 in
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
      with_type_snapshot ~subject infos typ stack (fun infos typ stack subject ->
        type_after_stack ?subject ~classify:(fun typ -> Some typ)
          (unit_type_reduction_infos infos) (create_tab ()) typ stack)))

let neutral_type_witness infos lift stack flex =
  let typ = match flex with
    | RelKey n -> rel_type_lifted infos (reloc_rel n (el_stack lift stack))
    | VarKey _ | ConstKey _ -> Option.map (fun typ -> el_id, typ) (flex_type infos flex)
  in
  let subject = match flex with
    | RelKey n -> mkRel (reloc_rel n (el_stack lift stack))
    | VarKey id -> mkVar id
    | ConstKey constant -> mkConstU constant in
  let subject =
    mk_clos (subs_id (Range.length infos.cnv_rel_types), UVars.Instance.empty) subject in
  Option.bind typ (fun (type_lift, typ) ->
    unit_type_after_stack infos lift type_lift typ stack subject)

(* The type of an operand of the conversion, in the current context, when it
   is a neutral term, a full unit-like constructor or a stuck inversion. *)
let unit_operand_type infos lift (head, stack) =
  let type_of_head infos head stack = match fterm_of head with
  | FFlex flex -> neutral_type_witness infos lift stack flex
  | FRel n -> neutral_type_witness infos lift stack (RelKey n)
  | FConstruct (((ind, constructor), u), args)
    when is_registered_unit_like (info_env infos.cnv_inf) ind ->
    let mib = Environ.lookup_mind (fst ind) (info_env infos.cnv_inf) in
    let nparams = mib.mind_nparams in
    let nfields = mib.mind_packets.(snd ind).mind_consnrealargs.(0) in
    (* a partial constructor is a function, even of irrelevant fields *)
    if constructor <> 1 || Array.length args <> nparams + nfields ||
       not (is_empty_stack stack) then None
    else
      let typ = zip (inject (mkIndU (ind, u))) [Zapp (Array.sub args 0 nparams)] in
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
    (* Opacity of a projection does not hide its declared field type: expose
       the neutral record under the projections in a private view, keeping
       the projections for the type instead of reducing their values. *)
    with_type_snapshot infos head stack (fun infos head stack _ ->
      let reds = infos_with_reds infos.cnv_inf RedFlags.betazeta in
      let tab = create_tab () in
      let rec spine fuel head stack =
        if fuel = 0 then None else
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

(* A projection or a case on the stack: the type needs the actual subject. *)
let has_type_elimination_stack stack =
  let rec inspect remaining = function
    | [] -> false
    | _ when remaining = 0 -> false
    | (Zproj _ | ZcaseT _) :: _ -> true
    | _ :: rest -> inspect (remaining - 1) rest in
  inspect 4096 stack

(* The inductive type of a flex under [stack], with the caller's transparency. *)
let flex_inductive infos lft stack fl =
  let fl = match fl with
    | RelKey n -> RelKey (reloc_rel n (el_stack lft stack))
    | VarKey _ | ConstKey _ -> fl in
  let all = RedFlags.(red_add_transparent all (red_transparent (info_flags infos.cnv_inf))) in
  Option.bind (flex_type infos fl) (fun typ ->
    try with_type_snapshot infos typ stack (fun infos typ stack _ ->
      type_after_stack ~classify:direct_inductive
        (infos_with_reds infos.cnv_inf all) (create_tab ()) typ stack)
    with Not_found | Assert_failure _ -> None)

let flex_has_inductive infos lft stack fl ind =
  Option.cata (Ind.UserOrd.equal ind) false (flex_inductive infos lft stack fl)

let flex_has_unit_like infos lft stack fl ind =
  Option.cata (Ind.UserOrd.equal ind) false (unit_like_of_flex infos lft stack fl)

(* Unfolding preferences of two flexes, read-only. *)

(* A direct alias of the other head, or the same constant with syntactically
   the same arguments: its major premise is not evaluated before unfolding. *)
let preserve_symbolic_arguments env lft1 fl1 v1 lft2 fl2 v2 =
  direct_head_alias env fl1 fl2 || direct_head_alias env fl2 fl1 ||
  (match fl1, fl2 with
   | ConstKey (c1, _), ConstKey (c2, _) when Constant.UserOrd.equal c1 c2 ->
     syntactically_same_arguments lft1 v1 lft2 v2
   | _ -> false)

(* The same eliminator with syntactically the same major on both sides. *)
let shared_major infos lft1 fl1 v1 lft2 fl2 v2 =
  match fl1, fl2 with
  | ConstKey (c1, u1), ConstKey (c2, u2)
    when Constant.UserOrd.equal c1 c2 && UVars.Instance.equal u1 u2 ->
    begin match eliminator_major infos fl1 with
    | Some index ->
      begin match stack_argument lft1 index v1, stack_argument lft2 index v2 with
      | Some (lift1, major1), Some (lift2, major2) -> fast_test lift1 major1 lift2 major2
      | _ -> false
      end
    | None -> false
    end
  | _ -> false

(* An expandable definition unfolds before its arguments are compared: a
   recursor wrapper must expose its subject before its branches. *)
let expand_before_arguments infos = function
  | ConstKey (c, _) when infos.cnv_typ && dep_heuristic infos ->
    oracle_expands infos c && Option.has_some (definition_body infos c)
  | _ -> false

(* A projection of a transparent wrapper may discard the wrapper's parameters:
   the field is exposed before congruence compares them. *)
let projection_before_congruence infos lft1 fl1 v1 lft2 fl2 v2 =
  applied_projection_source infos fl1 v1 || applied_projection_source infos fl2 v2 ||
  (not (bare_projection_stack v1) && projected_record_wrapper infos fl1 v1) ||
  (not (bare_projection_stack v2) && projected_record_wrapper infos fl2 v2) ||
  (bare_projection_stack v1 && bare_projection_stack v2 &&
   same_forwarded_projection_source infos lft1 fl1 v1 lft2 fl2 v2)

let unfoldable infos = function
  | ConstKey (c, _) -> Option.has_some (definition_body infos c)
  | RelKey _ | VarKey _ -> false

let is_constructor_head infos tab argument =
  let head, _ = whd_stack (infos_with_reds infos.cnv_inf RedFlags.betazeta) tab argument [] in
  match fterm_of head with FConstruct _ | FPeanoNat _ -> true | _ -> false

let has_constructor_argument infos tab stack =
  List.exists (function
    | Zapp args -> Array.exists (is_constructor_head infos tab) args
    | Zupdate _ | Zshift _ | Zproj _ | Zfix _ | ZcaseT _ | Zprimitive _ -> false) stack

(* The side whose arguments hold a constructor, when only one does; for the
   same head with constructors on both, the side whose rightmost differing
   argument is a constructor. *)
let constructor_argument_side infos ~same_reference v1 v2 =
  if infos.cnv_strategy.constructor_relevance && not same_reference then None
  else
    let constructor1 = has_constructor_argument infos infos.lft_tab v1 in
    let constructor2 = has_constructor_argument infos infos.rgt_tab v2 in
    if constructor1 <> constructor2 then Some constructor1
    else if not constructor1 || not same_reference then None
    else
      let rec prefix arrays = function
        | Zapp args :: stack -> prefix (args :: arrays) stack
        | (Zshift _ | Zupdate _) :: stack -> prefix arrays stack
        | _ -> Array.concat (List.rev arrays)
      in
      let args1 = prefix [] v1 and args2 = prefix [] v2 in
      if Array.is_empty args1 || not (Int.equal (Array.length args1) (Array.length args2))
      then None
      else
        let rec rightmost index =
          if index < 0 then None
          else
            let left = is_constructor_head infos infos.lft_tab args1.(index) in
            let right = is_constructor_head infos infos.rgt_tab args2.(index) in
            if left <> right then Some left else rightmost (index - 1)
        in
        rightmost (Array.length args1 - 1)

(* Whether [target] occurs in the process [term] under [stack], directly or,
   with [transitive], through the dependencies of the constants it mentions.
   Substitutions are inspected, nothing is quoted, reduced or updated; an
   unsupported cell or an exhausted budget is inconclusive. *)
let depends_on infos ~transitive term stack target =
  let exception Found in
  let exception Unknown in
  let remaining = ref 1024 in
  let updates = ref [] in
  let visit () = if Int.equal !remaining 0 then raise Unknown; decr remaining in
  let constant c =
    if Constant.UserOrd.equal c target then raise Found;
    if transitive then
      match Environ.constant_depends_on ~fuel:remaining (info_env infos.cnv_inf) c target with
      | Some true -> raise Found
      | Some false -> ()
      | None -> raise Unknown
  in
  let binder depth = visit (); depth + 1 in
  let rec syntax ~aliases_only subst depth term =
    visit ();
    match Constr.kind term with
    | Rel index when index > depth ->
      Option.iter (fun subst ->
        match inspect_substituted_rel subst (index - depth) with
        | Some term -> closure ~aliases_only term
        | None -> raise Unknown) subst
    | Const (c, _) -> if not aliases_only then constant c
    | _ -> Constr.iter_with_binders binder (syntax ~aliases_only subst) depth term
  and closure ~aliases_only term =
    visit ();
    (* an update frame may change a cell aliased by a later argument *)
    if aliases_only && List.memq term !updates then raise Unknown;
    match fterm_of term with
    | FFlex (ConstKey (c, _)) -> if not aliases_only then constant c
    | FRel _ | FFlex (RelKey _ | VarKey _) | FInd _ | FInt _ | FFloat _ | FString _ -> ()
    | FAtom term -> if not aliases_only then syntax ~aliases_only None 0 term
    | FConstruct (_, args) -> Array.iter (closure ~aliases_only) args
    | FApp (head, args) -> closure ~aliases_only head; Array.iter (closure ~aliases_only) args
    | FProj (_, _, term) | FLIFT (_, term) -> closure ~aliases_only term
    | FCLOS (term, subst) when is_subs_id (fst subst) ->
      if not aliases_only then syntax ~aliases_only None 0 term
    | FCLOS (term, subst) -> syntax ~aliases_only (Some subst) 0 term
    | FLambda (len, domains, body, subst) ->
      let subst = if is_subs_id (fst subst) then None else Some subst in
      if not aliases_only || Option.has_some subst then begin
        let rec inspect depth = function
          | [] ->
            if not (Int.equal depth len) then raise Unknown;
            syntax ~aliases_only subst len body
          | (_, domain) :: rest ->
            visit ();
            syntax ~aliases_only subst depth domain;
            inspect (binder depth) rest
        in
        inspect 0 domains
      end
    | FFix _ | FCoFix _ | FCaseT _ | FCaseInvert _ | FProd _ | FLetIn _ | FEvar _
    | FArray _ | FPeanoNat _ | FIrrelevant | FLOCKED -> raise Unknown
  in
  let rec frames ~aliases_only = function
    | [] -> ()
    | frame :: rest ->
      visit ();
      (match frame with
       | Zapp args -> Array.iter (closure ~aliases_only) args
       | Zproj _ | Zshift _ | Zupdate _ -> ()
       | Zfix _ | ZcaseT _ | Zprimitive _ -> raise Unknown);
      frames ~aliases_only rest
  in
  let rec collect_updates = function
    | [] -> ()
    | frame :: rest ->
      visit ();
      (match frame with
       | Zapp _ | Zproj _ | Zshift _ -> ()
       | Zupdate target ->
         if List.memq target !updates then raise Unknown;
         updates := target :: !updates
       | Zfix _ | ZcaseT _ | Zprimitive _ -> raise Unknown);
      collect_updates rest
  in
  try
    collect_updates stack;
    if not (List.is_empty !updates) then begin
      closure ~aliases_only:true term;
      frames ~aliases_only:true stack
    end;
    closure ~aliases_only:false term;
    frames ~aliases_only:false stack;
    Some false
  with
  | Found -> Some true
  | Unknown | Assert_failure _ -> None

(* The side whose unfolded application depends on the other head; a
   transitive dependency with an unknown converse must be confirmed by a
   direct occurrence, lest it divert conversion into arithmetic. *)
let dependency_side infos ~transitive fl1 t1 v1 fl2 t2 v2 =
  if not infos.cnv_strategy.dependency_preference then None
  else match fl1, fl2 with
  | ConstKey (c1, _), ConstKey (c2, _) ->
    let left = depends_on infos ~transitive t1 v1 c2 in
    let right = depends_on infos ~transitive t2 v2 c1 in
    (match left, right with
     | Some left, Some right when not (Bool.equal left right) -> Some left
     | Some true, None when depends_on infos ~transitive:false t1 v1 c2 = Some true -> Some true
     | None, Some true when depends_on infos ~transitive:false t2 v2 c1 = Some true -> Some false
     | _ -> None)
  | (ConstKey _ | VarKey _ | RelKey _), _ -> None

(* The registered compact Peano operations, which the reduction machine
   evaluates on compact naturals. *)
let compact_peano_operations env =
  let open! Retroknowledge in
  let retro = Environ.retroknowledge env in
  List.concat_map (fun (s : peano_nat) ->
    List.filter_map (fun c -> c)
      [s.peano_double; s.peano_add; s.peano_mul; s.peano_pow; s.peano_sub]
    @ s.peano_div_go @ s.peano_mod_go
    @ List.map (fun d -> d.decoder_constant) s.peano_decoders) retro.retro_peano_nat
  @ List.map (fun op -> op.bool_op_constant) (retro.retro_peano_nat_beq @ retro.retro_peano_nat_ble)

let is_compact_peano_operation infos constant =
  List.exists (Constant.UserOrd.equal constant) (compact_peano_operations (info_env infos.cnv_inf))

(* [constant] is, or depends on, a compact operation; an exhausted search is
   no evidence. *)
let backed_by_compact_operation ~fuel env constant =
  List.exists (fun operation ->
    Constant.UserOrd.equal constant operation ||
    Environ.constant_depends_on ~fuel env constant operation = Some true)
    (compact_peano_operations env)

(* An inductive with two constructors of one Peano argument each (integers). *)
let is_compact_peano_wrapper env ind =
  let retro = Environ.retroknowledge env in
  let is_peano_type typ =
    match Constr.kind (fst (Constr.decompose_app typ)) with
    | Ind (candidate, _) ->
      List.exists (fun s -> Ind.UserOrd.equal candidate s.Retroknowledge.peano_inductive)
        retro.Retroknowledge.retro_peano_nat
    | _ -> false
  in
  try
    let mib, mip = Inductive.lookup_mind_specif env ind in
    Int.equal (Array.length mib.mind_packets) 1 && Int.equal mib.mind_nparams 0 &&
    Int.equal (Array.length mip.mind_consnames) 2 &&
    Array.for_all (Int.equal 1) mip.mind_consnrealargs &&
    Array.for_all (fun (context, _) -> match context with
      | [declaration] -> is_peano_type (Context.Rel.Declaration.get_type declaration)
      | _ -> false) mip.mind_nf_lc
  with Not_found -> false

(* The unfolded application is a fixpoint eliminating a compact natural. *)
let compact_elimination infos tab term stack =
  let head, stack = whd_stack (infos_with_reds infos.cnv_inf RedFlags.betazeta) tab term stack in
  match fterm_of head, stack with
  | FPeanoNat _, Zfix _ :: _ -> true
  | _ -> false

(* Whether the process [term] under [stack] is closed and mentions a constant
   backed by a compact operation. Substitutions are inspected, nothing is
   quoted, reduced or updated; an unsupported cell, an aliased update or an
   exhausted budget declines. *)
let closed_compact_process infos term stack =
  let exception Unknown in
  let remaining = ref 1024 in
  let updates = ref [] in
  let constants = ref [] in
  let visit () = if Int.equal !remaining 0 then raise Unknown; decr remaining in
  let binder depth = visit (); depth + 1 in
  let rec syntax subst depth term =
    visit ();
    match Constr.kind term with
    | Rel index when index > depth ->
      (match Option.bind subst (fun subst -> inspect_substituted_rel subst (index - depth)) with
       | Some term -> closure term
       | None -> raise Unknown)
    | Const (c, _) -> constants := c :: !constants
    | Evar _ -> raise Unknown
    | _ -> Constr.iter_with_binders binder (syntax subst) depth term
  and closure term =
    visit ();
    if List.memq term !updates then raise Unknown;
    match fterm_of term with
    | FFlex (ConstKey (c, _)) -> constants := c :: !constants
    | FFlex (VarKey _) | FInd _ | FInt _ | FFloat _ | FString _ | FPeanoNat _ -> ()
    | FAtom term -> syntax None 0 term
    | FConstruct (_, args) -> Array.iter closure args
    | FApp (head, args) -> closure head; Array.iter closure args
    | FProj (_, _, term) | FLIFT (_, term) -> closure term
    | FCLOS (term, subst) -> syntax (Some subst) 0 term
    | FLambda (len, domains, body, subst) ->
      let rec inspect depth = function
        | [] ->
          if not (Int.equal depth len) then raise Unknown;
          syntax (Some subst) len body
        | (_, domain) :: rest ->
          visit ();
          syntax (Some subst) depth domain;
          inspect (binder depth) rest
      in
      inspect 0 domains
    | FRel _ | FFlex (RelKey _) | FFix _ | FCoFix _ | FCaseT _ | FCaseInvert _ | FProd _
    | FLetIn _ | FEvar _ | FArray _ | FIrrelevant | FLOCKED -> raise Unknown
  in
  let rec collect_updates = function
    | [] -> ()
    | frame :: rest ->
      visit ();
      (match frame with
       | Zapp _ | Zproj _ | Zshift _ -> ()
       | Zupdate target ->
         if List.memq target !updates then raise Unknown;
         updates := target :: !updates
       | Zfix _ | ZcaseT _ | Zprimitive _ -> raise Unknown);
      collect_updates rest
  in
  let rec frames = function
    | [] -> ()
    | frame :: rest ->
      visit ();
      (match frame with
       | Zapp args -> Array.iter closure args
       | Zproj _ | Zshift _ | Zupdate _ -> ()
       | Zfix _ | ZcaseT _ | Zprimitive _ -> raise Unknown);
      frames rest
  in
  try
    collect_updates stack;
    closure term;
    frames stack;
    (* the dependency queries run once the process is known to be closed *)
    let fuel = ref 16_384 in
    List.exists (backed_by_compact_operation ~fuel (info_env infos.cnv_inf)) (List.rev !constants)
  with Unknown | Assert_failure _ -> false

(* Two closed applications of different constants that are compact operations,
   or are backed by them and return the same wrapper of a Peano type (an
   operation behind a projection), neither eliminating a compact natural nor
   depending on the other: reduced independently to weak-head form instead of
   being unfolded alternately (2 * 2^31 against 2^32). *)
let independent_compact_applications infos ~compact:(compact1, compact2)
    lft1 fl1 t1 s1 lft2 fl2 t2 s2 =
  let env = info_env infos.cnv_inf in
  dep_heuristic infos &&
  match fl1, fl2 with
  | ConstKey (c1, _), ConstKey (c2, _) when not (Constant.UserOrd.equal c1 c2) ->
    let closed_wrapper_results () =
      closed_compact_process infos t1 s1 && closed_compact_process infos t2 s2 &&
      match flex_inductive infos lft1 s1 fl1, flex_inductive infos lft2 s2 fl2 with
      | Some ind1, Some ind2 when Ind.UserOrd.equal ind1 ind2 -> is_compact_peano_wrapper env ind1
      | _ -> false
    in
    ((is_compact_peano_operation infos c1 && is_compact_peano_operation infos c2) ||
     closed_wrapper_results ()) &&
    not (compact1 || compact2) &&
    (let fuel = ref 16_384 in
     match Environ.constant_depends_on ~fuel env c1 c2,
           Environ.constant_depends_on ~fuel env c2 c1 with
     | Some false, Some false -> true
     | _ -> false)
  | _ -> false

(* Which side to unfold when both do, [t1] under [s1] and [t2] under [s2]
   being the unfolded applications and [eliminates] telling which original
   application eliminates a constructor: that side, unless the other is a
   direct alias of its head; then a projected record wrapper on one side
   only; then the oracle and the dependencies. *)
let unfolding_action infos l2r ~eliminates:(constructor1, constructor2) ~compact
    fl1 (t1, s1) fl2 (t2, s2) =
  let env = info_env infos.cnv_inf in
  if constructor1 <> constructor2 then
    if constructor1 && direct_head_alias env fl2 fl1 then Unfold_right
    else if constructor2 && direct_head_alias env fl1 fl2 then Unfold_left
    else unfolding_side constructor1
  else
  let wrapper1 = projected_record_wrapper infos fl1 s1 in
  let wrapper2 = projected_record_wrapper infos fl2 s2 in
  if wrapper1 <> wrapper2 then unfolding_side wrapper1 else
  let reference = function
    | ConstKey (c, _) -> Some (Conv_oracle.EvalConstRef c)
    | VarKey id -> Some (Conv_oracle.EvalVarRef id)
    | RelKey _ -> None
  in
  let order =
    Conv_oracle.oracle_compare (oracle_of_infos infos.cnv_inf) (reference fl1) (reference fl2) in
  let same_reference = match fl1, fl2 with
    | ConstKey (c1, _), ConstKey (c2, _) -> Constant.UserOrd.equal c1 c2
    | VarKey id1, VarKey id2 -> Id.equal id1 id2
    | RelKey n1, RelKey n2 -> Int.equal n1 n2
    | (ConstKey _ | VarKey _ | RelKey _), _ -> false
  in
  let global_constants = match fl1, fl2 with ConstKey _, ConstKey _ -> true | _ -> false in
  choose_unfolding_action ~order ~l2r ~heuristic:(global_constants && dep_heuristic infos) ~compact
    ~direct_dependency:(fun () -> dependency_side infos ~transitive:false fl1 t1 s1 fl2 t2 s2)
    ~dependency:(fun () -> dependency_side infos ~transitive:true fl1 t1 s1 fl2 t2 s2)
    ~constructor:(fun () -> constructor_argument_side infos ~same_reference s1 s2)

(* For [f args .field more_args], the source [f args] is compared before the
   arguments of the projected field, which delta may discard: arguments are
   still compared right to left within a segment, but a projection is not
   crossed before its source segment succeeded. *)
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
  let probe = infos.cnv_probe in
  Option.iter (fun { work; _ } ->
    if Int.equal !work 0 then raise Probe_budget_exhausted;
    decr work) probe;
  let compare () =
    match symbolic_congruence cv_pb l2r infos lft1 lft2 term1 term2 cuniv with
    | Some cuniv -> cuniv
    | None -> eqappr cv_pb l2r infos (lft1, (term1,[])) (lft2, (term2,[])) cuniv in
  let compare () = match probe with
    | None -> compare ()
    | Some { depth; _ } ->
      if Int.equal !depth 0 then raise Probe_budget_exhausted;
      decr depth;
      Fun.protect compare ~finally:(fun () -> incr depth) in
  match infos.cnv_memo with
  | None -> if fast_test lft1 term1 lft2 term2 then cuniv else compare ()
  | Some memo ->
    (* the memo of cells before the syntactic test: it answers most repeated
       comparisons at once; the suspended syntax is captured before reduction
       overwrites the cells *)
    let site = { left_lift = lft1; right_lift = lft2; ctx = infos.cnv_ctx } in
    if Memo.cached memo cv_pb site term1 term2 || fast_test lft1 term1 lft2 term2 then cuniv
    else
      let suspended = Memo.suspended_key term1 term2 in
      if Option.cata (suspended_cached memo cv_pb site) false suspended then cuniv
      else
        let cuniv = compare () in
        Memo.remember memo cv_pb site term1 term2;
        Option.iter (Memo.remember_suspended memo cv_pb site) suspended;
        cuniv

(* Two cells whose spines before reduction are headed by flexes (see
   [CClosure.symbolic_view]) are first compared by symbolic reduction, under
   a budget: the spines may be congruent while the values are large. A failure
   or exhaustion is remembered by site and certifies nothing. *)
and symbolic_congruence cv_pb l2r infos lft1 lft2 term1 term2 cuniv =
  if not infos.cnv_typ || Option.has_some infos.cnv_symbolic ||
     !(infos.cnv_symbolic_total) = 0 || not (dep_heuristic infos) then None
  else
    let site = { left_lift = lft1; right_lift = lft2; ctx = infos.cnv_ctx } in
    if Sites.cached infos.cnv_symbolic_misses term1 term2 site then None else
    match symbolic_view term1, symbolic_view term2 with
    | Some left, Some right when left != term1 || right != term2 ->
      let infos' = { infos with cnv_inf = infos_with_symbolic_views infos.cnv_inf;
                                cnv_symbolic = Some (ref 4096) } in
      (try Some (eqappr cv_pb l2r infos' (lft1, (left, [])) (lft2, (right, [])) cuniv)
       with Symbolic_budget_exhausted | NotConvertible | NotConvertibleTrace _ ->
         Sites.remember infos.cnv_symbolic_misses term1 term2 site; None)
    | _ -> None

(* Conversion between [lft1](hd1 v1) and [lft2](hd2 v2) *)
and eqappr cv_pb l2r infos (lft1,st1) (lft2,st2) cuniv =
  Control.check_for_interrupt ();
  (* First head reduce both terms *)
  let ninfos = infos_with_reds infos.cnv_inf RedFlags.betaiotazeta in
  let appr1 = whd_stack ninfos infos.lft_tab (fst st1) (snd st1) in
  let appr2 = whd_stack ninfos infos.rgt_tab (fst st2) (snd st2) in
  eqwhnf cv_pb l2r infos (lft1, appr1) (lft2, appr2) cuniv

(* Two projections of the same field: the sources are compared while they
   are applications of constants (by congruence, then by unfolding the side
   the oracle prefers) and the fields are selected as soon as a constructor
   is exposed, so that unrelated fields of an exposed record are not
   compared. Masks are restricted to typed conversions. *)
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
  let frames =
    match unfold_projection infos.cnv_inf p1 r1, unfold_projection infos.cnv_inf p2 r2 with
    | Some frame1, Some frame2 -> Some (frame1, frame2)
    | _ -> None in
  let rec drive (h1, s1) (h2, s2) =
    Control.check_for_interrupt ();
    charge_step infos;
    let h1, s1 = whd_stack ninfos infos.lft_tab h1 s1 in
    let h2, s2 = whd_stack ninfos infos.rgt_tab h2 s2 in
    let selected_fields () =
      Option.map (fun (frame1, frame2) ->
        eqappr cv_pb l2r infos (lft1, (h1, s1 @ [frame1])) (lft2, (h2, s2 @ [frame2])) cuniv)
        frames in
    let remaining_sources () =
      try Some (eqappr CONV l2r infos (lft1, (h1, s1)) (lft2, (h2, s2)) cuniv)
      with NotConvertible | NotConvertibleTrace _ -> None in
    match fterm_of h1, fterm_of h2 with
    | FFlex fl1, FFlex fl2 when application_stack s1 && application_stack s2 ->
      let congruence () =
        if not (regular fl1 && regular fl2) ||
           Option.cata (fun (frame1, frame2) ->
             same_forwarded_projection_source infos
               lft1 fl1 (s1 @ [frame1]) lft2 fl2 (s2 @ [frame2])) false frames
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
  let env = info_env infos.cnv_inf in
  charge_step infos;
  let unit_eta () = unit_eta l2r infos appr1 appr2 cuniv in
  let unit_eta_exn () = match unit_eta () with
    | Some cuniv -> cuniv
    | None -> raise NotConvertible
  in
  (* Eta of a record constructor, on the [left] or the right of [other]; a
     unit-like one compares by type instead when [unit] holds. *)
  let construct_eta ~left ?(unit = fun () -> true) (ind, u) args other =
    if is_registered_unit_like env ind && unit () then unit_eta_exn ()
    else
      try
        let vc, vo = eta_expand_ind_stack env (ind, u) args (snd other) in
        if left then convert_stacks l2r infos lft1 lft2 vc vo cuniv
        else convert_stacks l2r infos lft1 lft2 vo vc cuniv
      with Not_found -> raise NotConvertible
  in
  (* Whether the operand facing a unit-like constructor compares by type:
     always for typed terms, else when its type needs the subject or it is
     a variable of the same unit-like type. *)
  let unit_operand lft (hd, v) ind =
    infos.cnv_typ || has_type_elimination_stack v ||
    (match fterm_of hd with FCaseInvert _ -> true | _ -> false) ||
    rel_has_unit_like infos lft (hd, v) ind
  in
  (* A flex against a variable or a stuck inversion: units before unfolding. *)
  let flex_unit_eta flex_lft flex_v fl rel_lft rel_v = function
    | FRel n ->
      if has_type_elimination_stack v1 || has_type_elimination_stack v2 ||
         same_unit_like (unit_like_of_flex infos flex_lft flex_v fl)
           (fun () -> unit_like_of_rel infos (reloc_rel n (el_stack rel_lft rel_v)) rel_v)
      then unit_eta () else None
    | FCaseInvert _ -> unit_eta ()
    | _ -> None
  in
  (* A flex against a record constructor of its own type ([left] when the
     constructor is on the left): eta before unfolding, unless the flex is a
     constructor or projection wrapper. *)
  let eta_before_unfolding ~left lft v fl = function
    | FConstruct (((ind, 1), u), args)
      when not (record_wrapper infos fl v) && flex_has_inductive infos lft v fl ind ->
      let () = assert_reduced_constructor (if left then v1 else v2) in
      (try Some (construct_eta ~left
             ~unit:(fun () -> infos.cnv_typ || flex_has_unit_like infos lft v fl ind)
             (ind, u) args (if left then appr2 else appr1))
       with NotConvertible | NotConvertibleTrace _ -> None)
    | _ -> None
  in
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
        let el1 = el_stack lft1 v1 in
        let el2 = el_stack lft2 v2 in
        let n = reloc_rel n el1 in
        let m = reloc_rel m el2 in
        let rn = Range.get (info_relevances infos.cnv_inf) (n - 1) in
        let rm = Range.get (info_relevances infos.cnv_inf) (m - 1) in
        if is_irrelevant infos.cnv_inf rn && is_irrelevant infos.cnv_inf rm then
          let v1 = CClosure.skip_irrelevant_stack infos.cnv_inf v1 in
          let v2 = CClosure.skip_irrelevant_stack infos.cnv_inf v2 in
          convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
        else
          let same_unit () =
            if has_type_elimination_stack v1 || has_type_elimination_stack v2 ||
               same_unit_like (unit_like_of_rel infos n v1)
                 (fun () -> unit_like_of_rel infos m v2)
            then unit_eta () else None
          in
          if Int.equal n m then
            try convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
            with (NotConvertible | NotConvertibleTrace _) as error ->
              (match same_unit () with Some cuniv -> cuniv | None -> raise error)
          else
            (match same_unit () with Some cuniv -> cuniv | None -> raise NotConvertible)

    (* 2 constants, 2 local defined vars or 2 defined rels *)
    | (FFlex fl1, FFlex fl2) ->
      let key = Option.bind infos.cnv_memo (fun memo ->
        Option.map (fun key -> memo, key) (application_key infos lft1 lft2 fl1 v1 fl2 v2)) in
      if Option.cata (fun (memo, key) -> Memo.completed memo cv_pb key) false key then cuniv
      else
        let cuniv = eq_flex_flex cv_pb l2r infos appr1 appr2 fl1 fl2 cuniv in
        Option.iter (fun (memo, key) -> Memo.complete memo cv_pb key) key;
        cuniv

    (* A projection that does not unfold against a record constructor: eta *)
    | (FProj (p1, r1, c1), FConstruct (((ind2, 1), u2), args2))
      when infos.cnv_typ && is_eta_record env (ind2, u2) ->
      let () = assert_reduced_constructor v2 in
      begin match unfold_projection infos.cnv_inf p1 r1 with
      | Some s1 -> eqappr cv_pb l2r infos (lft1, (c1, s1 :: v1)) appr2 cuniv
      | None -> construct_eta ~left:false (ind2, u2) args2 appr1
      end

    | (FConstruct (((ind1, 1), u1), args1), FProj (p2, r2, c2))
      when infos.cnv_typ && is_eta_record env (ind1, u1) ->
      let () = assert_reduced_constructor v1 in
      begin match unfold_projection infos.cnv_inf p2 r2 with
      | Some s2 -> eqappr cv_pb l2r infos appr1 (lft2, (c2, s2 :: v2)) cuniv
      | None -> construct_eta ~left:true (ind1, u1) args1 appr2
      end

    | (FProj (p1,r1,c1), FProj (p2, r2, c2)) ->
      let same_projections =
        Projection.Repr.CanOrd.equal (Projection.repr p1) (Projection.repr p2) &&
        compare_stack_shape v1 v2
      in
      let el1 = el_stack lft1 v1 and el2 = el_stack lft2 v2 in
      let congruence () =
        let cuniv = ccnv CONV l2r infos el1 el2 c1 c2 cuniv in
        convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
      in
      (* The sources of the same field are compared before the projections
         unfold: lazily when bare, else by congruence for a unit-like record
         or, under the strategy, any record not yet a constructor. *)
      let lazy_sources () =
        if dep_heuristic infos && same_projections && is_empty_stack v1 && is_empty_stack v2
        then lazy_projection_sources cv_pb l2r infos el1 p1 r1 c1 el2 p2 r2 c2 cuniv
        else None
      in
      let congruence_first () =
        let unit_like =
          is_registered_unit_like env (Projection.Repr.inductive (Projection.repr p1)) in
        let of_constructor = match fterm_of c1, fterm_of c2 with
          | FConstruct _, _ | _, FConstruct _ -> true
          | _ -> false in
        if not (infos.cnv_typ && dep_heuristic infos && same_projections &&
                (unit_like || (infos.cnv_strategy.projection_congruence && not of_constructor)))
        then None
        else
          try
            let site = { left_lift = el1; right_lift = el2; ctx = infos.cnv_ctx } in
            let cuniv =
              if Sites.cached infos.cnv_projections c1 c2 site then cuniv
              else begin
                let cuniv = ccnv CONV l2r infos el1 el2 c1 c2 cuniv in
                Sites.remember infos.cnv_projections c1 c2 site;
                cuniv
              end
            in
            Some (convert_stacks l2r infos lft1 lft2 v1 v2 cuniv)
          with NotConvertible | NotConvertibleTrace _ -> None
      in
      begin match (match lazy_sources () with
        | Some _ as result -> result
        | None -> congruence_first ()) with
      | Some cuniv -> cuniv
      | None ->
      (* Projections: prefer unfolding to first-order unification,
         which will happen naturally if the terms c1, c2 are not in constructor
         form *)
      match unfold_projection infos.cnv_inf p1 r1 with
      | Some s1 ->
        eqappr cv_pb l2r infos (lft1, (c1, (s1 :: v1))) appr2 cuniv
      | None ->
        match unfold_projection infos.cnv_inf p2 r2 with
        | Some s2 ->
          eqappr cv_pb l2r infos appr1 (lft2, (c2, (s2 :: v2))) cuniv
        | None ->
          if same_projections then congruence ()
          else (* Two projections in WHNF: unfold *)
            raise NotConvertible
      end

    (* An expandable constant against a projection unfolds first *)
    | (FProj _, FFlex (ConstKey (c2, _) as fl2)) when oracle_expands infos c2 ->
      begin match unfold_ref_with_args infos.cnv_inf infos.rgt_tab fl2 v2 with
      | Some t2 -> eqappr cv_pb l2r infos appr1 (lft2, t2) cuniv
      | None -> raise NotConvertible
      end

    | (FFlex (ConstKey (c1, _) as fl1), FProj _) when oracle_expands infos c1 ->
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
        let (x1,ty1,bd1) = lft_cells infos (fun () -> destFLambda mk_clos hd1) in
        let (_,ty2,bd2) = rgt_cells infos (fun () -> destFLambda mk_clos hd2) in
        let el1 = el_stack lft1 v1 in
        let el2 = el_stack lft2 v2 in
        let cuniv = ccnv CONV l2r infos el1 el2 ty1 ty2 cuniv in
        ccnv CONV l2r (push_relevance ~typ:ty1 ~type_lift:el1 infos x1)
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
        ccnv cv_pb l2r (push_relevance ~typ:c1 ~type_lift:el1 infos x1)
          (el_lift el1) (el_lift el2)
          (lft_cells infos (fun () -> mk_clos (usubs_lift e) c2))
          (rgt_cells infos (fun () -> mk_clos (usubs_lift e') c'2)) cuniv

    (* Eta-expansion on the fly *)
    | (FLambda _, _) ->
        let () = match v1 with
        | [] -> ()
        | _ ->
          anomaly (Pp.str "conversion was given unreduced term (FLambda).")
        in
        let (x1,ty1,bd1) = lft_cells infos (fun () -> destFLambda mk_clos hd1) in
        let infos = push_relevance ~typ:ty1 ~type_lift:lft1 infos x1 in
        eqappr CONV l2r infos
          (el_lift lft1, (bd1, [])) (el_lift lft2, (hd2, eta_expand_stack infos.cnv_inf x1 v2)) cuniv
    | (_, FLambda _) ->
        let () = match v2 with
        | [] -> ()
        | _ ->
          anomaly (Pp.str "conversion was given unreduced term (FLambda).")
        in
        let (x2,ty2,bd2) = rgt_cells infos (fun () -> destFLambda mk_clos hd2) in
        let infos = push_relevance ~typ:ty2 ~type_lift:lft2 infos x2 in
        eqappr CONV l2r infos
          (el_lift lft1, (hd1, eta_expand_stack infos.cnv_inf x2 v1)) (el_lift lft2, (bd2, [])) cuniv

    | FCaseInvert _, FRel _ | FRel _, FCaseInvert _ -> unit_eta_exn ()

    (* only one constant, defined var or defined rel *)
    | (FFlex fl1, c2)      ->
      begin match flex_unit_eta lft1 v1 fl1 lft2 v2 c2 with
      | Some cuniv -> cuniv
      | None ->
      match eta_before_unfolding ~left:false lft1 v1 fl1 c2 with
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
          (match c2 with
           | FConstruct (((ind2, 1), u2), args2) ->
             let () = assert_reduced_constructor v2 in
             construct_eta ~left:false (ind2, u2) args2 appr1
           | _ -> raise NotConvertible)
      end

    | (c1, FFlex fl2)      ->
      begin match flex_unit_eta lft2 v2 fl2 lft1 v1 c1 with
      | Some cuniv -> cuniv
      | None ->
      match eta_before_unfolding ~left:true lft2 v2 fl2 c1 with
      | Some cuniv -> cuniv
      | None ->
      match unfold_ref_with_args infos.cnv_inf infos.rgt_tab fl2 v2 with
        | Some (def2, v2) ->
          (** Symmetrical case of above. *)
          let all = RedFlags.(red_add_transparent all (red_transparent (info_flags infos.cnv_inf))) in
          let r2 = whd_stack (infos_with_reds infos.cnv_inf all) infos.rgt_tab def2 v2 in
          eqwhnf cv_pb l2r infos appr1 (lft2, r2) cuniv
        | None ->
          match c1 with
          | FConstruct (((ind1, 1), u1), args1) ->
            let () = assert_reduced_constructor v1 in
            construct_eta ~left:true (ind1, u1) args1 appr2
          | _ -> raise NotConvertible
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
          if infos.cnv_typ && infos.cnv_strategy.constructor_relevance
          then constructor_mask infos pctor1 else [||]
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
      construct_eta ~left:true ~unit:(fun () -> unit_operand lft2 (hd2, v2) ind1)
        (ind1, u1) args1 appr2

    | (_, FConstruct (((ind2, j2), u2), args2)) ->
      let () = assert_reduced_constructor v2 in
      (* records only have 1 constructor *)
      let () = if not @@ Int.equal j2 1 then raise NotConvertible in
      construct_eta ~left:false ~unit:(fun () -> unit_operand lft1 (hd1, v1) ind2)
        (ind2, u2) args2 appr1

    | (FFix (((op1, i1),(na1,tys1,cl1)),e1), FFix(((op2, i2),(_,tys2,cl2)),e2)) ->
        if Int.equal i1 i2 && Array.equal Int.equal op1 op2
        then
          let n = Array.length cl1 in
          let fty1, fcl1 = lft_cells infos (fun () ->
            Array.map (mk_clos e1) tys1, Array.map (mk_clos (usubs_liftn n e1)) cl1) in
          let fty2, fcl2 = rgt_cells infos (fun () ->
            Array.map (mk_clos e2) tys2, Array.map (mk_clos (usubs_liftn n e2)) cl2) in
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
          let fty1, fcl1 = lft_cells infos (fun () ->
            Array.map (mk_clos e1) tys1, Array.map (mk_clos (usubs_liftn n e1)) cl1) in
          let fty2, fcl2 = rgt_cells infos (fun () ->
            Array.map (mk_clos e2) tys2, Array.map (mk_clos (usubs_liftn n e2)) cl2) in
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
      let pms1 = lft_cells infos (fun () -> mk_clos_vect e1 pms1) in
      let pms2 = rgt_cells infos (fun () -> mk_clos_vect e2 pms2) in
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

(* Unit-like operands are convertible when their types are. The type is
   certified again in the current context: the classifications of the cases
   of [eqwhnf] are only hints. *)
and unit_eta l2r infos (lft1, (hd1, v1)) (lft2, (hd2, v2)) cuniv =
  Option.bind (unit_operand_type infos lft1 (hd1, v1)) (fun typ1 ->
    Option.bind (unit_like_after_stack infos typ1 []) (fun _ ->
      Option.bind (unit_operand_type infos lft2 (hd2, v2)) (fun typ2 ->
        try Some (ccnv CONV l2r infos el_id el_id typ1 typ2 cuniv)
        with NotConvertible | NotConvertibleTrace _ -> None)))

(* Two flexes: congruence of the same head, then unit eta, then unfolding of
   the side chosen from the dependencies. *)
and eq_flex_flex cv_pb l2r infos (lft1, (hd1, v1)) (lft2, (hd2, v2)) fl1 fl2 cuniv =
  let env = info_env infos.cnv_inf in
  let preserve = preserve_symbolic_arguments env lft1 fl1 v1 lft2 fl2 v2 in
  (* the same eliminator on the same major selects the same branch: expose it *)
  let v1, v2 =
    if preserve || not (shared_major infos lft1 fl1 v1 lft2 fl2 v2) then v1, v2
    else expose_major ~tab:infos.lft_tab infos fl1 v1, expose_major ~tab:infos.rgt_tab infos fl2 v2
  in
  let appr1 = lft1, (hd1, v1) and appr2 = lft2, (hd2, v2) in
  let unit_eta () = unit_eta l2r infos appr1 appr2 cuniv in
  (* the reduced major is carried into the unfolding of the selected side only,
     a constructor demand on the other side could evaluate a large term *)
  let expose_selected tab fl stack fallback =
    if preserve then fallback else
    let exposed = expose_major ~tab infos fl stack in
    if exposed == stack then fallback
    else Option.default fallback (unfold_ref_with_args infos.cnv_inf tab fl exposed)
  in
  try
    if expand_before_arguments infos fl1 ||
       projection_before_congruence infos lft1 fl1 v1 lft2 fl2 v2
    then raise NotConvertible;
    let nargs = same_args_size v1 v2 in
    let cuniv = conv_table_key infos ~nargs fl1 fl2 cuniv in
    (* a constructor major with different arguments computes, not congruence *)
    if (eliminates_constructor infos fl1 v1 || eliminates_constructor infos fl2 v2) &&
       not (syntactically_same_arguments lft1 v1 lft2 v2)
    then raise NotConvertible;
    let () = if irr_flex infos.cnv_inf fl1 then raise NotConvertible (* trigger the fallback *) in
    let mask = if infos.cnv_typ then match fl1 with
    | ConstKey _ -> get_ref_mask infos.cnv_inf infos.lft_tab fl1
    | RelKey _ | VarKey _ -> [||]
    else [||]
    in
    let constructor_first =
      infos.cnv_typ && infos.cnv_strategy.dependency_preference && dep_heuristic infos &&
      (match fl1 with ConstKey _ -> true | RelKey _ | VarKey _ -> false)
    in
    let compare infos =
      convert_stacks ~mask ~constructor_first
        ~projection_prefix_first:(infos.cnv_typ && dep_heuristic infos)
        l2r infos lft1 lft2 v1 v2 cuniv
    in
    if unfoldable infos fl1 then try_congruence infos lft1 lft2 fl1 v1 fl2 v2 compare
    else compare infos
  with NotConvertible | NotConvertibleTrace _ ->
    (* classified units first, then unfolding, then the operand types *)
    let same = same_unit_like (unit_like_of_flex infos lft1 v1 fl1)
        (fun () -> unit_like_of_flex infos lft2 v2 fl2) in
    match (if same then unit_eta () else None) with
    | Some cuniv -> cuniv
    | None ->
    let r1 = unfold_ref_with_args infos.cnv_inf infos.lft_tab fl1 v1 in
    let r2 = unfold_ref_with_args infos.cnv_inf infos.rgt_tab fl2 v2 in
    let all = RedFlags.(red_add_transparent all (red_transparent (info_flags infos.cnv_inf))) in
    match r1, r2 with
    | None, None ->
      (match unit_eta () with Some cuniv -> cuniv | None -> raise NotConvertible)
    | Some (t1, s1), None ->
      let t1, s1 = expose_selected infos.lft_tab fl1 v1 (t1, s1) in
      let t1 = whd_stack (infos_with_reds infos.cnv_inf all) infos.lft_tab t1 s1 in
      eqwhnf cv_pb l2r infos (lft1, t1) appr2 cuniv
    | None, Some (t2, s2) ->
      let t2, s2 = expose_selected infos.rgt_tab fl2 v2 (t2, s2) in
      let t2 = whd_stack (infos_with_reds infos.cnv_inf all) infos.rgt_tab t2 s2 in
      eqwhnf cv_pb l2r infos appr1 (lft2, t2) cuniv
    | Some (t1, s1), Some (t2, s2) ->
      let ninfos = infos_with_reds infos.cnv_inf RedFlags.betaiotazeta in
      let compact1 = compact_elimination infos infos.lft_tab t1 s1 in
      let compact2 = compact_elimination infos infos.rgt_tab t2 s2 in
      let prefix_congruence () =
        if dep_heuristic infos && (compact1 || compact2)
        then compact_prefix_congruence cv_pb l2r infos (lft1, hd1, s1) (lft2, hd2, s2) cuniv
        else None
      in
      begin match prefix_congruence () with
      | Some cuniv -> cuniv
      | None ->
      let () = Control.check_for_interrupt () in
      if independent_compact_applications infos ~compact:(compact1, compact2)
          lft1 fl1 t1 s1 lft2 fl2 t2 s2
      then
        let appr1 = whd_stack (infos_with_reds infos.cnv_inf all) infos.lft_tab t1 s1 in
        let appr2 = whd_stack (infos_with_reds infos.cnv_inf all) infos.rgt_tab t2 s2 in
        eqwhnf cv_pb l2r infos (lft1, appr1) (lft2, appr2) cuniv
      else
      (* the original applications: compact arithmetic may have consumed
         arguments of the unfolded ones *)
      let eliminates =
        let eliminates1 = eliminates_constructor infos fl1 v1 in
        let eliminates2 = eliminates_constructor infos fl2 v2 in
        let eliminates1 = eliminates1 || probed_constructor_major ~tab:infos.lft_tab infos fl1 v1 in
        let eliminates2 = eliminates2 || probed_constructor_major ~tab:infos.rgt_tab infos fl2 v2 in
        eliminates1, eliminates2
      in
      let action = unfolding_action infos l2r ~eliminates ~compact:(compact1, compact2)
          fl1 (t1, s1) fl2 (t2, s2) in
      match action with
      | Unfold_left ->
        let t1, s1 = expose_selected infos.lft_tab fl1 v1 (t1, s1) in
        let appr1 = whd_stack ninfos infos.lft_tab t1 s1 in
        eqwhnf cv_pb l2r infos (lft1, appr1) appr2 cuniv
      | Unfold_right ->
        let t2, s2 = expose_selected infos.rgt_tab fl2 v2 (t2, s2) in
        let appr2 = whd_stack ninfos infos.rgt_tab t2 s2 in
        eqwhnf cv_pb l2r infos appr1 (lft2, appr2) cuniv
      | Unfold_both ->
        (* one delta step on each side, as Lean's lazy_delta_reduction_step *)
        let t1, s1 = expose_selected infos.lft_tab fl1 v1 (t1, s1) in
        let t2, s2 = expose_selected infos.rgt_tab fl2 v2 (t2, s2) in
        let appr1 = whd_stack ninfos infos.lft_tab t1 s1 in
        let appr2 = whd_stack ninfos infos.rgt_tab t2 s2 in
        eqwhnf cv_pb l2r infos (lft1, appr1) (lft2, appr2) cuniv
      end

(* Before an elimination over a compact natural is forced, congruence on the
   outermost application: the function prefixes may be convertible while
   reducing either application would traverse a large recursion. The last
   arguments and the prefixes are quoted (one budget for all four) into fresh
   closures, so that the bounded probe cannot update shared cells. *)
and compact_prefix_congruence cv_pb l2r infos (lft1, hd1, s1) (lft2, hd2, s2) cuniv =
  let updates_only = List.for_all (function Zupdate _ -> true | _ -> false) in
  match s1, s2 with
  | Zapp args1 :: rest1, Zapp args2 :: rest2
    when Int.equal (Array.length args1) (Array.length args2) &&
         updates_only rest1 && updates_only rest2 &&
         Array.length args1 > 0 && Array.length args1 <= 2047 ->
    let last = Array.length args1 - 1 in
    let subst = subs_id (Range.length (info_relevances infos.cnv_inf)), UVars.Instance.empty in
    let remaining = ref 65_536 in
    let fresh lift term =
      if not (small_reification remaining term) then raise NotConvertible;
      mk_clos subst (Vars.exliftn lift (term_of_fconstr term))
    in
    let prefix head args =
      zip head (if Int.equal last 0 then [] else [Zapp (Array.sub args 0 last)]) in
    (try
       Some (bounded_congruence infos (fun infos ->
         let cuniv = ccnv CONV l2r infos el_id el_id
             (fresh lft1 args1.(last)) (fresh lft2 args2.(last)) cuniv in
         ccnv cv_pb l2r infos el_id el_id
           (fresh lft1 (prefix hd1 args1)) (fresh lft2 (prefix hd2 args2)) cuniv))
     with NotConvertible | NotConvertibleTrace _ -> None)
  | _ -> None

(* [constructor_first] compares the arguments of the head that are a
   constructor on one side only before the others, so that a mismatch is
   found before large arguments are normalised; [projection_prefix_first]
   compares the source of a projection before the arguments after it. *)
and convert_stacks ?(mask = [||]) ?(constructor_first = false)
    ?(projection_prefix_first = false) l2r infos lft1 lft2 stk1 stk2 cuniv =
  let f (l1, t1) (l2, t2) cuniv = ccnv CONV l2r infos l1 l2 t1 t2 cuniv in
  let relevant nargs i =
    nargs < 0 || nargs + i >= Array.length mask || mask.(nargs + i)
  in
  let fold_arguments selected nargs a1 a2 cuniv =
    let rec loop i cu =
      if i < 0 then cu
      else
        let cu = if relevant nargs i && selected i then f a1.(i) a2.(i) cu else cu in
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
              fold_arguments (fun i -> Array.is_empty compared || not compared.(i))
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
                let pms1 = lft_cells infos (fun () -> mk_clos_vect e1 pms1) in
                let pms2 = rgt_cells infos (fun () -> mk_clos_vect e2 pms2) in
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
  (* different projections reject the congruence before any argument is compared *)
  if compare_stack_shape ~check_projections:projection_prefix_first stk1 stk2 then
    let nargs = if Array.is_empty mask then -1 else 0 in
    let stack1 = pure_stack lft1 stk1 in
    let stack2 = pure_stack lft2 stk2 in
    let compared, cuniv = match stack1, stack2 with
    | Zlapp a1 :: _, Zlapp a2 :: _ when constructor_first ->
      let priority = Array.init (Array.length a1) (fun i ->
        relevant nargs i &&
        is_constructor_head infos infos.lft_tab (snd a1.(i)) <>
        is_constructor_head infos infos.rgt_tab (snd a2.(i)))
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
  ccnv CONV l2r infos lft1 lft2
    (lft_cells infos (fun () -> mk_clos e1 c1)) (rgt_cells infos (fun () -> mk_clos e2 c2)) cu

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

let clos_gen_conv (type err) ~typed ?(strategy = plain_strategy) trans cv_pb l2r evars env
    graph univs t1 t2 =
  NewProfile.profile "Conversion" begin fun () ->
      let reds = RedFlags.red_add_transparent RedFlags.betaiotazeta trans in
      let infos = create_conv_infos ~univs:graph ~evars reds env in
      let module Error = struct type payload += Error of err end in
      let box e = Error.Error e in
      let infos = {
        cnv_inf = infos;
        cnv_typ = typed;
        cnv_rel_types = Range.empty;
        cnv_rel_type_lifts = Range.empty;
        cnv_ctx = 0;
        cnv_ctx_steps = CtxSteps.create 64;
        cnv_strategy = strategy;
        cnv_steps = Option.map ref strategy.steps;
        cnv_probe = None;
        (* a bounded attempt shares its allowance with symbolic recovery *)
        cnv_symbolic = None;
        cnv_symbolic_total = ref (Option.default 16_384 strategy.steps);
        cnv_symbolic_misses = Sites.create ();
        cnv_projections = Sites.create ();
        cnv_failed = Applications.create ();
        cnv_memo =
          if typed && (Environ.typing_flags env).unfold_dep_heuristic
          then Some (Memo.create ()) else None;
        cnv_masks = ConstructorMasks.create 17;
        cnv_major_misses = MajorProbes.create 16;
        lft_tab = create_tab ~shared:true ();
        rgt_tab = create_tab ~shared:true ();
        err_ret = box;
      } in
      try Result.Ok (ccnv cv_pb l2r infos el_id el_id (inject t1) (inject t2) univs)
      with
      | NotConvertible -> Result.Error None
      | NotConvertibleTrace (Error.Error e) -> Result.Error (Some e)
      | NotConvertibleTrace _ -> assert false
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
        cnv_inf = infos; cnv_typ = true; lft_tab = tab; rgt_tab = tab; err_ret = box;
        cnv_rel_types = Range.empty; cnv_rel_type_lifts = Range.empty;
        cnv_ctx = 0; cnv_ctx_steps = CtxSteps.create 64;
        cnv_strategy = plain_strategy; cnv_steps = None; cnv_probe = None;
        cnv_symbolic = None; cnv_symbolic_total = ref 16_384;
        cnv_symbolic_misses = Sites.create (); cnv_projections = Sites.create ();
        cnv_failed = Applications.create (); cnv_memo = None;
        cnv_masks = ConstructorMasks.create 17; cnv_major_misses = MajorProbes.create 16;
      } in
      let state', _ = ccnv CONV false infos el_id el_id a b (state, checked_universes_gen qual_equal) in
      assert (state==state');
      true
    with
    | NotConvertible -> false
    | NotConvertibleTrace _ -> assert false
  in
  CClosure.set_conv conv

(* Bounded syntactic test before conversion; pairs already found equal are
   memoised so that a shared DAG is not expanded. *)
module AlphaPairs = Hashtbl.Make (struct
  type t = conv_pb * int * constr * constr
  let equal (p, n, a, b) (q, m, c, d) = p = q && Int.equal n m && a == c && b == d
  let hash (p, n, a, b) =
    Hashtbl.hash (p, n, Hashtbl.hash_param 8 32 a, Hashtbl.hash_param 8 32 b)
end)

let quick_constr_univs pb univs t1 t2 =
  let budget = ref 1024 in
  let seen = lazy (AlphaPairs.create 17) in
  let eq_universes _ = UGraph.check_eq_instances Sorts.Quality.equal univs in
  let eq_sorts s1 s2 = s1 == s2 || UGraph.check_eq_sort Sorts.Quality.equal univs s1 s2 in
  let leq_sorts s1 s2 = s1 == s2 || UGraph.check_leq_sort Sorts.Quality.equal univs s1 s2 in
  let rec compare pb nargs t1 t2 =
    !budget > 0 && begin
      decr budget;
      t1 == t2 ||
      (* casts are charged here, as compare_head would strip them for free *)
      match kind t1, kind t2 with
      | Cast (c, _, _), _ -> compare pb nargs c t2
      | _, Cast (c, _, _) -> compare pb nargs t1 c
      | (Evar _ | Meta _), _ | _, (Evar _ | Meta _) -> false
      | _ ->
        let key = pb, nargs, t1, t2 in
        (Lazy.is_val seen && AlphaPairs.mem (Lazy.force seen) key) ||
        let sorts = if pb = CONV then eq_sorts else leq_sorts in
        let ok = Constr.compare_head_gen_leq eq_universes sorts
          (fun _ _ -> false) (compare CONV) (compare pb) nargs t1 t2 in
        if ok then AlphaPairs.replace (Lazy.force seen) key ();
        ok
    end
  in compare pb 0 t1 t2

(* The attempts of a typed conversion, in order: two bounded dependency-first
   ones (without, then with constructor field masks) when the environment
   enables the heuristic, then unbounded ones with masks, then also
   projection congruence, then also the dependency preference. Exhaustion
   of a bounded attempt certifies nothing; the last attempt decides. *)
let strategies ~typed env =
  if not typed then [plain_strategy]
  else
    let masked = { plain_strategy with constructor_relevance = true } in
    let bounded steps constructor_relevance =
      { masked with steps = Some steps; constructor_relevance; dependency_preference = true } in
    (if (Environ.typing_flags env).unfold_dep_heuristic
     then [bounded 256 false; bounded 262_144 true] else []) @
    [ masked;
      { masked with projection_congruence = true };
      { masked with projection_congruence = true; dependency_preference = true } ]

let gen_conv ~typed cv_pb ?(l2r=false) ?(reds=TransparentState.full) env ?(evars=default_evar_handler env) t1 t2 =
  let univs = Environ.universes env in
  let state = univs in
  let b = quick_constr_univs cv_pb univs t1 t2 in
    if b then Result.Ok ()
    else
      let rec attempt = function
        | [] -> Result.Error ()
        | strategy :: rest ->
          match
            try clos_gen_conv ~typed ~strategy reds cv_pb l2r evars env univs
                  (state, checked_universes) t1 t2
            with Strategy_budget_exhausted -> Result.Error None
          with
          | Result.Ok (_ : 'a * ('a, Empty.t) universe_compare) -> Result.Ok ()
          | Result.Error None -> attempt rest
          | Result.Error (Some e) -> Empty.abort e
      in
      attempt (strategies ~typed env)

let conv = gen_conv ~typed:false CONV
let conv_leq = gen_conv ~typed:false CUMUL

let generic_conv cv_pb ~l2r reds env ?(evars=default_evar_handler env) state t1 t2 =
  let graph = Environ.universes env in
  match clos_gen_conv ~typed:false reds cv_pb l2r evars env graph state t1 t2 with
  | Result.Ok (s, _) -> Result.Ok s
  | Result.Error e -> Result.Error e

let default_conv cv_pb env t1 t2 =
    gen_conv ~typed:true cv_pb env t1 t2

let default_conv_leq = default_conv CUMUL

type graph_inconsistency = Univ of UGraph.univ_inconsistency | Qual of QGraph.elimination_error
