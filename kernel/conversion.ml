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

let compare_stack_shape stk1 stk2 =
  let rec compare_rec bal stk1 stk2 =
  match (stk1,stk2) with
      ([],[]) -> Int.equal bal 0
    | ((Zupdate _|Zshift _)::s1, _) -> compare_rec bal s1 stk2
    | (_, (Zupdate _|Zshift _)::s2) -> compare_rec bal stk1 s2
    | (Zapp l1::s1, _) -> compare_rec (bal+Array.length l1) s1 stk2
    | (_, Zapp l2::s2) -> compare_rec (bal-Array.length l2) stk1 s2
    | (Zproj _::s1, Zproj _::s2) ->
        Int.equal bal 0 && compare_rec 0 s1 s2
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
}

type successful_conversion = {
  conversion_problem : conv_pb;
  conversion_left_lift : lift;
  conversion_right_lift : lift;
  conversion_relevances : Sorts.relevance Range.t;
  conversion_rel_types : fconstr option Range.t;
}

module ConversionPairs = Hashtbl.Make (struct
  type t = fconstr * fconstr

  let equal (left1, right1) (left2, right2) =
    left1 == left2 && right1 == right2

  let hash (left, right) =
    Hashtbl.hash (fconstr_hash left, fconstr_hash right)
end)

type successful_conversion_cache = {
  successful_conversion_table :
    successful_conversion list ConversionPairs.t;
  successful_conversion_limit : int;
  mutable successful_conversion_size : int;
}

let successful_conversion_limit = 32_768

let make_successful_conversion_cache limit =
  {
    successful_conversion_table =
      ConversionPairs.create (if limit > 0 then min limit 251 else 0);
    successful_conversion_limit = limit;
    successful_conversion_size = 0;
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

type 'e conv_tab = {
  cnv_inf : clos_infos;
  cnv_typ : bool; (* true if the input terms were well-typed *)
  cnv_rel_types : fconstr option Range.t;
  (* Remaining depth, shared within one speculative congruence check. *)
  cnv_probe_budget : int ref option;
  cnv_projection_conversions : projection_conversion list ref;
  cnv_successful_conversions : successful_conversion_cache;
  cnv_memoize_successful_conversions : bool;
  cnv_projection_congruence : bool;
  cnv_dependency_preference : bool;
  cnv_constructor_relevance : bool;
  cnv_constructor_masks : bool array ConstructorMasks.t;
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

(* Bound speculative congruence depth; only the owner catches exhaustion. *)
let with_congruence_budget infos compare =
  if Option.has_some infos.cnv_probe_budget ||
     not (Environ.typing_flags (info_env infos.cnv_inf)).unfold_dep_heuristic
  then compare infos
  else
    try compare { infos with cnv_probe_budget = Some (ref 256) }
    with Probe_budget_exhausted -> raise NotConvertible

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

(* Expose cheap wrappers before eta; keep eta first for other record producers. *)
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

(* Projected forwarding wrappers can discard costly arguments. *)
let projected_record_wrapper infos reference stack =
  let rec projection = function
    | (Zapp _ | Zshift _ | Zupdate _) :: stack -> projection stack
    | Zproj (projection, _) :: _ -> Some projection
    | [] | (Zfix _ | ZcaseT _ | Zprimitive _) :: _ -> None
  in
  let rec forwarded term = match Constr.kind term with
    | Rel _ -> true
    | Proj (_, _, source) -> forwarded source
    | _ -> false
  in
  let rec constructor_body term = match Constr.kind term with
    | Lambda (_, _, body) -> constructor_body body
    | _ -> Constr.decompose_app term
  in
  let env = info_env infos.cnv_inf in
  if not infos.cnv_typ || not (Environ.typing_flags env).unfold_dep_heuristic
  then false
  else match reference, projection stack with
  | ConstKey (constant, _), Some projection
    when RedFlags.red_set (info_flags infos.cnv_inf) (RedFlags.fCONST constant) ->
    begin match (Environ.lookup_constant constant env).Declarations.const_body with
    | Def body ->
      let head, arguments = constructor_body body in
      begin match Constr.kind head with
      | Construct ((ind, 1), _)
        when Environ.QInd.equal env ind (Projection.Repr.inductive projection) ->
        let field = Projection.Repr.npars projection + Projection.Repr.arg projection in
        field < Array.length arguments && forwarded arguments.(field)
      | _ -> false
      end
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

let direct_registered_unit_like infos typ =
  let env = info_env infos.cnv_inf in
  match direct_inductive typ with
  | Some ind when
      List.exists (Ind.UserOrd.equal ind)
        (Environ.retroknowledge env).Retroknowledge.retro_unit_like -> Some ind
  | Some _ | None -> None

(* Unit-like fields need no comparison during record eta. *)
let record_unit_like_mask infos tab ((ind, _) as pind) args =
  let env = info_env infos.cnv_inf in
  let (mib, _ as spec) = Inductive.lookup_mind_specif env ind in
  let constructor_type =
    Inductive.type_of_constructor ((ind, 1), snd pind) spec |> inject
  in
  let rec fields index typ mask =
    if Int.equal index (Array.length args) then
      let mask = Array.of_list (List.rev mask) in
      if Array.exists (fun compare -> not compare) mask then mask else [||]
    else
      let typ, stack = whd_stack infos.cnv_inf tab typ empty_stack in
      let typ = zip typ stack in
      match fterm_of typ with
      | FProd (_, domain, body, subst) ->
        let domain, stack =
          whd_stack infos.cnv_inf tab domain empty_stack
        in
        let domain = zip domain stack in
        let mask =
          if index < mib.Declarations.mind_nparams then mask
          else Option.is_empty (direct_registered_unit_like infos domain) :: mask
        in
        let subst = usubs_cons args.(index) subst in
        fields (index + 1) (mk_clos subst body) mask
      | _ -> [||]
  in
  fields 0 constructor_type []

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

let push_relevance ?(typ = None) infos r =
  { infos with
    cnv_inf = CClosure.push_relevance infos.cnv_inf r;
    cnv_rel_types = Range.cons typ infos.cnv_rel_types }

let push_relevances infos nas =
  { infos with
    cnv_inf = CClosure.push_relevances infos.cnv_inf nas;
    cnv_rel_types =
      Array.fold_left (fun types _ -> Range.cons None types)
        infos.cnv_rel_types nas }

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

let rec compare_under e1 c1 e2 c2 =
  (c1 == c2 && eq_usubs_fast e1 e2)
  ||
  match Constr.kind c1, Constr.kind c2 with
  | Cast (c1, _, _), _ -> compare_under e1 c1 e2 c2
  | _, Cast (c2, _, _) -> compare_under e1 c1 e2 c2
  | Rel i, Rel j -> begin
      match Esubst.expand_rel i (fst e1), Esubst.expand_rel j (fst e2) with
      | Inl _, Inl _ ->
        CClosure.equal_compact_peano_rel e1 i e2 j
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
    compare_under e1 t1 e2 t2
    && compare_under (usubs_lift e1) c1 (usubs_lift e2) c2
  | Lambda (_,t1,c1), Lambda (_,t2,c2) ->
    compare_under e1 t1 e2 t2
    && compare_under (usubs_lift e1) c1 (usubs_lift e2) c2
  | LetIn (_,b1,_,c1), LetIn (_,b2,_,c2) ->
    (* don't care about types when bodies are equal *)
    compare_under e1 b1 e2 b2
    && compare_under (usubs_lift e1) c1 (usubs_lift e2) c2
  | App (c1, l1), App (c2, l2) ->
    let len = Array.length l1 in
    Int.equal len (Array.length l2)
    && compare_under e1 c1 e2 c2
    && Array.equal_norefl (fun c1 c2 -> compare_under e1 c1 e2 c2) l1 l2
  | Proj (p1,_,c1), Proj (p2,_,c2) ->
    Projection.UserOrd.equal p1 p2 && compare_under e1 c1 e2 c2
  | Evar _, Evar _ -> false
  | Const (c1,u1), Const (c2,u2) ->
    (* The args length currently isn't used but may as well pass it. *)
    Constant.UserOrd.equal c1 c2 && eq_universes e1 e2 u1 u2
  | Ind (c1,u1), Ind (c2,u2) -> Ind.UserOrd.equal c1 c2 && eq_universes e1 e2 u1 u2
  | Construct (c1,u1), Construct (c2,u2) ->
    Construct.UserOrd.equal c1 c2 && eq_universes e1 e2 u1 u2
  | Array(_,t1,def1,ty1), Array(_,t2,def2,ty2) ->
    Array.equal_norefl (fun c1 c2 -> compare_under e1 c1 e2 c2) t1 t2
    && compare_under e1 def1 e2 def2
    && compare_under e1 ty1 e2 ty2
  | (Rel _ | Meta _ | Var _ | Sort _ | Prod _ | Lambda _ | LetIn _ | App _
    | Proj _ | Evar _ | Const _ | Ind _ | Construct _ | Case _ | Fix _
    | CoFix _ | Int _ | Float _ | String _ | Array _), _ -> false

and fast_test lft1 term1 lft2 term2 = match fterm_of term1, fterm_of term2 with
  | FLIFT (i, term1), (FLIFT _ | FCLOS _) -> fast_test (el_shft i lft1) term1 lft2 term2
  | FCLOS _, FLIFT (j, term2) -> fast_test lft1 term1 (el_shft j lft2) term2
  | FCLOS (c1, (e1,u1)), FCLOS (c2, (e2,u2)) ->
    eq_lift lft1 lft2 &&
    compare_under (e1, u1) c1 (e2, u2) c2
  | FFix (fix1, e1), FFix (fix2, e2) ->
    eq_lift lft1 lft2 &&
    compare_under e1 (mkFix fix1) e2 (mkFix fix2)
  | FCoFix (fix1, e1), FCoFix (fix2, e2) ->
    eq_lift lft1 lft2 &&
    compare_under e1 (mkCoFix fix1) e2 (mkCoFix fix2)
  | _ -> false

let assert_reduced_constructor s =
  if not @@ CList.is_empty s then
    CErrors.anomaly Pp.(str "conversion was given unreduced term (FConstruct).")

let is_registered_unit_like env ind =
  List.exists (Ind.UserOrd.equal ind)
    (Environ.retroknowledge env).Retroknowledge.retro_unit_like

let is_eta_record env (ind, u) =
  Declareops.is_record_with_eta (Inductive.lookup_mind_specif env ind) u

let abbreviation_inductive_type ~fresh infos typ =
  try
    (* Inspect local types in fresh closures, without mutating conversion inputs. *)
    let tab = create_tab () in
    let typ = if fresh then typ else inject (term_of_fconstr typ) in
    let oracle = CClosure.oracle_of_infos infos.cnv_inf in
    let type_infos =
      infos_with_reds infos.cnv_inf RedFlags.betaiotazeta
    in
    let rec inspect typ stack =
      let typ, stack = whd_stack type_infos tab typ stack in
      match direct_inductive (zip typ stack) with
      | Some _ as ind -> ind
      | None -> begin match fterm_of typ with
        | FFlex (ConstKey (c, _) as fl) ->
          begin match Conv_oracle.get_strategy oracle
            (Conv_oracle.EvalConstRef c) with
          | Conv_oracle.Expand ->
            begin match unfold_ref_with_args infos.cnv_inf tab fl stack with
            | Some (typ, stack) -> inspect typ stack
            | None -> None
            end
          | Conv_oracle.Level _ | Conv_oracle.Opaque -> None
          end
        | _ -> None
        end
    in
    inspect typ empty_stack
  with Not_found | Assert_failure _ -> None

let rec application_args arrays = function
  | Zapp args :: stack -> application_args (args :: arrays) stack
  | (Zshift _ | Zupdate _) :: stack -> application_args arrays stack
  | [] -> Some (Array.concat (List.rev arrays))
  | (ZcaseT _ | Zproj _ | Zfix _ | Zprimitive _) :: _ -> None

let inductive_after_eliminating ?(expand_aliases = false)
    ?(allow_dependent_projections = true)
    reduction_infos tab typ stack =
  let env = info_env reduction_infos in
  let rec direct_unit_like_alias fuel (constant, instance) =
    if Int.equal fuel 0 then None
    else
      match Environ.constant_opt_value_in env (constant, instance) with
      | None -> None
      | Some body ->
        let head, _ = Constr.decompose_app body in
        begin match Constr.kind head with
        | Constr.Ind (ind, _)
          when is_registered_unit_like env ind -> Some ind
        | Constr.Const constant ->
          direct_unit_like_alias (fuel - 1) constant
        | _ -> None
        end
  in
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
    match direct_inductive (zip typ stack) with
    | Some _ as inductive -> inductive
    | None when expand_aliases && fuel > 0 ->
      begin match fterm_of typ, stack with
      | FFlex (ConstKey ((constant, _) as puniverses) as flex), [] ->
          begin match direct_unit_like_alias fuel puniverses with
          | Some _ as inductive -> inductive
          | None ->
            let oracle = CClosure.oracle_of_infos reduction_infos in
            begin match
              Conv_oracle.get_strategy oracle
                (Conv_oracle.EvalConstRef constant)
            with
            | Conv_oracle.Expand ->
              begin match
                unfold_ref_with_args reduction_infos tab flex stack
              with
              | Some (typ, stack) -> final (fuel - 1) (zip typ stack)
              | None -> None
              end
            | Conv_oracle.Level _ | Conv_oracle.Opaque -> None
            end
          end
      | _ -> None
      end
    | None -> None
  in
  let rec eliminate typ = function
    | [] ->
      final 32 typ
    | (Zshift _ | Zupdate _) :: stack -> eliminate typ stack
    | Zapp args :: stack ->
      Option.bind (apply_args typ args 0) (fun typ -> eliminate typ stack)
    | Zproj (repr, _) :: stack ->
      let typ, typ_stack =
        whd_stack reduction_infos tab typ empty_stack
      in
      begin match fterm_of typ, application_args [] typ_stack with
      | FInd ((current, u)), Some args
        when Environ.QInd.equal env current (Projection.Repr.inductive repr) ->
        begin match
          try Some (Environ.lookup_projection (Projection.make repr true) env)
          with Not_found -> None
        with
        | Some (_, projection_type)
          when allow_dependent_projections || Vars.noccurn 1 projection_type ->
          (* Substitute lazily: erased proof parameters may be [FIrrelevant]. *)
          let subst =
            Array.fold_left (fun subst arg -> usubs_cons arg subst)
              (subs_id 0, u) args
          in
          let subst = usubs_cons (inject (mkRel 1)) subst in
          eliminate (mk_clos subst projection_type) stack
        | Some _ | None -> None
        end
      | _ -> None
      end
    | (ZcaseT _ | Zfix _ | Zprimitive _) :: _ -> None
  in
  eliminate typ stack

let inductive_after_applying infos tab typ stack =
  inductive_after_eliminating infos.cnv_inf tab typ stack

let transparent_inductive_after_applying infos typ stack =
  try
  (* Follow transparent type aliases when checking the record-eta guard. *)
  let type_infos =
    let all = RedFlags.(red_add_transparent all
      (red_transparent (info_flags infos.cnv_inf)))
    in
    infos_with_reds infos.cnv_inf all
  in
  let rec fresh_stack = function
    | [] -> Some []
    | (Zshift _ | Zupdate _) :: stack -> fresh_stack stack
    | Zapp args :: stack ->
      let rec fresh_args index args' =
        if Int.equal index (Array.length args) then
          Some (Array.of_list (List.rev args'))
        else
          try
            let arg = inject (term_of_fconstr args.(index)) in
            fresh_args (index + 1) (arg :: args')
          with Assert_failure _ -> None
      in
      Option.bind (fresh_args 0 []) (fun args ->
        Option.map (fun stack -> Zapp args :: stack) (fresh_stack stack))
    | Zproj _ as projection :: stack ->
      Option.map (fun stack -> projection :: stack) (fresh_stack stack)
    | (ZcaseT _ | Zfix _ | Zprimitive _) :: _ -> None
  in
  match fresh_stack stack with
  | Some stack ->
    (* Isolate type reduction from the main conversion's tables and closures. *)
    let tab = create_tab () in
    let typ = inject (term_of_fconstr typ) in
    inductive_after_eliminating type_infos tab typ stack
  | None -> None
  with Not_found | Assert_failure _ -> None

(* Unit eta supports applications and projections, not other eliminations. *)
let rec unit_like_stack = function
  | [] -> true
  | (Zapp _ | Zproj _ | Zshift _ | Zupdate _) :: stack -> unit_like_stack stack
  | (ZcaseT _ | Zfix _ | Zprimitive _) :: _ -> false

let shallow_unit_like_after_applying infos typ stack =
  let env = info_env infos.cnv_inf in
  let substituted_inductive () =
    if not (unit_like_stack stack) then None
    else
      let type_infos =
        infos_with_reds infos.cnv_inf RedFlags.betaiotazeta
      in
      let tab = create_tab () in
      (* The dummy scrutinee requires a nondependent projection type. *)
      inductive_after_eliminating ~expand_aliases:true
        ~allow_dependent_projections:false
        type_infos tab (inject typ) stack
  in
  let rec strip_products count typ =
    if Int.equal count 0 then
      let typ = inject typ in
      begin match direct_registered_unit_like infos typ with
      | Some _ as ind -> ind
      | None ->
        Option.bind (abbreviation_inductive_type ~fresh:true infos typ)
          (fun ind -> if is_registered_unit_like env ind then Some ind else None)
      end
    else
      match Constr.kind typ with
      | Constr.Prod (_, _, body) -> strip_products (count - 1) body
      | Constr.Cast (term, _, _) -> strip_products count term
      | _ -> None
  in
  match substituted_inductive () with
  | Some ind when is_registered_unit_like env ind -> Some ind
  | Some _ | None ->
    match application_args [] stack with
    | Some arguments -> strip_products (Array.length arguments) typ
    | None -> None

let unit_like_of_rel infos _tab lft stack n =
  (* Reject unsupported stacks before reifying a potentially shared local type. *)
  if not (unit_like_stack stack) then None
  else
    let n = reloc_rel n (el_stack lft stack) in
    Option.bind (rel_type infos n) (fun typ ->
      try shallow_unit_like_after_applying infos (term_of_fconstr typ) stack
      with Assert_failure _ -> None)

let rel_has_unit_like infos tab lft (hd, stack) ind =
  match fterm_of hd with
  | FRel n -> begin match unit_like_of_rel infos tab lft stack n with
    | Some rel_ind -> Ind.UserOrd.equal ind rel_ind
    | None -> false
    end
  | _ -> false

let unit_like_of_flex infos _tab lft stack fl =
  (* Reject unsupported stacks before reifying a potentially shared local type. *)
  if not (unit_like_stack stack) then None
  else
    let env = info_env infos.cnv_inf in
    let typ = match fl with
    | RelKey n ->
      let n = reloc_rel n (el_stack lft stack) in
      Option.bind (rel_type infos n) (fun typ ->
        try Some (term_of_fconstr typ) with Assert_failure _ -> None)
    | VarKey id ->
      Some (Context.Named.Declaration.get_type (Environ.lookup_named id env))
    | ConstKey (c, u) ->
      Some (Environ.constant_type_in env (c, u))
    in
    Option.bind typ (fun typ ->
      shallow_unit_like_after_applying infos typ stack)

let flex_has_unit_like infos tab lft stack fl ind =
  match unit_like_of_flex infos tab lft stack fl with
  | Some flex_ind -> Ind.UserOrd.equal ind flex_ind
  | None -> false

let same_unit_like_flexes infos lft1 v1 fl1 lft2 v2 fl2 =
  match unit_like_of_flex infos infos.lft_tab lft1 v1 fl1,
        unit_like_of_flex infos infos.rgt_tab lft2 v2 fl2 with
  | Some ind1, Some ind2 -> Ind.UserOrd.equal ind1 ind2
  | _ -> false

let same_unit_like_flex_rel infos flex_tab flex_lift flex_stack flex
    rel_tab rel_lift rel_stack rel =
  match unit_like_of_flex infos flex_tab flex_lift flex_stack flex,
        unit_like_of_rel infos rel_tab rel_lift rel_stack rel with
  | Some flex_ind, Some rel_ind -> Ind.UserOrd.equal flex_ind rel_ind
  | _ -> false

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

let depends_on_registered_compact_peano_operation infos constant =
  let env = CClosure.info_env infos in
  matches_registered_compact_peano_operation infos (fun operation ->
    Constant.UserOrd.equal constant operation ||
    Environ.constant_depends_on env constant operation)

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

let flex_result_inductive infos tab lft stack fl =
  let env = info_env infos.cnv_inf in
  let typ = match fl with
  | RelKey n ->
    let n = reloc_rel n (el_stack lft stack) in
    rel_type infos n
  | VarKey id ->
    Some (inject
      (Context.Named.Declaration.get_type (Environ.lookup_named id env)))
  | ConstKey (c, u) ->
    Some (inject (Environ.constant_type_in env (c, u)))
  in
  let flex_ind = Option.bind typ (fun typ ->
    try match inductive_after_applying infos tab typ stack with
      | Some _ as ind -> ind
      | None -> transparent_inductive_after_applying infos typ stack
    with Not_found | Assert_failure _ -> None)
  in
  flex_ind

let flex_has_inductive infos tab lft stack fl ind =
  match flex_result_inductive infos tab lft stack fl with
  | Some flex_ind -> Ind.UserOrd.equal ind flex_ind
  | None -> false

let successful_conversion_cached infos cv_pb lft1 lft2 term1 term2 =
  infos.cnv_memoize_successful_conversions &&
  match ConversionPairs.find_opt
          infos.cnv_successful_conversions.successful_conversion_table
          (term1, term2) with
  | None -> false
  | Some conversions ->
    let relevances = info_relevances infos.cnv_inf in
    List.exists (fun conversion ->
      conversion.conversion_problem = cv_pb &&
      eq_lift conversion.conversion_left_lift lft1 &&
      eq_lift conversion.conversion_right_lift lft2 &&
      conversion.conversion_relevances == relevances &&
      conversion.conversion_rel_types == infos.cnv_rel_types)
      conversions

let remember_successful_conversion infos cv_pb lft1 lft2 term1 term2 =
  if infos.cnv_memoize_successful_conversions then begin
    let cache = infos.cnv_successful_conversions in
    if cache.successful_conversion_size >= cache.successful_conversion_limit
    then begin
      ConversionPairs.clear cache.successful_conversion_table;
      cache.successful_conversion_size <- 0
    end;
    let key = term1, term2 in
    let previous =
      Option.default []
        (ConversionPairs.find_opt cache.successful_conversion_table key)
    in
    ConversionPairs.replace cache.successful_conversion_table key
      ({
        conversion_problem = cv_pb;
        conversion_left_lift = lft1;
        conversion_right_lift = lft2;
        conversion_relevances = info_relevances infos.cnv_inf;
        conversion_rel_types = infos.cnv_rel_types;
      } :: previous);
    cache.successful_conversion_size <- cache.successful_conversion_size + 1
  end

(* Conversion between  [lft1]term1 and [lft2]term2 *)
let rec ccnv cv_pb l2r infos lft1 lft2 term1 term2 cuniv =
  let fast = fast_test lft1 term1 lft2 term2 in
  if fast || successful_conversion_cached infos cv_pb lft1 lft2 term1 term2
  then cuniv
  else begin
    let result =
      let compare () =
        eqappr cv_pb l2r infos
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
    result
  end

(* Conversion between [lft1](hd1 v1) and [lft2](hd2 v2) *)
and eqappr cv_pb l2r infos (lft1,st1) (lft2,st2) cuniv =
  Control.check_for_interrupt ();
  (* First head reduce both terms *)
  let ninfos = infos_with_reds infos.cnv_inf RedFlags.betaiotazeta in
  let appr1 = whd_stack ninfos infos.lft_tab
    (fst st1) (snd st1) in
  let appr2 = whd_stack ninfos infos.rgt_tab
    (fst st2) (snd st2) in
  eqwhnf cv_pb l2r infos (lft1, appr1) (lft2, appr2) cuniv

(* assumes that appr1 and appr2 are in whnf *)
and eqwhnf cv_pb l2r infos (lft1, (hd1, v1) as appr1) (lft2, (hd2, v2) as appr2) cuniv =
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
        let original_n = n in
        let original_m = m in
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
          let same_unit_like () =
            let unit1 =
              unit_like_of_rel infos infos.lft_tab lft1 v1 original_n
            in
            let unit2 =
              unit_like_of_rel infos infos.rgt_tab lft2 v2 original_m
            in
            match unit1, unit2 with
            | Some ind1, Some ind2 when Ind.UserOrd.equal ind1 ind2 -> true
            | _ -> false
          in
          if Int.equal n m then
            try convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
            with (NotConvertible | NotConvertibleTrace _) as error ->
              if same_unit_like () then cuniv else raise error
          else
            if same_unit_like () then cuniv else raise NotConvertible

    (* 2 constants, 2 local defined vars or 2 defined rels *)
    | (FFlex fl1, FFlex fl2) ->
      (try
         if projected_record_wrapper infos fl1 v1 ||
            projected_record_wrapper infos fl2 v2
         then raise NotConvertible;
         let nargs = same_args_size v1 v2 in
         let cuniv = conv_table_key infos ~nargs fl1 fl2 cuniv in
         let irrelevant1 = irr_flex infos.cnv_inf fl1 in
         let () = if irrelevant1 then raise NotConvertible (* trigger the fallback *) in
         let mask = if infos.cnv_typ then match fl1 with
         | ConstKey _ -> get_ref_mask infos.cnv_inf infos.lft_tab fl1
         | RelKey _ | VarKey _ -> [||]
         else [||]
         in
         let constructor_first =
           infos.cnv_typ && infos.cnv_dependency_preference &&
           (Environ.typing_flags (info_env infos.cnv_inf)).unfold_dep_heuristic &&
           (match fl1 with ConstKey _ -> true | RelKey _ | VarKey _ -> false)
         in
         let compare infos =
           convert_stacks ~mask ~constructor_first
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
         if can_unfold then with_congruence_budget infos compare
         else compare infos
       with NotConvertible | NotConvertibleTrace _ ->
        if same_unit_like_flexes infos lft1 v1 fl1 lft2 v2 fl2 then cuniv
        else
          let r1 = unfold_ref_with_args infos.cnv_inf infos.lft_tab fl1 v1 in
          let r2 = unfold_ref_with_args infos.cnv_inf infos.rgt_tab fl2 v2 in
          match r1, r2 with
          | None, None -> raise NotConvertible
          | Some (t1, v1), Some (t2, v2) ->
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
          let compact_elimination2 =
            is_compact_peano_elimination infos.rgt_tab t2 v2
          in
          (* Try outermost application congruence before a compact elimination.
             Fresh closures must preserve lifts and local binder depth. *)
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
              if Int.equal argument_count 0 then None
              else
                let prefix_length = argument_count - 1 in
                let subst =
                  subs_id (Range.length (info_relevances infos.cnv_inf)),
                  UVars.Instance.empty
                in
                let fresh_term lift term =
                  mk_clos subst (Vars.exliftn lift term)
                in
                let fresh_argument lift argument =
                  fresh_term lift (CClosure.term_of_fconstr argument)
                in
                let fresh_prefix lift head args =
                  let stack =
                    if Int.equal prefix_length 0 then []
                    else [Zapp (Array.sub args 0 prefix_length)]
                  in
                  fresh_term lift (CClosure.term_of_process head stack)
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
          begin match common_application_congruence () with
          | Some cuniv -> cuniv
          | None ->
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
            (* Probe dependencies without reifying or mutating shared closures.
               Unknown forms and exhausted budgets retain the ordinary unfolding strategy. *)
            let exception Found_dependency in
            let exception Unknown_dependency in
            let remaining = ref 1024 in
            let update_targets = ref [] in
            let visit () =
              if Int.equal !remaining 0 then
                raise Unknown_dependency;
              decr remaining
            in
            let inspect_constant constant =
              if Constant.UserOrd.equal constant target ||
                 (transitive && Environ.constant_depends_on
                   (CClosure.info_env infos.cnv_inf) constant target)
              then raise Found_dependency
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
                    raise Unknown_dependency))
              | Const (constant, _) ->
                if not aliases_only then inspect_constant constant
              | _ ->
                Constr.iter_with_binders enter_binder
                  (inspect_constr ~aliases_only substitution) depth term
            and inspect_closure ~aliases_only term =
              visit ();
              if aliases_only &&
                 List.exists (fun target -> target == term) !update_targets
              then raise Unknown_dependency;
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
                (* Raw terms contain no mutable closure cells. *)
                if not aliases_only then inspect_constr ~aliases_only None 0 term
              | FCLOS (term, substitution) ->
                inspect_constr ~aliases_only (Some substitution) 0 term
              | FLambda (len, domains, body, substitution) ->
                let substitution =
                  if is_subs_id (fst substitution) then None
                  else Some substitution
                in
                if not aliases_only || Option.has_some substitution then begin
                  (* Domains are outermost first; only free references use the substitution. *)
                  let rec inspect_domains depth = function
                    | [] ->
                      if not (Int.equal depth len) then
                        raise Unknown_dependency;
                      inspect_constr ~aliases_only substitution len body
                    | (_, domain) :: rest ->
                      visit ();
                      inspect_constr ~aliases_only substitution depth domain;
                      inspect_domains (enter_binder depth) rest
                  in
                  inspect_domains 0 domains
                end
              | FFix _ | FCoFix _ | FCaseT _ | FCaseInvert _ | FProd _
              | FLetIn _ | FEvar _ | FArray _ | FPeanoNat _ | FIrrelevant
              | FLOCKED -> raise Unknown_dependency
            in
            let rec inspect_stack ~aliases_only = function
              | [] -> ()
              | frame :: rest ->
                visit ();
                (match frame with
                | Zapp arguments ->
                  Array.iter (inspect_closure ~aliases_only) arguments
                | Zproj _ | Zshift _ | Zupdate _ -> ()
                | Zfix _ | ZcaseT _ | Zprimitive _ -> raise Unknown_dependency);
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
                  then raise Unknown_dependency;
                  update_targets := target :: !update_targets;
                  check_stack rest
                | Zfix _ | ZcaseT _ | Zprimitive _ -> raise Unknown_dependency)
            in
            try
              (* Check update aliases before accepting an early dependency witness. *)
              check_stack stack;
              if not (CList.is_empty !update_targets) then begin
                inspect_closure ~aliases_only:true term;
                inspect_stack ~aliases_only:true stack
              end;
              inspect_closure ~aliases_only:false term;
              inspect_stack ~aliases_only:false stack;
              Some false
            with
            | Found_dependency -> Some true
            | Unknown_dependency | Assert_failure _ -> None
          in
          (* Normalize eligible compact applications independently to avoid alternating delta steps. *)
          let reduce_applications_to_whnf () =
            let env = CClosure.info_env infos.cnv_inf in
            let compact_backed_closed_process term stack =
              (* Check closedness and a compact witness without expanding shared closures. *)
              let exception Unknown_eligibility in
              let remaining = ref 1024 in
              let backed = ref false in
              let update_targets = ref [] in
              let visit () =
                if Int.equal !remaining 0 then
                  raise Unknown_eligibility;
                decr remaining
              in
              let enter_binder depth =
                visit ();
                depth + 1
              in
              let inspect_constant constant =
                if not !backed &&
                   depends_on_registered_compact_peano_operation
                     infos.cnv_inf constant
                then backed := true
              in
              let rec inspect_constr substitution depth term =
                visit ();
                match Constr.kind term with
                | Rel index ->
                  if index > depth then begin
                    (* Inspect referenced substitutions; an unresolved relative variable is not closed. *)
                    match Option.bind substitution (fun substitution ->
                        inspect_substituted_rel substitution (index - depth)) with
                    | Some term -> inspect_closure term
                    | None -> raise Unknown_eligibility
                  end
                | Const (constant, _) -> inspect_constant constant
                | Evar _ -> raise Unknown_eligibility
                | _ ->
                  Constr.iter_with_binders enter_binder
                    (inspect_constr substitution) depth term
              and inspect_closure term =
                visit ();
                if List.exists (fun target -> target == term) !update_targets
                then raise Unknown_eligibility;
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
                  (* Domains are outermost first; the body is under all [len] binders. *)
                  let rec inspect_domains depth = function
                    | [] ->
                      if not (Int.equal depth len) then
                        raise Unknown_eligibility;
                      inspect_constr (Some substitution) len body
                    | (_, domain) :: rest ->
                      visit ();
                      inspect_constr (Some substitution) depth domain;
                      inspect_domains (enter_binder depth) rest
                  in
                  inspect_domains 0 domains
                | FRel _ | FFlex (RelKey _) | FFix _ | FCoFix _ | FCaseT _
                | FCaseInvert _ | FProd _ | FLetIn _ | FEvar _ | FArray _
                | FIrrelevant | FLOCKED -> raise Unknown_eligibility
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
                    then raise Unknown_eligibility;
                    update_targets := target :: !update_targets;
                    check_stack rest
                  | Zfix _ | ZcaseT _ | Zprimitive _ -> raise Unknown_eligibility)
              in
              let rec inspect_stack = function
                | [] -> ()
                | frame :: rest ->
                  visit ();
                  (match frame with
                  | Zapp arguments -> Array.iter inspect_closure arguments
                  | Zproj _ | Zshift _ | Zupdate _ -> ()
                  | Zfix _ | ZcaseT _ | Zprimitive _ -> raise Unknown_eligibility);
                  inspect_stack rest
              in
              let eligible =
                try
                  (* Update targets must not alias inspected subtrees. *)
                  check_stack stack;
                  inspect_closure term;
                  inspect_stack stack;
                  !backed
                with
                | Unknown_eligibility | Assert_failure _ -> false
              in
              eligible
            in
            let closed_applications () =
              (* Check bounded eligibility before inspecting result types. *)
              if not (compact_backed_closed_process t1 v1 &&
                      compact_backed_closed_process t2 v2)
              then false
              else
              let compact_wrapper_result =
                match
                  flex_result_inductive infos infos.lft_tab lft1 v1 fl1,
                  flex_result_inductive infos infos.rgt_tab lft2 v2 fl2
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
              (* Leave equal heads to ordinary unfolding after congruence fails. *)
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
              (* Only registered compact computations justify complete evaluation here. *)
              None
            else if
              compact_elimination1 || compact_elimination2
            then None
            else if
              match fl1, fl2 with
              | ConstKey (cst1, _), ConstKey (cst2, _) ->
                Environ.constant_depends_on env cst1 cst2
                || Environ.constant_depends_on env cst2 cst1
              | _ -> false
            then
              (* A common dependency can be exposed without evaluating either application. *)
              None
            else
              let all =
                RedFlags.(red_add_transparent all
                  (red_transparent (info_flags infos.cnv_inf)))
              in
              let full_infos = infos_with_reds infos.cnv_inf all in
              let appr1 = whd_stack full_infos infos.lft_tab t1 v1 in
              let appr2 = whd_stack full_infos infos.rgt_tab t2 v2 in
              Some (eqwhnf cv_pb l2r infos
                (lft1, appr1) (lft2, appr2) cuniv)
          in
          begin match reduce_applications_to_whnf () with
          | Some cuniv -> cuniv
          | None ->
          (* Determine which constant to unfold first *)
          let unfold_left =
            let wrapper1 = projected_record_wrapper infos fl1 v1 in
            let wrapper2 = projected_record_wrapper infos fl2 v2 in
            if wrapper1 <> wrapper2 then wrapper1 else
            let order = Conv_oracle.oracle_compare oracle (to_er fl1) (to_er fl2) in
            let oracle_choice () =
              match order with
              | Conv_oracle.Left -> true
              | Conv_oracle.Right -> false
              | Conv_oracle.Same -> l2r
            in
            let constructor_argument_preference () =
              if infos.cnv_constructor_relevance && not same_reference
              then None
              else
                let constructor1 =
                  has_constructor_argument infos.lft_tab v1
                in
                let constructor2 =
                  has_constructor_argument infos.rgt_tab v2
                in
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
            let constructor_preference =
              if global_constants then constructor_argument_preference ()
              else None
            in
            let dependency_preference =
              if not infos.cnv_dependency_preference then None
              else match fl1, fl2 with
              | ConstKey (constant1, _), ConstKey (constant2, _) ->
                let left = indirectly_depends_on t1 v1 constant2 in
                let right = indirectly_depends_on t2 v2 constant1 in
                (match left, right with
                | Some left, Some right when not (Bool.equal left right) -> Some left
                (* An unknown reverse probe requires a direct, not merely transitive, witness. *)
                | Some true, None when
                    indirectly_depends_on ~transitive:false t1 v1 constant2 = Some true ->
                  Some true
                | None, Some true when
                    indirectly_depends_on ~transitive:false t2 v2 constant1 = Some true ->
                  Some false
                | _ -> None)
              | (ConstKey _ | VarKey _ | RelKey _), _ -> None
            in
            if (Environ.typing_flags
                  (CClosure.info_env infos.cnv_inf)).unfold_dep_heuristic &&
               global_constants
            then
              match dependency_preference, constructor_preference with
              | Some unfold_left, _ -> unfold_left
              | None, Some unfold_left ->
                unfold_left
              | None, None ->
                if compact_elimination1 && not compact_elimination2 then false
                else if compact_elimination2 && not compact_elimination1 then true
                else oracle_choice ()
            else if compact_elimination1 && not compact_elimination2 then false
            else if compact_elimination2 && not compact_elimination1 then true
            else oracle_choice ()
          in
          if unfold_left then
            let appr1 = whd_stack ninfos infos.lft_tab t1 v1 in
            eqwhnf cv_pb l2r infos (lft1, appr1) appr2 cuniv
          else
            let appr2 = whd_stack ninfos infos.rgt_tab t2 v2 in
            eqwhnf cv_pb l2r infos appr1 (lft2, appr2) cuniv
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

    | (FProj (p1, r1, c1), FConstruct (((ind2, 1), u2), args2))
      when infos.cnv_typ &&
           is_eta_record (info_env infos.cnv_inf) (ind2, u2) ->
      let () = assert_reduced_constructor v2 in
      begin match unfold_projection infos.cnv_inf p1 r1 with
      | Some s1 ->
        eqappr cv_pb l2r infos (lft1, (c1, s1 :: v1)) appr2 cuniv
      | None ->
        if is_registered_unit_like (info_env infos.cnv_inf) ind2 then cuniv
        else
          begin match
            try Some (eta_expand_ind_stack (info_env infos.cnv_inf) (ind2, u2)
              args2 (snd appr1))
            with Not_found -> None
          with
          | Some (v2, v1) ->
            let mask =
              record_unit_like_mask infos infos.rgt_tab (ind2, u2) args2
            in
            convert_stacks ~mask l2r infos lft1 lft2 v1 v2 cuniv
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
        if is_registered_unit_like (info_env infos.cnv_inf) ind1 then cuniv
        else
          begin match
            try Some (eta_expand_ind_stack (info_env infos.cnv_inf) (ind1, u1)
              args1 (snd appr2))
            with Not_found -> None
          with
          | Some (v1, v2) ->
            let mask =
              record_unit_like_mask infos infos.lft_tab (ind1, u1) args1
            in
            convert_stacks ~mask l2r infos lft1 lft2 v1 v2 cuniv
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
            (* Cache successful source comparisons in this typed conversion only.
               Include lifts and local contexts; the universe graph is fixed. *)
            let cached =
              List.exists (fun conversion ->
                conversion.projection_left_term == c1 &&
                conversion.projection_right_term == c2 &&
                eq_lift conversion.projection_left_lift el1 &&
                eq_lift conversion.projection_right_lift el2 &&
                conversion.projection_relevances == relevances &&
                conversion.projection_rel_types == infos.cnv_rel_types)
                !(infos.cnv_projection_conversions)
            in
            let cuniv =
              if cached then cuniv
              else ccnv CONV l2r infos el1 el2 c1 c2 cuniv
            in
            let () =
              if not cached then
                infos.cnv_projection_conversions := {
                  projection_left_lift = el1;
                  projection_left_term = c1;
                  projection_right_lift = el2;
                  projection_right_term = c2;
                  projection_relevances = relevances;
                  projection_rel_types = infos.cnv_rel_types;
                } :: !(infos.cnv_projection_conversions)
            in
            Some (convert_stacks l2r infos lft1 lft2 v1 v2 cuniv)
          with NotConvertible | NotConvertibleTrace _ -> None
      in
      begin match congruence_first () with
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
        ccnv CONV l2r (push_relevance ~typ:(Some ty1) infos x1)
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
        ccnv cv_pb l2r (push_relevance ~typ:(Some c1) infos x1)
          (el_lift el1) (el_lift el2)
          (mk_clos (usubs_lift e) c2) (mk_clos (usubs_lift e') c'2) cuniv

    (* Eta-expansion on the fly *)
    | (FLambda _, _) ->
        let () = match v1 with
        | [] -> ()
        | _ ->
          anomaly (Pp.str "conversion was given unreduced term (FLambda).")
        in
        let (x1,ty1,bd1) = destFLambda mk_clos hd1 in
        let infos = push_relevance ~typ:(Some ty1) infos x1 in
        eqappr CONV l2r infos
          (el_lift lft1, (bd1, [])) (el_lift lft2, (hd2, eta_expand_stack infos.cnv_inf x1 v2)) cuniv
    | (_, FLambda _) ->
        let () = match v2 with
        | [] -> ()
        | _ ->
          anomaly (Pp.str "conversion was given unreduced term (FLambda).")
        in
        let (x2,ty2,bd2) = destFLambda mk_clos hd2 in
        let infos = push_relevance ~typ:(Some ty2) infos x2 in
        eqappr CONV l2r infos
          (el_lift lft1, (hd1, eta_expand_stack infos.cnv_inf x2 v1)) (el_lift lft2, (bd2, [])) cuniv

    (* only one constant, defined var or defined rel *)
    | (FFlex fl1, c2)      ->
      if
        match c2 with
        | FRel rel ->
          same_unit_like_flex_rel infos infos.lft_tab lft1 v1 fl1
            infos.rgt_tab lft2 v2 rel
        | _ -> false
      then cuniv
      else
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
          then Some cuniv
          else
            (try
               let v2, v1 =
                 eta_expand_ind_stack (info_env infos.cnv_inf) (ind2, u2)
                   args2 (snd appr1)
               in
               let mask =
                 record_unit_like_mask infos infos.rgt_tab (ind2, u2) args2
               in
               Some (convert_stacks ~mask l2r infos lft1 lft2 v1 v2 cuniv)
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
          (* Stuck eliminations can still use ordinary record eta. *)
          (match c2 with
           | FConstruct (((ind2, 1), u2), args2) ->
             let () = assert_reduced_constructor v2 in
             (try
                let v2, v1 =
                  eta_expand_ind_stack (info_env infos.cnv_inf)
                    (ind2, u2) args2 (snd appr1)
                in
                convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
              with Not_found -> raise NotConvertible)
           | _ -> raise NotConvertible)
      end

    | (c1, FFlex fl2)      ->
      if
        match c1 with
        | FRel rel ->
          same_unit_like_flex_rel infos infos.rgt_tab lft2 v2 fl2
            infos.lft_tab lft1 v1 rel
        | _ -> false
      then cuniv
      else
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
           then Some cuniv
           else
             (try
                let v1, v2 =
                  eta_expand_ind_stack (info_env infos.cnv_inf) (ind1, u1)
                    args1 (snd appr2)
                in
                let mask =
                  record_unit_like_mask infos infos.lft_tab (ind1, u1) args1
                in
                Some (convert_stacks ~mask l2r infos lft1 lft2 v1 v2 cuniv)
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
          match c1 with
          | FConstruct (((ind1, 1), u1), args1) ->
            let () = assert_reduced_constructor v1 in
            (try
               let v1, v2 =
                 eta_expand_ind_stack (info_env infos.cnv_inf)
                   (ind1, u1) args1 (snd appr2)
               in
               convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
             with Not_found -> raise NotConvertible)
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
      if is_registered_unit_like (info_env infos.cnv_inf) ind1 &&
         (infos.cnv_typ ||
          rel_has_unit_like infos infos.rgt_tab lft2 (hd2, v2) ind1)
      then cuniv
      else (try
         let v1, v2 =
            eta_expand_ind_stack (info_env infos.cnv_inf) (ind1,u1) args1 (snd appr2)
         in
         let mask = record_unit_like_mask infos infos.lft_tab (ind1, u1) args1 in
         convert_stacks ~mask l2r infos lft1 lft2 v1 v2 cuniv
       with Not_found -> raise NotConvertible)

    | (_, FConstruct (((ind2, j2), u2), args2)) ->
      let () = assert_reduced_constructor v2 in
      (* records only have 1 constructor *)
      let () = if not @@ Int.equal j2 1 then raise NotConvertible in
      if is_registered_unit_like (info_env infos.cnv_inf) ind2 &&
         (infos.cnv_typ ||
          rel_has_unit_like infos infos.lft_tab lft1 (hd1, v1) ind2)
      then cuniv
      else (try
         let v2, v1 =
            eta_expand_ind_stack (info_env infos.cnv_inf) (ind2,u2) args2 (snd appr1)
         in
         let mask = record_unit_like_mask infos infos.rgt_tab (ind2, u2) args2 in
         convert_stacks ~mask l2r infos lft1 lft2 v1 v2 cuniv
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
  let same_shape = compare_stack_shape stk1 stk2 in
  if same_shape then
    let nargs = if Array.is_empty mask then -1 else 0 in
    let stack1 = pure_stack lft1 stk1 in
    let stack2 = pure_stack lft2 stk2 in
    let compared, cuniv = match stack1, stack2 with
    | Zlapp a1 :: _, Zlapp a2 :: _ when constructor_first ->
      (* Try mismatched constructors among direct arguments before later eliminations. *)
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
    cmp_rec compared nargs stack1 stack2 cuniv
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

let clos_gen_conv (type err) ~typed ~constructor_relevance
    ~projection_congruence ~dependency_preference trans cv_pb l2r evars env
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
        cnv_probe_budget = None;
        cnv_projection_conversions = ref [];
        cnv_successful_conversions =
          make_successful_conversion_cache successful_conversion_limit;
        cnv_memoize_successful_conversions =
          typed &&
          (Environ.typing_flags env).unfold_dep_heuristic;
        cnv_projection_congruence = projection_congruence;
        cnv_dependency_preference = dependency_preference;
        cnv_constructor_relevance = constructor_relevance;
        cnv_constructor_masks = ConstructorMasks.create 17;
        lft_tab = create_tab ();
        rgt_tab = create_tab ();
        err_ret = box;
      } in
      try
        let result =
          ccnv cv_pb l2r infos el_id el_id (inject t1) (inject t2) univs
        in
        Result.Ok result
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
        cnv_inf = infos;
        cnv_typ = true;
        cnv_rel_types = Range.empty;
        cnv_probe_budget = None;
        cnv_projection_conversions = ref [];
        cnv_successful_conversions = make_successful_conversion_cache 0;
        cnv_memoize_successful_conversions = false;
        cnv_projection_congruence = false;
        cnv_dependency_preference = false;
        cnv_constructor_relevance = false;
        cnv_constructor_masks = ConstructorMasks.create 17;
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

let gen_conv ~typed cv_pb ?(l2r=false) ?(reds=TransparentState.full) env ?(evars=default_evar_handler env) t1 t2 =
  let univs = Environ.universes env in
  let state = univs in
  let b =
    if cv_pb = CUMUL then leq_constr_univs univs t1 t2
    else eq_constr_univs univs t1 t2
  in
    if b then Result.Ok ()
    else
      let convert constructor_relevance projection_congruence
          dependency_preference =
        clos_gen_conv ~typed ~constructor_relevance ~projection_congruence
          ~dependency_preference reds cv_pb l2r evars env univs
          (state, checked_universes) t1 t2
      in
      let conversion () =
        match convert false false false with
        | Result.Ok (_ : 'a * ('a, Empty.t) universe_compare) -> Result.Ok ()
        | Result.Error None when typed -> begin
          match convert true false false with
          | Result.Ok (_ : 'a * ('a, Empty.t) universe_compare) -> Result.Ok ()
          | Result.Error None -> begin
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
          | Result.Error (Some e) -> Empty.abort e
          end
        | Result.Error None -> Result.Error ()
        | Result.Error (Some e) -> Empty.abort e
      in
      if typed && (Environ.typing_flags env).unfold_dep_heuristic then
        (* Prefer dependencies first, retaining the other strategies as fallbacks. *)
        match convert false false true with
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
