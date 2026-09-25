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

type 'e conv_tab = {
  cnv_inf : clos_infos;
  cnv_typ : bool; (* true if the input terms were well-typed *)
  cnv_rel_types : fconstr option Range.t;
  cnv_rel_type_lifts : lift Range.t;
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
  { infos with
    cnv_inf = CClosure.push_relevance infos.cnv_inf r;
    cnv_rel_types = Range.cons typ infos.cnv_rel_types;
    cnv_rel_type_lifts = Range.cons type_lift infos.cnv_rel_type_lifts }

let push_relevances infos nas =
  { infos with
    cnv_inf = CClosure.push_relevances infos.cnv_inf nas;
    cnv_rel_types =
      Array.fold_left (fun types _ -> Range.cons None types) infos.cnv_rel_types nas;
    cnv_rel_type_lifts =
      Array.fold_left (fun lifts _ -> Range.cons el_id lifts) infos.cnv_rel_type_lifts nas }

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

let rec compare_under e1 c1 e2 c2 =
  match Constr.kind c1, Constr.kind c2 with
  | Cast (c1, _, _), _ -> compare_under e1 c1 e2 c2
  | _, Cast (c2, _, _) -> compare_under e1 c1 e2 c2
  | Rel i, Rel j -> begin match Esubst.expand_rel i (fst e1) with
      | Inl _ -> false
      | Inr (k, _) -> begin match Esubst.expand_rel j (fst e2) with
          | Inl _ -> false
          | Inr (k', _) -> Int.equal k k'
        end
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
  | Case _, Case _ | Fix _, Fix _ | CoFix _, CoFix _ -> false (* todo some other time *)
  | Array(_,t1,def1,ty1), Array(_,t2,def2,ty2) ->
    Array.equal_norefl (fun c1 c2 -> compare_under e1 c1 e2 c2) t1 t2
    && compare_under e1 def1 e2 def2
    && compare_under e1 ty1 e2 ty2
  | (Rel _ | Meta _ | Var _ | Sort _ | Prod _ | Lambda _ | LetIn _ | App _
    | Proj _ | Evar _ | Const _ | Ind _ | Construct _ | Case _ | Fix _
    | CoFix _ | Int _ | Float _ | String _ | Array _), _ -> false


let rec fast_test lft1 term1 lft2 term2 = match fterm_of term1, fterm_of term2 with
  | FLIFT (i, term1), (FLIFT _ | FCLOS _) -> fast_test (el_shft i lft1) term1 lft2 term2
  | FCLOS _, FLIFT (j, term2) -> fast_test lft1 term1 (el_shft j lft2) term2
  | FCLOS (c1, (e1,u1)), FCLOS (c2, (e2,u2)) ->
    eq_lift lft1 lft2 &&
    compare_under (e1, u1) c1 (e2, u2) c2
  | FPeanoNat n1, FPeanoNat n2 ->
    Ind.UserOrd.equal n1.peano_ind n2.peano_ind &&
    CClosure.PeanoNatValue.equal n1.peano_value n2.peano_value
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

(* Conversion between  [lft1]term1 and [lft2]term2 *)
let rec ccnv cv_pb l2r infos lft1 lft2 term1 term2 cuniv =
  let fast = fast_test lft1 term1 lft2 term2 in
  if fast then cuniv
  else
    eqappr cv_pb l2r infos (lft1, (term1,[])) (lft2, (term2,[])) cuniv

(* Conversion between [lft1](hd1 v1) and [lft2](hd2 v2) *)
and eqappr cv_pb l2r infos (lft1,st1) (lft2,st2) cuniv =
  Control.check_for_interrupt ();
  (* First head reduce both terms *)
  let ninfos = infos_with_reds infos.cnv_inf RedFlags.betaiotazeta in
  let appr1 = whd_stack ninfos infos.lft_tab (fst st1) (snd st1) in
  let appr2 = whd_stack ninfos infos.rgt_tab (fst st2) (snd st2) in
  eqwhnf cv_pb l2r infos (lft1, appr1) (lft2, appr2) cuniv

(* assumes that appr1 and appr2 are in whnf *)
and eqwhnf cv_pb l2r infos (lft1, (hd1, v1) as appr1) (lft2, (hd2, v2) as appr2) cuniv =
  let env = info_env infos.cnv_inf in
  (* Unit-like operands are convertible when their types are. The type is
     certified again in the current context: the classifications of the
     cases below are only hints. *)
  let unit_eta () =
    Option.bind (unit_operand_type infos lft1 (hd1, v1)) (fun typ1 ->
      Option.bind (unit_like_after_stack infos typ1 []) (fun _ ->
        Option.bind (unit_operand_type infos lft2 (hd2, v2)) (fun typ2 ->
          try Some (ccnv CONV l2r infos el_id el_id typ1 typ2 cuniv)
          with NotConvertible | NotConvertibleTrace _ -> None)))
  in
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
      (try
         let nargs = same_args_size v1 v2 in
         let cuniv = conv_table_key infos ~nargs fl1 fl2 cuniv in
         let () = if irr_flex infos.cnv_inf fl1 then raise NotConvertible (* trigger the fallback *) in
         let mask = if infos.cnv_typ then match fl1 with
         | ConstKey _ -> get_ref_mask infos.cnv_inf infos.lft_tab fl1
         | RelKey _ | VarKey _ -> [||]
         else [||]
         in
         convert_stacks ~mask l2r infos lft1 lft2 v1 v2 cuniv
       with NotConvertible | NotConvertibleTrace _ ->
        (* classified units first, then unfolding, then the operand types *)
        let same = same_unit_like (unit_like_of_flex infos lft1 v1 fl1)
            (fun () -> unit_like_of_flex infos lft2 v2 fl2) in
        match (if same then unit_eta () else None) with
        | Some cuniv -> cuniv
        | None ->
        let r1 = unfold_ref_with_args infos.cnv_inf infos.lft_tab fl1 v1 in
        let r2 = unfold_ref_with_args infos.cnv_inf infos.rgt_tab fl2 v2 in
        match r1, r2 with
        | None, None -> unit_eta_exn ()
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
          let () = Control.check_for_interrupt () in
          (* Determine which constant to unfold first *)
          let unfold_left =
            let order = Conv_oracle.oracle_compare oracle (to_er fl1) (to_er fl2) in
            match order with
            | Conv_oracle.Left -> true
            | Conv_oracle.Right -> false
            | Conv_oracle.Same ->
              (* When oracle doesn't prefer either, optionally use dependency heuristic *)
              let env = CClosure.info_env infos.cnv_inf in
              if (Environ.typing_flags env).unfold_dep_heuristic then
                match fl1, fl2 with
                | ConstKey (cst1, _), ConstKey (cst2, _) ->
                  if Environ.constant_depends_on env cst1 cst2 = Some true then true
                  else if Environ.constant_depends_on env cst2 cst1 = Some true then false
                  else l2r
                | _ -> l2r
              else l2r
          in
          if unfold_left then
            let appr1 = whd_stack ninfos infos.lft_tab t1 v1 in
            eqwhnf cv_pb l2r infos (lft1, appr1) appr2 cuniv
          else
            let appr2 = whd_stack ninfos infos.rgt_tab t2 v2 in
            eqwhnf cv_pb l2r infos appr1 (lft2, appr2) cuniv
        | Some (t1, v1), None ->
          let all = RedFlags.(red_add_transparent all (red_transparent (info_flags infos.cnv_inf))) in
          let t1 = whd_stack (infos_with_reds infos.cnv_inf all) infos.lft_tab t1 v1 in
          eqwhnf cv_pb l2r infos (lft1, t1) appr2 cuniv
        | None, Some (t2, v2) ->
          let all = RedFlags.(red_add_transparent all (red_transparent (info_flags infos.cnv_inf))) in
          let t2 = whd_stack (infos_with_reds infos.cnv_inf all) infos.rgt_tab t2 v2 in
          eqwhnf cv_pb l2r infos appr1 (lft2, t2) cuniv
        )

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
      let congruence () =
        let el1 = el_stack lft1 v1 in
        let el2 = el_stack lft2 v2 in
        let cuniv = ccnv CONV l2r infos el1 el2 c1 c2 cuniv in
        convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
      in
      (* the projections of a unit-like record are compared before unfolding *)
      let congruence_first =
        infos.cnv_typ && (Environ.typing_flags env).unfold_dep_heuristic &&
        same_projections &&
        is_registered_unit_like env (Projection.Repr.inductive (Projection.repr p1))
      in
      begin match
        if congruence_first then
          try Some (congruence ()) with NotConvertible | NotConvertibleTrace _ -> None
        else None
      with
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
          (mk_clos (usubs_lift e) c2) (mk_clos (usubs_lift e') c'2) cuniv

    (* Eta-expansion on the fly *)
    | (FLambda _, _) ->
        let () = match v1 with
        | [] -> ()
        | _ ->
          anomaly (Pp.str "conversion was given unreduced term (FLambda).")
        in
        let (x1,ty1,bd1) = destFLambda mk_clos hd1 in
        let infos = push_relevance ~typ:ty1 ~type_lift:lft1 infos x1 in
        eqappr CONV l2r infos
          (el_lift lft1, (bd1, [])) (el_lift lft2, (hd2, eta_expand_stack infos.cnv_inf x1 v2)) cuniv
    | (_, FLambda _) ->
        let () = match v2 with
        | [] -> ()
        | _ ->
          anomaly (Pp.str "conversion was given unreduced term (FLambda).")
        in
        let (x2,ty2,bd2) = destFLambda mk_clos hd2 in
        let infos = push_relevance ~typ:ty2 ~type_lift:lft2 infos x2 in
        eqappr CONV l2r infos
          (el_lift lft1, (hd1, eta_expand_stack infos.cnv_inf x2 v1)) (el_lift lft2, (bd2, [])) cuniv

    | FCaseInvert _, FRel _ | FRel _, FCaseInvert _ -> unit_eta_exn ()

    (* only one constant, defined var or defined rel *)
    | (FFlex fl1, c2)      ->
      begin match flex_unit_eta lft1 v1 fl1 lft2 v2 c2 with
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
        if UVars.Instance.is_empty u1 || UVars.Instance.is_empty u2 then
          let cuniv = fail_check infos @@ convert_instances ~flex:false u1 u2 cuniv in
          convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
        else
          let mind = Environ.lookup_mind (fst ind1) (info_env infos.cnv_inf) in
          match fail_check infos @@ convert_constructors (mind, snd ind1, j1) nargs u1 u2 cuniv with
          | cuniv -> convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
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

and convert_stacks ?(mask = [||]) l2r infos lft1 lft2 stk1 stk2 cuniv =
  let f (l1, t1) (l2, t2) cuniv = ccnv CONV l2r infos l1 l2 t1 t2 cuniv in
  let rec cmp_rec nargs pstk1 pstk2 cuniv =
    match (pstk1,pstk2) with
      | (z1::s1, z2::s2) ->
          (* Stacks are known to have the same argument size *)
          let rnargs = match z1 with
          | Zlapp a -> if nargs < 0 then -1 else nargs + Array.length a
          | Zlproj _ | Zlfix _ | Zlcase _ | Zlprimitive _ -> -1
          in
          let cu1 = cmp_rec rnargs s1 s2 cuniv in
          (match (z1,z2) with
            | (Zlapp a1,Zlapp a2) ->
              if nargs < 0 then
               Array.fold_right2 f a1 a2 cu1
              else
                let rec fold i cu =
                  if i < 0 then cu
                  else if nargs + i < Array.length mask && not mask.(nargs + i) then
                    fold (i - 1) cu (* skip runtime irrelevant argument *)
                  else
                    let cu = f a1.(i) a2.(i) cu in
                    fold (i - 1) cu
                in
                fold (Array.length a1 - 1) cu1
            | (Zlproj (c1,_l1),Zlproj (c2,_l2)) ->
              if not (Projection.Repr.CanOrd.equal c1 c2) then
                raise NotConvertible
              else cu1
            | (Zlfix(fx1,a1),Zlfix(fx2,a2)) ->
                let cu2 = f fx1 fx2 cu1 in
                cmp_rec (-1) a1 a2 cu2
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
  if compare_stack_shape stk1 stk2 then
    let nargs = if Array.is_empty mask then -1 else 0 in
    cmp_rec nargs (pure_stack lft1 stk1) (pure_stack lft2 stk2) cuniv
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

let clos_gen_conv (type err) ~typed trans cv_pb l2r evars env graph univs t1 t2 =
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
        lft_tab = create_tab ();
        rgt_tab = create_tab ();
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
      let infos = { cnv_inf = infos; cnv_typ = true; lft_tab = tab; rgt_tab = tab; err_ret = box;
                    cnv_rel_types = Range.empty; cnv_rel_type_lifts = Range.empty } in
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

let gen_conv ~typed cv_pb ?(l2r=false) ?(reds=TransparentState.full) env ?(evars=default_evar_handler env) t1 t2 =
  let univs = Environ.universes env in
  let state = univs in
  let b = quick_constr_univs cv_pb univs t1 t2 in
    if b then Result.Ok ()
    else match clos_gen_conv ~typed reds cv_pb l2r evars env univs (state, checked_universes) t1 t2 with
    | Result.Ok (_ : 'a * ('a, Empty.t) universe_compare)-> Result.Ok ()
    | Result.Error None -> Result.Error ()
    | Result.Error (Some e) -> Empty.abort e

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
