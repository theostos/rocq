(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Created by Jean-Christophe Filliâtre as part of the rebuilding of
   Coq around a purely functional abstract type-checker, Dec 1999 *)

(* This file provides the entry points to the kernel type-checker. It
   defines the abstract type of well-formed environments and
   implements the rules that build well-formed environments.

   An environment is made of constants and inductive types (E), of
   section declarations (Delta), of local bound-by-index declarations
   (Gamma) and of universe constraints (C). Below E[Delta,Gamma] |-_C
   means that the tuple E, Delta, Gamma, C is a well-formed
   environment. Main rules are:

   empty_environment:

     ------
     [,] |-

   push_named_assum(a,T):

     E[Delta,Gamma] |-_G
     ------------------------
     E[Delta,Gamma,a:T] |-_G'

   push_named_def(a,t,T):

     E[Delta,Gamma] |-_G
     ---------------------------
     E[Delta,Gamma,a:=t:T] |-_G'

   add_constant(ConstantEntry(DefinitionEntry(c,t,T))):

     E[Delta,Gamma] |-_G
     ---------------------------
     E,c:=t:T[Delta,Gamma] |-_G'

   add_constant(ConstantEntry(ParameterEntry(c,T))):

     E[Delta,Gamma] |-_G
     ------------------------
     E,c:T[Delta,Gamma] |-_G'
   add_mind(Ind(Ind[Gamma_p](Gamma_I:=Gamma_C))):


     E[Delta,Gamma] |-_G
     ------------------------
     E,Ind[Gamma_p](Gamma_I:=Gamma_C)[Delta,Gamma] |-_G'

   etc.
*)

open Util
open Names
open Declarations
open Mod_declarations
open Constr
open Context.Named.Declaration

module NamedDecl = Context.Named.Declaration

(** {6 Safe environments }

  Fields of [safe_environment] :

  - [env] : the underlying environment (cf Environ)
  - [modpath] : the current module name
  - [modvariant] :
    * NONE before coqtop initialization
    * LIBRARY at toplevel of a compilation or a regular coqtop session
    * STRUCT (params,oldsenv) : inside a local module, with
      module parameters [params] and earlier environment [oldsenv]
    * SIG (params,oldsenv) : same for a local module type
  - [modresolver] : delta_resolver concerning the module content, that needs to
    be marshalled on disk. Its root must be [modpath].
  - [paramresolver] : delta_resolver in scope but not part of the library per
    se, that is from functor parameters and required libraries
  - [revstruct] : current module content, most recent declarations first
  - [modlabels] and [objlabels] : names defined in the current module,
      either for modules/modtypes or for constants/inductives.
      These fields could be deduced from [revstruct], but they allow faster
      name freshness checks.
 - [univ] : current universe constraints
 - [future_cst] : delayed opaque constants yet to be checked
 - [required] : names and digests of Require'd libraries since big-bang.
      This field will only grow
 - [loads] : list of libraries Require'd inside the current module.
      They will be propagated to the upper module level when
      the current module ends.
 - [local_retroknowledge]

*)

type vodigest =
  | Dvo_or_vi of Digest.t        (* The digest of the seg_lib part *)

let digest_match ~actual ~required =
  match actual, required with
  | Dvo_or_vi d1, Dvo_or_vi d2 -> String.equal d1 d2

type library_info = DirPath.t * vodigest

(** Functor and funsig parameters, most recent first *)
type module_parameters = (MBId.t * module_type_body) list

type permanent_flags = {
  rewrite_rules_allowed : bool;
}

module ParamResolver :
sig
  type t
  val empty : DirPath.t -> t
  val add_delta_resolver : ModPath.t -> Mod_subst.delta_resolver -> t -> t
  val constant_of_delta_kn : t -> KerName.t -> Constant.t
  val mind_of_delta_kn : t -> KerName.t -> MutInd.t
end =
struct
  type t = {
    root : DirPath.t;
    data : Mod_subst.delta_resolver ModPath.Map.t;
    (** Invariant: No [MPdot] in data *)
  }

  let empty root = {
    root = root;
    data = ModPath.Map.empty;
  }

  let rec head mp = match mp with
  | MPfile _ | MPbound _ -> mp
  | MPdot (mp, _) -> head mp

  let add_delta_resolver mp delta preso =
    let self = MPfile preso.root in
    let data =
      if ModPath.subpath self mp then
        match ModPath.Map.find_opt self preso.data with
        | None ->
          (* we were at toplevel *)
          ModPath.Map.add self delta preso.data
        | Some reso ->
          ModPath.Map.add self (Mod_subst.add_delta_resolver delta reso) preso.data
      else
        let () = match mp with
        | MPfile _ | MPbound _ -> ()
        | MPdot _ -> assert false
        in
        let () = assert (not (ModPath.Map.mem mp preso.data)) in
        ModPath.Map.add mp delta preso.data
    in
    { preso with data }

  let kn_of_delta preso kn =
    let head = head (KerName.modpath kn) in
    match ModPath.Map.find_opt head preso.data with
    | None -> kn
    | Some delta -> Mod_subst.kn_of_delta delta kn

  let constant_of_delta_kn preso kn = Constant.make kn (kn_of_delta preso kn)

  let mind_of_delta_kn preso kn = MutInd.make kn (kn_of_delta preso kn)

end

type compiled_library = {
  comp_name : DirPath.t;
  comp_mod : module_body;
  comp_univs : Univ.ContextSet.t;
  comp_sorts : Sorts.QGlobal.Set.t * Sorts.ElimConstraints.t;
  comp_deps : library_info array;
  comp_flags : permanent_flags;
  comp_retro : Retroknowledge.action list;
}

type reimport = compiled_library * Vmlibrary.on_disk * vodigest

type required_lib = {
  req_root : bool; (* true if a root of the dependency DAG *)
  req_digest : vodigest;
}

(** Part of the safe_env at a section opening time to be backtracked *)
type section_data = {
  rev_env : Environ.env;
  rev_univ : Univ.ContextSet.t;
  rev_qualities : Sorts.QGlobal.Set.t * Sorts.ElimConstraints.t;
  rev_objlabels : Id.Set.t;
  rev_reimport : reimport list;
  rev_revstruct : structure_body;
  rev_paramresolver : ParamResolver.t;
}

module HandleMap = Opaqueproof.HandleMap

(** We rely on uniqueness of pointers to provide a simple implementation of
    kernel certificates. For this to work across processes, one needs the
    safe environments to be marshaled at the same time as their corresponding
    certificates and sharing to be preserved. *)
module Nonce :
sig
  type t
  val create : unit -> t
  val equal : t -> t -> bool
end =
struct
  type t = unit ref
  let create () = ref ()
  let equal x y = x == y
end

type safe_environment =
  { env : Environ.env;
    sections : section_data Section.t option;
    modpath : ModPath.t;
    modvariant : modvariant;
    modresolver : Mod_subst.delta_resolver;
    paramresolver : ParamResolver.t;
    revstruct : structure_body;
    modlabels : Id.Set.t;
    objlabels : Id.Set.t;
    univ : Univ.ContextSet.t;
    qualities : Sorts.QGlobal.Set.t;
    elims : Sorts.ElimConstraints.t;
    future_cst : (Constant_typing.typing_context * safe_environment * Nonce.t) HandleMap.t;
    required : required_lib DirPath.Map.t;
    loads : (ModPath.t * module_body) list;
    local_retroknowledge : Retroknowledge.action list;
    opaquetab : Opaqueproof.opaquetab;
}

and modvariant =
  | NONE
  | LIBRARY
  | SIG of module_parameters * safe_environment (** saved env *)
  | STRUCT of module_parameters * safe_environment (** saved env *)

let rec library_dp_of_senv senv =
  match senv.modvariant with
  | NONE | LIBRARY -> ModPath.dp senv.modpath
  | SIG(_,senv) -> library_dp_of_senv senv
  | STRUCT(_,senv) -> library_dp_of_senv senv

let empty_environment =
  { env = Environ.empty_env;
    modpath = ModPath.dummy;
    modvariant = NONE;
    modresolver = Mod_subst.empty_delta_resolver ModPath.dummy;
    paramresolver = ParamResolver.empty DirPath.dummy;
    revstruct = [];
    modlabels = Id.Set.empty;
    objlabels = Id.Set.empty;
    sections = None;
    future_cst = HandleMap.empty;
    univ = Univ.ContextSet.empty;
    qualities = Sorts.QGlobal.Set.empty;
    elims = Sorts.ElimConstraints.empty;
    required = DirPath.Map.empty;
    loads = [];
    local_retroknowledge = [];
    opaquetab = Opaqueproof.empty_opaquetab;
}

let is_initial senv =
  match senv.revstruct, senv.modvariant with
  | [], NONE -> ModPath.equal senv.modpath ModPath.dummy
  | _ -> false

let sections_are_opened senv = not (Option.is_empty senv.sections)

let delta_of_senv senv = senv.modresolver

let constant_of_delta_kn_senv senv kn =
  let mp = KerName.modpath kn in
  if ModPath.subpath senv.modpath mp then Mod_subst.constant_of_delta_kn senv.modresolver kn
  else ParamResolver.constant_of_delta_kn senv.paramresolver kn

let mind_of_delta_kn_senv senv kn =
  let mp = KerName.modpath kn in
  if ModPath.subpath senv.modpath mp then Mod_subst.mind_of_delta_kn senv.modresolver kn
  else ParamResolver.mind_of_delta_kn senv.paramresolver kn

(** The safe_environment state monad *)

type safe_transformer0 = safe_environment -> safe_environment
type 'a safe_transformer = safe_environment -> 'a * safe_environment


(** {6 Typing flags } *)

let set_typing_flags c senv =
  let env = Environ.set_typing_flags c senv.env in
  if env == senv.env then senv
  else { senv with env }

let set_typing_flags flags senv =
  (* NB: we allow changing the conv_oracle inside sections because it
     doesn't matter for consistency. *)
  if Option.has_some senv.sections
  && not (Environ.same_flags flags
            {(Environ.typing_flags senv.env) with
             conv_oracle = flags.conv_oracle;
             share_reduction = flags.share_reduction;
            })
  then CErrors.user_err Pp.(str "Changing typing flags inside sections is not allowed.");
  set_typing_flags flags senv

let set_impredicative_set b senv =
  let flags = Environ.typing_flags senv.env in
  set_typing_flags { flags with impredicative_set = b } senv

let set_check_guarded b senv =
  let flags = Environ.typing_flags senv.env in
  set_typing_flags { flags with check_guarded = b } senv

let set_check_positive b senv =
  let flags = Environ.typing_flags senv.env in
  set_typing_flags { flags with check_positive = b } senv

let set_check_universes b senv =
  let flags = Environ.typing_flags senv.env in
  set_typing_flags { flags with check_universes = b } senv

let set_indices_matter indices_matter senv =
  set_typing_flags { (Environ.typing_flags senv.env) with indices_matter } senv

let set_share_reduction b senv =
  let flags = Environ.typing_flags senv.env in
  set_typing_flags { flags with share_reduction = b } senv

let set_unfold_dep_heuristic b senv =
  let flags = Environ.typing_flags senv.env in
  set_typing_flags { flags with unfold_dep_heuristic = b } senv

let set_VM b senv =
  let flags = Environ.typing_flags senv.env in
  set_typing_flags { flags with enable_VM = b } senv

let set_native_compiler b senv =
  let flags = Environ.typing_flags senv.env in
  set_typing_flags { flags with enable_native_compiler = b } senv

let set_allow_sprop b senv = { senv with env = Environ.set_allow_sprop b senv.env }

let set_rewrite_rules_allowed b senv =
  if b then { senv with env = Environ.allow_rewrite_rules senv.env }
  else senv

(* Temporary sets custom typing flags *)
let with_typing_flags ?typing_flags senv ~f =
  match typing_flags with
  | None -> f senv
  | Some typing_flags ->
    let orig_typing_flags = Environ.typing_flags senv.env in
    let res, senv = f (set_typing_flags typing_flags senv) in
    res, set_typing_flags orig_typing_flags senv

(* f1 is stricter than f2 if terms typed with f1 also type with f2 *)
let stricter_flags f1 f2 =
  let impl b1 b2 = if b1 then b2 else true in
  let {
    check_guarded = check_guarded1;
    check_positive = check_positive1;
    check_universes = check_universes1;
    check_eliminations = check_eliminations1;
    indices_matter = indices_matter1;
    impredicative_set = impredicative_set1;
    sprop_allowed = sprop_allowed1;
    allow_uip = allow_uip1;
    (* The flags below do not change the theory *)
    conv_oracle = _;
    share_reduction = _;
    unfold_dep_heuristic = _;
    enable_VM = _;
    enable_native_compiler = _;
  } = f1
  in
  let {
    check_guarded = check_guarded2;
    check_positive = check_positive2;
    check_universes = check_universes2;
    check_eliminations = check_eliminations2;
    indices_matter = indices_matter2;
    impredicative_set = impredicative_set2;
    sprop_allowed = sprop_allowed2;
    allow_uip = allow_uip2;
    (* The flags below do not change the theory *)
    conv_oracle = _;
    share_reduction = _;
    unfold_dep_heuristic = _;
    enable_VM = _;
    enable_native_compiler = _;
  } = f2
  in
  impl check_guarded2 check_guarded1 &&
  impl check_positive2 check_positive1 &&
  impl check_universes2 check_universes1 &&
  impl check_eliminations2 check_eliminations1 &&
  impl indices_matter2 indices_matter1 &&
  (* Beware: the order is reversed below because a "true" flag is laxer *)
  impl impredicative_set1 impredicative_set2 &&
  impl sprop_allowed1 sprop_allowed2 &&
  impl allow_uip1 allow_uip2

(** {6 Stm machinery } *)

module Certificate :
sig
  type t

  val make : safe_environment -> t

  val universes : t -> Univ.ContextSet.t

  (** Checks whether [dst] is a valid extension of [src] by 1 declaration,
      possibly adding universes and constraints. *)
  val safe_extend : src:t -> dst:t -> t option

  (** [compatible src dst] checks whether [dst] adds exactly 1 declaration
      to an ancestor of [src] and the typing flags are compatible.
      If so, the declaration is also valid in [src] (up to universes). *)
  val compatible : safe_environment -> t -> bool
end =
struct

type t = {
  certif_struc : Mod_declarations.structure_body;
  certif_univs : Univ.ContextSet.t;
  certif_flags : Declarations.typing_flags;
}

let make senv = {
  certif_struc = senv.revstruct;
  certif_univs = senv.univ;
  certif_flags = Environ.typing_flags senv.env;
}

let is_suffix l suf = match l with
| [] -> false
| _ :: l -> l == suf

let safe_extend ~src ~dst =
  if is_suffix dst.certif_struc src.certif_struc && stricter_flags dst.certif_flags src.certif_flags then
    Some { certif_struc = dst.certif_struc;
           certif_univs = Univ.ContextSet.union src.certif_univs dst.certif_univs;
           certif_flags = dst.certif_flags }
  else None

let compatible src dst =
  stricter_flags dst.certif_flags (Environ.typing_flags src.env) &&
  let dst = dst.certif_struc in
  let src = src.revstruct in
  match dst with
  | [] -> false
  | _ :: dst_base ->
    let rec aux src =
      src == dst_base || match src with
      | [] -> false
      | _ :: src -> aux src
    in
    aux src

let universes c = c.certif_univs

end

type side_effect = {
  seff_certif : Certificate.t CEphemeron.key;
  seff_constant : Constant.t;
  seff_body : HConstr.t option * (Constr.t, Vmemitcodes.body_code) Declarations.pconstant_body;
  seff_univs : Univ.ContextSet.t;
}
(* Invariant: For any senv, if [Certificate.safe_extend senv seff_certif] returns [Some certif'] then
   [senv + Certificate.universes certif' + (c.seff_constant -> seff_body)] is well-formed
   (if no univ inconsistency). *)

module SideEffects :
sig
  type t
  val repr : t -> side_effect list
  val empty : t
  val is_empty : t -> bool
  val add : side_effect -> t -> t
  val concat : t -> t -> t
  val length : t -> int
  val pop : t -> int -> t * t
end =
struct

module SeffOrd = struct
type t = side_effect
let compare e1 e2 =
  Constant.UserOrd.compare e1.seff_constant e2.seff_constant
end

module SeffSet = Set.Make(SeffOrd)

type t = { seff : side_effect list; elts : SeffSet.t; len : int }
(** Invariant: [seff] is a permutation of the elements of [elts] *)

let repr eff = eff.seff
let empty = { seff = []; elts = SeffSet.empty; len = 0 }
let is_empty { seff; elts; _ } = List.is_empty seff && SeffSet.is_empty elts
let add x es =
  if SeffSet.mem x es.elts then es
  else { seff = x :: es.seff; elts = SeffSet.add x es.elts; len = es.len + 1 }
let concat xes yes =
  List.fold_right add xes.seff yes

let length eff = eff.len

let pop eff n =
  let () = assert (n <= eff.len) in
  let top, rem = List.chop n eff.seff in
  let fold accu x = SeffSet.remove x accu in
  let elts = List.fold_left fold eff.elts top in
  { seff = top; len = n; elts = SeffSet.of_list top }, { seff = rem; len = eff.len - n; elts }

end

type private_constants = SideEffects.t

let debug_print_private_constants seff =
  let open Pp in
  prlist_with_sep spc (fun seff -> Constant.print seff.seff_constant) (SideEffects.repr seff)

let side_effects_of_private_constants l =
  List.rev (SideEffects.repr l)

let length_private = SideEffects.length
let pop_private = SideEffects.pop

(* Only used to push in an Environ.env. *)
let lift_constant c =
  let body = match c.const_body with
  | OpaqueDef _ -> Undef None
  | Def _ | Undef _ | Primitive _ | Symbol _ as body -> body
  in
  { c with const_body = body }

let push_bytecode vmtab code =
  let open Vmemitcodes in
  let vmtab, code = match code with
  | BCdefined (mask, code, patches) ->
    let vmtab, index = Vmlibrary.add code vmtab in
    vmtab, BCdefined (mask, index, patches)
  | BCconstant | BCuncompiled | BCalias _ as code -> vmtab, code
  in
  vmtab, code

let push_private_constants env eff =
  let eff = side_effects_of_private_constants eff in
  let add_if_undefined env eff =
    if Environ.mem_constant eff.seff_constant env then env
    else
      let (_hbody, cb) = eff.seff_body in
      let vmtab, code = push_bytecode (Environ.vm_library env) cb.const_body_code in
      let cb = { cb with const_body_code = code } in
      let env = Environ.set_vm_library vmtab env in
      Environ.add_constant eff.seff_constant (lift_constant cb) env
  in
  List.fold_left add_if_undefined env eff

let empty_private_constants = SideEffects.empty
let is_empty_private_constants c = SideEffects.is_empty c
let concat_private = SideEffects.concat

let universes_of_private eff =
  let fold acc eff = Univ.ContextSet.union eff.seff_univs acc in
  List.fold_left fold Univ.ContextSet.empty (side_effects_of_private_constants eff)

let constants_of_private eff =
  let fold acc eff = eff.seff_constant :: acc in
  List.fold_left fold [] (side_effects_of_private_constants eff)

let env_of_safe_env senv = senv.env
let env_of_senv = env_of_safe_env

let structure_body_of_safe_env env = env.revstruct

let sections_of_safe_env senv = senv.sections

let rec is_modtype senv =
  match senv.modvariant with
  | STRUCT (_,senv) -> is_modtype senv
  | SIG _ -> true
  | NONE | LIBRARY -> false

let get_section = function
  | None -> CErrors.user_err Pp.(str "No open section.")
  | Some s -> s

let push_context_set ~strict cst senv =
  if Univ.ContextSet.is_empty cst then senv
  else
    let sections = Option.map (Section.push_level_constraints cst) senv.sections
    in
    { senv with
      env = Environ.push_context_set ~strict cst senv.env;
      univ = Univ.ContextSet.union cst senv.univ;
      sections }

let current_modpath senv = senv.modpath
let current_dirpath senv = Names.ModPath.dp (current_modpath senv)

let new_global_sort senv =
  if is_modtype senv then
    CErrors.user_err (Pp.str "Cannot declare global sort qualities inside module types.")
  else if Option.has_some senv.sections then
    CErrors.user_err (Pp.str "Cannot declare global sort qualities inside sections.")
  else
  let module QG = Sorts.QGlobal in
  let uid = QG.Set.cardinal senv.qualities in
  let s = QG.make (current_dirpath senv) uid in
  let qualities = QG.Set.add s senv.qualities in
  let env = Environ.push_qualities (Sorts.Quality.Set.singleton (QGlobal s)) senv.env in
  s, { senv with
       env;
       qualities;
     }

let merge_elim_constraints qcsts senv =
  if Sorts.ElimConstraints.is_empty qcsts then
    senv
  else if is_modtype senv then
    CErrors.user_err (Pp.str "Cannot declare global sort qualities inside module types.")
  else if Option.has_some senv.sections then
    CErrors.user_err (Pp.str "Cannot declare global sort qualities inside sections.")
  else
    let env = Environ.merge_elim_constraints ~rigid:true qcsts senv.env in
    { senv with
      env;
      elims = Sorts.ElimConstraints.union qcsts senv.elims;
    }

let is_curmod_library senv =
  match senv.modvariant with LIBRARY -> true | _ -> false

let is_joined_environment e = HandleMap.is_empty e.future_cst

(** {6 Various checks } *)

let exists_modlabel l senv = Id.Set.mem l senv.modlabels
let exists_objlabel l senv = Id.Set.mem l senv.objlabels

let check_modlabel l senv =
  if exists_modlabel l senv then Modops.error_existing_label l

let check_objlabel l senv =
  if exists_objlabel l senv then Modops.error_existing_label l

let check_objlabels ls senv =
  Id.Set.iter (fun l -> check_objlabel l senv) ls

(** Are we closing the right module / modtype ?
    No user error here, since the opening/ending coherence
    is now verified in [vernac_end_segment] *)

let check_current_label lab = function
  | MPdot (_,l) -> assert (Id.equal lab l)
  | _ -> assert false

let check_struct = function
  | STRUCT (params,oldsenv) -> params, oldsenv
  | NONE | LIBRARY | SIG _ -> assert false

let check_sig = function
  | SIG (params,oldsenv) -> params, oldsenv
  | NONE | LIBRARY | STRUCT _ -> assert false

let check_current_library dir senv = match senv.modvariant with
  | LIBRARY -> assert (ModPath.equal senv.modpath (MPfile dir))
  | NONE | STRUCT _ | SIG _ -> assert false (* cf Lib.end_compilation *)

(** When operating on modules, we're normally outside sections *)

let check_empty_context senv =
  assert (Environ.empty_context senv.env && Option.is_empty senv.sections)

(** When adding a parameter to the current module/modtype,
    it must have been freshly started *)

let check_empty_struct senv =
  assert (List.is_empty senv.revstruct
          && List.is_empty senv.loads)

(** When loading a library, its dependencies should be already there,
    with the correct digests. *)

let check_required current_libs needed =
  let check current (id, required) = match DirPath.Map.find_opt id current with
  | None ->
    CErrors.user_err Pp.(pr_sequence str ["Reference to unknown module"; DirPath.to_string id; "."])
  | Some { req_root; req_digest = actual } ->
    if not (digest_match ~actual ~required) then
      CErrors.user_err Pp.(pr_sequence str
        ["Inconsistent assumptions over module"; DirPath.to_string id; "."])
    else if req_root then
      (* the library is being transitively required, not a root anymore *)
      DirPath.Map.set id { req_root = false; req_digest = actual } current
    else
      (* nothing to do *)
      current
  in
  Array.fold_left check current_libs needed

(** When loading a library, the current flags should match
    those needed for the library *)

let check_flags_for_library lib senv =
  let { rewrite_rules_allowed } = lib.comp_flags in
  set_rewrite_rules_allowed rewrite_rules_allowed senv

(** {6 Insertion of section variables} *)

(** They are now typed before being added to the environment.
    Same as push_named, but check that the variable is not already
    there. Should *not* be done in Environ because tactics add temporary
    hypothesis many many times, and the check performed here would
    cost too much. *)

let safe_push_named d env =
  let id = NamedDecl.get_id d in
  let _ =
    try
      let _ = Environ.lookup_named id env in
      CErrors.user_err Pp.(pr_sequence str ["Identifier"; Id.to_string id; "already defined."])
    with Not_found -> () in
  Environ.push_named SecVar d env

let push_named_def (id,de) senv =
  let sections = get_section senv.sections in
  let c, r, typ = Constant_typing.infer_local_def senv.env id de in
  let d = LocalDef (Context.make_annot id r, c, typ) in
  let env'' = safe_push_named d senv.env in
  let sections = Section.push_local d sections in
  { senv with sections=Some sections; env = env'' }

let push_named_assum (x,t) senv =
  let sections = get_section senv.sections in
  let t, r = Constant_typing.infer_local_assum senv.env t in
  let d = LocalAssum (Context.make_annot x r, t) in
  let sections = Section.push_local d sections in
  let env'' = safe_push_named d senv.env in
  { senv with sections=Some sections; env = env'' }

let push_section_context uctx senv =
  let sections = get_section senv.sections in
  let sections = Section.push_local_universe_context uctx sections in
  let senv = { senv with sections=Some sections } in
  let qctx, ctx = UVars.UContext.to_context_set uctx in
  let check_quality q =
    Sorts.QVar.is_secvar q &&
    not (QGraph.is_declared (Sorts.Quality.QVar q) (Environ.qualities senv.env))
  in
  if not @@ Sorts.QVar.Set.for_all check_quality (fst qctx) then
    CErrors.user_err Pp.(str "Implicit section-wide sort variables are not allowed.");
  let check_fresh u = match UGraph.check_declared_universes (Environ.universes senv.env) (Univ.Level.Set.singleton u) with
  | Result.Ok _ -> assert false
  | Result.Error _ -> ()
  in
  let () = Univ.Level.Set.iter check_fresh (fst ctx) in
  let env = Environ.push_context_set ~strict:false ctx senv.env in
  (* FIXME: check validity of the sort context *)
  (* FIXME: marking the section-local sorts as rigid makes little sense *)
  let env = Environ.push_qualities (Sorts.Quality.Set.of_qvars @@ fst qctx) env in
  let env = Environ.merge_elim_constraints ~rigid:true (snd qctx) env in
  { senv with
    env;
    univ = Univ.ContextSet.union ctx senv.univ;
  }

(** {6 Insertion of new declarations to current environment } *)

let labels_of_mib mib =
  let add,get =
    let labels = ref Id.Set.empty in
    (fun id -> labels := Id.Set.add id !labels),
    (fun () -> !labels)
  in
  let visit_mip mip =
    add mip.mind_typename;
    Array.iter add mip.mind_consnames
  in
  Array.iter visit_mip mib.mind_packets;
  get ()

let add_retroknowledge pttc senv =
  (* Retroknowledge is only allowed in nested modules *)
  let rec is_nested = function
  | LIBRARY -> true
  | STRUCT ([], senv) -> is_nested senv.modvariant
  | SIG _ | NONE | STRUCT (_ :: _, _) -> false
  in
  let () = if sections_are_opened senv || not (is_nested senv.modvariant) then
    CErrors.user_err Pp.(str "Registering a kernel type is only allowed at toplevel.")
  in
  let () = assert (is_nested senv.modvariant) in
  { senv with
    env = Primred.add_retroknowledge senv.env pttc;
    local_retroknowledge = pttc::senv.local_retroknowledge }

(** A generic function for adding a new field in a same environment.
    It also performs the corresponding [add_constraints]. *)

type generic_name =
  | C of Constant.t
  | I of MutInd.t
  | R
  | M of ModPath.t
  | MT of ModPath.t

let add_field ((l,sfb) as field) gn senv =
  let mlabs,olabs = match sfb with
    | SFBmind mib ->
      let l = labels_of_mib mib in
      check_objlabels l senv; (Id.Set.empty,l)
    | SFBconst _ | SFBrules _ ->
      check_objlabel l senv; (Id.Set.empty, Id.Set.singleton l)
    | SFBmodule _ | SFBmodtype _ ->
      check_modlabel l senv; (Id.Set.singleton l, Id.Set.empty)
  in
  let env' = match sfb, gn with
    | SFBconst cb, C con -> Environ.add_constant con cb senv.env
    | SFBmind mib, I mind -> Environ.add_mind mind mib senv.env
    | SFBmodtype mtb, MT mp -> Environ.add_modtype mp mtb senv.env
    | SFBmodule mb, M mp -> Modops.add_module mp mb senv.env
    | SFBrules r, R -> Environ.add_rewrite_rules r.rewrules_rules senv.env
    | _ -> assert false
  in
  let sections = match senv.sections with
    | None -> None
    | Some sections ->
      match sfb, gn with
      | SFBconst cb, C con ->
        let poly = Declareops.constant_is_polymorphic cb in
        Some Section.(push_global ~poly env' (SecDefinition con) sections)
      | SFBmind mib, I mind ->
        let poly = Declareops.inductive_is_polymorphic mib in
        Some Section.(push_global ~poly env' (SecInductive mind) sections)
      | _, (M _ | MT _) -> Some sections
      | _ -> assert false
  in
  { senv with
    env = env';
    sections;
    revstruct = field :: senv.revstruct;
    modlabels = Id.Set.union mlabs senv.modlabels;
    objlabels = Id.Set.union olabs senv.objlabels }

(** Applying a certain function to the resolver of a safe environment *)

let update_resolver f senv = { senv with modresolver = f senv.modresolver }

type exported_opaque = {
  exp_handle : Opaqueproof.opaque_handle;
  exp_body : Constr.t;
  exp_univs : (int * int) option;
  (* Minimal amount of data needed to rebuild the private universes. We enforce
     in the API that private constants have no internal constraints. *)
}
type exported_private_constant = Constant.t * exported_opaque option

let repr_exported_opaque o =
  let priv = match o .exp_univs with
  | None -> Opaqueproof.PrivateMonomorphic ()
  | Some _ -> Opaqueproof.PrivatePolymorphic Univ.ContextSet.empty
  in
  (o.exp_handle, (o.exp_body, priv))

let set_vm_library lib senv =
  { senv with env = Environ.set_vm_library lib senv.env }

let push_const_bytecode senv cb =
  let vmtab, code = push_bytecode (Environ.vm_library senv.env) cb.const_body_code in
  let cb = { cb with const_body_code = code } in
  let senv = set_vm_library vmtab senv in
  senv, cb

let make_hbody = function
  | None -> None
  | Some hc -> Some (fun c ->
      assert (c == HConstr.self hc);
      snd @@ HConstr.hcons hc)

let add_constant_aux senv ?hbody (kn, cb) =
  let l = Constant.label kn in
  (* This is the only place where we hashcons the contents of a constant body *)
  let senv, cb = push_const_bytecode senv cb in
  let cb = if sections_are_opened senv then cb else
      Declareops.hcons_const_body ?hbody:(make_hbody hbody) cb
  in
  let senv' = add_field (l,SFBconst cb) (C kn) senv in
  let senv'' = match cb.const_body with
    | Undef (Some lev) ->
      update_resolver
        (Mod_subst.add_inline_delta_resolver (Constant.user kn) (lev,None)) senv'
    | _ -> senv'
  in
  senv''

let inline_side_effects env body side_eff =
  let open Constr in
  (** First step: remove the constants that are still in the environment *)
  let filter e =
    if Environ.mem_constant e.seff_constant env then None
    else Some e
  in
  (* CAVEAT: we assure that most recent effects come first *)
  let side_eff = List.map_filter filter (SideEffects.repr side_eff) in
  let sigs = List.rev_map (fun e -> e.seff_constant, e.seff_certif) side_eff in
  (** Most recent side-effects first in side_eff *)
  if List.is_empty side_eff then (body, Univ.ContextSet.empty, sigs, 0)
  else
    (** Second step: compute the lifts and substitutions to apply *)
    let cname c r = Context.make_annot (Name (Constant.label c)) r in
    let fold (subst, var, ctx, args) { seff_constant = c; seff_body = (_hbody, cb); seff_univs = univs; _ } =
      let (b, opaque) = match cb.const_body with
      | Def b -> (b, false)
      | OpaqueDef b -> (b, true)
      | _ -> assert false
      in
      match cb.const_universes with
      | Monomorphic ->
        (** Abstract over the term at the top of the proof *)
        let ty = cb.const_type in
        let subst = Cmap_env.add c (Inr var) subst in
        let ctx = Univ.ContextSet.union ctx univs in
        (subst, var + 1, ctx, (cname c cb.const_relevance, b, ty, opaque) :: args)
      | Polymorphic _ ->
        let () = assert (Univ.ContextSet.is_empty univs) in
        (** Inline the term to emulate universe polymorphism *)
        let subst = Cmap_env.add c (Inl b) subst in
        (subst, var, ctx, args)
    in
    let (subst, len, ctx, args) = List.fold_left fold (Cmap_env.empty, 1, Univ.ContextSet.empty, []) side_eff in
    (** Third step: inline the definitions *)
    let rec subst_const i k t = match Constr.kind t with
    | Const (c, u) ->
      let data = try Some (Cmap_env.find c subst) with Not_found -> None in
      begin match data with
      | None -> t
      | Some (Inl b) ->
        (** [b] is closed but may refer to other constants *)
        subst_const i k (Vars.subst_instance_constr u b)
      | Some (Inr n) ->
        mkRel (k + n - i)
      end
    | Rel n ->
      (** Lift free rel variables *)
      if n <= k then t
      else mkRel (n + len - i - 1)
    | _ -> Constr.map_with_binders ((+) 1) (fun k t -> subst_const i k t) k t
    in
    let map_args i (na, b, ty, opaque) =
      (** Both the type and the body may mention other constants *)
      let ty = subst_const (len - i - 1) 0 ty in
      let b = subst_const (len - i - 1) 0 b in
      (na, b, ty, opaque)
    in
    let args = List.mapi map_args args in
    let body = subst_const 0 0 body in
    let fold_arg (na, b, ty, opaque) accu =
      if opaque then mkApp (mkLambda (na, ty, accu), [|b|])
      else mkLetIn (na, b, ty, accu)
    in
    let body = List.fold_right fold_arg args body in
    (body, ctx, sigs, len - 1)

let inline_private_constants env ((body, ctx), side_eff) =
  let body, ctx', _, _ = inline_side_effects env body side_eff in
  let ctx' = Univ.ContextSet.union ctx ctx' in
  (body, ctx')

let warn_failed_cert = CWarnings.create ~name:"failed-abstract-certificate"
    ~category:CWarnings.CoreCategories.tactics ~default:CWarnings.AsError
    Pp.(fun kn ->
        str "Certificate for private constant " ++
        Id.print (Constant.label kn) ++
        str " failed.")

(* Given the list of signatures of side effects, checks if they match.
 * I.e. if they are ordered descendants of an ancestor of the current revstruct.
   Returns the universes needed to trust the side effects (None if they can't be trusted). *)
let check_signatures senv sl =
  match sl with
  | [] -> Ok Univ.ContextSet.empty
  | (firstkn,first) :: rest ->
    match CEphemeron.get first with
    | exception CEphemeron.InvalidKey -> Error None
    | first ->
    if not (Certificate.compatible senv first) then Error (Some firstkn)
    else
      let is_direct_ancestor curmb (kn, mb) =
        match CEphemeron.get mb with
        | exception CEphemeron.InvalidKey -> Error None
        | mb ->
          let mb = Certificate.safe_extend ~src:curmb ~dst:mb in
          match mb with
          | None -> Error (Some kn)
          | Some mb -> Ok mb
      in
      let accu = List.fold_left_error is_direct_ancestor first rest in
      match accu with
      | Error _ as e -> e
      | Ok mb ->
        let univs = Certificate.universes mb in
        Ok (Univ.ContextSet.diff univs senv.univ)

let check_signatures senv sl =
  match check_signatures senv sl with
  | Ok univs -> Some univs
  | Error None ->
    (* don't warn when the issue is an invalid ephemeron *)
    None
  | Error (Some kn) -> warn_failed_cert kn; None

type side_effect_declaration =
| DefinitionEff : Entries.definition_entry -> side_effect_declaration
| OpaqueEff : Constr.constr Entries.opaque_entry -> side_effect_declaration

let constant_entry_of_side_effect eff =
  let (_hbody, cb) = eff.seff_body in
  let open Entries in
  let univs =
    match cb.const_universes with
    | Monomorphic ->
      Monomorphic_entry
    | Polymorphic auctx ->
      Polymorphic_entry (UVars.AbstractContext.repr auctx)
  in
  let p =
    match cb.const_body with
    | OpaqueDef b -> b
    | Def b -> b
    | _ -> assert false in
  if Declareops.is_opaque cb then
  OpaqueEff {
    opaque_entry_body = p;
    opaque_entry_secctx = Context.Named.to_vars cb.const_hyps;
    opaque_entry_type = cb.const_type;
    opaque_entry_universes = univs;
  }
  else
  DefinitionEff {
    definition_entry_body = p;
    definition_entry_secctx = Some (Context.Named.to_vars cb.const_hyps);
    definition_entry_type = Some cb.const_type;
    definition_entry_universes = univs;
    definition_entry_inline_code = cb.const_inline_code }

let export_eff eff =
  (eff.seff_constant, eff.seff_body)

let is_empty_private = function
| Opaqueproof.PrivateMonomorphic ctx -> Univ.ContextSet.is_empty ctx
| Opaqueproof.PrivatePolymorphic ctx -> Univ.ContextSet.is_empty ctx

let compile_bytecode env cb =
  let code = Vmbytegen.compile_constant_body ~fail_on_error:false env cb.const_universes cb.const_body in
  { cb with const_body_code = code }

(* Special function to call when the body of an opaque definition is provided.
  It performs the type-checking of the body immediately. *)
let infer_direct_opaque ~sec_univs env ce =
  let cb, ctx = Constant_typing.infer_opaque ~sec_univs env ce in
  let body = ce.Entries.opaque_entry_body, Univ.ContextSet.empty in
  let handle _env c () = (c, Univ.ContextSet.empty, 0) in
  let (hbody, c, u) = Constant_typing.check_delayed handle ctx (body, ()) in
  (* No constraints can be generated, we set it empty everywhere *)
  let () = assert (is_empty_private u) in
  hbody, { cb with const_body = OpaqueDef c }

let export_side_effects senv eff =
  let sec_univs = Option.map Section.all_poly_univs senv.sections in
  let env = senv.env in
  let not_exists e = not (Environ.mem_constant e.seff_constant env) in
  let aux (acc,sl) e =
    if not (not_exists e) then acc, sl
    else e :: acc, (e.seff_constant, e.seff_certif) :: sl in
  let seff, signatures = List.fold_left aux ([],[]) (SideEffects.repr eff) in
  let trusted = check_signatures senv signatures in
  let push_seff env eff =
    let { seff_constant = kn; seff_body = (_hbody, cb); _ } = eff in
    let vmtab, code = push_bytecode (Environ.vm_library env) cb.const_body_code in
    let env = Environ.set_vm_library vmtab env in
    let cb = { cb with const_body_code = code } in
    let env = Environ.add_constant kn (lift_constant cb) env in
    env
  in
  match trusted with
  | Some univs ->
    univs, List.map export_eff seff
  | None ->
    let rec recheck_seff seff univs acc env = match seff with
      | [] -> univs, List.rev acc
      | eff :: rest ->
        let uctx = eff.seff_univs in
        let env = Environ.push_context_set ~strict:true uctx env in
        let univs = Univ.ContextSet.union uctx univs in
        let env, cb =
          let ce = constant_entry_of_side_effect eff in
          let hbody, cb = match ce with
            | DefinitionEff ce ->
              Constant_typing.infer_definition ~sec_univs env ce
            | OpaqueEff ce ->
              infer_direct_opaque ~sec_univs env ce
          in
          let cb = compile_bytecode env cb in
          let eff = { eff with seff_body = (hbody, cb) } in
          (push_seff env eff, export_eff eff)
        in
        recheck_seff rest univs (cb :: acc) env
    in
    recheck_seff seff Univ.ContextSet.empty [] env

let push_opaque_proof senv =
  let o, otab = Opaqueproof.create (library_dp_of_senv senv) senv.opaquetab in
  let senv = { senv with opaquetab = otab } in
  senv, o

let export_private_constants eff senv =
  let uctx, exported = export_side_effects senv eff in
  let senv = push_context_set ~strict:true uctx senv in
  let map senv (kn, (hbody, c)) = match c.const_body with
  | OpaqueDef body ->
    (* Don't care about the body, it has been checked by {!infer_direct_opaque} *)
    let senv, o = push_opaque_proof senv in
    let (_, _, _, h) = Opaqueproof.repr o in
    let univs = match c.const_universes with
    | Monomorphic -> None
    | Polymorphic auctx -> Some (UVars.AbstractContext.size auctx)
    in
    (* Hashcons now, before storing in the opaque table *)
    let _, body = match hbody with
    | None -> Constr.hcons body
    | Some hbody ->
      let () = assert (HConstr.self hbody == body) in
      HConstr.hcons hbody
    in
    let opaque = { exp_body = body; exp_handle = h; exp_univs = univs } in
    senv, (kn, { c with const_body = OpaqueDef o }, Some opaque, None)
  | Def _ | Undef _ | Primitive _ | Symbol _ as body ->
    (* Hashconsing is handled by {!add_constant_aux}, propagate hbody *)
    senv, (kn, { c with const_body = body }, None, hbody)
  in
  let senv, bodies = List.fold_left_map map senv exported in
  let exported = List.map (fun (kn, _, opaque, _) -> kn, opaque) bodies in
  (* No delayed constants to declare *)
  let fold senv (kn, cb, _, hbody) = add_constant_aux ?hbody senv (kn, cb) in
  let senv = List.fold_left fold senv bodies in
  exported, senv

let add_constant l decl senv =
  let kn = Constant.make2 senv.modpath l in
  let senv, (hbody, cb) =
    let sec_univs = Option.map Section.all_poly_univs senv.sections in
      match decl with
      | Entries.OpaqueEntry ce ->
        let senv, o = push_opaque_proof senv in
        let cb, ctx = Constant_typing.infer_opaque ~sec_univs senv.env ce in
        (* Push the delayed data in the environment *)
        let (_, _, _, i) = Opaqueproof.repr o in
        let nonce = Nonce.create () in
        let future_cst = HandleMap.add i (ctx, senv, nonce) senv.future_cst in
        let senv = { senv with future_cst } in
        senv, (None, { cb with const_body = OpaqueDef o })
      | Entries.DefinitionEntry entry ->
        senv, Constant_typing.infer_definition ~sec_univs senv.env entry
      | Entries.ParameterEntry entry ->
        senv, (None, Constant_typing.infer_parameter ~sec_univs senv.env entry)
      | Entries.PrimitiveEntry entry ->
        let senv = match entry with
        | { Entries.prim_entry_content = CPrimitives.OT_type t; _ } ->
          add_retroknowledge (Retroknowledge.Register_type(t,kn)) senv
        | _ -> senv in
        senv, (None, Constant_typing.infer_primitive senv.env entry)
      | Entries.SymbolEntry entry ->
        senv, (None, Constant_typing.infer_symbol senv.env entry)
  in
  let cb = compile_bytecode senv.env cb in
  let senv = add_constant_aux senv ?hbody (kn, cb) in
  kn, senv

let add_constant ?typing_flags l decl senv =
  with_typing_flags ?typing_flags senv ~f:(add_constant l decl)

type opaque_certificate = {
  opq_body : Constr.t;
  opq_univs : Univ.ContextSet.t Opaqueproof.delayed_universes;
  opq_handle : Opaqueproof.opaque_handle;
  opq_nonce : Nonce.t;
}

let check_opaque senv (i : Opaqueproof.opaque_handle) pf =
  let ty_ctx, trust, nonce =
    try HandleMap.find i senv.future_cst
    with Not_found ->
      CErrors.anomaly Pp.(str "Missing opaque with identifier " ++ int (Opaqueproof.repr_handle i))
  in
  let handle env body eff =
    let body, uctx, signatures, skip = inline_side_effects env body eff in
    let trusted = check_signatures trust signatures in
    let trusted, uctx = match trusted with
    | None -> 0, uctx
    | Some univs -> skip, Univ.ContextSet.union univs uctx
    in
    body, uctx, trusted
  in
  let (hbody, c, ctx) = Constant_typing.check_delayed handle ty_ctx pf in
  let _, c = match hbody with
    | Some hbody -> assert (c == HConstr.self hbody); HConstr.hcons hbody
    | None -> Constr.hcons c
  in
  let ctx = match ctx with
  | Opaqueproof.PrivateMonomorphic u ->
    Opaqueproof.PrivateMonomorphic (snd @@ Univ.ContextSet.hcons u)
  | Opaqueproof.PrivatePolymorphic u ->
    Opaqueproof.PrivatePolymorphic (snd @@ Univ.ContextSet.hcons u)
  in
  { opq_body = c; opq_univs = ctx; opq_handle = i; opq_nonce = nonce }

let fill_opaque { opq_univs = ctx; opq_handle = i; opq_nonce = n; _ } senv =
  let () = if not @@ HandleMap.mem i senv.future_cst then
    CErrors.anomaly Pp.(str "Missing opaque handle" ++ spc () ++ int (Opaqueproof.repr_handle i))
  in
  let _, _, nonce = HandleMap.find i senv.future_cst in
  let () =
    if not (Nonce.equal n nonce) then
      CErrors.anomaly  Pp.(str "Invalid opaque certificate")
  in
  (* TODO: Drop the the monomorphic constraints, they should really be internal
     but the higher levels use them haphazardly. *)
  let senv = match ctx with
  | Opaqueproof.PrivateMonomorphic ctx -> push_context_set ~strict:true ctx senv
  | Opaqueproof.PrivatePolymorphic _ -> senv
  in
  (* Mark the constant as having been checked *)
  { senv with future_cst = HandleMap.remove i senv.future_cst }

let is_filled_opaque i senv =
  let () = assert (Opaqueproof.mem_handle i senv.opaquetab) in
  not (HandleMap.mem i senv.future_cst)

let repr_certificate { opq_body = body; opq_univs = ctx; _ } =
  body, ctx

let check_constraints uctx = function
| Entries.Polymorphic_entry _ -> Univ.ContextSet.is_empty uctx
| Entries.Monomorphic_entry -> true

let add_private_constant l uctx decl senv : (Constant.t * private_constants) * safe_environment =
  let kn = Constant.make2 senv.modpath l in
  let senv = push_context_set ~strict:true uctx senv in
    let hbody, cb =
      let sec_univs = Option.map Section.all_poly_univs senv.sections in
      match decl with
      | OpaqueEff ce ->
        let () = assert (check_constraints uctx ce.Entries.opaque_entry_universes) in
        infer_direct_opaque ~sec_univs senv.env ce
      | DefinitionEff ce ->
        let () = assert (check_constraints uctx ce.Entries.definition_entry_universes) in
        Constant_typing.infer_definition ~sec_univs senv.env ce
    in
  let cb = compile_bytecode senv.env cb in
  let dcb = match cb.const_body with
  | Def _ as const_body -> { cb with const_body }
  | OpaqueDef _ ->
    (* We drop the body, to save the definition of an opaque and thus its
       hashconsing. It does not matter since this only happens inside a proof,
       and depending of the opaque status of the latter, this proof term will be
       either inlined or reexported. *)
    { cb with const_body = Undef None }
  | Undef _ | Primitive _ | Symbol _ -> assert false
  in
  let senv = add_constant_aux senv ?hbody (kn, dcb) in
  let eff =
    let from_env = CEphemeron.create (Certificate.make senv) in
    let eff = {
      seff_certif = from_env;
      seff_constant = kn;
      seff_body = (hbody, cb);
      seff_univs = uctx;
    } in
    SideEffects.add eff empty_private_constants
  in
  (kn, eff), senv

(** Rewrite rules *)

let add_rewrite_rules l rules senv =
  if Option.has_some senv.sections
  then CErrors.user_err Pp.(str "Adding rewrite rules not supported in sections.");
  (* TODO: Hashconsing? *)
  add_field (l, SFBrules rules) R senv

(** Insertion of inductive types *)

let check_mind mie lab =
  let open Entries in
  match mie.mind_entry_inds with
  | [] -> assert false (* empty inductive entry *)
  | oie::_ ->
    (* The label and the first inductive type name should match *)
    assert (Id.equal lab oie.mind_entry_typename)

let add_checked_mind kn mib senv =
  let mib =
    match mib.mind_hyps with [] -> Declareops.hcons_mind mib | _ -> mib
  in
  add_field (MutInd.label kn,SFBmind mib) (I kn) senv

let add_mind l mie senv =
  let () = check_mind mie l in
  let kn = MutInd.make2 senv.modpath l in
  let sec_univs = Option.map Section.all_poly_univs senv.sections in
  let mib, why_not_prim_record = Indtypes.check_inductive senv.env ~sec_univs kn mie in
  (* We still have to add the template monomorphic constraints, and only those
     ones. In all other cases, they are already part of the environment at this
     point. *)
  let senv = match mib.mind_template with
  | None -> senv
  | Some { template_context = ctx; template_defaults = u; _ } ->
    let qs, levels = UVars.Instance.levels u in
    let () = assert (Sorts.Quality.Set.for_all (fun q -> Sorts.Quality.equal Sorts.Quality.qtype q) qs) in
    let (qctx, uctx) = UVars.AbstractContext.instantiate u ctx in
    let () = assert (Sorts.ElimConstraints.is_empty qctx) in
    (* Eliminiation constraints used to be pushed with QGraph.Static *)
    let senv = push_context_set ~strict:true (levels, uctx) senv in
    senv
  in
  (kn, why_not_prim_record), add_checked_mind kn mib senv

let add_mind ?typing_flags l mie senv =
  with_typing_flags ?typing_flags senv ~f:(add_mind l mie)

(** Insertion of module types *)

let check_state senv =
  (Environ.universes senv.env, Conversion.checked_universes)

let vm_handler env univs c vmtab =
  let env = Environ.set_vm_library vmtab env in
  let code = Vmbytegen.compile_constant_body ~fail_on_error:false env univs (Def c) in
  let vmtab, code = push_bytecode vmtab code in
  vmtab, code

let vm_state senv =
  (Environ.vm_library senv.env, { Mod_typing.vm_handler })

let add_modtype l params_mte inl senv =
  let mp = MPdot(senv.modpath, l) in
  let state = check_state senv in
  let vmstate = vm_state senv in
  let mtb, _, vmtab = Mod_typing.translate_modtype state vmstate senv.env mp inl params_mte  in
  let senv = set_vm_library vmtab senv in
  let mtb = Mod_declarations.hcons_module_type mtb in
  let senv = add_field (l,SFBmodtype mtb) (MT mp) senv in
  mp, senv

(** Insertion of modules *)

let add_module l me inl senv =
  let mp = MPdot(senv.modpath, l) in
  let state = check_state senv in
  let vmstate = vm_state senv in
  let mb, _, vmtab = Mod_typing.translate_module state vmstate senv.env mp inl me in
  let senv = set_vm_library vmtab senv in
  let mb = Mod_declarations.hcons_module_body mb in
  let senv = add_field (l,SFBmodule mb) (M mp) senv in
  let senv = match mod_global_delta mb with
  | None -> senv
  | Some delta -> update_resolver (Mod_subst.add_delta_resolver delta) senv
  in
  (mp, mod_delta mb), senv

(** {6 Starting / ending interactive modules and module types } *)

let start_mod_modtype ~istype l senv =
  let () = check_modlabel l senv in
  let () = check_empty_context senv in
  let mp = MPdot(senv.modpath, l) in
  mp,
  {
    (* modified fields *)
    modpath = mp;
    modvariant = if istype then SIG ([], senv) else STRUCT ([],senv);

    (* carried over fields *)
    env = senv.env;
    future_cst = senv.future_cst;
    modresolver = Mod_subst.empty_delta_resolver mp;
    paramresolver = ParamResolver.add_delta_resolver senv.modpath senv.modresolver senv.paramresolver;
    univ = senv.univ;
    qualities = senv.qualities;
    elims = senv.elims;
    required = senv.required;
    opaquetab = senv.opaquetab;
    sections = None; (* checked in check_empty_context *)

    (* module local fields *)
    revstruct = [];
    modlabels = Id.Set.empty;
    objlabels = Id.Set.empty;
    loads = [];
    local_retroknowledge = [];
  }

let start_module l senv = start_mod_modtype ~istype:false l senv

let start_modtype l senv = start_mod_modtype ~istype:true l senv

(** Adding parameters to the current module or module type.
    This module should have been freshly started. *)

let add_module_parameter mbid mte inl senv =
  let () = check_empty_struct senv in
  let mp = MPbound mbid in
  let state = check_state senv in
  let vmstate = vm_state senv in
  let mtb, _, vmtab = Mod_typing.translate_modtype state vmstate senv.env mp inl ([],mte) in
  let senv = set_vm_library vmtab senv in
  let senv = { senv with env = Modops.add_module_parameter mbid mtb senv.env } in
  let new_variant = match senv.modvariant with
    | STRUCT (params,oldenv) -> STRUCT ((mbid,mtb) :: params, oldenv)
    | SIG (params,oldenv) -> SIG ((mbid,mtb) :: params, oldenv)
    | _ -> assert false
  in
  let new_paramresolver = match mod_global_delta mtb with
  | None -> senv.paramresolver
  | Some delta -> ParamResolver.add_delta_resolver mp delta senv.paramresolver
  in
  mtb,
  { senv with
    modvariant = new_variant;
    paramresolver = new_paramresolver }

let rec module_num_parameters senv =
  match senv.modvariant with
  | STRUCT (params,senv) -> List.length params :: module_num_parameters senv
  | SIG (params,senv) -> List.length params :: module_num_parameters senv
  | _ -> []

let rec module_is_modtype senv =
  match senv.modvariant with
  | STRUCT (_,senv) -> false :: module_is_modtype senv
  | SIG (_,senv) -> true :: module_is_modtype senv
  | _ -> []

let functorize params init =
  List.fold_left (fun e (mbid,mt) -> MoreFunctor(mbid,mt,e)) init params

let propagate_load senv (mp, mb as load) =
  let dp = ModPath.dp mp in
  let linkinfo = Nativecode.link_info_of_dirpath dp in
  { senv with
    paramresolver = ParamResolver.add_delta_resolver mp (mod_delta mb) senv.paramresolver;
    loads = load :: senv.loads;
    env = Modops.add_linked_module mp mb linkinfo senv.env;
  }

let propagate_loads loads senv =
  List.fold_left propagate_load senv (List.rev loads)

(** Build the module body of the current module, taking in account
    a possible return type (_:T) *)

let build_module_body params restype senv =
  let struc = NoFunctor (List.rev senv.revstruct) in
  let restype' = Option.map (fun (ty,inl) -> (([],ty),inl)) restype in
  let state = check_state senv in
  let vmstate = vm_state senv in
  (* XXX why are we dropping vmtab here? *)
  let mb, _, _vmtab =
    Mod_typing.finalize_module state vmstate senv.env senv.modpath
      (struc, senv.modresolver) restype'
  in
  let mb' = functorize_module params mb in
  mb'

(** Returning back to the old pre-interactive-module environment,
    with one extra component and some updated fields
    (constraints, required, etc) *)

let allow_delayed_constants = ref false

let propagate_senv newdef senv oldsenv =
  (* This asserts that after Paral-ITP, standard vo compilation is behaving
   * exctly as before: the same universe constraints are added to modules *)
  if not !allow_delayed_constants && not (HandleMap.is_empty senv.future_cst) then
    CErrors.anomaly ~label:"safe_typing"
      Pp.(str "True Future.t were created for opaque constants even if -async-proofs is off");
  propagate_loads senv.loads {
    oldsenv with
    env = senv.env;
    modresolver = senv.modresolver;
    revstruct = newdef::oldsenv.revstruct;
    modlabels = Id.Set.add (fst newdef) oldsenv.modlabels;
    univ = senv.univ;
    qualities = senv.qualities ;
    future_cst = senv.future_cst;
    required = senv.required;
    loads = oldsenv.loads;
    local_retroknowledge =
      senv.local_retroknowledge@oldsenv.local_retroknowledge;
    opaquetab = senv.opaquetab;
  }

let end_module l restype senv =
  let mp = senv.modpath in
  let params, oldsenv = check_struct senv.modvariant in
  let () = check_current_label l mp in
  let () = check_empty_context senv in
  let mbids = List.rev_map fst params in
  let mb = build_module_body params restype senv in
  let newenv = Environ.set_universes (Environ.universes senv.env) oldsenv.env in
  let newenv = Environ.set_qualities (Environ.qualities senv.env) newenv in
  let newenv = if Environ.rewrite_rules_allowed senv.env then Environ.allow_rewrite_rules newenv else newenv in
  let newenv = Environ.set_vm_library (Environ.vm_library senv.env) newenv in
  let newenv = Modops.add_retroknowledge senv.local_retroknowledge newenv in
  let newenv = Modops.add_module mp mb newenv in
  let newresolver = match mod_global_delta mb with
  | None -> oldsenv.modresolver
  | Some delta -> Mod_subst.add_delta_resolver delta oldsenv.modresolver
  in
  let () = assert (List.is_empty params || List.is_empty senv.local_retroknowledge) in
  (mp, mbids, mod_delta mb),
  propagate_senv (l,SFBmodule mb) { senv with env = newenv; modresolver = newresolver } oldsenv

let build_mtb = Mod_declarations.make_module_type

let end_modtype l senv =
  let mp = senv.modpath in
  let params, oldsenv = check_sig senv.modvariant in
  let () = check_current_label l mp in
  let () = check_empty_context senv in
  let mbids = List.rev_map fst params in
  let newenv = Environ.set_universes (Environ.universes senv.env) oldsenv.env in
  let newenv = if Environ.rewrite_rules_allowed senv.env then Environ.allow_rewrite_rules newenv else newenv in
  let newenv = Environ.set_vm_library (Environ.vm_library senv.env) newenv in
  let auto_tb = functorize params (NoFunctor (List.rev senv.revstruct)) in
  let mtb = build_mtb auto_tb senv.modresolver in
  let newenv = Environ.add_modtype mp mtb newenv in
  let newresolver = oldsenv.modresolver in
  let () = assert (List.is_empty senv.local_retroknowledge) in
  (mp,mbids),
  propagate_senv (l,SFBmodtype mtb) { senv with env = newenv; modresolver = newresolver } oldsenv

(** {6 Inclusion of module or module type } *)

let add_include me is_module inl senv =
  let open Mod_typing in
  let mp_sup = senv.modpath in
  let state = check_state senv in
  let vmstate = vm_state senv in
  let sign,(),resolver, _, vmtab =
    translate_mse_include is_module state vmstate senv.env mp_sup inl me
  in
  let senv = set_vm_library vmtab senv in
  (* Include Self support  *)
  let struc = NoFunctor (List.rev senv.revstruct) in
  let mb = Mod_declarations.make_module_body struc senv.modresolver in
  let rec compute_sign sign resolver =
    match sign with
    | MoreFunctor(mbid,mtb,str) ->
      let state = check_state senv in
      (* Module subcomponents are already part of senv.env at this point *)
      let env = Environ.shallow_add_module mp_sup mb senv.env in
      let (_ : UGraph.t) = Subtyping.check_subtypes state env mp_sup (MPbound mbid) mtb in
      let mpsup_delta =
        Modops.inline_delta_resolver senv.env inl mp_sup mbid mtb senv.modresolver
      in
      let subst = Mod_subst.map_mbid mbid mp_sup mpsup_delta in
      let resolver = Mod_subst.subst_codom_delta_resolver subst resolver in
      compute_sign (Modops.subst_signature subst mp_sup str) resolver
    | NoFunctor str -> resolver, str
  in
  let resolver, str = compute_sign sign resolver in
  let senv = update_resolver (Mod_subst.add_delta_resolver resolver) senv in
  let add senv ((l,elem) as field) =
    let new_name = match elem with
      | SFBconst _ ->
        C (Mod_subst.constant_of_delta_kn resolver (KerName.make mp_sup l))
      | SFBmind _ ->
        I (Mod_subst.mind_of_delta_kn resolver (KerName.make mp_sup l))
      | SFBrules _ -> R
      | SFBmodule _ -> M (MPdot (mp_sup, l))
      | SFBmodtype _ -> MT (MPdot (mp_sup, l))
    in
    add_field field new_name senv
  in
  resolver, List.fold_left add senv str

(** {6 Libraries, i.e. compiled modules } *)

let dirpath_of_library lib = lib.comp_name

let module_of_library lib = lib.comp_mod

let univs_of_library lib = lib.comp_sorts, lib.comp_univs

let retroknowledge_of_library lib = lib.comp_retro

let start_library dir senv =
  (* When starting a library, the current environment should be initial
     i.e. only composed of Require's *)
  (* XXX is it really possible / should be allowed to have nonempty Requires?
     especially if [dir] is in the [senv.required] *)
  assert (is_initial senv);
  assert (not (DirPath.is_empty dir));
  let mp = MPfile dir in
  let vmtab = Vmlibrary.set_path dir (Environ.vm_library senv.env) in
  let env = Environ.set_vm_library vmtab senv.env in
  mp,
  { env = env;
    modpath = mp;
    modvariant = LIBRARY;
    required = senv.required;

    modresolver = Mod_subst.empty_delta_resolver mp;
    paramresolver = ParamResolver.empty dir;
    revstruct = [];
    modlabels = Id.Set.empty;
    objlabels = Id.Set.empty;
    sections = None;
    future_cst = HandleMap.empty;
    univ = Univ.ContextSet.empty;
    qualities = Sorts.QGlobal.Set.empty;
    elims = Sorts.ElimConstraints.empty;
    loads = [];
    local_retroknowledge = [];
    opaquetab = Opaqueproof.empty_opaquetab;
  }

let export ~output_native_objects senv dir =
  let () = check_current_library dir senv in
  let mp = senv.modpath in
  let str = NoFunctor (List.rev senv.revstruct) in
  let mb = Mod_declarations.make_module_body str senv.modresolver in
  let ast, symbols =
    if output_native_objects then
      Nativelibrary.dump_library mp senv.env str
    else [], Nativevalues.empty_symbols
  in
  let permanent_flags = {
    rewrite_rules_allowed = Environ.rewrite_rules_allowed senv.env;
  } in
  let filter_dep (dp, { req_root; req_digest }) =
    if req_root then Some (dp, req_digest) else None
  in
  let comp_deps = List.map_filter filter_dep (DirPath.Map.bindings senv.required) in
  let lib = {
    comp_name = dir;
    comp_mod = mb;
    comp_univs = senv.univ;
    comp_sorts = senv.qualities, senv.elims;
    comp_deps = Array.of_list comp_deps;
    comp_flags = permanent_flags;
    comp_retro = senv.local_retroknowledge;
  } in
  let vmlib = Vmlibrary.export @@ Environ.vm_library senv.env in
  mp, lib, vmlib, (ast, symbols)

let import lib vmtab vodigest senv =
  let senv = check_flags_for_library lib senv in
  let required = check_required senv.required lib.comp_deps in
  if DirPath.equal (ModPath.dp senv.modpath) lib.comp_name then
    CErrors.user_err
      Pp.(strbrk "Cannot load a library with the same name as the current one ("
          ++ DirPath.print lib.comp_name ++ str").");
  let mp = MPfile lib.comp_name in
  let mb = lib.comp_mod in
  let univs = lib.comp_univs in
  let qualities = lib.comp_sorts in
  let retro = lib.comp_retro in
  let check_quality q =
    not (QGraph.is_declared (Sorts.Quality.QGlobal q) (Environ.qualities senv.env))
  in
  let () = assert (Sorts.QGlobal.Set.for_all check_quality (fst qualities)) in
  let env = Environ.push_qualities (Sorts.Quality.Set.of_qglobals @@ fst qualities) senv.env in
  let env = Environ.merge_elim_constraints ~rigid:true (snd qualities) env in
  let env = Environ.push_context_set ~strict:true univs env in
  let env = Modops.add_retroknowledge retro env in
  let env = Environ.link_vm_library vmtab env in
  let env =
    let linkinfo = Nativecode.link_info_of_dirpath lib.comp_name in
    Modops.add_linked_module mp mb linkinfo env
  in
  let sections =
    Option.map (Section.map_custom (fun custom ->
        {custom with rev_reimport = (lib,vmtab,vodigest) :: custom.rev_reimport}))
      senv.sections
  in
  let required =
    if DirPath.Map.mem lib.comp_name required then
      (* should probably be an error, we are requiring the same library twice *)
      required
    else DirPath.Map.add lib.comp_name { req_root = true; req_digest = vodigest } required
  in
  mp,
  { senv with
    env;
    (* Do NOT store the name quotient from the dependencies in the set of
       constraints that will be marshalled on disk. *)
    paramresolver = ParamResolver.add_delta_resolver mp (mod_delta mb) senv.paramresolver;
    required;
    loads = (mp,mb)::senv.loads;
    sections;
  }

(** {6 Interactive sections} *)

let open_section senv =
  let custom = {
    rev_env = senv.env;
    rev_univ = senv.univ;
    rev_qualities = senv.qualities, senv.elims;
    rev_objlabels = senv.objlabels;
    rev_reimport = [];
    rev_revstruct = senv.revstruct;
    rev_paramresolver = senv.paramresolver;
  } in
  let sections = Section.open_section ~custom senv.sections in
  { senv with sections=Some sections }

let close_section senv =
  let open Section in
  let sections0 = get_section senv.sections in
  let env0 = senv.env in
  (* First phase: revert the declarations added in the section *)
  let sections, entries, cstrs, revert = Section.close_section sections0 in
  (* Don't revert the delayed constraints (future_cst). If some delayed constraints
     were forced inside the section, they have been turned into global monomorphic
     that are going to be replayed. Those that are not forced are not readded
     by {!add_constant_aux}. *)
  let { rev_env = env; rev_univ = univ; rev_qualities = (qualities, elims); rev_objlabels = objlabels;
        rev_reimport; rev_revstruct = revstruct; rev_paramresolver = paramresolver } = revert in
  let env = if Environ.rewrite_rules_allowed env0 then Environ.allow_rewrite_rules env else env in
  let senv = { senv with env; revstruct; sections; univ; qualities; elims; objlabels; paramresolver } in
  (* Second phase: replay Requires *)
  let senv = List.fold_left (fun senv (lib,vmtab,vodigest) -> snd (import lib vmtab vodigest senv))
      senv (List.rev rev_reimport)
  in
  (* Third phase: replay the discharged section contents *)
  let senv = push_context_set ~strict:true cstrs senv in
  let fold entry senv =
    match entry with
  | SecDefinition kn ->
    let cb = Environ.lookup_constant kn env0 in
    let info = Section.segment_of_constant kn sections0 in
    let cb = Discharge.cook_constant senv.env info cb in
    let cb = compile_bytecode senv.env cb in
    (* Delayed constants are already in the global environment *)
    add_constant_aux senv (kn, cb)
  | SecInductive ind ->
    let mib = Environ.lookup_mind ind env0 in
    let info = Section.segment_of_inductive ind sections0 in
    let mib = Discharge.cook_inductive info mib in
    add_checked_mind ind mib senv
  in
  List.fold_right fold entries senv

let flatten_env senv =
  let label = function MPdot (_,l) -> l | _ -> assert false in
  let rec close senv =
    match senv.modvariant with
    | STRUCT _ -> close (snd (end_module (label senv.modpath) None senv))
    | SIG (params,env) -> close (snd (end_module (label senv.modpath) None {senv with modvariant = STRUCT (params,env)}))
    | LIBRARY | NONE -> senv in
  let senv = close senv in
  (senv.modpath, senv.revstruct)

(** {6 Safe typing } *)

type judgment = {
  jdg_env : safe_environment;
  jdg_val : constr;
  jdg_type : types;
}

let typing senv c =
  let j = Typeops.infer (env_of_senv senv) c in
  { jdg_env = senv;
    jdg_val = j.Environ.uj_val;
    jdg_type = j.Environ.uj_type;
  }

(** {6 Retroknowledge / native compiler } *)

let register_inline kn senv =
  let open Environ in
  if not (evaluable_constant kn senv.env) then
    CErrors.user_err Pp.(str "Register inline: an evaluable constant is expected");
  let env = senv.env in
  let cb = lookup_constant kn env in
  let cb = {cb with const_inline_code = true} in
  let env = add_constant kn cb env in { senv with env}

let check_register_ind (type t) ind (r : t CPrimitives.prim_ind) (mb, ob as spec) =
  let ind = match mb.mind_universes with
    | Polymorphic _ -> CErrors.user_err Pp.(str "A universe monomorphic inductive type is expected.")
    | Monomorphic -> Constr.UnsafeMonomorphic.mkInd ind
  in
  let check_if b msg =
    if not b then
      CErrors.user_err msg in
  check_if (Int.equal (Array.length mb.mind_packets) 1) Pp.(str "A non mutual inductive is expected.");
  check_if (not @@ Inductive.is_private spec) Pp.(str "A non-private inductive type is expected");
  let check_nparams n =
    check_if (Int.equal mb.mind_nparams n) Pp.(str "An inductive type with " ++ int n ++ str " parameters is expected")
  in
  let check_nconstr n =
    check_if (Int.equal (Array.length ob.mind_consnames) n)
      Pp.(str "an inductive type with " ++ int n ++ str " constructors is expected")
  in
  let check_name pos s =
    check_if (Id.equal ob.mind_consnames.(pos) (Id.of_string s))
      Pp.(str"the " ++ int (pos + 1) ++ str
       "th constructor does not have the expected name: " ++ str s) in
  let check_type pos t =
    check_if (Constr.equal t ob.mind_user_lc.(pos))
      Pp.(str"the " ++ int (pos + 1) ++ str
       "th constructor does not have the expected type") in
  let check_type_cte pos = check_type pos ind in
  match r with
  | CPrimitives.PIT_bool ->
    check_nparams 0;
    check_nconstr 2;
    check_name 0 "true";
    check_type_cte 0;
    check_name 1 "false";
    check_type_cte 1
  | CPrimitives.PIT_carry ->
    check_nparams 1;
    check_nconstr 2;
    let test_type pos =
      let c = ob.mind_user_lc.(pos) in
      let s = Pp.(str"the " ++ int (pos + 1) ++ str
              "th constructor does not have the expected type") in
      check_if (Constr.isProd c) s;
      let (_,d,cd) = Constr.destProd c in
      check_if (Constr.is_Type d) s;
      check_if
        (Constr.equal
                (mkProd (Context.anonR,mkRel 1, mkApp (ind,[|mkRel 2|])))
                cd)
        s in
    check_name 0 "C0";
    test_type 0;
    check_name 1 "C1";
    test_type 1;
  | CPrimitives.PIT_pair ->
    check_nparams 2;
    check_nconstr 1;
    check_name 0 "pair";
    let c = match mb.mind_template with
    | None -> ob.mind_user_lc.(0)
    | Some templ -> Vars.subst_instance_constr templ.template_defaults ob.mind_user_lc.(0)
    in
    let s =  Pp.str "the constructor does not have the expected type" in
    begin match Term.decompose_prod c with
      | ([_,b;_,a;_,_B;_,_A], codom) ->
        check_if (is_Type _A) s;
        check_if (is_Type _B) s;
        check_if (Constr.equal a (mkRel 2)) s;
        check_if (Constr.equal b (mkRel 2)) s;
        check_if (Constr.equal codom (mkApp (ind,[|mkRel 4; mkRel 3|]))) s
      | _ -> check_if false s
    end
  | CPrimitives.PIT_cmp ->
    check_nparams 0;
    check_nconstr 3;
    check_name 0 "Eq";
    check_type_cte 0;
    check_name 1 "Lt";
    check_type_cte 1;
    check_name 2 "Gt";
    check_type_cte 2
  | CPrimitives.PIT_f_cmp ->
    check_nconstr 4;
    check_name 0 "FEq";
    check_type_cte 0;
    check_name 1 "FLt";
    check_type_cte 1;
    check_name 2 "FGt";
    check_type_cte 2;
    check_name 3 "FNotComparable";
    check_type_cte 3
  | CPrimitives.PIT_f_class ->
    check_nconstr 9;
    check_name 0 "PNormal";
    check_type_cte 0;
    check_name 1 "NNormal";
    check_type_cte 1;
    check_name 2 "PSubn";
    check_type_cte 2;
    check_name 3 "NSubn";
    check_type_cte 3;
    check_name 4 "PZero";
    check_type_cte 4;
    check_name 5 "NZero";
    check_type_cte 5;
    check_name 6 "PInf";
    check_type_cte 6;
    check_name 7 "NInf";
    check_type_cte 7;
    check_name 8 "NaN";
    check_type_cte 8

let register_inductive ind prim senv =
  let spec = Inductive.lookup_mind_specif senv.env ind in
  let () = check_register_ind ind prim spec in
  let action = Retroknowledge.Register_ind(prim,ind) in
  add_retroknowledge action senv

let check_register_peano_nat ind (mb, ob as spec) =
  let fail message = CErrors.user_err Pp.(str message) in
  let ind_term = match mb.mind_universes with
    | Polymorphic a when UVars.AbstractContext.size a = (0, 0) ->
      Constr.mkIndU (ind, UVars.Instance.empty)
    | Polymorphic _ -> fail "A universe monomorphic inductive type is expected"
    | Monomorphic -> Constr.UnsafeMonomorphic.mkInd ind
  in
  if not (Int.equal (Array.length mb.mind_packets) 1) then
    fail "A non-mutual inductive type is expected";
  if Inductive.is_private spec then
    fail "A non-private inductive type is expected";
  if not (Int.equal mb.mind_nparams 0) then
    fail "A Peano type must have no parameters";
  if not (Int.equal (Array.length ob.mind_user_lc) 2) then
    fail "A Peano type must have two constructors";
  if not (Constr.equal ob.mind_user_lc.(0) ind_term) then
    fail "The zero constructor must be nullary";
  match Constr.kind ob.mind_user_lc.(1) with
  | Constr.Prod (annot, dom, codom)
    when Sorts.is_relevant annot.binder_relevance &&
         Constr.equal dom ind_term && Constr.equal codom ind_term -> ()
  | _ -> fail "The successor constructor must have type D -> D"

let register_peano_nat ind senv =
  let spec = Inductive.lookup_mind_specif senv.env ind in
  let () = check_register_peano_nat ind spec in
  add_retroknowledge (Retroknowledge.Register_peano_nat ind) senv

let check_register_unit_like _ind (mib, mip as spec) =
  let fail message = CErrors.user_err Pp.(str message) in
  if not (Int.equal (Array.length mib.mind_packets) 1) then
    fail "A non-mutual inductive type is expected";
  if Inductive.is_private spec then
    fail "A non-private inductive type is expected";
  if not (Int.equal mip.mind_nrealargs 0) then
    fail "A unit-like type must have no indices";
  if not (Int.equal (Array.length mip.mind_user_lc) 1) then
    fail "A unit-like type must have exactly one constructor";
  let constructor_context, _ = mip.mind_nf_lc.(0) in
  let fields, _ =
    List.chop mip.mind_consnrealdecls.(0) constructor_context
  in
  let runtime_irrelevant = function
    | Context.Rel.Declaration.LocalAssum (annot, _) ->
      not (Sorts.is_relevant annot.Context.binder_relevance)
    | Context.Rel.Declaration.LocalDef _ -> true
  in
  if not (List.for_all runtime_irrelevant fields) then
    fail "The constructor of a unit-like type must have no runtime-relevant fields"

let register_unit_like ind senv =
  let spec = Inductive.lookup_mind_specif senv.env ind in
  let () = check_register_unit_like ind spec in
  let duplicate =
    List.exists (Ind.UserOrd.equal ind)
      (Environ.retroknowledge senv.env).Retroknowledge.retro_unit_like
  in
  if duplicate then senv
  else add_retroknowledge (Retroknowledge.Register_unit_like ind) senv

let find_peano_nat env ind =
  match List.find_opt
    (fun scheme ->
      Ind.UserOrd.equal ind scheme.Retroknowledge.peano_inductive)
    (Environ.retroknowledge env).Retroknowledge.retro_peano_nat
  with
  | Some scheme -> scheme
  | None ->
    CErrors.user_err Pp.(str "Register the Peano inductive first")

let peano_baseline_env env =
  let retro = Environ.retroknowledge env in
  let baseline =
    { retro with
      Retroknowledge.retro_peano_nat = [];
      retro_peano_nat_beq = [];
      retro_peano_nat_ble = [] }
  in
  let env = Environ.set_retroknowledge env baseline in
  Environ.set_oracle env Conv_oracle.empty

let check_peano_conversion env description lhs rhs =
  match Conversion.conv (peano_baseline_env env) lhs rhs with
  | Result.Ok () -> ()
  | Result.Error () ->
    CErrors.user_err Pp.(str "The registered Peano " ++ str description ++
      str " does not have the expected computation rules")

let check_peano_equation ?(binders = []) env description lhs rhs =
  let abstract body =
    List.fold_left
      (fun body ty -> Constr.mkLambda (Context.anonR, ty, body))
      body binders
  in
  check_peano_conversion env description (abstract lhs) (abstract rhs)

let mono_const c = Constr.UnsafeMonomorphic.mkConst c
let mono_ctor c = Constr.UnsafeMonomorphic.mkConstruct c
let apply1 f x = Constr.mkApp (f, [|x|])
let apply2 f x y = Constr.mkApp (f, [|x; y|])

let check_transparent env description c =
  if not (Environ.evaluable_constant c env) then
    CErrors.user_err Pp.(str "A transparent Peano " ++ str description ++
      str " is expected")

let peano_unary_type env c =
  let ty = (Environ.lookup_constant c env).Declarations.const_type in
  match Constr.kind ty with
  | Constr.Prod (_, dom, codom) -> begin
    match Constr.kind dom, Constr.kind codom with
    | Constr.Ind (ind, u), Constr.Ind (ind', u')
      when Ind.UserOrd.equal ind ind' &&
           UVars.Instance.is_empty u && UVars.Instance.is_empty u' -> ind
    | _ -> CErrors.user_err Pp.(str "A monomorphic function D -> D is expected")
    end
  | _ -> CErrors.user_err Pp.(str "A monomorphic function D -> D is expected")

let peano_binary_type env c =
  let ty = (Environ.lookup_constant c env).Declarations.const_type in
  match Constr.kind ty with
  | Constr.Prod (_, dom1, rest) -> begin
    match Constr.kind dom1, Constr.kind rest with
    | Constr.Ind (ind, u), Constr.Prod (_, dom2, codom)
      when UVars.Instance.is_empty u && Constr.equal dom1 dom2 &&
           Constr.equal dom1 codom -> ind
    | _ -> CErrors.user_err Pp.(str
        "A monomorphic function D -> D -> D is expected")
    end
  | _ -> CErrors.user_err Pp.(str
      "A monomorphic function D -> D -> D is expected")

let check_register_peano_nat_double env ind c =
  let () = check_transparent env "doubling builder" c in
  let actual_ind = peano_unary_type env c in
  if not (Ind.UserOrd.equal actual_ind ind) then
    CErrors.user_err Pp.(str "The doubling builder has the wrong Peano type");
  let scheme = find_peano_nat env ind in
  let f = mono_const c in
  let zero = mono_ctor scheme.peano_zero in
  let succ x = apply1 (mono_ctor scheme.peano_succ) x in
  let x = Constr.mkRel 1 in
  let () = check_peano_equation env "doubling builder"
    (apply1 f zero) zero in
  check_peano_equation ~binders:[Constr.UnsafeMonomorphic.mkInd ind]
    env "doubling builder"
    (apply1 f (succ x)) (succ (succ (apply1 f x)))

let register_peano_nat_double c senv =
  let env = senv.env in
  let ind = peano_unary_type env c in
  let scheme = find_peano_nat env ind in
  match scheme.peano_double with
  | Some old when Constant.UserOrd.equal old c -> senv
  | Some _ -> CErrors.user_err Pp.(str
      "A doubling builder is already registered for this Peano type")
  | None ->
    let () = check_register_peano_nat_double env ind c in
    add_retroknowledge (Retroknowledge.Register_peano_nat_double (ind, c)) senv

let peano_decoder_shape env c =
  let ty = (Environ.lookup_constant c env).Declarations.const_type in
  let n_ind, ind =
    match Constr.kind ty with
    | Constr.Prod (_, dom, codom) -> begin
      match Constr.kind dom, Constr.kind codom with
      | Constr.Ind (n_ind, nu), Constr.Ind (ind, u)
        when UVars.Instance.is_empty nu && UVars.Instance.is_empty u ->
        n_ind, ind
      | _ ->
        CErrors.user_err Pp.(str "A monomorphic function N -> D is expected")
      end
    | _ -> CErrors.user_err Pp.(str "A monomorphic function N -> D is expected")
  in
  let n_mb, n_ob = Inductive.lookup_mind_specif env n_ind in
  let fail () =
    CErrors.user_err Pp.(str
      "The decoder domain must be a binary natural with constructors zero and positive")
  in
  let () =
    if not (Int.equal (Array.length n_mb.Declarations.mind_packets) 1) ||
       not (Int.equal n_mb.Declarations.mind_nparams 0) ||
       not (Int.equal (Array.length n_ob.Declarations.mind_user_lc) 2)
    then fail ()
  in
  let pos_ind =
    match Constr.kind n_ob.Declarations.mind_user_lc.(1) with
    | Constr.Prod (_, dom, codom) -> begin
      match Constr.kind dom, Constr.kind codom with
      | Constr.Ind (pos_ind, pu), Constr.Ind (n_ind', nu)
        when UVars.Instance.is_empty pu && UVars.Instance.is_empty nu &&
             Ind.UserOrd.equal n_ind n_ind' -> pos_ind
      | _ -> fail ()
      end
    | _ -> fail ()
  in
  let p_mb, p_ob = Inductive.lookup_mind_specif env pos_ind in
  let p_term = Constr.UnsafeMonomorphic.mkInd pos_ind in
  let valid_recursive_ctor t =
    match Constr.kind t with
    | Constr.Prod (_, dom, codom) ->
      Constr.equal dom p_term && Constr.equal codom p_term
    | _ -> false
  in
  let () =
    if not (Int.equal (Array.length p_mb.Declarations.mind_packets) 1) ||
       not (Int.equal p_mb.Declarations.mind_nparams 0) ||
       not (Int.equal (Array.length p_ob.Declarations.mind_user_lc) 3) ||
       not (valid_recursive_ctor p_ob.Declarations.mind_user_lc.(0)) ||
       not (valid_recursive_ctor p_ob.Declarations.mind_user_lc.(1)) ||
       not (Constr.equal p_ob.Declarations.mind_user_lc.(2) p_term)
    then fail ()
  in
  n_ind, ind, pos_ind

let check_register_peano_nat_of_N env ind n_ind pos_ind c =
  let () = check_transparent env "binary decoder" c in
  let actual_n, actual_ind, actual_pos = peano_decoder_shape env c in
  if not (Ind.UserOrd.equal actual_ind ind &&
          Ind.UserOrd.equal actual_n n_ind &&
          Ind.UserOrd.equal actual_pos pos_ind)
  then CErrors.user_err Pp.(str
    "The binary decoder registration has inconsistent inductive types");
  let scheme = find_peano_nat env ind in
  let p_term = Constr.UnsafeMonomorphic.mkInd pos_ind in
  let double = match scheme.peano_double with
  | Some double -> mono_const double
  | None -> CErrors.user_err Pp.(str
      "Register the Peano doubling builder before its binary decoder")
  in
  let f = mono_const c in
  let zero = mono_ctor scheme.peano_zero in
  let succ x = apply1 (mono_ctor scheme.peano_succ) x in
  let nzero = mono_ctor (n_ind, 1) in
  let npos p = apply1 (mono_ctor (n_ind, 2)) p in
  let xh = mono_ctor (pos_ind, 3) in
  let xo p = apply1 (mono_ctor (pos_ind, 2)) p in
  let xi p = apply1 (mono_ctor (pos_ind, 1)) p in
  let p = Constr.mkRel 1 in
  let decoded p = apply1 f (npos p) in
  let () = check_peano_equation env "binary decoder"
    (apply1 f nzero) zero in
  let () = check_peano_equation env "binary decoder"
    (decoded xh) (succ zero) in
  let () = check_peano_equation ~binders:[p_term] env "binary decoder"
    (decoded (xo p)) (apply1 double (decoded p)) in
  check_peano_equation ~binders:[p_term] env "binary decoder"
    (decoded (xi p)) (succ (apply1 double (decoded p)))

let register_peano_nat_of_N c senv =
  let env = senv.env in
  let n_ind, ind, pos_ind = peano_decoder_shape env c in
  let scheme = find_peano_nat env ind in
  let duplicate =
    List.exists (fun decoder ->
      Constant.UserOrd.equal decoder.Retroknowledge.decoder_constant c &&
      Ind.UserOrd.equal decoder.binary_nat n_ind &&
      Ind.UserOrd.equal decoder.binary_positive pos_ind)
      scheme.peano_decoders
  in
  if duplicate then senv else
  let () = check_register_peano_nat_of_N env ind n_ind pos_ind c in
  add_retroknowledge
    (Retroknowledge.Register_peano_nat_of_N (ind, n_ind, pos_ind, c)) senv

type peano_nat_operation = PeanoAdd | PeanoMul | PeanoPow | PeanoSub

let peano_operation_description = function
  | PeanoAdd -> "addition"
  | PeanoMul -> "multiplication"
  | PeanoPow -> "exponentiation"
  | PeanoSub -> "subtraction"

let peano_operation_constant scheme = function
  | PeanoAdd -> scheme.Retroknowledge.peano_add
  | PeanoMul -> scheme.Retroknowledge.peano_mul
  | PeanoPow -> scheme.Retroknowledge.peano_pow
  | PeanoSub -> scheme.Retroknowledge.peano_sub

let peano_predecessor env scheme value =
  let ind = scheme.Retroknowledge.peano_inductive in
  let mib, mip = Inductive.lookup_mind_specif env ind in
  let ci = {
    Constr.ci_ind = ind;
    ci_npar = mib.Declarations.mind_nparams;
    ci_cstr_ndecls = mip.Declarations.mind_consnrealdecls;
    ci_cstr_nargs = mip.Declarations.mind_consnrealargs;
    ci_pp_info = { Constr.style = Constr.MatchStyle };
  } in
  let binder = Context.make_annot Anonymous Sorts.Relevant in
  let ind_term = Constr.UnsafeMonomorphic.mkInd ind in
  let zero = mono_ctor scheme.peano_zero in
  Constr.mkCase
    (ci, UVars.Instance.empty, [||],
     (([|binder|], ind_term), Sorts.Relevant), Constr.NoInvert, value,
     [|([||], zero); ([|binder|], Constr.mkRel 1)|])

let check_register_peano_nat_operation env operation ind c =
  let description = peano_operation_description operation in
  let () = check_transparent env description c in
  let actual_ind = peano_binary_type env c in
  if not (Ind.UserOrd.equal actual_ind ind) then
    CErrors.user_err Pp.(str "The Peano " ++ str description ++
      str " operation has the wrong type");
  let scheme = find_peano_nat env ind in
  let dependency = match operation with
  | PeanoAdd | PeanoSub -> None
  | PeanoMul -> Some ("addition", scheme.peano_add)
  | PeanoPow -> Some ("multiplication", scheme.peano_mul)
  in
  let dependency = Option.map (fun (name, dependency) ->
    match dependency with
    | Some dependency -> mono_const dependency
    | None -> CErrors.user_err Pp.(str "Register Peano " ++ str name ++
        str " before " ++ str description)) dependency
  in
  let f = mono_const c in
  let zero = mono_ctor scheme.peano_zero in
  let succ x = apply1 (mono_ctor scheme.peano_succ) x in
  let ind_term = Constr.UnsafeMonomorphic.mkInd ind in
  let x = Constr.mkRel 1 in
  let () =
    let rhs = match operation with
    | PeanoAdd | PeanoSub -> x
    | PeanoMul -> zero
    | PeanoPow -> succ zero
    in
    check_peano_equation ~binders:[ind_term] env description
      (apply2 f x zero) rhs
  in
  let x = Constr.mkRel 2 in
  let y = Constr.mkRel 1 in
  let recursive = apply2 f x y in
  let rhs = match operation, dependency with
  | PeanoAdd, None -> succ recursive
  | PeanoSub, None -> peano_predecessor env scheme recursive
  | (PeanoMul | PeanoPow), Some dependency -> apply2 dependency recursive x
  | (PeanoAdd | PeanoSub), Some _ | (PeanoMul | PeanoPow), None -> assert false
  in
  check_peano_equation ~binders:[ind_term; ind_term] env description
    (apply2 f x (succ y)) rhs

let register_peano_nat_operation operation make_action c senv =
  let env = senv.env in
  let ind = peano_binary_type env c in
  let scheme = find_peano_nat env ind in
  match peano_operation_constant scheme operation with
  | Some old when Constant.UserOrd.equal old c -> senv
  | Some _ -> CErrors.user_err Pp.(str "A Peano " ++
      str (peano_operation_description operation) ++
      str " operation is already registered for this Peano type")
  | None ->
    let () = check_register_peano_nat_operation env operation ind c in
    add_retroknowledge (make_action ind c) senv

let register_peano_nat_add c senv =
  register_peano_nat_operation PeanoAdd
    (fun ind c -> Retroknowledge.Register_peano_nat_add (ind, c)) c senv

let register_peano_nat_mul c senv =
  register_peano_nat_operation PeanoMul
    (fun ind c -> Retroknowledge.Register_peano_nat_mul (ind, c)) c senv

let register_peano_nat_pow c senv =
  register_peano_nat_operation PeanoPow
    (fun ind c -> Retroknowledge.Register_peano_nat_pow (ind, c)) c senv

let register_peano_nat_sub c senv =
  register_peano_nat_operation PeanoSub
    (fun ind c -> Retroknowledge.Register_peano_nat_sub (ind, c)) c senv

let peano_bool_shape env c =
  let ty = (Environ.lookup_constant c env).Declarations.const_type in
  let ind, bool_ind = match Constr.kind ty with
  | Constr.Prod (_, dom1, rest) -> begin
    match Constr.kind dom1, Constr.kind rest with
    | Constr.Ind (ind, u), Constr.Prod (_, dom2, codom)
      when UVars.Instance.is_empty u && Constr.equal dom1 dom2 -> begin
      match Constr.kind codom with
      | Constr.Ind (bool_ind, bu) when UVars.Instance.is_empty bu ->
        ind, bool_ind
      | _ -> CErrors.user_err Pp.(str
          "A monomorphic function D -> D -> B is expected")
      end
    | _ -> CErrors.user_err Pp.(str
        "A monomorphic function D -> D -> B is expected")
    end
  | _ -> CErrors.user_err Pp.(str
      "A monomorphic function D -> D -> B is expected")
  in
  let b_mb, b_ob = Inductive.lookup_mind_specif env bool_ind in
  let bool_term = Constr.UnsafeMonomorphic.mkInd bool_ind in
  let () =
    if not (Int.equal (Array.length b_mb.Declarations.mind_packets) 1) ||
       not (Int.equal b_mb.Declarations.mind_nparams 0) ||
       not (Int.equal (Array.length b_ob.Declarations.mind_user_lc) 2) ||
       not (Constr.equal b_ob.Declarations.mind_user_lc.(0) bool_term) ||
       not (Constr.equal b_ob.Declarations.mind_user_lc.(1) bool_term)
    then CErrors.user_err Pp.(str
      "The Boolean codomain must have two nullary constructors")
  in
  ind, (bool_ind, 1), (bool_ind, 2)

type peano_bool_operation = PeanoBeq | PeanoBle

let peano_bool_description = function
  | PeanoBeq -> "equality test"
  | PeanoBle -> "less-than-or-equal test"

let peano_bool_operations env = function
  | PeanoBeq ->
    (Environ.retroknowledge env).Retroknowledge.retro_peano_nat_beq
  | PeanoBle ->
    (Environ.retroknowledge env).Retroknowledge.retro_peano_nat_ble

let check_register_peano_nat_bool operation env ind c false_ctor true_ctor =
  let description = peano_bool_description operation in
  let () = check_transparent env description c in
  let actual_ind, actual_false, actual_true = peano_bool_shape env c in
  if not (Ind.UserOrd.equal actual_ind ind &&
          Construct.UserOrd.equal actual_false false_ctor &&
          Construct.UserOrd.equal actual_true true_ctor)
  then CErrors.user_err Pp.(str
    "The Peano Boolean operation registration is inconsistent with its type");
  let scheme = find_peano_nat env ind in
  let false_term = mono_ctor false_ctor in
  let true_term = mono_ctor true_ctor in
  let zero = mono_ctor scheme.peano_zero in
  let succ x = apply1 (mono_ctor scheme.peano_succ) x in
  let f = mono_const c in
  let ind_term = Constr.UnsafeMonomorphic.mkInd ind in
  let x = Constr.mkRel 1 in
  let y = Constr.mkRel 2 in
  let equations = match operation with
  | PeanoBeq ->
    [ apply2 f zero zero, true_term;
      apply2 f zero (succ y), false_term;
      apply2 f (succ x) zero, false_term;
      apply2 f (succ x) (succ y), apply2 f x y ]
  | PeanoBle ->
    [ apply2 f zero y, true_term;
      apply2 f (succ x) zero, false_term;
      apply2 f (succ x) (succ y), apply2 f x y ]
  in
  List.iter (fun (lhs, rhs) ->
    check_peano_equation ~binders:[ind_term; ind_term]
      env description lhs rhs) equations

let register_peano_nat_bool operation make_action c senv =
  let env = senv.env in
  let ind, false_ctor, true_ctor = peano_bool_shape env c in
  let duplicate = List.exists (fun op ->
    Ind.UserOrd.equal ind op.Retroknowledge.bool_op_inductive &&
    Constant.UserOrd.equal c op.bool_op_constant)
    (peano_bool_operations env operation) in
  if duplicate then senv else
  let () = check_register_peano_nat_bool operation env ind c
    false_ctor true_ctor in
  add_retroknowledge
    (make_action ind c false_ctor true_ctor) senv

let register_peano_nat_beq c senv =
  register_peano_nat_bool PeanoBeq
    (fun ind c false_ctor true_ctor ->
      Retroknowledge.Register_peano_nat_beq
        (ind, c, false_ctor, true_ctor)) c senv

let register_peano_nat_ble c senv =
  register_peano_nat_bool PeanoBle
    (fun ind c false_ctor true_ctor ->
      Retroknowledge.Register_peano_nat_ble
        (ind, c, false_ctor, true_ctor)) c senv

let peano_convertible env lhs rhs =
  match Conversion.conv (peano_baseline_env env) lhs rhs with
  | Result.Ok () -> true
  | Result.Error () -> false

let fail_peano_fueled_worker message =
  CErrors.user_err Pp.(str "Invalid Peano fueled worker: " ++
    str message)

type peano_fueled_worker_kind = PeanoQuotient | PeanoRemainder

let push_rel_assum annot ty env =
  Environ.push_rel (Context.Rel.Declaration.LocalAssum (annot, ty)) env

let check_peano_le env scheme le_ind =
  let mib, mip = Inductive.lookup_mind_specif env le_ind in
  if not (Int.equal (Array.length mib.Declarations.mind_packets) 1) ||
     not (Int.equal mib.Declarations.mind_nparams 1) ||
     not (Int.equal (Array.length mip.Declarations.mind_user_lc) 2)
  then fail_peano_fueled_worker "the comparison predicate is not Peano <=";
  let ind_term = Constr.UnsafeMonomorphic.mkInd scheme.Retroknowledge.peano_inductive in
  let le a b = Constr.mkApp
    (Constr.UnsafeMonomorphic.mkInd le_ind, [|a; b|]) in
  let succ x = apply1 (mono_ctor scheme.peano_succ) x in
  let irrelevant = Context.make_annot Anonymous Sorts.Irrelevant in
  let refl_type =
    Constr.mkProd (Context.anonR, ind_term, le (Constr.mkRel 1) (Constr.mkRel 1))
  in
  let step_type =
    Constr.mkProd (Context.anonR, ind_term,
      Constr.mkProd (Context.anonR, ind_term,
        Constr.mkProd (irrelevant, le (Constr.mkRel 2) (Constr.mkRel 1),
          le (Constr.mkRel 3) (succ (Constr.mkRel 2)))))
  in
  if not (peano_convertible env mip.Declarations.mind_user_lc.(0) refl_type &&
          peano_convertible env mip.Declarations.mind_user_lc.(1) step_type)
  then fail_peano_fueled_worker "the comparison predicate is not Peano <="

let peano_fueled_worker_shape description env worker =
  let () = check_transparent env description worker in
  let fail () = fail_peano_fueled_worker
    "the worker must have type D -> proof -> D -> D -> proof -> D" in
  let ty = (Environ.lookup_constant worker env).Declarations.const_type in
  match Constr.kind ty with
  | Constr.Prod (y_annot, ind_term, rest) -> begin
    match Constr.kind ind_term, Constr.kind rest with
    | Constr.Ind (ind, u), Constr.Prod (hy_annot, hy_type, rest)
      when UVars.Instance.is_empty u ->
      let env_y = push_rel_assum y_annot ind_term env in
      let env_y_hy = push_rel_assum hy_annot hy_type env_y in
      begin match Constr.kind rest with
      | Constr.Prod (fuel_annot, fuel_type, rest)
        when Constr.equal fuel_type ind_term ->
        let env_fuel = push_rel_assum fuel_annot fuel_type env_y_hy in
        begin match Constr.kind rest with
        | Constr.Prod (x_annot, x_type, rest)
          when Constr.equal x_type ind_term ->
          let env_x = push_rel_assum x_annot x_type env_fuel in
          begin match Constr.kind rest with
          | Constr.Prod (hfuel_annot, hfuel_type, result)
            when Constr.equal result ind_term &&
                 Sorts.relevance_equal hy_annot.binder_relevance
                   Sorts.Irrelevant &&
                 Sorts.relevance_equal hfuel_annot.binder_relevance
                   Sorts.Irrelevant ->
            ind, ind_term, hy_type, env_y, hfuel_type, env_x
          | _ -> fail ()
          end
        | _ -> fail ()
        end
      | _ -> fail ()
      end
    | _ -> fail ()
    end
  | _ -> fail ()

let check_dependent_if env_ctx dite result_type predicate decider zero succ_zero =
  let decider_type =
    Reduction.whd_all (peano_baseline_env env_ctx)
      (Typeops.infer env_ctx decider).Environ.uj_type
  in
  let dec_ind, dec_u =
    let head, args = Constr.decompose_app decider_type in
    match Constr.kind head with
    | Constr.Ind (ind, u) when Int.equal (Array.length args) 1 &&
        peano_convertible env_ctx args.(0) predicate -> ind, u
    | _ -> fail_peano_fueled_worker
        "the condition is not decided by a two-constructor type"
  in
  let spec = Inductive.lookup_mind_specif env_ctx dec_ind in
  let mib, mip = spec in
  if not (Int.equal (Array.length mib.Declarations.mind_packets) 1) ||
     not (Int.equal mib.Declarations.mind_nparams 1) ||
     not (Int.equal (Array.length mip.Declarations.mind_user_lc) 2)
  then fail_peano_fueled_worker
    "the condition is not decided by a two-constructor type";
  let constructor_domain i =
    let ty = Inductive.type_of_constructor ((dec_ind, i), dec_u) spec in
    let ty = Reduction.hnf_prod_applist (peano_baseline_env env_ctx)
      ty [predicate] in
    match Constr.kind ty with
    | Constr.Prod (annot, domain, codomain)
      when peano_convertible env_ctx codomain (Vars.lift 1 decider_type) ->
      annot, domain
    | _ -> fail_peano_fueled_worker "a decision constructor has the wrong type"
  in
  let first_annot, first_domain = constructor_domain 1 in
  let second_annot, second_domain = constructor_domain 2 in
  let true_ctor, true_annot, false_ctor, false_annot, false_domain =
    if peano_convertible env_ctx first_domain predicate then
      (dec_ind, 1), first_annot, (dec_ind, 2), second_annot, second_domain
    else if peano_convertible env_ctx second_domain predicate then
      (dec_ind, 2), second_annot, (dec_ind, 1), first_annot, first_domain
    else fail_peano_fueled_worker
      "the decision type has no positive constructor"
  in
  let empty_type =
    match Constr.kind (Reduction.whd_all (peano_baseline_env env_ctx) false_domain) with
    | Constr.Prod (_, domain, codomain)
      when peano_convertible env_ctx domain predicate -> codomain
    | _ -> fail_peano_fueled_worker
        "the negative decision constructor is not a negation"
  in
  let empty_ind =
    let head, args = Constr.decompose_app
      (Reduction.whd_all (peano_baseline_env env_ctx) empty_type) in
    match Constr.kind head with
    | Constr.Ind (ind, _) when Array.is_empty args -> ind
    | _ -> fail_peano_fueled_worker
        "the negation does not target an empty inductive"
  in
  let empty_mib, empty_mip = Inductive.lookup_mind_specif env_ctx empty_ind in
  if not (Int.equal (Array.length empty_mib.Declarations.mind_packets) 1) ||
     not (Array.is_empty empty_mip.Declarations.mind_user_lc)
  then fail_peano_fueled_worker
    "the negation does not target an empty inductive";
  let make_branch annot domain result = Constr.mkLambda (annot, domain, result) in
  let check ctor outer_annot outer_domain expected =
    let lifted_predicate = Vars.lift 1 predicate in
    let lifted_false_domain = Vars.lift 1 false_domain in
    let decision = Constr.mkApp
      (Constr.mkConstructU (ctor, dec_u), [|lifted_predicate; Constr.mkRel 1|]) in
    let on_true = make_branch true_annot lifted_predicate zero in
    let on_false = make_branch false_annot lifted_false_domain succ_zero in
    let body = Constr.mkApp
      (dite, [|result_type; lifted_predicate; decision; on_true; on_false|]) in
    check_peano_conversion env_ctx "division worker conditional"
      (Constr.mkLambda (outer_annot, outer_domain, body))
      (Constr.mkLambda (outer_annot, outer_domain, expected))
  in
  check true_ctor true_annot predicate zero;
  check false_ctor false_annot false_domain succ_zero;
  dec_ind, dec_u, true_ctor, false_ctor, empty_ind

let check_register_peano_nat_fueled_go kind env expected_ind worker =
  let description = match kind with
  | PeanoQuotient -> "division worker"
  | PeanoRemainder -> "modulus worker"
  in
  let ind, ind_term, hy_type, env_y, hfuel_type, env_x =
    peano_fueled_worker_shape description env worker in
  let scheme = find_peano_nat env ind in
  let zero = mono_ctor scheme.peano_zero in
  let succ x = apply1 (mono_ctor scheme.peano_succ) x in
  let is_rel n t = match Constr.kind t with
    | Constr.Rel n' -> Int.equal n n'
    | _ -> false
  in
  let le_ind =
    let hy_type = Reduction.whd_all (peano_baseline_env env_y) hy_type in
    let head, args = Constr.decompose_app hy_type in
    match Constr.kind head with
    | Constr.Ind (le_ind, u) when UVars.Instance.is_empty u &&
        Int.equal (Array.length args) 2 &&
        peano_convertible env_y args.(0) (succ zero) && is_rel 1 args.(1) ->
      le_ind
    | _ -> fail_peano_fueled_worker
        "the divisor proof is not 0 < divisor"
  in
  let () = check_peano_le env scheme le_ind in
  let le a b = Constr.mkApp
    (Constr.UnsafeMonomorphic.mkInd le_ind, [|a; b|]) in
  let irrelevant = Context.make_annot Anonymous Sorts.Irrelevant in
  let env_y_hy = push_rel_assum irrelevant hy_type env_y in
  let env_y_hy_x = push_rel_assum Context.anonR ind_term env_y_hy in
  let env_y_hy_x_fuel =
    push_rel_assum Context.anonR ind_term env_y_hy_x in
  let equation_hfuel_type = le (succ (Constr.mkRel 2))
    (succ (Constr.mkRel 1)) in
  let env_ctx =
    push_rel_assum irrelevant equation_hfuel_type env_y_hy_x_fuel in
  let lhs = Constr.mkApp (mono_const worker,
    [|Constr.mkRel 5; Constr.mkRel 4; succ (Constr.mkRel 2);
      Constr.mkRel 3; Constr.mkRel 1|]) in
  let rec unfold_to_conditional depth constants projections =
    if Int.equal depth 0 then
      fail_peano_fueled_worker
        "one-step unfolding exceeded its constant bound";
    let flags = RedFlags.mkflags
      [RedFlags.fBETA; RedFlags.fDELTA; RedFlags.fMATCH; RedFlags.fFIX;
       RedFlags.fCOFIX; RedFlags.fZETA] in
    let flags = List.fold_left (fun flags c ->
      RedFlags.red_add flags (RedFlags.fCONST c)) flags constants in
    let flags = List.fold_left (fun flags p ->
      RedFlags.red_add flags (RedFlags.fPROJ p)) flags projections in
    let baseline = peano_baseline_env env_ctx in
    let infos = CClosure.create_clos_infos flags baseline in
    let reduced = CClosure.whd_val infos (CClosure.create_tab ())
      (CClosure.inject lhs) in
    let head, args = Constr.decompose_app reduced in
    let conditional = match Constr.kind head with
    | Constr.Const _ ->
      Int.equal (Array.length args) 5 &&
      peano_convertible env_ctx args.(0) ind_term &&
      begin match Constr.kind args.(3), Constr.kind args.(4) with
      | Constr.Lambda _, Constr.Lambda _ -> true
      | _ -> false
      end
    | _ -> false
    in
    if conditional then reduced
    else match Constr.kind head with
    | Constr.Const (c, _) when
        not (List.exists (Constant.UserOrd.equal c) constants) ->
      unfold_to_conditional (depth - 1) (c :: constants) projections
    | Constr.Proj (p, _, record) ->
      let p = Projection.repr p in
      let projection_is_new =
        not (List.exists (Projection.Repr.UserOrd.equal p) projections) in
      let projections =
        if projection_is_new then p :: projections else projections in
      let record_head, _ = Constr.decompose_app record in
      begin match Constr.kind record_head with
      | Constr.Const (c, _) when
          not (List.exists (Constant.UserOrd.equal c) constants) ->
        unfold_to_conditional (depth - 1) (c :: constants) projections
      | _ when projection_is_new ->
        unfold_to_conditional (depth - 1) constants projections
      | _ -> fail_peano_fueled_worker
          "one-step unfolding is blocked at a projection"
      end
    | _ -> fail_peano_fueled_worker
        "one-step unfolding did not expose its conditional"
  in
  let rhs = unfold_to_conditional 64 [worker] [] in
  let dite, predicate, decider, on_true, on_false =
    let head, args = Constr.decompose_app rhs in
    match Constr.kind head with
    | Constr.Const _ when Int.equal (Array.length args) 5 &&
        peano_convertible env_ctx args.(0) ind_term ->
      head, args.(1), args.(2), args.(3), args.(4)
    | _ -> fail_peano_fueled_worker
        "one-step unfolding is not a dependent conditional"
  in
  let predicate_le_ind =
    let predicate = Reduction.whd_all (peano_baseline_env env_ctx) predicate in
    let head, args = Constr.decompose_app predicate in
    match Constr.kind head with
    | Constr.Ind (le_ind, u) when UVars.Instance.is_empty u &&
        Int.equal (Array.length args) 2 && is_rel 5 args.(0) &&
        is_rel 3 args.(1) -> le_ind
    | _ -> fail_peano_fueled_worker "the condition is not y <= x"
  in
  if not (Ind.UserOrd.equal predicate_le_ind le_ind) then
    fail_peano_fueled_worker "the worker uses two comparison predicates";
  let decider_constant =
    let head, args = Constr.decompose_app decider in
    match Constr.kind head with
    | Constr.Const (decider_constant, u)
      when UVars.Instance.is_empty u && Int.equal (Array.length args) 2 &&
        is_rel 5 args.(0) && is_rel 3 args.(1) -> decider_constant
    | _ -> fail_peano_fueled_worker
        "the decision procedure is not applied to y and x"
  in
  check_peano_conversion env_y description hy_type
    (le (succ zero) (Constr.mkRel 1));
  check_peano_conversion env_x description hfuel_type
    (le (succ (Constr.mkRel 1)) (Constr.mkRel 2));
  let true_annot, true_type, true_body = match Constr.kind on_true with
  | Constr.Lambda (annot, ty, body) -> annot, ty, body
  | _ -> fail_peano_fueled_worker "the positive branch is not a function"
  in
  check_peano_conversion env_ctx description true_type predicate;
  let env_true = push_rel_assum true_annot true_type env_ctx in
  let sub = match scheme.Retroknowledge.peano_sub with
  | Some sub -> mono_const sub
  | None -> fail_peano_fueled_worker "register Peano subtraction first"
  in
  let recursive =
    let _, true_args = Constr.decompose_app true_body in
    let candidates = true_body :: Array.to_list true_args in
    let recognize candidate =
      let _, args = Constr.decompose_app candidate in
      if Array.is_empty args then None else
      let recursive_proof = args.(Array.length args - 1) in
      let expected = Constr.mkApp (mono_const worker,
        [|Constr.mkRel 6; Constr.mkRel 5; Constr.mkRel 3;
          apply2 sub (Constr.mkRel 4) (Constr.mkRel 6); recursive_proof|]) in
      try
        let expected_type =
          (Typeops.infer env_true expected).Environ.uj_type in
        if peano_convertible env_true expected_type ind_term &&
           peano_convertible env_true candidate expected
        then Some candidate else None
      with error when CErrors.noncritical error -> None
    in
    match List.filter_map recognize candidates with
    | [recursive] -> recursive
    | _ -> fail_peano_fueled_worker
        "the positive branch does not expose one recursive result"
  in
  let expected_true = match kind with
  | PeanoQuotient -> succ recursive
  | PeanoRemainder -> recursive
  in
  check_peano_conversion env_true description true_body expected_true;
  let false_annot, false_type, false_body = match Constr.kind on_false with
  | Constr.Lambda (annot, ty, body) -> annot, ty, body
  | _ -> fail_peano_fueled_worker "the negative branch is not a function"
  in
  let env_false = push_rel_assum false_annot false_type env_ctx in
  let expected_false = match kind with
  | PeanoQuotient -> zero
  | PeanoRemainder -> Constr.mkRel 4
  in
  check_peano_conversion env_false description false_body expected_false;
  let decision_ind, decision_u, decision_true, decision_false, empty_ind =
    check_dependent_if env_ctx dite ind_term predicate decider zero (succ zero) in
  let empty = Constr.UnsafeMonomorphic.mkInd empty_ind in
  let observe predicate decision =
    let negative = Constr.mkProd (true_annot, predicate, empty) in
    let on_true = Constr.mkLambda (true_annot, predicate, zero) in
    let on_false = Constr.mkLambda (false_annot, negative, succ zero) in
    Constr.mkApp
      (dite, [|ind_term; predicate; decision; on_true; on_false|])
  in
  let bool_operation =
    List.find_opt (fun operation ->
      Ind.UserOrd.equal ind operation.Retroknowledge.bool_op_inductive)
      (Environ.retroknowledge env).Retroknowledge.retro_peano_nat_ble
  in
  let bool_operation = match bool_operation with
  | Some operation -> operation
  | None -> fail_peano_fueled_worker
      "register Peano <= before its decision procedure"
  in
  let bool_ind = fst bool_operation.Retroknowledge.bool_op_false in
  let bool_term = Constr.UnsafeMonomorphic.mkInd bool_ind in
  let bool_false = mono_ctor bool_operation.bool_op_false in
  let bool_true = mono_ctor bool_operation.bool_op_true in
  let ble = mono_const bool_operation.bool_op_constant in
  let decider_body = Environ.constant_value_in env
    (decider_constant, UVars.Instance.empty) in
  let decider_lambdas, decider_body = Term.decompose_lambda decider_body in
  if not (Int.equal (List.length decider_lambdas) 2) then
    fail_peano_fueled_worker
      "the decision procedure must abstract y and x";
  let body_head, body_args = Constr.decompose_app decider_body in
  let dite_constant = match Constr.kind dite with
  | Constr.Const (constant, _) -> constant
  | _ -> assert false
  in
  begin match Constr.kind body_head with
  | Constr.Const (constant, _) when Constant.UserOrd.equal constant dite_constant &&
      Int.equal (Array.length body_args) 5 -> ()
  | _ -> fail_peano_fueled_worker
      "the decision procedure is not a dependent Boolean test"
  end;
  let equality_ind, equality_u, tested_bool =
    let head, args = Constr.decompose_app body_args.(1) in
    match Constr.kind head with
    | Constr.Ind (equality_ind, equality_u)
      when Int.equal (Array.length args) 3 &&
        Constr.equal args.(0) bool_term &&
        Constr.equal args.(1)
          (apply2 ble (Constr.mkRel 2) (Constr.mkRel 1)) &&
        Constr.equal args.(2) bool_true ->
      equality_ind, equality_u, args.(1)
    | _ -> fail_peano_fueled_worker
      "the decision procedure does not test whether y <= x is true"
  in
  let equality_mib, equality_mip =
    Inductive.lookup_mind_specif env equality_ind in
  if not
      (Int.equal
         (Array.length equality_mib.Declarations.mind_packets) 1 &&
       Int.equal equality_mib.Declarations.mind_nparams 2 &&
       Int.equal
         (Array.length equality_mip.Declarations.mind_user_lc) 1 &&
       Int.equal equality_mip.Declarations.mind_consnrealargs.(0) 0)
  then fail_peano_fueled_worker
    "the Boolean test does not use an equality type";
  let bool_decider_head =
    let head, args = Constr.decompose_app body_args.(2) in
    match Constr.kind head with
    | Constr.Const (_, _) when Int.equal (Array.length args) 2 &&
        Constr.equal args.(0) tested_bool && Constr.equal args.(1) bool_true ->
      head
    | _ -> fail_peano_fueled_worker
      "the Boolean equality test has the wrong arguments"
  in
  let check_decision_branch expected branch =
    match Constr.kind branch with
    | Constr.Lambda (_, _, body) ->
      let head, _ = Constr.decompose_app body in
      begin match Constr.kind head with
      | Constr.Construct (constructor, _) when
          Construct.UserOrd.equal constructor expected -> ()
      | _ -> fail_peano_fueled_worker
          "a decision branch returns the wrong constructor"
      end
    | _ -> fail_peano_fueled_worker
        "a decision branch is not a function"
  in
  check_decision_branch decision_true body_args.(3);
  check_decision_branch decision_false body_args.(4);
  let equality a b = Constr.mkApp
    (Constr.mkIndU (equality_ind, equality_u), [|bool_term; a; b|]) in
  let decide_bool a b = Constr.mkApp (bool_decider_head, [|a; b|]) in
  let observe_equality a b = observe (equality a b) (decide_bool a b) in
  check_peano_conversion env (description ^ " Boolean decision")
    (observe_equality bool_false bool_false) zero;
  check_peano_conversion env (description ^ " Boolean decision")
    (observe_equality bool_false bool_true) (succ zero);
  check_peano_conversion env (description ^ " Boolean decision")
    (observe_equality bool_true bool_false) (succ zero);
  check_peano_conversion env (description ^ " Boolean decision")
    (observe_equality bool_true bool_true) zero;
  let expected_decision = Constr.mkApp
    (Constr.mkIndU (decision_ind, decision_u), [|le (Constr.mkRel 2)
      (Constr.mkRel 1)|]) in
  let env_y_x = push_rel_assum Context.anonR ind_term
    (push_rel_assum Context.anonR ind_term env) in
  check_peano_conversion env_y_x (description ^ " decision result")
    body_args.(0) expected_decision;
  begin match expected_ind with
  | Some expected_ind when Ind.UserOrd.equal expected_ind ind -> ()
  | None -> ()
  | Some _ -> fail_peano_fueled_worker
      "the persisted descriptor does not match the worker"
  end;
  ind, worker

let register_peano_nat_div_go worker senv =
  let env = senv.env in
  let ind, worker = check_register_peano_nat_fueled_go PeanoQuotient
    env None worker in
  let scheme = find_peano_nat env ind in
  let duplicate =
    List.exists (Constant.UserOrd.equal worker) scheme.peano_div_go in
  if duplicate then senv
  else add_retroknowledge
    (Retroknowledge.Register_peano_nat_div_go (ind, worker)) senv

let register_peano_nat_mod_go worker senv =
  let env = senv.env in
  let ind, worker = check_register_peano_nat_fueled_go PeanoRemainder
    env None worker in
  let scheme = find_peano_nat env ind in
  let duplicate =
    List.exists (Constant.UserOrd.equal worker) scheme.peano_mod_go in
  if duplicate then senv
  else add_retroknowledge
    (Retroknowledge.Register_peano_nat_mod_go (ind, worker)) senv

let check_peano_retroknowledge env = function
  | Retroknowledge.Register_peano_nat ind ->
    check_register_peano_nat ind (Inductive.lookup_mind_specif env ind)
  | Retroknowledge.Register_peano_nat_double (ind, c) ->
    check_register_peano_nat_double env ind c
  | Retroknowledge.Register_peano_nat_of_N (ind, n_ind, pos_ind, c) ->
    check_register_peano_nat_of_N env ind n_ind pos_ind c
  | Retroknowledge.Register_peano_nat_add (ind, c) ->
    check_register_peano_nat_operation env PeanoAdd ind c
  | Retroknowledge.Register_peano_nat_mul (ind, c) ->
    check_register_peano_nat_operation env PeanoMul ind c
  | Retroknowledge.Register_peano_nat_pow (ind, c) ->
    check_register_peano_nat_operation env PeanoPow ind c
  | Retroknowledge.Register_peano_nat_sub (ind, c) ->
    check_register_peano_nat_operation env PeanoSub ind c
  | Retroknowledge.Register_peano_nat_div_go (ind, worker) ->
    ignore (check_register_peano_nat_fueled_go PeanoQuotient
      env (Some ind) worker)
  | Retroknowledge.Register_peano_nat_mod_go (ind, worker) ->
    ignore (check_register_peano_nat_fueled_go PeanoRemainder
      env (Some ind) worker)
  | Retroknowledge.Register_peano_nat_beq (ind, c, false_ctor, true_ctor) ->
    check_register_peano_nat_bool PeanoBeq env ind c false_ctor true_ctor
  | Retroknowledge.Register_peano_nat_ble (ind, c, false_ctor, true_ctor) ->
    check_register_peano_nat_bool PeanoBle env ind c false_ctor true_ctor
  | Retroknowledge.Register_unit_like ind ->
    check_register_unit_like ind (Inductive.lookup_mind_specif env ind)
  | Retroknowledge.Register_ind _ | Retroknowledge.Register_type _ ->
    invalid_arg "Safe_typing.check_peano_retroknowledge"

(* NB: The next old comment probably refers to [propagate_loads] above.
   When a Require is done inside a module, we'll redo this require
   at the upper level after the module is ended, and so on.
   This is probably not a big deal anyway, since these Require's
   inside modules should be pretty rare. Maybe someday we could
   brutally forbid this tricky "feature"... *)

(* we have an inefficiency: Since loaded files are added to the
environment every time a module is closed, their components are
calculated many times. This could be avoided in several ways:

1 - for each file create a dummy environment containing only this
file's components, merge this environment with the global
environment, and store for the future (instead of just its type)

2 - create "persistent modules" environment table in Environ add put
loaded by side-effect once and for all (like it is done in OCaml).
Would this be correct with respect to undo's and stuff ?
*)

let set_oracle ts e =
  { e with env = Environ.set_oracle e.env ts }

let set_strategy k l e = { e with env =
   (Environ.set_oracle e.env
      (Conv_oracle.set_strategy (Environ.oracle e.env) k l)) }
