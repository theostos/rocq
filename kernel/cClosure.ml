(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Created by Bruno Barras with Benjamin Werner's account to implement
   a call-by-value conversion algorithm and a lazy reduction machine
   with sharing, Nov 1996 *)
(* Addition of zeta-reduction (let-in contraction) by Hugo Herbelin, Oct 2000 *)
(* Call-by-value machine moved to cbv.ml, Mar 01 *)
(* Additional tools for module subtyping by Jacek Chrzaszcz, Aug 2002 *)
(* Extension with closure optimization by Bruno Barras, Aug 2003 *)
(* Support for evar reduction by Bruno Barras, Feb 2009 *)
(* Miscellaneous other improvements by Bruno Barras, 1997-2009 *)

(* This file implements a lazy reduction for the Calculus of Inductive
   Constructions *)

[@@@ocaml.warning "+4"]

open CErrors
open Util
open Names
open Constr
open Declarations
open Context
open Environ
open Vars
open Esubst
open RedFlags

module RelDecl = Context.Rel.Declaration
module NamedDecl = Context.Named.Declaration

type mode = Conversion | Reduction
(* In conversion mode we can introduce FIrrelevant terms.
   Invariants of the conversion mode:
   - the only irrelevant terms as returned by [knr] are either [FIrrelevant],
     [FLambda], [FFlex] or [FRel].
   - the stack never contains irrelevant-producing nodes i.e. [Zproj], [ZFix]
     and [ZcaseT] are all relevant
*)

(**********************************************************************)
(* Lazy reduction: the one used in kernel operations                  *)

(* type of shared terms. fconstr and frterm are mutually recursive.
 * Clone of the constr structure, but completely mutable, and
 * annotated with reduction state (reducible or not).
 *  - FLIFT is a delayed shift; allows sharing between 2 lifted copies
 *    of a given term.
 *  - FCLOS is a delayed substitution applied to a constr
 *  - FLOCKED is used to erase the content of a reference that must
 *    be updated. This is to allow the garbage collector to work
 *    before the term is computed.
 *)

(* Ntrl means the term is in βιδζ head normal form and cannot create a redex
     when substituted
   Cstr means the term is in βιδζ head normal form and that it can
     create a redex when substituted (i.e. constructor, fix, lambda)
   Red is used for terms that might be reduced
*)
type red_state = Ntrl | Cstr | Red

let neutr = function Ntrl -> Ntrl | Red | Cstr -> Red
let is_red = function Red -> true | Ntrl | Cstr -> false

type table_key = Constant.t UVars.puniverses tableKey

type evar_repack = Evar.t * constr list -> constr

module PeanoNatValue = struct
  (* little-endian bits without trailing zero: arbitrary precision, linear in
     the size of imported numerals *)
  type t = bool list

  let zero = []
  let one = [true]
  let is_zero = List.is_empty
  let equal = List.equal Bool.equal

  let norm bits =
    let rec drop = function false :: bits -> drop bits | bits -> bits in
    List.rev (drop (List.rev bits))

  let rec succ = function
    | [] -> [true]
    | false :: bits -> true :: bits
    | true :: bits -> false :: succ bits

  let pred = function
    | [] -> None
    | bits ->
      let rec go = function
        | [true] -> []
        | true :: bits -> false :: bits
        | false :: bits -> true :: go bits
        | [] -> assert false
      in
      Some (go bits)

  let double = function
    | [] -> []
    | bits -> false :: bits

  let rec add_carry carry a b = match a, b with
    | [], [] -> if carry then [true] else []
    | [], bits | bits, [] -> if carry then succ bits else bits
    | x :: a, y :: b ->
      (x <> y <> carry) :: add_carry ((x && y) || (carry && (x || y))) a b

  let add a b = add_carry false a b

  let rec mul a = function
    | [] -> zero
    | bit :: bits ->
      let higher = double (mul a bits) in
      if bit then add a higher else higher

  let compare a b =
    let c = Int.compare (List.length a) (List.length b) in
    if not (Int.equal c 0) then c
    else List.compare Bool.compare (List.rev a) (List.rev b)

  let le a b = compare a b <= 0

  (* [pow] gives up on results above a million bits *)
  let pow base exponent =
    let mul a b = let v = mul a b in if List.length v <= 1_000_000 then Some v else None in
    let rec loop result factor = function
      | [] -> Some result
      | bit :: bits ->
        let result = if bit then mul result factor else Some result in
        Option.bind result (fun result ->
          if List.is_empty bits then Some result
          else Option.bind (mul factor factor) (fun factor -> loop result factor bits))
    in
    loop one base exponent

  (* truncated subtraction *)
  let sub a b =
    if compare a b < 0 then zero else
    let rec borrow c a b = match a, b with
      | [], [] -> assert (not c); []
      | x :: a, [] -> (x <> c) :: borrow ((not x) && c) a []
      | x :: a, y :: b ->
        (x <> y <> c) :: borrow (((not x) && (y || c)) || (y && c)) a b
      | [], _ :: _ -> assert false
    in
    norm (borrow false a b)

  (* [div_mod a 0] is [0, 0] *)
  let div_mod dividend divisor =
    if is_zero divisor then zero, zero
    else
      let step (remainder, quotient) bit =
        let remainder = double remainder in
        let remainder = if bit then succ remainder else remainder in
        if compare remainder divisor < 0 then remainder, false :: quotient
        else sub remainder divisor, true :: quotient
      in
      let remainder, quotient = List.fold_left step (zero, []) (List.rev dividend) in
      norm quotient, remainder
end

type compact_peano = {
  peano_ind : inductive;
  peano_zero : constructor;
  peano_succ : constructor;
  peano_double : Constant.t;
  peano_value : PeanoNatValue.t;
}

type fconstr = {
  mutable state : int;
  mutable term: fterm;
  mutable symbolic : symbolic_view;
  mutable free : int; (* memoised [min_free_rel]: 0 unknown, [max_int] closed *)
}

(* Sharing overwrites a reduced cell with its value: the cell keeps a copy of
   the spine it had, which a symbolic reduction (see [knh]) reads instead. *)
and symbolic_view =
  | NoSymbolicView
  | SymbolicView of fconstr (* a copy of the former spine *)
  | SymbolicCopy (* the copy itself: immutable, never locked *)

and fterm =
  | FRel of int
  | FAtom of constr (* Metas and Sorts *)
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

and subs_content =
  | Regular of fconstr
  | HigherOrder of int * fconstr

and usubs = subs_content subs UVars.puniverses

and finvert = fconstr array

(* [state] packs the reduction mark in its two low bits and a unique creation
   counter above them, so [fconstr_hash] identifies a cell exactly. *)
let fconstr_hash v = v.state lsr 2

let mark_code = function Ntrl -> 0 | Cstr -> 1 | Red -> 2

let fconstr_mark v = match v.state land 3 with 0 -> Ntrl | 1 -> Cstr | _ -> Red

let set_fconstr_mark v mark = v.state <- v.state land lnot 3 lor mark_code mark

let next_uid = Atomic.make 0

let fresh_fconstr mark term =
  { state = Atomic.fetch_and_add next_uid 1 lsl 2 lor mark_code mark; term;
    symbolic = NoSymbolicView; free = 0 }

(* Content-addressed cells: closures with the same constructor, syntax, child
   cells and (shallowly) the same substitution denote the same term and share
   one cell, so that in-place reductions and the identity-keyed memos of a
   conversion apply to every occurrence of a shared subterm. *)
module CellTab = Hashtbl.Make (struct
  type t = fterm

  let eq_value a b = match a, b with
    | Regular a, Regular b -> a == b
    | HigherOrder (n, a), HigherOrder (m, b) -> Int.equal n m && a == b
    | (Regular _ | HigherOrder _), _ -> false
  let hash_value = function
    | Regular v -> fconstr_hash v
    | HigherOrder (n, v) -> Hashset.Combine.combine n (fconstr_hash v)
  let eq_usubs (s1, u1) (s2, u2) =
    (s1 == s2 || Esubst.eq_subs eq_value s1 s2) && (u1 == u2 || UVars.Instance.equal u1 u2)
  let hash_usubs (s, u) =
    Hashset.Combine.combine (Esubst.hash_subs hash_value s) (UVars.Instance.hash u)
  let hash_constr c = Hashtbl.hash_param 5 24 c

  let equal a b = match a, b with
    | FRel n, FRel m -> Int.equal n m
    | FAtom c, FAtom d -> c == d || Constr.equal c d
    | FFlex k, FFlex l -> eq_table_key (eq_pair eq_constant_key UVars.Instance.equal) k l
    | FInd (i, u), FInd (j, v) -> Ind.CanOrd.equal i j && UVars.Instance.equal u v
    | FConstruct ((c, u), a), FConstruct ((d, v), b) ->
      Construct.CanOrd.equal c d && UVars.Instance.equal u v && Array.equal (==) a b
    | FApp (h, a), FApp (g, b) -> h == g && Array.equal (==) a b
    | FProj (p, r, c), FProj (q, s, d) ->
      Projection.CanOrd.equal p q && Sorts.relevance_equal r s && c == d
    | FFix (((reci, i), rdcl), e), FFix (((reci', i'), rdcl'), e') ->
      (* the outer tuple is rebuilt at each unfolding, the rest is the syntax's *)
      Int.equal i i' && reci == reci' && rdcl == rdcl' && eq_usubs e e'
    | FCoFix ((i, rdcl), e), FCoFix ((i', rdcl'), e') ->
      Int.equal i i' && rdcl == rdcl' && eq_usubs e e'
    | FLambda (n, tys, b, e), FLambda (m, tys', b', e') ->
      (* [mk_lambda] allocates the domain list, its elements are the syntax's *)
      Int.equal n m && b == b' &&
      (tys == tys' ||
       List.equal (fun (na, ty) (na', ty') ->
           ty == ty' && Sorts.relevance_equal na.binder_relevance na'.binder_relevance) tys tys') &&
      eq_usubs e e'
    | FProd (na, ty, b, e), FProd (na', ty', b', e') ->
      na == na' && ty == ty' && b == b' && eq_usubs e e'
    | FLetIn (na, b, ty, c, e), FLetIn (na', b', ty', c', e') ->
      na == na' && b == b' && ty == ty' && c == c' && eq_usubs e e'
    | FLIFT (k, t), FLIFT (l, t') -> Int.equal k l && t == t'
    | FCLOS (t, e), FCLOS (t', e') -> t == t' && eq_usubs e e'
    | (FRel _ | FAtom _ | FFlex _ | FInd _ | FConstruct _ | FApp _ | FProj _ | FFix _
      | FCoFix _ | FLambda _ | FProd _ | FLetIn _ | FLIFT _ | FCLOS _ | FCaseT _
      | FCaseInvert _ | FEvar _ | FInt _ | FFloat _ | FString _ | FArray _ | FPeanoNat _
      | FIrrelevant | FLOCKED), _ -> false

  let hash term =
    let open Hashset.Combine in
    let cells a = Array.fold_left (fun acc c -> combine acc (fconstr_hash c)) 0 a in
    match term with
    | FRel n -> combinesmall 1 n
    | FAtom c -> combinesmall 2 (hash_constr c)
    | FFlex k -> combinesmall 3 (hash_table_key (fun (c, _) -> Constant.UserOrd.hash c) k)
    | FInd (i, _) -> combinesmall 4 (Ind.CanOrd.hash i)
    | FConstruct ((c, _), a) -> combinesmall 5 (combine (Construct.CanOrd.hash c) (cells a))
    | FApp (h, a) -> combinesmall 6 (combine (fconstr_hash h) (cells a))
    | FProj (p, _, c) -> combinesmall 7 (combine (Projection.CanOrd.hash p) (fconstr_hash c))
    | FFix (((_, i), (_, _, bodies)), e) ->
      combinesmall 8 (combine3 i (hash_constr bodies) (hash_usubs e))
    | FCoFix ((i, (_, _, bodies)), e) ->
      combinesmall 9 (combine3 i (hash_constr bodies) (hash_usubs e))
    | FLambda (n, _, b, e) -> combinesmall 10 (combine3 n (hash_constr b) (hash_usubs e))
    | FProd (_, ty, b, e) ->
      combinesmall 11 (combine3 (fconstr_hash ty) (hash_constr b) (hash_usubs e))
    | FLetIn (_, b, ty, c, e) ->
      combinesmall 12 (combine4 (fconstr_hash b) (fconstr_hash ty) (hash_constr c) (hash_usubs e))
    | FLIFT (k, t) -> combinesmall 13 (combine k (fconstr_hash t))
    | FCLOS (t, e) -> combinesmall 14 (combine (hash_constr t) (hash_usubs e))
    | FCaseT _ | FCaseInvert _ | FEvar _ | FInt _ | FFloat _ | FString _ | FArray _
    | FPeanoNat _ | FIrrelevant | FLOCKED -> 0
end)

let shareable = function
  | FRel _ | FAtom _ | FFlex _ | FInd _ | FConstruct _ | FApp _ | FProj _ | FFix _ | FCoFix _
  | FLambda _ | FProd _ | FLetIn _ | FLIFT _ | FCLOS _ -> true
  | FCaseT _ | FCaseInvert _ | FEvar _ | FInt _ | FFloat _ | FString _ | FArray _
  | FPeanoNat _ | FIrrelevant | FLOCKED -> false

(* The cells of the current sharing scope, see [with_cells]. *)
let cells : fconstr CellTab.t option ref = ref None

(* A cell under evaluation is never reused; a cell requested reducible accepts
   any mark, a certified mark must agree. *)
let make_fconstr mark term =
  match !cells with
  | Some cells when shareable term ->
    begin match CellTab.find_opt cells term with
    | Some v when v.term != FLOCKED && (mark == Red || mark_code mark == v.state land 3) -> v
    | Some _ -> fresh_fconstr mark term
    | None ->
      let v = fresh_fconstr mark term in
      (* a reset only loses sharing for later cells *)
      if CellTab.length cells >= 2_000_000 then CellTab.reset cells;
      CellTab.add cells term v; v
    end
  | _ -> fresh_fconstr mark term

(* Run [f] with cells allocated in [tab] ([None]: fresh cells only). *)
let with_cells tab f =
  let saved = !cells in
  cells := tab;
  match f () with
  | v -> cells := saved; v
  | exception e -> cells := saved; raise e

let get_invert fiv = fiv

let fterm_of v = v.term

(* Minimum free de Bruijn index of the term a cell denotes, relative to its
   frame; [max_int] when closed. Unknown shapes and an exhausted fuel answer
   1, the conservative value. *)
exception Min_free_exhausted
exception Min_free_one
let min_free_rel (v : fconstr) : int =
  let fuel = ref 4096 in
  let visit () = if !fuel <= 0 then raise Min_free_exhausted; decr fuel in
  let rec cell v =
    if v.free > 0 then v.free else begin
      visit ();
      let result = match v.term with
        | FRel n -> n
        | FAtom _ | FFlex (ConstKey _ | VarKey _ | RelKey _) | FInd _ | FInt _ | FFloat _
        | FString _ | FPeanoNat _ | FIrrelevant -> max_int
        | FConstruct (_, args) -> cells args
        | FApp (h, args) -> min (cell h) (cells args)
        | FProj (_, _, c) -> cell c
        | FLIFT (k, t) -> let m = cell t in if m = max_int then m else m + k
        | FCLOS (t, e) -> constr e 0 t
        | FLambda (_, tys, body, e) ->
          let rec domains depth acc = function
            | [] -> min acc (constr e depth body)
            | (_, ty) :: rest -> domains (depth + 1) (min acc (constr e depth ty)) rest
          in domains 0 max_int tys
        | FProd (_, ty, body, e) -> min (cell ty) (constr e 1 body)
        | FLetIn (_, b, ty, body, e) -> min (min (cell b) (cell ty)) (constr e 1 body)
        | FFix ((_, (names, tys, bodies)), e) | FCoFix ((_, (names, tys, bodies)), e) ->
          let n = Array.length names in
          let acc = Array.fold_left (fun acc ty -> min acc (constr e 0 ty)) max_int tys in
          Array.fold_left (fun acc b -> min acc (constr e n b)) acc bodies
        | FCaseT _ | FCaseInvert _ | FEvar _ | FArray _ | FLOCKED -> 1
      in
      (* reduction never frees a variable: the value stays a lower bound *)
      v.free <- result; result
    end
  and cells args = Array.fold_left (fun acc c -> min acc (cell c)) max_int args
  and constr (e, _) depth t =
    let best = ref max_int in
    let rec go depth t =
      visit ();
      match [@ocaml.warning "-4"] kind t with
      | Rel i ->
        if i > depth then begin
          let j = i - depth in
          (match expand_rel j e with
          | Inl (k, Regular v) ->
            let m = cell v in
            if m <> max_int then best := min !best (m + k)
          | Inl (_, HigherOrder _) -> best := 1
          | Inr (k, None) -> best := min !best k
          | Inr (_, Some _) -> ());
          if !best <= 1 then raise Min_free_one
        end
      | _ -> Constr.iter_with_binders succ go depth t
    in
    (try go depth t with Min_free_one -> ()); !best
  in
  try cell v with Min_free_exhausted -> (if v.free = 0 then v.free <- 1); 1

(* The former spine of a cell (or the cell itself) when its head, followed
   without reduction, is a flex. *)
let symbolic_view v =
  let view = match v.symbolic with
    | SymbolicView view -> view
    | NoSymbolicView | SymbolicCopy -> v in
  let rec flex_head fuel v =
    fuel > 0 && match [@ocaml.warning "-4"] v.term with
    | FFlex _ -> true
    | FApp (head, args) when Array.length args <= 256 -> flex_head (fuel - 1) head
    | FLIFT (_, head) | FProj (_, _, head) -> flex_head (fuel - 1) head
    | FCLOS (term, _) ->
      begin match [@ocaml.warning "-4"] Constr.kind (fst (Constr.decompose_app term)) with
      | Const _ | Var _ | Proj _ -> true
      | _ -> false end
    | _ -> false in
  if flex_head 32 view then Some view else None

let set_ntrl v = set_fconstr_mark v Ntrl

(* Number of syntax nodes [to_constr] builds for [n] (one for zero, two per
   doubling, two more per set bit); [None] when it exceeds [limit]. *)
let peano_quotation_cost ~limit n =
  let rec cost remaining total = function
    | [] -> Some total
    | bit :: rest ->
      let nodes = if bit then 4 else 2 in
      if remaining < nodes then None
      else cost (remaining - nodes) (total + nodes) rest in
  if limit < 1 then None else cost (limit - 1) 1 n.peano_value

let peano_constructor_view n =
  let empty = UVars.Instance.empty in
  match PeanoNatValue.pred n.peano_value with
  | None -> make_fconstr Cstr (FConstruct ((n.peano_zero, empty), [||]))
  | Some pred ->
    let pred = make_fconstr Cstr (FPeanoNat { n with peano_value = pred }) in
    make_fconstr Cstr (FConstruct ((n.peano_succ, empty), [|pred|]))

(* Could issue a warning if no is still Red, pointing out that we loose
   sharing. *)
let update v1 mark t =
  set_fconstr_mark v1 mark; v1.term <- t

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

let default_evar_handler env = {
  evar_expand = (fun _ -> assert false);
  evar_repack = (fun _ -> assert false);
  evar_irrelevant = (fun _ -> assert false);
  qvar_irrelevant = (fun q ->
      assert (QGraph.mem (QVar q) (Environ.qualities env));
      false);
  qual_equal = Sorts.Quality.equal;
  abstr_const = fun _ -> assert false;
}

let drop_opaque = function
| OpaqueDef _ -> OpaqueDef ()
| Def _ | Undef _ | Primitive _ | Symbol _ as body -> body

let drop_code env = function
| Vmemitcodes.BCdefined (mask, idx, patch) ->
  let code () = Environ.lookup_vm_code idx env in
  Vmemitcodes.BCdefined (mask, code, patch)
| (BCalias _ | BCconstant | BCuncompiled as code) -> code

let lookup_constant_handler env sigma cst = match lookup_constant_opt cst env with
| None -> sigma.abstr_const cst
| Some cb ->
  let const_body = drop_opaque cb.const_body in
  let const_body_code = drop_code env cb.const_body_code in
  { cb with const_body; const_body_code }

(** Reduction cache *)
type infos_cache = {
  i_env : env;
  i_sigma : evar_handler;
  i_share : bool;
  i_univs : UGraph.t;
  i_mode : mode;
}

type clos_infos = {
  i_flags : reds;
  i_symbolic : bool; (* symbolic reduction: reads the former spines of cells *)
  i_private : (fconstr -> fconstr) option; (* private view: copies a cell on demand *)
  i_relevances : Sorts.relevance Range.t;
  i_inspection : int ref option; (* remaining budget of an inspection *)
  i_cache : infos_cache }

(* An inspection is a budgeted reduction in a private view of the closures:
   every head step and cell visit is charged, and the operations it does not
   support decline. Both end the inspection with [Limit]. *)
module Inspection = struct
  exception Limit
  let active info = Option.has_some info.i_inspection
  let[@inline] charge info cost = match info.i_inspection with
    | None -> ()
    | Some remaining ->
      if cost > !remaining then raise_notrace Limit;
      remaining := !remaining - cost;
      if !remaining land 255 = 0 then Control.check_for_interrupt ()
  let[@inline] decline info = if active info then raise_notrace Limit
end

let info_flags info = info.i_flags
let info_env info = info.i_cache.i_env
let info_univs info = info.i_cache.i_univs

(* Symbolic reduction takes the former spine of a cell only during the cheap
   head reduction of a conversion; full reduction uses the values. *)
let symbolic_reduction info = info.i_symbolic && info.i_flags = RedFlags.betaiotazeta

let push_relevance infos x =
  { infos with i_relevances = Range.cons x.binder_relevance infos.i_relevances }

let push_relevances infos nas =
  { infos with
    i_relevances =
      Array.fold_left (fun l x -> Range.cons x.binder_relevance l)
        infos.i_relevances nas }

let set_info_relevances info r = { info with i_relevances = r }

let info_relevances info = info.i_relevances

(**********************************************************************)
(* The type of (machine) stacks (= lambda-bar-calculus' contexts)     *)
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

let empty_stack = []
let append_stack v s =
  if Int.equal (Array.length v) 0 then s else
  match s with
  | Zapp l :: s -> Zapp (Array.append v l) :: s
  | (ZcaseT _ | Zproj _ | Zfix _ | Zshift _ | Zupdate _ | Zprimitive _) :: _ | [] ->
    Zapp v :: s

(* Collapse the shifts in the stack *)
let zshift n s =
  match (n,s) with
      (0,_) -> s
    | (_,Zshift(k)::s) -> Zshift(n+k)::s
    | (_,(ZcaseT _ | Zproj _ | Zfix _ | Zapp _ | Zupdate _ | Zprimitive _) :: _) | _,[] -> Zshift(n)::s

let rec stack_args_size = function
  | Zapp v :: s -> Array.length v + stack_args_size s
  | Zshift(_)::s -> stack_args_size s
  | Zupdate(_)::s -> stack_args_size s
  | (ZcaseT _ | Zproj _ | Zfix _ | Zprimitive _) :: _ | [] -> 0

let usubs_shft (n,(e,u)) = subs_shft (n, e), u

module LiftMemo = Hashtbl.Make(struct
  type t = fconstr * int
  let equal (a, n) (b, m) = a == b && Int.equal n m
  let hash (v, n) = Hashtbl.hash (fconstr_hash v, n)
end)

(* Lifting. Preserves sharing (useful only for cell with norm=Red).
   lft_fconstr always create a new cell, while lift_fconstr avoids it
   when the lift is 0. Constructor arguments are copied, so a shared DAG of
   constructors is lifted once per cell. *)
let rec lft_fconstr n ft =
  match ft.symbolic with
  | SymbolicView _ -> lft_construct n ft
  | NoSymbolicView | SymbolicCopy -> lft_term n ft

and lft_term n ft =
  match ft.term with
    | (FInd _|FConstruct (_,[||])|FFlex(ConstKey _|VarKey _)|FInt _|FFloat _|FString _|FPeanoNat _|FIrrelevant) -> ft
    | FRel i -> make_fconstr (fconstr_mark ft) (FRel (i + n))
    | FLambda(k,tys,f,e) ->
      make_fconstr Cstr (FLambda (k, tys, f, usubs_shft (n, e)))
    | FFix(fx,e) ->
      make_fconstr Cstr (FFix (fx, usubs_shft (n, e)))
    | FCoFix(cfx,e) ->
      make_fconstr Cstr (FCoFix (cfx, usubs_shft (n, e)))
    | FLIFT(k,m) -> lft_fconstr (n+k) m
    | FConstruct _ -> lft_construct n ft
    | FLOCKED -> assert false
    | FFlex (RelKey _) | FAtom _ | FApp _ | FProj _ | FCaseT _ | FCaseInvert _ | FProd _
    | FLetIn _ | FEvar _ | FCLOS _ | FArray _ ->
      make_fconstr (fconstr_mark ft) (FLIFT (n, ft))

and lft_construct n ft =
  let tbl = LiftMemo.create 17 in
  let rec lift n ft =
    match LiftMemo.find_opt tbl (ft, n) with
    | Some v -> v
    | None ->
      Control.check_for_interrupt ();
      let v = match [@ocaml.warning "-4"] ft.term with
        | FConstruct (c, args) when not (Array.is_empty args) ->
          make_fconstr Cstr (FConstruct (c, Array.map (lift n) args))
        | FLIFT (k, m) -> lift (n + k) m
        | _ -> lft_term n ft in
      let v = match ft.symbolic with
        | NoSymbolicView | SymbolicCopy -> v
        | SymbolicView view ->
          (* a lifted cell with a view is a fresh cell, its view is shifted *)
          let v = if v == ft then fresh_fconstr (fconstr_mark ft) ft.term else v in
          let shifted = fresh_fconstr (fconstr_mark view) (FLIFT (n, view)) in
          shifted.symbolic <- SymbolicCopy;
          v.symbolic <- SymbolicView shifted;
          v in
      LiftMemo.add tbl (ft, n) v;
      v
  in
  lift n ft

let lift_fconstr k f =
  if Int.equal k 0 then f else lft_fconstr k f

let clos_rel e i =
  match expand_rel i e with
    | Inl (n, Regular mt) -> Regular (lift_fconstr n mt)
    | Inl (_, HigherOrder (0, mt)) -> Regular mt
    | Inl (_, HigherOrder (nargs, mt)) -> HigherOrder (nargs, mt)
    | Inr (k, None) -> Regular (make_fconstr Ntrl (FRel k))
    | Inr (k, Some p) ->
      Regular (lift_fconstr (k-p) (make_fconstr Red (FFlex (RelKey p))))

(* The value of a substituted variable, without its lift (regular values only:
   higher-order ones relocate differently). *)
let inspect_substituted_rel (e, _) i =
  match expand_rel i e with
  | Inl (_, Regular term) -> Some term
  | Inl (_, HigherOrder _) | Inr _ -> None

(* since the head may be reducible, we might introduce lifts of 0 *)
let compact_stack head stk =
  let rec strip_rec depth = function
    | Zshift(k)::s -> strip_rec (depth+k) s
    | Zupdate(m)::s ->
        (* Be sure to create a new cell otherwise sharing would be
           lost by the update operation *)
        let h' = lft_fconstr depth head in
        (** The stack contains [Zupdate] marks only if in sharing mode *)
        let () = update m (fconstr_mark h') h'.term in
        strip_rec depth s
    | ((ZcaseT _ | Zproj _ | Zfix _ | Zapp _ | Zprimitive _) :: _ | []) as stk -> zshift depth stk
  in
  strip_rec 0 stk

(* The spine of a cell about to be locked is kept for symbolic reduction,
   during the conversions of typed terms only. *)
let save_symbolic_view info m =
  if info.i_cache.i_mode = Conversion && Option.is_empty info.i_private &&
     not (Inspection.active info) &&
     (Environ.typing_flags info.i_cache.i_env).unfold_dep_heuristic
  then match [@ocaml.warning "-4"] m.symbolic, m.term with
    | NoSymbolicView, (FCLOS _ | FApp _ | FProj _) ->
      let copy = fresh_fconstr (fconstr_mark m) m.term in
      copy.symbolic <- SymbolicCopy;
      m.symbolic <- SymbolicView copy
    | _ -> ()

(* Put an update mark in the stack, only if needed *)
let zupdate info m s =
  let share = info.i_cache.i_share in
  if share && is_red (fconstr_mark m) && m.symbolic != SymbolicCopy then
    let () = save_symbolic_view info m in
    let s' = compact_stack m s in
    let _ = m.term <- FLOCKED in
    Zupdate(m)::s'
  else s

(* We use empty as a special identity value, if we don't check
   subst_instance_instance will raise array out of bounds. *)
let usubst_instance (_,u) u' =
  if UVars.Instance.is_empty u then u'
  else UVars.subst_instance_instance u u'

let usubst_punivs (_,u) (v,u' as orig) =
  if UVars.Instance.is_empty u then orig
  else v, UVars.subst_instance_instance u u'

let usubst_sort (_,u) s =
  if UVars.Instance.is_empty u then s
  else UVars.subst_instance_sort u s

let usubst_relevance (_,u) r =
  if UVars.Instance.is_empty u then r
  else UVars.subst_instance_relevance u r

let usubst_binder e x =
  let r = x.binder_relevance in
  let r' = usubst_relevance e r in
  if r == r' then x else { x with binder_relevance = r' }

let mk_lambda env t =
  let (rvars,t') = Term.decompose_lambda t in
  FLambda(List.length rvars, List.rev rvars, t', env)

let usubs_lift (e,u) = subs_lift e, u

let usubs_liftn n (e,u) = subs_liftn n e, u

(* t must be a FLambda and binding list cannot be empty *)
let destFLambda clos_fun t =
  match [@ocaml.warning "-4"] t.term with
  | FLambda(_,[(na,ty)],b,e) ->
    (usubst_binder e na,clos_fun e ty,clos_fun (usubs_lift e) b)
  | FLambda(n,(na,ty)::tys,b,e) ->
    (usubst_binder e na, clos_fun e ty,
     make_fconstr (fconstr_mark t) (FLambda (n - 1, tys, b, usubs_lift e)))
  | _ -> assert false

(* Optimization: do not enclose variables in a closure.
   Makes variable access much faster *)
let mk_clos (e:usubs) t =
  match kind t with
    | Rel i ->
      begin match clos_rel (fst e) i with
      | Regular v -> v
      | HigherOrder _ -> CErrors.anomaly Pp.(str "Uncaught pattern variable")
      end
    | Var x -> make_fconstr Red (FFlex (VarKey x))
    | Const c -> make_fconstr Red (FFlex (ConstKey (usubst_punivs e c)))
    | Sort s ->
      let s = usubst_sort e s in
      make_fconstr Ntrl (FAtom (mkSort s))
    | Meta _ -> make_fconstr Ntrl (FAtom t)
    | Ind kn -> make_fconstr Ntrl (FInd (usubst_punivs e kn))
    | Construct kn ->
      make_fconstr Cstr (FConstruct (usubst_punivs e kn, [||]))
    | Int i -> make_fconstr Cstr (FInt i)
    | Float f -> make_fconstr Cstr (FFloat f)
    | String s -> make_fconstr Cstr (FString s)
    | (CoFix _|Lambda _|Fix _|Prod _|Evar _|App _|Case _|Cast _|LetIn _|Proj _|Array _) ->
        make_fconstr Red (FCLOS (t, e))
  (* Invariant, pattern variables under apps are deferred to knht by being wrapped in FCLOS *)

let injectu c u = mk_clos (subs_id 0, u) c

let inject c = injectu c UVars.Instance.empty

let mk_irrelevant = make_fconstr Cstr FIrrelevant

let is_irrelevant info r = match info.i_cache.i_mode with
| Reduction -> false
| Conversion -> match r with
  | Sorts.Irrelevant -> true
  | Sorts.RelevanceVar q -> info.i_cache.i_sigma.qvar_irrelevant q
  | Sorts.Relevant -> false

let eq_quality info q1 q2 =
  info.i_cache.i_sigma.qual_equal q1 q2

(************************************************************************)

(* Relevance of the arguments of a term of type [typ]: [false] where the
   argument is irrelevant and need not be compared. *)
let relevance_mask info instance typ =
  let binders, _ = Term.decompose_prod typ in
  let relevant (binder, _) =
    not (is_irrelevant info (UVars.subst_instance_relevance instance binder.binder_relevance)) in
  Array.of_list (List.rev_map relevant binders)

let merge_masks first second =
  let length = max (Array.length first) (Array.length second) in
  Array.init length (fun index ->
    (index >= Array.length first || first.(index)) &&
    (index >= Array.length second || second.(index)))

type table_val = (fconstr * bool array, Empty.t, UVars.Instance.t * bool * machine_rewrite_rule list) constant_def

module Table : sig
  type t
  val create : ?shared:bool -> unit -> t
  val cells : t -> int -> fconstr CellTab.t option
  val lookup : clos_infos -> t -> table_key -> table_val
end = struct
  module Table = Hashtbl.Make(struct
    type t = table_key
    let equal = eq_table_key (eq_pair eq_constant_key UVars.Instance.equal)
    let hash = hash_table_key (fun (c, _) -> Constant.UserOrd.hash c)
  end)

  (* The tables of a conversion problem share cells, one content table per
     reduction class (see [reduction_class]); other tables allocate as usual. *)
  type t = { table : table_val Table.t; cells : fconstr CellTab.t Lazy.t array }

  let create ?(shared = false) () =
    { table = Table.create 17;
      cells = if shared then Array.init 128 (fun _ -> lazy (CellTab.create 64)) else [||] }

  let cells t cls = if Array.length t.cells = 0 then None else Some (Lazy.force t.cells.(cls))

  exception Irrelevant

  let shortcut_irrelevant info r =
    if is_irrelevant info r then raise Irrelevant

  let assoc_defined d =
    match d with
    | NamedDecl.LocalDef (_, c, _) -> inject c
    | NamedDecl.LocalAssum (_, _) -> raise Not_found

  let constant_value_in u = function
    | Def b -> injectu b u
    | OpaqueDef _ -> raise (NotEvaluableConst Opaque)
    | Undef _ -> raise (NotEvaluableConst NoBody)
    | Primitive p -> raise (NotEvaluableConst (IsPrimitive (u,p)))
    | Symbol _ -> assert false
    (*  Should already be dealt with *)

  let value_of info ref =
    try
      let env = info.i_cache.i_env in
      match ref with
      | RelKey n ->
        let d = Environ.lookup_rel n env in
        shortcut_irrelevant info (RelDecl.get_relevance d);
        let body =
          match d with
          | RelDecl.LocalAssum _ -> raise Not_found
          | RelDecl.LocalDef (_, t, _) ->
            (* an inspection pays for the syntax the lift traverses *)
            let () = if Inspection.active info then
              let rec visit t = Inspection.charge info 1; Constr.iter visit t in
              visit t in
            lift n t
        in
        Def (inject body, [||])
      | VarKey id ->
        let def = Environ.lookup_named id env in
        shortcut_irrelevant info
          (binder_relevance (NamedDecl.get_annot def));
        let ts = RedFlags.red_transparent info.i_flags in
        if TransparentState.is_transparent_variable ts id then
          Def (assoc_defined def, [||])
        else
          raise Not_found
      | ConstKey (cst,u) ->
        let cb = match lookup_constant_opt cst env with
        | Some cb -> { cb with const_body = drop_opaque cb.const_body; const_body_code = drop_code env cb.const_body_code }
        | None -> info.i_cache.i_sigma.abstr_const cst
        in
        shortcut_irrelevant info (UVars.subst_instance_relevance u cb.const_relevance);
        let ts = RedFlags.red_transparent info.i_flags in
        if TransparentState.is_transparent_constant ts cst then match cb.const_body with
        | Undef _ | Def _ | OpaqueDef _ | Primitive _ ->
          let mask = if Inspection.active info then [||] else
          let mask = match cb.const_body_code with
          | (Vmemitcodes.BCalias _ | Vmemitcodes.BCconstant | BCuncompiled) -> [||]
          | (Vmemitcodes.BCdefined (mask, _, _)) -> mask
          in
          merge_masks mask (relevance_mask info u cb.const_type)
          in
          Def (constant_value_in u cb.const_body, mask)
        | Symbol b ->
          let r = match lookup_rewrite_rules cst env with
          | exception Not_found -> assert false
          | r -> r
          in
          raise (NotEvaluableConst (HasRules (u, b, r)))
        else
          raise Not_found
    with
    | Irrelevant -> Def (mk_irrelevant, [||])
    | NotEvaluableConst (IsPrimitive (_u,op)) (* Const *) -> Primitive op
    | NotEvaluableConst (HasRules (u, b, r)) -> Symbol (u, b, r)
    | Not_found (* List.assoc *)
    | NotEvaluableConst _ (* Const *) -> Undef None

  let lookup info tab ref =
    try Table.find tab.table ref with Not_found ->
    let v = value_of info ref in
    Table.add tab.table ref v; v
end

type clos_tab = Table.t

let create_tab = Table.create

(************************************************************************)

(** Hand-unrolling of the map function to bypass the call to the generic array
    allocation *)
let mk_clos_vect env v = match v with
| [||] -> [||]
| [|v0|] -> [|mk_clos env v0|]
| [|v0; v1|] -> [|mk_clos env v0; mk_clos env v1|]
| [|v0; v1; v2|] -> [|mk_clos env v0; mk_clos env v1; mk_clos env v2|]
| [|v0; v1; v2; v3|] ->
  [|mk_clos env v0; mk_clos env v1; mk_clos env v2; mk_clos env v3|]
| v -> Array.Fun1.map mk_clos env v

(* Substitution under a fixed root [e] visits a shared syntax DAG once. *)
let subst_constr e c =
  let tbl = lazy (Constr.Memo.create 17) in
  let lift_ctx (depth, e) = depth + 1, usubs_lift e in
  let rec subst_constr (depth, _ as ctx) c = Constr.Memo.visit tbl subst_rec depth ctx c
  and subst_rec (_, (subst,usubst as e) as ctx) c =
  let c = Vars.map_constr_relevance (usubst_relevance e) c in
  match [@ocaml.warning "-4"] Constr.kind c with
| App (f, args) ->
  let args = Array.Fun1.map subst_constr ctx args in
  begin match [@ocaml.warning "-4"] Constr.kind f with
  | Rel i ->
    begin match expand_rel i subst with
    | Inl (k, Inl lazy v) -> mkApp (Vars.lift_substituend k v, args)
    | Inr (m, _) -> mkApp (mkRel m, args)
    | Inl (_, Inr (nargs, term)) ->
      let subs', args = Array.chop nargs args in
      let head = Vars.substl (Array.rev_to_list subs') term in
      mkApp (head, args)
    end
  | _ -> mkApp (subst_constr ctx f, args)
  end
| Rel i ->
  begin match expand_rel i subst with
  | Inl (k, Inl lazy v) -> Vars.lift_substituend k v
  | Inl (_, Inr (nargs, term)) -> assert (Int.equal nargs 0); term
  | Inr (m, _) -> mkRel m
  end
| Const _ | Ind _ | Construct _ | Sort _ -> subst_instance_constr usubst c
| Case (ci, u, pms, p, iv, discr, br) ->
  let u' = usubst_instance e u in
  let c = if u == u' then c else mkCase (ci, u', pms, p, iv, discr, br) in
  Constr.map_with_binders lift_ctx subst_constr ctx c
| Array (u,elems,def,ty) ->
  let u' = usubst_instance e u in
  let c = if u == u' then c else mkArray (u',elems,def,ty) in
  Constr.map_with_binders lift_ctx subst_constr ctx c
| _ ->
  Constr.map_with_binders lift_ctx subst_constr ctx c
  in
  subst_constr (0, e) c

module QuotationMemo = Hashtbl.Make(struct
  type t = fconstr * Esubst.lift
  let equal (v1, l1) (v2, l2) = v1 == v2 && Esubst.eq_lift l1 l2
  let hash (v, l) = Hashtbl.hash (fconstr_hash v, l)
end)

(** The inverse of mk_clos: move back to constr
    Assuming [Γ ⊢ lfts : Δ] and [Δ ⊢ v],
    we get [Γ ⊢ to_constr lfts v]

    Crucially, in the case of [FLIFT]s which are the sole reason
    why lifts are needed here, we have the following:
    assuming [Γ ⊢ lfts : Δ, Δ'] and [Δ, Δ' ⊢ FLIFT(|Δ'|, v)] (i.e. [Δ ⊢ v])
    we get [Γ ⊢ el_shft n lfts : Δ]; so [Γ ⊢ to_constr (el_shftn n lfts) v]

    In cases like [FCLOS(t, σ)] where substitutions happen,
    we have [Γ ⊢ lfts : Δ], [Δ ⊢ σ : Ξ] and [Ξ ⊢ v]
    so we compute [Γ ⊢ comp_subs lfts σ : Ξ]
    where [comp_subs lfts σ] returns a constr substitution,
    that can be applied to [v] *)
(* A shared cell is quoted once per lift. The table is local to this call,
   since a later reduction may update the cells. *)
let to_constr lfts v =
  let tbl = lazy (QuotationMemo.create 31) in
  let rec to_constr lfts v =
    match [@ocaml.warning "-4"] v.term with
    | FRel _ | FFlex _ | FInd _ | FAtom _ | FInt _ | FFloat _ | FString _
    | FConstruct (_, [||]) -> to_constr_rec lfts v
    | FCLOS (_, (s, u)) when is_subs_id s && is_lift_id lfts &&
        UVars.Instance.is_empty u -> to_constr_rec lfts v
    | _ ->
      let tbl = Lazy.force tbl in
      match QuotationMemo.find_opt tbl (v, lfts) with
      | Some c -> c
      | None ->
        Control.check_for_interrupt ();
        let c = to_constr_rec lfts v in
        QuotationMemo.add tbl (v, lfts) c;
        c
  and to_constr_rec lfts v =
  match v.term with
    | FRel i -> mkRel (reloc_rel i lfts)
    | FFlex (RelKey p) -> mkRel (reloc_rel p lfts)
    | FFlex (VarKey x) -> mkVar x
    | FAtom c -> exliftn lfts c
    | FFlex (ConstKey op) -> mkConstU op
    | FInd op -> mkIndU op
    | FConstruct (op,args) -> mkApp (mkConstructU op, Array.Fun1.map to_constr lfts args)
    | FCaseT (ci, u, pms, p, c, ve, env) ->
      to_constr_case lfts ci u pms p NoInvert c ve env
    | FCaseInvert (ci, u, pms, p, indices, c, ve, env) ->
      let iv = CaseInvert {indices=Array.Fun1.map to_constr lfts indices} in
      to_constr_case lfts ci u pms p iv c ve env
    | FFix ((op,(lna,tys,bds)) as fx, e) ->
      if is_subs_id (fst e) && is_lift_id lfts then
        subst_instance_constr (snd e) (mkFix fx)
      else
        let n = Array.length bds in
        let subs_ty = comp_subs lfts e in
        let subs_bd = comp_subs (el_liftn n lfts) (on_fst (subs_liftn n) e) in
        let lna = Array.Fun1.map usubst_binder subs_ty lna in
        let tys = Array.Fun1.map subst_constr subs_ty tys in
        let bds = Array.Fun1.map subst_constr subs_bd bds in
        mkFix (op, (lna, tys, bds))
    | FCoFix ((op,(lna,tys,bds)) as cfx, e) ->
      if is_subs_id (fst e) && is_lift_id lfts then
        subst_instance_constr (snd e) (mkCoFix cfx)
      else
        let n = Array.length bds in
        let subs_ty = comp_subs lfts e in
        let subs_bd = comp_subs (el_liftn n lfts) (on_fst (subs_liftn n) e) in
        let lna = Array.Fun1.map usubst_binder subs_ty lna in
        let tys = Array.Fun1.map subst_constr subs_ty tys in
        let bds = Array.Fun1.map subst_constr subs_bd bds in
        mkCoFix (op, (lna, tys, bds))
    | FApp (f,ve) ->
        mkApp (to_constr lfts f,
               Array.Fun1.map to_constr lfts ve)
    | FProj (p,r,c) ->
        mkProj (p,r,to_constr lfts c)

    | FLambda (len, tys, f, e) ->
      if is_subs_id (fst e) && is_lift_id lfts then
        subst_instance_constr (snd e) (Term.compose_lam (List.rev tys) f)
      else
        let subs = comp_subs lfts e in
        let tys = List.mapi (fun i (na, c) ->
            usubst_binder subs na, subst_constr (usubs_liftn i subs) c)
            tys
        in
        let f = subst_constr (usubs_liftn len subs) f in
        Term.compose_lam (List.rev tys) f
    | FProd (n, t, c, e) ->
      if is_subs_id (fst e) && is_lift_id lfts then
        mkProd (usubst_binder e n, to_constr lfts t, subst_instance_constr (snd e) c)
      else
        let subs' = comp_subs lfts e in
        mkProd (usubst_binder subs' n,
                to_constr lfts t,
                subst_constr (usubs_lift subs') c)
    | FLetIn (n,b,t,f,e) ->
      let subs = comp_subs (el_lift lfts) (usubs_lift e) in
      mkLetIn (usubst_binder subs n,
               to_constr lfts b,
               to_constr lfts t,
               subst_constr subs f)
    | FEvar (ev, args, env, repack) ->
      let subs = comp_subs lfts env in
      repack (ev, List.map (fun a -> subst_constr subs a) args)
    | FLIFT (k,a) -> to_constr (el_shft k lfts) a

    | FInt i ->
       Constr.mkInt i
    | FFloat f ->
        Constr.mkFloat f
    | FString s ->
        Constr.mkString s

    | FArray (u,t,ty) ->
      let def = to_constr lfts (Parray.default t) in
      let t = Array.init (Parray.length_int t) (fun i ->
          to_constr lfts (Parray.get t (Uint63.of_int i)))
      in
      let ty = to_constr lfts ty in
      mkArray(u, t, def,ty)

    | FPeanoNat n ->
      let rec quote value =
        match value with
        | [] ->
          Constr.UnsafeMonomorphic.mkConstruct n.peano_zero
        | bit :: higher ->
          let doubled = mkApp
              (Constr.UnsafeMonomorphic.mkConst n.peano_double,
               [|quote higher|]) in
          if not bit then doubled
          else mkApp
              (Constr.UnsafeMonomorphic.mkConstruct n.peano_succ, [|doubled|])
      in
      quote n.peano_value

    | FCLOS (t,env) ->
      if is_subs_id (fst env) && is_lift_id lfts then
        subst_instance_constr (snd env) t
      else
        let subs = comp_subs lfts env in
        subst_constr subs t

    | FIrrelevant -> assert (!Flags.in_debugger); mkVar(Id.of_string"_IRRELEVANT_")
    | FLOCKED -> assert (!Flags.in_debugger); mkVar(Id.of_string"_LOCKED_")

and to_constr_case lfts ci u pms (p,r) iv c ve env =
  let subs = comp_subs lfts env in
  let r = usubst_relevance subs r in
  if is_subs_id (fst env) && is_lift_id lfts then
    mkCase (ci, usubst_instance subs u, pms, (p,r), iv, to_constr lfts c, ve)
  else
    let f_ctx (nas, c) =
      let nas = Array.map (usubst_binder subs) nas in
      let c = subst_constr (usubs_liftn (Array.length nas) subs) c in
      (nas, c)
    in
    mkCase (ci,
            usubst_instance subs u,
            Array.map (fun c -> subst_constr subs c) pms,
            (f_ctx p,r),
            iv,
            to_constr lfts c,
            Array.map f_ctx ve)

and lift_to_constr el = function
  | Regular c -> Inl (lazy (Vars.make_substituend @@ to_constr el c))
  | HigherOrder (n, v) -> Inr (n, to_constr el_id v)

and comp_subs el (s,u') =
  Esubst.lift_subst lift_to_constr el s, u'
  in
  to_constr lfts v

(* This function defines the correspondence between constr and
   fconstr. When we find a closure whose substitution is the identity,
   then we directly return the constr to avoid possibly huge
   reallocation. *)
let term_of_fconstr c = to_constr el_id c

let lift_union k = function
  | Regular v -> Regular (lift_fconstr k v)
  | HigherOrder (n, v) -> HigherOrder (n+k, v)

let rec resubst subs v =
  (* the saved spine would keep the old substitution *)
  let v = match v.symbolic with
    | SymbolicView _ -> make_fconstr (fconstr_mark v) v.term
    | NoSymbolicView | SymbolicCopy -> v in
  match v.term with
  | FRel i ->
    begin match clos_rel subs i with
    | Regular v -> v
    | HigherOrder _ -> CErrors.anomaly Pp.(str "Uncaught pattern variable")
    end
  | FApp (f,ve) ->
    begin match [@ocaml.warning "-4"] f.term with
    | FRel i ->
      let args = Array.Fun1.map resubst subs ve in
      begin match clos_rel subs i with
      | Regular t -> make_fconstr (fconstr_mark v) (FApp (t, args))
      | HigherOrder (nargs, term) ->
        let subs', args = Array.chop nargs args in
        let subs' = Array.fold_left (fun s v -> subs_cons (Regular v) s) (subs_id 0) subs' in
        let head = resubst subs' term in
        make_fconstr (fconstr_mark v) (FApp (head, args))
      end
    | _ ->
      make_fconstr (fconstr_mark v)
        (FApp (resubst subs f,
               Array.Fun1.map resubst subs ve))
    end
  | FCaseT (ci, u, pms, p, c, ve, env) ->
    let env = comp_subs subs env in
    make_fconstr (fconstr_mark v)
      (FCaseT (ci, u, pms, p, resubst subs c, ve, env))
  | FCaseInvert (ci, u, pms, p, indices, c, ve, env) ->
    let env = comp_subs subs env in
    let indices = Array.Fun1.map resubst subs indices in
    make_fconstr (fconstr_mark v)
      (FCaseInvert (ci, u, pms, p, indices, resubst subs c, ve, env))
  | FFix (fx, e) ->
    let e = comp_subs subs e in
    make_fconstr (fconstr_mark v) (FFix (fx, e))
  | FCoFix (cfx, e) ->
    let e = comp_subs subs e in
    make_fconstr (fconstr_mark v) (FCoFix (cfx, e))
  | FProj (p, r, c) ->
    make_fconstr (fconstr_mark v) (FProj (p, r, resubst subs c))
  | FLambda (len, tys, f, e) ->
    let e = comp_subs subs e in
    make_fconstr (fconstr_mark v) (FLambda (len, tys, f, e))
  | FProd (n, t, c, e) ->
    let e = comp_subs subs e in
    make_fconstr (fconstr_mark v) (FProd (n, resubst subs t, c, e))
  | FLetIn (n, b, t, f, e) ->
    let e = comp_subs subs e in
    make_fconstr (fconstr_mark v)
      (FLetIn (n, resubst subs b, resubst subs t, f, e))
  | FEvar (ev, args, env, repack) ->
    let env = comp_subs subs env in
    make_fconstr (fconstr_mark v) (FEvar (ev, args, env, repack))
  | FLIFT (k, a) ->
    resubst (subs_popn k subs) a

  | FArray (u, t, ty) ->
    let t = Parray.map (resubst subs) t in
    let ty = resubst subs ty in
    make_fconstr (fconstr_mark v) (FArray (u, t, ty))

  | FCLOS (t,env) ->
    let env = comp_subs subs env in
    make_fconstr (fconstr_mark v) (FCLOS (t, env))

  | FFlex (RelKey _) -> v (* outside the substitution *)
  | FFlex (ConstKey _ | VarKey _) | FInd _ | FConstruct _ | FAtom _ | FInt _ | FFloat _ | FString _ | FPeanoNat _ -> v

  | FIrrelevant -> v (* Stable under substitution and lifts *)
  | FLOCKED -> assert (!Flags.in_debugger); v

and resubst_union subs = function
  | Regular v -> Regular (resubst subs v)
  | HigherOrder _ -> assert false

and comp_subs subs s =
  on_fst (Esubst.comp resubst_union lift_union subs) s

(* fstrong applies unfreeze_fun recursively on the (freeze) term and
 * yields a term.  Assumes that the unfreeze_fun never returns a
 * FCLOS term.
let rec fstrong unfreeze_fun lfts v =
  to_constr (fstrong unfreeze_fun) lfts (unfreeze_fun v)
*)

let mkFApp h args =
  if CArray.is_empty args then h
  else match[@warning "-4"] h.term with
    | FConstruct (c, args0) ->
      let args = if CArray.is_empty args0 then args else Array.append args0 args in
      make_fconstr Cstr (FConstruct (c, args))
    | _ ->
      (* don't bother collapsing FApp nodes *)
      make_fconstr (neutr (fconstr_mark h)) (FApp (h, args))

let rec zip m stk =
  match stk with
    | [] -> m
    | Zapp args :: s -> zip (mkFApp m args) s
    | ZcaseT(ci, u, pms, p, br, e)::s ->
        let t = FCaseT(ci, u, pms, p, m, br, e) in
        let mark = neutr (fconstr_mark m) in
        zip (make_fconstr mark t) s
    | Zproj (p,r) :: s ->
        let mark = neutr (fconstr_mark m) in
        zip (make_fconstr mark (FProj (Projection.make p true, r, m))) s
    | Zfix(fx,par)::s ->
        zip fx (par @ append_stack [|m|] s)
    | Zshift(n)::s ->
        zip (lift_fconstr n m) s
    | Zupdate(rf)::s ->
      (** The stack contains [Zupdate] marks only if in sharing mode *)
        let () = update rf (fconstr_mark m) m.term in
        zip rf s
    | Zprimitive(_op,c,rargs,kargs)::s ->
      let args = List.rev_append rargs (m::List.map snd kargs) in
      let f = make_fconstr Red (FFlex (ConstKey c)) in
      (* don't need to mkFApp because not a constructor *)
      zip (make_fconstr (neutr (fconstr_mark m))
             (FApp (f, Array.of_list args))) s

let fapp_stack (m,stk) = zip m stk

let term_of_process c stk = term_of_fconstr (zip c stk)

(*********************************************************************)

(* The assertions in the functions below are granted because they are
   called only when m is a constructor, a cofix
   (strip_update_shift_app), a fix (get_nth_arg) or an abstraction
   (strip_update_shift, through get_arg). *)

(* when we don't need to return the depth & initial part of the stack,
   with only the rebuilt term sufficing
   (typically head is a fconstruct so we return a fconstruct with added args) *)
let strip_update_shift_absorb_app head stk =
  let rec strip_rec h = function
    | Zshift(k) :: s ->
        strip_rec (lift_fconstr k h) s
    | (Zapp args :: s) ->
        strip_rec (mkFApp h args) s
    | Zupdate(m)::s ->
      (** The stack contains [Zupdate] marks only if in sharing mode *)
        let () = update m (fconstr_mark h) h.term in
        strip_rec m s
    | ((ZcaseT _ | Zproj _ | Zfix _ | Zprimitive _) :: _ | []) as stk ->
      (* depth and rstk only matter for cofix *)
      (h, stk)
  in
  strip_rec head stk

(* optimised for the case where there are no shifts... *)
let strip_update_shift_app_red head stk =
  let rec strip_rec rstk h depth = function
    | Zshift(k) as e :: s ->
        strip_rec (e::rstk) (lift_fconstr k h) (depth+k) s
    | (Zapp args :: s) ->
        strip_rec (Zapp args :: rstk) (mkFApp h args) depth s
    | Zupdate(m)::s ->
      (** The stack contains [Zupdate] marks only if in sharing mode *)
        let () = update m (fconstr_mark h) h.term in
        strip_rec rstk m depth s
    | ((ZcaseT _ | Zproj _ | Zfix _ | Zprimitive _) :: _ | []) as stk ->
      (* depth and rstk only matter for cofix *)
      (depth,h,List.rev rstk, stk)
  in
  strip_rec [] head 0 stk

let strip_update_shift_app head stack =
  assert (not (is_red (fconstr_mark head)));
  strip_update_shift_app_red head stack

let get_nth_arg head n stk =
  assert (not (is_red (fconstr_mark head)));
  let rec strip_rec rstk h n = function
    | Zshift(k) as e :: s ->
        strip_rec (e::rstk) (lift_fconstr k h) n s
    | Zapp args::s' ->
        let q = Array.length args in
        if n >= q
        then
          strip_rec (Zapp args::rstk) (mkFApp h args) (n-q) s'
        else
          let bef = Array.sub args 0 n in
          let aft = Array.sub args (n+1) (q-n-1) in
          let stk' =
            List.rev (if Int.equal n 0 then rstk else (Zapp bef :: rstk)) in
          (Some (stk', args.(n)), append_stack aft s')
    | Zupdate(m)::s ->
        (** The stack contains [Zupdate] mark only if in sharing mode *)
        let () = update m (fconstr_mark h) h.term in
        strip_rec rstk m n s
    | ((ZcaseT _ | Zproj _ | Zfix _ | Zprimitive _) :: _ | []) as s -> (None, List.rev rstk @ s) in
  strip_rec [] head n stk

(* An inspection may unfold fixpoints (a family's base case can be a computed
   type), but [get_nth_arg] and [contract_fix_vect] charge nothing: check the
   vectors and pay for them and for the application prefix first. *)
let inspect_fix_interface info ((recargs, index), (names, types, bodies)) stack =
  if Inspection.active info then begin
    let count = Array.length bodies in
    Inspection.charge info count;
    if count = 0 || index < 0 || index >= count ||
       Array.length recargs <> count || Array.length names <> count ||
       Array.length types <> count then Inspection.decline info;
    Array.iter (fun arg -> if arg < 0 then Inspection.decline info) recargs;
    let rec prefix = function
      | [] -> ()
      | Zapp args :: rest ->
        Inspection.charge info 1;
        Inspection.charge info (Array.length args);
        prefix rest
      | (Zshift _ | Zupdate _) :: rest ->
        Inspection.charge info 1;
        prefix rest
      | (ZcaseT _ | Zproj _ | Zfix _ | Zprimitive _) :: _ -> ()
    in
    prefix stack
  end

let usubs_cons x (s,u) = subs_cons (Regular x) s, u

let rec subs_consn v i n s =
  if Int.equal i n then s
  else subs_consn v (i + 1) n (subs_cons (Regular v.(i)) s)

let usubs_consn v i n s = on_fst (subs_consn v i n) s

let usubs_consv v s =
  usubs_consn v 0 (Array.length v) s

(* Beta reduction: look for an applied argument in the stack.
   Since the encountered update marks are removed, h must be a whnf *)
let rec get_args n tys f e = function
    | Zupdate r :: s ->
        (** The stack contains [Zupdate] mark only if in sharing mode *)
        let () = update r Cstr (FLambda(n,tys,f,e)) in
        get_args n tys f e s
    | Zshift k :: s ->
        get_args n tys f (usubs_shft (k,e)) s
    | Zapp l :: s ->
        let na = Array.length l in
        if n == na then (Inl (usubs_consn l 0 na e), s)
        else if n < na then (* more arguments *)
          let eargs = Array.sub l n (na-n) in
          (Inl (usubs_consn l 0 n e), Zapp eargs :: s)
        else (* more lambdas *)
          let etys = List.skipn na tys in
          get_args (n-na) etys f (usubs_consn l 0 na e) s
    | ((ZcaseT _ | Zproj _ | Zfix _ | Zprimitive _) :: _ | []) as stk ->
      (Inr (make_fconstr Cstr (FLambda (n, tys, f, e))), stk)

(* Eta expansion: add a reference to implicit surrounding lambda at end of stack *)
let rec eta_expand_stack info na = function
  | (Zapp _ | Zfix _ | ZcaseT _ | Zproj _
        | Zshift _ | Zupdate _ | Zprimitive _ as e) :: s ->
      e :: eta_expand_stack info na s
  | [] ->
    let arg =
      if is_irrelevant info na.binder_relevance then mk_irrelevant
      else make_fconstr Ntrl (FRel 1)
    in
    [Zshift 1; Zapp [|arg|]]

(* Get the arguments of a native operator *)
let rec skip_native_args rargs nargs =
  match nargs with
  | (kd, a) :: nargs' ->
      if kd = CPrimitives.Kwhnf then rargs, nargs
      else skip_native_args (a::rargs) nargs'
  | [] -> rargs, []

let get_native_args op c stk =
  let kargs = CPrimitives.kind op in
  let rec get_args rnargs kargs args =
    match kargs, args with
    | kd::kargs, a::args -> get_args ((kd,a)::rnargs) kargs args
    | _, _ -> rnargs, kargs, args in
  let rec strip_rec rnargs h depth kargs = function
    | Zshift k :: s ->
      strip_rec (List.map (fun (kd,f) -> kd,lift_fconstr k f) rnargs)
        (lift_fconstr k h) (depth+k) kargs s
    | Zapp args :: s' ->
      begin match get_args rnargs kargs (Array.to_list args) with
        | rnargs, [], [] ->
          (skip_native_args [] (List.rev rnargs), s')
        | rnargs, [], eargs ->
          (skip_native_args [] (List.rev rnargs),
           Zapp (Array.of_list eargs) :: s')
        | rnargs, kargs, _ ->
          (* head of h is not constructor -> no need to mkFApp *)
          strip_rec rnargs
            (make_fconstr (fconstr_mark h) (FApp (h, args)))
            depth kargs s'
      end
    | Zupdate(m) :: s ->
      let () = update m (fconstr_mark h) h.term in
      strip_rec rnargs m depth  kargs s
    | (Zprimitive _ | ZcaseT _ | Zproj _ | Zfix _) :: _ | [] -> assert false
  in strip_rec [] (make_fconstr Red (FFlex (ConstKey c))) 0 kargs stk

let get_native_args1 op c stk =
  match get_native_args op c stk with
  | ((rargs, (kd,a):: nargs), stk) ->
      assert (kd = CPrimitives.Kwhnf);
      (rargs, a, nargs, stk)
  | _ -> assert false

let check_native_args op stk =
  let nargs = CPrimitives.arity op in
  let rargs = stack_args_size stk in
  nargs <= rargs


let try_drop_parameters n args =
  let q = Array.length args in
  if n > q then raise Not_found
  else if q = 0 then [||]
  else Array.sub args n (q - n)

let drop_parameters n args =
  try try_drop_parameters n args
  with Not_found ->
  (* we know that n < stack_args_size(argstk) (if well-typed term) *)
  anomaly (Pp.str "ill-typed term: found a match on a partially applied constructor.")

let inductive_subst mib u pms =
  let rec mk_pms i ctx = match ctx with
  | [] -> subs_id 0
  | RelDecl.LocalAssum _ :: ctx ->
    let subs = mk_pms (i - 1) ctx in
    subs_cons (Regular pms.(i)) subs
  | RelDecl.LocalDef (_, c, _) :: ctx ->
    let subs = mk_pms i ctx in
    subs_cons (Regular (mk_clos (subs,u) c)) subs
  in
  mk_pms (Array.length pms - 1) mib.mind_params_ctxt, u

let args_subst ind_subst ctx args e =
  let rec aux args_subst ind_subst i = function
    | [] ->
      assert (Int.equal (Array.length args) i);
      args_subst
    | RelDecl.LocalAssum _ :: ctx ->
      let c = args.(i) in
      aux (usubs_cons c args_subst) (usubs_cons c ind_subst) (succ i) ctx
    | RelDecl.LocalDef (_, b, _) :: ctx ->
      let c = mk_clos ind_subst b in
      aux (usubs_cons c args_subst) (usubs_cons c ind_subst) i ctx
  in
  aux e ind_subst 0 (List.rev ctx)

let esubst_of_context ctx args e =
  let rec aux lft e args ctx = match ctx with
  | [] -> lft, e
  | None :: ctx -> aux (lft + 1) (usubs_lift e) (usubs_lift args) ctx
  | Some c :: ctx ->
    let c = mk_clos args c in
    aux lft (usubs_cons c e) (usubs_cons c args) ctx
  in
  aux 0 e args (List.rev ctx)

(* Iota-reduction: feed the arguments of the constructor to the branch *)
let get_branch infos ci pms ((ind, c), u) args br e =
  let i = c - 1 in
  (* An inspected constructor need not be well typed: check the case
     boundary before indexing and pay for the substitution first. *)
  let () = if Inspection.active infos then begin
      if not (Environ.QInd.equal (info_env infos) ind ci.ci_ind) ||
         Array.length br <> Array.length ci.ci_cstr_ndecls ||
         Array.length br <> Array.length ci.ci_cstr_nargs ||
         i < 0 || i >= Array.length br ||
         ci.ci_npar < 0 then
        Inspection.decline infos;
      let ndecls = ci.ci_cstr_ndecls.(i) in
      let nargs = ci.ci_cstr_nargs.(i) in
      if nargs < 0 || ndecls < nargs ||
         Array.length pms <> ci.ci_npar ||
         ci.ci_npar > Array.length args ||
         Array.length args - ci.ci_npar <> nargs ||
         Array.length (fst br.(i)) <> ndecls then
        Inspection.decline infos;
      Inspection.charge infos (Array.length args);
      Inspection.charge infos ndecls;
      if ndecls <> nargs then begin
        (* parameter lets enter the substitution too *)
        let mib = Environ.lookup_mind (fst ind) (info_env infos) in
        List.iter (fun _ -> Inspection.charge infos 1) mib.Declarations.mind_params_ctxt
      end
    end
  in
  let args = drop_parameters ci.ci_npar args in
  let (_nas, br) = br.(i) in
  if Int.equal ci.ci_cstr_ndecls.(i) ci.ci_cstr_nargs.(i) then
    (* No let-bindings in the constructor, we don't have to fetch the
      environment to know the value of the branch. *)
    let e = usubs_consv args e in
    (br, e)
  else
    (* The constructor contains let-bindings, but they are not physically
        present in the match, so we fetch them in the environment. *)
    let env = info_env infos in
    let mib = Environ.lookup_mind (fst ind) env in
    let mip = mib.mind_packets.(snd ind) in
    let (ctx, _) = mip.mind_nf_lc.(i) in
    let ctx, _ = List.chop mip.mind_consnrealdecls.(i) ctx in
    let ind_subst = inductive_subst mib u (Array.map (mk_clos e) pms) in
    let e = args_subst ind_subst ctx args e in
    (br, e)

(** [eta_expand_ind_stack env ind args t] computes stacks corresponding
    to the conversion of the eta expansion of t, considered as an inhabitant
    of ind, and the constructor of this inductive type applied to arguments args.
    @assumes [t] is a rigid term, and not a constructor;
    that [args] are valid arguments for the constructor of inductive [ind].
    @raise Not_found if the inductive is not a primitive record, or if the
    constructor is partially applied.
 *)
let eta_expand_ind_stack env (ind,u) args m' =
  let open Declarations in
  let mib = lookup_mind (fst ind) env in
  let specif = mib, mib.mind_packets.(snd ind) in
  (* disallow eta-exp for non-primitive records, also check postponed eta *)
  let () = if not (Declareops.is_record_with_eta specif u) then
    raise Not_found
  in
  match Declareops.inductive_make_projections ind mib with
  | None -> assert false
  | Some projs ->
    (* (Construct, pars1 .. parsm :: arg1...argn :: []) ~= m' ->
           arg1..argn ~= (proj1 t...projn t) where t = zip m' *)
    let pars = mib.Declarations.mind_nparams in
    let right = fapp_stack m' in
    (** Try to drop the params, might fail on partially applied constructors. *)
    let argss = try_drop_parameters pars args in
    let () = if not @@ Int.equal (Array.length projs) (Array.length argss)
      then raise Not_found (* partially applied constructor (missing non-param arguments) *)
    in
    let hstack = Array.map (fun (p,r) ->
        make_fconstr Red (* right can't be a constructor though *)
          (FProj (Projection.make p true,
             UVars.subst_instance_relevance u r, right)))
        projs
    in
    [Zapp argss], [Zapp hstack]

(* Iota reduction: expansion of a fixpoint.
 * Given a fixpoint and a substitution, returns the corresponding
 * fixpoint body, and the substitution in which it should be
 * evaluated: its first variables are the fixpoint bodies
 *
 * FCLOS(fix Fi {F0 := T0 .. Fn-1 := Tn-1}, S)
 *    -> (S. FCLOS(F0,S) . ... . FCLOS(Fn-1,S), Ti)
 *)
(* does not deal with FLIFT *)
let contract_fix_vect fix =
  let (thisbody, make_body, env, nfix) =
    match [@ocaml.warning "-4"] fix with
      | FFix (((reci,i),(_,_,bds as rdcl)),env) ->
          (bds.(i),
           (fun j -> make_fconstr Cstr (FFix (((reci, j), rdcl), env))),
           env, Array.length bds)
      | FCoFix ((i,(_,_,bds as rdcl)),env) ->
          (bds.(i),
           (fun j -> make_fconstr Cstr (FCoFix ((j, rdcl), env))),
           env, Array.length bds)
      | _ -> assert false
  in
  let rec mk_subs env i =
    if Int.equal i nfix then env
    else mk_subs (subs_cons (Regular (make_body i)) env) (i + 1)
  in
  (on_fst (fun env -> mk_subs env 0) env, thisbody)

let unfold_projection info p r =
  if red_projection info.i_flags p
  then
    Some (Zproj (Projection.repr p, r))
  else None

(************************************************************************)
(* Reduction of Native operators                                        *)

open Primred

module FNativeEntries =
  struct
    type elem = fconstr
    type args = fconstr array
    type evd = unit
    type uinstance = UVars.Instance.t

    let mk_construct c =
      (* All constructors used in primitive functions are relevant *)
      make_fconstr Cstr (FConstruct (UVars.in_punivs c, [||]))

    let get = Array.get

    let get_int () e =
      match [@ocaml.warning "-4"] e.term with
      | FInt i -> i
      | _ -> assert false

    let get_float () e =
      match [@ocaml.warning "-4"] e.term with
      | FFloat f -> f
      | _ -> assert false

    let get_string () e =
      match [@ocaml.warning "-4"] e.term with
      | FString s -> s
      | _ -> assert false

    let get_parray () e =
      match [@ocaml.warning "-4"] e.term with
      | FArray (_u,t,_ty) -> t
      | _ -> assert false

    let dummy = make_fconstr Ntrl (FRel 0)

    let current_retro = ref Retroknowledge.empty
    let defined_int = ref false
    let fint = ref dummy

    let init_int retro =
      match retro.Retroknowledge.retro_int63 with
      | Some c ->
        defined_int := true;
        fint := make_fconstr Ntrl (FFlex (ConstKey (UVars.in_punivs c)))
      | None -> defined_int := false

    let defined_float = ref false
    let ffloat = ref dummy

    let init_float retro =
      match retro.Retroknowledge.retro_float64 with
      | Some c ->
        defined_float := true;
        ffloat := make_fconstr Ntrl (FFlex (ConstKey (UVars.in_punivs c)))
      | None -> defined_float := false

    let defined_string = ref false
    let fstring = ref dummy

    let init_string retro =
      match retro.Retroknowledge.retro_string with
      | Some c ->
        defined_string := true;
        fstring := make_fconstr Ntrl (FFlex (ConstKey (UVars.in_punivs c)))
      | None -> defined_string := false

    let defined_bool = ref false
    let ftrue = ref dummy
    let ffalse = ref dummy

    let init_bool retro =
      match retro.Retroknowledge.retro_bool with
      | Some (ct,cf) ->
        defined_bool := true;
        ftrue := mk_construct ct;
        ffalse := mk_construct cf;
      | None -> defined_bool :=false

    let defined_carry = ref false
    let fC0 = ref dummy
    let fC1 = ref dummy

    let init_carry retro =
      match retro.Retroknowledge.retro_carry with
      | Some(c0,c1) ->
        defined_carry := true;
        fC0 := mk_construct c0;
        fC1 := mk_construct c1;
      | None -> defined_carry := false

    let defined_pair = ref false
    let fPair = ref dummy

    let init_pair retro =
      match retro.Retroknowledge.retro_pair with
      | Some c ->
        defined_pair := true;
        fPair := mk_construct c;
      | None -> defined_pair := false

    let defined_cmp = ref false
    let fEq = ref dummy
    let fLt = ref dummy
    let fGt = ref dummy
    let fcmp = ref dummy

    let init_cmp retro =
      match retro.Retroknowledge.retro_cmp with
      | Some (cEq, cLt, cGt) ->
        defined_cmp := true;
        fEq := mk_construct cEq;
        fLt := mk_construct cLt;
        fGt := mk_construct cGt;
        let (icmp, _) = cEq in
        fcmp := make_fconstr Ntrl (FInd (UVars.in_punivs icmp))
      | None -> defined_cmp := false

    let defined_f_cmp = ref false
    let fFEq = ref dummy
    let fFLt = ref dummy
    let fFGt = ref dummy
    let fFNotComparable = ref dummy

    let init_f_cmp retro =
      match retro.Retroknowledge.retro_f_cmp with
      | Some (cFEq, cFLt, cFGt, cFNotComparable) ->
        defined_f_cmp := true;
        fFEq := mk_construct cFEq;
        fFLt := mk_construct cFLt;
        fFGt := mk_construct cFGt;
        fFNotComparable := mk_construct cFNotComparable;
      | None -> defined_f_cmp := false

    let defined_f_class = ref false
    let fPNormal = ref dummy
    let fNNormal = ref dummy
    let fPSubn = ref dummy
    let fNSubn = ref dummy
    let fPZero = ref dummy
    let fNZero = ref dummy
    let fPInf = ref dummy
    let fNInf = ref dummy
    let fNaN = ref dummy

    let init_f_class retro =
      match retro.Retroknowledge.retro_f_class with
      | Some (cPNormal, cNNormal, cPSubn, cNSubn, cPZero, cNZero,
              cPInf, cNInf, cNaN) ->
        defined_f_class := true;
        fPNormal := mk_construct cPNormal;
        fNNormal := mk_construct cNNormal;
        fPSubn := mk_construct cPSubn;
        fNSubn := mk_construct cNSubn;
        fPZero := mk_construct cPZero;
        fNZero := mk_construct cNZero;
        fPInf := mk_construct cPInf;
        fNInf := mk_construct cNInf;
        fNaN := mk_construct cNaN;
      | None -> defined_f_class := false

    let defined_array = ref false

    let init_array retro =
      defined_array := Option.has_some retro.Retroknowledge.retro_array

    let init env =
      current_retro := Environ.retroknowledge env;
      init_int !current_retro;
      init_float !current_retro;
      init_string !current_retro;
      init_bool !current_retro;
      init_carry !current_retro;
      init_pair !current_retro;
      init_cmp !current_retro;
      init_f_cmp !current_retro;
      init_f_class !current_retro;
      init_array !current_retro

    let check_env env =
      if not (!current_retro == Environ.retroknowledge env) then init env

    let check_int env =
      check_env env;
      assert (!defined_int)

    let check_float env =
      check_env env;
      assert (!defined_float)

    let check_string env =
      check_env env;
      assert (!defined_string)

    let check_bool env =
      check_env env;
      assert (!defined_bool)

    let check_carry env =
      check_env env;
      assert (!defined_carry && !defined_int)

    let check_pair env =
      check_env env;
      assert (!defined_pair && !defined_int)

    let check_cmp env =
      check_env env;
      assert (!defined_cmp)

    let check_f_cmp env =
      check_env env;
      assert (!defined_f_cmp)

    let check_f_class env =
      check_env env;
      assert (!defined_f_class)

    let check_array env =
      check_env env;
      assert (!defined_array)

    let mkInt env i =
      check_int env;
      make_fconstr Cstr (FInt i)

    let mkFloat env f =
      check_float env;
      make_fconstr Cstr (FFloat f)

    let mkString env s =
      check_string env;
      make_fconstr Cstr (FString s)

    let mkBool env b =
      check_bool env;
      if b then !ftrue else !ffalse

    let mkCarry env b e =
      check_carry env;
      mkFApp (if b then !fC1 else !fC0) [|!fint;e|]

    let mkIntPair env e1 e2 =
      check_pair env;
      mkFApp !fPair [|!fint;!fint;e1;e2|]

    let mkFloatIntPair env f i =
      check_pair env;
      check_float env;
      mkFApp !fPair [|!ffloat;!fint;f;i|]

    let mkLt env =
      check_cmp env;
      !fLt

    let mkEq env =
      check_cmp env;
      !fEq

    let mkGt env =
      check_cmp env;
      !fGt

    let mkFLt env =
      check_f_cmp env;
      !fFLt

    let mkFEq env =
      check_f_cmp env;
      !fFEq

    let mkFGt env =
      check_f_cmp env;
      !fFGt

    let mkFNotComparable env =
      check_f_cmp env;
      !fFNotComparable

    let mkPNormal env =
      check_f_class env;
      !fPNormal

    let mkNNormal env =
      check_f_class env;
      !fNNormal

    let mkPSubn env =
      check_f_class env;
      !fPSubn

    let mkNSubn env =
      check_f_class env;
      !fNSubn

    let mkPZero env =
      check_f_class env;
      !fPZero

    let mkNZero env =
      check_f_class env;
      !fNZero

    let mkPInf env =
      check_f_class env;
      !fPInf

    let mkNInf env =
      check_f_class env;
      !fNInf

    let mkNaN env =
      check_f_class env;
      !fNaN

    let mkArray env u t ty =
      check_array env;
      make_fconstr Cstr (FArray (u, t, ty))

  end

module FredNative = RedNative(FNativeEntries)

(** Compact Peano naturals: a registered operation applied to compact values
    computes on the values instead of unfolding. *)

let peano_schemes info =
  (Environ.retroknowledge (info_env info)).Retroknowledge.retro_peano_nat

let compact_peano_of_scheme scheme peano_value =
  Option.map (fun peano_double ->
      { peano_ind = scheme.Retroknowledge.peano_inductive;
        peano_zero = scheme.peano_zero; peano_succ = scheme.peano_succ;
        peano_double; peano_value }) scheme.peano_double

let same_peano_scheme a b = Ind.UserOrd.equal a.peano_ind b.peano_ind
let peano_set_value n peano_value = { n with peano_value }
let peano_value n = make_fconstr Cstr (FPeanoNat n)

let compact_peano_zero info c =
  List.find_map (fun scheme ->
      if Construct.UserOrd.equal c scheme.Retroknowledge.peano_zero
      then compact_peano_of_scheme scheme PeanoNatValue.zero else None)
    (peano_schemes info)

type compact_peano_binary_operation = PeanoAdd | PeanoMul | PeanoPow | PeanoSub

let compact_peano_binary_operation info c =
  let is = function Some c' -> Constant.UserOrd.equal c c' | None -> false in
  List.find_map (fun scheme ->
      if is scheme.Retroknowledge.peano_add then Some (scheme, PeanoAdd)
      else if is scheme.peano_mul then Some (scheme, PeanoMul)
      else if is scheme.peano_pow then Some (scheme, PeanoPow)
      else if is scheme.peano_sub then Some (scheme, PeanoSub)
      else None)
    (peano_schemes info)

type compact_peano_fueled_operation = PeanoDivGo | PeanoModGo

let compact_peano_fueled_operation info c =
  let mem = List.exists (Constant.UserOrd.equal c) in
  List.find_map (fun scheme ->
      if mem scheme.Retroknowledge.peano_div_go then Some (scheme, PeanoDivGo)
      else if mem scheme.peano_mod_go then Some (scheme, PeanoModGo)
      else None)
    (peano_schemes info)

let compact_peano_bool_operation info c =
  let retro = Environ.retroknowledge (info_env info) in
  let find entries compare =
    Option.map (fun op ->
        op.Retroknowledge.bool_op_inductive, op.bool_op_false, op.bool_op_true, compare)
      (List.find_opt (fun op -> Constant.UserOrd.equal c op.Retroknowledge.bool_op_constant)
        entries)
  in
  match find retro.Retroknowledge.retro_peano_nat_beq PeanoNatValue.equal with
  | Some _ as operation -> operation
  | None -> find retro.Retroknowledge.retro_peano_nat_ble PeanoNatValue.le

(* [t] as an applied constructor of [ind] at the empty instance, looking
   through closures and lifts *)
let rec constructor_app ind t =
  match [@ocaml.warning "-4"] t.term with
  | FCLOS (t, e) -> constructor_app_constr ind e t
  | FLIFT (_, t) -> constructor_app ind t
  | FConstruct (((ind', i), u), args)
    when Ind.UserOrd.equal ind ind' && UVars.Instance.is_empty u -> Some (i, args)
  | FApp (head, args) ->
    begin match [@ocaml.warning "-4"] head.term with
    | FConstruct (c, [||]) -> constructor_app ind (make_fconstr Red (FConstruct (c, args)))
    | _ -> None
    end
  | _ -> None

and constructor_app_constr ind e t =
  match [@ocaml.warning "-4"] kind t with
  | Rel n ->
    begin match clos_rel (fst e) n with
    | Regular v -> constructor_app ind v
    | HigherOrder _ -> None
    end
  | Cast (t, _, _) -> constructor_app_constr ind e t
  | Construct (c, u) ->
    constructor_app ind (make_fconstr Cstr (FConstruct ((c, usubst_instance e u), [||])))
  | App (head, args) ->
    constructor_app ind (make_fconstr Red (FApp (mk_clos e head, mk_clos_vect e args)))
  | _ -> None

(* binary numerals [positive = xI p | xO p | xH] and [N = N0 | Npos p] *)
let rec compact_positive pos_ind t = match constructor_app pos_ind t with
  | Some (1, [|p|]) -> Option.map (fun v -> true :: v) (compact_positive pos_ind p)
  | Some (2, [|p|]) -> Option.map (fun v -> false :: v) (compact_positive pos_ind p)
  | Some (3, [||]) -> Some PeanoNatValue.one
  | _ -> None

let compact_N n_ind pos_ind t = match constructor_app n_ind t with
  | Some (1, [||]) -> Some PeanoNatValue.zero
  | Some (2, [|p|]) -> compact_positive pos_ind p
  | _ -> None

let compact_peano_may_unfold info c =
  TransparentState.is_transparent_constant (RedFlags.red_transparent info.i_flags) c &&
  match info.i_cache.i_mode with
  | Conversion -> true
  | Reduction -> red_set info.i_flags fDELTA

(* [c] is [fun x : D => match x with zero => zero | succ p => p] *)
let compact_peano_is_predecessor info n c =
  try
    let body = Environ.constant_value_in (info_env info) (c, UVars.Instance.empty) in
    match [@ocaml.warning "-4"] Constr.kind body with
    | Lambda (_, domain, body) ->
      begin match [@ocaml.warning "-4"] Constr.kind domain, Constr.kind body with
      | Ind (ind, u),
        Case (ci, case_u, [||], _, NoInvert, scrutinee,
              [|zero_binders, zero_body; succ_binders, succ_body|])
        when Ind.UserOrd.equal ind n.peano_ind && UVars.Instance.is_empty u &&
             Ind.UserOrd.equal ci.ci_ind n.peano_ind && UVars.Instance.is_empty case_u &&
             Int.equal ci.ci_npar 0 ->
        begin match [@ocaml.warning "-4"] Constr.kind scrutinee,
                    Constr.kind zero_body, Constr.kind succ_body with
        | Rel 1, Construct (zero, zero_u), Rel 1 ->
          Array.is_empty zero_binders && Int.equal (Array.length succ_binders) 1 &&
          Construct.UserOrd.equal zero n.peano_zero && UVars.Instance.is_empty zero_u
        | _ -> false
        end
      | _ -> false
      end
    | _ -> false
  with Environ.NotEvaluableConst _ -> false

let compact_peano_binary_values (scheme, operation) left right =
  if not (Ind.UserOrd.equal left.peano_ind scheme.Retroknowledge.peano_inductive &&
          same_peano_scheme left right)
  then None
  else
    let value = match operation with
      | PeanoAdd -> Some (PeanoNatValue.add left.peano_value right.peano_value)
      | PeanoMul -> Some (PeanoNatValue.mul left.peano_value right.peano_value)
      | PeanoPow -> PeanoNatValue.pow left.peano_value right.peano_value
      | PeanoSub -> Some (PeanoNatValue.sub left.peano_value right.peano_value)
    in
    Option.map (peano_set_value left) value

(* the workers are recognised only below their fuel *)
let compact_peano_fueled_values (scheme, operation) divisor fuel dividend =
  if not (Ind.UserOrd.equal divisor.peano_ind scheme.Retroknowledge.peano_inductive &&
          same_peano_scheme divisor fuel && same_peano_scheme divisor dividend) ||
     PeanoNatValue.is_zero divisor.peano_value ||
     PeanoNatValue.compare dividend.peano_value fuel.peano_value >= 0
  then None
  else
    let q, r = PeanoNatValue.div_mod dividend.peano_value divisor.peano_value in
    Some (peano_set_value dividend (match operation with PeanoDivGo -> q | PeanoModGo -> r))

let compact_peano_bool_values (ind, false_ctor, true_ctor, compare) left right =
  if not (Ind.UserOrd.equal ind left.peano_ind && same_peano_scheme left right) then None
  else
    let ctor = if compare left.peano_value right.peano_value then true_ctor else false_ctor in
    Some (make_fconstr Cstr (FConstruct ((ctor, UVars.Instance.empty), [||])))

(* [t] as a compact value, when it is a numeral or a registered operation
   applied to compact values *)
let rec compact_peano_of_fconstr info t =
  match [@ocaml.warning "-4"] t.term with
  | FPeanoNat n -> Some n
  | FCLOS (t, e) -> compact_peano_of_constr info e t
  | FLIFT (_, t) -> compact_peano_of_fconstr info t
  | FConstruct ((c, u), [||]) when UVars.Instance.is_empty u -> compact_peano_zero info c
  | FConstruct ((c, u), [|arg|]) when UVars.Instance.is_empty u ->
    begin match [@ocaml.warning "-4"] arg.term with
    | FPeanoNat n when Construct.UserOrd.equal c n.peano_succ ->
      Some (peano_set_value n (PeanoNatValue.succ n.peano_value))
    | _ -> None
    end
  | FApp (head, args) ->
    begin match [@ocaml.warning "-4"] head.term, args with
    | FFlex (ConstKey (c, u)), [|divisor; _; fuel; dividend; _|]
      when UVars.Instance.is_empty u && compact_peano_may_unfold info c ->
      compact_peano_fueled info c divisor fuel dividend
    | FFlex (ConstKey (c, u)), [|left; right|]
      when UVars.Instance.is_empty u && compact_peano_may_unfold info c ->
      compact_peano_binary info c left right
    | FFlex (ConstKey (c, u)), [|arg|]
      when UVars.Instance.is_empty u && compact_peano_may_unfold info c ->
      compact_peano_unary info c arg
    | FConstruct (c, [||]), [|_|] ->
      compact_peano_of_fconstr info (make_fconstr Red (FConstruct (c, args)))
    | _ -> None
    end
  | _ -> None

and compact_peano_of_constr info e t =
  match [@ocaml.warning "-4"] kind t with
  | Rel n ->
    begin match clos_rel (fst e) n with
    | Regular v -> compact_peano_of_fconstr info v
    | HigherOrder _ -> None
    end
  | Cast (t, _, _) -> compact_peano_of_constr info e t
  | Construct (c, u) when UVars.Instance.is_empty (usubst_instance e u) ->
    compact_peano_zero info c
  | App (head, args) ->
    begin match [@ocaml.warning "-4"] kind head, args with
    | Const (c, u), [|divisor; _; fuel; dividend; _|]
      when UVars.Instance.is_empty (usubst_instance e u) &&
           Option.has_some (compact_peano_fueled_operation info c) &&
           compact_peano_may_unfold info c ->
      compact_peano_fueled info c (mk_clos e divisor) (mk_clos e fuel) (mk_clos e dividend)
    | Const (c, u), [|left; right|]
      when UVars.Instance.is_empty (usubst_instance e u) &&
           Option.has_some (compact_peano_binary_operation info c) &&
           compact_peano_may_unfold info c ->
      compact_peano_binary info c (mk_clos e left) (mk_clos e right)
    | Const (c, u), [|arg|]
      when UVars.Instance.is_empty (usubst_instance e u) && compact_peano_may_unfold info c ->
      compact_peano_unary info c (mk_clos e arg)
    | Construct (c, u), [|arg|] when UVars.Instance.is_empty (usubst_instance e u) ->
      List.find_map (fun scheme ->
          if Construct.UserOrd.equal c scheme.Retroknowledge.peano_succ then
            Option.map (fun n -> peano_set_value n (PeanoNatValue.succ n.peano_value))
              (compact_peano_of_constr info e arg)
          else None)
        (peano_schemes info)
    | _ -> None
    end
  | _ -> None

(* doubling builder, predecessor or binary decoder *)
and compact_peano_unary info c arg =
  match compact_peano_of_fconstr info arg with
  | Some n when Constant.UserOrd.equal c n.peano_double ->
    Some (peano_set_value n (PeanoNatValue.double n.peano_value))
  | Some n ->
    if compact_peano_is_predecessor info n c then
      Some (peano_set_value n
        (Option.default PeanoNatValue.zero (PeanoNatValue.pred n.peano_value)))
    else None
  | None ->
    List.find_map (fun scheme ->
        List.find_map (fun d ->
            if Constant.UserOrd.equal c d.Retroknowledge.decoder_constant then
              Option.bind (compact_N d.binary_nat d.binary_positive arg)
                (compact_peano_of_scheme scheme)
            else None)
          scheme.Retroknowledge.peano_decoders)
      (peano_schemes info)

and compact_peano_binary info c left right =
  Option.bind (compact_peano_binary_operation info c) (fun op ->
    Option.bind (compact_peano_of_fconstr info left) (fun left ->
      Option.bind (compact_peano_of_fconstr info right) (fun right ->
        compact_peano_binary_values op left right)))

and compact_peano_fueled info c divisor fuel dividend =
  Option.bind (compact_peano_fueled_operation info c) (fun op ->
    Option.bind (compact_peano_of_fconstr info divisor) (fun divisor ->
      Option.bind (compact_peano_of_fconstr info fuel) (fun fuel ->
        Option.bind (compact_peano_of_fconstr info dividend) (fun dividend ->
          compact_peano_fueled_values op divisor fuel dividend))))

(* The registered Boolean test whose fixpoint is [fx]. Its syntax identifies
   it: the closure may bind irrelevant arguments that cannot be quoted. *)
let compact_peano_bool_fix info fx =
  match [@ocaml.warning "-4"] fterm_of fx with
  | FFix (fixpoint, _) ->
    let env = info_env info in
    let body = Constr.mkFix fixpoint in
    let registered op =
      try Constr.equal body (Environ.constant_value_in env
            (op.Retroknowledge.bool_op_constant, UVars.Instance.empty))
      with Environ.NotEvaluableConst _ -> false
    in
    let retro = Environ.retroknowledge env in
    let find entries =
      Option.map (fun op -> op.Retroknowledge.bool_op_constant) (List.find_opt registered entries)
    in
    let c = match find retro.Retroknowledge.retro_peano_nat_beq with
      | Some _ as c -> c
      | None -> find retro.Retroknowledge.retro_peano_nat_ble
    in
    Option.bind c (compact_peano_bool_operation info)
  | _ -> None

(* The arguments applied to a head on [stk], and how to rebuild the stack
   around the arguments left. Only closed results commute with the shifts. An
   update frame before the arguments belongs to the unapplied function and is
   left to ordinary reduction. *)
let rec compact_peano_application_stack = function
  | (Zshift _ as frame) :: rest ->
    Option.map (fun (args, rebuild) -> args, fun remaining -> frame :: rebuild remaining)
      (compact_peano_application_stack rest)
  | Zapp args :: rest -> Some (args, fun remaining -> append_stack remaining rest)
  | (Zupdate _ | ZcaseT _ | Zproj _ | Zfix _ | Zprimitive _) :: _ | [] -> None

(* The value of the registered operation [c] applied on [stk], with the rest
   of the stack. An argument that is not compact is reduced with [whd], with
   every constant transparent, and repackaged if it is a unary numeral. *)
let compact_peano_unfold info ~whd c stk =
  match compact_peano_application_stack stk with
  | None -> None
  | Some (args, rebuild) ->
    let nargs = Array.length args in
    let whd = lazy (whd { info with i_flags =
      RedFlags.(red_add_transparent all (red_transparent info.i_flags)) }) in
    let rec reduced arg =
      Control.check_for_interrupt ();
      let arg = Lazy.force whd arg in
      match compact_peano_of_fconstr info arg with
      | Some n -> Some n
      | None ->
        match [@ocaml.warning "-4"] arg.term with
        | FConstruct ((succ, u), [|pred|]) when UVars.Instance.is_empty u ->
          Option.bind (reduced pred) (fun n ->
            if Construct.UserOrd.equal succ n.peano_succ
            then Some (peano_set_value n (PeanoNatValue.succ n.peano_value)) else None)
        | _ -> None
    in
    let compact = compact_peano_of_fconstr info in
    let both f a b = Option.bind (f a) (fun a -> Option.bind (f b) (fun b -> Some (a, b))) in
    let nat = match compact_peano_fueled_operation info c with
      | Some op ->
        if nargs < 5 then None else
        let compute d f x = Option.map (fun n -> peano_value n, 5)
          (compact_peano_fueled_values op d f x) in
        begin match compact args.(0), compact args.(2), compact args.(3) with
        | Some d, Some f, Some x -> compute d f x
        | _ ->
          match reduced args.(0), reduced args.(2), reduced args.(3) with
          | Some d, Some f, Some x -> compute d f x
          | _ -> None
        end
      | None ->
        match compact_peano_binary_operation info c with
        | Some op when nargs >= 2 ->
          let compute (l, r) = Option.map (fun n -> peano_value n, 2)
            (compact_peano_binary_values op l r) in
          begin match both compact args.(0) args.(1) with
          | Some values -> compute values
          | None ->
            match snd op with
            | PeanoSub ->
              begin match reduced args.(1) with
              | Some r when not (PeanoNatValue.is_zero r.peano_value) ->
                Option.bind (reduced args.(0)) (fun l -> compute (l, r))
              | _ -> None
              end
            | PeanoAdd | PeanoMul | PeanoPow ->
              Option.bind (both reduced args.(0) args.(1)) compute
          end
        | _ -> None
    in
    let unary () =
      if nargs < 1 then None
      else Option.map (fun n -> peano_value n, 1) (compact_peano_unary info c args.(0))
    in
    let bool () = match compact_peano_bool_operation info c with
      | Some op when nargs >= 2 ->
        let compute (l, r) = Option.map (fun m -> m, 2) (compact_peano_bool_values op l r) in
        begin match both compact args.(0) args.(1) with
        | Some values -> compute values
        | None -> Option.bind (both reduced args.(0) args.(1)) compute
        end
      | _ -> None
    in
    let result = match nat with
      | Some _ -> nat
      | None -> match unary () with Some _ as r -> r | None -> bool ()
    in
    Option.map (fun (m, k) -> m, rebuild (Array.sub args k (nargs - k))) result

let rec skip_irrelevant_stack info stk = match stk with
| [] -> []
| (Zshift _ | Zapp _) :: s -> skip_irrelevant_stack info s
| (Zfix _ | Zproj _) :: s ->
  (* Typing rules ensure that fix / proj over SProp is irrelevant *)
  skip_irrelevant_stack info s
| ZcaseT (_, _, _, (_,r), _, e) :: s ->
  let r = usubst_relevance e r in
  if is_irrelevant info r then skip_irrelevant_stack info s
  else stk
| Zprimitive _ :: _ -> assert false (* no irrelevant primitives so far *)
| Zupdate m :: s ->
  (** The stack contains [Zupdate] marks only if in sharing mode *)
  let () = update m (fconstr_mark mk_irrelevant) mk_irrelevant.term in
  skip_irrelevant_stack info s

let is_irrelevant_constructor infos ((ind,_),u) =
  is_irrelevant infos @@ UVars.subst_instance_relevance u @@ ind_relevance ind (info_env infos)

(*********************************************************************)
(* A machine that inspects the head of a term until it finds an
   atom or a subterm that may produce a redex (abstraction,
   constructor, cofix, letin, constant), or a neutral term (product,
   inductive) *)
let rec knh info m stk =
  Inspection.charge info 1;
  (* a private view owns every cell the reducer visits, so updates go there *)
  let m = match info.i_private with None -> m | Some own -> own m in
  let m = match m.symbolic with
    | SymbolicView view when symbolic_reduction info -> view
    | SymbolicView _ | NoSymbolicView | SymbolicCopy -> m in
  let () = match [@ocaml.warning "-4"] m.term with
    | FCoFix _ | FCaseInvert _ | FEvar _ | FArray _
    | FPeanoNat _ -> Inspection.decline info
    | FApp (_, args) | FConstruct (_, args) ->
      Inspection.charge info (Array.length args)
    | _ -> ()
  in
  match m.term with
    | FLIFT(k,a) -> knh info a (zshift k stk)
    | FCLOS(t,e) when m.symbolic == SymbolicCopy ->
      (* a saved spine is instantiated once; its arguments are ordinary
         shared cells with their own views *)
      let exposed = match [@ocaml.warning "-4"] kind t with
        | App (f, args) -> begin match [@ocaml.warning "-4"] kind f with
          | Rel n -> begin match clos_rel (fst e) n with
            | Regular f -> Some (FApp (f, mk_clos_vect e args))
            | HigherOrder _ -> None end
          | _ -> Some (FApp (mk_clos e f, mk_clos_vect e args)) end
        | Proj (p, r, c) -> Some (FProj (p, usubst_relevance e r, mk_clos e c))
        | _ -> None
      in
      begin match exposed with
      | Some term -> update m Red term; knh info m stk
      | None -> knht info e t stk
      end
    | FCLOS(t,e) -> knht info e t (zupdate info m stk)
    | FLOCKED -> Inspection.decline info; assert false
    | FApp(a,b) -> knh info a (append_stack b (zupdate info m stk))
    | FCaseT(ci,u,pms,(_,r as p),t,br,e) ->
      let r' = usubst_relevance e r in
      if is_irrelevant info r' then
        (mk_irrelevant, skip_irrelevant_stack info stk)
      else
        knh info t (ZcaseT(ci,u,pms,p,br,e)::zupdate info m stk)
    | FFix (((ri, n), (lna, _, _) as fix), e) ->
      inspect_fix_interface info fix stk;
      if is_irrelevant info (usubst_relevance e (lna.(n)).binder_relevance) then
        (mk_irrelevant, skip_irrelevant_stack info stk)
      else
        (match get_nth_arg m ri.(n) stk with
             (Some(pars,arg),stk') -> knh info arg (Zfix(m,pars)::stk')
           | (None, stk') -> (m,stk'))
    | FProj (p,r,c) ->
      if is_irrelevant info r then
        (mk_irrelevant, skip_irrelevant_stack info stk)
      else
      (match unfold_projection info p r with
       | None -> (m, stk)
       | Some s -> knh info c (s :: zupdate info m stk))
    | FPeanoNat n when not (Int.equal (stack_args_size stk) 0) ->
      (* a compact value is saturated: expose a constructor to absorb the arguments *)
      knh info (peano_constructor_view n) stk
    | FConstruct _ | FPeanoNat _ -> strip_update_shift_absorb_app m stk

(* cases where knh stops *)
    | (FFlex _|FLetIn _|FEvar _|FCaseInvert _|FIrrelevant|
       FCoFix _|FLambda _|FRel _|FAtom _|FInd _|FProd _|FInt _|FFloat _|
       FString _|FArray _) ->
        (m, stk)

(* The same for pure terms *)
and knht info e t stk =
  Inspection.charge info 1;
  let () = match [@ocaml.warning "-4"] kind t with
    | CoFix _ | Case (_, _, _, _, CaseInvert _, _, _)
    | Evar _ | Array _ -> Inspection.decline info
    | App (_, args) -> Inspection.charge info (Array.length args)
    | _ -> ()
  in
  match (if Inspection.active info then None else compact_peano_of_constr info e t) with
  | Some n ->
    knh info (make_fconstr Cstr (FPeanoNat n)) stk
  | None -> match kind t with
  | Rel n ->
    begin match clos_rel (fst e) n with
    | Regular v -> knh info v stk
    | HigherOrder _ ->
      Inspection.decline info;
      CErrors.anomaly Pp.(str "Uncaught pattern variable")
    end
  | App (f, args) ->
    begin match [@ocaml.warning "-4"] kind f with
    | Rel n ->
      let args = mk_clos_vect e args in
      begin match clos_rel (fst e) n with
      | Regular t -> knh info t (append_stack args stk)
      | HigherOrder (nargs, term) ->
        Inspection.decline info;
        let subs', args = Array.chop nargs args in
        let id = subs_id (Range.length info.i_relevances) in
        let subs' = Array.fold_left (fun s v -> subs_cons (Regular v) s) id subs' in
        let head = resubst subs' term in
        knh info head (append_stack args stk)
      end
    | _ -> knht info e f (append_stack (mk_clos_vect e args) stk)
    end
    | Case(ci,u,pms,(_,r as p),NoInvert,t,br) ->
      if is_irrelevant info (usubst_relevance e r) then
        (mk_irrelevant, skip_irrelevant_stack info stk)
      else
        knht info e t (ZcaseT(ci, u, pms, p, br, e)::stk)
    | Case(ci,u,pms,(_,r as p),CaseInvert{indices},t,br) ->
      if is_irrelevant info (usubst_relevance e r) then
        (mk_irrelevant, skip_irrelevant_stack info stk)
      else
        let term = FCaseInvert (ci, u, pms, p, (Array.map (mk_clos e) indices), mk_clos e t, br, e) in
        (* a head returned without [knh] is fresh: a shared cell may be reduced *)
        fresh_fconstr Red term, stk
    | Fix (((_, n), (lna, _, _)) as fx) ->
      inspect_fix_interface info fx stk;
      if is_irrelevant info (usubst_relevance e (lna.(n)).binder_relevance) then
        (mk_irrelevant, skip_irrelevant_stack info stk)
      else
        knh info (make_fconstr Cstr (FFix (fx, e))) stk
    | Cast(a,_,_) -> knht info e a stk
    | Proj (p, r, c) ->
      let r = usubst_relevance e r in
      if is_irrelevant info r then
        (mk_irrelevant, skip_irrelevant_stack info stk)
      else begin match unfold_projection info p r with
      | None -> (fresh_fconstr Red (FProj (p, r, mk_clos e c)), stk)
      | Some s -> knht info e c (s :: stk)
      end
    | Construct _ -> knh info (mk_clos e t) stk
    | (Ind _|Const _|Var _|Meta _ | Sort _ | Int _|Float _|String _) -> (mk_clos e t, stk)
    | CoFix cfx ->
      make_fconstr Cstr (FCoFix (cfx, e)), stk
    | Lambda (na, ty, body) when Inspection.active info ->
      make_fconstr Cstr (FLambda (1, [na, ty], body, e)), stk
    | Lambda _ -> make_fconstr Cstr (mk_lambda e t), stk
    | Prod (n, t, c) ->
      make_fconstr Ntrl (FProd (n, mk_clos e t, c, e)), stk
    | LetIn (n,b,t,c) ->
      make_fconstr Red (FLetIn (n, mk_clos e b, mk_clos e t, c, e)), stk
    | Evar ev ->
      begin match info.i_cache.i_sigma.evar_expand ev with
      | EvarDefined c -> knht info e c stk
      | EvarUndefined (evk, args) ->
        assert (UVars.Instance.is_empty (snd e));
        if info.i_cache.i_mode = Conversion && info.i_cache.i_sigma.evar_irrelevant ev then
          (mk_irrelevant, skip_irrelevant_stack info stk)
        else
          let repack = info.i_cache.i_sigma.evar_repack in
          make_fconstr Ntrl (FEvar (evk, args, e, repack)), stk
      end
    | Array(u,t,def,ty) ->
      let u = usubst_instance e u in
      let len = Array.length t in
      let ty = mk_clos e ty in
      let t = Parray.init (Uint63.of_int len) (fun i -> mk_clos e t.(i)) (mk_clos e def) in
      let term = FArray (u,t,ty) in
      knh info (make_fconstr Cstr term) stk

(************************************************************************)

let conv : (clos_infos -> clos_tab -> fconstr -> fconstr -> bool) ref
  = ref (fun _ _ _ _ -> (assert false : bool))
let set_conv f = conv := f

type ('a, 'b) reduction = {
  red_ret : clos_infos -> Table.t -> pat_state:'b -> ?failed:bool -> (fconstr * stack) -> 'a;
  red_kni : clos_infos -> Table.t -> pat_state:'b -> fconstr -> stack -> 'a;
  red_knit : clos_infos -> Table.t -> pat_state:'b -> usubs -> Constr.t -> stack -> 'a;
}

type (_, _) escape =
  | No:  ('i, 'i) escape
  | Yes: ('a, 'a option) escape

module RedPattern :
sig

type resume_state

type _ depth =
  | Nil: (fconstr * stack, 'ret) escape -> 'ret depth
  | Cons: resume_state * 'ret depth -> 'ret depth

val match_symbol : ('a, 'a depth) reduction -> clos_infos -> Table.t ->
  pat_state:'a depth -> table_key -> UVars.Instance.t * bool * machine_rewrite_rule list -> stack -> 'a

val match_head : ('a, 'a depth) reduction -> clos_infos -> Table.t ->
  pat_state:'a depth -> resume_state -> fconstr -> stack -> 'a

end =
struct

type partial_subst = {
  subst: (int * fconstr, Sorts.Quality.t, Univ.Level.t) Partial_subst.t;
  rhs: constr;
}

type subst_status = Dead | Live of partial_subst

type 'a status =
  | Check of 'a
  | Ignore

module Status = struct
  let split_array n = function
  | Check a when Array.length a <> n -> invalid_arg "Status.split_array"
  | Check a -> Array.init n (fun i -> Check (Array.unsafe_get a i))
  | Ignore as p -> Array.make n p

  let fold_left f a = function Check b -> f a b | Ignore -> a
end

type ('a, 'b) next =
  | Continue of 'a
  | Return of 'b

type state =
  | LocStart of {
      elims: pattern_elimination list status array;
      depth: int;
      head: fconstr;
      stack: stack;
      next: state_next;
    }
  | LocArg of {
      patterns: pattern_argument status array;
      depth: int;
      arg: fconstr;
      next: state;
    }

and state_next = (state, bool * fconstr * stack) next

type resume_state = {
  states: subst_status array;
  depth: int;
  patterns: head_elimination status array;
  next: state;
}

type _ depth =
  | Nil: (fconstr * stack, 'ret) escape -> 'ret depth
  | Cons: resume_state * 'ret depth -> 'ret depth

let extract_or_kill filter a status =
  let step elim status =
    match elim, status with
    | Ignore, s -> s
    | _, Dead -> Dead
    | Check e, Live s -> match filter (e, s) with
      | None -> Dead
      | Some s -> Live s
  in
  Array.map2 step a status

let extract_or_kill2 filter a status =
  let step elim status =
    match elim, status with
   | Ignore, s -> Ignore, s
   | _, Dead -> Ignore, Dead
   | Check e, Live s -> match filter (e, s) with
      | None -> Ignore, Dead
      | Some (p, s) -> Check p, Live s
  in
  Array.split @@ Array.map2 step a status

let extract_or_kill3 filter a status =
  let step elim status =
    match elim, status with
    | Ignore, s -> Ignore, Ignore, s
    | _, Dead -> Ignore, Ignore, Dead
    | Check e, Live s -> match filter (e, s) with
      | None -> Ignore, Ignore, Dead
      | Some (p1, p2, s) -> Check p1, Check p2, Live s
  in
  Array.split3 @@ Array.map2 step a status

let extract_or_kill4 filter a status =
  let step elim status =
    match elim, status with
    | Ignore, s -> Ignore, Ignore, Ignore, s
    | _, Dead -> Ignore, Ignore, Ignore, Dead
    | Check e, Live s -> match filter (e, s) with
      | None -> Ignore, Ignore, Ignore, Dead
      | Some (p1, p2, p3, s) -> Check p1, Check p2, Check p3, Live s
  in
  Array.split4 @@ Array.map2 step a status

let rec match_main : type a. (a, a depth) reduction -> _ -> _ -> pat_state:a depth -> _ -> _ -> a =
  fun red info tab ~pat_state states loc ->
  if Array.for_all (function Dead -> true | Live _ -> false) states then match_kill red info tab ~pat_state loc else
  match [@ocaml.warning "-4"] loc with
  | LocStart { elims; depth; head; stack; next = Return _ as next } ->
    begin match Array.find2_map (fun state elim -> match state, elim with Live s, Check [] -> Some s | _ -> None) states elims with
    | Some { subst; rhs } ->
        let subst, qsubst, usubst = Partial_subst.to_arrays subst in
        let subst = Array.fold_right (fun (n, v) s -> subs_cons (HigherOrder (n, v)) s) subst (subs_id 0) in
        let usubst = UVars.Instance.of_array (qsubst, usubst) in
        let m' = mk_clos (subst, usubst) rhs in
        begin match pat_state with
        | Nil Yes -> Some (m', stack)
        | _ -> red.red_kni info tab ~pat_state m' stack
        end
    | None -> match_elim red info tab ~pat_state next depth states elims head stack
    end
  | LocArg { patterns; depth; arg; next } ->
      match_arg red info tab ~pat_state next depth states patterns arg
  | LocStart { elims; depth; head; stack; next } ->
      match_elim red info tab ~pat_state next depth states elims head stack

and match_kill : 'a. ('a, 'a depth) reduction -> _ -> _ -> pat_state:'a depth -> _ -> 'a =
  fun red info tab ~pat_state -> function
  | LocArg { next; _ } -> match_kill red info tab ~pat_state next
  | LocStart { head; stack; next; _ } ->
      ignore (zip head stack);
      match next with
      | Continue next -> match_kill red info tab ~pat_state next
      | Return k -> try_unfoldfix red info tab ~pat_state k

and match_endstack red info tab ~pat_state states next =
  match next with
  | Continue next -> match_main red info tab ~pat_state states next
  | Return k ->
      assert (Array.for_all (function Dead -> true | Live _ -> false) states);
      try_unfoldfix red info tab ~pat_state k

and try_unfoldfix red info tab ~pat_state (b, m, stk) =
  if not b then red.red_ret info tab ~pat_state ~failed:true (m, stk) else
  let rarg, stack = strip_update_shift_absorb_app m stk in
  match [@ocaml.warning "-4"] stack with
  | Zfix (fx, par) :: s ->
    let stk' = par @ append_stack [|rarg|] s in
    let (fxe,fxbd) = contract_fix_vect fx.term in
    red.red_knit info tab ~pat_state fxe fxbd stk'
  | _ -> red.red_ret info tab ~pat_state ~failed:true (m, stk)

and match_elim : 'a. ('a, 'a depth) reduction -> _ -> _ -> pat_state:'a depth -> _ -> _ -> _ -> _ -> _ -> _ -> 'a =
  fun red info tab ~pat_state next depth states elims head stk ->
  match stk with
  | Zapp args :: s ->
      let pargselims, states = extract_or_kill2 (function [@ocaml.warning "-4"] PEApp pargs :: es, subst -> Some ((pargs, es), subst) | _ -> None) elims states in
      let na = Array.length args in
      let np = Array.fold_left (Status.fold_left (fun a (pargs, _) -> min a (Array.length pargs))) na pargselims in
      let pargs, elims, states =
        extract_or_kill3 (fun ((pargs, elims), subst) ->
          let npp = Array.length pargs in
          if npp == np then Some (pargs, elims, subst) else
          let fst, lst = Array.chop np pargs in
          Some (fst, PEApp lst :: elims, subst))
          pargselims states
      in
      let args, rest = Array.chop np args in
      let head = mkFApp head args in
      let stack = if Array.length rest > 0 then Zapp rest :: s else s in
      let loc = LocStart { elims; depth; head; stack; next } in
      let loc = Array.fold_right2 (fun patterns arg next -> LocArg { patterns; depth; arg; next }) (Array.transpose (Array.map (Status.split_array np) pargs)) args loc in
      match_main red info tab ~pat_state states loc
  | Zshift k :: s -> match_elim red info tab ~pat_state next depth states elims (lift_fconstr k head) s
  | Zupdate m :: s ->
      let () = update m (fconstr_mark head) head.term in
      match_elim red info tab ~pat_state next depth states elims head s
  | ZcaseT (ci, u, pms, ((pctx, p), _ as pred), brs, e) :: s ->
      let t = FCaseT (ci, u, pms, pred, head, brs, e) in
      let mark = neutr (fconstr_mark head) in
      let head = fresh_fconstr mark t in
      let prets, pbrss, elims, states = extract_or_kill4 (function [@ocaml.warning "-4"]
      | PECase (pind, pret, pbrs) :: es, subst ->
        if not @@ QInd.equal (info_env info) pind ci.ci_ind then None else
          Some (pret, pbrs, es, subst)
      | _ -> None)
          elims states
      in
      let mib = Environ.lookup_mind (fst ci.ci_ind) info.i_cache.i_env in
      let mip = mib.mind_packets.(snd ci.ci_ind) in
      let ind_subst = inductive_subst mib u (Array.map (mk_clos e) pms) in
      let loc = LocStart { elims; depth; head; stack=s; next } in
      let loc = Array.fold_right_i (fun i patterns next ->
        let brctx, br = brs.(i) in
        let brdepth, br_e =
          if Int.equal mip.mind_consnrealdecls.(i) mip.mind_consnrealargs.(i) then
            let brdepth = Array.length brctx in
            brdepth, usubs_liftn brdepth e
          else
            let ctx, _ = List.chop mip.mind_consnrealdecls.(i) (fst mip.mind_nf_lc.(i)) in
            let ctx = List.map Context.Rel.Declaration.get_value ctx in
            esubst_of_context ctx ind_subst e
        in
        LocArg { patterns; depth = brdepth+depth; arg = mk_clos br_e br; next })
        (Array.transpose (Array.map (Status.split_array (Array.length brs)) pbrss)) loc in
      let pdepth, pred_e =
        if Int.equal mip.mind_nrealargs mip.mind_nrealdecls then
          let pdepth = Array.length pctx in
          pdepth, usubs_liftn pdepth e
        else
          let ctx, _ = List.chop mip.mind_nrealdecls mip.mind_arity_ctxt in
          let open Context.Rel.Declaration in
          (* Add the inductive binder *)
          let ctx = None :: List.map get_value ctx in
          esubst_of_context ctx ind_subst e
      in
      let loc = LocArg { patterns = prets; depth = pdepth + depth; arg = mk_clos pred_e p; next = loc } in
      match_main red info tab ~pat_state states loc
  | Zproj (proj', r) :: s ->
      let mark = neutr (fconstr_mark head) in
      let head =
        fresh_fconstr mark (FProj (Projection.make proj' true, r, head))
      in
      let elims, states = extract_or_kill2 (function [@ocaml.warning "-4"]
      | PEProj proj :: es, subst ->
        if not @@ QProjection.Repr.equal (info_env info) proj proj' then None else
        Some (es, subst)
      | _ -> None) elims states
      in
      let loc = LocStart { elims; depth; head; stack=s; next } in
      match_main red info tab ~pat_state states loc
  | Zfix _ :: _ | Zprimitive _ :: _ ->
      let states = extract_or_kill (fun _ -> None) elims states in
      ignore (zip head stk);
      match_endstack red info tab ~pat_state states next
  | [] ->
      let states = extract_or_kill (function [], subst -> Some subst | _ -> None) elims states in
      match_endstack red info tab ~pat_state states next

and match_arg : 'a. ('a, 'a depth) reduction -> _ -> _ -> pat_state:'a depth -> _ -> _ -> _ -> _ -> _ -> 'a =
  fun red info tab ~pat_state next depth states patterns t ->
  let match_deeper = ref false in
  let t' = depth, t in
  let patterns, states = Array.split @@ Array.map2
    (function Dead -> fun _ -> Ignore, Dead | (Live ({ subst; _ } as psubst) as state) -> function
      | Ignore -> Ignore, state
      | Check EHole i -> Ignore, Live { psubst with subst = Partial_subst.add_term i t' subst }
      | Check EHoleIgnored -> Ignore, state
      | Check ERigid p -> match_deeper := true; Check p, state
    ) states patterns in
  if !match_deeper then
    let pat_state = Cons ({ states; depth; patterns; next }, pat_state) in
    red.red_kni info tab ~pat_state t []
  else
    match_main red info tab ~pat_state states next

and match_head red info tab ~pat_state next depth states patterns t stk =
  match [@ocaml.warning "-4"] t.term with
  | FInd (ind', u) ->
    let elims, states = extract_or_kill2 (function [@ocaml.warning "-4"]
    | (PHInd (ind, pu), elims), psubst ->
      if not @@ QInd.equal (info_env info) ind ind' then None else
      let subst = UVars.Instance.pattern_match pu u psubst.subst in
      Option.map (fun subst -> elims, { psubst with subst }) subst
    | _ -> None) patterns states
    in
    let loc = LocStart { elims; depth; head=t; stack=stk; next=Continue next } in
    match_main red info tab ~pat_state states loc
  | FConstruct ((constr', u), args) ->
    let elims, states = extract_or_kill2 (function [@ocaml.warning "-4"]
    | (PHConstr (constr, pu), elims), psubst ->
      if not @@ QConstruct.equal (info_env info) constr constr' then None else
      let subst = UVars.Instance.pattern_match pu u psubst.subst in
      Option.map (fun subst -> elims, { psubst with subst }) subst
    | _ -> None) patterns states
    in
    let loc = LocStart { elims; depth; head=t; stack=append_stack args stk; next=Continue next } in
    match_main red info tab ~pat_state states loc
  | FAtom t' -> begin match [@ocaml.warning "-4"] kind t' with
    | Sort s ->
      let elims, states = extract_or_kill2 (function [@ocaml.warning "-4"]
      | (PHSort ps, elims), psubst ->
        let subst = Sorts.pattern_match ps s psubst.subst in
        Option.map (fun subst -> elims, { psubst with subst }) subst
      | _ -> None) patterns states
      in
      let loc = LocStart { elims; depth; head=t; stack=stk; next=Continue next } in
      match_main red info tab ~pat_state states loc
    | Meta _ ->
      let elims, states = extract_or_kill2 (fun _ -> None) patterns states in
      let loc = LocStart { elims; depth; head=t; stack=stk; next=Continue next } in
      match_main red info tab ~pat_state states loc
    | _ -> assert false
    end
  | FFlex (ConstKey (c', u)) ->
    let elims, states = extract_or_kill2 (function [@ocaml.warning "-4"]
    | (PHSymbol (c, pu), elims), psubst ->
      if not @@ QConstant.equal (info_env info) c c' then None else
      let subst = UVars.Instance.pattern_match pu u psubst.subst in
      Option.map (fun subst -> elims, { psubst with subst }) subst
    | _ -> None) patterns states
    in
    let loc = LocStart { elims; depth; head=t; stack=stk; next=Continue next } in
    match_main red info tab ~pat_state states loc
  | FRel n ->
    let elims, states = extract_or_kill2 (function [@ocaml.warning "-4"]
    | (PHRel n', elims), psubst ->
      if not @@ Int.equal n n' then None else
      Some (elims, psubst)
    | _ -> None) patterns states
    in
    let loc = LocStart { elims; depth; head=t; stack=stk; next=Continue next } in
    match_main red info tab ~pat_state states loc
  | FInt i' ->
    let elims, states = extract_or_kill2 (function [@ocaml.warning "-4"]
    | (PHInt i, elims), psubst ->
      if not @@ Uint63.equal i i' then None else
      Some (elims, psubst)
    | _ -> None) patterns states
    in
    let loc = LocStart { elims; depth; head=t; stack=stk; next=Continue next } in
    match_main red info tab ~pat_state states loc
  | FFloat f' ->
    let elims, states = extract_or_kill2 (function [@ocaml.warning "-4"]
    | (PHFloat f, elims), psubst ->
      if not @@ Float64.equal f f' then None else
      Some (elims, psubst)
    | _ -> None) patterns states
    in
    let loc = LocStart { elims; depth; head=t; stack=stk; next=Continue next } in
    match_main red info tab ~pat_state states loc
  | FString s' ->
    let elims, states = extract_or_kill2 (function [@ocaml.warning "-4"]
    | (PHString s, elims), psubst ->
      if not @@ Pstring.equal s s' then None else
      Some (elims, psubst)
    | _ -> None) patterns states
    in
    let loc = LocStart { elims; depth; head=t; stack=stk; next=Continue next } in
    match_main red info tab ~pat_state states loc
  | FProd (_, ty, body, e) ->
    let tysbodyelims, states = extract_or_kill2 (function [@ocaml.warning "-4"] (PHProd (ptys, pbod), es), psubst -> Some ((ptys, pbod, es), psubst) | _ -> None) patterns states in
    let pty, pbody, elims, states = extract_or_kill4 (fun ((ptys, pbod, elims), psubst) ->
        match Array.length ptys with
        | 0 -> assert false
        | 1 -> Some (ptys.(0), pbod, elims, psubst)
        | n ->
          let rem = Array.sub ptys 1 (n-1) in
          Some (ptys.(0), ERigid (PHProd (rem, pbod), []), elims, psubst)
      ) tysbodyelims states
    in
    let loc = LocStart { elims; depth; head=t; stack=stk; next=Continue next } in
    let loc = LocArg { patterns = pbody; depth = 1 + depth; arg = mk_clos (usubs_lift e) body; next = loc } in
    let loc = LocArg { patterns = pty; depth; arg = ty; next = loc } in
    match_main red info tab ~pat_state states loc
  | FLambda (na, ntys, body, e) ->
    let tysbodyelims, states = extract_or_kill2 (function [@ocaml.warning "-4"] (PHLambda (ptys, pbod), es), psubst when Array.length ptys <= na -> Some ((ptys, pbod, es), psubst) | _ -> None) patterns states in
    let na = Array.fold_left (Status.fold_left (fun a (p1, _, _) -> min a (Array.length p1))) na tysbodyelims in
    assert (na > 0);
    let ptys, pbody, elims, states = extract_or_kill4 (fun ((ptys, pbod, elims), psubst) ->
      let np = Array.length ptys in
      if np == na then Some (ptys, ERigid pbod, elims, psubst) else
      let fst, lst = Array.chop na ptys in
      Some (fst, ERigid (PHLambda (lst, pbod), []), elims, psubst)
      ) tysbodyelims states
    in
    let ntys, tys' = List.chop na ntys in
    let body = Term.compose_lam (List.rev tys') body in
    let tys = Array.of_list ntys in
    let tys = Array.mapi (fun n (_, t) -> n, mk_clos (usubs_liftn n e) t) tys in
    let loc = LocStart { elims; depth; head=t; stack=stk; next=Continue next } in
    let loc = LocArg { patterns = pbody; depth = Array.length tys + depth; arg = mk_clos (usubs_liftn na e) body; next = loc } in
    let loc = Array.fold_right2 (fun patterns (ldepth, arg) next -> LocArg { patterns; depth = ldepth + depth; arg; next }) (Array.transpose (Array.map (Status.split_array na) ptys)) tys loc
    in
    match_main red info tab ~pat_state states loc
  | _ ->
    let states = extract_or_kill (fun _ -> None) patterns states in
    ignore (zip t stk);
    match_main red info tab ~pat_state states next

let match_symbol red info tab ~pat_state fl (u, b, r) stk =
  let unfold_fix = b && red_set info.i_flags fFIX in
  let states, elims = Array.split @@ Array.map
    (fun r ->
      let pu, es = r.lhs_pat in
      let subst = Partial_subst.make r.nvars in
      let subst = UVars.Instance.pattern_match pu u subst in
      match subst with
      | Some subst -> Live { subst; rhs = r.Declarations.rhs }, Check es
      | None -> Dead, Ignore
    ) (Array.of_list r)
  in
  let m = make_fconstr Red (FFlex fl) in
  let loc = LocStart { elims; depth=0; head = m; stack = stk; next = Return (unfold_fix, m, stk) } in
  match_main red info tab ~pat_state states loc

let match_head red info tab ~pat_state { states; depth; patterns; next } m stk =
  match_head red info tab ~pat_state next depth states patterns m stk

end

type 'a depth = 'a RedPattern.depth

(* Computes a weak head normal form from the result of knh. *)
let rec knr : type a. _ -> _ -> pat_state:a depth -> _ -> _ -> a =
  fun info tab ~pat_state m stk ->
  Inspection.charge info 1;
  match m.term with
  | FLambda(n,tys,f,e) when red_set info.i_flags fBETA ->
      Inspection.charge info n;
      (match get_args n tys f e stk with
          Inl e', s -> knit info tab ~pat_state e' f s
        | Inr lam, s -> knr_ret info tab ~pat_state (lam,s))
  | FFlex fl when red_set info.i_flags fDELTA ->
      (match Table.lookup info tab fl with
        | Def (v, _) when Inspection.active info ->
          kni info tab ~pat_state v stk
        | Def (v, _) -> begin
          match [@ocaml.warning "-4"] fl with
          | ConstKey (c, _) ->
            let whd info m = fapp_stack (kni info tab ~pat_state:(RedPattern.Nil No) m []) in
            begin match compact_peano_unfold info ~whd c stk with
            | Some (m, stk) -> kni info tab ~pat_state m stk
            | None -> kni info tab ~pat_state v stk
            end
          | _ -> kni info tab ~pat_state v stk
          end
        | Primitive op ->
          Inspection.decline info;
          if check_native_args op stk then
            let c = match fl with ConstKey c -> c | RelKey _ | VarKey _ -> assert false in
            let rargs, a, nargs, stk = get_native_args1 op c stk in
            kni info tab ~pat_state a (Zprimitive(op,c,rargs,nargs)::stk)
          else
            (* Similarly to fix, partially applied primitives are not Ntrl! *)
            knr_ret info tab ~pat_state (m, stk)
        | Symbol (u, b, r) ->
          Inspection.decline info;
          RedPattern.match_symbol knred info tab ~pat_state fl (u, b, r) stk
        | Undef _ | OpaqueDef _ -> (set_ntrl m; knr_ret info tab ~pat_state (m,stk)))
  | FConstruct (c, args) ->
    let use_match = red_set info.i_flags fMATCH in
    let use_fix = red_set info.i_flags fFIX in
    begin match [@ocaml.warning "-4"] stk with
    | Zapp _ :: _ -> assert false (* knh *)
    | ZcaseT (ci, _, pms, _, br, e) :: s when use_match ->
      (* instance on the case and instance on the constructor are compatible by typing *)
      let (br, e) = get_branch info ci pms c args br e in
      knit info tab ~pat_state e br s
    | Zfix (fx, par) :: s when use_fix ->
      let () = match fx.term with
        | FFix (fix, _) -> inspect_fix_interface info fix par
        | _ -> Inspection.decline info
      in
      let stk' = par @ append_stack [|m|] s in
      let (fxe, fxbd) = contract_fix_vect fx.term in
      knit info tab ~pat_state fxe fxbd stk'
    | Zproj (p, _) :: s when use_match ->
      (* an inspected constructor need not be well typed: check the bounds *)
      let () = if Inspection.active info then
          let index = Projection.Repr.npars p + Projection.Repr.arg p in
          if not (Environ.QInd.equal info.i_cache.i_env
              (fst (fst c)) (Projection.Repr.inductive p)) ||
             index < 0 || index >= Array.length args then
            Inspection.decline info
      in
      let rargs = drop_parameters (Projection.Repr.npars p) args in
      let rarg = rargs.(Projection.Repr.arg p) in
      kni info tab ~pat_state rarg s
    | _ ->
      if is_irrelevant_constructor info c then
        knr_ret info tab ~pat_state (mk_irrelevant, skip_irrelevant_stack info stk)
      else
        knr_ret info tab ~pat_state (m, stk)
    end
  | FPeanoNat n ->
    let expose () = kni info tab ~pat_state (peano_constructor_view n) stk in
    begin match [@ocaml.warning "-4"] stk with
    | ZcaseT _ :: _ when red_set info.i_flags fMATCH -> expose ()
    | Zfix (fx, []) :: Zapp args :: s when red_set info.i_flags fFIX && not (Array.is_empty args) ->
      (* a registered Boolean test applied through its fixpoint *)
      begin match compact_peano_bool_fix info fx, compact_peano_of_fconstr info args.(0) with
      | Some op, Some other ->
        begin match compact_peano_bool_values op n other with
        | Some m ->
          kni info tab ~pat_state m (append_stack (Array.sub args 1 (Array.length args - 1)) s)
        | None -> expose ()
        end
      | _ -> expose ()
      end
    | Zfix _ :: _ when red_set info.i_flags fFIX -> expose ()
    | _ -> knr_ret info tab ~pat_state (m, stk)
    end
  | FCoFix ((i, (lna, _, _)), e) ->
    if is_irrelevant info (usubst_relevance e (lna.(i)).binder_relevance) then
      knr_ret info tab ~pat_state (mk_irrelevant, skip_irrelevant_stack info stk)
    else if red_set info.i_flags fCOFIX then
      (match strip_update_shift_app m stk with
        | (_, _, args, (((ZcaseT _|Zproj _)::_) as stk')) ->
            let (fxe,fxbd) = contract_fix_vect m.term in
            knit info tab ~pat_state fxe fxbd (args@stk')
        | (_, _, args, ((Zapp _ | Zfix _ | Zshift _ | Zupdate _ | Zprimitive _) :: _ | [] as s)) ->
            knr_ret info tab ~pat_state (m,args@s))
    else knr_ret info tab ~pat_state (m, stk)
  | FLetIn (_,v,_,bd,e) when red_set info.i_flags fZETA ->
      knit info tab ~pat_state (usubs_cons v e) bd stk
  | FInt _ | FFloat _ | FString _ | FArray _ ->
    (match [@ocaml.warning "-4"] strip_update_shift_app m stk with
     | (_, _, _, Zprimitive(op,(_,u as c),rargs,nargs)::s) ->
       let (rargs, nargs) = skip_native_args (m::rargs) nargs in
       begin match nargs with
         | [] ->
           let args = match rargs with
           | [] -> [||]
           | [a] -> [|a|]
           | [a; b] -> [|b; a|]
           | [a; b; c] -> [|c; b; a|]
           | [a; b; c; d] -> [|d; c; b; a|]
           | _ -> Array.rev_of_list rargs
           in
           begin match FredNative.red_prim (info_env info) () op u args with
            | Some m -> kni info tab ~pat_state m s
            | None -> assert false
           end
         | (kd,a)::nargs ->
           assert (kd = CPrimitives.Kwhnf);
           kni info tab ~pat_state a (Zprimitive(op,c,rargs,nargs)::s)
             end
     | (depth, _, _, stk) -> knr_ret info tab ~pat_state (m,zshift depth stk))
  (* symbolic reduction is a congruence search: an inverted case is kept for
     structural comparison, the ordinary reduction still inverts it *)
  | FCaseInvert (ci, u, pms, ((_pnas, p), _r), iv, _c, v, env)
    when red_set info.i_flags fMATCH && not info.i_symbolic ->
    begin match case_inversion info tab ci u pms p iv v env with
      | Some c -> knit info tab ~pat_state env c stk
      | None -> knr_ret info tab ~pat_state (m, stk)
    end
  | FIrrelevant ->
    let stk = skip_irrelevant_stack info stk in
    knr_ret info tab ~pat_state (m, stk)
  | FProd _ | FAtom _ | FInd _ (* relevant statically *)
  | FCaseInvert _ | FProj _ | FFix _ | FEvar _ (* relevant because of knh(t) *)
  | FLambda _ | FFlex _ | FRel _ (* irrelevance handled by conversion *)
  | FLetIn _ (* only happens in reduction mode *) ->
    knr_ret info tab ~pat_state (m, stk)
  | FLOCKED | FCLOS _ | FApp _ | FCaseT _ | FLIFT _ ->
    (* ruled out by knh(t) *)
    assert false

and knr_ret : type a. _ -> _ -> pat_state: a depth -> ?failed: _ -> _ -> a =
  fun info tab ~pat_state ?(failed=false) i ->
  match pat_state with
  | RedPattern.Cons (patt, pat_state) ->
      let m, stk = i in
      RedPattern.match_head knred info tab ~pat_state patt m stk
  | RedPattern.Nil b ->
      match b with No -> i | Yes -> if failed then None else Some i

(* Computes the weak head normal form of a term *)
and kni : type a. _ -> _ -> pat_state:a depth -> _ -> _ -> a =
  fun info tab ~pat_state m stk ->
  let (hm,s) = knh info m stk in
  knr info tab ~pat_state hm s
and knit : type a. _ -> _ -> pat_state:a depth -> _ -> _ -> _ -> a =
  fun info tab ~pat_state e t stk ->
  let (ht,s) = knht info e t stk in
  knr info tab ~pat_state ht s

and case_inversion info tab ci u pms p indices brs env = match brs with
| [||] -> None (* empty type *)
| [| [||], v |] ->
  (* No binders / lets at all in the unique branch *)
  let open Declarations in
  if Array.is_empty indices then Some v
  else
    let u = usubst_instance env u in
    let pms = mk_clos_vect env pms in
    let psubst = subs_consn pms 0 ci.ci_npar (subs_id 0) in

    let mib = Environ.lookup_mind (fst ci.ci_ind) (info_env info) in
    let mip = mib.mind_packets.(snd ci.ci_ind) in
    (* indtyping enforces 1 ctor with no letins in the context *)
    let _, indargs = mip.mind_nf_lc.(0) in
    let _, allargs = destApp indargs in
    let _, branch_indices = Array.chop ci.ci_npar allargs in
    let branch_indices = Array.map (fun c -> mk_clos (psubst, u) c) branch_indices in
    let branch_subs = usubs_cons mk_irrelevant (usubs_consv branch_indices env) in
    let external_subs = usubs_cons mk_irrelevant (usubs_consv indices env) in
    let branch_type = mk_clos branch_subs p in
    let external_type = mk_clos external_subs p in

    let tab = if info.i_cache.i_mode == Conversion then tab else Table.create () in
    let info = {info with i_cache = { info.i_cache with i_mode = Conversion}; i_flags=all} in
    if !conv info tab branch_type external_type
    then Some v else None
| _ -> assert false

and knred : 'a. ('a, 'a RedPattern.depth) reduction = {
  red_kni = kni;
  red_knit = knit;
  red_ret = knr_ret;
}

let kni info tab v stk = kni info tab ~pat_state:(RedPattern.Nil No) v stk
let knit info tab v stk = knit info tab ~pat_state:(RedPattern.Nil No) v stk
(* A cell reduced in place under one set of flags is no head for a reduction
   under another: sharing is per reduction class. Private and inspection
   reductions keep their copies distinct. *)
let reduction_class info =
  let bit kind i = if RedFlags.red_set info.i_flags kind then 1 lsl i else 0 in
  bit RedFlags.fBETA 0 lor bit RedFlags.fDELTA 1 lor bit RedFlags.fMATCH 2 lor
  bit RedFlags.fFIX 3 lor bit RedFlags.fCOFIX 4 lor bit RedFlags.fZETA 5 lor
  (if info.i_symbolic then 64 else 0)

let with_sharing info tab f =
  let cells =
    if Option.is_empty info.i_private && not (Inspection.active info)
    then Table.cells tab (reduction_class info) else None in
  with_cells cells f

let kh info tab v stk = with_sharing info tab (fun () -> fapp_stack (kni info tab v stk))

(************************************************************************)

(* Computes the strong normal form of a term.
   1- Calls kni
   2- tries to rebuild the term. If a closure still has to be computed,
      calls itself recursively. *)

let is_val v = match v.term with
| FAtom _ | FRel _   | FInd _ | FConstruct (_,[||]) | FInt _ | FFloat _ | FString _ | FPeanoNat _ -> true
| FFlex _ -> fconstr_mark v == Ntrl
| FConstruct _ | FApp _ | FProj _ | FFix _ | FCoFix _ | FCaseT _ | FCaseInvert _ | FLambda _
| FProd _ | FLetIn _ | FEvar _ | FArray _ | FLIFT _ | FCLOS _ -> false
| FIrrelevant | FLOCKED -> assert false

let rec kl info tab m =
  let share = info.i_cache.i_share in
  if is_val m then term_of_fconstr m
  else
    let (nm,s) = kni info tab m [] in
    let () = if share then ignore (fapp_stack (nm, s)) in (* to unlock Zupdates! *)
    zip_term info tab (norm_head info tab nm) s

and klt info tab e t = match kind t with
| Rel i ->
  begin match expand_rel i (fst e) with
  | Inl (n, Regular mt) -> kl info tab @@ lift_fconstr n mt
  | Inl (_, HigherOrder (nargs, term)) -> assert (Int.equal nargs 0); kl info tab term
  | Inr (k, None) -> if Int.equal k i then t else mkRel k
  | Inr (k, Some p) ->
    kl info tab @@
      lift_fconstr (k - p) (make_fconstr Red (FFlex (RelKey p)))
  end
| App (hd, args) ->
  let is_stuck = match kind hd with
  | Rel _ -> false (* For AppRel, in case of a higher-order substitution, knit correctly deals with it *)
  | Ind _ | Construct _ -> true
  | CoFix _ | Lambda _ | Fix _ | Prod _ | Evar _ | Case _
  | Cast _ | LetIn _ | Proj _ | Array _ | Meta _ | Sort _ | Int _
  | Float _ | String _ -> false
  | Const (cst, _) ->
    let ts = RedFlags.red_transparent info.i_flags in
    not @@ TransparentState.is_transparent_constant ts cst
  | Var id ->
    let ts = RedFlags.red_transparent info.i_flags in
    not @@ TransparentState.is_transparent_variable ts id
  | App _ -> assert false
  in
  if is_stuck then
    let args' = Array.Smart.map (fun c -> klt info tab e c) args in
    let hd' = subst_instance_constr (snd e) hd in
    if hd' == hd && args' == args then t
    else mkApp (hd', args')
  else
    let share = info.i_cache.i_share in
    let (nm,s) = knit info tab e t [] in
    let () = if share then ignore (fapp_stack (nm, s)) in (* to unlock Zupdates! *)
    zip_term info tab (norm_head info tab nm) s
| Lambda (na, u, c) ->
  let na' = usubst_binder e na in
  let u' = klt info tab e u in
  let c' = klt (push_relevance info na') tab (usubs_lift e) c in
  if na' == na && u' == u && c' == c then t
  else mkLambda (na', u', c')
| Prod (na, u, v) ->
  let na' = usubst_binder e na in
  let u' = klt info tab e u in
  let v' = klt (push_relevance info na') tab (usubs_lift e) v in
  if na' == na && u' == u && v' == v then t
  else mkProd (na', u', v')
| Cast (t, _, _) -> klt info tab e t
| Var _ | Const _ | CoFix _ | Fix _ | Evar _ | Case _ | LetIn _ | Proj _ | Array _ ->
  let share = info.i_cache.i_share in
  let (nm,s) = knit info tab e t [] in
  let () = if share then ignore (fapp_stack (nm, s)) in (* to unlock Zupdates! *)
  zip_term info tab (norm_head info tab nm) s
| Meta _ | Sort _ | Ind _ | Construct _ | Int _ | Float _ | String _ ->
  subst_instance_constr (snd e) t

(* no redex: go up for atoms and already normalized terms, go down
   otherwise. *)
and norm_head info tab m =
  if is_val m then term_of_fconstr m else
    match m.term with
      | FLambda(_n,tys,f,e) ->
        let fold (e, info, ctxt) (na, ty) =
          let na = usubst_binder e na in
          let ty = klt info tab e ty in
          let info = push_relevance info na in
          (usubs_lift e, info, (na, ty) :: ctxt)
        in
        let (e', info, rvtys) = List.fold_left fold (e,info,[]) tys in
        let bd = klt info tab e' f in
        List.fold_left (fun b (na,ty) -> mkLambda(na,ty,b)) bd rvtys
      | FLetIn(na,a,b,f,e) ->
          let na = usubst_binder e na in
          let c = klt (push_relevance info na) tab (usubs_lift e) f in
          mkLetIn(na, kl info tab a, kl info tab b, c)
      | FProd(na,dom,rng,e) ->
        let na = usubst_binder e na in
        let rng = klt (push_relevance info na) tab (usubs_lift e) rng in
          mkProd(na, kl info tab dom, rng)
      | FCoFix((n,(na,tys,bds)),e) ->
          let na = Array.Smart.map (usubst_binder e) na in
          let infobd = push_relevances info na in
          let ftys = Array.map (fun ty -> klt info tab e ty) tys in
          let fbds = Array.map (fun bd -> klt infobd tab (usubs_liftn (Array.length na) e) bd) bds in
          mkCoFix (n, (na, ftys, fbds))
      | FFix((n,(na,tys,bds)),e) ->
          let na = Array.Smart.map (usubst_binder e) na in
          let infobd = push_relevances info na in
          let ftys = Array.map (fun ty -> klt info tab e ty) tys in
          let fbds = Array.map (fun bd -> klt infobd tab (usubs_liftn (Array.length na) e) bd) bds in
          mkFix (n, (na, ftys, fbds))
      | FEvar(ev, args, env, repack) ->
          repack (ev, List.map (fun a -> klt info tab env a) args)
      | FProj (p,r,c) ->
        mkProj (p, r, kl info tab c)
      | FArray (u, a, ty) ->
        let a, def = Parray.to_array a in
        let a = Array.map (kl info tab) a in
        let def = kl info tab def in
        let ty = kl info tab ty in
        mkArray (u, a, def, ty)
      | FConstruct (c,args) -> mkApp (mkConstructU c, Array.map (kl info tab) args)
      | FLOCKED | FRel _ | FAtom _ | FFlex _ | FInd _
      | FApp _ | FCaseT _ | FCaseInvert _ | FLIFT _ | FCLOS _ | FInt _
      | FFloat _ | FString _ | FPeanoNat _ -> term_of_fconstr m
      | FIrrelevant -> assert false (* only introduced when converting *)

and zip_term info tab m stk = match stk with
| [] -> m
| Zapp args :: s ->
    zip_term info tab (mkApp(m, Array.map (kl info tab) args)) s
| ZcaseT(ci, u, pms, (p,r), br, e) :: s ->
  let zip_ctx (nas, c) =
      let nas = Array.map (usubst_binder e) nas in
      let e = usubs_liftn (Array.length nas) e in
      (nas, klt info tab e c)
    in
    let r = usubst_relevance e r in
    let u = usubst_instance e u in
    let t = mkCase(ci, u, Array.map (fun c -> klt info tab e c) pms, (zip_ctx p, r),
      NoInvert, m, Array.map zip_ctx br) in
    zip_term info tab t s
| Zproj (p,r)::s ->
    let t = mkProj (Projection.make p true, r, m) in
    zip_term info tab t s
| Zfix(fx,par)::s ->
    let h = mkApp(zip_term info tab (kl info tab fx) par,[|m|]) in
    zip_term info tab h s
| Zshift(n)::s ->
    zip_term info tab (lift n m) s
| Zupdate(_rf)::s ->
    zip_term info tab m s
| Zprimitive(_,c,rargs, kargs)::s ->
    let kargs = List.map (fun (_,a) -> kl info tab a) kargs in
    let args =
      List.fold_left (fun args a -> kl info tab a ::args) (m::kargs) rargs in
    let h = mkApp (mkConstU c, Array.of_list args) in
    zip_term info tab h s

(* Initialization and then normalization *)

(* weak reduction *)
let whd_val info tab v = term_of_fconstr (kh info tab v [])

(* strong reduction *)
let norm_val info tab v = with_sharing info tab (fun () -> kl info tab v)
let norm_term info tab e t = with_sharing info tab (fun () -> klt info tab e t)

let whd_stack infos tab m stk = with_sharing infos tab @@ fun () -> match fconstr_mark m with
| Ntrl when not (symbolic_reduction infos) ->
  (* every head subterm of [m] is [Ntrl], so [kni] is not needed; but [knh] may
     still push update frames on cells reached through a substitution: unlock them *)
  let (m', stk') as k = knh infos m stk in
  let () = if infos.i_cache.i_share && not (m == m' && stk == stk') then ignore (zip m' stk') in
  k
| Ntrl | Red | Cstr ->
  (* a neutral mark certifies the value; a saved spine may still be a redex *)
  let k = kni infos tab m stk in
  let () =
    if infos.i_cache.i_share then
      (* to unlock Zupdates! *)
      let (m', stk') = k in
      if not (m == m' && stk == stk') then ignore (zip m' stk')
  in
  k

let create_infos i_mode ?univs ?evars i_flags i_env =
  let evars = Option.default (default_evar_handler i_env) evars in
  let i_univs = Option.default (Environ.universes i_env) univs in
  let i_share = (Environ.typing_flags i_env).Declarations.share_reduction in
  let i_cache = {i_env; i_sigma = evars; i_share; i_univs; i_mode} in
  {i_flags; i_symbolic = false; i_private = None; i_relevances = Range.empty;
   i_inspection = None; i_cache}

let create_conv_infos = create_infos Conversion
let create_clos_infos = create_infos Reduction

let oracle_of_infos infos = Environ.oracle infos.i_cache.i_env

let infos_with_reds infos reds =
  { infos with i_flags = reds }

let infos_with_symbolic_views infos = { infos with i_symbolic = true }

module Cells = Hashtbl.Make(struct
  type t = fconstr
  let equal a b = a == b
  let hash = fconstr_hash
end)

(* Inspect [roots] with at most [steps] of reduction in a private view: the
   cells [knh] visits are copied there and the copies, not the caller's cells,
   receive the reducer's updates. Neutral marks depend on the reduction
   flags, so a copy recomputes its mark; constructor, lambda and fixpoint
   marks are kept. [None] when the budget runs out or the reduction reaches
   an unsupported construct. *)
(* A private call-by-need view of [infos]: a cell is copied, with [mark], the
   first time reduction visits it; the caller's cells are never updated. *)
let private_view ?(mark = fconstr_mark) ?(visit = ignore) infos =
  let cells = Cells.create 31 in
  let own source =
    visit ();
    match Cells.find_opt cells source with
    | Some owned -> owned
    | None ->
      let owned = fresh_fconstr (mark source) source.term in
      Cells.add cells source owned;
      (* an owned cell visited again keeps its updated result *)
      Cells.add cells owned owned;
      if Cells.length cells land 255 = 0 then Control.check_for_interrupt ();
      owned in
  { infos with i_private = Some own;
    i_cache = { infos.i_cache with i_share = true } }

let infos_with_private_reduction infos = private_view infos

exception Private_budget_exhausted

let with_bounded_private_reduction ~steps infos reduce =
  let remaining = ref (max 0 steps) in
  let visit () =
    if Int.equal !remaining 0 then raise_notrace Private_budget_exhausted;
    decr remaining;
    if !remaining land 255 = 0 then Control.check_for_interrupt () in
  try Some (reduce (private_view ~visit infos)) with Private_budget_exhausted -> None

let with_private_closure_query ~steps infos roots inspect =
  let infos = { infos with i_inspection = Some (ref (max 0 steps)) } in
  let mark source = match source.term with
    | FConstruct _ | FPeanoNat _ | FLambda _ | FFix _ | FCoFix _
    | FInt _ | FFloat _ | FString _ | FArray _ -> Cstr
    | FRel _ | FAtom _ | FInd _ | FProd _ | FIrrelevant -> Ntrl
    | FFlex _ | FApp _ | FProj _ | FCLOS _ | FLIFT _ | FLetIn _
    | FCaseT _ | FCaseInvert _ | FEvar _ -> Red
    | FLOCKED -> raise_notrace Inspection.Limit in
  let infos = private_view ~mark ~visit:(fun () -> Inspection.charge infos 1) infos in
  try inspect infos (List.map (Option.get infos.i_private) roots)
  with Inspection.Limit -> None

let unfold_ref_with_args infos tab fl v =
  match Table.lookup infos tab fl with
  | Def (def, _) when Inspection.active infos -> Some (def, v)
  | Def (def, _) -> begin
    match [@ocaml.warning "-4"] fl with
    | ConstKey (c, _) ->
      begin match compact_peano_unfold infos ~whd:(fun infos m -> kh infos tab m []) c v with
      | Some _ as result -> result
      | None -> Some (def, v)
      end
    | _ -> Some (def, v)
    end
  | Primitive op when check_native_args op v ->
    let c = match [@ocaml.warning "-4"] fl with ConstKey c -> c | _ -> assert false in
    let rargs, a, nargs, v = get_native_args1 op c v in
    (* the update frame must name the private view's cell, not the caller's *)
    let a = match infos.i_private with None -> a | Some own -> own a in
    Some (a, (Zupdate a::(Zprimitive(op,c,rargs,nargs)::v)))
  | Symbol (u, b, r) ->
    RedPattern.match_symbol knred (infos_with_reds infos all) tab ~pat_state:(RedPattern.Nil Yes) fl (u, b, r) v
  | Undef _ | OpaqueDef _ | Primitive _ -> None

let get_ref_mask info tab fl = match Table.lookup info tab fl with
| Def (_, mask) -> mask
| Primitive _ | Symbol _ | Undef _ | OpaqueDef _ -> [||]
