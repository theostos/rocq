open Constr
open CClosure

let identity = Esubst.subs_id 0, UVars.Instance.empty
let binder = Context.make_annot Names.Anonymous Sorts.Relevant
let infos = create_clos_infos RedFlags.betaiotazeta Environ.empty_env
let reduce infos term =
  let head, stack = whd_stack infos (create_tab ()) term [] in
  term_of_process head stack

let snapshot ?(steps = 4096) roots inspect =
  with_closure_snapshot ~steps infos roots inspect

let () =
  let node = mkVar (Names.Id.of_string "node") in
  let syntax = mkApp (node, [|mkRel 1; mkRel 1|]) in
  let huge = ref (inject (mkRel 1)) in
  let original_cells = ref [] in
  for _ = 1 to 50 do
    huge := mk_clos (usubs_cons !huge identity) syntax;
    original_cells := (!huge, fterm_of !huge) :: !original_cells
  done;
  let before = Gc.allocated_bytes () in
  assert (snapshot [!huge; !huge] (fun _ -> function
    | [left; right] -> assert (left == right && left != !huge); Some true
    | _ -> assert false) = Some true);
  let allocated = Gc.allocated_bytes () -. before in
  assert (allocated < 1_000_000.);

  (* An ignored enormous substitution is never quoted or normalized. *)
  let ignored = mk_clos (usubs_cons !huge identity)
      (mkLetIn (binder, mkRel 1, mkProp, mkProp)) in
  assert (snapshot [ignored] (fun infos -> function
    | [copy] -> assert (Constr.equal (reduce infos copy) mkProp); Some true
    | _ -> assert false) = Some true);
  List.iter (fun (cell, term) -> assert (fterm_of cell == term)) !original_cells;

  (* Every substitution relocation is retained, including across binders. *)
  let small = inject (mkApp (node, [|mkRel 1|])) in
  let s = usubs_cons small identity in
  let substitutions = [s; usubs_liftn 3 s;
    (Esubst.subs_shft (5, fst s), snd s);
    usubs_liftn 2 (Esubst.subs_shft (7, fst s), snd s)] in
  List.iter (fun s ->
    for index = 1 to 10 do
      let term = mk_clos s (mkLambda (binder, mkProp, mkRel index)) in
      let expected = term_of_fconstr term in
      assert (snapshot [term] (fun _ -> function
        | [copy] -> assert (Constr.equal (term_of_fconstr copy) expected); Some true
        | _ -> assert false) = Some true)
    done) substitutions;

  (* Budget exhaustion is inconclusive, not false equality or a corrupted cell.
     It is shared by repeated calls and checked inside beta reduction. *)
  assert (snapshot ~steps:2 [!huge] (fun _ _ -> Some true) = None);
  let omega = mkLambda (binder, mkProp, mkApp (mkRel 1, [|mkRel 1|])) in
  let diverging = inject (mkApp (omega, [|omega|])) in
  let before = fterm_of diverging in
  assert (snapshot ~steps:100 [diverging] (fun infos -> function
    | [copy] -> ignore (reduce infos copy); Some true
    | _ -> assert false) = None);
  assert (fterm_of diverging == before);
  assert (snapshot ~steps:100 [inject mkProp] (fun infos -> function
    | [copy] ->
      for _ = 1 to 1000 do ignore (reduce infos copy) done;
      Some true
    | _ -> assert false) = None);

  (* A partial fixpoint is a neutral result, not a reason to reject every
     recursive type family. Its interface still consumes the query budget. *)
  let fix = mkFix (([|0|], 0), ([|binder|], [|mkProp|], [|mkRel 1|])) in
  assert (snapshot [inject fix] (fun infos -> function
    | [copy] -> Some (Constr.equal (reduce infos copy) fix)
    | _ -> assert false) = Some true);

  (* Copying and restricted execution are separate: congruence can use a copy
     with ordinary reduction infos. A frozen fixpoint must retain its shape
     mark even though policy-dependent neutral cells are reactivated. *)
  let frozen, stack = whd_stack infos (create_tab ()) (inject fix) [] in
  assert (stack = []);
  assert (snapshot [frozen] (fun _ -> function
    | [copy] -> ignore (whd_stack infos (create_tab ()) copy []); Some true
    | _ -> assert false) = Some true);

  (* Looking up an environment-relative definition used to lift its whole
     expanded syntax before the query's head-step budget could apply. *)
  let raw = ref (mkRel 1) in
  for _ = 1 to 20 do raw := mkApp (node, [|!raw; !raw|]) done;
  let local_query body =
    let env = Environ.push_rel
      (Context.Rel.Declaration.LocalDef (binder, body, mkProp)) Environ.empty_env in
    let infos = create_clos_infos RedFlags.all env in
    with_closure_snapshot ~steps:128 infos [inject (mkRel 1)] (fun infos -> function
      | [copy] -> ignore (whd_stack infos (create_tab ()) copy []); Some true
      | _ -> assert false) in
  assert (local_query mkProp = Some true);
  assert (local_query !raw = None);

  (* A query view is not itself a typed declaration. A projection over a
     partial or mismatched constructor must decline before array indexing. *)
  let path = Names.ModPath.MPfile (Names.DirPath.make [Names.Id.of_string "Snapshot"] ) in
  let ind name = Names.MutInd.make2 path (Names.Id.of_string name), 0 in
  let record = ind "Record" in
  let constructor = inject (mkConstructU ((record, 1), UVars.Instance.empty)) in
  let projection record index =
    Zproj (Names.Projection.Repr.make record ~proj_npars:0 ~proj_arg:index,
           Sorts.Relevant) in
  let query constructor projection = snapshot [constructor] (fun infos -> function
    | [copy] ->
      let head, stack = whd_stack infos (create_tab ()) copy [projection] in
      Some (term_of_process head stack)
    | _ -> assert false) in
  assert (query constructor (projection record 0) = None);
  let applied = zip constructor [Zapp [|inject mkProp|]] in
  assert (query applied (projection record 0) = Some mkProp);
  assert (query applied (projection record 1) = None);
  assert (query applied (projection (ind "Different") 0) = None);

  (* Constructor cases use the head-machine budget, never quote the unchosen
     branch, and never invoke the unbounded case-inversion conversion hook. *)
  let ci = { ci_ind = record; ci_npar = 0;
    ci_cstr_ndecls = [|0; 0|]; ci_cstr_nargs = [|0; 0|];
    ci_pp_info = {style = MatchStyle} } in
  let predicate = (([|binder|], mkSet), Sorts.Relevant) in
  let case ci inv subject branches = inject (mkCase
    (ci, UVars.Instance.empty, [||], predicate, inv, subject, branches)) in
  let value = mkConstructU ((record, 1), UVars.Instance.empty) in
  let branches = [|([||], mkProp); ([||], mkApp (omega, [|omega|]))|] in
  let ordinary = case ci NoInvert value branches in
  let before = fterm_of ordinary in
  let run ?(steps=4096) term = snapshot ~steps [term] (fun infos -> function
    | [copy] -> Some (reduce infos copy)
    | _ -> assert false) in
  (* Structural fix reduction uses the same isolated cells and fuel as beta
     and constructor cases. An unchosen recursive body is never traversed. *)
  let family = mkFix (([|0|], 0), ([|binder|], [|mkProp|],
      [|mkLambda (binder, mkProp, mkProp)|])) in
  let applied_family = inject (mkApp (family, [|value|])) in
  let before_family = fterm_of applied_family in
  assert (run applied_family = Some mkProp);
  assert (fterm_of applied_family == before_family);
  let frozen_family, _ = whd_stack infos (create_tab ()) (inject family) [] in
  assert (run (zip frozen_family [Zapp [|inject value|]]) = Some mkProp);
  let looping_body = mkLambda (binder, mkProp, mkApp (mkRel 2, [|mkRel 1|])) in
  let looping_fix = mkFix (([|0|], 0), ([|binder|], [|mkProp|], [|looping_body|])) in
  let looping = inject (mkApp (looping_fix, [|value|])) in
  let before_looping = fterm_of looping in
  assert (run ~steps:128 looping = None);
  assert (fterm_of looping == before_looping);
  let mutual = mkFix (([|0; 0|], 1), ([|binder; binder|], [|mkProp; mkProp|],
      [|looping_body; mkLambda (binder, mkProp, mkProp)|])) in
  assert (run (inject (mkApp (mutual, [|value|]))) = Some mkProp);
  (* Validate raw query interfaces before indexing or allocating their spines. *)
  let malformed recargs index names types bodies =
    run (inject (mkFix ((recargs, index), (names, types, bodies)))) in
  assert (malformed [||] 0 [|binder|] [|mkProp|] [|mkProp|] = None);
  assert (malformed [|0|] 1 [|binder|] [|mkProp|] [|mkProp|] = None);
  assert (malformed [|-1|] 0 [|binder|] [|mkProp|] [|mkProp|] = None);
  assert (malformed [|0|] 0 [||] [|mkProp|] [|mkProp|] = None);
  assert (malformed [|0|] 0 [|binder|] [||] [|mkProp|] = None);
  let width = 5000 in
  let wide = mkFix ((Array.make width 0, 0),
      (Array.make width binder, Array.make width mkProp, Array.make width mkProp)) in
  assert (run ~steps:128 (inject wide) = None);
  let arguments = Array.make width (inject value) in
  assert (snapshot ~steps:128 [inject family] (fun infos -> function
    | [copy] -> ignore (whd_stack infos (create_tab ()) copy [Zapp arguments]); Some true
    | _ -> assert false) = None);
  (* Cofixpoints and inversion hooks remain excluded from restricted queries. *)
  let cofix = mkCoFix (0, ([|binder|], [|mkProp|], [|mkProp|])) in
  assert (run (inject cofix) = None);
  assert (run ordinary = Some mkProp);
  assert (fterm_of ordinary == before);
  assert (run (zip (inject value) [ZcaseT
    (ci, UVars.Instance.empty, [||], predicate, branches, identity)]) = Some mkProp);
  assert (run (case ci NoInvert
    (mkConstructU ((record, 2), UVars.Instance.empty)) branches) = None);
  assert (run (case ci (CaseInvert {indices = [||]}) value branches) = None);
  assert (run (case ci NoInvert
    (mkConstructU ((record, 3), UVars.Instance.empty)) branches) = None);
  assert (run (case ci NoInvert
    (mkConstructU ((ind "Different", 1), UVars.Instance.empty)) branches) = None);
  assert (run (case {ci with ci_cstr_nargs = [|1; 0|]} NoInvert value branches) = None);
  assert (run (case ci NoInvert value [||]) = None);
  assert (run (case ci NoInvert value [|([||], mkProp)|]) = None);
  let deep = ref mkProp in
  for _ = 1 to 1000 do
    deep := mkCase (ci, UVars.Instance.empty, [||], predicate, NoInvert,
      value, [|([||], !deep); ([||], mkProp)|])
  done;
  assert (run ~steps:100 (inject !deep) = None);
  Printf.printf "closure snapshots: PASS (50-level DAG, %.0f bytes)\n%!" allocated
