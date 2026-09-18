open Constr

let name = Context.make_annot Names.Name.Anonymous Sorts.Relevant
let head = mkVar (Names.Id.of_string "f")
let pair left right = mkApp (head, [|left; right|])
let rec dag n leaf = if n = 0 then leaf else
  let child = dag (n - 1) leaf in pair child child

let rec check_dag n leaf term =
  if n = 0 then assert (Constr.equal term leaf) else
  match kind term with
  | App (_, args) ->
    assert (Array.length args = 2 && args.(0) == args.(1));
    check_dag (n - 1) leaf args.(0)
  | _ -> assert false

let rec reference el term = match kind term with
| Rel i -> let j = Esubst.reloc_rel i el in
    if Int.equal i j then term else mkRel j
| _ -> map_with_binders Esubst.el_lift reference el term

let () =
  (* Eighteen levels already distinguish the tree implementation cheaply. *)
  let input = dag 18 (mkRel 1) in
  let before = Gc.allocated_bytes () in
  let result = lift 1 input in
  let allocated = Gc.allocated_bytes () -. before in
  Printf.printf "syntax lifting DAG allocated: %.0f bytes\n%!" allocated;
  check_dag 18 (mkRel 2) result;
  assert (allocated < 1_000_000.);
  check_dag 50 (mkRel 8) (lift 7 (dag 50 (mkRel 1)));

  (* Identical physical input at different binder depths must not share its
     transformed result. Neither may separate relocation operations. *)
  let shared = pair (mkRel 1) (mkRel 2) in
  let input = pair shared (mkLambda (name, mkSet, shared)) in
  let expected = pair (pair (mkRel 2) (mkRel 3))
      (mkLambda (name, mkSet, pair (mkRel 1) (mkRel 3))) in
  assert (Constr.equal (lift 1 input) expected);
  assert (Constr.equal (lift 2 input)
      (reference (Esubst.el_shft 2 Esubst.el_id) input));
  assert (lift 0 input == input);

  (* Differential checks retain the old tree algorithm as an independent
     reference, including case/fix/cofix binder accounting and array children. *)
  let ind = Names.MutInd.make1
      (Names.KerName.make (Names.ModPath.MPfile Names.DirPath.empty)
        (Names.Id.of_string "I")), 0 in
  let ci = { ci_ind = ind; ci_npar = 0;
    ci_cstr_ndecls = [|1; 2|]; ci_cstr_nargs = [|1; 2|];
    ci_pp_info = { style = MatchStyle } } in
  let u = UVars.Instance.empty in
  let rec terms depth =
    if depth = 0 then [mkRel 1; mkRel 3; head; mkSet] else
    List.concat_map (fun t ->
      [pair t t; mkLambda (name, t, t); mkProd (name, t, t);
       mkLetIn (name, t, t, t); mkCast (t, DEFAULTcast, t);
       mkArray (u, [|t; t|], t, t);
       mkFix (([|0; 0|], 1), ([|name; name|], [|t; t|], [|t; t|]));
       mkCoFix (1, ([|name; name|], [|t; t|], [|t; t|]));
       mkCase (ci, u, [||], (([|name|], t), Sorts.Relevant),
         CaseInvert { indices = [|t|] }, t,
         [|([|name|], t); ([|name; name|], t)|])]) (terms (depth - 1)) in
  List.iter (fun term ->
    List.iter (fun el ->
      assert (Constr.equal (exliftn el term) (reference el term)))
      Esubst.[el_shft 1 el_id; el_liftn 2 (el_shft 3 el_id);
              el_shft 2 (el_lift (el_shft 1 el_id))]) (terms 2);
  let large = dag 300 (mkRel 1) in
  Control.interrupt := true;
  let cancelled = Fun.protect ~finally:(fun () -> Control.interrupt := false)
    (fun () -> try ignore (lift 1 large); false with Sys.Break -> true) in
  assert cancelled;
  print_endline "syntax lifting: PASS"
