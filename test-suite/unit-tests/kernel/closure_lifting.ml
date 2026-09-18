open Constr
open CClosure

let () =
  let path = Names.ModPath.MPfile (Names.DirPath.make [Names.Id.of_string "Lifting"]) in
  let ind = Names.MutInd.make2 path (Names.Id.of_string "Node"), 0 in
  let ctor = inject (mkConstructU ((ind, 1), UVars.Instance.empty)) in
  let leaf = mk_clos (Esubst.subs_id 1, UVars.Instance.empty) (mkRel 1) in
  let node child = zip ctor [Zapp [|child; child|]] in
  let term = ref leaf in
  for _ = 1 to 20 do term := node !term done;
  let before = Gc.allocated_bytes () in
  let lifted = zip !term [Zshift 3] in
  let allocated = Gc.allocated_bytes () -. before in
  Printf.printf "closure lifting allocation: %.0f bytes\n%!" allocated;
  let rec check depth term = match fterm_of term with
    | FConstruct (_, args) when depth > 0 ->
      assert (args.(0) == args.(1));
      check (depth - 1) args.(0)
    | FRel 4 when depth = 0 -> ()
    | _ -> assert false in
  check 20 lifted;
  assert (allocated < 100_000.);
  let small = node (node leaf) in
  let syntax = term_of_fconstr small in
  List.iter (fun shift ->
    let lifted = zip small [Zshift shift] in
    assert (Constr.equal (term_of_fconstr lifted) (Vars.lift shift syntax))) [0; 1; 5];
  (* The same source can be reached with different shifts in one traversal.
     Form a delayed shift before the ordinary constructor update occurs. *)
  let suspended = mk_clos (Esubst.subs_id 1, UVars.Instance.empty)
      (mkApp (mkConstructU ((ind, 1), UVars.Instance.empty), [|mkRel 1; mkRel 1|])) in
  let delayed = zip suspended [Zshift 1] in
  ignore (zip (node leaf) [Zupdate suspended]);
  let mixed = zip ctor [Zapp [|suspended; delayed|]] in
  let expected = Vars.lift 3 (term_of_fconstr mixed) in
  assert (Constr.equal (term_of_fconstr (zip mixed [Zshift 3])) expected);
  let binder = Context.make_annot Names.Anonymous Sorts.Relevant in
  let under_binder = node (inject (mkLambda (binder, mkProp, mkRel 2))) in
  assert (Constr.equal (term_of_fconstr (zip under_binder [Zshift 3]))
      (Vars.lift 3 (term_of_fconstr under_binder)));
  assert (Constr.equal (term_of_fconstr leaf) (mkRel 1));
  Printf.printf "closure lifting: PASS (20-level constructor DAG, %.0f bytes)\n%!" allocated
