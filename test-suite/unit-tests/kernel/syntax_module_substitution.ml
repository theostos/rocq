open Names
open Constr

let path name = ModPath.MPfile (DirPath.make [Id.of_string name])
let constant path = Constant.make2 path (Id.of_string "c")
let mind path = MutInd.make2 path (Id.of_string "I")
let head = mkVar (Id.of_string "f")
let pair l r = mkApp (head, [|l; r|])
let rec dag n leaf = if n = 0 then leaf else
  let child = dag (n - 1) leaf in pair child child
let rec check n leaf term =
  if n = 0 then assert (equal term leaf) else
  match kind term with
  | App (_, args) -> assert (args.(0) == args.(1)); check (n - 1) leaf args.(0)
  | _ -> assert false

let () =
  let a, b, c = path "A", path "B", path "C" in
  let subst source target = Mod_subst.map_mp source target
      (Mod_subst.empty_delta_resolver target) in
  let ab, bc = subst a b, subst b c in
  let rename = Mod_subst.subst_mps ab in
  let u = UVars.Instance.empty in
  let atom path = mkConstU (constant path, u) in
  let array path = mkArray (u, [|atom path; atom path|], atom path,
      mkIndU ((mind path, 0), u)) in
  let mode name = Array.length Sys.argv = 1 || Sys.argv.(1) = name in
  if mode "array" then begin
    assert (equal (rename (array a)) (array b));
    assert (equal (Mod_subst.subst_mps_list [bc; ab] (array a)) (array c));
    print_endline "module substitution array: PASS"
  end;
  if mode "dag" then begin
    let input = dag 18 (atom a) in
    let before = Gc.allocated_bytes () in
    let result = rename input in
    let bytes = Gc.allocated_bytes () -. before in
    Printf.printf "module substitution DAG allocated: %.0f bytes\n%!" bytes;
    assert (bytes < 1_000_000.);
    check 18 (atom b) result;
    check 50 (atom b) (rename (dag 50 (atom a)));
    let unchanged = dag 50 (mkRel 1) in
    assert (rename unchanged == unchanged);
    assert (Mod_subst.subst_mps Mod_subst.empty_subst input == input);
    assert (equal (Mod_subst.subst_mps (Mod_subst.join ab bc) (array a)) (array c));
    print_endline "module substitution DAG: PASS"
  end;
  if mode "metadata" then begin
    let name = Context.make_annot Name.Anonymous Sorts.Relevant in
    let projection path = Projection.make
      (Projection.Repr.make (mind path, 0) ~proj_npars:0 ~proj_arg:0) true in
    let ci path = { ci_ind = mind path, 0; ci_npar = 0;
      ci_cstr_ndecls = [|1|]; ci_cstr_nargs = [|1|];
      ci_pp_info = { style = MatchStyle } } in
    let shape path =
      let atom = atom path in
      mkCase (ci path, u, [|atom|], (([|name|], atom), Sorts.Relevant),
        CaseInvert { indices = [|atom|] }, mkProj (projection path, Sorts.Relevant, atom),
        [|([|name|], mkApp (mkConstructU (((mind path, 0), 1), u), [|atom|]))|]) in
    assert (equal (rename (shape a)) (shape b));
    let instance n = UVars.Instance.of_array ([||], [|Univ.Level.var n|]) in
    let atoms path = pair (mkConstU (constant path, instance 0))
        (mkConstU (constant path, instance 1)) in
    assert (equal (rename (atoms a)) (atoms b));
    let large = dag 300 (atom a) in
    Control.interrupt := true;
    let cancelled = Fun.protect ~finally:(fun () -> Control.interrupt := false)
      (fun () -> try ignore (rename large); false with Sys.Break -> true) in
    assert cancelled;
    print_endline "module substitution metadata: PASS"
  end
