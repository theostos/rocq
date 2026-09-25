open Constr

let binder = Context.make_annot Names.Name.Anonymous Sorts.Relevant
let var name = mkVar (Names.Id.of_string name)
let pair left right = mkApp (var "f", [|left; right|])
let rec dag n leaf = if n = 0 then leaf else
  let child = dag (n - 1) leaf in pair child child
let rec check n leaf term =
  if n = 0 then assert (equal term leaf) else
  match kind term with
  | App (_, args) -> assert (args.(0) == args.(1)); check (n - 1) leaf args.(0)
  | _ -> assert false

let debruijn () =
  check 50 (var "x") (Vars.subst1 (var "x") (dag 50 (mkRel 1)));
  let shared = pair (mkRel 1) (mkRel 2) in
  let input = pair shared (mkLambda (binder, mkSet, shared)) in
  let expected = pair (pair (var "x") (mkRel 1))
      (mkLambda (binder, mkSet, pair (mkRel 1) (var "x"))) in
  assert (equal (Vars.subst1 (var "x") input) expected);
  let expected = pair (pair (mkRel 1) (mkRel 1))
      (mkLambda (binder, mkSet, pair (mkRel 1) (mkRel 2))) in
  assert (equal (Vars.subst1 (mkRel 1) input) expected);
  assert (Vars.substl [] input == input);
  (* Multiple substituends, a protected prefix and unaffected higher rels. *)
  let input = mkLambda (binder, mkSet,
    mkApp (var "f", [|mkRel 1; mkRel 2; mkRel 3; mkRel 4; mkRel 5|])) in
  let expected = mkLambda (binder, mkSet,
    mkApp (var "f", [|mkRel 1; mkRel 2; var "x"; var "y"; mkRel 3|])) in
  assert (equal (Vars.substnl [var "x"; var "y"] 1 input) expected)

let named () =
  let replace term = Vars.replace_vars [Names.Id.of_string "x", mkRel 1] term in
  check 50 (mkRel 1) (replace (dag 50 (var "x")));
  let shared = pair (var "x") (var "x") in
  let input = pair shared (mkLambda (binder, mkSet, shared)) in
  let expected = pair (pair (mkRel 1) (mkRel 1))
      (mkLambda (binder, mkSet, pair (mkRel 2) (mkRel 2))) in
  assert (equal (replace input) expected);
  assert (Vars.replace_vars [] input == input)

let universes () =
  let sort n = mkSort (Sorts.sort_of_univ (Univ.Universe.make (Univ.Level.var n))) in
  let instance n = UVars.Instance.of_array ([||], [|Univ.Level.var n|]) in
  let input = dag 50 (sort 0) in
  check 50 (sort 1) (Vars.subst_instance_constr (instance 1) input);
  check 50 (sort 2) (Vars.subst_instance_constr (instance 2) input);
  assert (Vars.subst_instance_constr UVars.Instance.empty input == input);
  (* Repeated array/default/type positions and quality-bearing binder fields. *)
  let input = mkArray (instance 0, [|sort 0; sort 0|], sort 0, sort 0) in
  let expected = mkArray (instance 2, [|sort 2; sort 2|], sort 2, sort 2) in
  assert (equal (Vars.subst_instance_constr (instance 2) input) expected);
  let q = Sorts.QVar.make_var 0 in
  let qbinder = { binder with Context.binder_relevance = Sorts.RelevanceVar q } in
  let input = mkLambda (qbinder, mkSort (Sorts.vsort q Univ.Universe.type0), mkRel 1) in
  let subst = UVars.Instance.of_array ([|Sorts.Quality.qsprop|], [||]) in
  let expected = mkLambda ({ binder with Context.binder_relevance = Sorts.Irrelevant },
    mkSProp, mkRel 1) in
  assert (equal (Vars.subst_instance_constr subst input) expected);
  (* Substituting into an atom allocates no memo table. *)
  let input = sort 0 in
  let before = Gc.allocated_bytes () in
  for _ = 1 to 1000 do ignore (Vars.subst_instance_constr (instance 1) input) done;
  assert (Gc.allocated_bytes () -. before < 450_000.)

let occurrence () =
  let closed = dag 50 (var "x") in
  assert (Vars.closed0 closed);
  assert (Vars.noccurn 1 closed);
  assert (Vars.noccur_between 1 5 closed);
  assert (Vars.noccur_with_meta 1 5 closed);
  let shared = pair (mkRel 1) (mkRel 1) in
  let input = pair (mkLambda (binder, mkSet, shared)) shared in
  assert (not (Vars.closed0 input));
  assert (not (Vars.noccurn 1 input));
  assert (not (Vars.noccur_between 1 1 input));
  assert (not (Vars.noccur_with_meta 1 1 input));
  assert (Vars.closedn 1 input);
  assert (Vars.noccurn 2 input);
  let opaque = mkApp (mkMeta 0, [|mkRel 1|]) in
  assert (Vars.noccur_with_meta 1 1 opaque);
  assert (not (Vars.noccurn 1 opaque));
  let cast_meta = mkApp (mkCast (mkMeta 0, DEFAULTcast, mkSet), [|mkRel 1|]) in
  assert (Vars.noccur_with_meta 1 1 cast_meta);
  Control.interrupt := true;
  let cancelled = Fun.protect ~finally:(fun () -> Control.interrupt := false)
    (fun () -> try ignore (Vars.closed0 (dag 300 (var "x"))); false with Sys.Break -> true) in
  assert cancelled

let () = debruijn (); named (); universes (); occurrence ()
