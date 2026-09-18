open Constr
open CClosure

let node = inject (mkVar (Names.Id.of_string "node"))
let duplicate child = zip node [Zapp [|child; child|]]

let children term = match kind term with
  | App (_, args) when Array.length args = 2 -> args.(0), args.(1)
  | _ -> assert false

let () =
  (* Reification must preserve a shared closure, not just equivalent syntax. *)
  let child = duplicate (inject (mkRel 1)) in
  let left, right = children (term_of_fconstr (duplicate child)) in
  assert (left == right);

  (* The same closure under different lifts must NOT share the wrong result. *)
  let lifted = zip child [Zshift 3] in
  let root = zip node [Zapp [|child; lifted|]] in
  let left, right = children (term_of_fconstr root) in
  assert (Constr.equal left (mkApp (mkVar (Names.Id.of_string "node"),
    [|mkRel 1; mkRel 1|])));
  assert (Constr.equal right (mkApp (mkVar (Names.Id.of_string "node"),
    [|mkRel 4; mkRel 4|])));

  (* Sharing within a quotation does not create a persistent cross-call cache. *)
  let first = term_of_fconstr child in
  let second = term_of_fconstr child in
  assert (Constr.equal first second);

  (* Substitutions and crossed binders are part of the closure, not a global
     quotation context. Compare small examples with ordinary substitution. *)
  let binder = Context.make_annot Names.Anonymous Sorts.Relevant in
  let identity = Esubst.subs_id 0, UVars.Instance.empty in
  let substitution = usubs_cons child identity in
  let child_term = term_of_fconstr child in
  let terms = [mkRel 1; mkRel 2;
    mkApp (mkRel 1, [|mkRel 2|]);
    mkLambda (binder, mkProp, mkApp (mkRel 2, [|mkRel 1|]));
    mkProd (binder, mkProp, mkRel 2);
    mkLetIn (binder, mkRel 1, mkProp, mkRel 2)] in
  List.iter (fun term ->
    let clos = mk_clos substitution term in
    let expected = Vars.subst1 child_term term in
    assert (Constr.equal (term_of_fconstr clos) expected);
    for shift = 0 to 4 do
      assert (Constr.equal (term_of_fconstr (zip clos [Zshift shift]))
        (Vars.lift shift expected))
    done) terms;

  (* A subsequent reduction may update the original cell. A quotation cache
     must not survive that call and return the pre-reduction syntax. *)
  let redex = inject (mkApp (mkLambda (binder, mkProp, mkRel 1),
    [|mkProp|])) in
  let before = term_of_fconstr redex in
  let infos = create_clos_infos RedFlags.all Environ.empty_env in
  let head, stack = whd_stack infos (create_tab ()) redex [] in
  assert (Constr.equal (term_of_process head stack) mkProp);
  assert (not (Constr.equal before (term_of_fconstr redex)));

  let huge = ref (inject (mkRel 1)) in
  for _ = 1 to 40 do huge := duplicate !huge done;
  let before = Gc.allocated_bytes () in
  let quoted = term_of_fconstr !huge in
  let allocated = Gc.allocated_bytes () -. before in
  assert (allocated < 1_000_000.);
  let rec check depth term =
    if depth = 0 then assert (Constr.equal term (mkRel 1))
    else let left, right = children term in
      assert (left == right); check (depth - 1) left
  in
  check 40 quoted;
  Printf.printf "closure quotation sharing: PASS (40 levels, %.0f bytes)\n%!" allocated;

  (* The same DAG can be represented by lazy substitution entries instead of
     explicit applications. Their quotation must share the same call cache. *)
  let syntax = mkApp (mkVar (Names.Id.of_string "node"), [|mkRel 1; mkRel 1|]) in
  let huge = ref (inject (mkRel 1)) in
  for _ = 1 to 40 do huge := mk_clos (usubs_cons !huge identity) syntax done;
  let before = Gc.allocated_bytes () in
  let quoted = term_of_fconstr !huge in
  let allocated = Gc.allocated_bytes () -. before in
  assert (allocated < 1_000_000.);
  check 40 quoted;
  Printf.printf "closure substitution quotation: PASS (40 levels, %.0f bytes)\n%!" allocated;

  (* A single closure can contain an already-shared raw syntax DAG. Caching
     closure cells alone does not preserve sharing while substituting it. *)
  let rec raw_dag depth = if depth = 0 then mkRel 1 else
    let child = raw_dag (depth - 1) in
    mkApp (mkVar (Names.Id.of_string "node"), [|child; child|]) in
  let raw_subst = usubs_cons (inject (mkRel 1)) identity in
  let raw = mk_clos raw_subst (raw_dag 18) in
  let before = Gc.allocated_bytes () in
  let quoted = term_of_fconstr raw in
  let allocated = Gc.allocated_bytes () -. before in
  Printf.printf "raw syntax inside closure quotation: %.0f bytes\n%!" allocated;
  assert (allocated < 1_000_000.);
  check 18 quoted;
  check 50 (term_of_fconstr (mk_clos raw_subst (raw_dag 50)));
  let shared = mkApp (mkVar (Names.Id.of_string "node"), [|mkRel 1; mkRel 2|]) in
  let input = mkApp (mkVar (Names.Id.of_string "node"),
      [|shared; mkLambda (binder, mkProp, shared)|]) in
  let inputs = [input;
    mkArray (UVars.Instance.empty, [|shared; shared|], shared, shared);
    mkFix (([|0; 0|], 0), ([|binder; binder|], [|shared; shared|], [|shared; shared|]));
    mkCoFix (0, ([|binder; binder|], [|shared; shared|], [|shared; shared|]))] in
  List.iter (fun value ->
    let subst = usubs_cons (inject value) identity in
    List.iter (fun input ->
      let result = term_of_fconstr (mk_clos subst input) in
      assert (Constr.equal result (Vars.subst1 value input))) inputs)
    [mkRel 3; mkVar (Names.Id.of_string "replacement")];
  print_endline "raw closure syntax substitution: PASS (DAG, binder contexts, repeated calls)"
