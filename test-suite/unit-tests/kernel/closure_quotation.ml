open Constr
open CClosure

let node = inject (mkVar (Names.Id.of_string "node"))
let duplicate child = zip node [Zapp [|child; child|]]
let binder = Context.make_annot Names.Anonymous Sorts.Relevant
let identity = Esubst.subs_id 0, UVars.Instance.empty

let children term = match kind term with
  | App (_, args) when Array.length args = 2 -> args.(0), args.(1)
  | _ -> assert false

let rec check depth term =
  if depth = 0 then assert (Constr.equal term (mkRel 1))
  else let left, right = children term in
    assert (left == right); check (depth - 1) left

let () =
  (* Quotation preserves the sharing of a closure. *)
  let child = duplicate (inject (mkRel 1)) in
  let left, right = children (term_of_fconstr (duplicate child)) in
  assert (left == right);
  (* The same closure under different lifts is quoted differently. *)
  let lifted = zip child [Zshift 3] in
  let root = zip node [Zapp [|child; lifted|]] in
  let left, right = children (term_of_fconstr root) in
  assert (Constr.equal left (mkApp (mkVar (Names.Id.of_string "node"),
    [|mkRel 1; mkRel 1|])));
  assert (Constr.equal right (mkApp (mkVar (Names.Id.of_string "node"),
    [|mkRel 4; mkRel 4|])));
  (* Quotation agrees with syntactic substitution and lifting. *)
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
  (* A reduction updating a cell is seen by the next quotation. *)
  let redex = inject (mkApp (mkLambda (binder, mkProp, mkRel 1), [|mkProp|])) in
  let before = term_of_fconstr redex in
  let infos = create_clos_infos RedFlags.all Environ.empty_env in
  let head, stack = whd_stack infos (create_tab ()) redex [] in
  assert (Constr.equal (term_of_process head stack) mkProp);
  assert (not (Constr.equal before (term_of_fconstr redex)));
  (* Deep DAGs of applications, of lazy substitution entries and of raw syntax
     inside one closure are all quoted with their sharing. *)
  let huge = ref (inject (mkRel 1)) in
  for _ = 1 to 40 do huge := duplicate !huge done;
  check 40 (term_of_fconstr !huge);
  let syntax = mkApp (mkVar (Names.Id.of_string "node"), [|mkRel 1; mkRel 1|]) in
  let huge = ref (inject (mkRel 1)) in
  for _ = 1 to 40 do huge := mk_clos (usubs_cons !huge identity) syntax done;
  check 40 (term_of_fconstr !huge);
  let rec raw_dag depth = if depth = 0 then mkRel 1 else
    let child = raw_dag (depth - 1) in
    mkApp (mkVar (Names.Id.of_string "node"), [|child; child|]) in
  let raw_subst = usubs_cons (inject (mkRel 1)) identity in
  check 50 (term_of_fconstr (mk_clos raw_subst (raw_dag 50)));
  (* Substitution in raw syntax respects binder depth in every context. *)
  let shared = mkApp (mkVar (Names.Id.of_string "node"), [|mkRel 1; mkRel 2|]) in
  let inputs = [
    mkApp (mkVar (Names.Id.of_string "node"), [|shared; mkLambda (binder, mkProp, shared)|]);
    mkArray (UVars.Instance.empty, [|shared; shared|], shared, shared);
    mkFix (([|0; 0|], 0), ([|binder; binder|], [|shared; shared|], [|shared; shared|]));
    mkCoFix (0, ([|binder; binder|], [|shared; shared|], [|shared; shared|]))] in
  List.iter (fun value ->
    let subst = usubs_cons (inject value) identity in
    List.iter (fun input ->
      let result = term_of_fconstr (mk_clos subst input) in
      assert (Constr.equal result (Vars.subst1 value input))) inputs)
    [mkRel 3; mkVar (Names.Id.of_string "replacement")]
