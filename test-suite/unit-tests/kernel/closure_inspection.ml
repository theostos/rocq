open Constr
open CClosure

(* Tests of the read-only substitution view, not typing judgments. *)
let identity = Esubst.subs_id 0, UVars.Instance.empty

let same_entry substitution index expected =
  match inspect_substituted_rel substitution index with
  | Some actual -> assert (actual == expected)
  | None -> assert false

let absent substitution index =
  match inspect_substituted_rel substitution index with
  | None -> ()
  | Some _ -> assert false

let () =
  absent identity 1;
  absent (Esubst.subs_id 3, UVars.Instance.empty) 2;
  let closed = inject mkProp in
  let open_term = inject (mkRel 1) in
  let substitution = usubs_cons open_term (usubs_cons closed identity) in
  same_entry substitution 1 open_term;
  same_entry substitution 2 closed;
  absent substitution 3;

  (* A lift must not copy or relocate the returned closure. In particular,
     returning an open term must not be confused with certifying closedness. *)
  let shifted = Esubst.subs_shft (7, fst substitution), snd substitution in
  same_entry shifted 1 open_term;
  same_entry shifted 2 closed;
  assert (Constr.equal (term_of_fconstr open_term) (mkRel 1));
  let lifted = usubs_liftn 2 substitution in
  absent lifted 1;
  absent lifted 2;
  same_entry lifted 3 open_term;
  same_entry lifted 4 closed;
  absent lifted 5;

  (* Looking up a suspended beta-redex must neither reduce it nor replace its
     frozen cell. An unrelated open substitution entry is not visited. *)
  let binder = Context.make_annot Names.Anonymous Sorts.Relevant in
  let redex = mkApp (mkLambda (binder, mkProp, mkRel 1), [|mkProp|]) in
  let suspended = mk_clos substitution redex in
  let before = fterm_of suspended in
  (match before with FCLOS _ -> () | _ -> assert false);
  let entries = usubs_cons suspended substitution in
  for _ = 1 to 1000 do same_entry entries 1 suspended done;
  assert (fterm_of suspended == before);
  (* The regular relocation may be carried separately by a structural
     inspector. In particular, it must not be lost under crossed binders. *)
  let check_relocated substitution index expected =
    match Esubst.expand_rel index (fst substitution),
          inspect_substituted_rel substitution index with
    | Util.Inl (shift, _), Some actual ->
      assert (actual == expected);
      let relocated = Vars.exliftn (Esubst.el_shft shift Esubst.el_id)
          (term_of_fconstr actual) in
      let copied = term_of_fconstr (mk_clos substitution (mkRel index)) in
      assert (Constr.equal relocated copied)
    | _ -> assert false
  in
  check_relocated substitution 1 open_term;
  check_relocated shifted 1 open_term;
  check_relocated lifted 3 open_term;
  check_relocated (Esubst.subs_shft (5, fst entries), snd entries) 1 suspended;
  assert (fterm_of suspended == before)
