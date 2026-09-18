(* Full types of stuck eliminations must be recovered, not guessed or erased. *)
open Names
open Constr
open Entries

let () =
  let id = Id.of_string in
  let binder = Context.make_annot (Name (id "A")) Sorts.Relevant in
  let entry names = {
    mind_entry_record = None;
    mind_entry_finite = Declarations.Finite;
    mind_entry_params = [];
    mind_entry_inds = [{
      mind_entry_typename = id "Choice";
      mind_entry_arity = mkSet;
      mind_entry_consnames = List.map id names;
      mind_entry_lc = List.map (fun _ -> mkRel 1) names;
    }];
    mind_entry_universes = Monomorphic_ind_entry;
    mind_entry_variance = None;
    mind_entry_private = None;
  } in
  let _, safe = Safe_typing.start_library (DirPath.make [id "UnitCase"])
      Safe_typing.empty_environment in
  let (choice, _), safe = Safe_typing.add_mind (id "Choice")
      (entry ["left"; "right"]) safe in
  let unit_entry = { (entry ["unit"]) with
    mind_entry_params = [Context.Rel.Declaration.LocalAssum (binder, mkSet)];
    mind_entry_inds = [{
      mind_entry_typename = id "ParamUnit";
      mind_entry_arity = mkSet;
      mind_entry_consnames = [id "unit"];
      mind_entry_lc = [mkApp (mkRel 2, [|mkRel 1|])];
    }];
  } in
  let (unit, _), safe = Safe_typing.add_mind (id "ParamUnit") unit_entry safe in
  let safe = Safe_typing.register_unit_like (unit, 0) safe in
  let var name = mkVar (id name) in
  let assume name typ env = Environ.push_named Environ.ProofVar
      (Context.Named.Declaration.LocalAssum
        (Context.make_annot (id name) Sorts.Relevant, typ)) env in
  let inst = UVars.Instance.empty in
  let typ name = mkApp (mkIndU ((unit, 0), inst), [|var name|]) in
  let ctor name = mkApp (mkConstructU (((unit, 0), 1), inst), [|var name|]) in
  let env = Safe_typing.env_of_safe_env safe |> assume "A" mkSet
      |> assume "B" mkSet |> assume "b" (mkIndU ((choice, 0), inst))
      |> assume "u" (typ "A") in
  let ci = { ci_ind = choice, 0; ci_npar = 0;
    ci_cstr_ndecls = [|0; 0|]; ci_cstr_nargs = [|0; 0|];
    ci_pp_info = { style = MatchStyle } } in
  let case name = mkCase (ci, inst, [||], (([|binder|], typ name), Sorts.Relevant),
      NoInvert, var "b", [|([||], ctor name); ([||], ctor name)|]) in
  List.iter (fun term -> ignore (Typeops.infer env term)) [case "A"; case "B"];
  List.iter (fun conv ->
    let accepted = conv env (case "A") (ctor "A") = Ok () in
    Printf.printf "same-type stuck case/unit constructor accepted: %b\n%!" accepted;
    assert accepted;
    assert (conv env (ctor "A") (case "A") = Ok ());
    assert (conv env (case "A") (var "u") = Ok ());
    assert (conv env (var "u") (case "A") = Ok ());
    assert (conv env (case "B") (ctor "A") = Error ());
    assert (conv env (ctor "A") (case "B") = Error ()))
    [(fun env left right -> Conversion.conv env left right);
     (fun env left right -> Conversion.default_conv Conversion.CONV env left right)];

  (* Independent proof checking compares inferred/declared types through the
     generic API. A lambda exposes a locally bound FRel, rather than the named
     FFlex above; cheap family-only eligibility must not reject its case. *)
  let under_lambda body = mkLambda (binder, mkIndU ((choice, 0), inst),
      Vars.subst_vars [id "b"] body) in
  let left = under_lambda (case "A") in
  let right = under_lambda (ctor "A") in
  List.iter (fun term -> ignore (Typeops.infer env term)) [left; right];
  List.iter (fun conv ->
    assert (conv env left right = Ok ());
    assert (conv env right left = Ok ());
    assert (conv env (under_lambda (case "B")) right = Error ()))
    [(fun env left right -> Conversion.conv env left right);
     (fun env left right -> Conversion.default_conv Conversion.CONV env left right)];

  (* A local/named value's type can itself be a reducible case. Both sides
     must retain full parameters: ParamUnit A and ParamUnit B do not become
     interchangeable just because their inductive family is registered. *)
  let family name scrutinee = mkCase (ci, inst, [||],
    (([|binder|], mkSort Sorts.type1), Sorts.Relevant), NoInvert, scrutinee,
    [|([||], typ name); ([||], mkIndU ((choice, 0), inst))|]) in
  let first = mkConstructU (((choice, 0), 1), inst) in
  let second = mkConstructU (((choice, 0), 2), inst) in
  let computed = family "A" first in
  let env = env |> assume "f" computed |> assume "g" computed
    |> assume "h" (family "B" first) |> assume "n" (family "A" second) in
  List.iter (fun term -> ignore (Typeops.infer env term)) [computed; family "A" second];
  let under_family body = mkLambda (binder, computed, Vars.subst_vars [id "f"] body) in
  List.iter (fun conv ->
    assert (conv env (var "f") (ctor "A") = Ok ());
    assert (conv env (ctor "A") (var "f") = Ok ());
    assert (conv env (var "f") (var "g") = Ok ());
    assert (conv env (var "f") (var "h") = Error ());
    assert (conv env (var "h") (ctor "A") = Error ());
    assert (conv env (var "n") first = Error ());
    assert (conv env (under_family (var "f")) (under_family (ctor "A")) = Ok ());
    assert (conv env (under_family (ctor "A")) (under_family (var "f")) = Ok ()))
    [(fun env left right -> Conversion.conv env left right);
     (fun env left right -> Conversion.default_conv Conversion.CONV env left right)];

  (* The return predicate uses the actual index, not a constructor branch's
     index or an invented neutral. Both compared terms are individually typed. *)
  let indexed_entry = { unit_entry with mind_entry_inds = [{
    mind_entry_typename = id "Indexed";
    mind_entry_arity = mkProd (binder, mkRel 1, mkSet);
    mind_entry_consnames = [id "indexed"];
    mind_entry_lc = [mkProd (binder, mkRel 1,
      mkApp (mkRel 3, [|mkRel 2; mkRel 1|]))];
  }]} in
  let (indexed, _), safe = Safe_typing.add_mind (id "Indexed") indexed_entry safe in
  let family index = mkApp (var "F", [|index|]) in
  let unit_type index = mkApp (mkIndU ((unit, 0), inst), [|family index|]) in
  let unit_value index = mkApp (mkConstructU (((unit, 0), 1), inst), [|family index|]) in
  let env = Safe_typing.env_of_safe_env safe |> assume "A" mkSet
      |> assume "F" (mkProd (binder, var "A", mkSet))
      |> assume "a" (var "A") |> assume "b" (var "A")
      |> assume "r" (mkApp (mkIndU ((indexed, 0), inst), [|var "A"; var "a"|]))
      |> assume "u" (unit_type (var "a")) in
  let ci = {ci with ci_ind = indexed, 0; ci_npar = 1;
    ci_cstr_ndecls = [|1|]; ci_cstr_nargs = [|1|]} in
  let term = mkCase (ci, inst, [|var "A"|],
      (([|binder; binder|], unit_type (mkRel 2)), Sorts.Relevant),
      NoInvert, var "r", [|([|binder|], unit_value (mkRel 1))|]) in
  ignore (Typeops.infer env term);
  List.iter (fun conv ->
    assert (conv env term (unit_value (var "a")) = Ok ());
    assert (conv env (unit_value (var "a")) term = Ok ());
    assert (conv env term (var "u") = Ok ());
    assert (conv env term (unit_value (var "b")) = Error ());
    assert (conv env (unit_value (var "b")) term = Error ()))
    [(fun env left right -> Conversion.conv env left right);
     (fun env left right -> Conversion.default_conv Conversion.CONV env left right)];
  print_endline "case result witnesses: PASS (constant and indexed predicates, both APIs)"
