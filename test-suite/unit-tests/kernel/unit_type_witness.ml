open Names
open Constr
open Entries

let () =
  let id = Id.of_string in
  let binder = Context.make_annot (Name (id "A")) Sorts.Relevant in
  let entry = {
    mind_entry_record = None;
    mind_entry_finite = Declarations.Finite;
    mind_entry_params = [Context.Rel.Declaration.LocalAssum (binder, mkSet)];
    mind_entry_inds = [{
      mind_entry_typename = id "ParamUnit";
      mind_entry_arity = mkSet;
      mind_entry_consnames = [id "param_unit"];
      mind_entry_lc = [mkApp (mkRel 2, [|mkRel 1|])];
    }];
    mind_entry_universes = Monomorphic_ind_entry;
    mind_entry_variance = None;
    mind_entry_private = None;
  } in
  let _, safe = Safe_typing.start_library (DirPath.make [id "UnitWitness"])
      Safe_typing.empty_environment in
  let (mind, _), safe = Safe_typing.add_mind (id "ParamUnit") entry safe in
  let safe = Safe_typing.register_unit_like (mind, 0) safe in
  let env = Safe_typing.env_of_safe_env safe in
  let assume name typ env =
    Environ.push_named Environ.ProofVar
      (Context.Named.Declaration.LocalAssum
         (Context.make_annot (id name) Sorts.Relevant, typ)) env in
  let unit_at name = mkApp (mkIndU ((mind, 0), UVars.Instance.empty),
    [|mkVar (id name)|]) in
  let env = env |> assume "A" mkSet |> assume "B" mkSet
      |> assume "x" (unit_at "A") |> assume "y" (unit_at "B")
      |> assume "z" (unit_at "A") in
  let accepts a b = match Conversion.conv env a b with
    | Ok () -> true | Error () -> false in
  assert (not (accepts (unit_at "A") (unit_at "B")));
  assert (accepts (mkVar (id "x")) (mkVar (id "z")));
  let incompatible = accepts (mkVar (id "x")) (mkVar (id "y")) in
  Printf.printf "unit comparison at incompatible types accepted: %b\n%!" incompatible;
  assert (not incompatible);

  let ctor_at name = mkApp
      (mkConstructU (((mind, 0), 1), UVars.Instance.empty), [|mkVar (id name)|]) in
  assert (accepts (mkVar (id "x")) (ctor_at "A"));
  assert (accepts (ctor_at "A") (mkVar (id "x")));
  assert (not (accepts (mkVar (id "x")) (ctor_at "B")));
  assert (not (accepts (ctor_at "B") (mkVar (id "x"))));

  (* Record eta must not erase a singleton field before establishing its
     instantiated type. The enclosing record is not globally unit-like. *)
  let box_entry = { entry with
    mind_entry_record = Some (Some [|id "self"|]);
    mind_entry_finite = Declarations.BiFinite;
    mind_entry_inds = [{
      mind_entry_typename = id "WitnessBox";
      mind_entry_arity = mkSet;
      mind_entry_consnames = [id "witness_box"];
      mind_entry_lc = [mkProd (binder, mkRel 1,
        mkApp (mkRel 3, [|mkRel 2|]))];
    }];
  } in
  let (box_mind, _), box_safe = Safe_typing.add_mind
      (id "WitnessBox") box_entry safe in
  let box_at name = mkApp (mkIndU ((box_mind, 0), UVars.Instance.empty),
      [|unit_at name|]) in
  let box_env = Safe_typing.env_of_safe_env box_safe
      |> assume "A" mkSet |> assume "B" mkSet
      |> assume "bx" (box_at "A") |> assume "by" (box_at "B") in
  let boxed = mkApp (mkConstructU (((box_mind, 0), 1), UVars.Instance.empty),
      [|unit_at "A"; ctor_at "A"|]) in
  ignore (Typeops.infer box_env boxed);
  List.iter (fun conv ->
    assert (conv box_env boxed (mkVar (id "bx")) = Ok ());
    assert (conv box_env (mkVar (id "bx")) boxed = Ok ());
    let incompatible = conv box_env boxed (mkVar (id "by")) = Ok () in
    Printf.printf "record eta at incompatible field types accepted: %b\n%!" incompatible;
    assert (not incompatible);
    assert (conv box_env (mkVar (id "by")) boxed = Error ()))
    [(fun env left right -> Conversion.conv env left right);
     (fun env left right -> Conversion.default_conv Conversion.CONV env left right)];

  (* Domain closures are retained before their binders are introduced. Their
     relocations must include all intervening binders when checking unit types. *)
  let unit_rel index = mkApp (mkIndU ((mind, 0), UVars.Instance.empty),
      [|mkRel index|]) in
  let lambda body y_parameter =
    mkLambda (binder, mkSet, mkLambda (binder, mkSet,
      mkLambda (binder, unit_rel 2,
        mkLambda (binder, unit_rel y_parameter, body)))) in
  let left = lambda (mkRel 2) 2 in
  let right = lambda (mkRel 1) 2 in
  ignore (Typeops.infer env left);
  ignore (Typeops.infer env right);
  assert (not (accepts left right));
  assert (accepts (lambda (mkRel 2) 3) (lambda (mkRel 1) 3));
  assert (Conversion.default_conv Conversion.CONV env left right = Error ());
  assert (Conversion.default_conv Conversion.CONV env
    (lambda (mkRel 2) 3) (lambda (mkRel 1) 3) = Ok ());

  (* Reconstructed open types must retain local neutrals, including a neutral
     function at the head of a parameter application. Treating H as an
     environment-relative definition raises Not_found in an empty rel context. *)
  let applied_unit h a = mkApp (mkIndU ((mind, 0), UVars.Instance.empty),
    [|mkApp (mkRel h, [|mkRel a|])|]) in
  let applied_lambda body y_parameter =
    mkLambda (binder, mkProd (binder, mkSet, mkSet),
      mkLambda (binder, mkSet, mkLambda (binder, mkSet,
        mkLambda (binder, applied_unit 3 2,
          mkLambda (binder, applied_unit 4 y_parameter, body))))) in
  let left = applied_lambda (mkRel 2) 2 in
  let right = applied_lambda (mkRel 1) 2 in
  ignore (Typeops.infer env left);
  ignore (Typeops.infer env right);
  assert (not (accepts left right));
  assert (accepts (applied_lambda (mkRel 2) 3) (applied_lambda (mkRel 1) 3));

  (* A projected singleton field can depend on earlier fields of the actual
     record. A dummy scrutinee cannot justify either the type or equality. *)
  let param_unit value = mkApp (mkIndU ((mind, 0), UVars.Instance.empty), [|value|]) in
  let field name = Context.make_annot (Name (id name)) Sorts.Relevant in
  let dep_entry = { entry with
    mind_entry_record = Some (Some [|id "self"|]);
    mind_entry_finite = Declarations.BiFinite;
    mind_entry_params = [
      Context.Rel.Declaration.LocalAssum (field "F", mkProd (binder, mkRel 1, mkSet));
      Context.Rel.Declaration.LocalAssum (binder, mkSet)];
    mind_entry_inds = [{
      mind_entry_typename = id "DependentUnit";
      mind_entry_arity = mkSet;
      mind_entry_consnames = [id "dependent_unit"];
      mind_entry_lc = [mkProd (field "tag", mkRel 2,
        mkProd (field "payload", param_unit (mkApp (mkRel 2, [|mkRel 1|])),
          mkApp (mkRel 5, [|mkRel 4; mkRel 3|])))];
    }];
  } in
  let (dep_mind, _), dep_safe = Safe_typing.add_mind
      (id "DependentUnit") dep_entry safe in
  let dep_env = Safe_typing.env_of_safe_env dep_safe in
  let mib = Environ.lookup_mind dep_mind dep_env in
  let projection index record =
    let repr, relevance = Declareops.inductive_make_projection (dep_mind, 0) mib
        ~proj_arg:index in
    mkProj (Projection.make repr true, relevance, record) in
  let var name = mkVar (id name) in
  let record_type = mkApp (mkIndU ((dep_mind, 0), UVars.Instance.empty),
    [|var "A"; var "F"|]) in
  let payload_type record = param_unit (mkApp (var "F", [|projection 0 record|])) in
  let dep_env = dep_env |> assume "A" mkSet
      |> assume "F" (mkProd (binder, var "A", mkSet))
      |> assume "r" record_type |> assume "s" record_type
      |> assume "x" (payload_type (var "r"))
      |> assume "y" (payload_type (var "s")) in
  let payload = projection 1 (var "r") in
  ignore (Typeops.infer dep_env payload);
  List.iter (fun conv ->
    assert (conv dep_env payload (var "x") = Ok ());
    assert (conv dep_env (var "x") payload = Ok ());
    assert (conv dep_env payload (var "y") = Error ()))
    [(fun env left right -> Conversion.conv env left right);
     (fun env left right -> Conversion.default_conv Conversion.CONV env left right)];
  let dep_env = dep_env
      |> assume "f" (mkProd (binder, var "A", record_type))
      |> assume "a" (var "A") |> assume "b" (var "A") in
  let call name = mkApp (var "f", [|var name|]) in
  let dep_env = dep_env |> assume "fa_payload" (payload_type (call "a"))
      |> assume "fb_payload" (payload_type (call "b")) in
  let payload = projection 1 (call "a") in
  ignore (Typeops.infer dep_env payload);
  assert (Conversion.conv dep_env payload (var "fa_payload") = Ok ());
  assert (Conversion.conv dep_env payload (var "fb_payload") = Error ());

  let univ_context n =
    UVars.AbstractContext.repr (UVars.AbstractContext.make
      { UVars.quals = [||]; univs = Array.make n Anonymous }
      PConstraints.empty) in
  let universe_entry = { entry with
    mind_entry_params = [];
    mind_entry_inds = [{
      mind_entry_typename = id "UniverseUnit";
      mind_entry_arity = mkSort (Sorts.sort_of_univ
        (Univ.Universe.make (Univ.Level.var 0)));
      mind_entry_consnames = [id "universe_unit"];
      mind_entry_lc = [mkRel 1];
    }];
    mind_entry_universes = Polymorphic_ind_entry (univ_context 1);
  } in
  let (univ_mind, _), safe = Safe_typing.add_mind
      (id "UniverseUnit") universe_entry safe in
  let safe = Safe_typing.register_unit_like (univ_mind, 0) safe in
  let unit_at_level n = mkIndU ((univ_mind, 0),
    UVars.Instance.of_array ([||], [|Univ.Level.var n|])) in
  let env = Environ.push_context (univ_context 2) (Safe_typing.env_of_safe_env safe)
    |> assume "u" (unit_at_level 0) |> assume "v" (unit_at_level 1)
    |> assume "w" (unit_at_level 0) in
  assert (Conversion.conv env (unit_at_level 0) (unit_at_level 1) = Error ());
  assert (Conversion.conv env (mkVar (id "u")) (mkVar (id "v")) = Error ());
  assert (Conversion.conv env (mkVar (id "u")) (mkVar (id "w")) = Ok ());

  (* Even an irrelevant field must be supplied before the constructor is an
     inhabitant. No elimination relaxation is needed for this regression. *)
  let proof_binder = { binder with Context.binder_relevance = Sorts.Irrelevant } in
  let proof_type = mkProd (binder, mkSProp,
      mkProd (proof_binder, mkRel 1, mkRel 2)) in
  let proof_value = mkLambda (binder, mkSProp,
      mkLambda (proof_binder, mkRel 1, mkRel 1)) in
  let proof_entry = { entry with mind_entry_inds = [{
    mind_entry_typename = id "ProofUnit";
    mind_entry_arity = mkSet;
    mind_entry_consnames = [id "proof_unit"];
    mind_entry_lc = [mkProd (proof_binder, proof_type,
      mkApp (mkRel 3, [|mkRel 2|]))];
  }]} in
  let (proof_mind, _), safe = Safe_typing.add_mind (id "ProofUnit") proof_entry safe in
  let safe = Safe_typing.register_unit_like (proof_mind, 0) safe in
  let var name = mkVar (id name) in
  let proof_at = mkApp (mkIndU ((proof_mind, 0), UVars.Instance.empty), [|var "A"|]) in
  let env = Safe_typing.env_of_safe_env safe |> assume "A" mkSet |> assume "x" proof_at in
  let ctor = mkConstructU (((proof_mind, 0), 1), UVars.Instance.empty) in
  let partial = mkApp (ctor, [|var "A"|]) in
  let full = mkApp (ctor, [|var "A"; proof_value|]) in
  List.iter (fun term -> ignore (Typeops.infer env term)) [partial; full];
  List.iter (fun conv ->
    assert (conv env full (var "x") = Ok ());
    assert (conv env (var "x") full = Ok ());
    assert (conv env partial (var "x") = Error ());
    assert (conv env (var "x") partial = Error ()))
    [(fun env left right -> Conversion.conv env left right);
     (fun env left right -> Conversion.default_conv Conversion.CONV env left right)];
  print_endline "unit type witness: PASS"
