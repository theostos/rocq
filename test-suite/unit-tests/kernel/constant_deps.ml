open Names
open Constr
open Declarations

let path = ModPath.MPfile (DirPath.make [Id.of_string "DependencyTest"])
let name s = Constant.make2 path (Id.of_string s)
let term c = mkConstU (c, UVars.Instance.empty)

let add c body env =
  Environ.add_constant c {
    const_hyps = [];
    const_univ_hyps = UVars.Instance.empty;
    const_body = body;
    const_type = mkProp;
    const_relevance = Sorts.Relevant;
    const_body_code = Vmemitcodes.BCconstant;
    const_universes = Monomorphic;
    const_inline_code = false;
    const_typing_flags = Declareops.safe_flags Conv_oracle.empty;
  } env

(* These are dependency graphs, not declarations submitted for typechecking. *)
let check_semantics () =
  let a, b, c, d = name "a", name "b", name "c", name "d" in
  let opaque = fst (Opaqueproof.create DirPath.empty Opaqueproof.empty_opaquetab) in
  let o = name "opaque" in
  let env = Environ.empty_env
    |> add a (Undef None)
    |> add o (OpaqueDef opaque)
    |> add b (Def (term a))
    |> add c (Def (mkApp (term b, [|term o|])))
  in
  let depends = Environ.constant_depends_on in
  assert (depends env c a);
  assert (depends env c b);
  assert (depends env c o);
  assert (not (depends env a a));
  assert (not (depends env c c));
  assert (not (depends env o a));
  assert (not (depends env c d));
  assert (not (depends env d a));
  (* Environment keys use user names, even when canonical names coincide. *)
  let alias = Constant.make (Constant.user (name "alias")) (Constant.canonical a) in
  assert (not (depends env c alias));
  let source_alias =
    Constant.make (Constant.user (name "source_alias")) (Constant.canonical c)
  in
  assert (not (depends env source_alias a));
  (* Exceed the 16,384-answer limit on this tiny graph; correctness cannot
     depend on earlier positive or negative answers remaining cached. *)
  for i = 0 to 16_384 do
    assert (not (depends env c (name ("absent" ^ string_of_int i))))
  done;
  assert (depends env c a);
  assert (not (depends env c alias));
  (* Dependencies inside binder types still count. *)
  let binder = Context.make_annot Anonymous Sorts.Relevant in
  assert (not (depends env d a));
  let extended = add d (Def (mkLambda (binder, term c, mkRel 1))) env in
  assert (depends extended d a);
  assert (not (depends env d a));
  (* Replacing a body must invalidate earlier positive and negative answers,
     without changing an older environment's answers. *)
  assert (depends extended c a);
  assert (not (depends extended b o));
  let replaced = add b (Def (term o)) extended in
  assert (not (depends replaced c a));
  assert (depends replaced b o);
  assert (depends extended c a);
  assert (not (depends extended b o))

let check_dag () =
  let n = 40 in
  let constants = Array.init n (fun i -> name ("dag" ^ string_of_int i)) in
  let reachable = Array.make_matrix n n false in
  let env = ref Environ.empty_env in
  for i = 0 to n - 1 do
    let refs = ref [] in
    for j = 0 to i - 1 do
      if (i + 3 * j) mod 7 = 0 || j = i - 1 && i mod 3 = 0 then begin
        refs := term constants.(j) :: !refs;
        reachable.(i).(j) <- true;
        for k = 0 to j - 1 do
          reachable.(i).(k) <- reachable.(i).(k) || reachable.(j).(k)
        done
      end
    done;
    let body = mkApp (mkProp, Array.of_list !refs) in
    env := add constants.(i) (Def body) !env
  done;
  for i = 0 to n - 1 do
    for j = 0 to n - 1 do
      assert (Bool.equal reachable.(i).(j)
        (Environ.constant_depends_on !env constants.(i) constants.(j)))
    done
  done

let check_shared_binders () =
  let source = name "shared_binders" in
  let a, b = name "shared_type", name "shared_body" in
  let c, d = name "intervening_type", name "intervening_body" in
  let unused, absent = name "unused_binder", name "absent_binder" in
  let binder = Context.make_annot Anonymous Sorts.Relevant in
  let wrap body =
    let body = ref body in
    (* Common prefixes also exercise collisions in shallow physical hashes. *)
    for _ = 1 to 12 do
      body := mkLambda (binder, mkProp, !body)
    done;
    !body
  in
  let shared = wrap (mkProd (binder, term a, term b)) in
  let intervening = wrap (mkProd (binder, term c, term d)) in
  let body = mkLambda (binder, shared,
    mkApp (mkRel 1, [|shared; intervening; shared;
      mkProd (binder, shared, shared)|])) in
  (* Expected references come from the fixture's names, not a term traversal. *)
  let expected = List.fold_left (fun set c -> Cset_env.add c set)
    Cset_env.empty [a; b; c; d] in
  let env = List.fold_left (fun env c -> add c (Undef None) env)
    Environ.empty_env [a; b; c; d; unused]
    |> add source (Def body)
  in
  List.iter (fun target ->
    assert (Bool.equal (Environ.constant_depends_on env source target)
      (Cset_env.mem target expected)))
    [absent; a; b; c; d; unused; source]

let measure_chain () =
  let n = 1500 in
  let constants = Array.init n (fun i -> name ("chain" ^ string_of_int i)) in
  let env = ref (add constants.(0) (Undef None) Environ.empty_env) in
  for i = 1 to n - 1 do
    env := add constants.(i) (Def (term constants.(i - 1))) !env
  done;
  Gc.full_major ();
  let before = (Gc.stat ()).live_words in
  let started = Sys.time () in
  assert (not (Environ.constant_depends_on !env constants.(n - 1) (name "absent")));
  Gc.full_major ();
  let retained = (Gc.stat ()).live_words - before in
  Printf.printf "chain=%d retained_cache_words=%d cpu_seconds=%.3f\n%!"
    n retained (Sys.time () -. started);
  (* Keep the environment/cache reachable through the measurement. *)
  assert (Environ.constant_depends_on (Sys.opaque_identity !env)
    constants.(n - 1) constants.(0));
  let absent = name "absent" in
  let started = Sys.time () in
  for _ = 1 to 1000 do
    assert (not (Environ.constant_depends_on !env constants.(n - 1) absent))
  done;
  Printf.printf "warm_negative_queries=1000 cpu_seconds=%.3f\n%!"
    (Sys.time () -. started)

let measure_term_shape ~shared depth =
  let shape = if shared then "shared_term_dag" else "unshared_term_chain" in
  let source = name (shape ^ "_source") in
  let f = name (shape ^ "_f") in
  let leaf = name (shape ^ "_leaf") in
  let unused = name (shape ^ "_unused") in
  let absent = name (shape ^ "_absent") in
  let body = ref (term leaf) in
  for _ = 1 to depth do
    let child = !body in
    let args = if shared then [|child; child|] else [|child|] in
    body := mkApp (term f, args);
    if shared then begin
      let _, args = destApp !body in
      assert (args.(0) == args.(1))
    end
  done;
  let env = Environ.empty_env
    |> add f (Undef None)
    |> add leaf (Undef None)
    |> add unused (Undef None)
    |> add source (Def !body)
  in
  Gc.full_major ();
  let before = (Gc.stat ()).live_words in
  let collections = (Gc.quick_stat ()).major_collections in
  let started = Sys.time () in
  (* The first query must collect the body's direct edges, even though its
     only reachable constants are [f] and [leaf]. No answer is warmed first. *)
  assert (not (Environ.constant_depends_on env source absent));
  let elapsed = Sys.time () -. started in
  let collections = (Gc.quick_stat ()).major_collections - collections in
  Gc.full_major ();
  let retained = (Gc.stat ()).live_words - before in
  Printf.printf
    "%s_depth=%d cold_cpu_seconds=%.6f major_collections=%d retained_cache_words=%d\n%!"
    shape depth elapsed collections retained;
  (* Also keep the environment live across the retained-memory measurement. *)
  let depends = Environ.constant_depends_on (Sys.opaque_identity env) source in
  List.iter (fun (target, expected) ->
    assert (Bool.equal (depends target) expected))
    [f, true; leaf, true; source, false; unused, false; absent, false]

let () =
  check_semantics ();
  check_dag ();
  check_shared_binders ();
  measure_chain ();
  (* Only 22 application nodes, but a tree traversal visits about 2^22 leaves. *)
  measure_term_shape ~shared:true 22;
  (* Unique application nodes: no repeated subtree to amortize physical-hash
     lookups, and homogeneous prefixes expose shallow-hash collisions. *)
  measure_term_shape ~shared:false 2048;
  Printf.printf "Dependency tests passed.\n%!"
