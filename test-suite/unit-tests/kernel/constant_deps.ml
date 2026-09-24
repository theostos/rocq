open Names
open Constr
open Declarations

let path = ModPath.MPfile (DirPath.make [Id.of_string "DependencyTest"])
let name s = Constant.make2 path (Id.of_string s)
let term c = mkConstU (c, UVars.Instance.empty)

let depends env source target =
  match Environ.constant_depends_on env source target with
  | Some answer -> answer
  | None -> failwith "unexpected dependency-query exhaustion"

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
  (* Many absent targets must not disturb earlier cached memberships. *)
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
  let n = 160 in
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
        (depends !env constants.(i) constants.(j)))
    done
  done

let check_cache_lifetime () =
  let a, b = name "fork_a", name "fork_b" in
  let x, y = name "fork_x", name "fork_y" in
  let base = Environ.empty_env |> add a (Undef None) |> add b (Undef None) in
  let left = add x (Def (term a)) base in
  let right = add y (Def (term b)) base in
  (* These independent forks must not share mutable cache updates. *)
  assert (depends left x a);
  assert (depends right y b);
  assert (not (depends left x b));
  assert (not (depends right y a));
  assert (depends left x a);
  assert (not (depends base x a));
  (* A cached reference to a missing name must not hide its newly added body. *)
  let missing = name "forward_reference" in
  let before = add x (Def (term missing)) base in
  assert (depends before x missing);
  assert (not (depends before x a));
  let after = add missing (Def (term a)) before in
  assert (depends after x a);
  assert (not (depends before x a));
  (* Ephemeron contents are process-local and absent after unmarshalling. *)
  let reloaded = Marshal.from_string (Marshal.to_string after []) 0 in
  assert (depends reloaded x a);
  assert (not (depends reloaded x b));
  assert (depends after x a)

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
    assert (Bool.equal (depends env source target)
      (Cset_env.mem target expected)))
    [absent; a; b; c; d; unused; source]

let check_budget () =
  let root, a, b, f = name "budget_root", name "budget_a",
    name "budget_b", name "budget_f" in
  let body = ref (term a) in
  for _ = 1 to 100 do body := mkApp (term f, [|!body|]) done;
  let env = Environ.empty_env |> add a (Undef None) |> add b (Undef None)
    |> add f (Undef None) |> add root (Def !body) in
  let query = Environ.constant_depends_on in
  List.iter (fun target ->
    let fuel = ref 8 in
    assert (query ~fuel env root target = None);
    assert (!fuel = 0)) [a; b];
  (* An incomplete adjacency scan must not poison either sign of the answer. *)
  assert (query env root a = Some true);
  assert (query env root b = Some false);
  List.iter (fun n ->
    let fuel = ref n in
    assert (query ~fuel env root a = None);
    assert (!fuel = n)) [0; -1];
  (* Warm hits also debit the common allowance. *)
  let fuel = ref 1 in
  assert (query ~fuel env root a = Some true);
  assert (query ~fuel env root b = None);
  assert (!fuel = 0);
  (* Extremely wide terms must not allocate an unbounded traversal worklist. *)
  let wide = name "wide_budget" in
  let env = add wide (Def (mkApp (term f, Array.make 200_000 (term a)))) env in
  let fuel = ref 16 in
  let before = Gc.allocated_bytes () in
  assert (query ~fuel env wide a = None);
  let allocated = Gc.allocated_bytes () -. before in
  assert (allocated < 100_000.);
  (* Syntactic cycles cannot occur in checked constants, but inspection must
     still terminate on an unsafe diagnostic environment. *)
  let x, y = name "cycle_x", name "cycle_y" in
  let cyclic = env |> add x (Def (term y)) |> add y (Def (term x)) in
  assert (query cyclic x x = Some true);
  assert (query cyclic x b = Some false)

let check_answer_storage () =
  let source, a = name "storage_source", name "storage_leaf" in
  let env = Environ.empty_env |> add a (Undef None) |> add source (Def (term a)) in
  Gc.full_major ();
  let before = (Gc.stat ()).live_words in
  for i = 0 to 49_999 do
    assert (not (depends env source (name ("storage_absent" ^ string_of_int i))))
  done;
  Gc.full_major ();
  let retained = (Gc.stat ()).live_words - before in
  (* Name objects and negative-answer nodes must not accumulate per query. *)
  assert (retained < 500_000);
  assert (depends (Sys.opaque_identity env) source a)

let check_direct_storage () =
  let leaves = Array.init 32 (fun i -> name ("storage_edge" ^ string_of_int i)) in
  let sources = Array.init 20_000 (fun i -> name ("storage_node" ^ string_of_int i)) in
  let body = mkApp (mkProp, Array.map term leaves) in
  let env = Array.fold_left (fun env c -> add c (Undef None) env)
    Environ.empty_env leaves in
  let env = Array.fold_left (fun env c -> add c (Def body) env) env sources in
  let absent = name "storage_unreachable" in
  Gc.full_major ();
  let before = (Gc.stat ()).live_words in
  Array.iter (fun source -> assert (not (depends env source absent))) sources;
  Gc.full_major ();
  let retained = (Gc.stat ()).live_words - before in
  (* Direct-edge storage is capped by edges, not just by declaration count.
     Without the cap these 640,000 edges retain several million words. *)
  assert (retained < 700_000);
  let env = Sys.opaque_identity env in
  Array.iter (fun i -> assert (depends env sources.(i) leaves.(i mod 32)))
    [|0; 8191; 19_999|]

let check_overlapping_searches () =
  let chain = Array.init 1000 (fun i -> name ("overlap" ^ string_of_int i)) in
  let target = name "overlap_absent" in
  let env = ref (add chain.(0) (Undef None) Environ.empty_env) in
  for i = 1 to Array.length chain - 1 do
    env := add chain.(i) (Def (term chain.(i - 1))) !env
  done;
  let tail = chain.(Array.length chain - 1) in
  assert (not (depends !env tail target));
  let before = !env in
  (* New roots share an already completed subgraph. Warm answers must survive
     ordinary extensions, and the graph walker must consult them internally. *)
  for i = 0 to 999 do
    let source = name ("new_root" ^ string_of_int i) in
    env := add source (Def (term tail)) !env;
    assert (Environ.constant_depends_on ~fuel:(ref 16) !env source target = Some false)
  done;
  let after = add chain.(500) (Def (term target)) !env in
  assert (depends after tail target);
  assert (not (depends before tail target));
  (* A back edge is not a completed negative subgraph: another branch of its
     ancestor can still reach the target. *)
  let a, b, c = name "cycle_root", name "z_cycle_branch", name "a_cycle_exit" in
  let cyclic = Environ.empty_env |> add target (Undef None)
    |> add a (Def (mkApp (term b, [|term c|])))
    |> add b (Def (term a)) |> add c (Def (term target)) in
  assert (depends cyclic a target);
  assert (depends cyclic b target)

let check_unstable_answer_eviction () =
  let target, missing, child, root = name "eviction_target", name "eviction_missing",
    name "zz_eviction_child", name "eviction_root" in
  let branches = Array.init 9000 (fun i -> name ("eviction_branch" ^ string_of_int i)) in
  let env = Array.fold_left (fun env c -> add c (Def mkProp) env)
      (add target (Undef None) Environ.empty_env) branches in
  let env = env |> add child (Def (term missing))
    |> add root (Def (mkApp (term child, Array.map term branches))) in
  assert (not (depends env child target));
  (* The unstable cached child is visited first; the rest of the graph evicts
     that cache entry. The derived root answer must retain its instability. *)
  assert (Environ.constant_depends_on ~fuel:(ref 200_000) env root target = Some false);
  let extended = add missing (Def (term target)) env in
  assert (Environ.constant_depends_on ~fuel:(ref 200_000) extended root target = Some true)

let check_certified_heights () =
  let a = Array.init 1000 (fun i -> name ("height_a" ^ string_of_int i)) in
  let b = Array.init 1000 (fun i -> name ("height_b" ^ string_of_int i)) in
  let build nodes env =
    let env = ref (add nodes.(0) (Undef None) env) in
    for i = 1 to Array.length nodes - 1 do
      env := add nodes.(i) (Def (term nodes.(i - 1))) !env
    done;
    !env in
  let env = Environ.empty_env |> build a |> build b in
  let absent = name "height_absent" in
  let a_top, b_top = a.(999), b.(999) in
  assert (not (depends env a_top absent));
  assert (not (depends env b_top absent));
  (* Equal-height DAG roots cannot reach each other. Neither source/target
     pair has been queried before, and two units cannot traverse either DAG. *)
  assert (Environ.constant_depends_on ~fuel:(ref 2) env a_top b_top = Some false);
  assert (Environ.constant_depends_on ~fuel:(ref 2) env b_top a_top = Some false);
  assert (depends env a_top a.(500));
  let changed = add a.(500) (Def (term b_top)) env in
  assert (depends changed a_top b_top);
  assert (not (depends env a_top b_top));
  (* A cached negative through a missing reference cannot certify a height. *)
  let missing, source = name "height_missing", name "height_forward" in
  let env = add source (Def (term missing)) env in
  assert (not (depends env source absent));
  assert (Environ.constant_depends_on ~fuel:(ref 2) env source b_top = None);
  let parent = name "height_forward_parent" in
  let env = add parent (Def (term source)) env in
  assert (not (depends env parent absent));
  assert (Environ.constant_depends_on ~fuel:(ref 2) env parent b_top = None);
  let extended = add missing (Def (term b_top)) env in
  assert (depends extended source b_top);
  assert (depends extended parent b_top);
  (* Partial scans cannot leave an underestimated root height. *)
  let partial = name "height_partial" in
  let env = add partial (Def (term a_top)) env in
  assert (Environ.constant_depends_on ~fuel:(ref 2) env partial absent = None);
  assert (depends env partial a.(500));
  (* No member of a cycle may receive a finite certified height. *)
  let x, y = name "height_cycle_x", name "height_cycle_y" in
  let cyclic = env |> add x (Def (term y)) |> add y (Def (term x)) in
  assert (not (depends cyclic x absent));
  assert (depends cyclic x y);
  assert (depends cyclic y x)

let check_height_eviction () =
  let leaves = Array.init 70_000 (fun i -> name ("height_storage" ^ string_of_int i)) in
  let env = Array.fold_left (fun env c -> add c (Undef None) env)
      Environ.empty_env leaves in
  let absent = name "height_storage_absent" in
  Gc.full_major ();
  let before = (Gc.stat ()).live_words in
  Array.iter (fun leaf -> assert (not (depends env leaf absent))) leaves;
  Gc.full_major ();
  let retained = (Gc.stat ()).live_words - before in
  assert (retained < 700_000);
  let env = Sys.opaque_identity env in
  assert (Environ.constant_depends_on ~fuel:(ref 2) env leaves.(69_999) leaves.(69_998) = Some false);
  assert (Environ.constant_depends_on ~fuel:(ref 2) env leaves.(0) leaves.(69_998) = None);
  assert (not (depends env leaves.(0) leaves.(69_998)))

let () =
  check_semantics ();
  check_dag ();
  check_cache_lifetime ();
  check_shared_binders ();
  check_budget ();
  check_answer_storage ();
  check_direct_storage ();
  check_overlapping_searches ();
  check_unstable_answer_eviction ();
  check_certified_heights ();
  check_height_eviction ()
