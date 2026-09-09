# Rocq kernel review stack

Check original Lean proofs through `rocq-lean-import`; no library theorem is
rewritten. These are experimental Rocq changes, separate from the importer PRs.

Review each branch against its stated base, not the whole stack against upstream.
The baseline is `f756383de2e66f63c95815c73838596d7d97c1c2` (Rocq 9.3 development).
The cleaned stack is published on [theostos/rocq](https://github.com/theostos/rocq).

| Branch | Review base |
| --- | --- |
| `review/dependency-cache` | `f756383de2` |
| `review/term-sharing` | `review/dependency-cache` |
| `review/reduction-registrations` | `review/term-sharing` |
| `review/compact-peano` | `review/reduction-registrations` |
| `review/unit-eta` | `review/compact-peano` |
| `review/conversion-strategies` | `review/unit-eta` |

## PR text

### dependency-cache — Bound dependency-query storage

Cache direct definition dependencies and bounded reachability answers instead
of retaining transitive closures. This reduces memory retained by the unfolding
heuristic during large imports; a 1,500-definition chain went from 94.5 MiB to
0.26 MiB in the isolated cache benchmark.

This is a resource fix, not an independently attributed cslib typing error.
Measurement: `rocq-lean-arena/work/cslib-v2/README.md`.

### term-sharing — Preserve sharing during kernel term traversals

Memoize hash-consing and universe traversals so shared proof subterms are not
revisited as separate trees. This supports large imported proof DAGs without
changing conversion rules.

No isolated cslib declaration/error is established for this topic alone.

### reduction-registrations — Validate and persist reduction registrations

Add checked registrations for Peano arithmetic and eligible unit-like inductives,
including module substitution and checker replay. This is the common foundation
for the arithmetic and unit-conversion patches below, not a standalone fix.

### compact-peano — Evaluate registered Peano arithmetic without unary expansion

Evaluate registered natural operations using compact closures, retaining a
constructor view for elimination. This addresses `Int32.minValue_div_neg_one`
failing with `Stack overflow`, including computed division/modulus fuel.

Before/after checks: `rocq-lean-arena/work/int32-min-div-repro/README.md`.
Closure inspection also avoids the guarded memory failure at `Int32.ofInt_tdiv`.

### unit-eta — Support conversion for registered unit-like inductives

Recognize inhabitants of eligible registered unit-like types as convertible,
including supported projections. This addresses `LawfulMonadStateOf.modify_eq`
failing with `Illegal application` when comparing identity with a constant
function returning a `PUnit` projection.

Evidence: `rocq-lean-arena/work/unit-projection-repro/README.md`. This extends
definitional equality; ordinary proof irrelevance is not the new feature.

### conversion-strategies — Refine dependency-guided conversion

Refine unfolding order, projection comparisons and bounded speculative
congruence. This addresses `Std.HashMap.unitOfList_cons` and
`Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.go_denote_eq._unary` failing with
`Lean import line timed out`; ordinary reduction and conversion still check equality.

Evidence: `rocq-lean-arena/work/hashmap-unit-cons-repro/README.md` and
`rocq-lean-arena/work/blastadd-unary-repro/README.md`.

## Consolidation

`fix/compact-fueled-arguments` is folded into `review/compact-peano`.
The five other follow-ups (`direct-unfolding-dependency`,
`constructor-wrapper-conversion`, `stuck-record-eta`, `congruence-probe-scope`,
`bounded-congruence`) are folded into `review/conversion-strategies`.
Later runtime corrections belong to those topics too, not additional fix branches.
Diagnostic-only code, including the library-digest bypass, is excluded.
Review notes and regression evidence stay outside the implementation commits.

`draft/binary-peano-zarith` retains the Zarith/default-off proposal separately,
based on `review/reduction-registrations`. It has not been built or tested and
was not used for the cslib run; it must not inherit that result.

Old branches and dirty experiments are preserved as recovery tags under
`archive/kernel-cleanup-20260909/`. Recover one with:

```sh
git fetch fork tag archive/kernel-cleanup-20260909/review/conversion-strategies
git branch recovered-conversion archive/kernel-cleanup-20260909/review/conversion-strategies
```

## Evidence and limits

The fresh cslib run reached its final export declaration and reported `Done!`:
22,828,731 input lines, 253,649 entries. However, its process exited with status
241 and produced no `Full.vo`; successful saving and fresh reload are unverified.
Run evidence: `rocq-lean-arena/work/cslib-from-start/20260908T183629430908Z/`
(`Full.run.log`, `manifest.json`, `result.json`).

Cleanup leaves the live source, binaries and running experiment untouched.
Historical tests apply to the combined runtime, not automatically to each newly
split head. All 21 changed sources parse; 14 implementations typecheck against
existing experimental interfaces. The standalone checker's interfaces were not
built. Rebuild and runtime regression tests remain necessary;
neither reaching EOF nor these tests constitutes a soundness certification.
