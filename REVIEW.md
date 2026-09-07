# Preserve binder scope in application-congruence probes

Base: `fix/stuck-record-eta`. Compare against this base.

The experimental application-congruence probe reified closures, then used
`inject`, whose substitution has zero local binders. Under a binder, this
mistook a bound `FRel` for an external `RelKey`. Relevance lookup could then
raise `Not_found` in the outer environment.

Apply each side's lift before rebuilding its closure with the current local
binder depth. Compare the rebuilt terms with identity lifts. This retains
the probe's isolated sharing state and ordinary conversion checks; it does
not catch the exception or add an equality rule.

## Validation

The unchanged Lean theorem `List.insertIdx_eraseIdx_of_le` fails at cslib
export line 15,367,062. A 4,380-line dependency-only export reproduces the
same anomaly before the patch and passes afterward, including fresh import
and reload.

`congruence_probe_scope.v` reproduces the anomaly without the importer.
It covers lambdas, eta lifts, external relatives, fixpoint bodies, SProp
binders and products, and rejects equalities between distinct variables.

All 40 selected kernel/importer checks and 19 checkpoint-runner unit tests
pass. These use the combined experimental kernel with this exact source
correction, not a clean build of this review branch or the full Rocq suite.
Reproduction and logs: arena workspace, `work/list-insert-erase-repro`.

No importer or library proof changed. Full cslib verification remains
incomplete; the inherited experimental kernel still needs review.
