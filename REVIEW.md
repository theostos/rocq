# Normalize compact division and modulus arguments consistently

Base: `fix/direct-unfolding-dependency`. Compare against this base, not upstream.

Conversion head-reduced a registered division/modulus worker's arguments,
leaving the predecessor of a fuel value such as `S (computed dividend)`
unevaluated. Compact evaluation then failed and ordinary recursive division
could overflow the stack (`Int32.minValue_div_neg_one`).

Use the existing compact-numeral probe, as the reduction machine already does.
Registration validation, arithmetic results and fallback checks are unchanged.

## Validation

The original theorem and dependencies export to 15,560 lines. Before the fix,
the target times out at 30s, or overflows with an 8 MiB diagnostic stack. After
the fix it passes with that same stack (0.82 CPU seconds through import).
Fresh imports of the original Int8/Int16/Int32/Int64 versions pass, along with
six division/modulus controls and three kernel-rejected incorrect results.
The reproduction is in the arena workspace, `work/int32-min-div-repro`.

These checks use the combined experimental kernel with this exact correction,
not a separate clean build of this review branch. No library proof or importer
code was changed.

The full cslib continuation has not been rerun. The inherited experimental
kernel changes still need review.
