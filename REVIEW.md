# Bound speculative congruence before unfolding

Base: `fix/congruence-probe-scope`. Compare against this base.

`UInt32.toUInt64_shiftLeft_of_lt` overflows at cslib export line 16,372,304.
Conversion compares recursor branches involving different large bounds,
although evaluating the original applications would discard those branches.

With the dependency heuristic enabled, limit speculative congruence on
unfoldable definitions to 256 nested, uncached conversion calls. Nested
comparisons share the counter, restoring it on return; only its owner catches
exhaustion and resumes ordinary unfolding. The peeled-application probe uses
the same mechanism. Long, shallow comparisons are not limited by their work.
Opaque and local heads cannot start a budget: without an unfolding fallback,
congruence may be their only valid checking route.

This limits a trial strategy, not whole-proof checking or every reduction
step. No new equality rule, arithmetic operation, importer patch or library
proof replacement.

## Validation

The 117,502-line export of the unchanged theorem and dependencies fails
before the patch and passes afterward, including fresh import and reload.
Six original widening-shift theorems cover UInt8, UInt16, UInt32 and UInt64.

`bounded_congruence.v` reproduces the overflow without the importer. It tests
both comparison directions, binders, wrong results and genuine opacity, plus
long valid comparisons under opaque and local heads.

All 45 selected kernel/importer checks pass under tag `depth-final`, along
with 19 checkpoint-runner unit tests. This includes the earlier HashMap,
integer arithmetic, record eta, binder-scope and nested-inductive regressions.

These checks use the combined experimental kernel with this exact source
delta, not a clean build of this review branch or the full Rocq suite.
Reproduction and logs: arena workspace, `work/uint32-shift-repro`.
Full cslib verification remains incomplete; the inherited kernel needs review.
