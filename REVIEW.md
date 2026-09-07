# Unfold constructor wrappers before record eta

Base: `fix/compact-fueled-arguments`. Compare against this base, not upstream.

When comparing a transparent record wrapper with a constructor, conversion
tried record eta before unfolding the wrapper. The resulting projections
could force an expensive field computation (`UInt32.toInt32_not`).

Prefer ordinary unfolding for syntactic lambda/application-to-constructor
wrappers with application-only stacks. Other bodies, existing eliminations
and opaque constants keep the previous path. No new conversion rule, cache
or importer special case.

## Validation

The original theorem and dependencies export to 22,363 lines. Before the fix,
the target overflows with an 8 MiB diagnostic stack. It passes with the same
stack after the fix, as do fresh imports of all five unsigned-to-signed
complement theorems. A pure Rocq regression times out before the fix, succeeds
after it in both directions, and rejects unequal values and opaque wrappers
at Qed. Reproduction: arena workspace, `work/uint32-not-repro`.

These checks use the combined experimental kernel with this exact correction,
not a separate clean build of this review branch. No library proof or importer
code was changed.

The full cslib continuation has not been rerun. The inherited experimental
kernel changes still need review.
