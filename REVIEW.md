# Guide conversion through dependencies and shared projections

Base: `review/unit-eta`. Compare against this base, not upstream.

Prefer useful dependency/constructor unfolding, try projection congruence, respect constructor-field relevance and memoize successful typed comparisons with their lift/context. Motivating imports include Int32.toBitVec_not, Std.DHashMap.Internal.Raw₀.Const.insertManyIfNewUnit_cons and Lean.Widget.MsgEmbed._sizeOf_2_eq. Includes the experimental strategy switches and tracing embedded in conversion; these still need cleanup and kernel-expert review. The unit-eta rules are in the base branch.

## Validation

Not rebuilt at this split head. Earlier checks cover the combined experimental sources, not this intermediate branch.

This is an experimental review branch, not a claim of a complete cslib check.
