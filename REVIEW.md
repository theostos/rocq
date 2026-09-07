# Restore record eta after failed unfolding

Base: `fix/constructor-wrapper-conversion`. Compare against this base.

The experimental early-eta probe only recognizes some elimination stacks.
It can miss the record type of a computation stuck on a variable. The
optimization had also removed Rocq's original eta fallback when that variable
cannot unfold, causing valid conversions to be rejected.

Restore that fallback in both directions. This reuses the original
`eta_expand_ind_stack` and field comparison; it adds no new equality rule.
The speculative early probe and constructor-wrapper ordering are unchanged.

## Validation

The original Lean theorem
`Std.Tactic.BVDecide.LRAT.Internal.DefaultFormula.restoreAssignments_performRupCheck_base_case`
fails at cslib export line 15,281,867. Its dependency-only export has 138,299
lines and reproduces the same error before the fix, with or without the
dependency heuristic. Afterward the unchanged theorem passes, including a
fresh import and reload.

`stuck_record_eta.v` reproduces the failure without the importer. It checks
stuck matches and fixpoints in both directions, and rejects unequal fields
and eta for an ordinary non-record inductive.

These tests use the combined experimental kernel with this exact correction,
not a separate clean build of this review branch. Reproduction and logs are
in the arena workspace, `work/lrat-restore-repro`.

No importer or library proof was changed. The full-library check remains
incomplete; the inherited experimental kernel still needs review.
