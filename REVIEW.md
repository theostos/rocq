# Preserve the remaining kernel experiment diagnostics

Base: `review/conversion-strategies`. Compare against this base, not upstream.

Reproduce the exact experimental source snapshot, including opt-in type/error traces and the ROCQ_DIAGNOSTIC_IGNORE_VO_DIGEST escape hatch. The digest bypass is diagnostic-only and must not be enabled for a checking result or proposed as a production fix. This branch is for reproducing the experiment, not an upstream PR.

## Validation

Not rebuilt at this split head. Earlier checks cover the combined experimental sources, not this intermediate branch.

This is an experimental review branch, not a claim of a complete cslib check.
