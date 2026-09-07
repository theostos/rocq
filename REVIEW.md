# Support conversion for registered unit-like inductives

Base: `review/compact-peano`. Compare against this base, not upstream.

Recognize neutral inhabitants of registered unindexed single-constructor types without runtime-relevant fields, including supported unit-valued projections. This addresses FinLoop totality and LawfulMonadStateOf.modify_eq. Projection parameter substitution stays lazy: reifying an erased proof parameter caused the LinearMap.exists_ne_zero_of_sSup_eq assertion. Dependent projection types are conservatively excluded from the unit query. This is a change to definitional equality, not merely an unfolding heuristic.

## Validation

Not rebuilt at this split head. Earlier checks cover the combined experimental sources, not this intermediate branch.

This is an experimental review branch, not a claim of a complete cslib check.
