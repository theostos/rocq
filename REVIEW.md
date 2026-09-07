# Validate and persist experimental reduction registrations

Base: `review/term-sharing`. Compare against this base, not upstream.

Add checked registrations for Peano naturals, arithmetic operations and unit-like inductives. Validate operation equations with compact arithmetic disabled, and carry registrations through modules and the checker. This is the registration layer; the following branches implement the evaluator and unit conversion. Unit eta changes definitional equality and needs separate soundness review.

## Validation

Not rebuilt at this split head. Earlier checks cover the combined experimental sources, not this intermediate branch.

This is an experimental review branch, not a claim of a complete cslib check.
