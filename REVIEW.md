# Evaluate registered Peano arithmetic using compact closures

Base: `review/reduction-registrations`. Compare against this base, not upstream.

Keep large Peano values compact inside reduction and expose zero/successor only when elimination needs it. Includes a read-only substitution inspection used to recognize eligible closed operations without copying or reducing their arguments. Motivating imports include Int32.toInt_lt and Int32.ofInt_tdiv. No new source-term constructor is added; the registered definitions remain the specification. Arithmetic/registration controls are in compact_peano.v; closure_inspection.ml tests the read-only substitution view.

## Validation

Not rebuilt at this split head. Earlier checks cover the combined experimental sources, not this intermediate branch.

This is an experimental review branch, not a claim of a complete cslib check.
