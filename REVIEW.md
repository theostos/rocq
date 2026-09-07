# Preserve DAG sharing during kernel term traversals

Base: `review/dependency-cache`. Compare against this base, not upstream.

Memoize hash-consing and universe traversals by physical term and, where needed, binder context. Large imported proof DAGs otherwise repeat the same traversal. These are traversal changes, not additional conversion equations.

## Validation

Not rebuilt at this split head. Earlier checks cover the combined experimental sources, not this intermediate branch.

This is an experimental review branch, not a claim of a complete cslib check.
