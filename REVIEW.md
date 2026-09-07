# Bound dependency-query storage

Base: `f756383de2e66f63c95815c73838596d7d97c1c2`. Compare against this base, not upstream.

Cache direct definition edges and bounded reachability answers instead of transitive closures. Scan shared bodies once per physical node. This addresses dependency-cache growth during the cslib import; optional scalar diagnostics remain with the cache.

## Validation

Not rebuilt at this split head. Earlier checks cover the combined experimental sources, not this intermediate branch.

This is an experimental review branch, not a claim of a complete cslib check.
