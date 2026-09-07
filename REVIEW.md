# Recognize direct references in dependency-guided unfolding

Base: `review/conversion-strategies`. Compare against this base, not upstream.

The dependency probe ignored a direct occurrence of its target constant. In
`Std.HashMap.unitOfList_cons`, this made conversion unfold the DHashMap
implementation instead of the HashMap wrapper, causing a 600s timeout.

Count the target itself as a dependency witness, alongside constants whose
bodies depend on it. This changes unfolding order, not the conversion rules.

## Validation

The unchanged theorem times out in a 30s dependency-only reproduction before
the fix and passes afterwards (about 2s). A fresh import of all 2,032 dependency
entries also passes. `direct_unfolding_dependency.v` is a Rocq-only regression:
it times out before the fix, passes in both directions afterwards, and includes
a negative check. `exact_no_check` leaves validation to the kernel at `Qed`.

These checks use the combined experimental kernel with this exact correction,
not a separate clean build of this review branch.

The full cslib continuation has not been rerun. The inherited experimental
kernel changes still need review.
