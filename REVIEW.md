# Evaluate registered Peano arithmetic in binary

Base: `review/reduction-registrations`. Compare against this base, not upstream.

Use Zarith for large Peano values inside reduction; expose zero/successor when elimination needs it. This avoids unary expansion in imports such as `Int32.toInt_lt` and `Int32.ofInt_tdiv`. Registered definitions remain the specification; no source-term constructor is added.

Disabled by default. Enable with `Set Kernel Binary Peano.`; disable with `Unset Kernel Binary Peano.`. The standalone checker requires `-binary-peano`, independently of flags stored in compiled libraries. This puts Zarith/GMP on the enabled evaluator's trusted path.

The new typing flag changes the `.vo` layout. This branch uses a separate format version to reject older artifacts; switching to it requires a clean rebuild, including libraries and the importer.

## Validation

Not built or executed: the active cslib experiment was left untouched. `binary_peano.v` now exercises small arithmetic before enabling the option, large computations while enabled, and ordinary reduction after disabling it.

This is an experimental review branch, not a claim of a complete cslib check.
