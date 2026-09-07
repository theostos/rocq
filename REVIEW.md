# Kernel diagnostic snapshot

Base: `fix/bounded-congruence` (`1ff9ec82b3`).

This carries the existing `review/kernel-diagnostics` changes over the six
subsequent conversion fixes. It adds tracing and diagnostic switches, not a
new production fix. In particular, `ROCQ_DIAGNOSTIC_IGNORE_VO_DIGEST` bypasses
module digest checks: never enable it for a verification result.

The active `String.utf8EncodeChar.eq_def` repair is excluded. The seven copied
implementation files match the earlier diagnostic commit. No clean rebuild
of this review head was launched while the repair owns the compiler.
