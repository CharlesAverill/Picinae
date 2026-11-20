These finite maps use the opt-in `critical-seq-v1-base` sequential projection.
Each `_sync_view` preserves DMB/DSB/ISB SY occurrence tags; `_prog` explicitly
forgets those tags. Hardware ordering, completion, pipeline/context visibility,
interrupt delivery/exclusion, termination and function correctness are unproved.
See `notes/e20-armv6m-critical/README.md` for the exact boundary and provenance.
The actual nesting global is memory at 0x20000000, accessed by actual instructions.
`vPortExitCritical` retains the real call to `fixture_assert_fail` at 0x419c.
That callee is absent: the exit call closure remains blocked on e23/r44.
