> Preserved original record. [Original source](https://github.com/kangxyz/motivic/blob/be8e17f5286874bd44942f796b96860b4b924993/docs/PERFORMANCE.md#reuse-the-build-environment) · [Context](original-context.md) · [Case index](README.md) · [Previous record](prove-over-abstract-objects-then-specialize.md) · [Next record](source-and-log-evidence.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Reuse the build environment

Use an ordinary incremental Lake build for changed providers and their actual
consumers, with a bounded batch of independent jobs. Preserve compatible
artifacts in the managed remote workspace. A serialized dependency chain cannot
use all compiler slots; increasing concurrency does not reduce one declaration's
conversion cost.

Run final package tests in the same native build batch. For declaration lint,
import the production umbrella once per configured linter framework and select
declarations in that shared environment. Starting a fresh import environment for
every origin repeats the expensive transitive import work. Generated-entry and
text-style scripts need their actual tool dependencies prepared once; a missing
tool artifact calls for that dependency, not a clean library rebuild. Reuse
successful checks after a repair and rerun only changed inputs, failures and
coverage gaps. Extra replay and downstream builds are separate requested work.

Prefer a compatible compiled checker executable when it is already available.
The pinned Mathlib text-style driver contains an initialization declaration:
directly interpreting its source with `lean --run` spent several minutes
elaborating it and then failed with `cannot evaluate [init] declaration ... in
the same module`. This was a checker-launch failure, not a reported source-style
failure. Its native `mathlib/lint-style` executable, or the packaged runtime
that first compiles the driver and runs an importing shim, handles that boundary.
Read-only tool reuse must match the Lean version, Mathlib revision and exact
driver source; a neighboring library's mathematical artifacts are not substitutes
for this library's compiled subjects.

For a warranted single-file diagnosis, `lake lean path/to/File.lean --
-Dtrace.profiler=true -Dtrace.profiler.threshold=100 -o /fresh/File.olean` builds
only missing imports and supplies Lake's file context. Do not assume a previous
build's temporary `.setup.json` remains on disk. Keep diagnostic outputs outside
the maintained source and distinguish a profiled run from the ordinary module
timings above.

