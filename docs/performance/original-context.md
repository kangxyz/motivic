> Preserved original record. [Original source](https://github.com/kangxyz/motivic/blob/be8e17f5286874bd44942f796b96860b4b924993/docs/PERFORMANCE.md#lean-compilation-performance) · [Context](original-context.md) · [Case index](README.md) · [Next record](repair-workflow.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

# Lean compilation performance

This guide records reusable repairs from the 2026-10-21 sheafification
integration. Measurements below are successful Lake module jobs on
`lean-build-cqa1`, using Lean 4.34.1, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` and Aglib
`52e09db47998f139064acf48a2d3a64494d0dd9a`.
The native build admitted eight jobs with four Lean threads each, a 12800 MiB
frontend limit and the ordinary 200000-heartbeat budget. These are observations
from incremental runs with different active dependency jobs, not a controlled
whole-library benchmark. A cached job supplies no fresh timing.

