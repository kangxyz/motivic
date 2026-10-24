> Preserved original record. [Original source](https://github.com/kangxyz/motivic/blob/be8e17f5286874bd44942f796b96860b4b924993/docs/PERFORMANCE.md#ci-dependency-handoff-and-native-resource-limits) · [Context](original-context.md) · [Case index](README.md) · [Previous record](repair-workflow.md) · [Next record](generated-import-entries.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## CI dependency handoff and native resource limits

The shared workflow now transfers Build's native dependency snapshot when
Test's optional Actions restore misses or fails. This includes unpublished
upstream leaves compiled by Build, before the mandatory current-run root
overlay and unchanged no-build verification. The [shared repair and bounded
native evidence](https://github.com/kangxyz/aglib/blob/main/docs/performance/test-dependency-handoff-and-native-resource-limits.md#test-dependency-handoff-and-native-resource-limits)
record the failure, successful transport, hosted startup and remaining full-CI
validation.
The mathematical dependency pins are unchanged. This package retains weak
`-M12800 -j4` frontend arguments without changing native artifact traces;
Lake retains `LEAN_NUM_THREADS=1`. Existing dependency packages retain their
own flags, while the workflow's aggregate memory scope also bounds them. No CPU-utilization improvement or
cause of the earlier runner shutdown is claimed.

