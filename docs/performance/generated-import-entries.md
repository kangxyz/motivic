> Preserved original record. [Original source](https://github.com/kangxyz/motivic/blob/be8e17f5286874bd44942f796b96860b4b924993/docs/PERFORMANCE.md#generated-import-entries) · [Context](original-context.md) · [Case index](README.md) · [Previous record](ci-dependency-handoff-and-native-resource-limits.md) · [Next record](copyright-headers-and-cached-command-lint.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Generated import entries

A fixed line allowance on an import-only entry can expire as the source graph
grows; see the [Aglib failure and pinned-linter reproduction](https://github.com/kangxyz/aglib/blob/main/docs/performance/generated-import-entries-and-file-length-limits.md#generated-import-entries-and-file-length-limits).
The existing opt-in topic generator now writes `set_option linter.style.longFile 0`
for every generated entry. Fixtures cover new and growing topics, repeated
refresh and preservation of native roots and manually owned files. No current
Motivic topic is enrolled; native defaults and CI commands are unchanged.

