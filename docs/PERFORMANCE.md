# Lean performance findings

Use this page to find a relevant method and this library's
[local cases](performance/local-cases.md). Current preparation and validation
belong to [development](DEVELOPMENT.md#normal-task) and
[the toolkit entry guide](../scripts/README.md).

| Problem | Read |
| --- | --- |
| Concrete geometric conversions or repeated supplier construction | [Shared conversion methods](https://github.com/kangxyz/aglib/blob/main/docs/performance/conversion-boundaries.md), [shared constructions](https://github.com/kangxyz/aglib/blob/main/docs/performance/shared-constructions.md), [local history/cover cases](performance/local-cases.md#history-context-and-complete-supplier-conversion) |
| Instance, parent-structure or universe mismatch | [Instances and universes](https://github.com/kangxyz/aglib/blob/main/docs/performance/instances-and-universes.md) |
| Unexpected compile/lint coverage or checker startup | [Header case](performance/local-cases.md#cached-command-lint-coverage), [compiled checker](performance/local-cases.md#compiled-checker-startup), [common build/check lessons](https://github.com/kangxyz/aglib/blob/main/docs/performance/build-and-check-costs.md) |
| Explicitly requested cause or timing investigation | [Diagnosis and evidence](https://github.com/kangxyz/aglib/blob/main/docs/performance/diagnosis-and-evidence.md) |

Keep the original maps, rich suppliers, signs, universes and public hypotheses.
The recorded constructor regressions show that a context wrapper alone does
not guarantee a cheaper consumer. Preserve compatible artifacts and check
results; a cached module supplies no new timing or command-linter coverage.

## Repair workflow

For serious compilation trouble, read the matching topic and its conditions
before further experiments or budget changes. If they do not cover the failure,
use the shared
[upstream reference search](https://github.com/kangxyz/aglib/blob/main/docs/performance/diagnosis-and-evidence.md#search-upstream-references)
and check the pinned implementation. Ordinary proof iteration stays incremental;
profiling and probes are explicitly requested diagnostics. Retain the existing
[source and finite-budget policy](DEVELOPMENT.md#source-and-contribution-conventions).

When a validated repair adds new reusable knowledge, update the matching topic
in `docs/performance/`. Merge repeated experience and retain the symptom,
conditions, effective change, important failed alternative or limit, and existing
source/build evidence. Another run or pass of a known method needs no entry.
Common methods have one Aglib owner; keep local cases here and this page short.
Recording experience creates no new benchmark, build or acceptance cycle.
