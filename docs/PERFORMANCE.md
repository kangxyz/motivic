# Lean performance findings

This page keeps key guidance. The [case folder and index](performance/README.md)
preserve all earlier records, including measured jobs, unsuccessful variants and
the complete source/run table. Their [original context](performance/original-context.md)
retains toolchain, dependency and resource conditions.

| Problem | Original records |
| --- | --- |
| Concrete cover/history/supplier conversion | [Abstract-object repair](performance/prove-over-abstract-objects-then-specialize.md), [module-cost observations](performance/observed-module-costs.md) |
| A wrapper or constructor regresses | [Failed history-context variants](performance/observed-module-costs.md) |
| Cached compilation does not cover a command linter | [Copyright-header case](performance/copyright-headers-and-cached-command-lint.md) |
| Repeated checker startup or driver launch failure | [Build-environment case](performance/reuse-the-build-environment.md) |
| Source/run evidence | [Complete evidence table](performance/source-and-log-evidence.md) |

Retain original maps, witnesses, E3 sign, coefficient universes and public
hypotheses. More packaging is not automatically cheaper; module-job durations
are not a whole-build speedup. Common key guidance is in
[Aglib](https://github.com/kangxyz/aglib/blob/main/docs/PERFORMANCE.md).

## Repair workflow

For serious compilation trouble, read the matching case and its conditions before
further experiments or budget changes. Current commands, source/budget policy and
validation remain in [development](DEVELOPMENT.md#source-and-contribution-conventions)
and [the toolkit entry guide](../scripts/README.md). Historical commands inside
records retain their original scope.

If no case covers the failure, search upstream by diagnostic, public symbol,
phase and version and check the pinned source. Ordinary proof iteration stays
incremental; profiling and probes are explicitly requested diagnostics.

## Preserve cases

Save each reusable repair in `docs/performance/`, retaining its conditions,
failed alternatives, effective change and existing source/build evidence.
Update the same case for follow-ups and its folder-index link. Refine key
guidance here without deleting the underlying case or replacing it by a summary
or Git-history link. Recording experience adds no benchmark, build or acceptance.
