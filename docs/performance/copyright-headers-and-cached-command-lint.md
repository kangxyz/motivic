> Preserved original record. [Original source](https://github.com/kangxyz/motivic/blob/be8e17f5286874bd44942f796b96860b4b924993/docs/PERFORMANCE.md#copyright-headers-and-cached-command-lint) · [Context](original-context.md) · [Case index](README.md) · [Previous record](generated-import-entries.md) · [Next record](observed-module-costs.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Copyright headers and cached command lint

The [2026-10-24 Build failure](https://github.com/kangxyz/motivic/actions/runs/39996085343/job/120559858728)
reported malformed copyright headers in 37 production modules after cache
restoration caused them to compile again. The earlier incremental build reused
outputs for those modules, and the separate native text-style check does not
cover copyright headers. A green incremental run therefore did not establish
that every source header met the enabled command linter.

The repair completes 190 production headers, retaining concrete upstream authors
and leaving all mathematical bodies unchanged. One shared Lean environment
loaded the [pinned Mathlib header checker](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Tactic/Linter/Header.lean):
`Lean.Parser.parseHeader` supplies the leading comment to
`Mathlib.Linter.copyrightHeaderChecks` with the unchanged Apache license string.
All 2414 production leaf headers pass that predicate. This is copyright-format
coverage; it does not replace native compilation, declaration lint or axiom
checks. Keep those checks and compatible cached outputs, and batch this cheap
source repair before rebuilding affected consumers.

