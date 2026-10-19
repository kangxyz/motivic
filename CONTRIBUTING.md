# Contributing

Use the [documentation routes](docs/README.md) to select the current family.
Start with an exact mathematical object, map or theorem and its complete
hypotheses. Reuse the pinned Mathlib/Aglib implementation before adding a new
one. The [architecture](docs/ARCHITECTURE.md), [naming](docs/NAMING.md) and
[interface boundaries](docs/INTERFACES.md) govern source ownership.

General theory intended for Aglib belongs in `Motivic/Aglib/`, under the
[shared candidate policy](https://github.com/kangxyz/aglib/blob/main/doc/DEVELOPMENT.md#downstream-candidates-for-aglib).
Use native mathematical namespaces and a general dependency closure. State the
intended upstream module, full hypotheses and current consumer in the module
docstring; describe the actual interfaces in the occupied family guide.
Motivic comparisons and application adapters stay outside the candidate tree.
Names, an existing motivic consumer, or curve geometry alone do not select
application ownership. Never create a package-root `Aglib/` directory.

Keep `docs/` as concise package-wide summaries, conventions and indexes. Put
mathematical definitions, full hypotheses, universes, degree/sign conventions,
API examples and remaining theorem inputs in their owning source-family README
or child document. Link from central summaries rather than duplicating the
mathematical prose.

Use precise imports, English source comments, modern public module headers,
and actual contributor attribution. Use `Authors: kangxyz` for this project
owner's code, preserving concrete upstream authors when adapting sources. Preserve source provenance and
license exceptions. Avoid package-wide options or blanket linter suppression
to repair one declaration.

Use [incremental validation](docs/DEVELOPMENT.md#verification-by-scope) throughout
normal work, including merge and publication. It covers applicable compilation,
declaration/text-style lint, affected `MotivicTest` and client tests, and
source/trust checks. During development, build the changed leaf and needed
affected consumers and handle compiler diagnostics. Run independent lint and
tests only in the task's final validation before delivery; helper returns,
internal commits and merges do not trigger them. Reuse compatible evidence and
rerun only failed or newly affected checks after final-check repairs.

Add tests for mathematical edge cases, map
identity, signs, universes or an API boundary that needs evidence. A helper
does not need a ceremonial new test. Production cannot import `MotivicTest`.

Describe mathematical changes separately from source movement, compilation
repairs and evidence. Update a family guide when the public statement or scope
changes. Preserve others' work and do not upgrade pins as a side effect of a
proof edit.
