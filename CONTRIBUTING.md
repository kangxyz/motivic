# Contributing

Start with an exact mathematical object, map or theorem and its complete
hypotheses. Reuse the pinned Mathlib/Aglib implementation before adding a new
one. The [architecture](doc/ARCHITECTURE.md), [naming](doc/NAMING.md) and
[interface boundaries](doc/INTERFACES.md) govern source ownership.

Use precise imports, English source comments, modern public module headers,
and actual contributor attribution. Use `Authors: kangxyz` for this project
owner's code, preserving concrete upstream authors when adapting sources. Preserve source provenance and
license exceptions. Avoid package-wide options or blanket linter suppression
to repair one declaration.

Use [incremental validation](doc/DEVELOPMENT.md#verification-by-scope) throughout
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
