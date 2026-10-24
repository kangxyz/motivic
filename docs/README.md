# Documentation and reading routes

The [source-family guide](../Motivic/README.md) gives public imports, actual
objects, main results and exact conditions. Mathematical content belongs in
those source owners. This directory holds package-wide summaries, conventions,
reading routes and the scope of recorded evidence.

| Guide | Purpose |
| --- | --- |
| [Architecture](ARCHITECTURE.md) | Source ownership, dependency direction and extension admission |
| [Naming](NAMING.md) | Native namespaces, subject names, leaves and facades |
| [Interface routes](INTERFACES.md) | Links to mathematical interfaces and retained input boundaries |
| [Development](DEVELOPMENT.md) | Locked setup, incremental compilation, lint, tests and clients |
| [Performance](PERFORMANCE.md) | Symptom lookup, key methods and focused cases under `performance/` |
| [Developer tools](../scripts/README.md) | Selected-target cache/build commands and check coverage |
| [Verification](VERIFICATION.md) | Dated validation milestones and their limits |
| [Provenance](provenance/README.md) | Imported source identities, historical evidence and recovery records |

## Choose a source owner

| Task | Route |
| --- | --- |
| First public import or focused optional entry | [Library guide](../Motivic/README.md) |
| General theory intended for Aglib | [Candidate guide](../Motivic/Aglib/README.md) |
| Finite correspondences and transfer actions | [Correspondences](../Motivic/AlgebraicGeometry/Correspondences/README.md), then [transfers](../Motivic/Transfers/README.md) |
| Current motivic model and computations | [Cohomology](../Motivic/Cohomology/README.md) |
| HI-presheaf sheafification and strict invariance | [Sheafification](../Motivic/Cohomology/A1/Sheafification/README.md), then [A1 family](../Motivic/Cohomology/A1/README.md) |
| Public/trust consumers | [Tests](../MotivicTest/README.md) and [separate client](../examples/downstream/README.md) |

Find a theorem through its family guide, exact import and native declaration
name. Extend the actual object using precise lower leaves and update that
owner's guide. Put definitions, full hypotheses, universes, signs, API examples
and theorem-input boundaries there; keep central pages as summaries and links.
Source paths and declaration namespaces are distinct.

Follow [incremental validation](DEVELOPMENT.md#verification-by-scope) for changed
leaves and affected consumers. Retain compatible caches and evidence. A dated
check or source correspondence does not establish an unsupplied theorem input
or assign independent mathematical acceptance.
