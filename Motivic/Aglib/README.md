# General-theory candidates for Aglib

`Motivic/Aglib/` contains maintained general theory developed here for later
inclusion in Aglib. Follow the
[shared candidate policy](https://github.com/kangxyz/aglib/blob/main/doc/DEVELOPMENT.md#downstream-candidates-for-aglib).
Candidates are ordinary Motivic production modules, checked with the same Lean
options, lint, axiom policy and incremental build route.

Use `Motivic.Aglib` as the temporary module prefix and mirror the intended
upstream mathematical hierarchy below it. Use native declaration namespaces,
such as `AlgebraicGeometry.Scheme`, `CategoryTheory.Sheaf` and
`CochainComplex`. Do not create a package-root `Aglib/` tree: that would shadow
the upstream dependency. Candidate status does not assert upstream acceptance.

Search Mathlib and the pinned Aglib APIs before adding source. Keep the entire
candidate import closure in Mathlib, Aglib and designated general candidate
leaves. Ordinary host applications and comparison adapters belong outside this
subtree. Extract a required general prerequisite before admitting its consumer;
do not accept a host dependency merely because the existing file compiles.
Coordinate one implementation owner across downstream libraries.

State the intended `Aglib.*` module, exact hypotheses and current consumer in
each module docstring. Each occupied family's guide identifies its objects,
maps, principal results and exact imports. General curve, line-bundle, frame
and pencil theorems remain candidates when their full interfaces are general;
the theorem's name and its first motivic consumer do not select an application
owner. Correspondences and transfer actions are host constructions.

Use canonical upstream declarations when already available. In particular,
general Milnor K-theory is supplied by independent Aglib, and shared Koszul
basics use `ChainComplex.Koszul`. After an accepted candidate dependency group
is available in a pinned upstream revision, retarget consumers and remove the
local implementations in the same change, preserving native names. Avoid
duplicate copies and default legacy facades.

Occupied general families have their own interfaces and reuse routes:

- [Algebra and homology](Algebra/README.md).
- [Algebraic geometry](AlgebraicGeometry/README.md).
- [Category and site theory](CategoryTheory/README.md).
- [Dependent `Fin 2` families](Data/Fin/README.md).
- [Field theory](FieldTheory/README.md).
- [Linear algebra](LinearAlgebra/README.md).
- [Ring theory](RingTheory/README.md), including [Krull dimension](RingTheory/KrullDimension/README.md).
- [Topology](Topology/README.md).

See [architecture](../../docs/ARCHITECTURE.md) for ownership and dependency rules,
[naming](../../docs/NAMING.md) for exact object distinctions, and the
[library guide](../README.md) for host imports and consumers.
