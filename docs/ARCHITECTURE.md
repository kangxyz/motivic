# Architecture

## Mathematical objects and ownership

Motivic develops finite correspondences, transfers and a concrete motivic
cohomology model. Their actual constructions and comparison boundaries are
recorded in the [source-family guides](../Motivic/README.md). This page owns
source structure and dependency direction, not the detailed interfaces.

Reuse Mathlib first, then the pinned Aglib extension. General theory intended
for Aglib is maintained in `Motivic/Aglib/`, following the
[shared candidate policy](https://github.com/kangxyz/aglib/blob/main/docs/DEVELOPMENT.md#downstream-candidates-for-aglib).
This is an active source layer of the Motivic library, with the temporary
module prefix `Motivic.Aglib`; it is neither a separate package nor a claim of
upstream acceptance. Never create a package-root `Aglib/` shadow.

A module path identifies a source owner. A declaration namespace identifies
the mathematical object. Candidates use native namespaces from the outset;
relocation normally changes imports rather than declaration names. General
scheme theory belongs under its actual scheme objects and morphisms, rather
than scattered implementation files directly under `AlgebraicGeometry`.

## Selected occupied families

The source organization separates reusable general theory from its motivic
applications:

```text
Motivic/
  Aglib/
    Algebra/  AlgebraicGeometry/  CategoryTheory/
    FieldTheory/  LinearAlgebra/  RingTheory/  Topology/
  AlgebraicGeometry/
    Correspondences/
  Transfers/
    Presheaf/  Sheaf/  SingularComplex/  Cohomology/
  Cohomology/
    SuslinVoevodsky/
    Coefficients/Finite/
    A1/
      Contraction/  Boundary/  LocalVanishing/
      Sheafification/  StrictInvariance/  Purity/  HigherImages/
    Diagonal/  WeightOne/  WeightTwo/
  RingTheory/LocalLength/
  KTheory/MilnorK/
```

The [library guide](../Motivic/README.md) and occupied family READMEs give exact
imports. This tree selects mathematical owners, not a promised future framework
or an assertion that every sibling is independent. Add a directory or facade
only for actual source and a current consumer.

Generic geometry includes schemes, morphisms, modules, sites, cycles, affine
spectra and Weil-style constructions under their actual objects. General
curve, line-bundle, frame and pencil results with complete general interfaces
remain candidates even when their first consumer is a motivic proof. A name or
current consumer alone does not make a theorem an application. Finite
correspondences and the adaptations that use their transfer actions remain
host mathematics.

## Candidate admission and dependency direction

Before adding a candidate, search Mathlib, pinned Aglib and existing candidates
for its actual object and maps. Record the intended `Aglib.*` module, exact
hypotheses, mathematical interface and current consumer in the module docstring;
the occupied family guide records the principal results and reuse routes.

The complete candidate import closure contains only Mathlib, Aglib and
explicitly designated general candidate leaves. Ordinary host applications
and their adapters stay outside `Motivic/Aglib`. Resolve an apparent coupling
by extracting the general prerequisite first, or by leaving the application
outside the candidate tree. A compiled cross-family dependency does not waive
this rule. In particular, generic site-point cohomology must consume general
sheaf cohomology; generic algebra cannot import a motivic scalar-extension
application; general Tor support cannot depend on a correspondence-specific
incidence construction. Preserve actual maps while separating their general
primitives from specializations.

Candidates use normal production enrollment, Lean options, lint, axiom policy
and focused incremental builds. They are maintained proofs. Coordinate one
implementation owner across downstream libraries. After an accepted upstream
revision is pinned, retarget consumers and remove the local implementation in
the same change. Avoid duplicate implementations and default legacy facades.

Already accepted upstream implementations are used directly. The
[Milnor bridge guide](../Motivic/KTheory/MilnorK/README.md) and
[homological candidate guide](../Motivic/Aglib/Algebra/README.md) record the
canonical upstream reuse and actual consumers.

## Public surface and model extension

`Motivic.lean` is the generated entry for all enrolled production modules; CI
checks it with Mathlib's `mk_all`. The focused core entries are `Motivic.Cor`,
`Motivic.Transfers`, `Motivic.Cohomology` and `Motivic.KTheory.MilnorK`.
Family facades contain precise public imports and a scope comment;
implementation leaves import the exact lower leaves they use. Computations
and stronger theorems have focused entries with their own hypotheses.
Tests, separate clients, provenance and scratch never supply production
prerequisites.

The current model lives under `Cohomology/SuslinVoevodsky`. Generic coefficient
operations have their general owners; the current model's finite-coefficient
construction and comparisons live under `Cohomology/Coefficients/Finite`.
Degree computations live under `Diagonal`, `WeightOne` and `WeightTwo`.
Future higher-Chow, motives or spectrum models need actual constructions and
explicit comparison maps with stated hypotheses. Do not reserve empty model
hierarchies or identify models by an abstract replacement isomorphism.

The [interface index](INTERFACES.md) routes to actual objects, complete
hypotheses, universes, maps and remaining theorem inputs in their source
families. Keep detailed mathematical statements there. Compilation and finite
checks are production evidence; they do not assign mathematical acceptance or
supply an unproved theorem-family premise.
