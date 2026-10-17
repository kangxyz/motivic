# Local algebraic-geometry candidates and dependency boundaries

These are native local `Motivic.Aglib` modules under the project's exact pinned
Aglib and Mathlib versions. This location records mathematical reuse potential;
it does not mean that every file can already be imported in a standalone Aglib
checkout. Exact dependency imports remain visible in each source.

## Finite supports and line bundles

The finite-center, finite-neighborhood, and invertible-module leaves give actual
scheme maps and unit isomorphisms under their stated hypotheses. In particular,
triviality near finite supports is not a statement that a line bundle on an
arbitrary complete curve fiber is trivial. See the owning
[finite-morphism](Morphisms/Finite/README.md) and
[invertible-module](Modules/Invertible/README.md) families.

## Relative endpoint scalar and graph adapters

`FlatPolynomialComponentRegularity` proves that the literal parameter `t - a`
acts regularly on every actual reduced generic component of a whole flat
polynomial family, and on its original ambient kernel quotient. It imposes no
finiteness or quasi-compactness assumption on the whole family. Dominance and
actual germ maps supply regularity; no component flatness over a larger relative
base is inferred. The mathematical statement is general scheme theory; its
current imports reuse the project's finite-curve scalar and closed-stalk APIs.

`GraphPolynomialBlock`, `GraphClosedSupportBlock`, and `GraphPolynomialTor`
are downstream adapters. They currently depend on `Motivic.Graph`, actual
correspondence-product support infrastructure, and the project's proved Koszul
and Tor constructions. They are not yet standalone upstream imports. They keep
literal graph, closed-support, and endpoint stalk maps and exact scalar actions.
Only explicitly stated ambient maps are flat; support maps need not be flat.
The Tor adapter retains all homological degrees and the full principal-quotient
length, before any integer conversion.

These local results do not alone identify the four-factor correspondence
incidence modules or prove the relative-base endpoint correspondence. The imported snapshot referenced additional graph-block consumer notes that
were not included in the supplied source package. Use the actual source
statements and [historical check index](../../../doc/provenance/source-checks.json)
for retained scope and evidence.

Downstream original triple-support, four-factor incidence, and component
fundamental-correspondence attachments retain the same dependency boundary;
their separately referenced consumer notes were not part of this source package. The whole-family weighted replacement
is now supplied by `RelativeFiniteFlatFiberGenerics`,
`ClosedImmersionPointCoefficient`, `PolynomialFiberCycleSpecialization`, and
`RelativeFiniteFlatSpecialization`, with native `AlgebraicGeometry` namespaces.
They use proven generic support preservation to control off-generic coefficients
of positive-dimensional endpoint fibers. Use the exact statements of those leaves for their scope.
The relative endpoint correspondence assembly remains downstream; the
separately referenced assembly notes were not included in this source package.
Boundary-avoiding moving-divisor construction is still a separate geometric input.

Upstream extraction needs the relevant general prerequisites moved or replaced
first. Motivic correspondence assembly and strict-A¹ consumers remain downstream.

## Generic-base and original-open geometry

[AffineEtaleClosedSectionNeighborhood](AffineEtaleClosedSectionNeighborhood.lean)
constructs a principal refinement preserving the full original closed base
change and its section. [RelativeCurveOverlapShrinking](RelativeCurveOverlapShrinking.lean)
and [RelativeOpenImmersionOverlapShrinking](RelativeOpenImmersionOverlapShrinking.lean)
keep the prescribed scheme while shrinking over an actual generic base open.
The relative-line application is in the optional
[generic-base cohomology entry](../../Cohomology/AffineLine/GenericBase.lean).
Dimension-one bounds concern the actual generic fiber.

The original étale presentation and one-sided moving constructions feed the
[affine local-zero detection entry](../../Cohomology/A1/GenericDetection.lean).
The [source record](../../../doc/provenance/generic-detection-20261017/README.md)
separates admitted results from unlogged archival inputs.
