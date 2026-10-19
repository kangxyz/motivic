# General algebraic-geometry candidates

These maintained candidates mirror intended `Aglib.AlgebraicGeometry` owners.
They extend actual schemes, scheme maps, module sheaves and native mathematical
namespaces. Their complete import closure uses only Mathlib, Aglib and general
candidates. The motivating motivic consumer does not weaken this condition.

| Exact import | Interface and boundary |
| --- | --- |
| `Motivic.Aglib.AlgebraicGeometry.BaseChange.Affine.AdjoinRootBaseChange` | Actual affine base changes and generic-component transport. |
| `Motivic.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.AffineProduct` | Polynomial quotient and Laurent affine schemes, scalar maps and branch identifications. |
| `Motivic.Aglib.AlgebraicGeometry.Morphisms.ClosedImmersion.BaseChange.ClosedImageBaseChange` | Closed/open immersions, étale and finite morphisms, actual fibers and component images. |
| `Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.BoundaryCanonicalCoordinate` | Actual Cartier ideals, complement and boundary maps; relative finiteness keeps flatness. |
| `Motivic.Aglib.AlgebraicGeometry.WeilRestriction.Affine.ActualPair` | Affine finite-free restriction neighborhoods and literal scalar evaluations. |
| `Motivic.Aglib.AlgebraicGeometry.AffineLine.Open.AffineLineCoprimeOpenPresentation` | Actual affine-line opens and polynomial presentations. |
| `Motivic.Aglib.AlgebraicGeometry.IdealSheaf.Complement.AffineOpenComplementIdeal` | Ideal-sheaf complements and original stalk/pullback maps. |
| `Motivic.Aglib.AlgebraicGeometry.Cycles.BaseChange.BranchTransport` | Finite signed cycles, actual pushforwards and generic multiplicities. |
| `Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.Boundary.Sections.FiniteGraphSections` | Projective and relative-curve section constructions with stated twist/vanishing inputs. |
| `Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.CanonicalFrame` | General relative curves, frames, sections, pencils and endpoint geometry. |
| `Motivic.Aglib.AlgebraicGeometry.Modules.Gluing.AffineCharts` | Actual module sheaves, gluing, pullback, finite pushforward and invertible modules. |
| `Motivic.Aglib.AlgebraicGeometry.Properties.Discrete.DiscreteReducedCoproduct` | Discrete/reduced scheme decompositions under their actual hypotheses. |
| `Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.AffineLine.Basic` | Finite-curve normalization, compactification and actual function fields. |
| `Motivic.Aglib.AlgebraicGeometry.ResidueField.FiniteFieldResidueDegree` | Literal residue-field lifts and finite-field residue degrees. |
| [Graph morphisms and stalk comparisons](Graph/README.md) | General graph maps, pair bridges and original support/stalk maps. |
| `Motivic.Aglib.AlgebraicGeometry.Divisors.Order.IdealFrameOrderCancellation` | Ideal-frame order and cancellation with actual scalar maps. |
| `Motivic.Aglib.AlgebraicGeometry.Moving.OneSidedAffineSections` | General one-sided sections and pencils, retaining their supplied geometry. |
| `Motivic.Aglib.AlgebraicGeometry.Sites.Nisnevich.Lifting.ArtinianNeighborhood` | Smooth and Nisnevich objects, covers, neighborhoods and original germs. |
| `Motivic.Aglib.AlgebraicGeometry.Products.Diagonal.BaseChange` | Scheme products and actual diagonal ideals. |
| `Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Charts.BaseChange` | Charts, coheight and affine/étale neighborhood constructions. |
| `Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.GraphClosureEquations` | Twists, schematic images and graph closures. |
| `Motivic.Aglib.AlgebraicGeometry.QuasiAffine.FiniteNeighborhood` | Actual quasi-affine finite neighborhoods. |
| `Motivic.Aglib.AlgebraicGeometry.Stalk.Dimension.SmoothStalkFiniteRank` | Original stalk, dimension and generic-component interfaces. |
| `Motivic.Aglib.AlgebraicGeometry.Simplex.AffineBoundaryOneComplex` | Scheme realizations of the existing algebraic-simplex coordinate rings. |
| `Motivic.Aglib.AlgebraicGeometry.Intersection.AffineClosedSupportTor` | Tor coefficients and coherent restrictions on actual intersections. |
| `Motivic.Aglib.AlgebraicGeometry.Diagonal.AffineClosedSupportCoordinates` | Original diagonal supports, scalar actions and Koszul comparisons. |
| `Motivic.Aglib.AlgebraicGeometry.Scheme.DomainStalkComponents` | Normality, reduced components and original stalk localization. |

The table gives a concrete lower import for each occupied subject, rather than
an aggregate importing every result. Inspect the selected leaf for its full
hypotheses and maps. General frame/pencil and line-bundle interfaces stay here;
actual finite correspondences and their adapters live in
[the host correspondence family](../../AlgebraicGeometry/Correspondences/README.md).

Use the [cycle guide](Cycles/README.md), [site guide](Sites/README.md),
[invertible modules](Modules/Invertible/README.md),
[finite morphisms](Morphisms/Finite/README.md),
[relative curves](RelativeCurve/README.md) and
[Cartier divisors](EffectiveCartierDivisor/README.md) for detailed boundaries.
General graph/Tor interfaces retain original stalk scalar actions; flat ambient
maps do not imply flat support maps. Generic Tor and diagonal prerequisites are
candidates before their correspondence specializations consume them.

Finite-fiber triviality concerns the actual finite support scheme, including
nonreduced and empty fibers. It does not trivialize an arbitrary proper curve
fiber.

Each candidate module names its intended upstream module, hypotheses and current
consumer. See the [candidate policy](../README.md) and
[architecture](../../../docs/ARCHITECTURE.md). Historical source/check locators
remain in [provenance](../../../docs/provenance/README.md); relocation does not
turn an old check into validation of current bytes.

The [normalization and retained-chart guide](Normalization/README.md) records
one original cover/boundary choice and the actual inverse-chart maps. The
[finite-morphism guide](Morphisms/Finite/README.md) records whole finite norm
charts and generic ratios.
