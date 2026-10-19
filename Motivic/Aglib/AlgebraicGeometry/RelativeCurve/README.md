# General relative-curve, frame and pencil interfaces

This family retains actual relative curves, open embeddings, sections, divisors,
frames and pencils. These are general candidates under native mathematical
namespaces; their first use in a motivic proof does not select host ownership.

| Exact import | Interface and boundary |
| --- | --- |
| `Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Open.CurveOpenShrinking` | Shrink over the actual generic base open while preserving the prescribed curve. |
| `Motivic.Aglib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.ComponentRegularity` | Literal endpoint parameter regularity on reduced generic components of a flat polynomial family; the whole family need not be finite. |
| `Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Sections.DivisorPairs.BoundaryFramed` | Actual Serre divisor pairs and boundary-framed classes; finite projective presentation and all-twist frames remain explicit. |

The component theorem retains the original ambient ideal quotient and scalar
map. It does not infer flatness of a component over a higher-dimensional base.
Boundary-framed divisor pairs use the actual finite-flat zero schemes and literal
boundary equations. They do not prove general relative Picard representability.

[Invertible-module results](../Modules/Invertible/README.md) supply finite-support
frames; [Cartier results](../EffectiveCartierDivisor/README.md) retain relative
flatness. General section/pencil leaves keep each displayed twist, vanishing,
finite-presentation and prescribed-boundary input. Actual correspondence producers and transfer actions are
[host consumers](../../../AlgebraicGeometry/Correspondences/README.md).

## One section choice and actual norm-boundary comparisons

| Exact import | Interface and retained boundary |
| --- | --- |
| `Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Data.BoundarySectionData` | One retained original whole-boundary section choice; older interfaces project that same data. |
| `Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Data.FullBoundarySectionData` | One Serre choice from the same full target-boundary frame. |
| `Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Norm.SectionPairBoundaryEquality` | The actual source norm equals the unchanged target marked coefficient for the same original section pairs. |
| `Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Boundary.SectionPairGraphInfinityNorm` | The same section-induced coefficient has norm one on the whole actual inverse infinity. |

The two pairs retain their original global numerator, pole and boundary
trivializations. Thickened source boundaries are not replaced by reduced
infinity. Marked norm comparisons retain actual chart maps and require only
the displayed total-chart freeness; residual freeness or graph-coefficient
invertibility is not added. The full-infinity factor retains nilpotents.

See the [host principal and norm actions](../../../Transfers/Presheaf/Actions/README.md)
for the corresponding application conditions.
Keep each fixed section-data record with its projected data and original maps.
An independent `Nonempty` witness is not an equality with that record and does
not identify its chosen sections or frame without an explicit compatibility.
