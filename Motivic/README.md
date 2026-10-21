# Source families and public imports

[Motivic.lean](../Motivic.lean) is the generated entry for all production modules.
Use an exact lower leaf for implementation work or a focused facade for its
public interface. Module paths identify source owners; native declaration
namespaces identify mathematical objects.

| Focused core import | Actual interface |
| --- | --- |
| `Motivic.Cor` | Signed finite correspondences on smooth separated finite-type schemes over a field; [guide](AlgebraicGeometry/Correspondences/README.md) |
| `Motivic.Transfers` | Original ordinary Nisnevich cohomology with transfers in every natural degree, retaining ordinary `HasExt`; [guide](Transfers/README.md) |
| `Motivic.Cohomology` | Curated cohomology interface and the current motivic model; [guide](Cohomology/README.md) |
| `Motivic.KTheory.MilnorK` | Small bridge to independent Aglib's canonical Milnor theory; [guide](KTheory/README.md) |

## Focused theorem and computation imports

| Exact import | Scope and conditions |
| --- | --- |
| `Motivic.Cohomology.SuslinVoevodsky` | Current complex and ordinary hypercohomology; [model guide](Cohomology/SuslinVoevodsky/README.md) |
| `Motivic.Cohomology.Coefficients.Finite` | Actual cone, hypercohomology and original coefficient maps; [guide](Cohomology/Coefficients/Finite/README.md) |
| `Motivic.Cohomology.A1.StrictInvariance` | Every-perfect-field strict invariance, HI transfer sheaves, coefficient `u+1`, ordinary `HasExt.{u+1}`; [A1 guide](Cohomology/A1/README.md) |
| `Motivic.Cohomology.A1.Sheafification.HomotopyInvariance` | Actual Nisnevich sheafification of HI transfer presheaves over any field, coefficient universe `u + 1`; [guide](Cohomology/A1/Sheafification/README.md) |
| `Motivic.Cohomology.A1.Sheafification.StrictInvariance` | Strict invariance of that canonical sheaf over perfect fields, retaining ordinary `HasExt.{u+1}`; [guide](Cohomology/A1/Sheafification/README.md) |
| `Motivic.Cohomology.A1.GenericDetection` | Infinite-field affine local-zero detection for original HI presheaves |
| `Motivic.Cohomology.AffineLine` | Ordinary higher vanishing and positive vanishing for HI transfer sheaves |
| `Motivic.Cohomology.AffineLine.GenericBase` | Classwise generic-base vanishing over a smooth integral affine base, with the original whole line and restrictions |
| `Motivic.Cohomology.A1.CartierBoundary` | Genuine higher direct-image vanishing retaining stated current-degree HI and boundary-Epi inputs |
| `Motivic.KTheory.MilnorK.Norms` | Aglib characteristic-zero finite-extension norms with original tower data |
| `Motivic.Cohomology.Diagonal` | Characteristic-zero diagonal comparison; [guide](Cohomology/Diagonal/README.md) |
| `Motivic.Cohomology.WeightOne` | Original unit-sheaf and hypercohomology comparisons; [guide](Cohomology/WeightOne/README.md) |
| `Motivic.Cohomology.WeightTwo` | Implemented weight-two computation family; [family guide](Cohomology/WeightTwo/README.md) |

The [20 October sheafification intake](../docs/provenance/hi-presheaf-sheafification-20261020/README.md)
records the source identities, ordinary mathematical review relative to its
recorded baseline and ongoing current-pin validation of those new entries.
The conditional whole-cylinder lifting interfaces remain available.

## General foundations and host applications

[Motivic/Aglib](Aglib/README.md) is the active maintained candidate layer for
general theory, mirroring intended upstream subjects with native declaration
namespaces. Its closure uses Mathlib, Aglib and designated candidates only.
[General geometry](Aglib/AlgebraicGeometry/README.md) owns schemes, morphisms,
modules, sites and cycles, including general curve/frame/pencil interfaces.
The independent Aglib package supplies already accepted APIs, including
canonical Milnor K-theory and Koszul basics. Do not duplicate them locally.

[Correspondences](AlgebraicGeometry/Correspondences/README.md),
[transfer presheaves](Transfers/Presheaf/README.md),
[transfer sheaves](Transfers/Sheaf/README.md),
[singular complexes](Transfers/SingularComplex/README.md) and their cohomology
are host constructions. Their applications consume general primitives.

Use the [documentation routes](../docs/README.md) for theorem search, extension
and validation. [Verification](../docs/VERIFICATION.md) and
[provenance](../docs/provenance/README.md) retain identified evidence boundaries.
Source-family guides record theorem hypotheses and remaining inputs;
verification records identify the checks actually run.
