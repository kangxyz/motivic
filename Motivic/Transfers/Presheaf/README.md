# Presheaves with transfers

`Motivic.PresheafWithTransfers` is the actual category of additive
contravariant functors on `Motivic.Cor`. Its action retains signed cycle
coefficients and original graph correspondences. Construction works over an
arbitrary field, with an independent coefficient universe.

| Exact import | Interface and boundary |
| --- | --- |
| `Motivic.Transfers.Presheaf.Basic` | The original additive presheaf category |
| `Motivic.Transfers.Presheaf.GraphRestriction` | The ordinary underlying presheaf along the actual graph functor |
| `Motivic.Transfers.Presheaf.Yoneda` | Original additive representables and their maps |
| `Motivic.Transfers.Presheaf.NisnevichComparison` | Additive sheaf condition compared with ordinary graph restriction |
| `Motivic.Transfers.Presheaf.NisnevichSheafification` | Transfer-preserving Nisnevich sheafification and the actual unit comparison |
| `Motivic.Transfers.Presheaf.Contraction` | Cokernel of the actual affine-line-to-torus restriction |
| `Motivic.Transfers.Presheaf.ContractionHI` | `contractionIsoKernel` for HI coefficients, with the original torus unit restriction |
| `Motivic.Transfers.Presheaf.ContractionNaturality` | Coefficient functoriality and quotient/kernel naturality |
| `Motivic.Transfers.Presheaf.ContractionInvariance` | `contraction_isA1Invariant`, preserving the literal projection pullback |
| `Motivic.Transfers.Presheaf.NisnevichLocalZero` | Genuine local-zero data and sheafification, with the original unit |

The native contraction interfaces are
`Motivic.PresheafWithTransfers.contraction`, `.contractionIsoKernel` and
`.contraction_isA1Invariant`. The latter two retain coefficient HI; the
underlying cokernel does not require it. `ContractionExterior` supplies parameter
products on signed correspondences. General affine-line/Laurent complement
geometry has its [candidate site owner](../../Aglib/AlgebraicGeometry/Sites/README.md).

`MotivicTest.TransferContraction` and
`MotivicTest.TransferContractionInvariance` consume these actual interfaces.
The [A1 family](../../Cohomology/A1/README.md) uses the cohomological boundary
comparisons. Strict invariance over all perfect fields retains ordinary
`HasExt.{u+1}` and HI transfer-sheaf coefficients in universe `u+1`.
The [presheaf-entry theorem](../../Cohomology/A1/Sheafification/README.md)
constructs HI of the actual Nisnevich sheafification in coefficient universe
`u+1`; its strict corollary retains perfectness and ordinary HasExt. Sheaf
cokernels retain their categorical construction.

Use [singular complexes](../SingularComplex/README.md) for the parameter-complex
construction and [transfer sheaves](../Sheaf/README.md) for the sheaf category.

## Sheafification and actions

| Family | Entry and reading route |
| --- | --- |
| [Image and representatives](Sheafification/README.md) | `Motivic.Transfers.Presheaf.Sheafification.Image` and focused representative leaves |
| [Pencil, norm and principal actions](Actions/README.md) | Exact original actions and their geometric hypotheses |

Use the [A1 sheafification guide](../../Cohomology/A1/Sheafification/README.md)
for the public HI and strict-invariance entries and reusable conditional
assemblies. These families add no root facade.
