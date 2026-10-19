# Transfers and ordinary cohomology

The small public entry `Motivic.Transfers` selects the canonical all-degree
transfer action on the original ordinary Nisnevich cohomology groups. It works
over any field for a Nisnevich sheaf with transfers and `n : ℕ`. Ordinary
`HasExt` and coefficient universes remain explicit; the transfer-category
instance is constructed internally. Neither perfectness nor coefficient HI
is a premise of this endpoint.

| Family | Exact lower import and interface |
| --- | --- |
| [Presheaves](Presheaf/README.md) | `Motivic.Transfers.Presheaf.Basic`: additive actions on actual signed correspondences |
| [Sheaves](Sheaf/README.md) | `Motivic.Transfers.Sheaf.Basic`: actual transfer sheaves and ordinary graph restriction |
| [Singular complexes](SingularComplex/README.md) | `Motivic.Transfers.SingularComplex.Presheaf`: original parameter complex |
| [Cohomology](Cohomology/README.md) | `Motivic.Transfers.Cohomology.Basic`: original ordinary groups and transfer action |

The endpoint uses genuine sheaf exactness, enough injectives, ordinary
acyclicity of transfer-injectives and the actual Ext comparison with graph and
coefficient naturality. Keep original restrictions and coefficient maps.
`MotivicTest.OrdinaryCohomologyTransfers` is the direct public/trust consumer.
Historical hash-matched source checks remain attached to their dated records;
source reorganization does not imply a new build or mathematical review.

[General sheaf cohomology](../Aglib/CategoryTheory/Sites/SheafCohomology/Large/README.md)
and [scheme sites](../Aglib/AlgebraicGeometry/Sites/README.md) are general
candidates. Transfer actions and HI specializations remain host constructions.
The [A1 guide](../Cohomology/A1/README.md) describes strict invariance over every
perfect field and the separate unsupplied boundaries.
