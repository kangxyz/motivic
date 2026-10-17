# Source families

The public entry is [Motivic.lean](../Motivic.lean). Select a focused family
or exact implementation leaf for development.

| Entry | Source owner |
| --- | --- |
| [Cor](Cor.lean) | [Correspondences](AlgebraicGeometry/Correspondences/README.md), presheaves and smooth Nisnevich sites |
| [Transfers](Transfers.lean) | [Ordinary cohomology transfers](Transfers/README.md) |
| [Cohomology](Cohomology.lean) | [Ordinary and motivic cohomology](Cohomology/README.md) |
| [Affine-line cohomology](Cohomology/AffineLine.lean) | Optional ordinary higher/positive-degree vanishing over fields |
| [Affine generic detection](Cohomology/A1/GenericDetection.lean) | Local-zero neighborhoods for HI presheaves with transfers over infinite fields |
| [Relative affine-line generic base](Cohomology/AffineLine/GenericBase.lean) | Classwise eventual ordinary higher vanishing with the whole line retained |
| [Milnor K](KTheory/MilnorK.lean) | [Integral symbol groups](KTheory/MilnorK/README.md) |
| [Milnor norms](KTheory/MilnorK/Norms.lean) | Optional characteristic-zero finite-extension norms |
| [Diagonal](Cohomology/Motivic/Diagonal.lean) | Optional characteristic-zero comparison |
| [Weight one](Cohomology/Motivic/WeightOne.lean) | Optional unit-sheaf/hypercohomology computation |

`Algebra`, `RingTheory` and the inherited [Aglib candidates](Aglib/README.md)
hold local foundations. Their exact imports determine usable dependency
boundaries. Further retained leaves remain directly selectable and are not
all admitted by the curated root. See [provenance](../doc/provenance/README.md)
for original successful-check coverage and unverified source boundaries.
