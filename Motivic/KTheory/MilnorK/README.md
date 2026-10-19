# Public Milnor bridges

`Motivic.KTheory.MilnorK` reexports `Aglib.KTheory.MilnorK`;
`Motivic.KTheory.MilnorK.Norms` reexports its optional characteristic-zero norm
tower. These are the two retained public compatibility imports.

For general symbol work use focused upstream imports:

```lean
import Aglib.KTheory.MilnorK.Basic
```

The canonical group remains `MilnorK.K F n`, with native `MilnorK` declarations.
The tensor presentations `MilnorK.K2.Group F` and `MilnorK.K3.Group F` have
explicit symbol-preserving comparisons; they are not replacement all-degree
theories. Retain valuation/uniformizer conditions for residues and
characteristic-zero, algebra, finite-dimensional and scalar-tower conditions
for general finite-extension norms.

Use [Aglib's family guide](https://github.com/kangxyz/aglib/blob/main/Aglib/KTheory/MilnorK/README.md)
for current general imports, with the revision fixed by this package's manifest.
Diagonal and weight-two applications live under
[cohomology](../../Cohomology/README.md), with actual endpoint maps and stated
normalization hypotheses. General curve/frame prerequisites have their
[candidate owner](../../Aglib/AlgebraicGeometry/RelativeCurve/README.md).
[Provenance](../../../docs/provenance/README.md) preserves source identity;
old implementation/test paths are historical rather than present imports.
