# Mapping-cone finite coefficients and the positive Bockstein

For `K : CochainComplex C ℤ` and every `n : ℕ`,
`CochainComplex.finiteCoefficients K n` is the mapping cone of `n • 𝟙 K`.
Its signed coordinates are `a = snd` and `b = -fst`; for modules the differential
is `(da - n b, -db)`. The connecting map is the positive Bockstein coordinate
`b`, followed by the canonical shift identification. Reduction, insertion and
the contraction at level one retain these signs in every integer degree.

| Exact import | Interface and hypotheses |
| --- | --- |
| `Motivic.Aglib.Algebra.Homology.CochainComplex.FiniteCoefficients.Basic` | The cone, coefficient triangle, functorial maps, reduction and insertion; `[Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]` for `C : Type u`. |
| `Motivic.Aglib.Algebra.Homology.CochainComplex.FiniteCoefficients.Module` | Explicit pairs, differential and cocycle equations for modules over any ring, with independent ring and module universes. |
| `Motivic.Aglib.Algebra.Homology.CochainComplex.FiniteCoefficients.Cohomology` | `bocksteinHomology` and its positive representative formula, additionally using `[CategoryWithHomology C]`. |
| `Motivic.Aglib.Algebra.Homology.CochainComplex.FiniteCoefficients.Exact` | The exact coefficient sequence in an abelian category, including every natural coefficient level. |

The native interfaces are `CochainComplex.finiteCoefficients` and its
`triangle`, `integral`, `bockstein`, `reduction` and `insertion` declarations.
`Motivic.motivicFiniteComplex` specializes this same cone; the host
[finite-coefficient family](../../../../../Cohomology/Coefficients/Finite/README.md)
uses its original maps. No derived-tensor identification or invertibility of
`n` is claimed.

Intended upstream family:
`Aglib.Algebra.Homology.CochainComplex.FiniteCoefficients`.
Follow the [candidate policy](../../../../README.md), using the exact lower
import and retaining its categorical assumptions and universes.
