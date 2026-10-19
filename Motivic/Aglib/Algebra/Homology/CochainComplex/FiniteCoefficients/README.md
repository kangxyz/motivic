# Algebra / Homology / CochainComplex / FiniteCoefficients

The actual mapping cone of n times the identity, for all natural n, retaining a=snd and positive Bockstein b=-fst, reduction/insertion maps and contraction at level one.

Original additive/biproduct/category assumptions; every integer degree is supported. No derived-tensor identification or invertibility of n is claimed.

| Exact import |
| --- |
| `Motivic.Aglib.Algebra.Homology.CochainComplex.FiniteCoefficients.Basic` |
| `Motivic.Aglib.Algebra.Homology.CochainComplex.FiniteCoefficients.Exact` |

Native interfaces:

- `CochainComplex.finiteCoefficients`
- `CochainComplex.finiteCoefficients.triangle`
- `CochainComplex.finiteCoefficients.bockstein`

`Motivic.motivicFiniteComplex` specializes this cone; coefficient sequences consume its actual maps.

Intended upstream family: `Aglib.Algebra.Homology.CochainComplex.FiniteCoefficients`. Use exact lower
imports; a current motivating consumer does not change the general hypotheses.
Follow the [candidate policy](../../../../README.md) and retain the actual maps and
universes when extending these interfaces.
