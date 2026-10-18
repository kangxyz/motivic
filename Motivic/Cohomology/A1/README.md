# Affine-line invariance

`Motivic.Cohomology.A1.StrictInvariance` proves strict A¹ invariance over an
infinite perfect field. For a field `k : Type u` and an HI coefficient
`F : Motivic.SheafWithTransfers.{u + 1} k`, every original ordinary Nisnevich
cohomology projection is an isomorphism in every natural degree. The ordinary
`HasExt.{u + 1}` instance on the big Nisnevich sheaf category remains explicit.

```lean
import Motivic.Cohomology.A1.StrictInvariance
```

The native theorem is
`Motivic.SheafWithTransfers.isStrictA1Invariant_of_isA1Invariant`;
`isStrictA1Invariant_iff_isA1Invariant` gives the converse comparison. These
use the existing groups, transfer coefficient and literal projection maps.
`MotivicTest.StrictA1Invariance` exercises both the IsIso and bijective forms.

| Entry | Scope |
| --- | --- |
| `GenericDetection` | Local zero-neighborhoods from generic vanishing over infinite fields |
| `PresheafContractionBoundaryEpi` | The canonical boundary Epi for an HI original presheaf with transfers over an infinite field |
| `PointedCartierH1Restriction` | Original H¹ restriction Mono with every full field-valued marking |
| `PointedCartierPositiveRestriction` | Higher restriction Mono using lower coefficient degrees and degree N−1 of the actual contraction |
| `StrictInvariance` | Strong induction over all HI coefficients; no supplied puncture-Mono or positive-degree HI family |
| `CartierBoundary` | The retained genuine higher-direct-image theorem with its stated current-degree HI and Epi inputs |

The new strict theorem closes the infinite-perfect-field endpoint. Finite-field
descent, general derived continuity, full canonical purity and the separate
frame/standard-triple/norm/Picard program retain their own proof boundaries.
Positive-characteristic diagonal, higher-Chow and spectrum comparisons are
separate from this ordinary-cohomology result.

[Source and verification records](../../../doc/provenance/strict-a1-infinite-perfect-20261018/README.md)
separate admitted sources, historical Linux evidence and archived candidates.
