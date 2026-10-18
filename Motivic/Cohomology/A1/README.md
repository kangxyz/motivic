# Affine-line invariance

`Motivic.Cohomology.A1.StrictInvariancePerfectField` proves strict A¹ invariance
over every perfect field, including finite fields. For `k : Type u` and an HI
coefficient `F : Motivic.SheafWithTransfers.{u + 1} k`, every original ordinary
Nisnevich cohomology projection is an isomorphism in every natural degree. The
ordinary `HasExt.{u + 1}` instance on the big Nisnevich sheaf category remains
explicit.

```lean
import Motivic.Cohomology.A1.StrictInvariancePerfectField
```

The native theorem is
`Motivic.SheafWithTransfers.isStrictA1Invariant_of_perfect`;
`isStrictA1Invariant_iff_isA1Invariant_of_perfect` gives the equivalence with
coefficient-level HI. `MotivicTest.PerfectFieldStrictA1Invariance` checks both
the IsIso and bijective forms of the literal ordinary projection. No cardinality,
local-zero, boundary-Epi or positive-degree HI family is supplied to this theorem.

| Entry | Scope |
| --- | --- |
| `GenericDetection` | Original local zero-neighborhoods over infinite fields |
| `FiniteIntegralAffineLocalZero` | Constructed finite-field local zero for original HI presheaves, with arbitrary coefficient universe |
| `FiniteCoefficientLocalZero` | The finite local-zero contract and actual dense-open restriction for HI transfer sheaves |
| `PresheafContractionBoundaryEpi` | Canonical boundary Epi for original HI presheaves over infinite fields |
| `FinitePresheafContractionBoundaryEpi` | Canonical boundary Epi for original HI presheaves in universe `u + 1` over finite fields |
| `StrictInvarianceCoefficientInputs` | Reusable perfect-field assembly conditional on explicit original local-zero and boundary-Epi inputs |
| `StrictInvarianceFiniteField` | Finite-field strict invariance with both inputs constructed |
| `StrictInvariance` | Existing infinite-perfect-field theorem and lower-degree induction over all HI coefficients |
| `StrictInvariancePerfectField` | Unified perfect-field theorem using the finite and infinite branches |
| `CartierBoundary` | Genuine higher-direct-image theorem retaining its stated current-degree HI and Epi inputs |

The strict theorem closes the perfect-field transfer-sheaf endpoint. General
HI-presheaf sheafification, nonperfect fields, derived continuity, full canonical
purity and the separate global principal-family/norm/Picard program keep their
own boundaries. Positive-characteristic diagonal, higher-Chow and spectrum
comparisons remain separate.

[Source and verification records](../../../doc/provenance/perfect-strict-20261018/README.md)
separate the admitted proofs, supplied checks and independent review from the
independent source candidates outside the strict proof.
