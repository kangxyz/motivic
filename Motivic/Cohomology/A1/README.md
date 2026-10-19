# Affine-line invariance

`Motivic.Cohomology.A1.StrictInvariance` exports the perfect-field endpoint,
implemented in `Motivic.Cohomology.A1.StrictInvariance.PerfectField`. It proves strict A¹ invariance
over every perfect field, including finite fields. For `k : Type u` and an HI
coefficient `F : Motivic.SheafWithTransfers.{u + 1} k`, every original ordinary
Nisnevich cohomology projection is an isomorphism in every natural degree. The
ordinary `HasExt.{u + 1}` instance on the big Nisnevich sheaf category remains
explicit.

```lean
import Motivic.Cohomology.A1.StrictInvariance
```

The native theorem is
`Motivic.SheafWithTransfers.isStrictA1Invariant_of_perfect`;
`isStrictA1Invariant_iff_isA1Invariant_of_perfect` gives the equivalence with
coefficient-level HI. `MotivicTest.PerfectFieldStrictA1Invariance` checks both
the IsIso and bijective forms of the literal ordinary projection. No cardinality,
local-zero, boundary-Epi or positive-degree HI family is supplied to this theorem.

Entries below are exact suffixes of `Motivic.Cohomology.A1`.

| Lower entry | Scope |
| --- | --- |
| `GenericDetection` | Original local zero-neighborhoods over infinite fields |
| `LocalVanishing.FiniteField.IntegralAffineLocalZero` | Constructed finite-field local zero for original HI presheaves, with arbitrary coefficient universe |
| `LocalVanishing.FiniteField.CoefficientLocalZero` | The finite local-zero contract and actual dense-open restriction for HI transfer sheaves |
| `Boundary.Presheaf.Contraction.Epi` | Canonical boundary Epi for original HI presheaves over infinite fields |
| `Boundary.Presheaf.FiniteFieldEpi` | Canonical boundary Epi for original HI presheaves in universe `u + 1` over finite fields |
| `StrictInvariance.CoefficientInputs` | Reusable perfect-field assembly conditional on explicit original local-zero and boundary-Epi inputs |
| `StrictInvariance.FiniteField` | Finite-field strict invariance with both inputs constructed |
| `StrictInvariance.InfiniteField` | Existing infinite-perfect-field theorem and lower-degree induction over all HI coefficients |
| `StrictInvariance.PerfectField` | Unified perfect-field theorem using the finite and infinite branches |
| `CartierBoundary` | Genuine higher-direct-image theorem retaining its stated current-degree HI and Epi inputs |

The strict theorem closes the perfect-field transfer-sheaf endpoint. General
HI-presheaf sheafification, nonperfect fields, derived continuity, full canonical
purity and the separate global principal-family/norm/Picard program keep their
own boundaries. Positive-characteristic diagonal, higher-Chow and spectrum
comparisons remain separate.

[Source and verification records](../../../docs/provenance/perfect-strict-20261018/README.md)
separate the admitted proofs, supplied checks and independent review from the
independent source candidates outside the strict proof.

The older `StrictInvariancePerfectField` and `StrictInvarianceFiniteField`
imports remain compatibility entries. The short `StrictInvariance` entry now
selects the all-perfect-field result, while `.StrictInvariance.InfiniteField`
is the precise infinite-field implementation. Declarations retain their native
names and hypotheses.

For example, the endpoint is applied to the original coefficient object:

```lean
import Motivic.Cohomology.A1.StrictInvariance

open CategoryTheory AlgebraicGeometry Motivic

universe u

example {k : Type u} [Field k] [PerfectField k]
    [HasExt.{u + 1}
      (Sheaf (Scheme.SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant) :
    F.IsStrictA1Invariant :=
  SheafWithTransfers.isStrictA1Invariant_of_perfect F hF
```

The [existing consumer](../../../MotivicTest/PerfectFieldStrictA1Invariance.lean)
spells out the literal ordinary projection in both IsIso and bijective forms.

## Other theorem inputs and proof boundaries

Henselian/essentially-smooth derived continuity and full canonical purity retain
separate proof obligations. General higher-Chow, motives and spectrum comparisons
need their own constructions and original-map comparisons. A conditional result,
checked theorem family or finite computation does not supply a missing input.
The [historical roadmap](../../../docs/provenance/strict-a1-proof-roadmap-20261017.md)
records its own snapshot frontier rather than replacing current source statements.

See [local vanishing](LocalVanishing/README.md),
[boundary maps](Boundary/README.md), [higher images](HigherImages/README.md) and
[ordinary affine-line cohomology](../AffineLine/README.md) for complete
supplier conditions and original-map boundaries.

The retained `Motivic.Cohomology.A1.Projection` import reexports
`Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.Projection`.
It is a narrow import bridge to the generic projection geometry, with no
second object or stronger invariance theorem. General source work imports the
candidate leaf directly.

## Original HI-presheaf sheafification

The [sheafification reduction guide](Sheafification/README.md) records the
actual-unit image, dense detection, whole-cylinder input and conditional
middle-lift assembly. It distinguishes that open presheaf-entry problem from
the already-HI Nisnevich transfer-sheaf strict theorem above.
