# HI-presheaf sheafification and strict invariance

| Exact import | Interface |
| --- | --- |
| `Motivic.Cohomology.A1.Sheafification.HomotopyInvariance` | HI of the actual Nisnevich sheafification over a field |
| `Motivic.Cohomology.A1.Sheafification.StrictInvariance` | Strict ordinary cohomological invariance over a perfect field |
| `Motivic.Cohomology.A1.Sheafification.WholeCylinderLifting` | Constructed lifting on a whole cylinder over a nonempty base open |
| `Motivic.Cohomology.A1.Sheafification.DenseDetection` | Original dense restrictions without assuming target HI |
| `Motivic.Cohomology.A1.Sheafification.CylinderCriterion` | Reusable assembly from an explicit lifting datum |
| `Motivic.Cohomology.A1.Sheafification.MiddleLiftDifference` | Signed action relations and actual-cover lifting |

## Public theorem and hypotheses

For `k : Type u`, `[Field k]` and
`P : PresheafWithTransfers.{u + 1} k`, the theorem
`Motivic.PresheafWithTransfers.nisnevichSheafify_isA1Invariant P hP`
proves that `((nisnevichSheafify k).obj P).obj` is HI from
`hP : P.IsA1Invariant`. The coefficient is the actual transfer-preserving
Nisnevich sheafification of the original presheaf. Perfectness, target HI and
a whole-cylinder lifting premise are absent from this statement.

With `[PerfectField k]` and ordinary `HasExt.{u + 1}` on
`Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}`,
`Motivic.PresheafWithTransfers.nisnevichSheafify_isStrictA1Invariant P hP`
proves `((nisnevichSheafify k).obj P).IsStrictA1Invariant`. Thus, for every
`n : ℕ` and smooth-site `X`, the literal map

```lean
(CategoryTheory.Sheaf.LargeCohomology.presheaf
  (SmoothSite.nisnevichTopology (Spec (.of k)))
  ((SheafWithTransfers.toSheaf k).obj ((nisnevichSheafify k).obj P)) n).map
    (SmoothSite.a1Projection (.of k) X).op
```

is an isomorphism, with the original degree and coefficient universes. This
uses the [perfect-field transfer-sheaf theorem](../README.md) after proving
HI of this very coefficient sheaf. Ordinary degree zero follows from HI over
an arbitrary field with HasExt; perfectness is needed for the stated
all-degree result. Nonperfect strict invariance, other coefficient universes,
derived continuity, higher-Chow and spectrum comparisons have their separate
boundaries.

## Constructed lifting and original maps

`modelWholeCylinderLifting_of_isA1Invariant P hP` constructs
`ModelWholeCylinderLifting P`. Given an affine integral smooth `X` and a
section of the actual sheafification on `X × A1`, it produces an open immersion
`U ⟶ X`, `Nonempty U.left` and an image section on the **whole** `U × A1`,
with the original sheafification-unit equation. The base open `U` need not be
affine. A dense open of the total cylinder is not substituted for this output.

The proof follows one original normalization and section history:

1. [OriginalHistory](../../../Transfers/Presheaf/Actions/Norm/NativeRefinement/OriginalHistory.lean)
   binds the original source, target and raw-difference suppliers to the same
   history and witnesses.
2. [OriginalHistoryMiddleRelations](../../../Transfers/Presheaf/Actions/Pencils/OriginalHistoryMiddleRelations.lean)
   derives the simultaneous image-action identities from those suppliers.
3. [OriginalHistoryLine](../../../Transfers/Presheaf/Actions/Norm/NativeRefinement/OriginalHistoryLine.lean)
   and [OriginalHistoryRestrictions](../../../Transfers/Presheaf/Actions/Norm/NativeRefinement/OriginalHistoryRestrictions.lean)
   supply the native-owned line, actual Nisnevich cover and restriction squares.
4. [OriginalHistoryLifting](OriginalHistoryLifting.lean) joins that diagram to
   the original matching representatives; [WholeCylinderLifting](WholeCylinderLifting.lean)
   constructs the choices and removes the lifting premise.
5. [HomotopyInvariance](HomotopyInvariance.lean) applies dense detection and
   the cylinder criterion. [StrictInvariance](StrictInvariance.lean) applies
   the existing all-perfect-field result to the resulting HI sheaf.

The actual-unit image remains HI and separated rather than being assumed a
sheaf. The actual sheafification detects equality on the constructed cover;
all original graph, restriction and unit maps and the E3 correction sign are
retained. No raw-zero, middle-relations or target-HI hypothesis is added to
the public theorem.

## Reusable conditional interfaces and verification

`nisnevichSheafify_isA1Invariant_of_modelWholeCylinderLifting` and
`nisnevichSheafify_isStrictA1Invariant_of_modelWholeCylinderLifting` remain
available for callers with an independently supplied lifting datum. The middle
adapters likewise retain their explicit cover, representatives and simultaneous
action relations. Their hypotheses describe those general interfaces; they
are discharged by the original-history producer for the public theorem.

[HIPresheafSheafificationReduction](../../../../MotivicTest/HIPresheafSheafificationReduction.lean)
contains consumers of the unconditional HI, arbitrary-field degree-zero and
perfect-field all-degree signatures, the conditional APIs and standard axioms.
The [integration record](../../../../docs/provenance/hi-presheaf-sheafification-20261020/README.md)
separates current validation from supplied historical receipts and indexes the
preserved experiments. Ordinary mathematical review passed relative to its
recorded baseline. The integration record gives current compilation, exact-origin
lint and transitive standard-axiom coverage at their recorded source snapshots.
Hosted execution is reported separately. Production imports no recovery
snapshots or diagnostics.
