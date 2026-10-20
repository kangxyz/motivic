# Original pencil, norm and principal actions

| Exact import | Interface |
| --- | --- |
| `Motivic.Transfers.Presheaf.Actions.Pencils.CorrectionBoundary` | Pole-minus-numerator correction from the original boundary-compatible pair |
| `Motivic.Transfers.Presheaf.Actions.Pencils.GraphBoundary` | Numerator-minus-pole graph action on the actual whole zero schemes |
| `Motivic.Transfers.Presheaf.Actions.Pencils.Correction` | The literal retained-curve correction from the same global sections |
| `Motivic.Transfers.Presheaf.Actions.Pencils.Graph` | The literal retained-curve identity graph action |
| `Motivic.Transfers.Presheaf.Actions.Pencils.LambdaDictionary` | Original lambda/psi and whole-zero correspondence identities |
| `Motivic.Transfers.Presheaf.Actions.Norm.OriginalPair` | Original numerator-minus-pole norm-action comparison |
| `Motivic.Transfers.Presheaf.Actions.Principal.Family` | Null action of the original principal correspondence |
| `Motivic.Transfers.Presheaf.Actions.Principal.Open` | The same principal action on its original open and canonical germ |

## Fixed sections and pencil actions

Pencil actions retain the original global numerator, denominator, boundary
frames, compactification, cover and whole finite-flat zero schemes. The
correction orientation is pole minus numerator; the graph action uses numerator
minus pole. Actual zero-scheme isomorphisms and retained-open inclusions identify
the original actions. No replacement section or assumed action equality is
substituted. A fixed section-data record and its projection must remain together;
an independent `Nonempty` witness does not identify its selected sections or
frame with that fixed record without the required compatibility.

## Norm actions and full boundary inputs

`transfer_originalPair_norm_difference_eq` compares literal `P.obj.map`
actions for HI presheaves with transfers in an independent coefficient universe.
It retains an affine integral parameter `X`, flat parameter maps, the integral
Noetherian proper compactified target, quasi-affine smooth relative-curve opens,
original finite sources, local-free neighborhoods, and every displayed original
and pulled-functional regularity/invertibility condition. Neither finite source
is assumed integral. A component-reduction comment does not remove the theorem's
integral `X` premise.

The canonical norm-germ ratio must be represented by a unit on a nonempty
whole-boundary neighborhood. A nonempty actual boundary covers the entire
omitted locus and pulls the unit back to one as a scheme-level equation,
including nilpotents. The retained-open comparison needs actual map commutation;
separate parameter-change Cartesian squares remain required. Original section
choices, target maps and numerator-minus-pole signs are retained. These are
explicit inputs, not consequences of the action equality.

## Principal actions and the assembly boundary

Principal actions retain an affine integral smooth source, an integral
Noetherian proper compactification with quasi-affine smooth relative-curve
retained open, an integral Noetherian boundary neighborhood, and a function
invertible on that whole neighborhood. The nonempty actual boundary covers the
whole omitted locus and has literal value one. The original principal family
and its zero/one graph endpoints give the null action; no sheaf condition or
HI of sheafification is assumed. The open sibling preserves the same original
open, section and canonical function-field germ.

The principal-action leaves supply individual relations. The original-history
assembly below joins them on the [actual unit image](../Sheafification/README.md)
using the same geometric witnesses. The [A1 sheafification guide](../../../Cohomology/A1/Sheafification/README.md)
owns the resulting whole-cylinder producer. General norm geometry and zero-cycle
maps have their [candidate owners](../../../Aglib/AlgebraicGeometry/Morphisms/Finite/README.md).

## Native R3/R5 principal actions from fixed section records

The [general constructors](../../../Aglib/AlgebraicGeometry/RelativeCurve/Pencils/README.md)
produce normalized units from the original section records. In the native
namespace `Motivic.PresheafWithTransfers`,
[Pencils/NativeSectionPairTransferAction](Pencils/NativeSectionPairTransferAction.lean)
supplies `exists_nativeSectionPairPrincipalAction_zero` on each actual integral
parameter component; [NativeCorrectionNormAction](Pencils/NativeCorrectionNormAction.lean)
supplies `exists_nativeCorrectionPrincipalAction_zero` on the original
nonempty affine puncture. The former keeps `PresheafWithTransfers.{w} k`, the
latter `PresheafWithTransfers.{v} k`, with these coefficient universes independent
of `k : Type u`. Both take `Pst.IsA1Invariant` and an actual smooth coefficient
structure map. Neither takes a sheaf hypothesis or HI of sheafification.

The interfaces retain the normal Noetherian original coefficient domain,
actual finite map and whole free charts, flat retained map and its literal
commuting equation, open smooth relative curves, Cartesian marked square,
fixed `BoundarySectionData`, target Serre divisor data, prescribed full-boundary
frames/units, actual residual and inverse-infinity factors, and the displayed
small-open cover conditions. The R3 statement also retains the original source
normalization and its component cover. The R5 statement retains its original
small retained target map and structure equation. Their conclusions construct
the good open, regular unit, original generic germ, nonempty whole boundary,
its factor and complement cover, value one, and zero action of the corresponding
`PrincipalOrderCorrespondence.correspondence`. The units and their boundary
equalities are outputs; they are not an assumed normalization tuple.

[Pencils/NativeOriginalRestrictionActions](Pencils/NativeOriginalRestrictionActions.lean)
gives `BoundarySectionData.native_original_restriction_actions`, retaining
the same source record for the E2/E4 restrictions.
[OriginalPairNormDictionary](Pencils/OriginalPairNormDictionary.lean) identifies
the literal lambda and psi correspondences with original whole-zero terms:
lambda is numerator minus pole, while psi is denominator minus numerator.
[OriginalTargetLambda](Pencils/OriginalTargetLambda.lean) defines the one target
lambda used by the two middle comparisons. All comparison targets must be
identified with this same datum and actual map.

## Original differences and the E3 zero-action APIs

[Pencils/NativeOriginalPairTransferAction](Pencils/NativeOriginalPairTransferAction.lean)
is an intermediate consumer: `Motivic.Cor.originalComponentLambda_eq_principal`
retains its normalized-unit, generic-germ, full-boundary, normality and free-chart
inputs, with integral Noetherian parameter product `T`.
[OriginalComponentLambdaDifference](Pencils/OriginalComponentLambdaDifference.lean)
names the literal original component difference and its principal comparison;
[OriginalLambdaDifference](Pencils/OriginalLambdaDifference.lean) names the
one global difference. In the shared target, write

`δ = λB ; graph(uA) − graph(p) ; λA`,

where `λB` comes from the fixed source `BoundarySectionData`, `λA` is
`originalTargetLambda` of the fixed target pair and `uA` is the smooth-site
arrow induced by the displayed small-target map `vA`. Then
`originalComponentLambdaDifference_eq_comp_originalLambdaDifference`
identifies `δᵢ` with `graph(αᵢ) ; δ` for the actual component inclusion.
All original graph, restriction and target maps are retained.
[OriginalComponentLambdaDifferenceAction](Pencils/OriginalComponentLambdaDifferenceAction.lean)
and `originalLambda_action_eq_of_difference_zero` are additive bridges:
they turn zero action of the supplied difference into the two original action
equalities. Their difference-zero premise remains explicit; they require no
HI or sheaf hypothesis for that additive implication.

[NativeSectionPairPrincipalPresentation](Pencils/NativeSectionPairPrincipalPresentation.lean)
identifies the two principal presentations on the same schemes, arrows, open,
function and unit witness; only proof and smooth-site instance presentations
differ. [NativeSectionPairCanonicalPrincipalAction](Pencils/NativeSectionPairCanonicalPrincipalAction.lean)
constructs the R3 tuple with zero action in this canonical presentation.
[NativeSectionPairCorSpecialization](Pencils/NativeSectionPairCorSpecialization.lean)
specializes the original correspondence comparison to that same tuple and
Cartesian generic germ, retaining its displayed unit/germ premises.
Neither comparison assumes a desired correspondence or action equality.

[NativeSectionPairDifferenceZero](Pencils/NativeSectionPairDifferenceZero.lean)
supplies `transfer_nativeSectionPair_originalDifference_zero` for
`Pst : PresheafWithTransfers.{w} k` with `Pst.IsA1Invariant`.
It constructs the normalized tuple internally on each actual integral component.
Its source hypotheses retain the original normalization and component cover,
finite/free projective charts, flat retained map, fixed source section record,
target Serre divisor data, full marked/infinity frames, residual and
inverse-infinity factors, small-target compatibility and original cover
conditions. No desired zero-action relation is an input.
[NativeSectionPairGlobalDifferenceZero](Pencils/NativeSectionPairGlobalDifferenceZero.lean)
supplies `nisnevichImage_transfer_nativeSectionPair_originalDifference_zero`
for `P : PresheafWithTransfers.{u+1} k` with `P.IsA1Invariant`. It descends the
component result by separatedness of the actual Nisnevich image, using the
literal global difference. Empty or disconnected sources are included; the
whole source need not be integral.

## The original E5 pair and psi endpoints

[Pencils/NativeCorrectionPairMiddle](Pencils/NativeCorrectionPairMiddle.lean)
defines `Motivic.Cor.originalPairMarkedMiddle` as the target numerator-minus-pole
correspondence, minus the correction denominator-minus-numerator correspondence,
minus the actual restriction graph. Its canonical and generic original finite-pair presentations land in
this one middle term. The empty-parameter branch gives the zero correspondence.
[OriginalPairMarkedNormMiddle](Pencils/OriginalPairMarkedNormMiddle.lean)
then retains the complete original norm-product telescope and genuine norm-germ
premise when comparing that middle term to the principal correspondence.
This wrapper does not construct the norm-germ input.

[NativeCorrectionTransferAction](Pencils/NativeCorrectionTransferAction.lean)
supplies `transfer_nativeCorrection_originalPairs` and
`transfer_nativeCorrection_originalPsi`. They keep
`Pst : PresheafWithTransfers.{v} k`, `Pst.IsA1Invariant`, the actual smooth
field-structure map, fixed source record `c`, target pair and `iA` divisor
witnesses, original full-boundary equations, residual/infinity factors,
whole free charts and all displayed small-target/restriction compatibilities.
The normalized unit and generic germ are constructed from those same sections.
The public statements include an empty `A` branch rather than assuming
nonemptiness of that parameter. In schematic notation their sign is

`transfer(graph(a);λA) = transfer(ψ;graph(uA)) + transfer(graph(rA))`.

Here `rA : A ⟶ U` is the displayed small parameter map with `rA ≫ u = a`;
the source theorem uses `correctionSmallParameterMap` for its smooth-site
arrow. The graph is not silently replaced by an identity. The target identity
leg of the finite-pair norm diagram takes no norm along a parameter-change map.
The revised archive has selected production/trust evidence for these two
endpoints and for the local/global E3 difference-zero APIs; current native
coverage is recorded separately in
[provenance](../../../../docs/provenance/normalization-recovery-20261019/README.md)
under every displayed premise.

## Refined covers and the original-history joins

[Components/NisnevichImage](Components/NisnevichImage.lean) detects transfer
equality on a given Nisnevich or open cover.
[NativeOriginalComponentActions](Pencils/NativeOriginalComponentActions.lean)
uses the actual native component cover for that detection. The older individual
refined-cover APIs retain their displayed coordinates and restriction premises.

[OriginalHistory](Norm/NativeRefinement/OriginalHistory.lean) binds the actual
source and target suppliers and the raw E3 difference to one normalization
history. [OriginalHistoryMiddleRelations](Pencils/OriginalHistoryMiddleRelations.lean)
then proves the simultaneous image-action relations on those same witnesses.
[OriginalHistoryLine](Norm/NativeRefinement/OriginalHistoryLine.lean) and
[OriginalHistoryRestrictions](Norm/NativeRefinement/OriginalHistoryRestrictions.lean)
construct the native-owned cover and original restriction squares for the same
line. The host lifting assembly consumes them with the original matching
representatives, preserving the E3 difference sign and every graph/unit map.

The [difference-form middle-lift adapter](../../../Cohomology/A1/Sheafification/README.md)
continues to accept explicit cover and E2/E3-difference/E4/E5 relations. The
original-history producer now discharges those inputs for an original HI
presheaf, yielding `modelWholeCylinderLifting_of_isA1Invariant` and actual
sheafification HI. Perfectness and ordinary HasExt give strict invariance in
all degrees; nonperfect strict invariance remains outside this result.
Superseded external comparison attempts and diagnostics are preserved in the
[integration recovery archive](../../../../docs/provenance/hi-presheaf-sheafification-20261020/README.md).
