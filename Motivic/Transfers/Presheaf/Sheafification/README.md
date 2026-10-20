# Actual sheafification image and representatives

| Exact import | Interface |
| --- | --- |
| `Motivic.Transfers.Presheaf.Sheafification.Image` | Image of the actual Nisnevich unit, HI descent and canonical unit comparison |
| `Motivic.Transfers.Presheaf.Sheafification.Representatives.Basic` | Original local representatives and their matching equations |
| `Motivic.Transfers.Presheaf.Sheafification.Representatives.Distinguished` | Representatives on a distinguished cover of a whole original cylinder |
| `Motivic.Transfers.Presheaf.Sheafification.Representatives.Affine` | Actual affine refinement retaining the full marked scheme |
| `Motivic.Transfers.Presheaf.Sheafification.Representatives.Restriction` | Restriction of the same representative, with the actual pullback overlap |
| `Motivic.Transfers.Presheaf.Sheafification.Representatives.Normalized` | The same representatives bound to one actual normalization and boundary |
| `Motivic.Transfers.Presheaf.Sheafification.MatchingPairExtension` | Extension from four simultaneous given signed-action identities |

For `k : Type u`, `[Field k]` and an original
`P : PresheafWithTransfers.{u+1} k`, let `G` be its actual transfer-preserving
Nisnevich sheafification and `I` the categorical image of the actual unit.
The image retains the original pointwise epi/mono factorization. Under
`P.IsA1Invariant`, HI descends to `I`; `I` is Nisnevich-separated and its mono
into the underlying presheaf of `G` is locally surjective. Its canonical ordinary
sheafification comparison retains the original unit equation. HI of `G` is
neither an input nor a conclusion of the image construction.

Basic representatives lift a given sheafification section on a genuine smooth
Nisnevich cover and agree over each pair of compatible test maps by monicity
of `I → G`. No HI hypothesis is needed for this local representation. The
cylinder remains the cover's whole base; the result is not a section of `I` on
the entire cylinder.

The distinguished and affine interfaces retain the original base restriction,
full marked scheme, representatives and matching equations. The monic
principal-open member is actually affine; this does not assert affineness of
the other étale member or arbitrary finite-support complements. Affine
restriction uses the original section once and the literal pullback overlap.
Normalization retains the same representatives, marked scheme and restriction
equations, without choosing new sections or frames.

`MatchingPairExtension` takes the actual correspondences and four simultaneous
action relations as inputs, preserving the correction sign. It constructs
neither their geometric witnesses nor a curve-gluing theorem. See the
[whole-cylinder and middle-lift guide](../../../Cohomology/A1/Sheafification/README.md)
for its exact role, and [original actions](../Actions/README.md) for the distinct
norm/principal/pencil interfaces.

## The same representatives with a produced section choice

[Representatives/SectionChosen](Representatives/SectionChosen.lean) supplies
`exists_sectionChosen_distinguished_nisnevichImage_representatives` in
`Motivic.PresheafWithTransfers`. For `k : Type u`, `[Field k]`,
`P : PresheafWithTransfers.{u+1} k`, an affine integral smooth-site `X` and
a section of the actual sheafification over `a1Cylinder X`, it constructs a
nonempty affine original base open, a whole-cylinder presentation, the
original open/étale distinguished cover, its full marked scheme finite over
the base, the original image representatives and their matching equations.
It then retains one nonzero coefficient restriction and an affine source open
containing the entire restricted marked fiber, with its actual Cartesian
square, original restricted representative and overlap equation.
No A1-invariance hypothesis is needed for this representative constructor.

The output also includes `OriginalRefinedSectionChoice`, defined in
[Actions/Norm/RefinedSectionChoice](../Actions/Norm/RefinedSectionChoice.lean).
`originalRefinedSectionChoice_of_square` derives the native normal Noetherian
coefficient-domain, étale/separated/quasi-compact source and finite marked
conditions from the displayed affine refinement and marked square, then invokes
one [normalization/section constructor](../../../Aglib/AlgebraicGeometry/Normalization/README.md).
The common normalization, thickening, frames and source/target sections are
therefore tied to these same original representatives.

[Representatives/RefinedRestriction](Representatives/RefinedRestriction.lean)
retains their actual source/puncture restrictions to the native refined sites.
`originalRefinedSource_representative_image` and
`originalRefinedPuncture_representative_image` preserve the original
sheafification-image equations, and `originalRefined_representatives_matching`
compares the same two restrictions over the literal overlap. These restriction statements alone do not construct an image section over
the whole cylinder. The [original-history action assembly](../Actions/README.md)
now binds the actual E3/E5 suppliers and native cover to those same
representatives. The [whole-cylinder producer](../../../Cohomology/A1/Sheafification/README.md)
constructs `ModelWholeCylinderLifting P` from `P.IsA1Invariant` and derives HI
of the actual Nisnevich sheafification over a field. With perfectness and
ordinary HasExt it also gives strict ordinary cohomological invariance.
The conditional middle-lift adapter remains usable with its explicit cover
and signed simultaneous action relations.
