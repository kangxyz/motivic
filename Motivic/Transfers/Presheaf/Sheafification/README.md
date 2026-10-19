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
[conditional whole-cylinder and middle-lift guide](../../../Cohomology/A1/Sheafification/README.md)
for its exact role, and [original actions](../Actions/README.md) for the distinct
norm/principal/pencil interfaces.
