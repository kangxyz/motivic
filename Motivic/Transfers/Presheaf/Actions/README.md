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

These original-presheaf actions do not construct the simultaneous four actions
on the [actual unit image](../Sheafification/README.md), their common geometric
witnesses, or the input of the [conditional A1 assembly](../../../Cohomology/A1/Sheafification/README.md).
The latter guide owns the open whole-cylinder boundary. General norm geometry
and zero-cycle maps have their [candidate owners](../../../Aglib/AlgebraicGeometry/Morphisms/Finite/README.md).
