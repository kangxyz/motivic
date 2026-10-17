# Finite correspondence geometry

The existing `Category.lean` implements the actual signed finite-correspondence
category on smooth separated finite-type schemes over a field. The following
focused leaves add finite-flat and relative-divisor producers on that category.

## Whole finite-flat supports

`FiniteFlat.lean` supplies `Motivic.Cor.ofFiniteFlatSpan` and its faithful cycle
equation. A finite flat map `D → X` and a compatible map `D → Y` give an actual
`Cor(X,Y)`. Smooth `X` and `Y` may be disconnected. The whole finite scheme need
not be reduced; its map to the product need not be a closed immersion. Every
generic component contributes its original local length times the actual residue
degree. Components with the same image contribute by addition.

The lower `FiniteFlatCorrespondence.cycleAssembly` works over arbitrary schemes
with the stated finite, flat, separated-target, finite-type-target, and Noetherian
support hypotheses. Generic-image admissibility is proved from finite flatness;
finite morphisms alone do not preserve generic components.

`MotivicTest/FiniteFlatCorrespondence.lean` checks the actual category endpoint, empty
support, equality with the old irreducible closed-support implementation, and
standard-axiom dependency rejection. The older
`FiniteFlatCurveFamily.lean` additionally proves affine-line endpoint graph
restriction; the new arbitrary-source assembly does not claim that comparison.

## Proper relative Cartier divisors and boundary avoidance

`RelativeCartierDivisor.lean` supplies
`Motivic.RelativeCartierDivisor.correspondence` and
`toIntegralCycle_correspondence`. Its input is:

- A smooth-relative-dimension-one `p : C → X`
- A closed immersion `i : D → C` whose actual ideal is locally rank one
- Flatness and properness of the actual composite `D → X`
- An open immersion `j : U → C` containing the entire image of `D`
- A compatible target map `U → Y`

The native Cartier producer proves finiteness, local finite presentation, and
finite local freeness of the actual structure-sheaf direct image. The actual
open-immersion lift defines the target map on the unchanged divisor scheme.
The faithful underlying cycle is its full fundamental-cycle pushforward.
Neither irreducibility, reducedness, perfection, infinitude, nor a characteristic
restriction is imposed. `MotivicTest/RelativeCartierDivisor.lean` checks arbitrary-base
local freeness, the literal boundary lift, the full cycle, the identity-open case,
and standard axioms.

## Remaining standard-triple prerequisites

The present producers do not construct standard triples or their splittings.
The following are still missing for the MVW route; existing shrinking and
semilocal algebra must be reused rather than re-proved.

1. Actual diagonal line bundle, semilocal trivialization, and extension of its
   trivialization to a neighborhood containing finitely many complete fibers.
   Mathlib already proves semilocal-ring Picard triviality; this project already
   proves finite closed-image shrinking.
2. Boundary-trivialized relative Picard classes represented by relative divisors,
   with principal relations realized by actual A¹-correspondence families.
3. Compatible splittings and boundary-unit corrections along covering triples,
   including norm compatibility and the equations for the Mayer–Vietoris homotopy.
4. Geometric standard-triple existence near finite point sets, followed by the
   finite-field transfer-degree descent.

Source scope: [MVW](https://sites.math.rutgers.edu/~weibel/MVWnotes/prova-hyperlink.pdf),
11.5–11.18 and 21.3–21.10. These are future geometric proof obligations;
no splitting, Gersten resolution, or strict A¹-invariance hypothesis is added to
the new results.
