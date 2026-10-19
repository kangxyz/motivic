# Finite correspondence geometry

The existing `Basic.lean` implements the actual signed finite-correspondence
category on smooth separated finite-type schemes over a field. The following
focused leaves add finite-flat and relative-divisor producers on that category.

| Exact import below `Motivic.AlgebraicGeometry.Correspondences` | Interface |
| --- | --- |
| `Basic` | Actual signed finite-correspondence category `Motivic.Cor k` |
| `Graph.Functor` | The original scheme graph functor into correspondences |
| `Coproducts.Finite` | Finite coproduct interfaces on those same objects |
| `Spans.FiniteFlat.Basic` | `Motivic.Cor.ofFiniteFlatSpan` and its faithful cycle equation |
| `Endpoints.Cartier.Divisor` | Original divisor correspondence and boundary lift |

The focused facade `Motivic.AlgebraicGeometry.Correspondences` exports the first
three leaves. Smooth sites, signed integral cycles and lower ring/Tor identities
precede their geometric composition and incidence applications.

## Public consumer

```lean
import Motivic

open CategoryTheory

noncomputable example (k : Type*) [Field k] : Category (Motivic.Cor k) := inferInstance
```

Use exact lower imports for implementation work. This public category consumer
does not import every proof leaf or establish any additional theorem inputs.

## Whole finite-flat supports

`Spans/FiniteFlat/Basic.lean` supplies `Motivic.Cor.ofFiniteFlatSpan` and its faithful cycle
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
`Spans/FiniteFlat/CurveFamily.lean` additionally proves affine-line endpoint graph
restriction; the new arbitrary-source assembly does not claim that comparison.
Its actual correspondence-generating APIs retain the host namespace
`Motivic.FiniteFlatCurveFamily`. The pure field/line/ambient/component-support
helpers have the separate native
`AlgebraicGeometry.Scheme.SmoothSite.AffineLineField` owner in
`Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.Field`.


## Proper relative Cartier divisors and boundary avoidance

`Endpoints/Cartier/Divisor.lean` supplies
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
The complete MVW standard-triple route retains the following assembly
obligations. Reuse the already available general shrinking, line-bundle frames
and pencil interfaces rather than re-proving their lower statements.

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

The remaining standard-triple route is separate from the implemented
[perfect-field strict theorem](../../Cohomology/A1/README.md); it should not be
read as that theorem's current prerequisite list. [Architecture](../../../docs/ARCHITECTURE.md)
records the model and comparison boundaries for future extensions.

General scheme, cycle, graph and intersection prerequisites have the
[candidate geometry owner](../../Aglib/AlgebraicGeometry/README.md). Their
full general interfaces stay there; this family owns their actual correspondence
specializations and transfer actions.

## Original principal-family endpoints

`Motivic.AlgebraicGeometry.Correspondences.Moving.Polynomial.PrincipalFamilyEndpoints` concerns the literal signed
principal family: composition with its zero graph is zero, and composition with
its one graph is the original transported principal-order correspondence.
Whole support multiplicities, residue degrees and collision sums are retained.
Only the individual support maps need be finite; global parameter-forgetting
finiteness and support flatness are not introduced.

This endpoint retains an affine integral smooth source, an integral Noetherian
proper compactification with quasi-affine smooth relative-curve retained open,
an integral Noetherian boundary neighborhood, a nonempty actual boundary
covering the entire omitted locus, and an original function invertible on that
whole neighborhood with boundary value one. It is not the simultaneous
standard-triple splitting theorem or a whole-cylinder lifting producer. Its
[HI-presheaf action consumer](../../Transfers/Presheaf/README.md) keeps the same
original maps and signs and does not assume sheafification HI.
