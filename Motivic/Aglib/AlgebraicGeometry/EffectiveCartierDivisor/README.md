# Proper flat Cartier subschemes of relative curves

`ProperRelativeCurve.lean` uses native `Scheme.Hom.idealModule` and
`Scheme.Modules.Invertible.IsLocallyRankOne`. For a smooth-relative-dimension-one
map `p : C → S` and closed immersion `i : D → C`, it proves:

- If the actual ideal is locally rank one and `i ≫ p` is flat and proper, then
  the original composite is finite and locally of finite presentation.
- Its actual `Scheme.Modules.pushforwardStructureSheaf (i ≫ p)` is finite
  locally free, in the existing class with genuine local basis witnesses.

The first proof consumes pinned Aglib's actual relative Cartier locality theorem
and Mathlib's proper-quasi-finite theorem. The second consumes pinned Aglib's
finite-flat direct-image theorem. The base can be nonreduced and non-Noetherian.
Flatness is retained: an absolute Cartier divisor in a relative curve can be
vertical, so ambient smoothness and properness alone do not prove finiteness.

The correspondence consumer is
`Motivic.AlgebraicGeometry.Correspondences.RelativeCartierDivisor`. It retains
boundary avoidance and the whole original divisor scheme. Standard-triple
existence, line-bundle splitting, relative Picard comparison, and A¹-homotopies
are separate unproved consumers, not hypotheses disguised as conclusions here.
