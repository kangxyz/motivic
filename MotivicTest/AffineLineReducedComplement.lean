module

import Motivic.Aglib.AlgebraicGeometry.AffineLineReducedComplement

/-! Direct consumers of the actual full reduced affine-line complement. -/

set_option linter.hashCommand false
noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent
open Motivic Motivic.AffineLineReducedComplement

universe u

variable {k : Type u} [Field k] (U : (line k).Opens)

example (hU : genericPoint (line k) ∈ U) :
    ∃ f : Polynomial k, f ≠ 0 ∧ PrimeSpectrum.basicOpen f ≤ U :=
  exists_nonzero_basicOpen U hU

example : IsReduced (closedComplement U) := inferInstance

example : IsClosedImmersion (inclusion U) := inferInstance

example : Set.range (inclusion U) = (U : Set (line k))ᶜ := range_inclusion U

example (hU : genericPoint (line k) ∈ U) :
    IsFinite (inclusion U ≫ polynomialProjection (.of k)) := finite_projection U hU

example : SmoothSite (Spec (.of k)) := openObject U

example : openObject U ⟶ SmoothSite.affineLine (.of k) := openInclusion U

example : (openInclusion U).left = U.ι := rfl

example : (openObject U).hom = U.ι ≫ polynomialProjection (.of k) := rfl

#print axioms Motivic.AffineLineReducedComplement.exists_nonzero_basicOpen
#print axioms Motivic.AffineLineReducedComplement.range_inclusion
#print axioms Motivic.AffineLineReducedComplement.finite_quotient_of_basicOpen
#print axioms Motivic.AffineLineReducedComplement.finite_projection
#print axioms Motivic.AffineLineReducedComplement.openObject
