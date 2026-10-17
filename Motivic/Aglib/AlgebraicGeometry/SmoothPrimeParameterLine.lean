/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.SmoothPrimeParameterChart
public import Motivic.Aglib.RingTheory.Etale.PrescribedLineCoordinate

/-! # The original prime parameter as a literal affine-line coordinate -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace Algebra

/-- A positive-rank point supplies the unchanged prime equation in an actual
etale affine-line chart, over the original ground field. -/
theorem exists_prime_parameter_etale_line_chart
    (k R : Type u) [Field k] [PerfectField k] [CommRing R]
    [Algebra k R] [Smooth k R] (p : Ideal R) [p.IsPrime]
    (hpos : 0 < ringKrullDim (Localization.AtPrime p)) :
    ∃ f ∈ p, ∃ (d : ℕ) (i : Fin d), ∃ r ∉ p,
      ∃ ψ : Polynomial (MvPolynomial {j : Fin d // j ≠ i} k) →ₐ[k] Localization.Away r,
        ψ.toRingHom.Etale ∧ ψ Polynomial.X = algebraMap R (Localization.Away r) f := by
  obtain ⟨f, hfp, d, g, i, hi, r, hr, he⟩ := exists_prime_parameter_etale_chart k R p hpos
  let h : MvPolynomial (Fin d) k →ₐ[k] Localization.Away r :=
    (IsScalarTower.toAlgHom k R (Localization.Away r)).comp (MvPolynomial.aeval g)
  obtain ⟨ψ, hψ, hx⟩ := exists_etale_line_map_of_polynomial_map k (Localization.Away r)
    d i h he
  refine ⟨f, hfp, d, i, r, hr, ψ, hψ, hx.trans ?_⟩
  change algebraMap R (Localization.Away r) ((MvPolynomial.aeval g) (MvPolynomial.X i)) = _
  rw [MvPolynomial.aeval_X, hi]

end Algebra
