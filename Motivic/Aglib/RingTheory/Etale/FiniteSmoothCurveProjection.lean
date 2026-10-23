/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Etale.FiniteRelativeCurveCoordinates
public import Motivic.Aglib.RingTheory.Etale.PolynomialCurveProjection

/-! # Actual finite projection smooth of relative dimension one at selected primes -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open Module TensorProduct KaehlerDifferential _root_.MvPolynomial
universe u v
namespace Algebra

/-- The literal finite closed projection is smooth of relative dimension one on
actual principal neighborhoods of all selected primes. -/
theorem exists_finite_closed_projection_smooth_relative_one
    (k R : Type u) [Field k] [Infinite k] [CommRing R] [Algebra k R] [Smooth k R]
    (I : Ideal R) (d : ℕ) (htr : Algebra.trdeg k (R ⧸ I) ≤ d)
    {ι : Type v} [Finite ι] (p : ι → Ideal R) [∀ i, (p i).IsPrime]
    (hd : ∀ i, Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime (p i)))
      (IsLocalRing.ResidueField (Localization.AtPrime (p i)) ⊗[R] Ω[R⁄k]) = d + 1) :
    ∃ ψ : MvPolynomial (Fin d) k →ₐ[k] R,
      ((Ideal.Quotient.mkₐ k I).comp ψ).Finite ∧ ∀ i, ∃ r ∉ p i,
        RingHom.IsStandardSmoothOfRelativeDimension 1
          ((algebraMap R (Localization.Away r)).comp ψ.toRingHom) := by
  obtain ⟨ψ, hψ, hh⟩ := exists_finite_closed_projection_with_etale_curve_charts
    k R I d htr p hd
  refine ⟨ψ, hψ, fun i => ?_⟩
  obtain ⟨t, r, hr, he⟩ := hh i
  let g : Fin d → Localization.Away r := fun j => algebraMap R _ (ψ (X j))
  have heq : (MvPolynomial.aeval (R := k)
      (Fin.cons (α := fun _ => Localization.Away r) (algebraMap R _ t) g)).toRingHom =
      (algebraMap R (Localization.Away r)).comp
        (MvPolynomial.aeval (R := k)
          (Fin.cons (α := fun _ => R) t (fun j => ψ (X j)))).toRingHom := by
    ext j
    · simpa using (IsScalarTower.algebraMap_apply k R (Localization.Away r) j)
    · cases j using Fin.cases <;> simp [g]
  have hs := RingHom.etale_cons_base_standardSmooth_one k (Localization.Away r)
    (algebraMap R _ t) g (heq.symm ▸ he)
  have hbase : (MvPolynomial.aeval (R := k) g).toRingHom =
      (algebraMap R (Localization.Away r)).comp ψ.toRingHom := by
    ext j
    · simpa using (IsScalarTower.algebraMap_apply k R (Localization.Away r) j)
    · simp [g]
  exact ⟨r, hr, hbase ▸ hs⟩

end Algebra
