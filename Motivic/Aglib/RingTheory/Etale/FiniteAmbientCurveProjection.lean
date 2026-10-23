/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Kaehler.FiniteAmbientAndClosedProjection
public import Motivic.Aglib.RingTheory.Etale.ResidueCoordinateCriterion
public import Motivic.Aglib.RingTheory.Etale.PolynomialCurveProjection

/-! # A finite ambient map and finite bad locus with the same smooth curve base -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open Module TensorProduct KaehlerDifferential _root_.MvPolynomial
universe u v
namespace Algebra

/-- Construct an actual finite ambient coordinate map, étale near the selected
primes, whose literal base projection is finite on the whole prescribed closed locus. -/
theorem exists_finite_ambient_projection_etale_with_finite_closed_base
    (k R : Type u) [Field k] [Infinite k] [CommRing R] [Algebra k R] [Smooth k R]
    (I : Ideal R) (d : ℕ)
    (hR : Algebra.trdeg k R ≤ d + 1) (hI : Algebra.trdeg k (R ⧸ I) ≤ d)
    {ι : Type v} [Finite ι] (p : ι → Ideal R) [∀ i, (p i).IsPrime]
    (hd : ∀ i, Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime (p i)))
      (IsLocalRing.ResidueField (Localization.AtPrime (p i)) ⊗[R] Ω[R⁄k]) = d + 1) :
    ∃ ψ : MvPolynomial (Fin (d + 1)) k →ₐ[k] R, ψ.Finite ∧
      ((Ideal.Quotient.mkₐ k I).comp (ψ.comp (MvPolynomial.rename Fin.succ))).Finite ∧
      ∀ i, ∃ r ∉ p i, ((algebraMap R (Localization.Away r)).comp ψ.toRingHom).Etale := by
  let K (i : ι) := IsLocalRing.ResidueField (Localization.AtPrime (p i))
  obtain ⟨ψ, hfin, hclosed, _, θ, E, hψ, hθ⟩ :=
    exists_finite_ambient_and_closed_projection_with_initial_chart k R I d hR hI K hd
  refine ⟨ψ, hfin, hclosed, fun i => ?_⟩
  let bK := basisOfLinearIndependentOfCardEqFinrank'
    (fun j => (1 ⊗ₜ[R] D k R (θ (X j)) : K i ⊗[R] Ω[R⁄k])) (hθ i)
      (by simpa using (hd i).symm)
  obtain ⟨r, hr, he⟩ := exists_etale_polynomial_map_of_residue_differential_basis
    k R (p i) (fun j => θ (X j)) bK
      (fun j => congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _) j)
  have heq : MvPolynomial.aeval (R := k) (fun j => θ (X j)) = θ := by
    ext j
    simp
  rw [heq] at he
  have hh := RingHom.Etale.stableUnderComposition E.toAlgHom.toRingHom
    ((algebraMap R (Localization.Away r)).comp θ.toRingHom)
    (RingHom.Etale.of_bijective E.bijective) he
  refine ⟨r, hr, ?_⟩
  simpa only [hψ, AlgHom.comp_toRingHom, RingHom.comp_assoc] using! hh

end Algebra
