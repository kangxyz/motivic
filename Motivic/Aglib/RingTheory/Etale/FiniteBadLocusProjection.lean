module
public import Motivic.Aglib.RingTheory.Etale.FiniteAmbientCurveProjection
public import Motivic.Aglib.RingTheory.AlgebraicIndependent.QuotientTrdeg

/-! # Finite coordinates for the whole proper bad locus in a smooth affine domain -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open Module TensorProduct KaehlerDifferential MvPolynomial
universe u v
namespace Algebra

/-- The full nonzero closed bad locus is finite over the same curve base.
No dimension estimate on the closed quotient or chosen coordinates is supplied. -/
theorem exists_finite_bad_locus_curve_projection
    (k R : Type u) [Field k] [Infinite k] [CommRing R] [IsDomain R]
    [Algebra k R] [Smooth k R] (I : Ideal R) (hI : I ≠ ⊥) (d : ℕ)
    (hR : Algebra.trdeg k R ≤ d + 1)
    {ι : Type v} [Finite ι] (p : ι → Ideal R) [∀ i, (p i).IsPrime]
    (hd : ∀ i, Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime (p i)))
      (IsLocalRing.ResidueField (Localization.AtPrime (p i)) ⊗[R] Ω[R⁄k]) = d + 1) :
    ∃ ψ : MvPolynomial (Fin (d + 1)) k →ₐ[k] R, ψ.Finite ∧
      ((Ideal.Quotient.mkₐ k I).comp (ψ.comp (MvPolynomial.rename Fin.succ))).Finite ∧
      ∀ i, ∃ r ∉ p i,
        ((algebraMap R (Localization.Away r)).comp ψ.toRingHom).Etale ∧
        RingHom.IsStandardSmoothOfRelativeDimension 1
          ((algebraMap R (Localization.Away r)).comp
            (ψ.comp (MvPolynomial.rename Fin.succ)).toRingHom) := by
  obtain ⟨ψ, hfin, hclosed, hh⟩ :=
    exists_finite_ambient_projection_etale_with_finite_closed_base
      k R I d hR (I.trdeg_quotient_le_of_ne_bot hI hR) p hd
  refine ⟨ψ, hfin, hclosed, fun i => ?_⟩
  obtain ⟨r, hr, he⟩ := hh i
  let f := (algebraMap R (Localization.Away r)).comp ψ.toRingHom
  have hf : f.IsStandardSmoothOfRelativeDimension 0 := by
    let := f.toAlgebra
    change IsStandardSmoothOfRelativeDimension 0 _ _
    exact Etale.iff_isStandardSmoothOfRelativeDimension_zero.mp he
  have hs := hf.comp (RingHom.mvPolynomial_rename_succ_standardSmooth_one k d)
  refine ⟨r, hr, he, ?_⟩
  simpa only [f, zero_add, RingHom.comp_assoc, AlgHom.comp_toRingHom] using! hs

end Algebra
