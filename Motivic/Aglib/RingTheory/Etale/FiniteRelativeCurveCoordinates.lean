module
public import Motivic.Aglib.RingTheory.Etale.RelativeCurveCoordinateCriterion
public import Motivic.Aglib.RingTheory.Kaehler.FiniteProjectionWithCotangentRank

/-! # Finite closed projection with the same actual relative-curve coordinates

The iterative finite elimination and smooth local charts share their literal
base functions. The original closed quotient, including nilpotents, is retained.
-/
@[expose] public noncomputable section
open Module TensorProduct KaehlerDifferential MvPolynomial
universe u v
namespace Algebra

/-- Over an infinite field, a closed quotient of transcendence degree at most `d`
admits a finite projection whose same base coordinates extend to actual étale
curve charts at every selected prime of cotangent dimension `d+1`. -/
theorem exists_finite_closed_projection_with_etale_curve_charts
    (k R : Type u) [Field k] [Infinite k] [CommRing R] [Algebra k R] [Smooth k R]
    (I : Ideal R) (d : ℕ) (htr : Algebra.trdeg k (R ⧸ I) ≤ d)
    {ι : Type v} [Finite ι] (p : ι → Ideal R) [∀ i, (p i).IsPrime]
    (hd : ∀ i, Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime (p i)))
      (IsLocalRing.ResidueField (Localization.AtPrime (p i)) ⊗[R] Ω[R⁄k]) = d + 1) :
    ∃ ψ : MvPolynomial (Fin d) k →ₐ[k] R,
      ((Ideal.Quotient.mkₐ k I).comp ψ).Finite ∧ ∀ i, ∃ t : R, ∃ r ∉ p i,
        ((algebraMap R (Localization.Away r)).comp
          (MvPolynomial.aeval (R := k)
            (Fin.cons (α := fun _ => R) t (fun j => ψ (X j)))).toRingHom).Etale := by
  let K (i : ι) := IsLocalRing.ResidueField (Localization.AtPrime (p i))
  obtain ⟨ψ, hψ, hdiff⟩ := exists_finite_closed_projection_independent_differentials
    k R I d (d + 1) (Nat.le_succ d) htr K hd
  exact ⟨ψ, hψ, fun i => exists_etale_curve_chart_preserving_coordinates
    k R (p i) (fun j => ψ (X j)) (hd i) (hdiff i)⟩

end Algebra
