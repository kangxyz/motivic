module
import Motivic.Aglib.RingTheory.Etale.FiniteRelativeCurveCoordinates

/-! # Direct consumer: the same finite closed projection supplies the curve charts -/
open Module TensorProduct KaehlerDifferential _root_.MvPolynomial

example (k R : Type) [Field k] [Infinite k] [CommRing R] [Algebra k R]
    [Algebra.Smooth k R] (I : Ideal R) (d : ℕ)
    (htr : Algebra.trdeg k (R ⧸ I) ≤ d)
    {ι : Type} [Finite ι] (p : ι → Ideal R) [∀ i, (p i).IsPrime]
    (hd : ∀ i, Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime (p i)))
      (IsLocalRing.ResidueField (Localization.AtPrime (p i)) ⊗[R] Ω[R⁄k]) = d + 1) :
    ∃ ψ : MvPolynomial (Fin d) k →ₐ[k] R,
      ((Ideal.Quotient.mkₐ k I).comp ψ).Finite ∧ ∀ i, ∃ t : R, ∃ r ∉ p i,
        ((algebraMap R (Localization.Away r)).comp
          (MvPolynomial.aeval (R := k)
            (Fin.cons (α := fun _ => R) t (fun j => ψ (X j)))).toRingHom).Etale :=
  Algebra.exists_finite_closed_projection_with_etale_curve_charts k R I d htr p hd
