module
import Motivic.Aglib.RingTheory.Etale.FiniteAmbientCurveProjection

/-! # Original ambient algebra and whole closed quotient share one finite coordinate system -/
open Module TensorProduct KaehlerDifferential MvPolynomial

example (k R : Type) [Field k] [Infinite k] [CommRing R] [Algebra k R]
    [Algebra.Smooth k R] (I : Ideal R) (d : ℕ)
    (hR : Algebra.trdeg k R ≤ d + 1) (hI : Algebra.trdeg k (R ⧸ I) ≤ d)
    {ι : Type} [Finite ι] (p : ι → Ideal R) [∀ i, (p i).IsPrime]
    (hd : ∀ i, Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime (p i)))
      (IsLocalRing.ResidueField (Localization.AtPrime (p i)) ⊗[R] Ω[R⁄k]) = d + 1) :
    ∃ ψ : MvPolynomial (Fin (d + 1)) k →ₐ[k] R, ψ.Finite ∧
      ((Ideal.Quotient.mkₐ k I).comp (ψ.comp (MvPolynomial.rename Fin.succ))).Finite ∧
      ∀ i, ∃ r ∉ p i, ((algebraMap R (Localization.Away r)).comp ψ.toRingHom).Etale :=
  Algebra.exists_finite_ambient_projection_etale_with_finite_closed_base k R I d hR hI p hd
