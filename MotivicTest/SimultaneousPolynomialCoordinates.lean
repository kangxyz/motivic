module
import Motivic.Aglib.RingTheory.Etale.SimultaneousPolynomialCoordinates

/-! # Direct consumer on actual smooth affine algebras and nonrational primes -/
open Module TensorProduct KaehlerDifferential

example (k R : Type) [Field k] [Infinite k] [CommRing R] [Algebra k R]
    [Algebra.Smooth k R] {ι : Type} [Finite ι]
    (p : ι → Ideal R) [∀ i, (p i).IsPrime] (d : ℕ)
    (hd : ∀ i, Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime (p i)))
      (IsLocalRing.ResidueField (Localization.AtPrime (p i)) ⊗[R] Ω[R⁄k]) = d) :
    ∃ g : Fin d → R, ∀ i, ∃ r ∉ p i,
      ((algebraMap R (Localization.Away r)).comp
        (MvPolynomial.aeval (R := k) g).toRingHom).Etale :=
  Algebra.exists_simultaneous_etale_polynomial_coordinates k R p d hd
