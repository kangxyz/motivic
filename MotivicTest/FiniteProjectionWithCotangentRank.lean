module
import Motivic.Aglib.RingTheory.Kaehler.FiniteProjectionWithCotangentRank
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-! # Actual closed quotient and prime-residue consumer of the full elimination induction -/
open Module TensorProduct KaehlerDifferential _root_.MvPolynomial

example (k R : Type) [Field k] [Infinite k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (I : Ideal R) (d : ℕ)
    (htr : Algebra.trdeg k (R ⧸ I) ≤ d)
    {ι : Type} [Finite ι] (p : ι → Ideal R) [∀ i, (p i).IsPrime]
    (hdim : ∀ i, Module.finrank (p i).ResidueField ((p i).ResidueField ⊗[R] Ω[R⁄k]) = d + 1) :
    ∃ ψ : MvPolynomial (Fin d) k →ₐ[k] R,
      ((Ideal.Quotient.mkₐ k I).comp ψ).Finite ∧ ∀ i,
        LinearIndependent (p i).ResidueField
          (fun j => (1 ⊗ₜ[R] D k R (ψ (X j)) : (p i).ResidueField ⊗[R] Ω[R⁄k])) :=
  exists_finite_closed_projection_independent_differentials k R I d (d + 1)
    (Nat.le_succ d) htr (fun i => (p i).ResidueField) hdim
