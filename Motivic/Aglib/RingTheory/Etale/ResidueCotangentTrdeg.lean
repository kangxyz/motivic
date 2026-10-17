module
public import Motivic.Aglib.RingTheory.Etale.PolynomialTrdeg
public import Motivic.Aglib.RingTheory.Etale.ResidueCoordinateCriterion
public import Motivic.Aglib.RingTheory.Kaehler.ResidueFunctionBasis

/-! # Native transcendence bounds from one actual residue cotangent dimension

Smoothness turns an original-function basis of the residue cotangent fiber into
an étale polynomial chart. That chart bounds the original domain's actual
transcendence degree. No infinite-field assumption is needed.
-/
@[expose] public noncomputable section

open Module TensorProduct KaehlerDifferential

universe u

namespace Algebra

/-- An actual original-function residue differential basis bounds the native
transcendence degree of the entire smooth domain. -/
theorem trdeg_le_of_residue_differential_basis
    (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R] [Smooth k R]
    (p : Ideal R) [p.IsPrime] {n : ℕ} (g : Fin n → R)
    (b : Basis (Fin n) (IsLocalRing.ResidueField (Localization.AtPrime p))
      (IsLocalRing.ResidueField (Localization.AtPrime p) ⊗[R] Ω[R⁄k]))
    (hb : ∀ j, b j = 1 ⊗ₜ[R] D k R (g j)) :
    Algebra.trdeg k R ≤ n := by
  obtain ⟨r, hr, he⟩ :=
    exists_etale_polynomial_map_of_residue_differential_basis k R p g b hb
  have hr0 : r ≠ 0 := by
    intro h
    exact hr (h.symm ▸ p.zero_mem)
  exact trdeg_le_of_etale_localized_polynomial_map (MvPolynomial.aeval g) hr0 he

/-- The actual cotangent dimension at any one prime bounds the native
transcendence degree of a smooth domain. Coordinates and the chart are derived. -/
theorem trdeg_le_of_residue_cotangent_finrank
    (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R] [Smooth k R]
    (p : Ideal R) [p.IsPrime] {n : ℕ}
    (hn : Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime p))
      (IsLocalRing.ResidueField (Localization.AtPrime p) ⊗[R] Ω[R⁄k]) = n) :
    Algebra.trdeg k R ≤ n := by
  obtain ⟨g, b, hb⟩ := exists_residue_basis_fin_original_functions k R
    (IsLocalRing.ResidueField (Localization.AtPrime p)) n hn
  exact trdeg_le_of_residue_differential_basis k R p g b hb

end Algebra
