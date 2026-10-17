module
import Motivic.Aglib.RingTheory.Kaehler.ResidueFunctionBasis
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-! # Actual prime-residue cotangent basis without a chosen coordinate chart -/
open Module TensorProduct KaehlerDifferential

example (k R : Type) [Field k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (p : Ideal R) [p.IsPrime] :
    ∃ (s : Set R), s.Finite ∧
      ∃ b : Basis s p.ResidueField (p.ResidueField ⊗[R] Ω[R⁄k]),
        ∀ j, b j = 1 ⊗ₜ[R] D k R j :=
  exists_residue_basis_original_functions k R p.ResidueField
