module
import Motivic.Aglib.RingTheory.Kaehler.SimultaneousResidueCoordinates
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-! # Common original functions at actual nonrational prime residues -/
open Module TensorProduct KaehlerDifferential

example (k R : Type) [Field k] [Infinite k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] {ι : Type} [Finite ι]
    (p : ι → Ideal R) [∀ i, (p i).IsPrime] (d : ℕ)
    (hd : ∀ i, Module.finrank (p i).ResidueField ((p i).ResidueField ⊗[R] Ω[R⁄k]) = d) :
    ∃ g : Fin d → R, ∀ i,
      LinearIndependent (p i).ResidueField
        (fun j => (1 ⊗ₜ[R] D k R (g j) : (p i).ResidueField ⊗[R] Ω[R⁄k])) :=
  exists_simultaneous_residue_differential_coordinates k R (fun i => (p i).ResidueField) d hd
