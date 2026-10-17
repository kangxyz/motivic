module
public import Motivic.Aglib.RingTheory.ZeroNeighborhoodInterpolation
/-! # A numerator defined before restricting to the zero-section neighborhood

The numerator uses only the unit at zero, so its source coordinate is global.
The comparison is a literal coefficient-map equality, not a descent premise.
-/
@[expose] public noncomputable section
open Polynomial
universe u v
namespace Polynomial.ZeroNeighborhoodInterpolation
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

lemma numeratorResidue_map (ρ : R →+* S) (f : R[X]) (a : R) (u : Rˣ) :
    (numeratorResidue f a u).map ρ =
      numeratorResidue (f.map ρ) (ρ a) (Units.map ρ u) := by
  simp [numeratorResidue]

lemma monicLift_map (ρ : R →+* S) (f r : R[X]) (N : ℕ) :
    (monicLift f r N).map ρ = monicLift (f.map ρ) (r.map ρ) N := by
  simp [monicLift]

/-- The first variable is the unrestricted source coordinate. -/
def globalNumerator (f : R[X]) (u : Rˣ) (N : ℕ) : R[X][X] :=
  monicLift (f.map C) (numeratorResidue (f.map C) X (Units.map (C : R →+* R[X]) u)) N

lemma globalNumerator_specialize (f : R[X]) (u : Rˣ) (N : ℕ)
    (ρ : R[X] →+* S) :
    (globalNumerator f u N).map ρ =
      monicLift (f.map (ρ.comp C))
        (numeratorResidue (f.map (ρ.comp C)) (ρ X) (Units.map (ρ.comp C) u)) N := by
  rw [globalNumerator, monicLift_map, numeratorResidue_map]
  simp only [Polynomial.map_map]
  rfl

lemma globalNumerator_monic [Nontrivial R] (f : R[X]) (hf : f.Monic)
    (u : Rˣ) (N : ℕ)
    (hN : (numeratorResidue (f.map C) X (Units.map (C : R →+* R[X]) u)).natDegree ≤ N) :
    (globalNumerator f u N).Monic :=
  (monicLift_monic_natDegree _ _ (hf.map C) N hN).1

lemma globalNumerator_zero (f : R[X]) (u : Rˣ) (N : ℕ)
    (h0 : f.eval 0 = ↑u) : (globalNumerator f u N).eval 0 = -X := by
  rw [globalNumerator, monicLift_eval_zero]
  apply numeratorResidue_eval_zero
  simpa using congrArg C h0

lemma globalNumerator_boundary (f : R[X]) (u : Rˣ) (N : ℕ) :
    f.map C ∣ globalNumerator f u N - 1 := by
  have h1 := monicLift_boundary (f.map C)
    (numeratorResidue (f.map C) X (Units.map (C : R →+* R[X]) u)) N
  have h2 := numeratorResidue_boundary (f.map C) X (Units.map (C : R →+* R[X]) u)
  convert dvd_add h1 h2 using 1
  dsimp only [globalNumerator]
  ring
end Polynomial.ZeroNeighborhoodInterpolation
