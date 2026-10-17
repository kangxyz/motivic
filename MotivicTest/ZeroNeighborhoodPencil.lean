module
import Motivic.Aglib.RingTheory.ZeroNeighborhoodPencil
import Motivic.Aglib.RingTheory.ZeroNeighborhoodGlobalNumerator
/-! Direct consumers of actual interpolation, whole finite-free families, and descent. -/
set_option linter.hashCommand false
open Polynomial Polynomial.ZeroNeighborhoodInterpolation
universe u v
variable {R : Type u} [CommRing R] [Nontrivial R]

example (f : R[X]) (hf : f.Monic) (a : R)
    (h0 : IsUnit (f.eval 0)) (ha : IsUnit (f.eval a)) :
    ∃ d g : R[X], d.Monic ∧ g.Monic ∧
      Module.Finite R[X] (AdjoinRoot (pencil ((X - C a) * d) g)) ∧
      IsUnit (AdjoinRoot.mk (pencil ((X - C a) * d) g) (f.map C)) := by
  obtain ⟨d, g, hd, hg, _, _, _, hfin, _, hu, _⟩ :=
    exists_finite_free_pencil f hf a h0 ha
  exact ⟨d, g, hd, hg, hfin, hu⟩

example {S : Type v} [CommRing S] (f : R[X]) (u : Rˣ) (N : ℕ)
    (ρ : R[X] →+* S) :
    (globalNumerator f u N).map ρ =
      monicLift (f.map (ρ.comp C))
        (numeratorResidue (f.map (ρ.comp C)) (ρ X) (Units.map (ρ.comp C) u)) N :=
  globalNumerator_specialize f u N ρ

#print axioms exists_finite_free_pencil
#print axioms globalNumerator_specialize
