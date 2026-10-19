/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.ZeroNeighborhoodBoundary

/-! # Actual infinity makes the target boundary nonempty

This concerns the target projective line, not the source compactification boundary.
No nonemptiness is inferred from a covering condition.


Intended upstream module: `Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Boundary.Nonempty`.
Incoming project consumers: `Motivic.Transfers.Presheaf.Actions.Norm.RefinedNormalization`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R] [Nontrivial R]

/-- The opposite-chart zero point lies in every whole projective neighborhood boundary. -/
theorem neighborhoodBoundary_nonempty (V : (Spec (.of (Polynomial R))).Opens) :
    Nonempty (neighborhoodBoundary R V) := by
  let x : Spec (.of R) := Classical.choice inferInstance
  let y := Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) x
  have hy : y ∉ (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R) :
      Set (PrimeSpectrum (Polynomial R))) := by
    rw [← Set.mem_compl_iff, ← range_affine_zero R]
    exact ⟨x, rfl⟩
  have hz : chart R (⟨1⟩ : ULift.{u} (Fin 2)) y ∈
      Set.range (neighborhoodBoundaryInclusion R V) := by
    rw [range_neighborhoodBoundaryInclusion]
    intro h
    obtain ⟨w, _, hw⟩ := h
    have hc : chart R (⟨1⟩ : ULift.{u} (Fin 2)) y ∈
        ProjectiveSpace.coordinateOpen R (ULift.{u} (Fin 2)) ⟨0⟩ := by
      rw [← chart_opensRange]
      exact ⟨w, hw⟩
    apply hy
    rw [← chart_preimage_other R ⟨1⟩ ⟨0⟩ (by decide)]
    exact hc
  obtain ⟨b, _⟩ := hz
  exact ⟨b⟩

end AlgebraicGeometry.RelativeProjectiveLine
