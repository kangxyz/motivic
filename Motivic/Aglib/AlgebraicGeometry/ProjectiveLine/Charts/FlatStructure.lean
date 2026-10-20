/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Charts.Basic
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# Flatness of the relative projective-line structure map

The native structure map over any commutative ring is flat, as verified on the
actual two polynomial charts. No nonzero, reducedness, or field hypothesis occurs.

Intended upstream module: `Aglib.AlgebraicGeometry.ProjectiveLine.Charts.FlatStructure`.
Current direct consumer: `ProjectiveLine.BaseChange.TwoLocalizationBoundaryGeometry`
under the same candidate root.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.RelativeProjectiveLine

/-- The projective-line structure map is flat, checked on its two polynomial charts. -/
theorem toSpec_flat (R : Type u) [CommRing R] :
    Flat (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) := by
  let 𝒰 : (ProjectiveSpace R (ULift.{u} (Fin 2))).OpenCover :=
    Scheme.Cover.mkOfCovers (ULift.{u} (Fin 2))
      (fun _ ↦ Spec (.of (Polynomial R))) (chart R) (by
        intro x
        have hx : x ∈ (⨆ i, (chart R i).opensRange) := by
          rw [iSup_chart_opensRange]
          trivial
        obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
        exact ⟨i, hi⟩)
  let : IsZariskiLocalAtSource (@Flat : MorphismProperty Scheme.{u}) := by
    set_option backward.isDefEq.respectTransparency false in infer_instance
  apply (IsZariskiLocalAtSource.iff_of_openCover (P := @Flat) 𝒰).mpr
  change ∀ i : ULift.{u} (Fin 2),
    Flat (chart R i ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))
  intro i
  rw [chart_toSpec, Flat.SpecMap_iff]
  change RingHom.Flat (algebraMap R (Polynomial R))
  rw [RingHom.flat_algebraMap_iff]
  infer_instance

end AlgebraicGeometry.RelativeProjectiveLine
