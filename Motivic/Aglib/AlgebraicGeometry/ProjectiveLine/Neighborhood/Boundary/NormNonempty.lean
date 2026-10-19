/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.ZeroNeighborhoodBoundary
public import Mathlib.AlgebraicGeometry.PullbackCarrier
/-! # Nonemptiness of the actual projective norm boundary

The opposite-chart zero point lies over every base point and outside the
retained affine chart. Thus the actual infinity component remains nonempty
after base change by any nonempty parameter scheme.

Intended upstream module:
`Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Boundary.NormNonempty`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`Pencils.NativeCorrectionNormAction`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine

variable (R : Type u) [CommRing R]

/-- The full projective neighborhood boundary lies over every base point,
using the actual opposite-chart zero point rather than a covering condition. -/
theorem neighborhoodBoundary_toSpec_surjective
    (V : (Spec (.of (Polynomial R))).Opens) :
    Function.Surjective (neighborhoodBoundaryInclusion R V ≫
      ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) := by
  intro x
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
  obtain ⟨b, hb⟩ := hz
  have hs : (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) ≫
      chart R (⟨1⟩ : ULift.{u} (Fin 2))) ≫
      ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)) = 𝟙 _ := by
    rw [Category.assoc, chart_toSpec, ← Spec.map_comp]
    have hcoeff : CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R) ≫
        CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)) = 𝟙 _ := by
      ext a
      simp
    rw [hcoeff, Spec.map_id]
  refine ⟨b, ?_⟩
  rw [Scheme.Hom.comp_apply, hb]
  exact congrArg (fun m : Spec (.of R) ⟶ Spec (.of R) => m x) hs

/-- The unchanged two-component norm boundary is nonempty over every nonempty
parameter scheme because its first, actual infinity, component is nonempty. -/
theorem normFullBoundarySource_nonempty
    (V : (Spec (.of (Polynomial R))).Opens)
    {A Z : Scheme.{u}} [Nonempty A] (a : A ⟶ Spec (.of R))
    (z : Z ⟶ ProjectiveSpace R (ULift.{u} (Fin 2))) :
    Nonempty ((pullback a (neighborhoodBoundaryInclusion R V ≫
      ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) ⨿
      pullback a (z ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))) : Scheme.{u}) := by
  let x : A := Classical.choice inferInstance
  obtain ⟨b, hb⟩ := neighborhoodBoundary_toSpec_surjective R V (a x)
  obtain ⟨y, _, _⟩ := Scheme.Pullback.exists_preimage_pullback x b hb.symm
  exact ⟨(coprod.inl : pullback a (neighborhoodBoundaryInclusion R V ≫
    ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) ⟶
    pullback a (neighborhoodBoundaryInclusion R V ≫
      ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) ⨿
    pullback a (z ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))) y⟩

end AlgebraicGeometry.RelativeProjectiveLine
