/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.FiniteSchemeNormBaseChange
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Charts.Basic
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Flatness from the actual two free projective-line charts

For an affine morphism to the native relative projective line, freeness of the
two actual coordinate modules implies flatness of that same morphism. The scalar
actions come from the literal pullback projections. No coefficient localization,
normalization, module basis, or positive-rank hypothesis is chosen.

The two polynomial charts cover the relative projective line.

Intended upstream module: `Aglib.AlgebraicGeometry.ProjectiveLine.Charts.FlatOfFreeCharts`.
Current direct import consumers:
`Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.CoefficientFlat`.
The interfaces and exact hypotheses are given in the declarations below.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Polynomial

namespace AlgebraicGeometry.RelativeProjectiveLine

universe u

private def polynomialChartCover (R : Type u) [CommRing R] :
    (ProjectiveSpace R (ULift.{u} (Fin 2))).OpenCover :=
  Scheme.Cover.mkOfCovers (ULift.{u} (Fin 2))
    (fun _ ↦ Spec (.of R[X])) (chart R) (by
      intro x
      have hx : x ∈ (⨆ i, (chart R i).opensRange) := by
        rw [iSup_chart_opensRange]
        trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact ⟨i, hi⟩)

/-- Freeness of the two actual affine-chart coordinate modules makes the given
affine morphism flat. Empty or disconnected sources are allowed. -/
theorem flat_of_free_chart_sections
    (R : Type u) [CommRing R] {C : Scheme.{u}}
    (f : C ⟶ ProjectiveSpace R (ULift.{u} (Fin 2))) [IsAffineHom f]
    (hfree : ∀ i : ULift.{u} (Fin 2),
      let q := pullback.snd f (chart R i)
      let : Algebra R[X] Γ(pullback f (chart R i), ⊤) :=
        (FiniteSchemeNormBaseChange.scalarMap q).toAlgebra
      Module.Free R[X] Γ(pullback f (chart R i), ⊤)) :
    Flat f := by
  let : IsZariskiLocalAtTarget (@Flat : MorphismProperty Scheme.{u}) := by
    set_option backward.isDefEq.respectTransparency false in infer_instance
  apply (IsZariskiLocalAtTarget.iff_of_openCover (P := @Flat)
    (polynomialChartCover R)).mpr
  intro i
  change Flat (pullback.snd f (chart R i))
  let T := pullback f (chart R i)
  let q : T ⟶ Spec (.of R[X]) := pullback.snd f (chart R i)
  let : IsAffine T := inferInstance
  let : Algebra R[X] Γ(T, ⊤) := (FiniteSchemeNormBaseChange.scalarMap q).toAlgebra
  let : Module.Free R[X] Γ(T, ⊤) := hfree i
  have hSpec : Flat
      (Spec.map (CommRingCat.ofHom (FiniteSchemeNormBaseChange.scalarMap q))) := by
    rw [Flat.SpecMap_iff]
    change RingHom.Flat (algebraMap R[X] Γ(T, ⊤))
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  have hq : Spec.map (CommRingCat.ofHom (FiniteSchemeNormBaseChange.scalarMap q)) =
      T.isoSpec.inv ≫ q := by
    change Spec.map ((Scheme.ΓSpecIso (.of R[X])).inv ≫ q.appTop) = _
    rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv, Scheme.isoSpec_inv_naturality]
  rw [hq] at hSpec
  let : Flat (T.isoSpec.inv ≫ q) := hSpec
  simpa only [Iso.hom_inv_id_assoc] using
    (Flat.comp T.isoSpec.hom (T.isoSpec.inv ≫ q))

end AlgebraicGeometry.RelativeProjectiveLine
