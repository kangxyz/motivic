/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Pencils.GlobalBoundaryPencil
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Sections.DualFunctional

/-! # Finite flat divisors of actual sections with invertible boundary value -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- A supplied section, rather than a separately supplied equation, produces its
finite flat Cartier zero divisor on the retained smooth open. -/
theorem sectionDualFunctional_finite_mono_flat_on_open {X B U S : Scheme.{u}}
    (i : B ⟶ X) (q : X ⟶ S) [IsProper q] [IsAffine S]
    (j : U ⟶ X) [IsOpenImmersion j] [U.IsQuasiAffine]
    [SmoothOfRelativeDimension 1 (j ≫ q)] (L : LineBundle X)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ L.val)
    [IsIso (pullbackSectionMap i s)]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range i) :
    IsFinite (Hom.zeroInclusion (Hom.pullbackToUnit (sectionDualFunctional X L s) j) ≫ j ≫ q) ∧
      Mono (Hom.pullbackToUnit (sectionDualFunctional X L s) j) ∧
      Flat (Hom.zeroInclusion (Hom.pullbackToUnit (sectionDualFunctional X L s) j) ≫ j ≫ q) := by
  let a := sectionDualFunctional X L s
  have := sectionDualFunctional_pullback_isIso i L s
  have : IsIso ((Scheme.Modules.pullback i).map a) := by
    have ha : (Scheme.Modules.pullback i).map a =
        Hom.pullbackToUnit a i ≫ (pullbackUnitIso i).inv := by
      simp [Hom.pullbackToUnit]
    rw [ha]
    infer_instance
  have hp := GlobalBoundaryPencil.pencil_finite_flat_on_open
    i q j (dualLineBundle X L) a a 0 rfl hcover
  rw [GlobalBoundaryPencil.pencil_zero] at hp
  exact hp

/-- The full scheme-theoretic zero support is contained in the retained open. -/
theorem sectionDualFunctional_zero_range {X B U : Scheme.{u}} (i : B ⟶ X) (j : U ⟶ X)
    (L : LineBundle X) (s : SheafOfModules.unit X.ringCatSheaf ⟶ L.val)
    [IsIso (pullbackSectionMap i s)]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range i) :
    Set.range (Hom.zeroInclusion (sectionDualFunctional X L s)) ⊆ Set.range j := by
  let := sectionDualFunctional_boundary_isEmpty i L s
  rintro x ⟨z, rfl⟩
  rcases hcover (Hom.zeroInclusion (sectionDualFunctional X L s) z) with hx | hx
  · exact hx
  · have hz : z ∈ Set.range
        (Limits.pullback.snd i (Hom.zeroInclusion (sectionDualFunctional X L s))) := by
      rw [Scheme.Pullback.range_snd]
      exact hx
    obtain ⟨w, _⟩ := hz
    exact isEmptyElim w

/-- The full original zero scheme, not just a chosen supported subscheme, is finite flat. -/
theorem sectionDualFunctional_whole_zero_finite_flat {X B U S : Scheme.{u}}
    (i : B ⟶ X) (q : X ⟶ S) [IsProper q] [IsAffine S]
    (j : U ⟶ X) [IsOpenImmersion j] [U.IsQuasiAffine]
    [SmoothOfRelativeDimension 1 (j ≫ q)] (L : LineBundle X)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ L.val)
    [IsIso (pullbackSectionMap i s)]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range i) :
    IsFinite (Hom.zeroInclusion (sectionDualFunctional X L s) ≫ q) ∧
      Flat (Hom.zeroInclusion (sectionDualFunctional X L s) ≫ q) := by
  let a := sectionDualFunctional X L s
  let := lineBundle_isLocallyFree X (dualLineBundle X L)
  have hr := sectionDualFunctional_zero_range i j L s hcover
  have : Surjective (Limits.pullback.snd j (Hom.zeroInclusion a)) := by
    constructor
    intro x
    change x ∈ Set.range (Limits.pullback.snd j (Hom.zeroInclusion a))
    rw [Scheme.Pullback.range_snd]
    exact hr ⟨x, rfl⟩
  have : IsIso (Limits.pullback.snd j (Hom.zeroInclusion a)) :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩
  let e := Hom.zeroSchemePullbackIso a j ≪≫ asIso (Limits.pullback.snd j (Hom.zeroInclusion a))
  have he : e.hom ≫ (Hom.zeroInclusion a ≫ q) =
      Hom.zeroInclusion (Hom.pullbackToUnit a j) ≫ j ≫ q := by
    simp only [e, Iso.trans_hom, asIso_hom, Category.assoc]
    rw [← Limits.pullback.condition_assoc, Hom.zeroSchemePullbackIso_hom_fst_assoc]
  obtain ⟨hf, _, hflat⟩ := sectionDualFunctional_finite_mono_flat_on_open i q j L s hcover
  constructor
  · rw [← MorphismProperty.cancel_left_of_respectsIso @IsFinite e.hom, he]
    exact hf
  · rw [← MorphismProperty.cancel_left_of_respectsIso @Flat e.hom, he]
    exact hflat

end AlgebraicGeometry.Scheme.Modules.Invertible
