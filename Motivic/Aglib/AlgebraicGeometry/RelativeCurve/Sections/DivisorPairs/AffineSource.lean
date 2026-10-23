/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.ProjectiveMap.AffineSource
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.SectionDivisorBaseIso
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Sections.DivisorPairs.Normalized
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Sections.DivisorPairs.NormalizedScalar
/-! # Actual Serre divisors on unchanged affine-source products -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ProjectiveSpace Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.CoherentGraph
variable (R : Type u) [CommRing R] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))
  {Y C W U : Scheme.{u}} [IsAffine Y] [IsNoetherianRing Γ(Y, ⊤)]
  (b : Y ⟶ Spec (.of R)) (f : C ⟶ ProjectiveSpace R ι) [IsFinite f]
  [IsLocallyNoetherian (pullback b (f ≫ toSpec R ι))]
  (z : W ⟶ pullback b (f ≫ toSpec R ι)) [IsClosedImmersion z]
  (eQ : ∀ d : ℕ, (moduleTensorLeftFunctor W
    ((Modules.pullback z).obj ((Modules.pullback
      (ConstantCurve.affineSourceToProjectiveSpace R ι b f)).obj
        (twistingSheaf Γ(Y, ⊤) ι (d : ℤ))))).obj
    ((Modules.pullback z).obj
      (SheafOfModules.unit (pullback b (f ≫ toSpec R ι)).ringCatSheaf)) ≅
        SheafOfModules.unit W.ringCatSheaf)
  (j : U ⟶ pullback b (f ≫ toSpec R ι)) [IsOpenImmersion j] [U.IsQuasiAffine]
  [SmoothOfRelativeDimension 1 (j ≫ pullback.fst b (f ≫ toSpec R ι))]
  (hcover : ∀ x : (Limits.pullback b (f ≫ toSpec R ι) : Scheme.{u}),
    x ∈ Set.range j ∨ x ∈ Set.range z)

include n e eQ hcover in
/-- The native Serre map is finite by base change, and the finite-flat divisors remain
relative to the original source Y, not a silently substituted affine scheme. -/
theorem exists_affineSource_normalized_divisor_pair
    (M : LineBundle (pullback b (f ≫ toSpec R ι)))
    (E : (Modules.pullback z).obj M.val ≅ SheafOfModules.unit W.ringCatSheaf) :
    ∃ B : ℕ, ∀ d : ℕ, B ≤ d →
      let T := pullbackLineBundle (ConstantCurve.affineSourceToProjectiveSpace R ι b f)
        (twistingLineBundle Γ(Y, ⊤) ι (d : ℤ))
      ∃ s : SheafOfModules.unit (pullback b (f ≫ toSpec R ι)).ringCatSheaf ⟶
        (tensorLineBundle _ T M).val,
      ∃ t : SheafOfModules.unit (pullback b (f ≫ toSpec R ι)).ringCatSheaf ⟶ T.val,
        pullbackSectionMap z s ≫ pullbackTensorMap z T.val M.val =
          tensorUnitSection (pullbackSectionMap z t) E.inv ∧
        IsIso (pullbackSectionMap z s) ∧ IsIso (pullbackSectionMap z t) ∧
        SectionDivisorFiniteFlat (pullback.fst b (f ≫ toSpec R ι)) j
          (tensorLineBundle _ T M) s ∧
        SectionDivisorFiniteFlat (pullback.fst b (f ≫ toSpec R ι)) j T t := by
  let a := ConstantCurve.affineSourceToProjectiveSpace R ι b f
  have ha : a ≫ toSpec Γ(Y, ⊤) ι = pullback.fst b (f ≫ toSpec R ι) ≫ Y.isoSpec.hom :=
    ConstantCurve.affineSourceToProjectiveSpace_toSpec R ι b f
  have : SmoothOfRelativeDimension 1 (j ≫ a ≫ toSpec Γ(Y, ⊤) ι) := by
    rw [ha, ← Category.assoc]
    exact inferInstanceAs (SmoothOfRelativeDimension (1 + 0)
      ((j ≫ pullback.fst b (f ≫ toSpec R ι)) ≫ Y.isoSpec.hom))
  obtain ⟨B, hB⟩ :=
    exists_normalized_boundary_divisor_pair Γ(Y, ⊤) ι n e a z eQ j hcover M E
  refine ⟨B, fun d hd => ?_⟩
  obtain ⟨s, t, h, hs, ht, hfs, hft⟩ := hB d hd
  rw [ha] at hfs hft
  exact ⟨s, t, h, hs, ht, (sectionDivisorFiniteFlat_comp_iso_iff _ j Y.isoSpec _ s).mp hfs,
    (sectionDivisorFiniteFlat_comp_iso_iff _ j Y.isoSpec _ t).mp hft⟩

include n e eQ hcover in
/-- The unchanged punctured affine source receives the scalar-prescribed psi pair. -/
theorem exists_affineSource_scalar_divisor_pair
    (E : SheafOfModules.unit W.ringCatSheaf ≅ SheafOfModules.unit W.ringCatSheaf) :
    ∃ B : ℕ, ∀ d : ℕ, B ≤ d →
      let T := pullbackLineBundle (ConstantCurve.affineSourceToProjectiveSpace R ι b f)
        (twistingLineBundle Γ(Y, ⊤) ι (d : ℤ))
      ∃ s t : SheafOfModules.unit (pullback b (f ≫ toSpec R ι)).ringCatSheaf ⟶ T.val,
        pullbackSectionMap z s = E.hom ≫ pullbackSectionMap z t ∧
        IsIso (pullbackSectionMap z s) ∧ IsIso (pullbackSectionMap z t) ∧
        SectionDivisorFiniteFlat (pullback.fst b (f ≫ toSpec R ι)) j T s ∧
        SectionDivisorFiniteFlat (pullback.fst b (f ≫ toSpec R ι)) j T t := by
  let a := ConstantCurve.affineSourceToProjectiveSpace R ι b f
  have ha : a ≫ toSpec Γ(Y, ⊤) ι = pullback.fst b (f ≫ toSpec R ι) ≫ Y.isoSpec.hom :=
    ConstantCurve.affineSourceToProjectiveSpace_toSpec R ι b f
  have : SmoothOfRelativeDimension 1 (j ≫ a ≫ toSpec Γ(Y, ⊤) ι) := by
    rw [ha, ← Category.assoc]
    exact inferInstanceAs (SmoothOfRelativeDimension (1 + 0)
      ((j ≫ pullback.fst b (f ≫ toSpec R ι)) ≫ Y.isoSpec.hom))
  obtain ⟨B, hB⟩ := exists_normalized_scalar_divisor_pair Γ(Y, ⊤) ι n e a z eQ j hcover E
  refine ⟨B, fun d hd => ?_⟩
  obtain ⟨s, t, h, hs, ht, hfs, hft⟩ := hB d hd
  rw [ha] at hfs hft
  exact ⟨s, t, h, hs, ht, (sectionDivisorFiniteFlat_comp_iso_iff _ j Y.isoSpec _ s).mp hfs,
    (sectionDivisorFiniteFlat_comp_iso_iff _ j Y.isoSpec _ t).mp hft⟩
end AlgebraicGeometry.Scheme.CoherentGraph
