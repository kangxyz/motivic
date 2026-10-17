/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.DerivedCategory.ConeHomologyWindow
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-! # The first nonzero homology detects maps from the original single source -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
universe w v u
namespace DerivedCategory
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

private theorem single_to_single_eq_zero_of_homology
    (P Q : C) (n : ℤ) (f : (singleFunctor C n).obj P ⟶ (singleFunctor C n).obj Q)
    (hf : (homologyFunctor C n).map f = 0) : f = 0 := by
  let φ := (singleFunctor C n).preimage f
  have hφ : (singleFunctor C n).map φ = f := Functor.map_preimage _ _
  have : (singleFunctor C n ⋙ homologyFunctor C n).Faithful :=
    Functor.Faithful.of_iso (singleFunctorCompHomologyFunctorIso C n).symm
  have hz : φ = 0 := (singleFunctor C n ⋙ homologyFunctor C n).map_injective (by
    simpa only [Functor.comp_map, hφ, Functor.map_zero] using hf)
  rw [← hφ, hz, Functor.map_zero]

/-- When the target starts in degree `n`, its first homology detects a map from
an object placed in degree `n`. Only detection, not a spectral sequence, is used. -/
theorem single_hom_eq_zero_of_first_homology
    (P : C) (n : ℤ) {X : DerivedCategory C} [X.IsGE n]
    (f : (singleFunctor C n).obj P ⟶ X)
    (hf : (homologyFunctor C n).map f = 0) : f = 0 := by
  let t := TStructure.t (C := C)
  let T := (t.triangleLEGT n).obj X
  have hT := t.triangleLEGT_distinguished n X
  have : T.obj₃.IsGE (n + 1) := by
    change t.IsGE ((t.truncGT n).obj X) (n + 1)
    infer_instance
  have hz : IsZero (((homologyFunctor C 0).shift (n - 1)).obj T.obj₃) := by
    simpa only [shift_homologyFunctor] using
      (isZero_of_isGE T.obj₃ (n + 1) (n - 1) (by omega))
  have hm : Mono (((homologyFunctor C 0).shift n).map T.mor₁) :=
    ((homologyFunctor C 0).homologySequence_mono_shift_map_mor₁_iff
      T hT (n - 1) n (by omega)).mpr (hz.eq_of_src _ 0)
  have hm' : Mono ((homologyFunctor C n).map ((t.truncLEι n).app X)) := by
    simpa only [shift_homologyFunctor, T, Triangulated.TStructure.triangleLEGT_obj_mor₁,
      Triangulated.TStructure.triangleLEGT_obj_obj₁,
      Triangulated.TStructure.triangleLEGT_obj_obj₂] using hm
  let g := t.liftTruncLE f n
  have hg : g ≫ (t.truncLEι n).app X = f := t.liftTruncLE_ι f n
  have hgH : (homologyFunctor C n).map g = 0 := by
    apply (cancel_mono ((homologyFunctor C n).map ((t.truncLEι n).app X))).mp
    rw [Limits.zero_comp, ← Functor.map_comp, hg, hf]
  obtain ⟨Q, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE
    ((t.truncLE n).obj X) n
  have he : g ≫ e.hom = 0 := single_to_single_eq_zero_of_homology P Q n _ (by
    rw [Functor.map_comp, hgH, Limits.zero_comp])
  have hg0 : g = 0 := (cancel_mono e.hom).mp (by simpa using he)
  rw [← hg, hg0, Limits.zero_comp]

/-- The concrete first-homology obstruction vanishes exactly when the original
triangle arrow has a preimage. -/
theorem single_lift_iff_first_homology_obstruction_zero
    (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang (DerivedCategory C))
    (P : C) (n : ℤ) [T.obj₃.IsGE n]
    (f : (singleFunctor C n).obj P ⟶ T.obj₂) :
    (∃ g : (singleFunctor C n).obj P ⟶ T.obj₁, g ≫ T.mor₁ = f) ↔
      (homologyFunctor C n).map (f ≫ T.mor₂) = 0 := by
  constructor
  · rintro ⟨g, rfl⟩
    rw [Category.assoc, comp_distTriang_mor_zero₁₂ T hT, Limits.comp_zero, Functor.map_zero]
  · intro hf
    obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ T hT f
      (single_hom_eq_zero_of_first_homology P n (f ≫ T.mor₂) hf)
    exact ⟨g, hg.symm⟩

end DerivedCategory
