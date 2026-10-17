/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.TorComparison.ExteriorHomotopy

/-!
# Totalizing two modules concentrated in degree zero

For any additive bifunctor, the actual nonnegative signed total complex of two
single complexes is canonically the single complex of the bifunctor's value.
The comparison is built from the actual degree-zero summand inclusion and the
coproduct universal property. It supplies the target identification needed by
the exterior-resolution augmentation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace Motivic.TorComparison

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  [HasZeroObject C₁] [HasZeroObject C₂]
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X₁, (F.obj X₁).Additive]
  (M : C₁) (N : C₂)
  [HasMapBifunctor ((ChainComplex.single₀ C₁).obj M)
    ((ChainComplex.single₀ C₂).obj N) F (ComplexShape.down ℕ)]

/-- The total of two degree-zero complexes has zero objects in positive degrees. -/
theorem exteriorSingle_isZero_succ (n : ℕ) :
    IsZero ((mapBifunctor ((ChainComplex.single₀ C₁).obj M)
      ((ChainComplex.single₀ C₂).obj N) F (ComplexShape.down ℕ)).X (n + 1)) := by
  rw [IsZero.iff_id_eq_zero]
  ext i j h
  have hsum : i + j = n + 1 := h
  by_cases hi : i = 0
  · have hj : j ≠ 0 := by omega
    exact ((F.obj (((ChainComplex.single₀ C₁).obj M).X i)).map_isZero
      (isZero_single_obj_X _ 0 N j hj)).eq_of_src _ _
  · have : F.flip.Additive := { }
    have (X₂ : C₂) : (F.flip.obj X₂).Additive := { }
    exact ((F.flip.obj (((ChainComplex.single₀ C₂).obj N).X j)).map_isZero
      (isZero_single_obj_X _ 0 M i hi)).eq_of_src _ _

/-- Projection of the unique degree-zero summand of the exterior total complex. -/
noncomputable def exteriorSingleProjection :
    (mapBifunctor ((ChainComplex.single₀ C₁).obj M)
      ((ChainComplex.single₀ C₂).obj N) F (ComplexShape.down ℕ)).X 0 ⟶
      (F.obj M).obj N :=
  mapBifunctorDesc fun i j h =>
    (F.map (singleObjXIsoOfEq (ComplexShape.down ℕ) 0 M i
      (Nat.add_eq_zero_iff.mp h).1).hom).app _ ≫
      (F.obj M).map (singleObjXIsoOfEq (ComplexShape.down ℕ) 0 N j
        (Nat.add_eq_zero_iff.mp h).2).hom

/-- The canonical inclusion of the unique degree-zero summand. -/
noncomputable def exteriorSingleInclusion :
    (F.obj M).obj N ⟶
      (mapBifunctor ((ChainComplex.single₀ C₁).obj M)
        ((ChainComplex.single₀ C₂).obj N) F (ComplexShape.down ℕ)).X 0 :=
  ιMapBifunctor ((ChainComplex.single₀ C₁).obj M)
    ((ChainComplex.single₀ C₂).obj N) F (ComplexShape.down ℕ) 0 0 0 rfl

/-- The degree-zero summand inclusion is inverse to the canonical projection. -/
@[reassoc (attr := simp)]
theorem exteriorSingle_inclusion_projection :
    exteriorSingleInclusion F M N ≫ exteriorSingleProjection F M N =
      𝟙 ((F.obj M).obj N) := by
  unfold exteriorSingleInclusion exteriorSingleProjection
  erw [ι_mapBifunctorDesc]
  change (F.map (𝟙 M)).app N ≫ (F.obj M).map (𝟙 N) = 𝟙 _
  simp

/-- The canonical projection is inverse to the degree-zero summand inclusion. -/
@[reassoc (attr := simp)]
theorem exteriorSingle_projection_inclusion :
    exteriorSingleProjection F M N ≫ exteriorSingleInclusion F M N = 𝟙 _ := by
  ext i j h
  have hsum : i + j = 0 := h
  obtain ⟨rfl, rfl⟩ := Nat.add_eq_zero_iff.mp hsum
  change exteriorSingleInclusion F M N ≫
    (exteriorSingleProjection F M N ≫ exteriorSingleInclusion F M N) =
      exteriorSingleInclusion F M N ≫ 𝟙 _
  simp

variable [HasZeroObject D]

/-- The total of two degree-zero complexes is the degree-zero complex of their
bifunctor value, with no choice of homology representative. -/
noncomputable def exteriorSingleIso :
    mapBifunctor ((ChainComplex.single₀ C₁).obj M)
      ((ChainComplex.single₀ C₂).obj N) F (ComplexShape.down ℕ) ≅
      (ChainComplex.single₀ D).obj ((F.obj M).obj N) where
  hom := (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨exteriorSingleProjection F M N, (exteriorSingle_isZero_succ F M N 0).eq_of_src _ _⟩
  inv := (ChainComplex.fromSingle₀Equiv _ _).symm (exteriorSingleInclusion F M N)
  hom_inv_id := by
    apply HomologicalComplex.hom_ext
    intro n
    cases n with
    | zero =>
        simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
          ChainComplex.toSingle₀Equiv_symm_apply_f_zero,
          ChainComplex.fromSingle₀Equiv_symm_apply_f_zero]
        exact exteriorSingle_projection_inclusion F M N
    | succ n => exact (exteriorSingle_isZero_succ F M N n).eq_of_src _ _
  inv_hom_id := by
    apply HomologicalComplex.hom_ext
    intro n
    cases n with
    | zero =>
        simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
          ChainComplex.toSingle₀Equiv_symm_apply_f_zero,
          ChainComplex.fromSingle₀Equiv_symm_apply_f_zero]
        exact exteriorSingle_inclusion_projection F M N
    | succ n => exact (isZero_single_obj_X _ 0 _ (n + 1) (by omega)).eq_of_src _ _

/-- The target identification uses the canonical degree-zero coproduct projection. -/
@[simp]
theorem exteriorSingleIso_hom_f_zero :
    (exteriorSingleIso F M N).hom.f 0 = exteriorSingleProjection F M N := by
  simp [exteriorSingleIso]

end Motivic.TorComparison
