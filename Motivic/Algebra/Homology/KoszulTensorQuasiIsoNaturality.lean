/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.KoszulTensorQuasiIsoCriterion

/-!
# Naturality of the two-column Koszul tensor coordinates

The actual tensor of a chain map acts on both columns by that chain map.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace Motivic.Koszul

variable {R : Type u} [CommRing R] (a : R)
variable {K L : ChainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ L)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem singleTensorιZero_naturality (n : ℕ) :
    singleTensorιZero a K n ≫ ((singleComplex R a) ◁ f).f n =
      f.f n ≫ singleTensorιZero a L n := by
  unfold singleTensorιZero
  erw [Category.assoc, HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f]
  erw [← Category.assoc, ← leftUnitor_inv_naturality]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem singleTensorιOne_naturality (n : ℕ) :
    singleTensorιOne a K n ≫ ((singleComplex R a) ◁ f).f (n + 1) =
      f.f n ≫ singleTensorιOne a L n := by
  unfold singleTensorιOne
  erw [Category.assoc, HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f]
  erw [← Category.assoc, ← leftUnitor_inv_naturality]

@[simp]
theorem singleTensor_map_ιZero_apply (n : ℕ) (x : K.X n) :
    ((singleComplex R a) ◁ f).f n (singleTensorιZero a K n x) =
      singleTensorιZero a L n (f.f n x) :=
  ConcreteCategory.congr_hom (singleTensorιZero_naturality a f n) x

@[simp]
theorem singleTensor_map_ιOne_apply (n : ℕ) (x : K.X n) :
    ((singleComplex R a) ◁ f).f (n + 1) (singleTensorιOne a K n x) =
      singleTensorιOne a L n (f.f n x) :=
  ConcreteCategory.congr_hom (singleTensorιOne_naturality a f n) x

@[simp]
theorem singleTensorπZero_map_apply (n : ℕ)
    (x : (HomologicalComplex.tensorObj (singleComplex R a) K).X n) :
    singleTensorπZero a L n (((singleComplex R a) ◁ f).f n x) =
      f.f n (singleTensorπZero a K n x) := by
  cases n with
  | zero =>
    rw [← singleTensor_decomposition_zero_apply a K x]
    simp
  | succ n =>
    rw [← singleTensor_decomposition_apply a K n x]
    simp

@[simp]
theorem singleTensorπOne_map_apply (n : ℕ)
    (x : (HomologicalComplex.tensorObj (singleComplex R a) K).X (n + 1)) :
    singleTensorπOne a L n (((singleComplex R a) ◁ f).f (n + 1) x) =
      f.f n (singleTensorπOne a K n x) := by
  rw [← singleTensor_decomposition_apply a K n x]
  simp

/-- Chain maps commute with differentials on module elements. -/
theorem chainMap_d_apply (i j : ℕ) (x : K.X i) :
    L.d i j (f.f i x) = f.f j (K.d i j x) :=
  ConcreteCategory.congr_hom (f.comm i j) x

/-- The differential squares to zero on module elements. -/
theorem chainComplex_d_d_apply (i j k : ℕ) (x : K.X i) :
    K.d j k (K.d i j x) = 0 :=
  ConcreteCategory.congr_hom (K.d_comp_d i j k) x

end Motivic.Koszul
