/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.KoszulSingleTensorDifferential

/-!
# Cross-ring additive functors and one-element Koszul tensors

The two-column decomposition gives an explicit comparison between applying an
additive functor to a one-element tensor complex and tensoring the image
complex. When the functor preserves multiplication by the chosen scalar, the
comparison respects differentials and is a genuine chain isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace Motivic.Koszul

variable {R S : Type u} [CommRing R] [CommRing S]
variable (F : ModuleCat R ⥤ ModuleCat S) [F.Additive]
variable (a : R) (b : S) (K : ChainComplex (ModuleCat R) ℕ)

/-- The image complex under an additive module functor. -/
abbrev crossMappedComplex := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K

set_option backward.isDefEq.respectTransparency false in
/-- Mapped old-column and new-column inclusions jointly detect maps in positive degrees. -/
theorem crossMappedSingleTensor_hom_ext {A : ModuleCat S} (n : ℕ)
    {f g : F.obj ((HomologicalComplex.tensorObj (singleComplex R a) K).X (n + 1)) ⟶ A}
    (h₀ : F.map (singleTensorιZero a K (n + 1)) ≫ f =
      F.map (singleTensorιZero a K (n + 1)) ≫ g)
    (h₁ : F.map (singleTensorιOne a K n) ≫ f = F.map (singleTensorιOne a K n) ≫ g) :
    f = g := by
  have hd : F.map (singleTensorπZero a K (n + 1)) ≫
        F.map (singleTensorιZero a K (n + 1)) +
      F.map (singleTensorπOne a K n) ≫ F.map (singleTensorιOne a K n) = 𝟙 _ := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_add, singleTensor_decomposition]
    exact F.map_id _
  have h := congrArg (fun p => p ≫ f) hd
  have h' := congrArg (fun p => p ≫ g) hd
  simp only [Preadditive.add_comp, Category.assoc, Category.id_comp] at h h'
  rw [h₀, h₁] at h
  exact h.symm.trans h'

omit [F.Additive] in
set_option backward.isDefEq.respectTransparency false in
/-- The mapped old-column inclusion detects maps in degree zero. -/
theorem crossMappedSingleTensor_hom_ext_zero {A : ModuleCat S}
    {f g : F.obj ((HomologicalComplex.tensorObj (singleComplex R a) K).X 0) ⟶ A}
    (h : F.map (singleTensorιZero a K 0) ≫ f = F.map (singleTensorιZero a K 0) ≫ g) :
    f = g := by
  have hd : F.map (singleTensorπZero a K 0) ≫ F.map (singleTensorιZero a K 0) = 𝟙 _ := by
    rw [← Functor.map_comp, singleTensor_decomposition_zero]
    exact F.map_id _
  have h' := congrArg (fun p => F.map (singleTensorπZero a K 0) ≫ p) h
  simpa only [← Category.assoc, hd, Category.id_comp] using h'

/-- The explicit termwise comparison from the image of a one-element tensor. -/
noncomputable def singleTensorCrossMapToX : (n : ℕ) →
    F.obj ((HomologicalComplex.tensorObj (singleComplex R a) K).X n) ⟶
      (HomologicalComplex.tensorObj (singleComplex S b) (crossMappedComplex F K)).X n
  | 0 => F.map (singleTensorπZero a K 0) ≫ singleTensorιZero b (crossMappedComplex F K) 0
  | n + 1 =>
      F.map (singleTensorπZero a K (n + 1)) ≫
          singleTensorιZero b (crossMappedComplex F K) (n + 1) +
        F.map (singleTensorπOne a K n) ≫ singleTensorιOne b (crossMappedComplex F K) n

/-- The explicit inverse comparison on terms. -/
noncomputable def singleTensorCrossMapFromX : (n : ℕ) →
    (HomologicalComplex.tensorObj (singleComplex S b) (crossMappedComplex F K)).X n ⟶
      F.obj ((HomologicalComplex.tensorObj (singleComplex R a) K).X n)
  | 0 => singleTensorπZero b (crossMappedComplex F K) 0 ≫ F.map (singleTensorιZero a K 0)
  | n + 1 =>
      singleTensorπZero b (crossMappedComplex F K) (n + 1) ≫
          F.map (singleTensorιZero a K (n + 1)) +
        singleTensorπOne b (crossMappedComplex F K) n ≫ F.map (singleTensorιOne a K n)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem crossMappedιZero_singleTensorCrossMapToX (n : ℕ) :
    F.map (singleTensorιZero a K n) ≫ singleTensorCrossMapToX F a b K n =
      singleTensorιZero b (crossMappedComplex F K) n := by
  cases n <;> simp [singleTensorCrossMapToX, Preadditive.comp_add, ← Category.assoc,
    ← Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem crossMappedιOne_singleTensorCrossMapToX (n : ℕ) :
    F.map (singleTensorιOne a K n) ≫ singleTensorCrossMapToX F a b K (n + 1) =
      singleTensorιOne b (crossMappedComplex F K) n := by
  simp [singleTensorCrossMapToX, Preadditive.comp_add, ← Category.assoc, ← Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem ιZero_singleTensorCrossMapFromX (n : ℕ) :
    singleTensorιZero b (crossMappedComplex F K) n ≫ singleTensorCrossMapFromX F a b K n =
      F.map (singleTensorιZero a K n) := by
  cases n <;> simp [singleTensorCrossMapFromX, Preadditive.comp_add, ← Category.assoc]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem ιOne_singleTensorCrossMapFromX (n : ℕ) :
    singleTensorιOne b (crossMappedComplex F K) n ≫ singleTensorCrossMapFromX F a b K (n + 1) =
      F.map (singleTensorιOne a K n) := by
  simp [singleTensorCrossMapFromX, Preadditive.comp_add, ← Category.assoc]

/-- The comparison is an actual isomorphism in every degree. -/
noncomputable def singleTensorCrossMapXIso (n : ℕ) :
    F.obj ((HomologicalComplex.tensorObj (singleComplex R a) K).X n) ≅
      (HomologicalComplex.tensorObj (singleComplex S b) (crossMappedComplex F K)).X n where
  hom := singleTensorCrossMapToX F a b K n
  inv := singleTensorCrossMapFromX F a b K n
  hom_inv_id := by
    cases n with
    | zero =>
      apply crossMappedSingleTensor_hom_ext_zero F a K
      simp only [← Category.assoc, crossMappedιZero_singleTensorCrossMapToX,
        ιZero_singleTensorCrossMapFromX, Category.comp_id]
    | succ n =>
      apply crossMappedSingleTensor_hom_ext F a K n
      · simp only [← Category.assoc, crossMappedιZero_singleTensorCrossMapToX,
          ιZero_singleTensorCrossMapFromX, Category.comp_id]
      · simp only [← Category.assoc, crossMappedιOne_singleTensorCrossMapToX,
          ιOne_singleTensorCrossMapFromX, Category.comp_id]
  inv_hom_id := by
    cases n with
    | zero =>
      apply singleTensor_hom_ext_zero b (crossMappedComplex F K)
      simp only [← Category.assoc, ιZero_singleTensorCrossMapFromX,
        crossMappedιZero_singleTensorCrossMapToX, Category.comp_id]
    | succ n =>
      apply singleTensor_hom_ext b (crossMappedComplex F K) n
      · simp only [← Category.assoc, ιZero_singleTensorCrossMapFromX,
          crossMappedιZero_singleTensorCrossMapToX, Category.comp_id]
      · simp only [← Category.assoc, ιOne_singleTensorCrossMapFromX,
          crossMappedιOne_singleTensorCrossMapToX, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- Cross-ring scalar compatibility makes the explicit comparison commute with differentials. -/
theorem singleTensorCrossMapToX_comm
    (ha : ∀ X : ModuleCat R, F.map (ModuleCat.ofHom (LinearMap.lsmul R X a)) =
      ModuleCat.ofHom (LinearMap.lsmul S (F.obj X) b)) (n : ℕ) :
    singleTensorCrossMapToX F a b K (n + 1) ≫
        (HomologicalComplex.tensorObj (singleComplex S b) (crossMappedComplex F K)).d (n + 1) n =
      F.map ((HomologicalComplex.tensorObj (singleComplex R a) K).d (n + 1) n) ≫
        singleTensorCrossMapToX F a b K n := by
  apply crossMappedSingleTensor_hom_ext F a K n
  · rw [← Category.assoc, crossMappedιZero_singleTensorCrossMapToX, singleTensorιZero_d]
    rw [← Category.assoc, ← Functor.map_comp, singleTensorιZero_d,
      Functor.map_comp, Category.assoc, crossMappedιZero_singleTensorCrossMapToX]
    rfl
  · rw [← Category.assoc, crossMappedιOne_singleTensorCrossMapToX]
    cases n with
    | zero =>
      rw [singleTensorιOne_zero_d, ← Category.assoc, ← Functor.map_comp,
        singleTensorιOne_zero_d, Functor.map_comp, Category.assoc,
        crossMappedιZero_singleTensorCrossMapToX, ha]
      rfl
    | succ n =>
      rw [singleTensorιOne_d, ← Category.assoc, ← Functor.map_comp,
        singleTensorιOne_d, Functor.map_sub, Preadditive.sub_comp, Functor.map_comp,
        Functor.map_comp, Category.assoc, Category.assoc,
        crossMappedιZero_singleTensorCrossMapToX, crossMappedιOne_singleTensorCrossMapToX, ha]
      rfl

/-- An additive functor preserving the scalar gives a genuine one-element tensor comparison. -/
noncomputable def singleTensorCrossMapIso
    (ha : ∀ X : ModuleCat R, F.map (ModuleCat.ofHom (LinearMap.lsmul R X a)) =
      ModuleCat.ofHom (LinearMap.lsmul S (F.obj X) b)) :
    crossMappedComplex F (HomologicalComplex.tensorObj (singleComplex R a) K) ≅
      HomologicalComplex.tensorObj (singleComplex S b) (crossMappedComplex F K) :=
  HomologicalComplex.Hom.isoOfComponents (singleTensorCrossMapXIso F a b K) (by
    intro i j hij
    have hi : j + 1 = i := hij
    subst i
    exact singleTensorCrossMapToX_comm F a b K ha j)

end Motivic.Koszul
