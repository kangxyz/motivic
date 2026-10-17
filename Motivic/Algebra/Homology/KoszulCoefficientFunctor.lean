/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.KoszulCoefficientComplex
public import Motivic.Algebra.Homology.KoszulTensorQuasiIsoNaturality
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Exact coefficient functor for arbitrary finite Koszul complexes

The coefficient functor is the actual iterated tensor construction. Its maps
act on both columns by the preceding chain map. The checked two-column
coordinates prove that it carries every short exact coefficient sequence to a
short exact sequence of complexes, with no scalar-regularity hypothesis.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace Motivic.Koszul

variable {R : Type u} [CommRing R]

/-- Tensoring on the left with the actual one-equation complex. -/
noncomputable def singleTensorFunctor (a : R) :
    ChainComplex (ModuleCat R) ℕ ⥤ ChainComplex (ModuleCat R) ℕ :=
  (tensoringLeft (ChainComplex (ModuleCat R) ℕ)).obj (singleComplex R a)

instance (a : R) : (singleTensorFunctor a).Additive where
  map_add {K L} f g := by
    apply HomologicalComplex.Hom.ext
    funext n
    change ((singleComplex R a) ◁ (f + g)).f n =
      ((singleComplex R a) ◁ f).f n + ((singleComplex R a) ◁ g).f n
    cases n with
    | zero =>
      apply singleTensor_hom_ext_zero a K
      simp only [Preadditive.comp_add, singleTensorιZero_naturality,
        HomologicalComplex.add_f_apply, Preadditive.add_comp]
    | succ n =>
      apply singleTensor_hom_ext a K n
      · simp only [Preadditive.comp_add, singleTensorιZero_naturality,
          HomologicalComplex.add_f_apply, Preadditive.add_comp]
      · simp only [Preadditive.comp_add, singleTensorιOne_naturality,
          HomologicalComplex.add_f_apply, Preadditive.add_comp]

/-- Coefficient morphisms are the actual recursively tensored chain maps. -/
noncomputable def coefficientMap {M N : ModuleCat R} (f : M ⟶ N) :
    (s : List R) → coefficientComplex M s ⟶ coefficientComplex N s
  | [] => (ChainComplex.single₀ (ModuleCat R)).map f
  | a :: s => (singleTensorFunctor a).map (coefficientMap f s)

set_option backward.isDefEq.respectTransparency false in
/-- The actual finite-list Koszul construction, functorial in its coefficient module. -/
noncomputable def coefficientFunctor (s : List R) :
    ModuleCat R ⥤ ChainComplex (ModuleCat R) ℕ where
  obj M := coefficientComplex M s
  map f := coefficientMap f s
  map_id M := by
    induction s with
    | nil => exact (ChainComplex.single₀ (ModuleCat R)).map_id M
    | cons a s ih =>
      change (singleTensorFunctor a).map (coefficientMap (𝟙 M) s) = _
      rw [ih]
      exact (singleTensorFunctor a).map_id _
  map_comp f g := by
    induction s with
    | nil => exact (ChainComplex.single₀ (ModuleCat R)).map_comp f g
    | cons a s ih =>
      change (singleTensorFunctor a).map (coefficientMap (f ≫ g) s) = _
      rw [ih]
      exact (singleTensorFunctor a).map_comp _ _

@[simp]
theorem coefficientFunctor_obj (s : List R) (M : ModuleCat R) :
    (coefficientFunctor s).obj M = coefficientComplex M s := rfl

instance (s : List R) : (coefficientFunctor s).Additive where
  map_add {M N} f g := by
    change coefficientMap (f + g) s = coefficientMap f s + coefficientMap g s
    induction s with
    | nil => exact (ChainComplex.single₀ (ModuleCat R)).map_add
    | cons a s ih =>
      change (singleTensorFunctor a).map (coefficientMap (f + g) s) = _
      rw [ih]
      exact (singleTensorFunctor a).map_add

/-- One-element tensoring preserves degreewise injectivity of the actual chain map. -/
theorem singleTensor_map_injective (a : R) {K L : ChainComplex (ModuleCat R) ℕ}
    (f : K ⟶ L) (hf : ∀ n, Function.Injective (f.f n)) (n : ℕ) :
    Function.Injective (((singleComplex R a) ◁ f).f n) := by
  intro x y hxy
  cases n with
  | zero =>
    apply singleTensor_ext_zero a K
    apply hf 0
    simpa only [singleTensorπZero_map_apply] using congrArg (singleTensorπZero a L 0) hxy
  | succ n =>
    apply singleTensor_ext a K n
    · apply hf (n + 1)
      simpa only [singleTensorπZero_map_apply] using
        congrArg (singleTensorπZero a L (n + 1)) hxy
    · apply hf n
      simpa only [singleTensorπOne_map_apply] using
        congrArg (singleTensorπOne a L n) hxy

/-- One-element tensoring preserves degreewise surjectivity of the actual chain map. -/
theorem singleTensor_map_surjective (a : R) {K L : ChainComplex (ModuleCat R) ℕ}
    (f : K ⟶ L) (hf : ∀ n, Function.Surjective (f.f n)) (n : ℕ) :
    Function.Surjective (((singleComplex R a) ◁ f).f n) := by
  intro x
  cases n with
  | zero =>
    obtain ⟨y, hy⟩ := hf 0 (singleTensorπZero a L 0 x)
    refine ⟨singleTensorιZero a K 0 y, ?_⟩
    rw [singleTensor_map_ιZero_apply, hy, singleTensor_decomposition_zero_apply]
  | succ n =>
    obtain ⟨y, hy⟩ := hf (n + 1) (singleTensorπZero a L (n + 1) x)
    obtain ⟨z, hz⟩ := hf n (singleTensorπOne a L n x)
    refine ⟨singleTensorιZero a K (n + 1) y + singleTensorιOne a K n z, ?_⟩
    simp only [map_add, singleTensor_map_ιZero_apply, singleTensor_map_ιOne_apply,
      hy, hz]
    exact singleTensor_decomposition_apply a L n x

/-- One-element tensoring preserves exactness by lifting the two kernel coordinates. -/
theorem singleTensor_map_exact (a : R) {K L N : ChainComplex (ModuleCat R) ℕ}
    (f : K ⟶ L) (g : L ⟶ N) (hex : ∀ n, Function.Exact (f.f n) (g.f n)) (n : ℕ) :
    Function.Exact (((singleComplex R a) ◁ f).f n) (((singleComplex R a) ◁ g).f n) := by
  intro x
  constructor
  · intro hx
    cases n with
    | zero =>
      have hz : g.f 0 (singleTensorπZero a L 0 x) = 0 := by
        simpa only [singleTensorπZero_map_apply, map_zero] using
          congrArg (singleTensorπZero a N 0) hx
      obtain ⟨y, hy⟩ := (hex 0 _).mp hz
      refine ⟨singleTensorιZero a K 0 y, ?_⟩
      rw [singleTensor_map_ιZero_apply, hy, singleTensor_decomposition_zero_apply]
    | succ n =>
      have hz : g.f (n + 1) (singleTensorπZero a L (n + 1) x) = 0 := by
        simpa only [singleTensorπZero_map_apply, map_zero] using
          congrArg (singleTensorπZero a N (n + 1)) hx
      have ho : g.f n (singleTensorπOne a L n x) = 0 := by
        simpa only [singleTensorπOne_map_apply, map_zero] using
          congrArg (singleTensorπOne a N n) hx
      obtain ⟨y, hy⟩ := (hex (n + 1) _).mp hz
      obtain ⟨z, hz⟩ := (hex n _).mp ho
      refine ⟨singleTensorιZero a K (n + 1) y + singleTensorιOne a K n z, ?_⟩
      simp only [map_add, singleTensor_map_ιZero_apply, singleTensor_map_ιOne_apply,
        hy, hz]
      exact singleTensor_decomposition_apply a L n x
  · rintro ⟨y, rfl⟩
    cases n with
    | zero =>
      apply singleTensor_ext_zero a N
      simp only [singleTensorπZero_map_apply, map_zero, (hex 0).apply_apply_eq_zero]
    | succ n =>
      apply singleTensor_ext a N n
      · simp only [singleTensorπZero_map_apply, map_zero, (hex (n + 1)).apply_apply_eq_zero]
      · simp only [singleTensorπOne_map_apply, map_zero, (hex n).apply_apply_eq_zero]

/-- The actual one-element tensor functor preserves every short exact sequence of complexes. -/
theorem singleTensor_shortExact (a : R)
    (S : ShortComplex (ChainComplex (ModuleCat R) ℕ)) (hS : S.ShortExact) :
    (S.map (singleTensorFunctor a)).ShortExact := by
  have hd := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact {
    exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
      (singleTensor_map_exact a S.f S.g (fun n =>
        (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (hd n).exact) n)
    mono_f := (ModuleCat.mono_iff_injective _).mpr
      (singleTensor_map_injective a S.f
        (fun n => (ModuleCat.mono_iff_injective _).mp (hd n).mono_f) n)
    epi_g := (ModuleCat.epi_iff_surjective _).mpr
      (singleTensor_map_surjective a S.g
        (fun n => (ModuleCat.epi_iff_surjective _).mp (hd n).epi_g) n) }

/-- Arbitrary finite-list Koszul tensoring preserves a short exact coefficient sequence. -/
theorem coefficientFunctor_shortExact (s : List R)
    (S : ShortComplex (ModuleCat R)) (hS : S.ShortExact) :
    (S.map (coefficientFunctor s)).ShortExact := by
  induction s with
  | nil => exact hS.map_of_exact (ChainComplex.single₀ (ModuleCat R))
  | cons a s ih => exact singleTensor_shortExact a (S.map (coefficientFunctor s)) ih

end Motivic.Koszul
