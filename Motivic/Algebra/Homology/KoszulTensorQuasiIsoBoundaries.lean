/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.KoszulTensorQuasiIsoCycles

/-!
# Reflection of boundaries through a one-element Koszul tensor

The two-column cycle chase proves that tensoring an arbitrary quasi-isomorphism
with the actual one-element ring Koszul complex reflects boundaries.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace Motivic.Koszul

variable {R : Type u} [CommRing R] (a : R)
variable {K L : ChainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ L)

set_option backward.isDefEq.respectTransparency false in
/-- Positive-degree tensor cycles whose images are boundaries are boundaries. -/
theorem singleTensor_reflect_boundary_succ [QuasiIso f] (n : ℕ)
    (z : (HomologicalComplex.tensorObj (singleComplex R a) K).X (n + 1))
    (hz : (HomologicalComplex.tensorObj (singleComplex R a) K).d (n + 1) n z = 0)
    (y : (HomologicalComplex.tensorObj (singleComplex R a) L).X (n + 2))
    (hy : (HomologicalComplex.tensorObj (singleComplex R a) L).d (n + 2) (n + 1) y =
      ((singleComplex R a) ◁ f).f (n + 1) z) :
    ∃ w : (HomologicalComplex.tensorObj (singleComplex R a) K).X (n + 2),
      (HomologicalComplex.tensorObj (singleComplex R a) K).d (n + 2) (n + 1) w = z := by
  let u := singleTensorπZero a K (n + 1) z
  let v := singleTensorπOne a K n z
  let y₀ := singleTensorπZero a L (n + 2) y
  let y₁ := singleTensorπOne a L (n + 1) y
  have hu : K.d (n + 1) n u + a • v = 0 := singleTensor_cycle_πZero a n z hz
  have hv : K.d n (n - 1) v = 0 := singleTensor_cycle_πOne a n z hz
  have hy₀ : L.d (n + 2) (n + 1) y₀ + a • y₁ = f.f (n + 1) u := by
    have h := congrArg (singleTensorπZero a L (n + 1)) hy
    simpa [u, y₀, y₁] using h
  have hy₁ : -(L.d (n + 1) n y₁) = f.f n v := by
    have h := congrArg (singleTensorπOne a L n) hy
    simpa [v, y₁] using h
  obtain ⟨t, ht⟩ := quasiIso_reflect_boundary f n v hv (-y₁) (by simpa using hy₁)
  let q := y₁ + f.f (n + 1) t
  have hq : L.d (n + 1) n q = 0 := by
    dsimp [q]
    rw [map_add, chainMap_d_apply, ht, ← hy₁, add_neg_cancel]
  obtain ⟨q', b, hq', hb⟩ := quasiIso_lift_cycle f (n + 1) q (by simpa using hq)
  have hq'' : K.d (n + 1) n q' = 0 := by simpa using hq'
  let r := u + a • t - a • q'
  have hr : K.d (n + 1) n r = 0 := by
    dsimp [r]
    simpa [ht, hq''] using hu
  have hbr : L.d (n + 2) (n + 1) (y₀ - a • b) = f.f (n + 1) r := by
    dsimp [r]
    simp only [map_sub, map_add, map_smul, ← hy₀, hb, smul_add]
    dsimp [q]
    rw [smul_add]
    abel
  obtain ⟨c, hc⟩ := quasiIso_reflect_boundary f (n + 1) r (by simpa using hr)
    (y₀ - a • b) hbr
  refine ⟨singleTensorιZero a K (n + 2) c + singleTensorιOne a K (n + 1) (q' - t), ?_⟩
  apply singleTensor_ext a K n
  · simp only [singleTensorπZero_d_apply, map_add, singleTensorπZero_ιZero_apply,
      singleTensorπZero_ιOne_apply, singleTensorπOne_ιZero_apply,
      singleTensorπOne_ιOne_apply, map_zero, smul_zero, add_zero, zero_add, hc]
    dsimp [r, u]
    rw [smul_sub]
    abel
  · simp [hq'', ht, v]

set_option backward.isDefEq.respectTransparency false in
/-- Degree-zero tensor cycles whose images are boundaries are boundaries. -/
theorem singleTensor_reflect_boundary_zero [QuasiIso f]
    (z : (HomologicalComplex.tensorObj (singleComplex R a) K).X 0)
    (y : (HomologicalComplex.tensorObj (singleComplex R a) L).X 1)
    (hy : (HomologicalComplex.tensorObj (singleComplex R a) L).d 1 0 y =
      ((singleComplex R a) ◁ f).f 0 z) :
    ∃ w : (HomologicalComplex.tensorObj (singleComplex R a) K).X 1,
      (HomologicalComplex.tensorObj (singleComplex R a) K).d 1 0 w = z := by
  let u := singleTensorπZero a K 0 z
  let y₀ := singleTensorπZero a L 1 y
  let y₁ := singleTensorπOne a L 0 y
  have hy₀ : L.d 1 0 y₀ + a • y₁ = f.f 0 u := by
    have h := congrArg (singleTensorπZero a L 0) hy
    simpa [u, y₀, y₁] using h
  obtain ⟨q, b, _, hb⟩ := quasiIso_lift_cycle f 0 y₁ (by
    rw [L.shape 0 0 (by simp)]; rfl)
  have hbr : L.d 1 0 (y₀ - a • b) = f.f 0 (u - a • q) := by
    simp only [map_sub, map_smul, ← hy₀, hb, smul_add]
    abel
  obtain ⟨c, hc⟩ := quasiIso_reflect_boundary f 0 (u - a • q) (by
    rw [K.shape 0 0 (by simp)]; rfl) (y₀ - a • b) hbr
  refine ⟨singleTensorιZero a K 1 c + singleTensorιOne a K 0 q, ?_⟩
  apply singleTensor_ext_zero a K
  simp [hc, u]

set_option backward.isDefEq.respectTransparency false in
/-- Tensoring with the actual two-term ring Koszul complex preserves quasi-isomorphisms. -/
theorem singleTensor_quasiIso [QuasiIso f] : QuasiIso ((singleComplex R a) ◁ f) := by
  change QuasiIso (HomologicalComplex.tensorHom (𝟙 (singleComplex R a)) f)
  apply quasiIso_of_lift_cycle_of_reflect_boundary
  · exact singleTensor_lift_cycle a f
  · intro n x hx y hy
    cases n with
    | zero => exact singleTensor_reflect_boundary_zero a f x y hy
    | succ n => exact singleTensor_reflect_boundary_succ a f n x (by simpa using hx) y hy

end Motivic.Koszul
