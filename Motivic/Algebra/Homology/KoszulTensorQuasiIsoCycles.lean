/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.KoszulTensorQuasiIsoNaturality

/-!
# Lifting homology classes through a one-element Koszul tensor

A quasi-isomorphism lifts a cycle of the actual one-element tensor modulo an
actual total-complex boundary. No regularity of the scalar is used.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace Motivic.Koszul

variable {R : Type u} [CommRing R] (a : R)
variable {K L : ChainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ L)

/-- The shifted component of a tensor cycle is a cycle of the coefficient complex. -/
theorem singleTensor_cycle_πOne (n : ℕ)
    (y : (HomologicalComplex.tensorObj (singleComplex R a) K).X (n + 1))
    (hy : (HomologicalComplex.tensorObj (singleComplex R a) K).d (n + 1) n y = 0) :
    K.d n (n - 1) (singleTensorπOne a K n y) = 0 := by
  cases n with
  | zero =>
    rw [K.shape 0 0 (by simp)]
    rfl
  | succ n =>
    have h := congrArg (singleTensorπOne a K n) hy
    simpa using h

/-- The old component of a tensor cycle satisfies the scalar-cone equation. -/
theorem singleTensor_cycle_πZero (n : ℕ)
    (y : (HomologicalComplex.tensorObj (singleComplex R a) K).X (n + 1))
    (hy : (HomologicalComplex.tensorObj (singleComplex R a) K).d (n + 1) n y = 0) :
    K.d (n + 1) n (singleTensorπZero a K (n + 1) y) +
      a • singleTensorπOne a K n y = 0 := by
  have h := congrArg (singleTensorπZero a K n) hy
  simpa using h

set_option backward.isDefEq.respectTransparency false in
/-- Positive-degree cycles lift modulo genuine tensor boundaries. -/
theorem singleTensor_lift_cycle_succ [QuasiIso f] (n : ℕ)
    (y : (HomologicalComplex.tensorObj (singleComplex R a) L).X (n + 1))
    (hy : (HomologicalComplex.tensorObj (singleComplex R a) L).d (n + 1) n y = 0) :
    ∃ (x : (HomologicalComplex.tensorObj (singleComplex R a) K).X (n + 1))
      (w : (HomologicalComplex.tensorObj (singleComplex R a) L).X (n + 2)),
      (HomologicalComplex.tensorObj (singleComplex R a) K).d (n + 1) n x = 0 ∧
      ((singleComplex R a) ◁ f).f (n + 1) x =
        y + (HomologicalComplex.tensorObj (singleComplex R a) L).d (n + 2) (n + 1) w := by
  let u := singleTensorπZero a L (n + 1) y
  let v := singleTensorπOne a L n y
  have hu : L.d (n + 1) n u + a • v = 0 := singleTensor_cycle_πZero a n y hy
  have hv : L.d n (n - 1) v = 0 := singleTensor_cycle_πOne a n y hy
  obtain ⟨v', b, hv', hb⟩ := quasiIso_lift_cycle f n v hv
  have hsv : K.d n (n - 1) (a • v') = 0 := by simp [hv']
  have hsb : L.d (n + 1) n (-u + a • b) = f.f n (a • v') := by
    simp only [map_add, map_neg, map_smul, hb, smul_add]
    have hu' : -(L.d (n + 1) n u) = a • v := neg_eq_iff_add_eq_zero.mpr hu
    rw [hu']
  obtain ⟨c, hc⟩ := quasiIso_reflect_boundary f n (a • v') hsv (-u + a • b) hsb
  let q := -(f.f (n + 1) c) - u + a • b
  have hq : L.d (n + 1) n q = 0 := by
    dsimp [q]
    simp only [map_add, map_sub, map_neg, map_smul, chainMap_d_apply, hc, hb, smul_add]
    have hu' : -(L.d (n + 1) n u) = a • v := neg_eq_iff_add_eq_zero.mpr hu
    rw [sub_eq_add_neg, hu']
    abel
  obtain ⟨z, w, hz, hw⟩ := quasiIso_lift_cycle f (n + 1) q (by simpa using hq)
  have hz' : K.d (n + 1) n z = 0 := by simpa using hz
  refine ⟨-singleTensorιZero a K (n + 1) c + singleTensorιOne a K n v' -
      singleTensorιZero a K (n + 1) z,
    -singleTensorιOne a L (n + 1) b - singleTensorιZero a L (n + 2) w, ?_, ?_⟩
  · cases n with
    | zero =>
      apply singleTensor_ext_zero a K
      simp [hc, hz']
    | succ n =>
      apply singleTensor_ext a K n
      · simp [hc, hz']
      · simpa using hv'
  · apply singleTensor_ext a L n
    · simp only [map_sub, map_add, map_neg, singleTensorπZero_map_apply,
        singleTensorπZero_ιZero_apply, singleTensorπZero_ιOne_apply,
        singleTensorπZero_d_apply, singleTensorπOne_ιOne_apply,
        singleTensorπOne_ιZero_apply, map_zero, add_zero, smul_zero]
      rw [hw]
      dsimp [q, u]
      abel
    · simp [hb, v]

set_option backward.isDefEq.respectTransparency false in
/-- All tensor cycles lift modulo boundaries, including degree zero. -/
theorem singleTensor_lift_cycle [QuasiIso f] (n : ℕ)
    (y : (HomologicalComplex.tensorObj (singleComplex R a) L).X n)
    (hy : (HomologicalComplex.tensorObj (singleComplex R a) L).d n (n - 1) y = 0) :
    ∃ (x : (HomologicalComplex.tensorObj (singleComplex R a) K).X n)
      (w : (HomologicalComplex.tensorObj (singleComplex R a) L).X (n + 1)),
      (HomologicalComplex.tensorObj (singleComplex R a) K).d n (n - 1) x = 0 ∧
      ((singleComplex R a) ◁ f).f n x =
        y + (HomologicalComplex.tensorObj (singleComplex R a) L).d (n + 1) n w := by
  cases n with
  | zero =>
    obtain ⟨x, w, _, hw⟩ := quasiIso_lift_cycle f 0 (singleTensorπZero a L 0 y) (by
      rw [L.shape 0 0 (by simp)]; rfl)
    refine ⟨singleTensorιZero a K 0 x, singleTensorιZero a L 1 w, ?_, ?_⟩
    · rw [(HomologicalComplex.tensorObj (singleComplex R a) K).shape 0 0 (by simp)]
      rfl
    · apply singleTensor_ext_zero a L
      simpa using hw
  | succ n => exact singleTensor_lift_cycle_succ a f n y (by simpa using hy)

end Motivic.Koszul
