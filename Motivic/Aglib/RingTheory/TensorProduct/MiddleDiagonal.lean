/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Affine coordinate rings of the middle diagonal

For three commutative algebras over an arbitrary commutative ring, the four-factor
ambient ring maps onto the tensor product identifying the two middle actions.
The latter is explicitly isomorphic to the ordinary triple tensor product.
These are affine coordinate rings, not tensor products of local stalks.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u

namespace Algebra.TensorProduct.MiddleDiagonal

variable (k A B C : Type u) [CommRing k] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]

/-- The right middle factor acts on the left adjacent coordinate ring. -/
scoped instance middleAlgebra : Algebra B (A ⊗[k] B) :=
  Algebra.TensorProduct.rightAlgebra

/-- The two base actions on the left adjacent coordinate ring agree. -/
scoped instance middleTower : IsScalarTower k B (A ⊗[k] B) :=
  Algebra.TensorProduct.right_isScalarTower

/-- The literal four-factor coordinate ring. -/
abbrev ambientRing := (A ⊗[k] B) ⊗[k] (B ⊗[k] C)

/-- The literal ring obtained by identifying the two middle actions. -/
abbrev tripleRing := (A ⊗[k] B) ⊗[B] (B ⊗[k] C)

/-- The first adjacent coordinate inclusion into the triple ring. -/
def leftMap : (A ⊗[k] B) →ₐ[k] tripleRing k A B C :=
  Algebra.TensorProduct.includeLeft

/-- The second adjacent coordinate inclusion into the triple ring. -/
def rightMap : (B ⊗[k] C) →ₐ[k] tripleRing k A B C :=
  Algebra.TensorProduct.includeRight.restrictScalars k

/-- The actual affine ring map identifying the two middle factors. -/
def quotientMap : ambientRing k A B C →ₐ[k] tripleRing k A B C :=
  Algebra.TensorProduct.lift (leftMap k A B C) (rightMap k A B C)
    (fun _ _ ↦ Commute.all _ _)

/-- The ambient quotient sends a pure tensor to the same tensor balanced over the middle ring. -/
@[simp] theorem quotientMap_tmul (x : A ⊗[k] B) (y : B ⊗[k] C) :
    quotientMap k A B C (x ⊗ₜ[k] y) = x ⊗ₜ[B] y := by
  simp [quotientMap, leftMap, rightMap, Algebra.TensorProduct.tmul_mul_tmul]

/-- The left scalar map is exactly the restriction of the ambient quotient. -/
@[simp] theorem quotientMap_comp_left :
    (quotientMap k A B C).comp Algebra.TensorProduct.includeLeft = leftMap k A B C := by
  apply AlgHom.ext
  intro x
  simp [leftMap]

/-- The right scalar map is exactly the restriction of the ambient quotient. -/
@[simp] theorem quotientMap_comp_right :
    (quotientMap k A B C).comp Algebra.TensorProduct.includeRight = rightMap k A B C := by
  apply AlgHom.ext
  intro y
  simp [rightMap]

/-- The two actual maps from the middle coordinate ring agree after the quotient. -/
theorem middle_actions_equal (b : B) :
    leftMap k A B C (1 ⊗ₜ[k] b) = rightMap k A B C (b ⊗ₜ[k] 1) := by
  change (algebraMap B (A ⊗[k] B) b) ⊗ₜ[B] (1 : B ⊗[k] C) =
    (1 : A ⊗[k] B) ⊗ₜ[B] (algebraMap B (B ⊗[k] C) b)
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
    TensorProduct.smul_tmul]

/-- The actual coordinate map selecting both middle factors of the ambient ring. -/
def middlePairMap : B ⊗[k] B →ₐ[k] ambientRing k A B C :=
  Algebra.TensorProduct.map Algebra.TensorProduct.includeRight Algebra.TensorProduct.includeLeft

/-- The middle coordinate in the balanced triple ring. -/
def middleMap : B →ₐ[k] tripleRing k A B C :=
  (leftMap k A B C).comp Algebra.TensorProduct.includeRight

/-- The affine middle-diagonal square commutes as an equality of actual algebra maps. -/
theorem quotientMap_comp_middlePairMap :
    (quotientMap k A B C).comp (middlePairMap k A B C) =
      (middleMap k A B C).comp (Algebra.TensorProduct.lmul' k) := by
  apply Algebra.TensorProduct.ext
  · apply AlgHom.ext
    intro b
    simp [middlePairMap, middleMap, leftMap, Algebra.TensorProduct.one_def]
  · apply AlgHom.ext
    intro b
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
      Algebra.TensorProduct.includeRight_apply, middlePairMap, Algebra.TensorProduct.map_tmul,
      Algebra.TensorProduct.includeLeft_apply, map_one, quotientMap_tmul,
      Algebra.TensorProduct.lmul'_apply_tmul, one_mul, middleMap]
    exact (middle_actions_equal k A B C b).symm

/-- The ambient map is a genuine surjection; neither support-flatness nor integrality is used. -/
theorem quotientMap_surjective : Function.Surjective (quotientMap k A B C) := by
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul x y => exact ⟨x ⊗ₜ[k] y, quotientMap_tmul k A B C x y⟩
  | add z w hz hw =>
    obtain ⟨x, rfl⟩ := hz
    obtain ⟨y, rfl⟩ := hw
    exact ⟨x + y, map_add _ _ _⟩

/-- Cancellation of the repeated middle factor gives the ordinary triple tensor ring. -/
def tripleEquiv : tripleRing k A B C ≃ₐ[k] (A ⊗[k] B) ⊗[k] C :=
  (Algebra.TensorProduct.cancelBaseChange k B B (A ⊗[k] B) C).restrictScalars k

/-- The cancellation formula multiplies precisely the two middle coordinates. -/
@[simp] theorem tripleEquiv_tmul (a : A) (b b' : B) (c : C) :
    tripleEquiv k A B C ((a ⊗ₜ[k] b) ⊗ₜ[B] (b' ⊗ₜ[k] c)) =
      (a ⊗ₜ[k] (b * b')) ⊗ₜ[k] c := by
  simp [tripleEquiv, Algebra.smul_def, Algebra.TensorProduct.right_algebraMap_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_comm]

/-- In ordinary triple coordinates, the ambient map multiplies the middle coordinates. -/
theorem tripleEquiv_quotientMap_tmul (a : A) (b b' : B) (c : C) :
    tripleEquiv k A B C (quotientMap k A B C ((a ⊗ₜ[k] b) ⊗ₜ[k] (b' ⊗ₜ[k] c))) =
      (a ⊗ₜ[k] (b * b')) ⊗ₜ[k] c := by
  rw [quotientMap_tmul, tripleEquiv_tmul]

end Algebra.TensorProduct.MiddleDiagonal
