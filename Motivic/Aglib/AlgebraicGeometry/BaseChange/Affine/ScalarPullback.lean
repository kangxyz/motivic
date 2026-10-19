/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Relative affine scalar pullbacks and original scalar extension

The comparison is constructed from the tensor-product affine pullback and
pullback pasting. It applies to an arbitrary scheme over the original Spec A;
no scalar comparison isomorphism is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]
variable {Y : Scheme.{u}} (p : Y ⟶ Spec (.of A))

/-- Native scalar extension of a scheme over Spec A is its relative scalar pullback. -/
def affineScalarPullbackIso :
    pullback (p ≫ Spec.algebraMap R A) (Spec.algebraMap R B) ≅
      pullback p (Spec.algebraMap A (A ⊗[R] B)) :=
  (pullbackRightPullbackFstIso (Spec.algebraMap R A) (Spec.algebraMap R B) p).symm ≪≫
    asIso (pullback.map p (pullback.fst (Spec.algebraMap R A) (Spec.algebraMap R B))
      p (Spec.algebraMap A (A ⊗[R] B)) (𝟙 Y) (pullbackSpecIso R A B).hom (𝟙 _)
      (by simp) (by simp))

set_option backward.isDefEq.respectTransparency false in
/-- The comparison retains the original source scheme projection literally. -/
@[reassoc (attr := simp)]
theorem affineScalarPullbackIso_hom_fst :
    (affineScalarPullbackIso R A B p).hom ≫
        pullback.fst p (Spec.algebraMap A (A ⊗[R] B)) =
      pullback.fst (p ≫ Spec.algebraMap R A) (Spec.algebraMap R B) := by
  simp [affineScalarPullbackIso, pullback.map, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The other projection is the actual tensor-product affine comparison, not a chosen map. -/
@[reassoc]
theorem affineScalarPullbackIso_hom_snd :
    (affineScalarPullbackIso R A B p).hom ≫
        pullback.snd p (Spec.algebraMap A (A ⊗[R] B)) =
      (pullbackRightPullbackFstIso (Spec.algebraMap R A) (Spec.algebraMap R B) p).inv ≫
        pullback.snd p (pullback.fst (Spec.algebraMap R A) (Spec.algebraMap R B)) ≫
          (pullbackSpecIso R A B).hom := by
  simp [affineScalarPullbackIso, pullback.map, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The scalar-base component is precisely the original scalar projection. -/
@[reassoc (attr := simp)]
theorem affineScalarPullbackIso_hom_scalar :
    (affineScalarPullbackIso R A B p).hom ≫
        pullback.snd p (Spec.algebraMap A (A ⊗[R] B)) ≫
          Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B) : B →+* A ⊗[R] B)) =
      pullback.snd (p ≫ Spec.algebraMap R A) (Spec.algebraMap R B) := by
  rw [← Category.assoc, affineScalarPullbackIso_hom_snd]
  simp only [Category.assoc]
  rw [show (pullbackSpecIso R A B).hom ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B) : B →+* A ⊗[R] B)) =
      pullback.snd (Spec.algebraMap R A) (Spec.algebraMap R B) from
    pullbackSpecIso_hom_snd R A B]
  exact pullbackRightPullbackFstIso_inv_snd_snd _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The constructed comparison respects every original morphism over Spec A. -/
theorem affineScalarPullbackIso_naturality {Z : Scheme.{u}}
    (q : Z ⟶ Spec (.of A)) (f : Y ⟶ Z) (hf : p = f ≫ q) :
    pullback.map (p ≫ Spec.algebraMap R A) (Spec.algebraMap R B)
        (q ≫ Spec.algebraMap R A) (Spec.algebraMap R B) f (𝟙 _) (𝟙 _)
        (by simp [hf]) (by simp) ≫ (affineScalarPullbackIso R A B q).hom =
      (affineScalarPullbackIso R A B p).hom ≫
        pullback.map p (Spec.algebraMap A (A ⊗[R] B))
          q (Spec.algebraMap A (A ⊗[R] B)) f (𝟙 _) (𝟙 _)
          (by simpa using hf) (by simp) := by
  apply pullback.hom_ext
  · simp [pullback.map, Category.assoc]
  · apply (cancel_mono (pullbackSpecIso R A B).inv).mp
    simp only [Category.assoc]
    rw [affineScalarPullbackIso_hom_snd_assoc]
    simp only [Iso.hom_inv_id, Category.comp_id]
    apply pullback.hom_ext
    · simp only [pullback.map, Category.assoc, pullback.lift_fst_assoc,
        pullback.lift_snd_assoc, Category.id_comp, pullbackSpecIso_inv_fst,
        pullbackRightPullbackFstIso_inv_snd_fst]
      change _ = (affineScalarPullbackIso R A B p).hom ≫
        pullback.snd p (Spec.algebraMap A (A ⊗[R] B)) ≫
          Spec.algebraMap A (A ⊗[R] B)
      rw [← pullback.condition, affineScalarPullbackIso_hom_fst_assoc, hf, Category.assoc]
    · simp only [pullback.map, Category.assoc, pullback.lift_snd_assoc,
        pullbackSpecIso_inv_snd, pullbackRightPullbackFstIso_inv_snd_snd,
        pullback.lift_snd, Category.comp_id]
      exact (affineScalarPullbackIso_hom_scalar R A B p).symm

end AlgebraicGeometry
