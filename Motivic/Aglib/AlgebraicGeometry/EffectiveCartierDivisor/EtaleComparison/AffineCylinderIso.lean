/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.CoordinateGraphIdeal

/-! # The original cylinder and its affine polynomial presentation -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Polynomial

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable (k D : Type u) [CommRing k] [CommRing D]
variable {Z : Scheme.{u}}

/-- The literal affine-line cylinder over a scheme with its specified base map. -/
abbrev cylinder (z : Z ⟶ Spec (.of k)) :=
  pullback (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))) z

/-- The zero section of the literal cylinder. -/
def cylinderZeroSection (z : Z ⟶ Spec (.of k)) : Z ⟶ cylinder k z :=
  pullback.lift (z ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))))
    (𝟙 Z) (by
      simp only [Category.assoc, ← Spec.map_comp, Category.id_comp]
      have h : CommRingCat.ofHom (Polynomial.C : k →+* k[X]) ≫
          CommRingCat.ofHom (Polynomial.evalRingHom (0 : k)) = 𝟙 (CommRingCat.of k) := by
        ext r
        simp
      rw [h, Spec.map_id, Category.comp_id])

/-- Identify the cylinder over the original scheme with its polynomial spectrum. -/
def affineCylinderIso (f : k →+* D) (e : Z ≅ Spec (.of D))
    (z : Z ⟶ Spec (.of k)) (hz : z = e.hom ≫ Spec.map (CommRingCat.ofHom f)) :
    cylinder k z ≅ Spec (.of D[X]) :=
  asIso (pullback.map _ _ _ _ (𝟙 _) e.hom (𝟙 _)
    (by simp) (by simpa using hz)) ≪≫ (coordinateProductIso k f).symm

/-- The original zero section becomes evaluation at zero, not merely a map with
an equal topological image. -/
@[reassoc] theorem cylinderZeroSection_affineCylinderIso
    (f : k →+* D) (e : Z ≅ Spec (.of D))
    (z : Z ⟶ Spec (.of k)) (hz : z = e.hom ≫ Spec.map (CommRingCat.ofHom f)) :
    cylinderZeroSection k z ≫ (affineCylinderIso k D f e z hz).hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : D))) := by
  apply (cancel_mono (coordinateProductIso k f).hom).mp
  simp only [affineCylinderIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, asIso_hom]
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, cylinderZeroSection,
      coordinateProductIso_hom_fst, Category.comp_id]
    rw [hz]
    simp only [Category.assoc, ← Spec.map_comp]
    congr 2
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext
    · intro r
      simp
    · simp
  · simp only [pullback.map, Category.assoc, pullback.lift_snd,
      cylinderZeroSection, pullback.lift_snd_assoc, coordinateProductIso_hom_snd,
      Category.id_comp, ← Spec.map_comp]
    have h : CommRingCat.ofHom (Polynomial.C : D →+* D[X]) ≫
        CommRingCat.ofHom (Polynomial.evalRingHom (0 : D)) = 𝟙 (CommRingCat.of D) := by
      ext r
      simp
    rw [h, Spec.map_id, Category.comp_id]

end AlgebraicGeometry.Scheme.Hom
