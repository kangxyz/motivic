/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.AffineCylinderIso

/-! # Base compatibility of the original cylinder presentation -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Polynomial

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable (k D : Type u) [CommRing k] [CommRing D] {Z : Scheme.{u}}

/-- The polynomial presentation retains the projection to the original scheme. -/
@[reassoc] theorem affineCylinderIso_hom_projection
    (f : k →+* D) (e : Z ≅ Spec (.of D))
    (z : Z ⟶ Spec (.of k)) (hz : z = e.hom ≫ Spec.map (CommRingCat.ofHom f)) :
    (affineCylinderIso k D f e z hz).hom ≫
        Spec.map (CommRingCat.ofHom (Polynomial.C : D →+* D[X])) =
      pullback.snd _ _ ≫ e.hom := by
  rw [← coordinateProductIso_hom_snd k f]
  simp only [affineCylinderIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc, asIso_hom, pullback.map, pullback.lift_snd]

/-- The polynomial presentation is over the original base. -/
@[reassoc] theorem affineCylinderIso_hom_base
    (f : k →+* D) (e : Z ≅ Spec (.of D))
    (z : Z ⟶ Spec (.of k)) (hz : z = e.hom ≫ Spec.map (CommRingCat.ofHom f)) :
    (affineCylinderIso k D f e z hz).hom ≫
        Spec.map (CommRingCat.ofHom ((Polynomial.C : D →+* D[X]).comp f)) =
      pullback.snd _ _ ≫ z := by
  change (affineCylinderIso k D f e z hz).hom ≫
      Spec.map (CommRingCat.ofHom f ≫ CommRingCat.ofHom (Polynomial.C : D →+* D[X])) = _
  rw [Spec.map_comp, affineCylinderIso_hom_projection_assoc, hz]

end AlgebraicGeometry.Scheme.Hom
