/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Affine quotient presentation of the original closed fiber -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The affine quotient by the actual restriction kernel presents the complete
scheme-theoretic closed fiber over an affine open. -/
theorem exists_quotient_isPullback_of_kernel
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.Opens) (hU : IsAffineOpen U) (I : Ideal Γ(X, U))
    (hI : RingHom.ker (i.app U).hom = I) :
    ∃ j : Spec (.of (Γ(X, U) ⧸ I)) ⟶ Z,
      IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) j hU.fromSpec i := by
  subst I
  let hZ := hU.preimage i
  have hcomm : Spec.map (i.app U) ≫ hU.fromSpec = hZ.fromSpec ≫ i := by
    simpa only [Scheme.Hom.app_eq_appLE] using
      IsAffineOpen.SpecMap_appLE_fromSpec i hU hZ le_rfl
  have hp : IsPullback (Spec.map (i.app U)) hZ.fromSpec hU.fromSpec i := by
    apply (isPullback_morphismRestrict i U).of_iso'
      hZ.isoSpec.symm hU.isoSpec.symm (Iso.refl Z) (Iso.refl X)
    · apply (cancel_mono U.ι).mp
      simpa only [Category.assoc, morphismRestrict_ι, IsAffineOpen.isoSpec_inv_ι,
        IsAffineOpen.isoSpec_inv_ι_assoc, Iso.symm_hom] using hcomm.symm
    · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id,
        IsAffineOpen.isoSpec_inv_ι]
    · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id,
        IsAffineOpen.isoSpec_inv_ι]
    · simp
  let e := (i.app U).hom.quotientKerEquivOfSurjective (i.app_surjective U hU)
  let eS := Scheme.Spec.mapIso e.symm.toCommRingCatIso.op
  refine ⟨eS.hom ≫ hZ.fromSpec, ?_⟩
  apply hp.of_iso' eS (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id]
    change Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ Spec.map (i.app U) = _
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact RingHom.quotientKerEquivOfSurjective_symm_comp (i.app_surjective U hU)
  · simp
  · simp
  · simp

end AlgebraicGeometry.Scheme.Hom
