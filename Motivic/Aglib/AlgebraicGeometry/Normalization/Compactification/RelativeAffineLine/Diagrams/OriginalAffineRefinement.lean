/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.Diagrams.AffineRefinement

/-! # Native coordinates with the original coefficient-map domains unchanged

Intended upstream module:
Module prefix: `Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.`
Module suffix: `Diagrams.OriginalAffineRefinement`.
Incoming project consumers: `Motivic.Transfers.Presheaf.Actions.Norm.RefinedNormalization`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RelativeProjectiveLine Scheme.Hom
universe u
namespace AlgebraicGeometry.Scheme
variable (R : Type u) [CommRing R] {T Y Z : Scheme.{u}}
  (e : T ≅ Spec (.of (Polynomial R))) (q : T ⟶ Spec (.of R))
  (hq : e.hom ≫ boundaryLineProjection R = q)
  (O : (Spec (.of R)).Opens) [IsAffine O.toScheme]

/-- Only the target-open presentation is changed; all original source domains remain literal. -/
def originalAffineRefinedTargetIso : (q ⁻¹ᵁ O).toScheme ≅
    Spec (.of (Polynomial Γ(O.toScheme, ⊤))) :=
  T.isoOfEq (by rw [hq]) ≪≫ affineRefinedTargetIso R e O

@[reassoc]
theorem originalAffineRefinedTargetIso_coordinate :
    (originalAffineRefinedTargetIso R e q hq O).hom ≫
      Spec.map (CommRingCat.ofHom
        (Polynomial.mapRingHom (ConstantCurve.affineSourceCoefficientMap R O.ι))) =
      (q ⁻¹ᵁ O).ι ≫ e.hom := by
  simp only [originalAffineRefinedTargetIso, Iso.trans_hom, Category.assoc,
    affineRefinedTargetIso_coordinate]
  rw [← Category.assoc, Scheme.isoOfEq_hom_ι]

@[reassoc]
theorem originalAffineRefinedTargetIso_projection :
    (originalAffineRefinedTargetIso R e q hq O).hom ≫
      boundaryLineProjection Γ(O.toScheme, ⊤) = (q ∣_ O) ≫ O.toScheme.isoSpec.hom := by
  apply (cancel_mono (O.toScheme.isoSpec.inv ≫ O.ι)).mp
  simp only [originalAffineRefinedTargetIso, Iso.trans_hom, Category.assoc,
    affineRefinedTargetIso_projection, Iso.hom_inv_id_assoc, morphismRestrict_ι]
  rw [← Category.assoc, Scheme.isoOfEq_hom_ι, hq]

variable (p : Y ⟶ T) (W : Y.Opens) (hW : W ≤ p ⁻¹ᵁ (q ⁻¹ᵁ O))

/-- Native map on the literal affine open produced from the original representative. -/
def originalAffineRefinedNativeMap :
    W.toScheme ⟶ Spec (.of (Polynomial Γ(O.toScheme, ⊤))) :=
  p.resLE (q ⁻¹ᵁ O) W hW ≫ (originalAffineRefinedTargetIso R e q hq O).hom

instance originalAffineRefinedNativeMap_etale [Etale p] :
    Etale (originalAffineRefinedNativeMap R e q hq O p W hW) := by
  unfold originalAffineRefinedNativeMap
  infer_instance

@[reassoc]
theorem originalAffineRefinedNativeMap_coordinate :
    originalAffineRefinedNativeMap R e q hq O p W hW ≫
      Spec.map (CommRingCat.ofHom
        (Polynomial.mapRingHom (ConstantCurve.affineSourceCoefficientMap R O.ι))) =
      W.ι ≫ p ≫ e.hom := by
  simp only [originalAffineRefinedNativeMap, Category.assoc,
    originalAffineRefinedTargetIso_coordinate]
  rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]

variable (z : Z ⟶ T)

/-- The native marked map has the original full marked restriction as its domain. -/
def originalAffineRefinedNativeMarked : ((z ≫ q) ⁻¹ᵁ O).toScheme ⟶
    Spec (.of (Polynomial Γ(O.toScheme, ⊤))) :=
  (z ∣_ (q ⁻¹ᵁ O)) ≫ (originalAffineRefinedTargetIso R e q hq O).hom

instance originalAffineRefinedNativeMarked_closed [IsClosedImmersion z] :
    IsClosedImmersion (originalAffineRefinedNativeMarked R e q hq O z) := by
  unfold originalAffineRefinedNativeMarked
  infer_instance

instance originalAffineRefinedNativeMarked_finite [IsFinite (z ≫ q)] :
    IsFinite (originalAffineRefinedNativeMarked R e q hq O z ≫
      boundaryLineProjection Γ(O.toScheme, ⊤)) := by
  have he : originalAffineRefinedNativeMarked R e q hq O z ≫
      boundaryLineProjection Γ(O.toScheme, ⊤) = ((z ≫ q) ∣_ O) ≫ O.toScheme.isoSpec.hom := by
    apply (cancel_mono (O.toScheme.isoSpec.inv ≫ O.ι)).mp
    simp only [originalAffineRefinedNativeMarked, Category.assoc,
      originalAffineRefinedTargetIso_projection, Iso.hom_inv_id_assoc,
      morphismRestrict_ι, morphismRestrict_ι_assoc]
    rfl
  rw [he]
  infer_instance

/-- The original marked lift t and its full square are unchanged. -/
theorem originalAffineRefinedNativeMarked_isPullback
    (t : ((z ≫ q) ⁻¹ᵁ O).toScheme ⟶ W.toScheme)
    (H : IsPullback t (𝟙 _) (p.resLE (q ⁻¹ᵁ O) W hW) (z ∣_ (q ⁻¹ᵁ O))) :
    IsPullback t (𝟙 _) (originalAffineRefinedNativeMap R e q hq O p W hW)
      (originalAffineRefinedNativeMarked R e q hq O z) :=
  H.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (originalAffineRefinedTargetIso R e q hq O)
    (by simp) (by simp) (by simp [originalAffineRefinedNativeMap])
    (by simp [originalAffineRefinedNativeMarked])

end AlgebraicGeometry.Scheme
