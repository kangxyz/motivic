/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Target.MarkedBaseChange
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.PencilSites

/-! # The whole restricted source parameter in the same native target coordinates

Intended upstream module:
`Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Source.NativeParameter`.
Incoming project consumers:
Module prefix: `Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.`
Module suffix: `RelativeAffineLine.RestrictedMarkedSquare`,
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Data.NativeBoundarySectionData`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme Scheme.Hom
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R]
  (O : (Spec (.of R)).Opens) [IsAffine O.toScheme]

/-- Only the redundant intersection with the whole parameter is removed. -/
def sourceWholeParameterIso :
    (boundaryBaseSourceOpen (boundaryLineProjection R) ⊤ O).toScheme ≅
      ((boundaryLineProjection R) ⁻¹ᵁ O).toScheme :=
  (Spec (.of (Polynomial R))).isoOfEq (by
    simp only [boundaryBaseSourceOpen, top_inf_eq])

omit [IsAffine O.toScheme] in
@[reassoc (attr := simp)]
theorem sourceWholeParameterIso_hom_ι :
    (sourceWholeParameterIso R O).hom ≫ ((boundaryLineProjection R) ⁻¹ᵁ O).ι =
      (boundaryBaseSourceOpen (boundaryLineProjection R) ⊤ O).ι :=
  Scheme.isoOfEq_hom_ι _ _

/-- This is the same native affine line used for the target, with no new shrink. -/
def sourceNativeParameterIso :
    (boundaryBaseSourceOpen (boundaryLineProjection R) ⊤ O).toScheme ≅
      Spec (.of (Polynomial Γ(O.toScheme, ⊤))) :=
  sourceWholeParameterIso R O ≪≫ (targetAffineOpenIso R O).symm

instance sourceWholeParameter_affine :
    IsAffine (boundaryBaseSourceOpen (boundaryLineProjection R) ⊤ O).toScheme :=
  .of_isIso (sourceNativeParameterIso R O).hom

@[reassoc]
theorem sourceNativeParameterIso_hom_projection :
    (sourceNativeParameterIso R O).hom ≫ boundaryLineProjection Γ(O.toScheme, ⊤) =
      boundaryBaseSpecProjection (boundaryLineProjection R) ⊤ O := by
  rw [sourceNativeParameterIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    targetAffineOpenIso_inv_projection]
  have h : (sourceWholeParameterIso R O).hom ≫ (boundaryLineProjection R ∣_ O) =
      boundaryBaseSourceProjection (boundaryLineProjection R) ⊤ O := by
    apply (cancel_mono O.ι).mp
    simp only [Category.assoc, morphismRestrict_ι,
      sourceWholeParameterIso_hom_ι_assoc, boundaryBaseSourceProjection_ι]
  simpa only [Category.assoc, boundaryBaseSpecProjection] using
    congrArg (fun f => f ≫ O.toScheme.isoSpec.hom) h

/-- Forgetting the new coefficients recovers the literal original parameter inclusion. -/
@[reassoc]
theorem sourceNativeParameterIso_hom_coordinate :
    (sourceNativeParameterIso R O).hom ≫
      Spec.map (CommRingCat.ofHom
        (Polynomial.mapRingHom (Scheme.ConstantCurve.affineSourceCoefficientMap R O.ι))) =
      (boundaryBaseSourceOpen (boundaryLineProjection R) ⊤ O).ι := by
  simp only [sourceNativeParameterIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    targetAffineOpenIso_inv_coordinate, sourceWholeParameterIso_hom_ι]

variable {Z : Scheme.{u}} (z : Z ⟶ Spec (.of (Polynomial R)))

/-- The original marked lift becomes the literal native marked map, not a new choice. -/
@[reassoc]
theorem boundaryBaseLift_sourceNativeParameterIso :
    boundaryBaseLift (boundaryLineProjection R) z ⊤ O (fun _ _ => trivial) ≫
      (sourceNativeParameterIso R O).hom = targetNativeMarked R O z := by
  unfold sourceNativeParameterIso targetNativeMarked
  simp only [Iso.trans_hom, Iso.symm_hom, ← Category.assoc]
  congr 1
  apply (cancel_mono ((boundaryLineProjection R) ⁻¹ᵁ O).ι).mp
  simp only [Category.assoc, sourceWholeParameterIso_hom_ι,
    boundaryBaseLift_ι, morphismRestrict_ι]
  rfl

variable {Y : Scheme.{u}} (p : Y ⟶ Spec (.of (Polynomial R)))

/-- The original restricted cover, mapped to the same native parameter. -/
def sourceNativeCoverMap :
    (boundaryBaseCoverOpen (boundaryLineProjection R) p ⊤ O).toScheme ⟶
      Spec (.of (Polynomial Γ(O.toScheme, ⊤))) :=
  boundaryBaseCoverMap (boundaryLineProjection R) p ⊤ O ≫
    (sourceNativeParameterIso R O).hom

instance sourceNativeCoverMap_flat [Flat p] : Flat (sourceNativeCoverMap R O p) := by
  dsimp [sourceNativeCoverMap, boundaryBaseCoverMap]
  infer_instance

instance sourceNativeCoverMap_open [IsOpenImmersion p] :
    IsOpenImmersion (sourceNativeCoverMap R O p) := by
  dsimp [sourceNativeCoverMap, boundaryBaseCoverMap]
  infer_instance

@[reassoc]
theorem sourceNativeCoverMap_projection :
    sourceNativeCoverMap R O p ≫ boundaryLineProjection Γ(O.toScheme, ⊤) =
      boundaryBaseCoverMap (boundaryLineProjection R) p ⊤ O ≫
        boundaryBaseSpecProjection (boundaryLineProjection R) ⊤ O := by
  rw [sourceNativeCoverMap, Category.assoc, sourceNativeParameterIso_hom_projection]

/-- Reconstruct the original cover map, including the original retained-open inclusion. -/
@[reassoc]
theorem sourceNativeCoverMap_coordinate :
    sourceNativeCoverMap R O p ≫
      Spec.map (CommRingCat.ofHom
        (Polynomial.mapRingHom (Scheme.ConstantCurve.affineSourceCoefficientMap R O.ι))) =
      (boundaryBaseCoverOpen (boundaryLineProjection R) p ⊤ O).ι ≫ p := by
  rw [sourceNativeCoverMap, Category.assoc, sourceNativeParameterIso_hom_coordinate]
  exact morphismRestrict_ι _ _

variable (s : Z ⟶ Y) (hs : s ≫ p = z)

@[reassoc]
theorem sourceNativeCoverLift_map :
    boundaryBaseCoverLift (boundaryLineProjection R) p z s hs ⊤ O
        (fun _ _ => trivial) ≫ sourceNativeCoverMap R O p =
      targetNativeMarked R O z := by
  rw [sourceNativeCoverMap, ← Category.assoc, boundaryBaseCoverLift_map,
    boundaryBaseLift_sourceNativeParameterIso]

/-- The full original marked square stays Cartesian after the parameter iso. -/
theorem sourceNativeCoverLift_isPullback (H : IsPullback s (𝟙 Z) p z) :
    IsPullback
      (boundaryBaseCoverLift (boundaryLineProjection R) p z s hs ⊤ O
        (fun _ _ => trivial))
      (𝟙 _) (sourceNativeCoverMap R O p) (targetNativeMarked R O z) := by
  exact (boundaryBaseCoverLift_isPullback (boundaryLineProjection R) p z s hs ⊤ O
    (fun _ _ => trivial) H).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (sourceNativeParameterIso R O)
      (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
      (by simp only [Iso.refl_hom, Category.comp_id])
      (by simp only [Iso.refl_hom, Category.id_comp, sourceNativeCoverMap])
      (by simp only [Iso.refl_hom, Category.id_comp,
        boundaryBaseLift_sourceNativeParameterIso])

end AlgebraicGeometry.RelativeProjectiveLine
