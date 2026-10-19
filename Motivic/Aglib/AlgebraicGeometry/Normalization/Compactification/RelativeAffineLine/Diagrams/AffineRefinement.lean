/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Target.MarkedBaseChange
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.AffineMarkedSourceRefinement

/-! # The same affine refinement in native whole-line coordinates

The original affine source and full marked domain are not replaced. Only the
whole target parameter is reindexed through its actual coefficient-open iso.


Intended upstream module:
Module prefix: `Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.`
Module suffix: `Diagrams.AffineRefinement`.
Incoming project consumers:
Module prefix: `Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.`
Module suffix: `RelativeAffineLine.Diagrams.OriginalAffineRefinement`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RelativeProjectiveLine Scheme.Hom
universe u
namespace AlgebraicGeometry.Scheme
variable (R : Type u) [CommRing R]
  {T Y Z : Scheme.{u}} (e : T ≅ Spec (.of (Polynomial R)))
  (O : (Spec (.of R)).Opens) [IsAffine O.toScheme]

/-- The actual target-open restriction followed by the canonical native line iso. -/
def affineRefinedTargetIso :
    ((e.hom ≫ boundaryLineProjection R) ⁻¹ᵁ O).toScheme ≅
      Spec (.of (Polynomial Γ(O.toScheme, ⊤))) :=
  asIso (e.hom ∣_ (boundaryLineProjection R ⁻¹ᵁ O)) ≪≫ (targetAffineOpenIso R O).symm

@[reassoc]
theorem affineRefinedTargetIso_coordinate :
    (affineRefinedTargetIso R e O).hom ≫
      Spec.map (CommRingCat.ofHom
        (Polynomial.mapRingHom (ConstantCurve.affineSourceCoefficientMap R O.ι))) =
      ((e.hom ≫ boundaryLineProjection R) ⁻¹ᵁ O).ι ≫ e.hom := by
  simp only [affineRefinedTargetIso, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    Category.assoc, targetAffineOpenIso_inv_coordinate, morphismRestrict_ι]
  rfl

@[reassoc]
theorem affineRefinedTargetIso_projection :
    (affineRefinedTargetIso R e O).hom ≫ boundaryLineProjection Γ(O.toScheme, ⊤) =
      ((e.hom ≫ boundaryLineProjection R) ∣_ O) ≫ O.toScheme.isoSpec.hom := by
  apply (cancel_mono (O.toScheme.isoSpec.inv ≫ O.ι)).mp
  simp only [affineRefinedTargetIso, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    Category.assoc, targetAffineOpenIso_inv_projection, Iso.hom_inv_id_assoc,
    morphismRestrict_ι, morphismRestrict_ι_assoc]
  rfl

instance affineRefinedTarget_affine :
    IsAffine ((e.hom ≫ boundaryLineProjection R) ⁻¹ᵁ O).toScheme :=
  .of_isIso (affineRefinedTargetIso R e O).hom

/-- A genuinely affine original open member stays affine under this coefficient restriction. -/
theorem affineRefinedOpen_affine {A : Scheme.{u}} [IsAffine A] (i : A ⟶ T) :
    IsAffine ((i ≫ e.hom ≫ boundaryLineProjection R) ⁻¹ᵁ O).toScheme := by
  let : IsAffine T := .of_isIso e.hom
  exact (show IsAffineOpen ((e.hom ≫ boundaryLineProjection R) ⁻¹ᵁ O) from
    affineRefinedTarget_affine R e O).preimage i

variable (p : Y ⟶ T) (W : Y.Opens)
  (hW : W ≤ p ⁻¹ᵁ ((e.hom ≫ boundaryLineProjection R) ⁻¹ᵁ O))

/-- Native coordinates on the same original affine source. -/
def affineRefinedNativeMap : W.toScheme ⟶ Spec (.of (Polynomial Γ(O.toScheme, ⊤))) :=
  p.resLE ((e.hom ≫ boundaryLineProjection R) ⁻¹ᵁ O) W hW ≫
    (affineRefinedTargetIso R e O).hom

instance affineRefinedNativeMap_etale [Etale p] :
    Etale (affineRefinedNativeMap R e O p W hW) := by
  unfold affineRefinedNativeMap
  infer_instance

@[reassoc]
theorem affineRefinedNativeMap_coordinate :
    affineRefinedNativeMap R e O p W hW ≫
      Spec.map (CommRingCat.ofHom
        (Polynomial.mapRingHom (ConstantCurve.affineSourceCoefficientMap R O.ι))) =
      W.ι ≫ p ≫ e.hom := by
  simp only [affineRefinedNativeMap, Category.assoc, affineRefinedTargetIso_coordinate]
  rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]

/-- Both actual refined source objects are affine, hence so is their literal overlap. -/
theorem affineRefinedOverlap_affine [IsAffine W.toScheme]
    {A : Scheme.{u}} [IsAffine A] (i : A ⟶ T) :
    IsAffine (pullback
      ((i ∣_ ((e.hom ≫ boundaryLineProjection R) ⁻¹ᵁ O)) ≫
        (affineRefinedTargetIso R e O).hom)
      (affineRefinedNativeMap R e O p W hW)) := by
  let : IsAffine (i ⁻¹ᵁ ((e.hom ≫ boundaryLineProjection R) ⁻¹ᵁ O)).toScheme :=
    affineRefinedOpen_affine R e O i
  infer_instance

variable (z : Z ⟶ T)

/-- The entire original marked scheme over the coefficient open, in the same target. -/
def affineRefinedNativeMarked :
    ((z ≫ e.hom ≫ boundaryLineProjection R) ⁻¹ᵁ O).toScheme ⟶
      Spec (.of (Polynomial Γ(O.toScheme, ⊤))) :=
  (z ∣_ ((e.hom ≫ boundaryLineProjection R) ⁻¹ᵁ O)) ≫
    (affineRefinedTargetIso R e O).hom

instance affineRefinedNativeMarked_closed [IsClosedImmersion z] :
    IsClosedImmersion (affineRefinedNativeMarked R e O z) := by
  unfold affineRefinedNativeMarked
  infer_instance

/-- Finiteness uses the whole original marked map to the coefficient base. -/
instance affineRefinedNativeMarked_finite
    [IsFinite (z ≫ e.hom ≫ boundaryLineProjection R)] :
    IsFinite (affineRefinedNativeMarked R e O z ≫
      boundaryLineProjection Γ(O.toScheme, ⊤)) := by
  have he : affineRefinedNativeMarked R e O z ≫
      boundaryLineProjection Γ(O.toScheme, ⊤) =
      ((z ≫ e.hom ≫ boundaryLineProjection R) ∣_ O) ≫ O.toScheme.isoSpec.hom := by
    apply (cancel_mono (O.toScheme.isoSpec.inv ≫ O.ι)).mp
    simp only [affineRefinedNativeMarked, Category.assoc,
      affineRefinedTargetIso_projection, Iso.hom_inv_id_assoc,
      morphismRestrict_ι, morphismRestrict_ι_assoc]
    rfl
  rw [he]
  infer_instance

/-- The full scheme-theoretic marked square survives the target reindexing. -/
theorem affineRefinedNativeMarked_isPullback
    (t : ((z ≫ e.hom ≫ boundaryLineProjection R) ⁻¹ᵁ O).toScheme ⟶ W.toScheme)
    (H : IsPullback t (𝟙 _)
      (p.resLE ((e.hom ≫ boundaryLineProjection R) ⁻¹ᵁ O) W hW)
      (z ∣_ ((e.hom ≫ boundaryLineProjection R) ⁻¹ᵁ O))) :
    IsPullback t (𝟙 _) (affineRefinedNativeMap R e O p W hW)
      (affineRefinedNativeMarked R e O z) :=
  H.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (affineRefinedTargetIso R e O)
    (by simp) (by simp) (by simp [affineRefinedNativeMap])
    (by simp [affineRefinedNativeMarked])

end AlgebraicGeometry.Scheme
