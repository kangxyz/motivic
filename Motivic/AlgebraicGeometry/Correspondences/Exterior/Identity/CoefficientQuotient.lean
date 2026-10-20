/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Exterior.Identity.ParameterDiagonal

/-!
# The full coefficient quotient by the parameter diagonal

The literal parameter-diagonal pullback is the full original support product
with one common parameter. All comparisons are actual scheme isomorphisms.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X Y Z : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom]

/-- The same coefficient product, with its base maps expressed by parameter projections. -/
def exteriorCoefficientBaseIso :
    (A.exteriorIdentityGenerator T).supportProduct (B.exteriorIdentityGenerator T) ≅
      pullback (A.exteriorIdentityParameter T ≫ T.hom) (B.exteriorIdentityParameter T ≫ T.hom) :=
  pullback.congrHom (A.exteriorIdentityParameter_target_base T).symm
    (B.exteriorIdentityParameter_source_base T).symm

/-- The canonical pair map on the parameter presentation of the coefficient product. -/
abbrev exteriorParameterPairCanonical :=
  pullback.map (A.exteriorIdentityParameter T ≫ T.hom) (B.exteriorIdentityParameter T ≫ T.hom)
    T.hom T.hom (A.exteriorIdentityParameter T) (B.exteriorIdentityParameter T)
    (𝟙 (Spec (.of k))) (by simp) (by simp)

@[reassoc]
theorem exteriorCoefficientBaseIso_hom_pair :
    (A.exteriorCoefficientBaseIso B T).hom ≫ A.exteriorParameterPairCanonical B T =
      A.exteriorCoefficientParameterPair T B := by
  apply pullback.hom_ext <;>
    simp [exteriorCoefficientBaseIso, exteriorParameterPairCanonical,
      exteriorCoefficientParameterPair, pullback.congrHom_hom, pullback.map]

/-- Impose equality of the actual support parameters before changing the base presentation. -/
def exteriorParameterPullbackToCoefficient :
    pullback (A.exteriorIdentityParameter T) (B.exteriorIdentityParameter T) ⟶
      (A.exteriorIdentityGenerator T).supportProduct (B.exteriorIdentityGenerator T) :=
  pullback.mapDesc (A.exteriorIdentityParameter T) (B.exteriorIdentityParameter T) T.hom ≫
    (A.exteriorCoefficientBaseIso B T).inv

/-- The parameter pullback is the exact closed fiber of the actual coefficient parameter pair. -/
theorem exteriorParameterPullback_isPullback :
    IsPullback
      (pullback.fst (A.exteriorIdentityParameter T) (B.exteriorIdentityParameter T) ≫
        A.exteriorIdentityParameter T)
      (A.exteriorParameterPullbackToCoefficient B T)
      (pullback.diagonal T.hom) (A.exteriorCoefficientParameterPair T B) := by
  apply (pullback_map_diagonal_isPullback
    (A.exteriorIdentityParameter T) (B.exteriorIdentityParameter T) T.hom).of_iso
      (Iso.refl _) (Iso.refl _) (A.exteriorCoefficientBaseIso B T).symm (Iso.refl _)
  · simp
  · simp [exteriorParameterPullbackToCoefficient]
  · simp
  · simpa only [Iso.refl_hom, Category.comp_id, Iso.symm_hom,
      ← A.exteriorCoefficientBaseIso_hom_pair B T] using
      (Iso.inv_hom_id_assoc (A.exteriorCoefficientBaseIso B T)
        (A.exteriorParameterPairCanonical B T)).symm

/-- The explicit parameter pullback is the actual parameter-diagonal quotient scheme. -/
def exteriorParameterPullbackIso :
    pullback (A.exteriorIdentityParameter T) (B.exteriorIdentityParameter T) ≅
      A.exteriorParameterDiagonal T B :=
  (A.exteriorParameterPullback_isPullback B T).isoPullback

/-- Use the first support's target-side base map without changing its parameter. -/
def exteriorFirstTargetProductIso :
    pullback (A.targetProjection ≫ Y.hom) T.hom ≅ (A.exteriorIdentityGenerator T).scheme :=
  pullback.congrHom A.projection_base.symm rfl ≪≫ A.exteriorIdentitySchemeIso T

@[reassoc (attr := simp)]
theorem exteriorFirstTargetProductIso_hom_parameter :
    (A.exteriorFirstTargetProductIso T).hom ≫ A.exteriorIdentityParameter T =
      pullback.snd (A.targetProjection ≫ Y.hom) T.hom := by
  simp [exteriorFirstTargetProductIso, exteriorIdentityParameter, Category.assoc,
    pullback.congrHom_hom, pullback.map]

/-- Compare the common-parameter pullbacks through the actual support image isomorphisms. -/
def exteriorSupportParameterPullbackIso :
    pullback (pullback.snd (A.targetProjection ≫ Y.hom) T.hom)
      (pullback.snd (B.projection ≫ Y.hom) T.hom) ≅
        pullback (A.exteriorIdentityParameter T) (B.exteriorIdentityParameter T) := by
  let f := pullback.map
    (pullback.snd (A.targetProjection ≫ Y.hom) T.hom)
    (pullback.snd (B.projection ≫ Y.hom) T.hom)
    (A.exteriorIdentityParameter T) (B.exteriorIdentityParameter T)
    (A.exteriorFirstTargetProductIso T).hom (B.exteriorIdentitySchemeIso T).hom (𝟙 T.left)
    (by simp) (by simp [exteriorIdentityParameter])
  have : IsIso (𝟙 T.left) := (Iso.refl T.left).isIso_hom
  have : IsIso f := pullback.map_isIso _ _ _ _ _ _ _ _ _
  exact asIso f

/-- The old support product with a single independent parameter. -/
abbrev exteriorCoefficientQuotientSupport :=
  pullback
    (pullback.fst (A.targetProjection ≫ Y.hom) (B.projection ≫ Y.hom) ≫
      (A.targetProjection ≫ Y.hom)) T.hom

/-- Pullback associativity identifies the literal shared-parameter support product. -/
def exteriorCoefficientProductIso :
    A.exteriorCoefficientQuotientSupport B T ≅
      pullback (pullback.snd (A.targetProjection ≫ Y.hom) T.hom)
        (pullback.snd (B.projection ≫ Y.hom) T.hom) :=
  pullback.congrHom pullback.condition rfl ≪≫
    pullbackAssoc (A.targetProjection ≫ Y.hom) (B.projection ≫ Y.hom)
      (B.projection ≫ Y.hom) T.hom ≪≫
    pullback.congrHom rfl (pullback.condition (f := B.projection ≫ Y.hom) (g := T.hom)) ≪≫
    (pullbackLeftPullbackSndIso (A.targetProjection ≫ Y.hom) T.hom
      (pullback.snd (B.projection ≫ Y.hom) T.hom)).symm

/-- The full parameter-diagonal coefficient quotient is the original support product times T. -/
def exteriorCoefficientQuotientIso :
    A.exteriorCoefficientQuotientSupport B T ≅ A.exteriorParameterDiagonal T B :=
  A.exteriorCoefficientProductIso B T ≪≫ A.exteriorSupportParameterPullbackIso B T ≪≫
    A.exteriorParameterPullbackIso B T

@[reassoc (attr := simp)]
theorem exteriorParameterPullbackIso_hom_inclusion :
    (A.exteriorParameterPullbackIso B T).hom ≫ A.exteriorParameterDiagonalInclusion T B =
      A.exteriorParameterPullbackToCoefficient B T :=
  (A.exteriorParameterPullback_isPullback B T).isoPullback_hom_snd

@[reassoc (attr := simp)]
theorem exteriorParameterPullbackIso_hom_parameter :
    (A.exteriorParameterPullbackIso B T).hom ≫
      pullback.fst (pullback.diagonal T.hom) (A.exteriorCoefficientParameterPair T B) =
        pullback.fst (A.exteriorIdentityParameter T) (B.exteriorIdentityParameter T) ≫
          A.exteriorIdentityParameter T :=
  (A.exteriorParameterPullback_isPullback B T).isoPullback_hom_fst

@[reassoc]
theorem exteriorCoefficientBaseIso_inv_fst :
    (A.exteriorCoefficientBaseIso B T).inv ≫
      pullback.fst
        ((A.exteriorIdentityGenerator T).targetProjection ≫ (SmoothSite.product Y T).hom)
        ((B.exteriorIdentityGenerator T).projection ≫ (SmoothSite.product Y T).hom) =
      pullback.fst (A.exteriorIdentityParameter T ≫ T.hom)
        (B.exteriorIdentityParameter T ≫ T.hom) := by
  simp [exteriorCoefficientBaseIso, pullback.congrHom_inv, pullback.map]

@[reassoc (attr := simp)]
theorem exteriorCoefficientBaseIso_inv_fst_simp :
    (A.exteriorCoefficientBaseIso B T).inv ≫
      pullback.fst
        ((@FiniteCorrespondenceGenerator.targetProjection (Spec (.of k))
          (pullback X.hom T.hom) (pullback Y.hom T.hom)
          (pullback.fst X.hom T.hom ≫ X.hom)
          (pullback.fst Y.hom T.hom ≫ Y.hom)
          (A.exteriorIdentityGenerator T)) ≫ (pullback.fst Y.hom T.hom ≫ Y.hom))
        ((@FiniteCorrespondenceGenerator.projection (Spec (.of k))
          (pullback Y.hom T.hom) (pullback Z.hom T.hom)
          (pullback.fst Y.hom T.hom ≫ Y.hom)
          (pullback.fst Z.hom T.hom ≫ Z.hom)
          (B.exteriorIdentityGenerator T)) ≫ (pullback.fst Y.hom T.hom ≫ Y.hom)) =
      pullback.fst (A.exteriorIdentityParameter T ≫ T.hom)
        (B.exteriorIdentityParameter T ≫ T.hom) :=
  exteriorCoefficientBaseIso_inv_fst A B T

@[reassoc]
theorem exteriorCoefficientBaseIso_inv_snd :
    (A.exteriorCoefficientBaseIso B T).inv ≫
      pullback.snd
        ((A.exteriorIdentityGenerator T).targetProjection ≫ (SmoothSite.product Y T).hom)
        ((B.exteriorIdentityGenerator T).projection ≫ (SmoothSite.product Y T).hom) =
      pullback.snd (A.exteriorIdentityParameter T ≫ T.hom)
        (B.exteriorIdentityParameter T ≫ T.hom) := by
  simp [exteriorCoefficientBaseIso, pullback.congrHom_inv, pullback.map]

@[reassoc (attr := simp)]
theorem exteriorCoefficientBaseIso_inv_snd_simp :
    (A.exteriorCoefficientBaseIso B T).inv ≫
      pullback.snd
        ((@FiniteCorrespondenceGenerator.targetProjection (Spec (.of k))
          (pullback X.hom T.hom) (pullback Y.hom T.hom)
          (pullback.fst X.hom T.hom ≫ X.hom)
          (pullback.fst Y.hom T.hom ≫ Y.hom)
          (A.exteriorIdentityGenerator T)) ≫ (pullback.fst Y.hom T.hom ≫ Y.hom))
        ((@FiniteCorrespondenceGenerator.projection (Spec (.of k))
          (pullback Y.hom T.hom) (pullback Z.hom T.hom)
          (pullback.fst Y.hom T.hom ≫ Y.hom)
          (pullback.fst Z.hom T.hom ≫ Z.hom)
          (B.exteriorIdentityGenerator T)) ≫ (pullback.fst Y.hom T.hom ≫ Y.hom)) =
      pullback.snd (A.exteriorIdentityParameter T ≫ T.hom)
        (B.exteriorIdentityParameter T ≫ T.hom) :=
  exteriorCoefficientBaseIso_inv_snd A B T

@[reassoc (attr := simp)]
theorem exteriorSupportParameterPullbackIso_hom_fst :
    (A.exteriorSupportParameterPullbackIso B T).hom ≫
      pullback.fst (A.exteriorIdentityParameter T) (B.exteriorIdentityParameter T) =
        pullback.fst (pullback.snd (A.targetProjection ≫ Y.hom) T.hom)
          (pullback.snd (B.projection ≫ Y.hom) T.hom) ≫
            (A.exteriorFirstTargetProductIso T).hom :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem exteriorSupportParameterPullbackIso_hom_snd :
    (A.exteriorSupportParameterPullbackIso B T).hom ≫
      pullback.snd (A.exteriorIdentityParameter T) (B.exteriorIdentityParameter T) =
        pullback.snd (pullback.snd (A.targetProjection ≫ Y.hom) T.hom)
          (pullback.snd (B.projection ≫ Y.hom) T.hom) ≫
            (B.exteriorIdentitySchemeIso T).hom :=
  pullback.lift_snd _ _ _

omit [GeometricallyIntegral T.hom] in
@[reassoc (attr := simp)]
theorem exteriorCoefficientProductIso_hom_first :
    (A.exteriorCoefficientProductIso B T).hom ≫
      pullback.fst (pullback.snd (A.targetProjection ≫ Y.hom) T.hom)
        (pullback.snd (B.projection ≫ Y.hom) T.hom) ≫
          pullback.fst (A.targetProjection ≫ Y.hom) T.hom =
      pullback.fst _ T.hom ≫
        pullback.fst (A.targetProjection ≫ Y.hom) (B.projection ≫ Y.hom) := by
  simp [exteriorCoefficientProductIso, pullback.congrHom_hom, pullback.map, Category.assoc]

omit [GeometricallyIntegral T.hom] in
@[reassoc (attr := simp)]
theorem exteriorCoefficientProductIso_hom_second :
    (A.exteriorCoefficientProductIso B T).hom ≫
      pullback.snd (pullback.snd (A.targetProjection ≫ Y.hom) T.hom)
        (pullback.snd (B.projection ≫ Y.hom) T.hom) ≫
          pullback.fst (B.projection ≫ Y.hom) T.hom =
      pullback.fst _ T.hom ≫
        pullback.snd (A.targetProjection ≫ Y.hom) (B.projection ≫ Y.hom) := by
  simp [exteriorCoefficientProductIso, pullback.congrHom_hom, pullback.map, Category.assoc]

omit [GeometricallyIntegral T.hom] in
@[reassoc (attr := simp)]
theorem exteriorCoefficientProductIso_hom_parameter :
    (A.exteriorCoefficientProductIso B T).hom ≫
      pullback.fst (pullback.snd (A.targetProjection ≫ Y.hom) T.hom)
        (pullback.snd (B.projection ≫ Y.hom) T.hom) ≫
          pullback.snd (A.targetProjection ≫ Y.hom) T.hom =
      pullback.snd _ T.hom := by
  simp [exteriorCoefficientProductIso, pullback.congrHom_hom, pullback.map, Category.assoc]

@[reassoc (attr := simp)]
theorem exteriorCoefficientQuotientIso_hom_parameter :
    (A.exteriorCoefficientQuotientIso B T).hom ≫
      pullback.fst (pullback.diagonal T.hom) (A.exteriorCoefficientParameterPair T B) =
        pullback.snd _ T.hom := by
  simp [exteriorCoefficientQuotientIso, Category.assoc]

@[reassoc (attr := simp)]
theorem exteriorFirstTargetProductIso_hom_old_fst :
    (A.exteriorFirstTargetProductIso T).hom ≫ (A.exteriorIdentitySchemeIso T).inv ≫
      pullback.fst (A.projection ≫ X.hom) T.hom =
        pullback.fst (A.targetProjection ≫ Y.hom) T.hom := by
  simp [exteriorFirstTargetProductIso, Category.assoc, pullback.congrHom_hom, pullback.map]

@[reassoc]
theorem exteriorCoefficientQuotientIso_hom_first :
    (A.exteriorCoefficientQuotientIso B T).hom ≫
      A.exteriorParameterDiagonalInclusion T B ≫
        pullback.fst
          ((A.exteriorIdentityGenerator T).targetProjection ≫ (SmoothSite.product Y T).hom)
          ((B.exteriorIdentityGenerator T).projection ≫ (SmoothSite.product Y T).hom) ≫
            (A.exteriorIdentitySchemeIso T).inv ≫ pullback.fst (A.projection ≫ X.hom) T.hom =
      pullback.fst _ T.hom ≫
        pullback.fst (A.targetProjection ≫ Y.hom) (B.projection ≫ Y.hom) := by
  simp only [exteriorCoefficientQuotientIso, Iso.trans_hom, Category.assoc,
    exteriorParameterPullbackIso_hom_inclusion_assoc, exteriorParameterPullbackToCoefficient,
    exteriorCoefficientBaseIso_inv_fst_assoc, pullback.mapDesc, pullback.map,
    pullback.lift_fst_assoc, Category.comp_id,
    exteriorSupportParameterPullbackIso_hom_fst_assoc,
    exteriorFirstTargetProductIso_hom_old_fst, exteriorCoefficientProductIso_hom_first]

@[reassoc (attr := simp)]
theorem exteriorCoefficientQuotientIso_hom_first_simp :
    (A.exteriorCoefficientQuotientIso B T).hom ≫
      A.exteriorParameterDiagonalInclusion T B ≫
        pullback.fst
          ((@FiniteCorrespondenceGenerator.targetProjection (Spec (.of k))
            (pullback X.hom T.hom) (pullback Y.hom T.hom)
            (pullback.fst X.hom T.hom ≫ X.hom)
            (pullback.fst Y.hom T.hom ≫ Y.hom)
            (A.exteriorIdentityGenerator T)) ≫ (pullback.fst Y.hom T.hom ≫ Y.hom))
          ((@FiniteCorrespondenceGenerator.projection (Spec (.of k))
            (pullback Y.hom T.hom) (pullback Z.hom T.hom)
            (pullback.fst Y.hom T.hom ≫ Y.hom)
            (pullback.fst Z.hom T.hom ≫ Z.hom)
            (B.exteriorIdentityGenerator T)) ≫ (pullback.fst Y.hom T.hom ≫ Y.hom)) ≫
            (A.exteriorIdentitySchemeIso T).inv ≫ pullback.fst (A.projection ≫ X.hom) T.hom =
      pullback.fst _ T.hom ≫
        pullback.fst (A.targetProjection ≫ Y.hom) (B.projection ≫ Y.hom) :=
  exteriorCoefficientQuotientIso_hom_first A B T

@[reassoc]
theorem exteriorCoefficientQuotientIso_hom_second :
    (A.exteriorCoefficientQuotientIso B T).hom ≫
      A.exteriorParameterDiagonalInclusion T B ≫
        pullback.snd
          ((A.exteriorIdentityGenerator T).targetProjection ≫ (SmoothSite.product Y T).hom)
          ((B.exteriorIdentityGenerator T).projection ≫ (SmoothSite.product Y T).hom) ≫
            (B.exteriorIdentitySchemeIso T).inv ≫ pullback.fst (B.projection ≫ Y.hom) T.hom =
      pullback.fst _ T.hom ≫
        pullback.snd (A.targetProjection ≫ Y.hom) (B.projection ≫ Y.hom) := by
  simp only [exteriorCoefficientQuotientIso, Iso.trans_hom, Category.assoc,
    exteriorParameterPullbackIso_hom_inclusion_assoc, exteriorParameterPullbackToCoefficient,
    exteriorCoefficientBaseIso_inv_snd_assoc, pullback.mapDesc, pullback.map,
    pullback.lift_snd_assoc, Category.comp_id,
    exteriorSupportParameterPullbackIso_hom_snd_assoc,
    Iso.hom_inv_id_assoc, exteriorCoefficientProductIso_hom_second]

@[reassoc (attr := simp)]
theorem exteriorCoefficientQuotientIso_hom_second_simp :
    (A.exteriorCoefficientQuotientIso B T).hom ≫
      A.exteriorParameterDiagonalInclusion T B ≫
        pullback.snd
          ((@FiniteCorrespondenceGenerator.targetProjection (Spec (.of k))
            (pullback X.hom T.hom) (pullback Y.hom T.hom)
            (pullback.fst X.hom T.hom ≫ X.hom)
            (pullback.fst Y.hom T.hom ≫ Y.hom)
            (A.exteriorIdentityGenerator T)) ≫ (pullback.fst Y.hom T.hom ≫ Y.hom))
          ((@FiniteCorrespondenceGenerator.projection (Spec (.of k))
            (pullback Y.hom T.hom) (pullback Z.hom T.hom)
            (pullback.fst Y.hom T.hom ≫ Y.hom)
            (pullback.fst Z.hom T.hom ≫ Z.hom)
            (B.exteriorIdentityGenerator T)) ≫ (pullback.fst Y.hom T.hom ≫ Y.hom)) ≫
            (B.exteriorIdentitySchemeIso T).inv ≫ pullback.fst (B.projection ≫ Y.hom) T.hom =
      pullback.fst _ T.hom ≫
        pullback.snd (A.targetProjection ≫ Y.hom) (B.projection ≫ Y.hom) :=
  exteriorCoefficientQuotientIso_hom_second A B T

/-- The actual coefficient quotient projects flatly to the original support product. -/
def exteriorCoefficientQuotientProjection :
    A.exteriorParameterDiagonal T B ⟶ A.supportProduct B :=
  (A.exteriorCoefficientQuotientIso B T).inv ≫ pullback.fst _ T.hom

instance exteriorCoefficientQuotientProjection_flat :
    Flat (A.exteriorCoefficientQuotientProjection B T) := by
  unfold exteriorCoefficientQuotientProjection
  infer_instance

@[reassoc (attr := simp)]
theorem exteriorCoefficientQuotientIso_hom_projection :
    (A.exteriorCoefficientQuotientIso B T).hom ≫
      A.exteriorCoefficientQuotientProjection B T = pullback.fst _ T.hom := by
  simp [exteriorCoefficientQuotientProjection]

@[reassoc]
theorem exteriorCoefficientQuotientProjection_fst :
    A.exteriorCoefficientQuotientProjection B T ≫
      pullback.fst (A.targetProjection ≫ Y.hom) (B.projection ≫ Y.hom) =
        A.exteriorParameterDiagonalInclusion T B ≫
          pullback.fst
            ((A.exteriorIdentityGenerator T).targetProjection ≫ (SmoothSite.product Y T).hom)
            ((B.exteriorIdentityGenerator T).projection ≫ (SmoothSite.product Y T).hom) ≫
              (A.exteriorIdentitySchemeIso T).inv ≫ pullback.fst (A.projection ≫ X.hom) T.hom := by
  apply (cancel_epi (A.exteriorCoefficientQuotientIso B T).hom).mp
  simp only [exteriorCoefficientQuotientIso_hom_projection_assoc,
    exteriorCoefficientQuotientIso_hom_first]

@[reassoc]
theorem exteriorCoefficientQuotientProjection_snd :
    A.exteriorCoefficientQuotientProjection B T ≫
      pullback.snd (A.targetProjection ≫ Y.hom) (B.projection ≫ Y.hom) =
        A.exteriorParameterDiagonalInclusion T B ≫
          pullback.snd
            ((A.exteriorIdentityGenerator T).targetProjection ≫ (SmoothSite.product Y T).hom)
            ((B.exteriorIdentityGenerator T).projection ≫ (SmoothSite.product Y T).hom) ≫
              (B.exteriorIdentitySchemeIso T).inv ≫ pullback.fst (B.projection ≫ Y.hom) T.hom := by
  apply (cancel_epi (A.exteriorCoefficientQuotientIso B T).hom).mp
  simp only [exteriorCoefficientQuotientIso_hom_projection_assoc,
    exteriorCoefficientQuotientIso_hom_second]

end Motivic.FiniteCorrespondenceGenerator
