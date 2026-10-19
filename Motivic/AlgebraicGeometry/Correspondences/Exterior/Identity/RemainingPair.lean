/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Exterior.Identity.CoefficientQuotient
public import Motivic.Aglib.AlgebraicGeometry.Intersection.StalkTorTransport
public import Motivic.Aglib.Algebra.Homology.Koszul.FlatLocalMultiplicity

/-!
# The original remaining middle pair on exterior coefficient quotients

The parameter quotient preserves both original middle coordinates. Its flat
projection to the original support product therefore gives the same pointed
scalar map on every original middle-diagonal equation. No regularity is
asserted for these remaining equations after imposing correspondence supports.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Products

variable {k : Type u} [Field k] {X Y Z : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom]

/-- The original middle pair on the original coefficient support product. -/
def originalCoefficientMiddlePair : A.supportProduct B ⟶ pullback Y.hom Y.hom :=
  A.supportProductInclusion B ≫ correspondenceMiddlePair X.hom Y.hom Z.hom

omit [GeometricallyIntegral T.hom] in
@[reassoc (attr := simp)]
theorem originalCoefficientMiddlePair_fst :
    A.originalCoefficientMiddlePair B ≫ pullback.fst Y.hom Y.hom =
      pullback.fst (A.targetProjection ≫ Y.hom) (B.projection ≫ Y.hom) ≫ A.targetProjection := by
  simp only [originalCoefficientMiddlePair, Category.assoc, correspondenceMiddlePair_fst,
    supportProductInclusion_fst_assoc]

omit [GeometricallyIntegral T.hom] in
@[reassoc (attr := simp)]
theorem originalCoefficientMiddlePair_snd :
    A.originalCoefficientMiddlePair B ≫ pullback.snd Y.hom Y.hom =
      pullback.snd (A.targetProjection ≫ Y.hom) (B.projection ≫ Y.hom) ≫ B.projection := by
  simp only [originalCoefficientMiddlePair, Category.assoc, correspondenceMiddlePair_snd,
    supportProductInclusion_snd_assoc]
  rfl

/-- Forget only the two parameter coordinates on the actual exterior coefficient product. -/
def exteriorCoefficientOldMiddlePair :
    (A.exteriorIdentityGenerator T).supportProduct (B.exteriorIdentityGenerator T) ⟶
      pullback Y.hom Y.hom :=
  pullback.map _ _ Y.hom Y.hom
    ((A.exteriorIdentityGenerator T).targetProjection ≫ (SmoothSite.productFst Y T).left)
    ((B.exteriorIdentityGenerator T).projection ≫ (SmoothSite.productFst Y T).left)
    (𝟙 (Spec (.of k)))
    (by
      exact (Category.comp_id (obj := Scheme) _).trans
        (Category.assoc _ _ _).symm)
    (by
      exact (Category.comp_id (obj := Scheme) _).trans
        (Category.assoc _ _ _).symm)

@[reassoc (attr := simp)]
theorem exteriorCoefficientOldMiddlePair_fst :
    A.exteriorCoefficientOldMiddlePair B T ≫ pullback.fst Y.hom Y.hom =
      pullback.fst
        ((A.exteriorIdentityGenerator T).targetProjection ≫ (SmoothSite.product Y T).hom)
        ((B.exteriorIdentityGenerator T).projection ≫ (SmoothSite.product Y T).hom) ≫
          (A.exteriorIdentityGenerator T).targetProjection ≫ pullback.fst Y.hom T.hom :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem exteriorCoefficientOldMiddlePair_snd :
    A.exteriorCoefficientOldMiddlePair B T ≫ pullback.snd Y.hom Y.hom =
      pullback.snd
        ((A.exteriorIdentityGenerator T).targetProjection ≫ (SmoothSite.product Y T).hom)
        ((B.exteriorIdentityGenerator T).projection ≫ (SmoothSite.product Y T).hom) ≫
          (B.exteriorIdentityGenerator T).projection ≫ pullback.fst Y.hom T.hom :=
  pullback.lift_snd _ _ _

@[reassoc]
theorem exteriorIdentitySchemeIso_inv_old_target :
    (A.exteriorIdentitySchemeIso T).inv ≫ pullback.fst (A.projection ≫ X.hom) T.hom ≫
      A.targetProjection =
        (A.exteriorIdentityGenerator T).targetProjection ≫ pullback.fst Y.hom T.hom := by
  rw [← A.exteriorIdentitySchemeIso_inv_target T]
  simp only [Category.assoc, exteriorIdentityTarget_fst]

@[reassoc]
theorem exteriorIdentitySchemeIso_inv_old_source :
    (A.exteriorIdentitySchemeIso T).inv ≫ pullback.fst (A.projection ≫ X.hom) T.hom ≫
      A.projection =
        (A.exteriorIdentityGenerator T).projection ≫ pullback.fst X.hom T.hom := by
  rw [← A.exteriorIdentitySchemeIso_inv_source T]
  simp only [Category.assoc, exteriorIdentitySource_fst]

/-- The two literal routes to the original middle self-product agree. -/
@[reassoc]
theorem exteriorCoefficientQuotientProjection_middlePair :
    A.exteriorCoefficientQuotientProjection B T ≫ A.originalCoefficientMiddlePair B =
      A.exteriorParameterDiagonalInclusion T B ≫ A.exteriorCoefficientOldMiddlePair B T := by
  apply pullback.hom_ext
  · simp only [Category.assoc, originalCoefficientMiddlePair_fst,
      exteriorCoefficientOldMiddlePair_fst, exteriorCoefficientQuotientProjection_fst_assoc,
      exteriorIdentitySchemeIso_inv_old_target]
  · simp only [Category.assoc, originalCoefficientMiddlePair_snd,
      exteriorCoefficientOldMiddlePair_snd, exteriorCoefficientQuotientProjection_snd_assoc,
      exteriorIdentitySchemeIso_inv_old_source]

/-- The common middle equation has exactly the same actual pointed stalk action by either route. -/
theorem exteriorRemainingPair_pointedMap_square (z : A.exteriorParameterDiagonal T B)
    (p : (pullback Y.hom Y.hom : Scheme))
    (hp : p = A.originalCoefficientMiddlePair B (A.exteriorCoefficientQuotientProjection B T z))
    (hp' : p = A.exteriorCoefficientOldMiddlePair B T
      (A.exteriorParameterDiagonalInclusion T B z)) :
    StalkTransport.pointedMap (A.originalCoefficientMiddlePair B)
        (A.exteriorCoefficientQuotientProjection B T z) p hp ≫
      (A.exteriorCoefficientQuotientProjection B T).stalkMap z =
    StalkTransport.pointedMap (A.exteriorCoefficientOldMiddlePair B T)
        (A.exteriorParameterDiagonalInclusion T B z) p hp' ≫
      (A.exteriorParameterDiagonalInclusion T B).stalkMap z := by
  simpa only [StalkTransport.pointedMap_image] using
    StalkTransport.pointedMap_square
      (A.exteriorCoefficientQuotientProjection B T) (A.originalCoefficientMiddlePair B)
      (A.exteriorParameterDiagonalInclusion T B) (A.exteriorCoefficientOldMiddlePair B T)
      (A.exteriorCoefficientQuotientProjection_middlePair B T) z
      (A.exteriorCoefficientQuotientProjection B T z)
      (A.exteriorParameterDiagonalInclusion T B z) p rfl rfl hp hp'

/-- The same original list, with actual scalar maps, survives the parameter quotient. -/
theorem exteriorRemainingPair_list_square (z : A.exteriorParameterDiagonal T B)
    (p : (pullback Y.hom Y.hom : Scheme))
    (hp : p = A.originalCoefficientMiddlePair B (A.exteriorCoefficientQuotientProjection B T z))
    (hp' : p = A.exteriorCoefficientOldMiddlePair B T
      (A.exteriorParameterDiagonalInclusion T B z))
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk p)) :
    (s.map (StalkTransport.pointedMap (A.originalCoefficientMiddlePair B)
      (A.exteriorCoefficientQuotientProjection B T z) p hp).hom).map
        ((A.exteriorCoefficientQuotientProjection B T).stalkMap z).hom =
    (s.map (StalkTransport.pointedMap (A.exteriorCoefficientOldMiddlePair B T)
      (A.exteriorParameterDiagonalInclusion T B z) p hp').hom).map
        ((A.exteriorParameterDiagonalInclusion T B).stalkMap z).hom := by
  simp only [List.map_map]
  congr 1
  funext r
  exact ConcreteCategory.congr_hom (A.exteriorRemainingPair_pointedMap_square B T z p hp hp') r

/-- Every remaining homology length scales by the actual local closed fiber of
`(A.supportProduct B) × T → A.supportProduct B`. The remaining equations need
not be regular on the supports, and the closed fiber is not reduced by fiat. -/
theorem exteriorRemainingPair_homology_length (z : A.exteriorParameterDiagonal T B)
    (p : (pullback Y.hom Y.hom : Scheme))
    (hp : p = A.originalCoefficientMiddlePair B
      (A.exteriorCoefficientQuotientProjection B T z))
    (hp' : p = A.exteriorCoefficientOldMiddlePair B T
      (A.exteriorParameterDiagonalInclusion T B z))
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk p)) (n : ℕ) :
    Module.length ((A.exteriorParameterDiagonal T B).presheaf.stalk z)
      ((_root_.ChainComplex.Koszul.coefficientComplex
        (ModuleCat.of ((A.exteriorParameterDiagonal T B).presheaf.stalk z)
          ((A.exteriorParameterDiagonal T B).presheaf.stalk z))
        ((s.map (StalkTransport.pointedMap (A.exteriorCoefficientOldMiddlePair B T)
          (A.exteriorParameterDiagonalInclusion T B z) p hp').hom).map
            ((A.exteriorParameterDiagonalInclusion T B).stalkMap z).hom)).homology n) =
    Module.length ((A.supportProduct B).presheaf.stalk
        (A.exteriorCoefficientQuotientProjection B T z))
      ((_root_.ChainComplex.Koszul.coefficientComplex
        (ModuleCat.of ((A.supportProduct B).presheaf.stalk
            (A.exteriorCoefficientQuotientProjection B T z))
          ((A.supportProduct B).presheaf.stalk
            (A.exteriorCoefficientQuotientProjection B T z)))
        (s.map (StalkTransport.pointedMap (A.originalCoefficientMiddlePair B)
          (A.exteriorCoefficientQuotientProjection B T z) p hp).hom)).homology n) *
      Module.length ((A.exteriorParameterDiagonal T B).presheaf.stalk z)
        (_root_.ChainComplex.Koszul.coefficientClosedFiber
          ((A.exteriorCoefficientQuotientProjection B T).stalkMap z).hom) := by
  rw [← A.exteriorRemainingPair_list_square B T z p hp hp' s]
  exact _root_.ChainComplex.Koszul.regularCoefficientFlat_length
    ((A.exteriorCoefficientQuotientProjection B T).stalkMap z).hom
    (Flat.stalkMap _ _) _ n

end Motivic.FiniteCorrespondenceGenerator
