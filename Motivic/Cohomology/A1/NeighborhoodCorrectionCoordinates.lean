/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.SmoothSiteNeighborhoodLambdaCylinder
public import Motivic.Cohomology.WholeAffineLineBaseSquare

/-! # Original neighborhood corrections over their unchanged coefficient field

The coefficient-localization field map is compared explicitly with the canonical
algebra map. Only the smooth-site structure is transported; every underlying
scheme map, polynomial coordinate, and whole-zero marking remains unchanged.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

namespace AlgebraicGeometry.RelativeProjectiveLine

variable (k R : Type u) [Field k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]
  (b : Spec (.of R) ⟶ Spec (.of k)) [Smooth b]
  (hb : b = AffineTorusPolynomialPresentation.baseMap k R)
  (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme] (r : R)

/-- The original psi object is the actual torus over D(r), with its original field map. -/
def neighborhoodPsiTorusIsoOfBaseEq :
    neighborhoodPsiSite k R b r ≅
      SmoothSite.torusCylinder (.of k) (fixedPsiBaseSite R r k) := by
  subst b
  exact neighborhoodPsiTorusIso R r k

/-- The original lambda map has the unchanged native scheme morphism. -/
def neighborhoodLambdaToCylinderOfBaseEq :
    neighborhoodLambdaSite k R b V r ⟶
      SmoothSite.a1Cylinder (.of k) (fixedPsiBaseSite R r k) := by
  subst b
  exact neighborhoodLambdaToCylinder k R V r

/-- Changing the field-map presentation does not change the psi morphism. -/
theorem neighborhoodPsiTorusIsoOfBaseEq_left :
    (neighborhoodPsiTorusIsoOfBaseEq k R b hb r).hom.left =
      (neighborhoodPsiTorusIso R r k).hom.left := by
  subst b
  rfl

/-- Changing the field-map presentation does not change the lambda morphism. -/
theorem neighborhoodLambdaToCylinderOfBaseEq_left :
    (neighborhoodLambdaToCylinderOfBaseEq k R b hb V r).left =
      (neighborhoodLambdaToCylinder k R V r).left := by
  subst b
  rfl

/-- The original lambda correction is still an actual open immersion. -/
instance neighborhoodLambdaToCylinderOfBaseEq_isOpenImmersion :
    IsOpenImmersion (neighborhoodLambdaToCylinderOfBaseEq k R b hb V r).left := by
  rw [neighborhoodLambdaToCylinderOfBaseEq_left]
  infer_instance

/-- The original correction square is cartesian in the actual smooth site. -/
theorem neighborhoodCorrection_isPullback :
    IsPullback
      (neighborhoodPencilBeta k R b V r ≫
        (neighborhoodPsiTorusIsoOfBaseEq k R b hb r).hom)
      (neighborhoodPencilAlpha k R b V r)
      (SmoothSite.contractionOpen (.of k) (fixedPsiBaseSite R r k))
      (neighborhoodLambdaToCylinderOfBaseEq k R b hb V r) := by
  subst b
  have H := neighborhoodLambdaPuncture_isPullback k R V r
  apply SmoothSite.isPullback_of_left
    (Square.mk _ _ _ _ (by
      apply MorphismProperty.Over.Hom.ext
      exact H.w)) H

/-- The full original zero marking remains the literal cylinder zero section. -/
@[reassoc] theorem neighborhoodLambdaZero_cylinderOfBaseEq
    (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V) :
    neighborhoodLambdaZero R V hV r ≫
      (neighborhoodLambdaToCylinderOfBaseEq k R b hb V r).left =
      (SmoothSite.a1Section (.of k) (fixedPsiBaseSite R r k) 0).left := by
  rw [neighborhoodLambdaToCylinderOfBaseEq_left]
  exact neighborhoodLambdaZero_cylinder k R V r hV

/-- The retained cylinder followed by an original scalar map has the literal
polynomial inclusion as its underlying affine-coordinate morphism. -/
@[reassoc] theorem neighborhoodLambdaToCylinderOfBaseEq_scalar
    (A : Type u) [CommRing A] [Algebra k A] [Algebra.Smooth k A] (f : A →ₐ[k] R) :
    (neighborhoodLambdaToCylinderOfBaseEq k R b hb V r).left ≫
      (SmoothSite.a1Map (.of k)
        (SmoothSite.openInclusion (AffineTorusPolynomialPresentation.affineSite k R)
          (PrimeSpectrum.basicOpen r) ≫
            AffineTorusPolynomialPresentation.affineMorphism f)).left =
      (neighborhoodSourceOpen R V r).ι ≫ V.ι ≫
        Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f.toRingHom)) ≫
          (Motivic.SmoothSiteAffineCoordinates.lineCylinderIso (k := k) (R := A)).hom.left := by
  have hn := congrArg (fun g => g.left)
    (Motivic.SmoothSiteAffineCoordinates.lineCylinderIso_naturality f)
  change Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f.toRingHom)) ≫
      (PolynomialOpenQuotient.ambientIso (algebraMap k A)).hom =
    (PolynomialOpenQuotient.ambientIso (algebraMap k R)).hom ≫
      (SmoothSite.a1Map (.of k) (AffineTorusPolynomialPresentation.affineMorphism f)).left at hn
  rw [SmoothSite.a1Map_comp]
  change (neighborhoodLambdaToCylinderOfBaseEq k R b hb V r).left ≫
      (SmoothSite.a1Map (.of k) (SmoothSite.openInclusion
        (AffineTorusPolynomialPresentation.affineSite k R) (PrimeSpectrum.basicOpen r))).left ≫
      (SmoothSite.a1Map (.of k) (AffineTorusPolynomialPresentation.affineMorphism f)).left = _
  rw [neighborhoodLambdaToCylinderOfBaseEq_left, ← Category.assoc,
    neighborhoodLambdaToCylinder_original]
  change ((neighborhoodSourceOpen R V r).ι ≫ V.ι ≫
      (PolynomialOpenQuotient.ambientIso (algebraMap k R)).hom) ≫
      (SmoothSite.a1Map (.of k) (AffineTorusPolynomialPresentation.affineMorphism f)).left =
    (neighborhoodSourceOpen R V r).ι ≫ V.ι ≫
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f.toRingHom)) ≫
        (PolynomialOpenQuotient.ambientIso (algebraMap k A)).hom
  simpa only [Category.assoc] using congrArg
    (fun g => (neighborhoodSourceOpen R V r).ι ≫ V.ι ≫ g) hn.symm

end AlgebraicGeometry.RelativeProjectiveLine
