/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Intersection.ClosedIntersectionAffineChart
public import Motivic.AlgebraicGeometry.Correspondences.TripleDiagonalAmbient

/-!
# Actual correspondence and quotient consumers of canonical affine charts

The first-stage support product uses its original six-factor closed immersion
and both original ideals. Refinement retains actual source restrictions; no
integrality, radicality or fixed component dimension is imposed.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic Motivic.Intersection

universe u

namespace Motivic.MotivicTest.ClosedIntersectionAffineChart

variable {S X Y Z W : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
  {h : Z ⟶ S} {i : W ⟶ S} [IsSeparated g]
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)

/-- The whole actual first-stage affine preimage is the literal sum-ideal quotient. -/
def firstStageAffineQuotient (U : (correspondenceSixfoldAmbient f g h i).affineOpens) :
    Γ(correspondenceSixfoldAmbient f g h i, U) ⧸
        ((correspondenceFirstDiagonalInclusion f g h i).ker.ideal U ⊔
          (F.tripleSupportProductInclusion G H).ker.ideal U) ≃+*
      Γ(F.leftIntermediateSupportProduct G H,
        (F.leftIntermediateAmbientInclusion G H) ⁻¹ᵁ U) :=
  closedIntersectionAffineQuotientEquiv (F.tripleSupportProductInclusion G H)
    (F.leftIntermediateSupportInclusion G H) (F.leftIntermediateToTripleSupport G H)
    (correspondenceFirstDiagonalInclusion f g h i) (F.leftIntermediate_ambient_isPullback G H) U

/-- This first-stage chart has the exact ambient-to-support section map. -/
theorem firstStageAffineQuotient_mk (U : (correspondenceSixfoldAmbient f g h i).affineOpens)
    (r : Γ(correspondenceSixfoldAmbient f g h i, U)) :
    firstStageAffineQuotient F G H U (Ideal.Quotient.mk _ r) =
      (F.leftIntermediateAmbientInclusion G H).app U r :=
  closedIntersectionAffineQuotientEquiv_mk _ _ _ _ _ U r

/-- Refinement compares the original source sections, not independently chosen charts. -/
theorem firstStageRefinement {U V : (correspondenceSixfoldAmbient f g h i).affineOpens}
    (hUV : U ≤ V)
    (x : Γ(correspondenceSixfoldAmbient f g h i, V) ⧸
      (F.leftIntermediateAmbientInclusion G H).ker.ideal V) :
    closedAffineQuotientEquiv (F.leftIntermediateAmbientInclusion G H) U
        (closedAffineQuotientRestriction (F.leftIntermediateAmbientInclusion G H) hUV x) =
      (F.leftIntermediateSupportProduct G H).presheaf.map
        (homOfLE ((F.leftIntermediateAmbientInclusion G H).preimage_mono hUV)).op
        (closedAffineQuotientEquiv (F.leftIntermediateAmbientInclusion G H) V x) :=
  closedAffineQuotientEquiv_naturality _ _ _

omit [IsSeparated g] in
/-- Repeated genuine refinements obey the original quotient restriction composition. -/
theorem firstStageRefinement_comp
    {U V T : (correspondenceSixfoldAmbient f g h i).affineOpens}
    (hUV : U ≤ V) (hVT : V ≤ T) :
    (closedAffineQuotientRestriction (F.leftIntermediateAmbientInclusion G H) hUV).comp
        (closedAffineQuotientRestriction (F.leftIntermediateAmbientInclusion G H) hVT) =
      closedAffineQuotientRestriction (F.leftIntermediateAmbientInclusion G H)
        (hUV.trans hVT) :=
  closedAffineQuotientRestriction_comp _ _ _

/-- Two arbitrary quotient closed subschemes use their actual Cartesian intersection.
The input ideals may be nonradical and the quotient rings may have nilpotents. -/
def quotientIntersection (R : Type u) [CommRing R] (I J : Ideal R)
    (U : (Spec (CommRingCat.of R)).affineOpens) :=
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  closedIntersectionAffineQuotientEquiv
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (pullback.fst (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))
    (pullback.snd (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) (.of_hasPullback _ _) U

end Motivic.MotivicTest.ClosedIntersectionAffineChart
