/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Modules.FinitePushforwardRestriction
public import Motivic.AlgebraicGeometry.Correspondences.IntermediateDiagonalLists

/-!
# Actual finite image-product open-base-change consumers

The genuine finite intermediate-image map is used as the vertical morphism.
Its whole affine chart is proved Cartesian. Arbitrary original complexes and
maps satisfy the actual base-change squares; a genuinely given QC complex
also yields the actual global pushforward stalk from its constructed whole
coordinate complex. No coefficient-sheaf existence is presumed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.MotivicTest.FinitePushforwardRestriction

open Scheme.Modules Motivic.FiniteAffineChart Motivic.AffineQuasicoherent
  Motivic.FinitePushforwardRestriction Motivic.ModuleStalk

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i) [IsSeparated h]
  {U : (F.leftIntermediateImageProduct G H).Opens} (hU : IsAffineOpen U)

/-- The actual finite image-product map has the whole Cartesian coordinate chart. -/
theorem actualImageProductPullback :
    IsPullback (sourceChart (F.leftIntermediateImageMap G H) hU)
      (coordinateMap (F.leftIntermediateImageMap G H))
      (F.leftIntermediateImageMap G H) hU.fromSpec :=
  wholeChartIsPullback _ hU

/-- The real finite vertical map, without an open-immersion hypothesis on it,
satisfies natural base change for every original module map. -/
theorem actualImageProductNaturality
    {M N : (F.leftIntermediateSupportProduct G H).Modules} (φ : M ⟶ N) :
    (pushforward (F.leftIntermediateImageMap G H) ⋙ restrictFunctor hU.fromSpec).map φ ≫
        (wholeChartPushforwardIso (F.leftIntermediateImageMap G H) hU).hom.app N =
      (wholeChartPushforwardIso (F.leftIntermediateImageMap G H) hU).hom.app M ≫
        (restrictFunctor (sourceChart (F.leftIntermediateImageMap G H) hU) ⋙
          pushforward (coordinateMap (F.leftIntermediateImageMap G H))).map φ :=
  (wholeChartPushforwardIso _ hU).hom.naturality φ

/-- Arbitrary original sheaf-complex differentials survive the actual finite
vertical/open-horizontal base-change square. -/
theorem actualImageProductDifferential
    (K : ChainComplex (F.leftIntermediateSupportProduct G H).Modules ℕ) (n m : ℕ) :
    (((pushforward (F.leftIntermediateImageMap G H) ⋙
        restrictFunctor hU.fromSpec).mapHomologicalComplex _).obj K).d n m ≫
        ((wholeChartPushforwardComplexIso (F.leftIntermediateImageMap G H) hU _).app K).hom.f m =
      ((wholeChartPushforwardComplexIso (F.leftIntermediateImageMap G H) hU _).app K).hom.f n ≫
        (((restrictFunctor (sourceChart (F.leftIntermediateImageMap G H) hU) ⋙
          pushforward (coordinateMap (F.leftIntermediateImageMap G H))).mapHomologicalComplex _).obj
            K).d n m :=
  (((wholeChartPushforwardComplexIso _ hU _).app K).hom.comm n m).symm

/-- A given QC complex on the actual first-stage support has its original
global finite pushforward stalk recovered from the entire coordinate algebra. -/
def actualImageProductPushforwardStalk
    (K : ChainComplex (F.leftIntermediateSupportProduct G H).Modules ℕ)
    [∀ n, (K.X n).IsQuasicoherent]
    (p : Spec Γ(F.leftIntermediateImageProduct G H, U)) :
    ((tilde.functor Γ(F.leftIntermediateSupportProduct G H,
        (F.leftIntermediateImageMap G H) ⁻¹ᵁ U) ⋙
      pushforward (coordinateMap (F.leftIntermediateImageMap G H)) ⋙
      functor p).mapHomologicalComplex _).obj
        (wholeChartCoordinateComplex _ (F.leftIntermediateImageMap G H) hU K) ≅
      ((pushforward (F.leftIntermediateImageMap G H) ⋙ functor (hU.fromSpec p) ⋙
        ModuleCat.restrictScalars
          (inv (hU.fromSpec.stalkMap p)).hom).mapHomologicalComplex _).obj K :=
  wholeChartPushforwardStalkIso _ hU _ K p

end Motivic.MotivicTest.FinitePushforwardRestriction
