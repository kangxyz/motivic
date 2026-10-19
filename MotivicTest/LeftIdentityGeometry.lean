/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Graph.Stalks.Left
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Identity.Left.Fundamental
public import Motivic.Aglib.AlgebraicGeometry.Graph.LeftPair

/-!
# Independent consumers of actual left identity geometry and scalar transport

The actual support-product ring isomorphism retains every point and scalar
map. The ordinary fundamental-cycle identity is independent of the common
smooth graph regularity theorem and of any derived unit assertion.
-/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme.Products (correspondenceTripleInclusion leftGraphMiddlePair)
open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open _root_.AlgebraicGeometry.Scheme.Diagonal (baseChangeStalkMap)
open _root_.AlgebraicGeometry.Scheme.Intersection (coefficientStalkMap point_eq)
open _root_.AlgebraicGeometry.Scheme.Products (correspondenceTripleMiddle
  correspondenceTriple_isPullback)
open _root_.AlgebraicGeometry.Scheme.StalkTransport (pointedMap)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Motivic

universe u

namespace MotivicTest.LeftIdentityGeometry

variable {S X Y Z : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S}
  (A : FiniteCorrespondenceGenerator f g)

/-- Left diagonal incidence uses an actual ring isomorphism of full support-product stalks. -/
def identityCoefficientStalk [IsIntegral X] [IsSeparated f]
    (w : (identityGenerator f).incidence A) :
    (pullback (A.projection ≫ f) f).presheaf.stalk
        (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph A.projection f
          ((identityGenerator f).incidenceSnd A w)) ≅
      ((identityGenerator f).supportProduct A).presheaf.stalk
        ((identityGenerator f).incidenceToSupportProduct A w) :=
  (identityGenerator f).incidenceLeftGraphStalkIso A w

/-- Every actual diagonal scalar follows the same path to the actual coefficient stalk. -/
theorem actual_scalar_element
    (B : FiniteCorrespondenceGenerator g h) [IsIso A.targetProjection] (w : A.incidence B)
    (r : (pullback g g).presheaf.stalk
      (pullback.diagonal g
        (correspondenceTripleMiddle f g h (A.incidenceInclusion B w)))) :
    coefficientStalkMap
        (correspondenceTripleInclusion f g h) (A.incidenceInclusion B w)
        (A.supportProductInclusion B) (A.incidenceToSupportProduct B w)
        (point_eq _ _ _ _ (A.incidence_ambient_isPullback B) w)
      (baseChangeStalkMap (correspondenceTriple_isPullback f g h)
        (A.incidenceInclusion B w) r) =
    (A.incidenceLeftGraphStalkIso B w).hom
      (pointedMap (leftGraphMiddlePair B.projection g)
        (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph B.projection g (A.incidenceSnd B
          w))
        (pullback.diagonal g
          (correspondenceTripleMiddle f g h (A.incidenceInclusion B w)))
        (A.incidenceLeftGraphMiddlePoint_eq B w) r) :=
  ConcreteCategory.congr_hom (A.incidenceLeftDiagonalStalkMap_comp B w) r

/-- Ordinary fundamental pushforward already gives the genuine left identity cycle. -/
theorem ordinary_left_identity (k : Type u) [Field k]
    {X Y : SmoothSite (Spec (.of k))} (A : FiniteCorrespondenceGenerator X.hom Y.hom)
    [IsIntegral ((𝟭 Scheme).obj X.left)] :
    (identityGenerator X.hom).incidenceFundamentalCorrespondence k A = A.cycle :=
  A.incidenceFundamentalCorrespondence_identity_left k

end MotivicTest.LeftIdentityGeometry
