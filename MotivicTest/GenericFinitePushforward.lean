/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.GenericFinitePushforward
public import Motivic.AlgebraicGeometry.Correspondences.ExteriorImageGeneric
public import Motivic.AlgebraicGeometry.Intersection.WholeFiberTorGeneric

/-!
# Actual exterior collision regrouping consumers

The map is the original whole intermediate image map on arbitrary-field smooth
correspondences. Generic preservation and finite generic index types come from
the actual geometry. Signed collision consumers retain the actual residue degree
of each source point. The whole inverse-image coefficient consumer also retains
the original pair coefficient and the actual exterior closed-fiber length.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open scoped BigOperators

universe u

namespace MotivicTest.GenericFinitePushforward

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

local instance exteriorBase_isNoetherian :
    IsNoetherian (pullback X.hom (H.projection ≫ Z.hom)) := by
  have : IsNoetherian ((𝟭 Scheme).obj X.left) :=
    inferInstanceAs (IsNoetherian X.left)
  exact isNoetherian_of_finiteType (pullback.fst X.hom (H.projection ≫ Z.hom))

local instance exteriorImage_isNoetherian :
    IsNoetherian (F.leftIntermediateImageProduct G H) := by
  have := F.isFinite_leftExteriorImageSourceMap k G H
  exact isNoetherian_of_finiteType (F.leftExteriorImageSourceMap G H)

local instance exteriorSupport_isNoetherian :
    IsNoetherian (F.leftIntermediateSupportProduct G H) :=
  isNoetherian_of_finiteType (F.leftIntermediateImageMap G H)

/-- The original exterior source and whole image have finite generic index sets. -/
theorem actualExteriorGenericIndicesFinite :
    (genericPoints (F.leftIntermediateSupportProduct G H)).Finite ∧
      (genericPoints (F.leftIntermediateImageProduct G H)).Finite :=
  ⟨genericPoints.finite finite_irreducibleComponents_of_isNoetherian,
    genericPoints.finite finite_irreducibleComponents_of_isNoetherian⟩

/-- The actual integral finite-image support is the point closure of the original image. -/
theorem actualExteriorImagePointClosure
    (w : genericPoints (F.leftIntermediateSupportProduct G H)) :
    (IntegralClosedSubscheme.pointClosure w.1).finiteImage
        (F.leftIntermediateImageMap G H) =
      IntegralClosedSubscheme.pointClosure (F.leftIntermediateImageMap G H w.1) :=
  IntegralClosedSubscheme.pointClosure_finiteImage (F.leftIntermediateImageMap G H) w.1

/-- Every actual collision is regrouped on the genuine target generic components;
generic preservation is proved by the component-normal Cartesian geometry. -/
theorem actualExteriorGroupedCycle
    (c : genericPoints (F.leftIntermediateSupportProduct G H) → ℤ) :
    IntegralCycle.finitePushforward (F.leftIntermediateImageMap G H)
        (IntegralCycle.ofGenericCoefficients (F.leftIntermediateSupportProduct G H) c) =
      IntegralCycle.ofGenericCoefficients (F.leftIntermediateImageProduct G H)
        (fun y => IntegralCycle.genericPushforwardCoefficient
          (F.leftIntermediateImageMap G H) c y.1) :=
  IntegralCycle.finitePushforward_ofGenericCoefficients
    (F.leftIntermediateImageMap G H)
    (fun w => F.leftIntermediateImageMap_mem_genericPoints k G H w.1 w.2) c

/-- Signed coefficients at colliding actual exterior components retain both degrees. -/
theorem actualExteriorSignedCollision
    (w₁ w₂ : genericPoints (F.leftIntermediateSupportProduct G H))
    (h : F.leftIntermediateImageMap G H w₁.1 = F.leftIntermediateImageMap G H w₂.1)
    (m n : ℤ) :
    IntegralCycle.finitePushforward (F.leftIntermediateImageMap G H)
        (Finsupp.single (IntegralClosedSubscheme.pointClosure w₁.1) m +
          Finsupp.single (IntegralClosedSubscheme.pointClosure w₂.1) n) =
      Finsupp.single (IntegralClosedSubscheme.pointClosure
          (F.leftIntermediateImageMap G H w₂.1))
        (m * ((F.leftIntermediateImageMap G H).residueDegree w₁.1 : ℤ) +
          n * ((F.leftIntermediateImageMap G H).residueDegree w₂.1 : ℤ)) :=
  IntegralCycle.finitePushforward_two_pointClosures
    (F.leftIntermediateImageMap G H) w₁.1 w₂.1 h m n

/-- Genuine opposite cross-degree weights cancel without any injective generic map. -/
theorem actualExteriorCollisionCancellation
    (w₁ w₂ : genericPoints (F.leftIntermediateSupportProduct G H))
    (h : F.leftIntermediateImageMap G H w₁.1 = F.leftIntermediateImageMap G H w₂.1) :
    IntegralCycle.finitePushforward (F.leftIntermediateImageMap G H)
        (Finsupp.single (IntegralClosedSubscheme.pointClosure w₁.1)
            ((F.leftIntermediateImageMap G H).residueDegree w₂.1 : ℤ) -
          Finsupp.single (IntegralClosedSubscheme.pointClosure w₂.1)
            ((F.leftIntermediateImageMap G H).residueDegree w₁.1 : ℤ)) = 0 :=
  IntegralCycle.finitePushforward_collision_cancel
    (F.leftIntermediateImageMap G H) w₁.1 w₂.1 h

open Classical in
/-- The original whole Tor cycle gives the finite collision sum with its pair
coefficient, true exterior closed-fiber multiplicity and actual restricted-map degree. -/
theorem actualWholeCoefficientCollisionSum
    (V : (F.leftIntermediateImageProduct G H).affineOpens) (y : V.1) :
    IntegralCycle.toPoints
        (IntegralCycle.finitePushforward ((F.leftIntermediateImageMap G H) ∣_ V.1)
          (F.firstStageWholeTorGenericCycle G H V)) y =
      letI := IntegralCycle.genericPointFintype (F.firstStageWholeOpen G H V)
      ∑ w, if ((F.leftIntermediateImageMap G H) ∣_ V.1) w.1 = y then
        (F.incidenceTorCoefficient (S := Spec (.of k)) G
            (F.firstStageWholeGenericPair G H V w) *
          F.firstStageWholeGenericFiberMultiplicity G H V w) *
            (((F.leftIntermediateImageMap G H) ∣_ V.1).residueDegree w.1 : ℤ)
        else 0 := by
  rw [F.firstStageWholeTorGenericCycle_eq_pair_mul G H V]
  exact IntegralCycle.toPoints_finitePushforward_ofGenericCoefficients_apply
    ((F.leftIntermediateImageMap G H) ∣_ V.1) _ y

end MotivicTest.GenericFinitePushforward
