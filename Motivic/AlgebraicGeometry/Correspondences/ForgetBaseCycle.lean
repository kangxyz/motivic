/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.ForgetBaseSupport

/-! # Original signed cycle pushforward under forgetting the base -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic

variable {S T X Y : Scheme.{u}} (r : T ⟶ S) {f : X ⟶ T} {g : Y ⟶ T}
  [IsSeparated r] [LocallyOfFiniteType r] [IsSeparated g] [LocallyOfFiniteType g]

namespace FiniteCorrespondence

/-- The additive map is the literal finite pushforward in the original products. -/
theorem toIntegralCycle_forgetBase (α : FiniteCorrespondence f g) :
    toIntegralCycle (forgetBase r f g α) =
      IntegralCycle.finitePushforward (forgetBaseProductMap r f g) (toIntegralCycle α) := by
  have he : toIntegralCycle.comp (forgetBase r f g) =
      (IntegralCycle.finitePushforward (forgetBaseProductMap r f g)).comp toIntegralCycle := by
    apply Finsupp.addHom_ext
    intro A n
    simp [IntegralCycle.finitePushforward_single, residueDegree_of_surjectiveOnStalks]
  exact DFunLike.congr_fun he α

end FiniteCorrespondence

namespace FiniteCorrespondenceGenerator

/-- The original source component is unchanged after forgetting the base. -/
theorem forgetBase_range_projection (A : FiniteCorrespondenceGenerator f g) :
    Set.range (A.forgetBase r).projection = Set.range A.projection := by
  rw [← A.forgetBaseSupportIso_hom_projection r]
  exact ((A.forgetBaseSupportIso r).hom.homeomorph.surjective.range_comp _).symm

/-- The original graph relation is transported by the actual support isomorphism. -/
theorem forgetBase_projection_target (A : FiniteCorrespondenceGenerator f g)
    (a : X ⟶ Y) (ha : A.projection ≫ a = A.targetProjection) :
    (A.forgetBase r).projection ≫ a = (A.forgetBase r).targetProjection := by
  apply (cancel_epi (A.forgetBaseSupportIso r).hom).mp
  simpa using ha

end FiniteCorrespondenceGenerator

end Motivic
