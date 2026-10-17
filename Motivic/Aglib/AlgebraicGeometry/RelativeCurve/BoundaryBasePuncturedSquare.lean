/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.BoundaryBaseWholeTarget
/-! # The actual punctured square after the common source and base refinement -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Hom
variable {S X Y A C T : Scheme.{u}} (q : X ⟶ S) (p : Y ⟶ X) (a : A ⟶ X)
  (U : X.Opens) (V : S.Opens)

abbrev boundaryBaseOverlap :=
  pullback (boundaryBaseCoverMap q p U V) (boundaryBaseCoverMap q a U V)

def boundaryBaseOverlapMap : boundaryBaseOverlap q p a U V ⟶ pullback p a :=
  pullback.lift (pullback.fst _ _ ≫ (boundaryBaseCoverOpen q p U V).ι)
    (pullback.snd _ _ ≫ (boundaryBaseCoverOpen q a U V).ι) (by
      simp only [Category.assoc, ← morphismRestrict_ι]
      exact congrArg (fun f => f ≫ (boundaryBaseSourceOpen q U V).ι)
        (pullback.condition (f := boundaryBaseCoverMap q p U V)
          (g := boundaryBaseCoverMap q a U V)))

@[reassoc (attr := simp)]
theorem boundaryBaseOverlapMap_fst : boundaryBaseOverlapMap q p a U V ≫ pullback.fst p a =
    pullback.fst _ _ ≫ (boundaryBaseCoverOpen q p U V).ι := pullback.lift_fst _ _ _
@[reassoc (attr := simp)]
theorem boundaryBaseOverlapMap_snd : boundaryBaseOverlapMap q p a U V ≫ pullback.snd p a =
    pullback.snd _ _ ≫ (boundaryBaseCoverOpen q a U V).ι := pullback.lift_snd _ _ _

variable (π : C ⟶ S) (j : Y ⟶ C) (hj : j ≫ π = p ≫ q)
  (v : T ⟶ C) (φ : pullback p a ⟶ T) (hφ : φ ≫ v = pullback.fst p a ≫ j)

/-- The overlap maps to the original retained target restricted only on the base. -/
def boundaryBaseOverlapTarget : boundaryBaseOverlap q p a U V ⟶ ((v ≫ π) ⁻¹ᵁ V).toScheme :=
  (isPullback_morphismRestrict (v ≫ π) V).lift
    (pullback.fst _ _ ≫ boundaryBaseCoverMap q p U V ≫ boundaryBaseSourceProjection q U V)
    (boundaryBaseOverlapMap q p a U V ≫ φ) (by
      simp only [Category.assoc, boundaryBaseSourceProjection_ι]
      rw [← Category.assoc φ, hφ]
      simp only [Category.assoc, boundaryBaseOverlapMap_fst_assoc, hj]
      simp only [boundaryBaseCoverMap, morphismRestrict_ι_assoc])

@[reassoc (attr := simp)]
theorem boundaryBaseOverlapTarget_ι :
    boundaryBaseOverlapTarget q p a U V π j hj v φ hφ ≫ ((v ≫ π) ⁻¹ᵁ V).ι =
      boundaryBaseOverlapMap q p a U V ≫ φ :=
  (isPullback_morphismRestrict (v ≫ π) V).lift_snd _ _ _

/-- Literal target compatibility needed by the original-section pencil consumer. -/
@[reassoc]
theorem boundaryBaseOverlapTarget_inclusion :
    boundaryBaseOverlapTarget q p a U V π j hj v φ hφ ≫
      boundaryBaseRetainedTarget π V v =
    pullback.fst _ _ ≫ boundaryBaseCoverInclusion q p π j hj U V := by
  apply (cancel_mono (pullback.snd V.ι π)).mp
  simp only [Category.assoc, boundaryBaseRetainedTarget, boundaryBaseWholeMap_snd,
    boundaryBaseOverlapTarget_ι_assoc, boundaryBaseCoverInclusion_snd]
  rw [hφ]
  simp only [boundaryBaseOverlapMap_fst_assoc]
end AlgebraicGeometry.Scheme.Hom
