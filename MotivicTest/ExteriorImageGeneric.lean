/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.ExteriorImageGeneric
public import Motivic.AlgebraicGeometry.Intersection.WholeFiberTorGeneric

/-!
# Original smooth-site exterior image generic consumers

These consumers use arbitrary-field smooth-site objects and actual finite
correspondence supports, including the constructed whole coefficient sheaf.
No genericity, component-image injectivity or coefficient equality is supplied
as an extra hypothesis.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

namespace MotivicTest.ExteriorImageGeneric

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

/-- The first dominance step is attached to the original second generator. -/
theorem actualFirstSupportCartesianSquare :
    IsPullback (F.leftExteriorFirstSupportMap G H)
      (pullback.fst (F.incidenceTarget G ≫ Z.hom) (H.projection ≫ Z.hom) ≫
        F.incidenceSnd G)
      (pullback.fst (F.projection ≫ X.hom) (H.projection ≫ Z.hom) ≫ F.targetProjection)
      G.projection :=
  F.leftExteriorFirstSupportMap_isPullback G H

/-- The actual whole-image projection is finite, including all its nilpotents. -/
theorem actualImageSourceFinite : IsFinite (F.leftExteriorImageSourceMap G H) :=
  F.isFinite_leftExteriorImageSourceMap k G H

/-- Original exterior generic points land at true whole-image-product generics. -/
theorem actualExteriorImageGeneric (w : genericPoints (F.leftIntermediateSupportProduct G H)) :
    F.leftIntermediateImageMap G H w.1 ∈ genericPoints (F.leftIntermediateImageProduct G H) :=
  F.leftIntermediateImageMap_mem_genericPoints k G H w.1 w.2

variable (V : (F.leftIntermediateImageProduct G H).affineOpens)
  (w : genericPoints (F.firstStageWholeOpen G H V))

/-- The actual whole inverse-image generic point lands on a generic component
of the unreduced image product, using its original open immersion. -/
theorem actualWholeOpenImageGeneric :
    F.leftIntermediateImageMap G H w.1.1 ∈ genericPoints (F.leftIntermediateImageProduct G H) :=
  F.leftIntermediateImageMap_mem_genericPoints k G H w.1.1
    (F.firstStageWholeGenericOriginal G H V w).2

/-- The original whole-sheaf generic coefficient is now attached to an actual
image generic, while its original pair coefficient and true fiber length remain. -/
theorem actualWholeCoefficientImageAttachment :
    F.leftIntermediateImageMap G H w.1.1 ∈ genericPoints (F.leftIntermediateImageProduct G H) ∧
      F.firstStageWholeTorGenericCoefficient G H V w =
        F.incidenceTorCoefficient (S := Spec (.of k)) G (F.firstStageWholeGenericPair G H V w) *
          F.firstStageWholeGenericFiberMultiplicity G H V w :=
  ⟨actualWholeOpenImageGeneric F G H V w,
    F.firstStageWholeTorGenericCoefficient_eq_pair_mul G H V w⟩

end MotivicTest.ExteriorImageGeneric
