/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Intersection.RightWholeFiberTorGeneric

/-!
# Actual right whole Tor generic-cycle consumers

These consumers use arbitrary fields and the actual smooth-site objects,
without separability, perfectness, reduction, or one-branch assumptions. They
identify the previously constructed whole ambient coefficient, preserve its
literal original stalk action, and retain all Tor degrees and every generic
branch in the resulting integral cycle. These are source-only consumers;
compilation and acceptance are separate from their implementation.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

namespace MotivicTest.RightWholeFiberTorGeneric

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)
  (V : (F.rightIntermediateImageProduct G H).affineOpens)
  (w : genericPoints (F.rightFirstStageWholeOpen G H V))

local instance rightGenericBaseIsSeparated :
    ((Functor.fromPUnit (Spec (.of k))).obj X.right).IsSeparated :=
  inferInstanceAs (Spec (.of k)).IsSeparated

omit w in
/-- The whole-open coefficient is the original ambient coefficient restricted
along the original whole inverse-image open inclusion. -/
theorem actualExistingCoefficient (n : ℕ) :
    F.rightFirstStageWholeTorSheaf G H V n =
      (Scheme.Modules.restrictFunctor ((F.rightIntermediateImageMap G H) ⁻¹ᵁ V).ι).obj
        (F.rightFirstStageWholeAmbientCoefficient G H V n) :=
  F.rightFirstStageWholeTorSheaf_eq_restrict G H V n

/-- The whole generic projects to the genuine original G,H incidence generic. -/
theorem actualOriginalPairGeneric :
    F.rightExteriorPairProjection G H w.1.1 ∈ genericPoints (G.incidence H) :=
  (F.rightFirstStageWholeGenericPair G H V w).2

/-- The stalk attachment retains the actual open-inclusion scalar map. -/
def actualOriginalSupportedStalk (n : ℕ) :
    (ModuleCat.restrictScalars
      (((F.rightIntermediateImageMap G H) ⁻¹ᵁ V).ι.stalkMap w.1).hom).obj
        (F.rightFirstStageWholeGenericStalk G H V w n) ≅
      Intersection.closedIntersectionSupportedStalkTor
        (correspondenceSecondAmbientInclusion X.hom Y.hom Z.hom W.hom)
        (F.tripleSupportProductInclusion G H)
        (F.rightIntermediateSupportInclusion G H) (F.rightIntermediateToTripleSupport G H)
        (F.rightIntermediate_ambient_isPullback G H) w.1.1 n :=
  F.rightFirstStageWholeGenericStalkOriginalIso G H V w n

/-- Every actual whole stalk degree retains the original pair and exterior fiber. -/
theorem actualDegreewiseWholeMultiplicity (n : ℕ) :
    Module.length ((F.rightFirstStageWholeOpen G H V).presheaf.stalk w.1)
        (F.rightFirstStageWholeGenericStalk G H V w n) =
      Module.length (G.incidenceAmbientStalk H (F.rightFirstStageWholeGenericPair G H V w).1)
        (G.incidenceTor H (F.rightFirstStageWholeGenericPair G H V w).1 n) *
          Module.length ((F.rightIntermediateSupportProduct G H).presheaf.stalk w.1.1)
            (F.rightExteriorClosedFiber G H w.1.1) :=
  F.rightFirstStageWholeGeneric_length G H V w n

/-- The actual original quotient fiber has finite length before integer conversion. -/
theorem actualClosedFiberLength :
    Module.length ((F.rightIntermediateSupportProduct G H).presheaf.stalk w.1.1)
      (((F.rightIntermediateSupportProduct G H).presheaf.stalk w.1.1) ⧸
        (IsLocalRing.maximalIdeal
          ((G.incidence H).presheaf.stalk (F.rightExteriorPairProjection G H w.1.1))).map
            ((F.rightExteriorPairProjection G H).stalkMap w.1.1).hom) ≠ ⊤ :=
  F.rightFirstStageWholeGenericFiber_length_ne_top G H V w

/-- Every actual whole coefficient degree has finite length and finite degree support. -/
theorem actualWholeFiniteLengthSupport :
    LengthEuler.FiniteLengthSupport (F.rightFirstStageWholeGenericStalk G H V w) :=
  F.rightFirstStageWholeGeneric_finiteLengthSupport G H V w

/-- The original all-degree right whole coefficient has the original G,H weight. -/
theorem actualWholeGenericCoefficient :
    F.rightFirstStageWholeTorGenericCoefficient G H V w =
      G.incidenceTorCoefficient (S := Spec (.of k)) H (F.rightFirstStageWholeGenericPair G H V w) *
        F.rightFirstStageWholeGenericFiberMultiplicity G H V w :=
  F.rightFirstStageWholeTorGenericCoefficient_eq_pair_mul G H V w

/-- A later original finite-image degree factor stays attached to the same pair
point; this consumer makes no degree constancy or injectivity assumption. -/
theorem actualGenericCoefficientWithPairResidueDegree :
    F.rightFirstStageWholeTorGenericCoefficient G H V w *
        ((G.incidenceMap H).residueDegree (F.rightFirstStageWholeGenericPair G H V w).1 : ℤ) =
      (G.incidenceTorCoefficient (S := Spec (.of k)) H
          (F.rightFirstStageWholeGenericPair G H V w) *
        ((G.incidenceMap H).residueDegree (F.rightFirstStageWholeGenericPair G H V w).1 : ℤ)) *
          F.rightFirstStageWholeGenericFiberMultiplicity G H V w := by
  rw [F.rightFirstStageWholeTorGenericCoefficient_eq_pair_mul G H V w]
  ring

omit w in
/-- The full actual integral cycle keeps every whole-open generic branch,
with its own original G,H coefficient and unreduced exterior multiplicity. -/
theorem actualWholeGenericCycle :
    F.rightFirstStageWholeTorGenericCycle G H V =
      IntegralCycle.ofGenericCoefficients (F.rightFirstStageWholeOpen G H V)
        (fun w => G.incidenceTorCoefficient (S := Spec (.of k)) H
          (F.rightFirstStageWholeGenericPair G H V w) *
          F.rightFirstStageWholeGenericFiberMultiplicity G H V w) :=
  F.rightFirstStageWholeTorGenericCycle_eq_pair_mul G H V

end MotivicTest.RightWholeFiberTorGeneric
