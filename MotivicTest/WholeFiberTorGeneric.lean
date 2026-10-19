/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Intersection.WholeFiberTorGeneric

/-!
# Original arbitrary-field whole Tor generic consumers

The consumers use the original smooth-site objects and actual whole finite
inverse image. They retain all Tor degrees, the unreduced incidence closed
fiber and every original pair generic point. Neither a coefficient comparison
nor a unit multiplicity is supplied as an input.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.AlgebraicGeometry.Scheme (IntegralCycle SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

namespace MotivicTest.WholeFiberTorGeneric

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)
  (V : (F.leftIntermediateImageProduct G H).affineOpens)
  (w : genericPoints (F.firstStageWholeOpen G H V))

/-- The actual whole-open generic point projects to a genuine pair-incidence generic. -/
theorem actualPairGenericPoint :
    F.leftExteriorPairProjection G H w.1.1 ∈ genericPoints (F.incidence G) :=
  (F.firstStageWholeGenericPair G H V w).2

/-- Every original sheaf stalk degree has the retained true exterior-fiber factor. -/
theorem actualDegreewiseWholeMultiplicity (n : ℕ) :
    Module.length ((F.firstStageWholeOpen G H V).presheaf.stalk w.1)
        (F.firstStageWholeGenericStalk G H V w n) =
      Module.length (F.incidenceAmbientStalk G (F.firstStageWholeGenericPair G H V w).1)
        (F.incidenceTor G (F.firstStageWholeGenericPair G H V w).1 n) *
          Module.length ((F.leftIntermediateSupportProduct G H).presheaf.stalk w.1.1)
            (F.leftExteriorClosedFiber G H w.1.1) :=
  F.firstStageWholeGeneric_length G H V w n

/-- Finite length is established for the original coefficient in all degrees. -/
theorem actualWholeFiniteLengthSupport :
    _root_.HomologicalComplex.ModuleLengthEuler.FiniteLengthSupport
        (F.firstStageWholeGenericStalk G H V w) :=
  F.firstStageWholeGeneric_finiteLengthSupport G H V w

/-- The original closed fiber remains its literal quotient by the source
maximal ideal under the original incidence-product projection. -/
theorem actualClosedFiberLength :
    Module.length ((F.leftIntermediateSupportProduct G H).presheaf.stalk w.1.1)
      (((F.leftIntermediateSupportProduct G H).presheaf.stalk w.1.1) ⧸
        (IsLocalRing.maximalIdeal
          ((F.incidence G).presheaf.stalk (F.leftExteriorPairProjection G H w.1.1))).map
            ((F.leftExteriorPairProjection G H).stalkMap w.1.1).hom) ≠ ⊤ :=
  F.firstStageWholeGenericFiber_length_ne_top G H V w

/-- The actual all-degree whole coefficient equals the already defined
candidate's original pair Tor coefficient times the genuine fiber multiplicity. -/
theorem actualWholeGenericCoefficient :
    F.firstStageWholeTorGenericCoefficient G H V w =
      F.incidenceTorCoefficient (S := Spec (.of k)) G (F.firstStageWholeGenericPair G H V w) *
        F.firstStageWholeGenericFiberMultiplicity G H V w :=
  F.firstStageWholeTorGenericCoefficient_eq_pair_mul G H V w

/-- Each original pair contribution keeps the same whole generic factor even
when subsequently weighted by its actual finite-image residue degree. -/
theorem actualGenericCoefficientWithPairResidueDegree :
    F.firstStageWholeTorGenericCoefficient G H V w *
        ((F.incidenceMap G).residueDegree (F.firstStageWholeGenericPair G H V w).1 : ℤ) =
      (F.incidenceTorCoefficient (S := Spec (.of k)) G (F.firstStageWholeGenericPair G H V w) *
        ((F.incidenceMap G).residueDegree (F.firstStageWholeGenericPair G H V w).1 : ℤ)) *
          F.firstStageWholeGenericFiberMultiplicity G H V w := by
  rw [F.firstStageWholeTorGenericCoefficient_eq_pair_mul G H V w]
  ring

omit w in
/-- The component cycle on the actual whole inverse image retains all original
components with their own pair coefficient and unreduced exterior multiplicity. -/
theorem actualWholeGenericCycle :
    F.firstStageWholeTorGenericCycle G H V =
      IntegralCycle.ofGenericCoefficients (F.firstStageWholeOpen G H V)
        (fun w => F.incidenceTorCoefficient (S := Spec (.of k)) G
          (F.firstStageWholeGenericPair G H V w) *
          F.firstStageWholeGenericFiberMultiplicity G H V w) :=
  F.firstStageWholeTorGenericCycle_eq_pair_mul G H V

end MotivicTest.WholeFiberTorGeneric
