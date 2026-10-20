/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.BaseChange.ComponentDecomposition

public import Motivic.Aglib.AlgebraicGeometry.Cycles.BaseChange.ClosedFiber
public import Motivic.Aglib.AlgebraicGeometry.Cycles.Fundamental.Invariance
public import Motivic.Aglib.AlgebraicGeometry.Cycles.GenericFinitePushforward
public import Motivic.Aglib.AlgebraicGeometry.Stalk.Generic.Points
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Intersection.WholeFiberTorGeneric

/-!
# The actual whole-open Tor cycle and its component exteriors

Restrict the unreduced exterior of every original reduced component support to
an actual open of the whole exterior. Their closed immersions partition the
whole-open generic points. The original component index is recovered by the
flat exterior projection, before any finite image is taken.

Generic preservation of these particular support immersions is proved, not
assumed: an ambient generization projects to the same original generic point,
lifts through the Cartesian support square, and then equals the given point
by genericity and the embedding's reflection of specialization. No normality,
separability, unique tensor branch, or generic preservation of arbitrary finite
maps is used.

The actual ambient closed-fiber quotient and the actual open support stalk are
compared using the original immersion and open-stalk maps. The full regular
stalk length is retained. A finite reindexing then identifies the EXISTING
whole first-stage Tor cycle with the restricted Tor-weighted component sum.
This stops before finite-image/open-restriction compatibility, the remaining
diagonal, or identification with an iterated incidence pairing.

Validation scope and recorded evidence are maintained in
`docs/VERIFICATION.md`.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

universe u


namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme

open _root_.AlgebraicGeometry.Scheme.Cycles.BaseChange.ComponentDecomposition

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)
  (V : (F.leftIntermediateImageProduct G H).affineOpens)

local instance wholeExterior_factorFlat : Flat (H.projection ≫ Z.hom) := by
  let : Subsingleton (Spec (.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  let : IsIntegral (Spec (.of k)) := inferInstance
  exact Flat.instOfSubsingletonCarrierCarrierCommRingCatOfIsIntegral
    (Y := Spec (.of k)) (H.projection ≫ Z.hom)

/-- Restrict the original pair component exterior to the actual whole inverse-image open. -/
abbrev firstStageComponentExteriorOpen (z : genericPoints (F.incidence G)) :=
  componentOpen (F.incidenceTarget G ≫ Z.hom) (H.projection ≫ Z.hom)
    ((F.leftIntermediateImageMap G H) ⁻¹ᵁ V) z

/-- Its literal closed immersion into the existing whole-open Tor coefficient scheme. -/
abbrev firstStageComponentExteriorInclusion (z : genericPoints (F.incidence G)) :
    F.firstStageComponentExteriorOpen G H V z ⟶ F.firstStageWholeOpen G H V :=
  componentInclusion (F.incidenceTarget G ≫ Z.hom) (H.projection ≫ Z.hom)
    ((F.leftIntermediateImageMap G H) ⁻¹ᵁ V) z

/-- The whole-open generic partition is by original pair-incidence generics,
with every exterior branch and no image-component quotienting. -/
def firstStageComponentExteriorGenericPartition :
    (Σ z : genericPoints (F.incidence G),
      genericPoints (F.firstStageComponentExteriorOpen G H V z)) ≃
        genericPoints (F.firstStageWholeOpen G H V) :=
  genericPartition (F.incidenceTarget G ≫ Z.hom) (H.projection ≫ Z.hom)
    ((F.leftIntermediateImageMap G H) ⁻¹ᵁ V)

/-- The partition inverse is the EXISTING original pair label of the whole Tor API. -/
theorem firstStageComponentExteriorGenericPartition_symm_fst
    (w : genericPoints (F.firstStageWholeOpen G H V)) :
    ((F.firstStageComponentExteriorGenericPartition G H V).symm w).1 =
      F.firstStageWholeGenericPair G H V w :=
  genericPartition_symm_fst _ _ _ w

/-- Forward partitioning recovers the same original pair label, before any image map. -/
theorem firstStageWholeGenericPair_component
    (z : genericPoints (F.incidence G))
    (w : genericPoints (F.firstStageComponentExteriorOpen G H V z)) :
    F.firstStageWholeGenericPair G H V
        (F.firstStageComponentExteriorGenericPartition G H V ⟨z, w⟩) = z :=
  componentGeneric_genericInclusion _ _ _ z w

/-- The genuine whole-Tor closed-fiber multiplicity is the full multiplicity
of the corresponding actual restricted component-exterior stalk. -/
theorem firstStageWholeGenericFiberMultiplicity_component
    (z : genericPoints (F.incidence G))
    (w : genericPoints (F.firstStageComponentExteriorOpen G H V z)) :
    F.firstStageWholeGenericFiberMultiplicity G H V
        (F.firstStageComponentExteriorGenericPartition G H V ⟨z, w⟩) =
      (genericMultiplicity w : ℤ) :=
  closedFiberMultiplicity_genericInclusion _ _ _ z w

/-- The genuine all-degree whole-Tor sheaf coefficient equals the original
pair Tor weight times the full restricted exterior generic-stalk multiplicity. -/
theorem firstStageWholeTorGenericCoefficient_component
    (z : genericPoints (F.incidence G))
    (w : genericPoints (F.firstStageComponentExteriorOpen G H V z)) :
    F.firstStageWholeTorGenericCoefficient G H V
        (F.firstStageComponentExteriorGenericPartition G H V ⟨z, w⟩) =
      F.incidenceTorCoefficient (S := Spec (.of k)) G z * (genericMultiplicity w : ℤ) := by
  rw [F.firstStageWholeTorGenericCoefficient_eq_pair_mul G H V,
    F.firstStageWholeGenericPair_component G H V,
    F.firstStageWholeGenericFiberMultiplicity_component G H V]

/-- The existing whole first-stage Tor cycle is IDENTIFIED with the actual
restricted component-fundamental-cycle sum. This is a source cycle identity,
not an identification of an iterated incidence pairing. -/
theorem firstStageWholeTorGenericCycle_eq_componentExterior_sum :
    letI := IntegralCycle.genericPointFintype (F.incidence G)
    F.firstStageWholeTorGenericCycle G H V =
      ∑ z : genericPoints (F.incidence G),
        F.incidenceTorCoefficient (S := Spec (.of k)) G z •
          IntegralCycle.finitePushforward (F.firstStageComponentExteriorInclusion G H V z)
            (fundamentalCycle (F.firstStageComponentExteriorOpen G H V z)) := by
  rw [F.firstStageWholeTorGenericCycle_eq_pair_mul G H V]
  exact ofGenericCoefficients_eq_component_sum _ _ _
    (F.incidenceTorCoefficient (S := Spec (.of k)) G)

end Motivic.FiniteCorrespondenceGenerator
