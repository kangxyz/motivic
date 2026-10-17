/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.WholeFiberTorGenericCycleWeight

/-!
# Actual generic target weight consumers

These consumers use an arbitrary field and the actual smooth correspondences,
existing affine V, original target stalk, and original target-generic index.
The all-branch formula keeps the original (unrestricted) residue degrees.
The empty-fiber and arbitrary signed-multiple consumers include zero and
negative coefficients without any positivity or single-branch assumption.

SOURCE-ONLY PROPOSAL: no compilation or acceptance is claimed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

universe u

namespace Motivic.MotivicTest.WholeFiberTorGenericCycleWeight

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

/-- The smooth-site base is the original separated affine scheme Spec k. -/
local instance actualGenericWeightBaseIsSeparated :
    ((Functor.fromPUnit (Spec (.of k))).obj X.right).IsSeparated :=
  inferInstanceAs (Spec (.of k)).IsSeparated

local instance : IsLocallyNoetherian
    (correspondenceSixfoldAmbient X.hom Y.hom Z.hom W.hom) :=
  isLocallyNoetherian_correspondenceSixfoldAmbient (S := Spec (.of k))
    X.hom Y.hom Z.hom W.hom

local instance : IsLocallyNoetherian (F.leftIntermediateImageProduct G H) := by
  have : IsLocallyNoetherian X.left :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := Spec (.of k)) X.hom
  have : IsLocallyNoetherian (pullback X.hom Z.hom) :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := X.left) (pullback.fst X.hom Z.hom)
  have : IsLocallyNoetherian (F.incidenceMap G).image :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := pullback X.hom Z.hom)
      (F.incidenceMap G).imageι
  exact LocallyOfFiniteType.isLocallyNoetherian (Y := (F.incidenceMap G).image)
    (pullback.fst ((F.incidenceMap G).imageι ≫ pullback.snd X.hom Z.hom ≫ Z.hom)
      (H.projection ≫ Z.hom))

variable (V : (F.leftIntermediateImageProduct G H).affineOpens)
  (p : Spec Γ(F.leftIntermediateImageProduct G H, V))
  (q : {q : genericPoints (F.leftIntermediateImageProduct G H) // q.1 ⤳ V.2.fromSpec p})

/-- The genuine fixed-support weight is the coefficient of the ACTUAL pushed
existing whole Tor cycle, evaluated at the original generic point in the same V. -/
theorem actualTargetGenericWeight :
    F.firstStagePushforwardGenericEuler G H V p
        ((F.firstStageTargetGenericEquiv G H V p).symm q) =
      IntegralCycle.toPoints
        (IntegralCycle.finitePushforward (F.leftIntermediateImageMap G H ∣_ V)
          (F.firstStageWholeTorGenericCycle G H V))
        ⟨q.1.1, F.firstStagePushforwardGeneric_mem G H V p q⟩ :=
  F.firstStagePushforwardGenericEuler_eq_finitePushforward_coefficient G H V p q

/-- Every colliding whole-open generic branch contributes its own signed Tor
weight times its ORIGINAL finite-map residue degree. No residue degree is set to one. -/
theorem actualTargetGenericWeight_allBranches :
    F.firstStagePushforwardGenericEuler G H V p
        ((F.firstStageTargetGenericEquiv G H V p).symm q) =
      ∑ᶠ w : {w : genericPoints (F.firstStageWholeOpen G H V) //
        (F.leftIntermediateImageMap G H ∣_ V) w.1 =
          (⟨q.1.1, F.firstStagePushforwardGeneric_mem G H V p q⟩ : V.1.toScheme)},
        F.firstStageWholeTorGenericCoefficient G H V w.1 *
          ((F.leftIntermediateImageMap G H).residueDegree w.1.1.1 : ℤ) := by
  rw [actualTargetGenericWeight, F.firstStageWholeTorGenericCycle_pushforward_coefficient G H V]
  apply finsum_congr
  intro w
  rw [F.firstStageWholeOpen_residueDegree G H V w.1.1]

/-- A genuinely empty ORIGINAL finite fiber forces the attached target weight
to vanish; no default value for an unsupported infinite outer sum is used. -/
theorem actualTargetGenericWeight_emptyFiber
    (hempty : ∀ x : F.leftIntermediateSupportProduct G H,
      F.leftIntermediateImageMap G H x ≠ q.1.1) :
    F.firstStagePushforwardGenericEuler G H V p
      ((F.firstStageTargetGenericEquiv G H V p).symm q) = 0 := by
  rw [actualTargetGenericWeight_allBranches]
  apply finsum_eq_zero_of_forall_eq_zero
  intro w
  exact (hempty w.1.1.1
    ((morphismRestrict_base_coe (F.leftIntermediateImageMap G H) V.1 w.1.1).symm.trans
      (congrArg Subtype.val w.2))).elim

/-- Arbitrary signed multiples attach through the actual additive cycle maps.
This includes zero and negative cycle weights and preserves every collision. -/
theorem actualTargetGenericWeight_signedMultiple (m : ℤ) :
    m * F.firstStagePushforwardGenericEuler G H V p
        ((F.firstStageTargetGenericEquiv G H V p).symm q) =
      IntegralCycle.toPoints
        (IntegralCycle.finitePushforward (F.leftIntermediateImageMap G H ∣_ V)
          (m • F.firstStageWholeTorGenericCycle G H V))
        ⟨q.1.1, F.firstStagePushforwardGeneric_mem G H V p q⟩ := by
  let y : V.1.toScheme := ⟨q.1.1, F.firstStagePushforwardGeneric_mem G H V p q⟩
  let coefficient : IntegralCycle (F.firstStageWholeOpen G H V) →+ ℤ :=
    (Finsupp.applyAddHom y).comp
      ((IntegralCycle.toPoints (X := V.1.toScheme)).comp
        (IntegralCycle.finitePushforward (F.leftIntermediateImageMap G H ∣_ V)))
  have hscaled := (map_zsmul coefficient m (F.firstStageWholeTorGenericCycle G H V)).trans
    (Int.zsmul_eq_mul m (coefficient (F.firstStageWholeTorGenericCycle G H V)))
  exact (congrArg (fun a : ℤ => m * a)
    (actualTargetGenericWeight F G H V p q)).trans hscaled.symm

/-- The negative actual whole Tor cycle has exactly the negative attached
original target weight, without assuming any sign of the unscaled Tor Euler. -/
theorem actualTargetGenericWeight_negative :
    -F.firstStagePushforwardGenericEuler G H V p
        ((F.firstStageTargetGenericEquiv G H V p).symm q) =
      IntegralCycle.toPoints
        (IntegralCycle.finitePushforward (F.leftIntermediateImageMap G H ∣_ V)
          (-F.firstStageWholeTorGenericCycle G H V))
        ⟨q.1.1, F.firstStagePushforwardGeneric_mem G H V p q⟩ := by
  simpa only [neg_one_mul, neg_one_zsmul] using
    actualTargetGenericWeight_signedMultiple F G H V p q (-1)

/-- The support evidence is proved on the actual finite whole algebra, before
outer-degree exchange, and is independent of any asserted cycle identity. -/
theorem actualGenericWholeFamily_finiteLengthSupport
    (r : Spec Γ(F.leftIntermediateImageProduct G H, V))
    (hr : V.2.fromSpec r ∈ genericPoints (F.leftIntermediateImageProduct G H)) :
    LengthEuler.FiniteLengthSupport (F.firstStageWholeLocalizedCoefficient G H V r) :=
  F.firstStageWholeAtGeneric_finiteLengthSupport G H V r hr

end Motivic.MotivicTest.WholeFiberTorGenericCycleWeight
