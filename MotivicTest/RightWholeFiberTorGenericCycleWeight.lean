/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.RightWholeFiberTorGenericCycleWeight

/-!
# Actual right generic target weight consumers

These consumers use an arbitrary field and the actual smooth correspondences,
existing right affine V, original target stalk, and original target-generic index.
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

namespace Motivic.MotivicTest.RightWholeFiberTorGenericCycleWeight
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Products

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

/-- The smooth-site base is the original separated affine scheme Spec k. -/
local instance actualRightGenericWeightBaseIsSeparated :
    ((Functor.fromPUnit (Spec (.of k))).obj X.right).IsSeparated :=
  inferInstanceAs (Spec (.of k)).IsSeparated

local instance : IsLocallyNoetherian
    (correspondenceSixfoldAmbient X.hom Y.hom Z.hom W.hom) :=
  isLocallyNoetherian_correspondenceSixfoldAmbient (S := Spec (.of k))
    X.hom Y.hom Z.hom W.hom

/-- The actual right target is locally finite type over the closed G,H image
inside the smooth Y-times-W product. No flatness of F over Y is required. -/
local instance : IsLocallyNoetherian (F.rightIntermediateImageProduct G H) := by
  have : IsLocallyNoetherian Y.left :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := Spec (.of k)) Y.hom
  have : IsLocallyNoetherian (pullback Y.hom W.hom) :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := Y.left) (pullback.fst Y.hom W.hom)
  have : IsLocallyNoetherian (G.incidenceMap H).image :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := pullback Y.hom W.hom)
      (G.incidenceMap H).imageι
  exact LocallyOfFiniteType.isLocallyNoetherian (Y := (G.incidenceMap H).image)
    (pullback.snd (F.targetProjection ≫ Y.hom)
      ((G.incidenceMap H).imageι ≫ pullback.fst Y.hom W.hom ≫ Y.hom))

variable (V : (F.rightIntermediateImageProduct G H).affineOpens)
  (p : Spec Γ(F.rightIntermediateImageProduct G H, V))
  (q : {q : genericPoints (F.rightIntermediateImageProduct G H) // q.1 ⤳ V.2.fromSpec p})

/-- The genuine fixed-support weight is the coefficient of the ACTUAL pushed
existing whole Tor cycle, evaluated at the original generic point in the same V. -/
theorem actualTargetGenericWeight :
    F.rightFirstStagePushforwardGenericEuler G H V p
        ((F.rightFirstStageTargetGenericEquiv G H V p).symm q) =
      IntegralCycle.toPoints
        (IntegralCycle.finitePushforward (F.rightIntermediateImageMap G H ∣_ V)
          (F.rightFirstStageWholeTorGenericCycle G H V))
        ⟨q.1.1, F.rightFirstStagePushforwardGeneric_mem G H V p q⟩ :=
  F.rightFirstStagePushforwardGenericEuler_eq_finitePushforward_coefficient G H V p q

/-- Every colliding whole-open generic branch contributes its own signed Tor
weight times its ORIGINAL finite-map residue degree. No residue degree is set to one. -/
theorem actualTargetGenericWeight_allBranches :
    F.rightFirstStagePushforwardGenericEuler G H V p
        ((F.rightFirstStageTargetGenericEquiv G H V p).symm q) =
      ∑ᶠ w : {w : genericPoints (F.rightFirstStageWholeOpen G H V) //
        (F.rightIntermediateImageMap G H ∣_ V) w.1 =
          (⟨q.1.1, F.rightFirstStagePushforwardGeneric_mem G H V p q⟩ : V.1.toScheme)},
        F.rightFirstStageWholeTorGenericCoefficient G H V w.1 *
          ((F.rightIntermediateImageMap G H).residueDegree w.1.1.1 : ℤ) := by
  rw [actualTargetGenericWeight,
    F.rightFirstStageWholeTorGenericCycle_pushforward_coefficient G H V]
  apply finsum_congr
  intro w
  rw [F.rightFirstStageWholeOpen_residueDegree G H V w.1.1]

/-- A genuinely empty ORIGINAL finite fiber forces the attached target weight
to vanish; no default value for an unsupported infinite outer sum is used. -/
theorem actualTargetGenericWeight_emptyFiber
    (hempty : ∀ x : F.rightIntermediateSupportProduct G H,
      F.rightIntermediateImageMap G H x ≠ q.1.1) :
    F.rightFirstStagePushforwardGenericEuler G H V p
      ((F.rightFirstStageTargetGenericEquiv G H V p).symm q) = 0 := by
  rw [actualTargetGenericWeight_allBranches]
  apply finsum_eq_zero_of_forall_eq_zero
  intro w
  exact (hempty w.1.1.1
    ((morphismRestrict_base_coe (F.rightIntermediateImageMap G H) V.1 w.1.1).symm.trans
      (congrArg Subtype.val w.2))).elim

/-- Arbitrary signed multiples attach through the actual additive cycle maps.
This includes zero and negative cycle weights and preserves every collision. -/
theorem actualTargetGenericWeight_signedMultiple (m : ℤ) :
    m * F.rightFirstStagePushforwardGenericEuler G H V p
        ((F.rightFirstStageTargetGenericEquiv G H V p).symm q) =
      IntegralCycle.toPoints
        (IntegralCycle.finitePushforward (F.rightIntermediateImageMap G H ∣_ V)
          (m • F.rightFirstStageWholeTorGenericCycle G H V))
        ⟨q.1.1, F.rightFirstStagePushforwardGeneric_mem G H V p q⟩ := by
  let y : V.1.toScheme := ⟨q.1.1, F.rightFirstStagePushforwardGeneric_mem G H V p q⟩
  let coefficient : IntegralCycle (F.rightFirstStageWholeOpen G H V) →+ ℤ :=
    (Finsupp.applyAddHom y).comp
      ((IntegralCycle.toPoints (X := V.1.toScheme)).comp
        (IntegralCycle.finitePushforward (F.rightIntermediateImageMap G H ∣_ V)))
  have hscaled := (map_zsmul coefficient m (F.rightFirstStageWholeTorGenericCycle G H V)).trans
    (Int.zsmul_eq_mul m (coefficient (F.rightFirstStageWholeTorGenericCycle G H V)))
  exact (congrArg (fun a : ℤ => m * a)
    (actualTargetGenericWeight F G H V p q)).trans hscaled.symm

/-- The negative actual whole Tor cycle has exactly the negative attached
original target weight, without assuming any sign of the unscaled Tor Euler. -/
theorem actualTargetGenericWeight_negative :
    -F.rightFirstStagePushforwardGenericEuler G H V p
        ((F.rightFirstStageTargetGenericEquiv G H V p).symm q) =
      IntegralCycle.toPoints
        (IntegralCycle.finitePushforward (F.rightIntermediateImageMap G H ∣_ V)
          (-F.rightFirstStageWholeTorGenericCycle G H V))
        ⟨q.1.1, F.rightFirstStagePushforwardGeneric_mem G H V p q⟩ := by
  simpa only [neg_one_mul, neg_one_zsmul] using
    actualTargetGenericWeight_signedMultiple F G H V p q (-1)

/-- The support evidence is proved on the actual finite whole algebra, before
outer-degree exchange, and is independent of any asserted cycle identity. -/
theorem actualGenericWholeFamily_finiteLengthSupport
    (r : Spec Γ(F.rightIntermediateImageProduct G H, V))
    (hr : V.2.fromSpec r ∈ genericPoints (F.rightIntermediateImageProduct G H)) :
    _root_.HomologicalComplex.ModuleLengthEuler.FiniteLengthSupport
        (F.rightFirstStageWholeLocalizedCoefficient G H V r) :=
  F.rightFirstStageWholeAtGeneric_finiteLengthSupport G H V r hr

end Motivic.MotivicTest.RightWholeFiberTorGenericCycleWeight
