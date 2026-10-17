/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.ExteriorIdentityComponentPushforward
public import Motivic.AlgebraicGeometry.Correspondences.ExteriorIdentityTorCycle
public import Motivic.AlgebraicGeometry.Correspondences.SimplexExterior

/-!
# Exterior identity preserves the actual correspondence composition

The actual generic Tor coefficients retain their whole local closed-fiber lengths.
The whole-fiber component decomposition and the finite component pushforward then
retain the original residue degrees. Additivity extends the resulting generator
identity to arbitrary signed finite correspondences.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

universe u

namespace Motivic

namespace FiniteCorrespondenceGenerator

variable {k : Type u} [Field k] {X Y Z : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom]

/-- Exterior extension preserves every actual Tor and residue-degree contribution. -/
theorem exteriorIdentity_incidenceTorCorrespondence :
    FiniteCorrespondence.exteriorIdentity (X := X) (Y := Z) T
        (A.incidenceTorCorrespondence k B) =
      (A.exteriorIdentityGenerator T).incidenceTorCorrespondence k
        (B.exteriorIdentityGenerator T) := by
  classical
  let := IntegralCycle.genericPointFintype (A.incidence B)
  have hold :
      FiniteCorrespondence.exteriorIdentity (X := X) (Y := Z) T
          (A.incidenceTorCorrespondence k B) =
        ∑ x : genericPoints (A.incidence B),
          (A.incidenceTorCoefficient (S := Spec (.of k)) B x *
            ((A.incidenceMap B).residueDegree x.1 : ℤ)) •
            ((A.smoothIncidenceComponentGenerator k B x).exteriorIdentityGenerator T).cycle := by
    rw [incidenceTorCorrespondence, incidenceCycleAssembly_eq_sum, map_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [FiniteCorrespondence.exteriorIdentity_single]
    simp [FiniteCorrespondenceGenerator.cycle]
  apply FiniteCorrespondence.toIntegralCycle_injective
  symm
  rw [toIntegralCycle_incidenceTorCorrespondence,
    exteriorIncidenceTorCycle_eq_component_sum,
    ← AddMonoidHom.comp_apply, ← IntegralCycle.finitePushforward_comp]
  change IntegralCycle.finitePushforward (A.exteriorIncidenceAmbientMap B T) _ = _
  rw [hold, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [map_zsmul, exteriorIncidence_finitePushforward_componentFundamentalCycle,
    map_zsmul, smul_smul]

end FiniteCorrespondenceGenerator

namespace FiniteCorrespondence

variable {k : Type u} [Field k] {X Y Z : SmoothSite (Spec (.of k))}
  (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom]

/-- Exterior extension commutes with the actual incidence Tor pairing on unit cycles. -/
theorem exteriorIdentity_incidenceTorPairing_cycle
    (A : FiniteCorrespondenceGenerator X.hom Y.hom)
    (B : FiniteCorrespondenceGenerator Y.hom Z.hom) :
    exteriorIdentity (X := X) (Y := Z) T
        (incidenceTorPairing k (X := X) (Y := Y) (Z := Z) A.cycle B.cycle) =
      incidenceTorPairing k (X := SmoothSite.product X T) (Y := SmoothSite.product Y T)
        (Z := SmoothSite.product Z T)
        (exteriorIdentity (X := X) (Y := Y) T A.cycle)
        (exteriorIdentity (X := Y) (Y := Z) T B.cycle) := by
  simp only [incidenceTorPairing_cycle, exteriorIdentity_cycle]
  exact A.exteriorIdentity_incidenceTorCorrespondence B T

/-- Every signed correspondence preserves actual composition under exterior extension. -/
theorem exteriorIdentity_incidenceTorPairing
    (α : FiniteCorrespondence X.hom Y.hom) (β : FiniteCorrespondence Y.hom Z.hom) :
    exteriorIdentity (X := X) (Y := Z) T
        (incidenceTorPairing k (X := X) (Y := Y) (Z := Z) α β) =
      incidenceTorPairing k (X := SmoothSite.product X T) (Y := SmoothSite.product Y T)
        (Z := SmoothSite.product Z T)
        (exteriorIdentity (X := X) (Y := Y) T α)
        (exteriorIdentity (X := Y) (Y := Z) T β) := by
  have hright (A : FiniteCorrespondenceGenerator X.hom Y.hom) :
      (exteriorIdentity (X := X) (Y := Z) T).comp
          (incidenceTorPairing k (X := X) (Y := Y) (Z := Z) A.cycle) =
        (incidenceTorPairing k (X := SmoothSite.product X T) (Y := SmoothSite.product Y T)
          (Z := SmoothSite.product Z T)
          (exteriorIdentity (X := X) (Y := Y) T A.cycle)).comp
          (exteriorIdentity (X := Y) (Y := Z) T) := by
    apply Finsupp.addHom_ext
    intro B n
    have hsingle : Finsupp.single B n = n • B.cycle := by
      simp [FiniteCorrespondenceGenerator.cycle]
    rw [hsingle, map_zsmul, map_zsmul]
    exact congrArg (fun γ => n • γ) (exteriorIdentity_incidenceTorPairing_cycle T A B)
  have hleft :
      (exteriorIdentity (X := X) (Y := Z) T).comp
          ((incidenceTorPairing k (X := X) (Y := Y) (Z := Z)).flip β) =
        ((incidenceTorPairing k (X := SmoothSite.product X T) (Y := SmoothSite.product Y T)
          (Z := SmoothSite.product Z T)).flip
          (exteriorIdentity (X := Y) (Y := Z) T β)).comp
          (exteriorIdentity (X := X) (Y := Y) T) := by
    apply Finsupp.addHom_ext
    intro A n
    have hsingle : Finsupp.single A n = n • A.cycle := by
      simp [FiniteCorrespondenceGenerator.cycle]
    rw [hsingle, map_zsmul, map_zsmul]
    exact congrArg (fun F => n • F β) (hright A)
  exact congrArg (fun F => F α) hleft

end FiniteCorrespondence

namespace Cor

variable {k : Type u} [Field k] {X Y Z : Cor k}

/-- The actual simplex exterior operation preserves all signed `Cor` compositions. -/
@[simp] theorem simplexExterior_comp (n : ℕ) (α : X ⟶ Y) (β : Y ⟶ Z) :
    simplexExterior n (α ≫ β) = simplexExterior n α ≫ simplexExterior n β :=
  FiniteCorrespondence.exteriorIdentity_incidenceTorPairing
    (AlgebraicSimplex.smoothSiteObj k n) α β

end Cor

end Motivic
