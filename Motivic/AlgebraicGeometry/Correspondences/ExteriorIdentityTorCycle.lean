/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.ExteriorIdentityTorLengthComparison
public import Motivic.AlgebraicGeometry.Cycles.RightWholeFiberTorExteriorDecomposition

/-!
# The actual exterior incidence Tor cycle

The actual generic Tor coefficient cycle is the transported signed sum of the
whole original component exteriors. The full local closed fibers and every
original Tor coefficient are retained. The proof applies the existing generic
component decomposition to the top open and removes the open wrappers by their
actual isomorphisms.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

universe u

namespace Motivic.FiniteCorrespondenceGenerator

open WholeFiberTorExteriorDecomposition RightWholeFiberTorExteriorDecomposition

variable {k : Type u} [Field k] {X Y Z : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom]

local instance exteriorTorCycle_productNoetherian :
    IsNoetherian (A.exteriorIncidenceSupport B T) :=
  isNoetherian_of_finiteType (pullback.fst (A.incidenceSource B ≫ X.hom) T.hom)

local instance exteriorTorCycle_topNoetherian :
    IsNoetherian (⊤ : (A.exteriorIncidenceSupport B T).Opens).toScheme :=
  isNoetherian_of_finiteType (Scheme.topIso (A.exteriorIncidenceSupport B T)).hom

local instance exteriorTorCycle_componentNoetherian (x : genericPoints (A.incidence B)) :
    IsNoetherian (componentExterior (A.incidenceSource B ≫ X.hom) T.hom x) :=
  isNoetherian_of_finiteType
    (componentExteriorInclusion (A.incidenceSource B ≫ X.hom) T.hom x)

/-- The incidence isomorphism preserves the literal old incidence projection. -/
@[reassoc (attr := simp)]
theorem exteriorIdentityIncidenceIso_hom_originalCoordinate :
    (A.exteriorIdentityIncidenceIso B T).hom ≫ A.exteriorIncidenceOriginalCoordinate B T =
      pullback.fst (A.incidenceSource B ≫ X.hom) T.hom := by
  rw [← A.exteriorIncidenceFromGenerators_fst B T]
  change (A.exteriorIdentityIncidenceIso B T).hom ≫
    (A.exteriorIdentityIncidenceIso B T).inv ≫ _ = _
  simp only [Iso.hom_inv_id_assoc]

/-- The original projection stalk maps agree as arrows through the actual incidence isomorphism. -/
def exteriorIncidenceProjectionStalkArrowIso (w : A.exteriorIncidenceSupport B T) :
    Arrow.mk ((A.exteriorIncidenceOriginalCoordinate B T).stalkMap
      ((A.exteriorIdentityIncidenceIso B T).hom w)) ≅
    Arrow.mk ((pullback.fst (A.incidenceSource B ≫ X.hom) T.hom).stalkMap w) :=
  Arrow.isoMk
    ((A.incidence B).presheaf.stalkCongr (.of_eq (congrArg
      (fun f : A.exteriorIncidenceSupport B T ⟶ A.incidence B => f w)
      (A.exteriorIdentityIncidenceIso_hom_originalCoordinate B T))))
    (asIso ((A.exteriorIdentityIncidenceIso B T).hom.stalkMap w)) (by
      dsimp only [Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom, asIso_hom]
      simpa only [Scheme.Hom.stalkMap_comp] using
        (Scheme.Hom.stalkMap_congr_hom
          ((A.exteriorIdentityIncidenceIso B T).hom ≫ A.exteriorIncidenceOriginalCoordinate B T)
          (pullback.fst (A.incidenceSource B ≫ X.hom) T.hom)
          (A.exteriorIdentityIncidenceIso_hom_originalCoordinate B T) w).symm)

/-- The top-open generic retains precisely its original incidence label. -/
private theorem exteriorIncidenceTopGeneric_original
    (w : genericPoints (⊤ : (A.exteriorIncidenceSupport B T).Opens).toScheme) :
    A.exteriorIncidenceOriginalGeneric B T
      (mapGenericPoint
        ((Scheme.topIso (A.exteriorIncidenceSupport B T)).hom ≫
          (A.exteriorIdentityIncidenceIso B T).hom) w) =
    componentGeneric (A.incidenceSource B ≫ X.hom) T.hom ⊤ w := by
  apply Subtype.ext
  exact congrArg (fun f : A.exteriorIncidenceSupport B T ⟶ A.incidence B => f w.1.1)
    (A.exteriorIdentityIncidenceIso_hom_originalCoordinate B T)

/-- The actual incidence fiber multiplicity is the whole decomposition fiber multiplicity. -/
private theorem exteriorIncidenceTopGeneric_fiber
    (w : genericPoints (⊤ : (A.exteriorIncidenceSupport B T).Opens).toScheme) :
    A.exteriorIncidenceFiberMultiplicity B T
      (mapGenericPoint
        ((Scheme.topIso (A.exteriorIncidenceSupport B T)).hom ≫
          (A.exteriorIdentityIncidenceIso B T).hom) w) =
    closedFiberMultiplicity (A.incidenceSource B ≫ X.hom) T.hom ⊤ w := by
  unfold exteriorIncidenceFiberMultiplicity closedFiberMultiplicity LengthEuler.integerLength
  exact congrArg (fun n : ℕ∞ => (n.toNat : ℤ))
    (closedFiberArrow_length (A.exteriorIncidenceProjectionStalkArrowIso B T w.1.1))

omit [GeometricallyIntegral T.hom] in
/-- Removing the top-open wrappers keeps the whole component fundamental cycle. -/
private theorem exteriorIncidenceTop_component
    (x : genericPoints (A.incidence B)) :
    IntegralCycle.finitePushforward (Scheme.topIso (A.exteriorIncidenceSupport B T)).hom
      (IntegralCycle.finitePushforward
        (componentInclusion (A.incidenceSource B ≫ X.hom) T.hom ⊤ x)
        (fundamentalCycle (componentOpen (A.incidenceSource B ≫ X.hom) T.hom ⊤ x))) =
    IntegralCycle.finitePushforward
      (componentExteriorInclusion (A.incidenceSource B ≫ X.hom) T.hom x)
      (fundamentalCycle (componentExterior (A.incidenceSource B ≫ X.hom) T.hom x)) := by
  let b := componentExteriorInclusion (A.incidenceSource B ≫ X.hom) T.hom x
  have : IsIso (b ⁻¹ᵁ (⊤ : (A.exteriorIncidenceSupport B T).Opens)).ι := by
    rw [Scheme.Hom.preimage_top]
    exact (Scheme.topIso _).isIso_hom
  have hmap :
      componentInclusion (A.incidenceSource B ≫ X.hom) T.hom ⊤ x ≫
          (Scheme.topIso (A.exteriorIncidenceSupport B T)).hom =
        (b ⁻¹ᵁ (⊤ : (A.exteriorIncidenceSupport B T).Opens)).ι ≫ b :=
    componentInclusion_ambient (A.incidenceSource B ≫ X.hom) T.hom ⊤ x
  have hcongr {D E : Scheme.{u}} (f g : D ⟶ E) (hf : IsFinite f) (hg : IsFinite g)
      (h : f = g) (c : IntegralCycle D) :
      @IntegralCycle.finitePushforward D E f hf c =
        @IntegralCycle.finitePushforward D E g hg c := by
    cases h
    rfl
  rw [← AddMonoidHom.comp_apply, ← IntegralCycle.finitePushforward_comp]
  refine (hcongr _ _ inferInstance inferInstance hmap _).trans ?_
  rw [IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply,
    finitePushforward_fundamentalCycle]

/-- The actual exterior incidence Tor cycle is the transported signed sum of
all original component exteriors, with their complete fundamental multiplicities. -/
theorem exteriorIncidenceTorCycle_eq_component_sum :
    IntegralCycle.ofGenericCoefficients
      ((A.exteriorIdentityGenerator T).incidence (B.exteriorIdentityGenerator T))
      ((A.exteriorIdentityGenerator T).incidenceTorCoefficient (S := Spec (.of k))
        (B.exteriorIdentityGenerator T)) =
    letI := IntegralCycle.genericPointFintype (A.incidence B)
    IntegralCycle.finitePushforward (A.exteriorIdentityIncidenceIso B T).hom
      (∑ x : genericPoints (A.incidence B),
        A.incidenceTorCoefficient (S := Spec (.of k)) B x •
          IntegralCycle.finitePushforward
            (componentExteriorInclusion (A.incidenceSource B ≫ X.hom) T.hom x)
            (fundamentalCycle (componentExterior (A.incidenceSource B ≫ X.hom) T.hom x))) := by
  classical
  let := IntegralCycle.genericPointFintype (A.incidence B)
  let p := A.incidenceSource B ≫ X.hom
  let c := A.incidenceTorCoefficient (S := Spec (.of k)) B
  have hc := finitePushforward_genericCoefficients_iso
    ((Scheme.topIso (A.exteriorIncidenceSupport B T)).hom ≫
      (A.exteriorIdentityIncidenceIso B T).hom)
    (fun w => c (componentGeneric p T.hom ⊤ w) * closedFiberMultiplicity p T.hom ⊤ w)
    ((A.exteriorIdentityGenerator T).incidenceTorCoefficient (S := Spec (.of k))
      (B.exteriorIdentityGenerator T)) (fun w => by
        rw [A.exteriorIncidenceTorCoefficient_eq B T,
          A.exteriorIncidenceTopGeneric_original B T,
          A.exteriorIncidenceTopGeneric_fiber B T])
  rw [← hc, ofGenericCoefficients_eq_component_sum,
    IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply]
  apply congrArg (IntegralCycle.finitePushforward (A.exteriorIdentityIncidenceIso B T).hom)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [map_zsmul, A.exteriorIncidenceTop_component B T x]

end Motivic.FiniteCorrespondenceGenerator
