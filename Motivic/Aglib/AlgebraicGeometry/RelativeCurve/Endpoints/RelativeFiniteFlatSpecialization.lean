/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Endpoints.PolynomialFiberCycleSpecialization
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeEndpointFiberGenerics

/-!
# Whole endpoint cycles of relative finite-flat families

For a finite-flat family over `X × A¹`, with `X` any smooth-site object,
the whole endpoint fundamental cycle is the weighted sum of the whole endpoint
fibers of the original reduced components. Weights are the original generic
local lengths. Smoothness supplies normal stalks componentwise, and flatness
is used only for the whole family. Both literal endpoint-fiber models are
provided. Current imports still depend on the project's cycle and relative
endpoint infrastructure.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram
open scoped BigOperators

universe u

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.SmoothSite

private theorem finitePushforward_congr {P Q : Scheme.{u}} (f g : P ⟶ Q)
    [IsFinite f] [IsFinite g] (h : f = g) (c : IntegralCycle P) :
    IntegralCycle.finitePushforward f c = IntegralCycle.finitePushforward g c := by
  cases h
  rfl

variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
  {P : Scheme.{u}} (f : P ⟶ relativeLine X.hom) [IsFinite f] [Flat f] (a : k)

local instance : IsNoetherian (relativeLine X.hom) :=
  inferInstanceAs (IsNoetherian (SmoothSite.product X (AffineLineField.line k)).left)

include f in
omit [Flat f] in
/-- The actual finite relative family is Noetherian over the smooth base. -/
theorem relativeFiniteFlat_isNoetherian : IsNoetherian P :=
  isNoetherian_of_finiteType f

/-- The literal parameter-fiber formula retains all original generic weights
and every component fiber's complete scheme structure. -/
theorem relativeFiniteFlat_parameter_fundamentalCycle_specialization :
    let : IsNoetherian P := relativeFiniteFlat_isNoetherian X f
    let := IntegralCycle.genericPointFintype P
    fundamentalCycle (FiniteFlatCurve.fiber (familyParameter X.hom f) a) =
      ∑ z : genericPoints P, (genericMultiplicity z : ℤ) •
        IntegralCycle.finitePushforward
          (FiniteFlatCurve.fiberMap (familyParameter X.hom f) a
            (RelativeFiniteFlat.componentInclusion z))
          (fundamentalCycle (FiniteFlatCurve.fiber
            (RelativeFiniteFlat.componentInclusion z ≫ familyParameter X.hom f) a)) := by
  let : IsNoetherian P := relativeFiniteFlat_isNoetherian X f
  apply FiniteFlatCurve.fundamentalCycle_specialization_of_generic_preservation
  exact componentFiberMap_mem_genericPoints_smooth X f a

local instance : IsNoetherian (pullback (endpoint X.hom a) f) :=
  haveI : IsNoetherian ((𝟭 Scheme).obj X.left) := inferInstanceAs (IsNoetherian X.left)
  isNoetherian_of_finiteType (pullback.fst (endpoint X.hom a) f)

local instance (z : genericPoints P) :
    IsNoetherian (pullback (endpoint X.hom a) (RelativeFiniteFlat.componentInclusion z ≫ f)) :=
  haveI : IsNoetherian ((𝟭 Scheme).obj X.left) := inferInstanceAs (IsNoetherian X.left)
  isNoetherian_of_finiteType
    (pullback.fst (endpoint X.hom a) (RelativeFiniteFlat.componentInclusion z ≫ f))

/-- The same weighted formula on the actual base change by `X → X × A¹`.
This is the whole relative endpoint, with neither the base nor the family
assumed integral or reduced. -/
theorem relativeFiniteFlat_fundamentalCycle_specialization :
    let : IsNoetherian P := relativeFiniteFlat_isNoetherian X f
    let := IntegralCycle.genericPointFintype P
    fundamentalCycle (pullback (endpoint X.hom a) f) =
      ∑ z : genericPoints P, (genericMultiplicity z : ℤ) •
        IntegralCycle.finitePushforward
          (RelativeFiniteFlat.componentBaseChangeMap f (endpoint X.hom a) z)
          (fundamentalCycle (pullback (endpoint X.hom a)
            (RelativeFiniteFlat.componentInclusion z ≫ f))) := by
  classical
  let : IsNoetherian P := relativeFiniteFlat_isNoetherian X f
  let := IntegralCycle.genericPointFintype P
  apply IntegralCycle.finitePushforward_injective_of_isClosedImmersion
    (relativeFiberIso X.hom f a).hom
  rw [finitePushforward_fundamentalCycle, map_sum]
  simp_rw [map_zsmul]
  rw [relativeFiniteFlat_parameter_fundamentalCycle_specialization X f a]
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  rw [← AddMonoidHom.comp_apply, ← IntegralCycle.finitePushforward_comp]
  rw [finitePushforward_congr _ _ (relativeFiberIso_componentMap X.hom f a z)]
  rw [IntegralCycle.finitePushforward_comp,
    AddMonoidHom.comp_apply,
    finitePushforward_fundamentalCycle (componentRelativeFiberIso X.hom f a z).hom]

end AlgebraicGeometry
