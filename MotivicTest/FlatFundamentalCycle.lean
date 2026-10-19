/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.ScalarExtension.FlatFundamentalCycle

/-!
# Consumers of the flat fundamental-cycle decomposition

The schemes may have nilpotents or disconnected components. The test morphism
is never required to be of finite type. The field-change test uses an actual
arbitrary field extension and proves Noetherianity from the original finite-type
structure maps, without a finite-type hypothesis on the extension itself.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.AlgebraicGeometry.Scheme (IntegralCycle fundamentalCycle genericMultiplicity
  isNoetherian_of_finiteType)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Cycles.BaseChange.ComponentDecomposition
open scoped BigOperators

universe u

namespace MotivicTest.FlatFundamentalCycle

/-- Arbitrary flat base change, without integrality, reducedness, connectedness,
or finite type for either structure map. -/
theorem arbitraryFlatBaseChange
    {P S T : Scheme.{u}} (p : P ⟶ S) (t : T ⟶ S)
    [Flat t] [IsNoetherian P] [IsNoetherian (pullback p t : Scheme.{u})] :
    letI := IntegralCycle.genericPointFintype P
    letI : ∀ z : genericPoints P, IsNoetherian (componentExterior p t z) :=
      fun z => isNoetherian_of_finiteType (componentExteriorInclusion p t z)
    fundamentalCycle (pullback p t) =
      ∑ z : genericPoints P, (genericMultiplicity z : ℤ) •
        IntegralCycle.finitePushforward (componentExteriorInclusion p t z)
          (fundamentalCycle (componentExterior p t z)) :=
  fundamentalCycle_pullback_eq_component_sum p t

/-- The product of two possibly nonreduced disconnected schemes retains the
full fundamental cycle of every pair product, rather than its reduction. -/
theorem possiblyNonreducedDisconnectedProduct
    {K : Type u} [Field K] {P T : Scheme.{u}}
    (p : P ⟶ Spec (.of K)) (t : T ⟶ Spec (.of K))
    [IsNoetherian P] [IsNoetherian T] [IsNoetherian (pullback p t : Scheme.{u})] :
    letI := IntegralCycle.genericPointFintype P
    letI := IntegralCycle.genericPointFintype T
    letI : ∀ a : genericPoints P, ∀ b : genericPoints T,
        IsNoetherian (componentPairExterior p t a b) :=
      fun a b => isNoetherian_of_finiteType (componentPairExteriorInclusion p t a b)
    fundamentalCycle (pullback p t) =
      ∑ a : genericPoints P, ∑ b : genericPoints T,
        ((genericMultiplicity a : ℤ) * (genericMultiplicity b : ℤ)) •
          IntegralCycle.finitePushforward (componentPairExteriorInclusion p t a b)
            (fundamentalCycle (componentPairExterior p t a b)) :=
  fundamentalCycle_product_eq_component_pair_sum p t

/-- A literal field-change product. The arbitrary extension may be inseparable
or transcendental, and neither original scheme is required to be reduced. -/
theorem arbitraryFieldChangeProduct
    {K L : Type u} [Field K] [Field L] [Algebra K L] {P T : Scheme.{u}}
    (p : P ⟶ Spec (.of K)) (t : T ⟶ Spec (.of K)) [LocallyOfFiniteType p] [QuasiCompact p]
    [LocallyOfFiniteType t] [QuasiCompact t] :
    let e := Spec.map (CommRingCat.ofHom (algebraMap K L))
    let pL := pullback.snd p e
    let tL := pullback.snd t e
    letI : IsNoetherian (pullback p e : Scheme.{u}) := isNoetherian_of_finiteType pL
    letI : IsNoetherian (pullback t e : Scheme.{u}) := isNoetherian_of_finiteType tL
    letI : IsNoetherian (pullback pL tL : Scheme.{u}) :=
      isNoetherian_of_finiteType (pullback.fst pL tL)
    letI := IntegralCycle.genericPointFintype (pullback p e : Scheme.{u})
    letI := IntegralCycle.genericPointFintype (pullback t e : Scheme.{u})
    letI : ∀ a : genericPoints (pullback p e : Scheme.{u}),
        ∀ b : genericPoints (pullback t e : Scheme.{u}),
          IsNoetherian (componentPairExterior pL tL a b) :=
      fun a b => isNoetherian_of_finiteType (componentPairExteriorInclusion pL tL a b)
    fundamentalCycle (pullback pL tL) =
      ∑ a : genericPoints (pullback p e : Scheme.{u}),
        ∑ b : genericPoints (pullback t e : Scheme.{u}),
          ((genericMultiplicity a : ℤ) * (genericMultiplicity b : ℤ)) •
            IntegralCycle.finitePushforward (componentPairExteriorInclusion pL tL a b)
              (fundamentalCycle (componentPairExterior pL tL a b)) := by
  dsimp only
  let e := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let : IsNoetherian (pullback p e : Scheme.{u}) :=
    isNoetherian_of_finiteType (pullback.snd p e)
  let : IsNoetherian (pullback t e : Scheme.{u}) :=
    isNoetherian_of_finiteType (pullback.snd t e)
  let : IsNoetherian (pullback (pullback.snd p e) (pullback.snd t e) : Scheme.{u}) :=
    isNoetherian_of_finiteType (pullback.fst (pullback.snd p e) (pullback.snd t e))
  exact fundamentalCycle_product_eq_component_pair_sum (pullback.snd p e) (pullback.snd t e)

open Lean in
run_cmd do
  for name in #[``IsLocalRing.length_self_of_flat,
      ``AlgebraicGeometry.Flat.generic_stalk_lengths_ne_top,
      ``AlgebraicGeometry.Flat.genericMultiplicity_eq_mul_closedFiber,
      ``AlgebraicGeometry.genericMultiplicity_componentGeneric_mul_closedFiber,
      ``AlgebraicGeometry.fundamentalCycle_open_eq_component_sum,
      ``AlgebraicGeometry.finitePushforward_top_component_fundamentalCycle,
      ``AlgebraicGeometry.fundamentalCycle_pullback_eq_component_sum,
      ``AlgebraicGeometry.componentExteriorSndInclusion_eq_map,
      ``AlgebraicGeometry.fundamentalCycle_pullback_eq_second_component_sum,
      ``AlgebraicGeometry.componentPairExteriorInclusion_eq_map,
      ``AlgebraicGeometry.fundamentalCycle_product_eq_component_pair_sum,
      ``arbitraryFlatBaseChange, ``possiblyNonreducedDisconnectedProduct,
      ``arbitraryFieldChangeProduct] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Flat fundamental-cycle decomposition uses only standard foundations."

end MotivicTest.FlatFundamentalCycle
