/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.FlatFundamentalCycle
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Whole fundamental cycles in a tower of flat base changes

The comparison is the canonical iterated-pullback isomorphism. The tower
formula retains the original generic lengths of every intermediate component
and the whole, possibly nonreduced, pullback of that component. No finite-type
hypothesis is imposed on either change of base.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Motivic
open Motivic.WholeFiberTorExteriorDecomposition
open scoped BigOperators

universe u

namespace AlgebraicGeometry

variable {P S T U : Scheme.{u}} (p : P ⟶ S) (t : T ⟶ S) (s : U ⟶ T)

/-- The identity base-change comparison is its actual first projection. -/
def pullbackIdentityIso : pullback p (𝟙 S) ≅ P :=
  asIso (pullback.fst p (𝟙 S))

@[simp]
theorem pullbackIdentityIso_hom :
    (pullbackIdentityIso p).hom = pullback.fst p (𝟙 S) := rfl

/-- The inverse identity comparison is the canonical section of the pullback. -/
theorem pullbackIdentityIso_inv :
    (pullbackIdentityIso p).inv = pullback.lift (𝟙 P) p (by simp) := by
  apply (cancel_mono (pullback.fst p (𝟙 S))).mp
  simp [pullbackIdentityIso]

/-- The whole iterated pullback is identified with the direct pullback by
pasting its two original Cartesian squares. -/
def pullbackTowerIso : pullback (pullback.snd p t) s ≅ pullback p (s ≫ t) :=
  pullbackLeftPullbackSndIso p t s

@[reassoc (attr := simp)]
theorem pullbackTowerIso_hom_fst :
    (pullbackTowerIso p t s).hom ≫ pullback.fst p (s ≫ t) =
      pullback.fst (pullback.snd p t) s ≫ pullback.fst p t :=
  pullbackLeftPullbackSndIso_hom_fst p t s

@[reassoc (attr := simp)]
theorem pullbackTowerIso_hom_snd :
    (pullbackTowerIso p t s).hom ≫ pullback.snd p (s ≫ t) =
      pullback.snd (pullback.snd p t) s :=
  pullbackLeftPullbackSndIso_hom_snd p t s

/-- Identity base change preserves all generic local lengths, including those
of nonreduced schemes, along the literal projection. -/
theorem finitePushforward_pullbackIdentity_fundamentalCycle [IsNoetherian P] :
    let : IsNoetherian (pullback p (𝟙 S) : Scheme.{u}) :=
      isNoetherian_of_finiteType (pullbackIdentityIso p).hom
    IntegralCycle.finitePushforward (pullbackIdentityIso p).hom
      (fundamentalCycle (pullback p (𝟙 S))) = fundamentalCycle P := by
  let : IsNoetherian (pullback p (𝟙 S) : Scheme.{u}) :=
    isNoetherian_of_finiteType (pullbackIdentityIso p).hom
  exact finitePushforward_fundamentalCycle (pullbackIdentityIso p).hom

/-- The canonical tower comparison preserves the entire fundamental cycle. -/
theorem finitePushforward_pullbackTower_fundamentalCycle
    [IsNoetherian (pullback p (s ≫ t) : Scheme.{u})] :
    let : IsNoetherian (pullback (pullback.snd p t) s : Scheme.{u}) :=
      isNoetherian_of_finiteType (pullbackTowerIso p t s).hom
    IntegralCycle.finitePushforward (pullbackTowerIso p t s).hom
      (fundamentalCycle (pullback (pullback.snd p t) s)) =
        fundamentalCycle (pullback p (s ≫ t)) := by
  let : IsNoetherian (pullback (pullback.snd p t) s : Scheme.{u}) :=
    isNoetherian_of_finiteType (pullbackTowerIso p t s).hom
  exact finitePushforward_fundamentalCycle (pullbackTowerIso p t s).hom

/-- Direct base change equals the actual weighted sum of the full pullbacks of
all intermediate reduced components. Their old and new nilpotent lengths are
both retained. Only the second change of base needs to be flat. -/
theorem fundamentalCycle_pullbackTower_eq_component_sum
    [Flat s] [IsNoetherian (pullback p t : Scheme.{u})]
    [IsNoetherian (pullback p (s ≫ t) : Scheme.{u})] :
    let : IsNoetherian (pullback (pullback.snd p t) s : Scheme.{u}) :=
      isNoetherian_of_finiteType (pullbackTowerIso p t s).hom
    let := IntegralCycle.genericPointFintype (pullback p t : Scheme.{u})
    let : ∀ z : genericPoints (pullback p t : Scheme.{u}),
        IsNoetherian (componentExterior (pullback.snd p t) s z) :=
      fun z => isNoetherian_of_finiteType
        (componentExteriorInclusion (pullback.snd p t) s z)
    fundamentalCycle (pullback p (s ≫ t)) =
      ∑ z : genericPoints (pullback p t : Scheme.{u}),
        (genericMultiplicity z : ℤ) •
          IntegralCycle.finitePushforward
            (componentExteriorInclusion (pullback.snd p t) s z ≫
              (pullbackTowerIso p t s).hom)
            (fundamentalCycle (componentExterior (pullback.snd p t) s z)) := by
  let : IsNoetherian (pullback (pullback.snd p t) s : Scheme.{u}) :=
    isNoetherian_of_finiteType (pullbackTowerIso p t s).hom
  let := IntegralCycle.genericPointFintype (pullback p t : Scheme.{u})
  let : ∀ z : genericPoints (pullback p t : Scheme.{u}),
      IsNoetherian (componentExterior (pullback.snd p t) s z) :=
    fun z => isNoetherian_of_finiteType
      (componentExteriorInclusion (pullback.snd p t) s z)
  rw [← finitePushforward_pullbackTower_fundamentalCycle p t s,
    fundamentalCycle_pullback_eq_component_sum (pullback.snd p t) s, map_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [map_zsmul, IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply]

end AlgebraicGeometry

namespace Motivic.IntegralCycle

/-- Finite pushforward depends on the actual morphism, not on its finiteness proof.
This form permits geometric comparison equations to be used without a dependent rewrite. -/
theorem finitePushforward_congr {X Y : AlgebraicGeometry.Scheme.{u}} {f g : X ⟶ Y}
    [AlgebraicGeometry.IsFinite f] [AlgebraicGeometry.IsFinite g] (h : f = g) :
    finitePushforward f = finitePushforward g := by
  subst h
  rfl

end Motivic.IntegralCycle
