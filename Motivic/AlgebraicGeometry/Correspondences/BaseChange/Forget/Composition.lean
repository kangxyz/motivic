/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.ForgetBase
public import Motivic.AlgebraicGeometry.Correspondences.BaseChange.Forget.Cycle
public import Motivic.AlgebraicGeometry.Correspondences.BaseChange.Forget.IncidenceTor
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Incidence.TorCycle

/-! # Genuine signed correspondence composition after forgetting a finite separable base -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic
open _root_.AlgebraicGeometry.Scheme

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [Module.Finite k L] [Algebra.IsSeparable k L]
  {X Y Z : SmoothSite (Spec (.of L))}

local notation "r" => SmoothSite.finiteSeparableBaseMap k L
local notation "F" => SmoothSite.finiteSeparableForgetBase k L

namespace FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme

variable (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom)

local instance forgottenIncidence_noetherian :
    IsNoetherian ((A.forgetBase r).incidence (B.forgetBase r)) :=
  isNoetherian_smoothIncidence k (X := (F).obj X) (Y := (F).obj Y) (Z := (F).obj Z) _ _

/-- The whole original signed incidence cycle is transported through the incidence isomorphism. -/
theorem finitePushforward_forgetBase_incidenceTorCycle :
    IntegralCycle.finitePushforward (A.forgetBaseIncidenceMap r B)
      (IntegralCycle.ofGenericCoefficients (A.incidence B)
        (A.incidenceTorCoefficient (S := Spec (.of L)) B)) =
    IntegralCycle.ofGenericCoefficients ((A.forgetBase r).incidence (B.forgetBase r))
      ((A.forgetBase r).incidenceTorCoefficient (S := Spec (.of k)) (B.forgetBase r)) := by
  classical
  let e := A.forgetBaseIncidenceMap r B
  apply IntegralCycle.toPoints_injective
  rw [← AddMonoidHom.comp_apply, IntegralCycle.toPoints_finitePushforward,
    AddMonoidHom.comp_apply, residuePushforward_eq_mapDomain_of_surjectiveOnStalks]
  ext y
  obtain ⟨x, rfl⟩ := e.homeomorph.surjective y
  change Finsupp.mapDomain e (IntegralCycle.toPoints
    (IntegralCycle.ofGenericCoefficients (A.incidence B)
        (A.incidenceTorCoefficient (S := Spec (.of L)) B))) (e x) = _
  rw [Finsupp.mapDomain_apply_of_injective
    (show Function.Injective e from e.homeomorph.injective)]
  simp only [IntegralCycle.toPoints_ofGenericCoefficients_apply, Scheme.Hom.homeomorph_apply]
  by_cases hx : x ∈ genericPoints (A.incidence B)
  · rw [dite_eq_left hx, dite_eq_left ((mem_genericPoints_iff_of_isIso e x).mpr hx)]
    exact (A.forgetBase_incidenceTorCoefficient r B ⟨x, hx⟩).symm
  · rw [dite_eq_right hx,
      dite_eq_right (fun hy => hx ((mem_genericPoints_iff_of_isIso e x).mp hy))]

/-- Forgetting the base preserves the original generator composition, with all signed weights. -/
theorem forgetBase_incidenceTorCorrespondence :
    FiniteCorrespondence.forgetBase r X.hom Z.hom (A.incidenceTorCorrespondence L B) =
      (A.forgetBase r).incidenceTorCorrespondence k
        (X := (F).obj X) (Y := (F).obj Y) (Z := (F).obj Z) (B.forgetBase r) := by
  apply FiniteCorrespondence.toIntegralCycle_injective
  refine (FiniteCorrespondence.toIntegralCycle_forgetBase r _).trans ?_
  refine (congrArg (IntegralCycle.finitePushforward (forgetBaseProductMap r X.hom Z.hom))
    (A.toIntegralCycle_incidenceTorCorrespondence L B)).trans ?_
  refine Eq.trans ?_ ((A.forgetBase r).toIntegralCycle_incidenceTorCorrespondence k
    (X := (F).obj X) (Y := (F).obj Y) (Z := (F).obj Z) (B.forgetBase r)).symm
  refine Eq.trans ?_ (congrArg
    (IntegralCycle.finitePushforward ((A.forgetBase r).incidenceMap (B.forgetBase r)))
    (A.finitePushforward_forgetBase_incidenceTorCycle k L B))
  have hc := IntegralCycle.finitePushforward_comp (A.forgetBaseIncidenceMap r B)
    ((A.forgetBase r).incidenceMap (B.forgetBase r))
  simp only [A.forgetBaseIncidenceMap_map r B, IntegralCycle.finitePushforward_comp] at hc
  exact DFunLike.congr_fun hc _

end FiniteCorrespondenceGenerator

namespace FiniteCorrespondence

/-- Unit signed cycles recover the proved original generator pairing. -/
theorem forgetBase_incidenceTorPairing_cycle
    (A : FiniteCorrespondenceGenerator X.hom Y.hom)
    (B : FiniteCorrespondenceGenerator Y.hom Z.hom) :
    forgetBase r X.hom Z.hom (incidenceTorPairing L (X := X) (Y := Y) (Z := Z) A.cycle B.cycle) =
      incidenceTorPairing k (X := (F).obj X) (Y := (F).obj Y) (Z := (F).obj Z)
        (forgetBase r X.hom Y.hom A.cycle) (forgetBase r Y.hom Z.hom B.cycle) := by
  rw [incidenceTorPairing_cycle L]
  simp only [FiniteCorrespondenceGenerator.cycle, forgetBase_single]
  rw [incidenceTorPairing_single k (X := (F).obj X) (Y := (F).obj Y) (Z := (F).obj Z),
    one_mul, one_smul]
  exact A.forgetBase_incidenceTorCorrespondence k L B

/-- Actual composition is preserved for arbitrary signed cycles and disconnected objects. -/
theorem forgetBase_incidenceTorPairing
    (α : FiniteCorrespondence X.hom Y.hom) (β : FiniteCorrespondence Y.hom Z.hom) :
    forgetBase r X.hom Z.hom (incidenceTorPairing L (X := X) (Y := Y) (Z := Z) α β) =
      incidenceTorPairing k (X := (F).obj X) (Y := (F).obj Y) (Z := (F).obj Z)
        (forgetBase r X.hom Y.hom α) (forgetBase r Y.hom Z.hom β) := by
  have hright (A : FiniteCorrespondenceGenerator X.hom Y.hom) :
      (forgetBase r X.hom Z.hom).comp
          (incidenceTorPairing L (X := X) (Y := Y) (Z := Z) A.cycle) =
        (incidenceTorPairing k (X := (F).obj X) (Y := (F).obj Y) (Z := (F).obj Z)
          (forgetBase r X.hom Y.hom A.cycle)).comp (forgetBase r Y.hom Z.hom) := by
    apply Finsupp.addHom_ext
    intro B n
    have hs : Finsupp.single B n = n • B.cycle := by simp [FiniteCorrespondenceGenerator.cycle]
    rw [hs, map_zsmul, map_zsmul]
    exact congrArg (fun γ => n • γ) (forgetBase_incidenceTorPairing_cycle k L A B)
  have hleft :
      (forgetBase r X.hom Z.hom).comp
          ((incidenceTorPairing L (X := X) (Y := Y) (Z := Z)).flip β) =
        ((incidenceTorPairing k (X := (F).obj X) (Y := (F).obj Y) (Z := (F).obj Z)).flip
          (forgetBase r Y.hom Z.hom β)).comp (forgetBase r X.hom Y.hom) := by
    apply Finsupp.addHom_ext
    intro A n
    have hs : Finsupp.single A n = n • A.cycle := by simp [FiniteCorrespondenceGenerator.cycle]
    rw [hs, map_zsmul, map_zsmul]
    exact congrArg (fun G => n • G β) (hright A)
  exact congrArg (fun G => G α) hleft

end FiniteCorrespondence

end Motivic
