/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Intersection.ClosedAffineOverlap
public import Motivic.AlgebraicGeometry.Modules.OpenRefinementCoherence

/-!
# Descent for a coherent system on actual ambient affine charts

A system of local module sheaves with actualested restriction isomorphisms
and their proved composition law supplies ordinary finite descent data. The
pair and triple intersections are the genuine intersections of ambient affine
opens; arbitrary common support opens are allowed in the resulting cocycle.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.AffineChartModuleDescent

open Scheme.Modules ClosedAffineCover FiniteOpenModuleGluing OpenRefinement

variable {P W : Scheme.{u}} [P.IsSeparated] (p : W ⟶ P)
  (M : ∀ U : P.affineOpens, (p ⁻¹ᵁ U).toScheme.Modules)
  (e : ∀ {U V : P.affineOpens} (h : U ≤ V),
    (restrictFunctor (W.homOfLE (p.preimage_mono h))).obj (M V) ≅ M U)
  (hc : ∀ {U V L : P.affineOpens} (h : U ≤ V) (k : V ≤ L),
    (compositionIso (p.preimage_mono h) (p.preimage_mono k)).app (M L) ≪≫
      (restrictFunctor (W.homOfLE (p.preimage_mono h))).mapIso (e k) ≪≫ e h =
        e (h.trans k))

/-- Restriction of a supplied chart comparison to any smaller support open. -/
def restrictionOn {U V : P.affineOpens} (h : U ≤ V)
    {O : W.Opens} (hO : O ≤ p ⁻¹ᵁ U) :
    (restrictFunctor (W.homOfLE (hO.trans (p.preimage_mono h)))).obj
        (M V) ≅
      (restrictFunctor (W.homOfLE hO)).obj
        (M U) :=
  liftIso (p.preimage_mono h)
    (e h) hO

include hc in
omit [P.IsSeparated] in
set_option backward.isDefEq.respectTransparency false in
/-- The supplied nested composition law remains coherent after an arbitrary smaller restriction. -/
theorem restrictionOn_comp {U V L : P.affineOpens}
    (h : U ≤ V) (k : V ≤ L) {O : W.Opens}
    (hO : O ≤ p ⁻¹ᵁ U) :
    restrictionOn p M e (h.trans k) hO =
      restrictionOn p M e k
        (hO.trans (p.preimage_mono h)) ≪≫
      restrictionOn p M e h hO := by
  unfold restrictionOn
  exact (congrArg (fun q => liftIso (p.preimage_mono (h.trans k)) q hO)
    (hc h k)).symm.trans (liftIso_comp _ _ _ _ _)

/-- The transition uses both original chart restrictions to their genuine affine overlap. -/
def transition (U V : P.affineOpens) :
    (restrictFunctor (W.homOfLE (inf_le_left :
      (p ⁻¹ᵁ U) ⊓ (p ⁻¹ᵁ V) ≤ p ⁻¹ᵁ U))).obj
        (M U) ≅
      (restrictFunctor (W.homOfLE (inf_le_right :
        (p ⁻¹ᵁ U) ⊓ (p ⁻¹ᵁ V) ≤ p ⁻¹ᵁ V))).obj
        (M V) :=
  e (affineOverlap_le_left U V) ≪≫
    (e
      (affineOverlap_le_right U V)).symm

/-- Repeated-chart transitions are identities by the original map/inverse cancellation. -/
theorem transition_identity (U : P.affineOpens) :
    transition p M e U U = Iso.refl _ := by
  apply Iso.ext
  exact Iso.hom_inv_id _

variable {ι : Type u} (U : ι → P.affineOpens)

include hc in
set_option backward.isDefEq.respectTransparency false in
/-- Every pair transition on a common smaller open factors through any actual
ambient affine refinement of that pair. -/
theorem transitionOn_refinement (r s : ι)
    (A : P.affineOpens) (hr : A ≤ U r) (hs : A ≤ U s)
    {O : W.Opens} (hO : O ≤ p ⁻¹ᵁ A) :
    transitionOn (fun t => p ⁻¹ᵁ U t)
        (fun t => M (U t))
        (fun t v => transition p M e (U t) (U v))
        r s (hO.trans (p.preimage_mono hr))
          (hO.trans (p.preimage_mono hs)) =
      restrictionOn p M e hr hO ≪≫
        (restrictionOn p M e hs hO).symm := by
  have hA : A ≤ affineOverlap (U r) (U s) := by
    change A.1 ≤ (U r).1 ⊓ (U s).1
    exact le_inf (show A.1 ≤ (U r).1 from hr) (show A.1 ≤ (U s).1 from hs)
  change transitionOn (fun t => p ⁻¹ᵁ U t)
    (fun t => M (U t))
    (fun t v => e
      (affineOverlap_le_left (U t) (U v)) ≪≫
        (e
          (affineOverlap_le_right (U t) (U v))).symm) r s _ _ = _
  rw [transitionOn_pair]
  rw [restrictionOn_comp p M e hc hA
      (affineOverlap_le_left (U r) (U s)) hO,
    restrictionOn_comp p M e hc hA
      (affineOverlap_le_right (U r) (U s)) hO]
  apply Iso.ext
  simp [restrictionOn]

/-- The constructed chart datum has its identity and every common-open cocycle proved. -/
def datum :
    Datum (fun t => p ⁻¹ᵁ U t)
      (fun t => M (U t)) where
  transition r s := transition p M e (U r) (U s)
  identity r := transition_identity p M e (U r)
  cocycle O r s t hr hs ht := by
    let A := affineOverlap (affineOverlap (U r) (U s)) (U t)
    have hAr : A ≤ U r := (affineOverlap_le_left _ _).trans (affineOverlap_le_left _ _)
    have hAs : A ≤ U s := (affineOverlap_le_left _ _).trans (affineOverlap_le_right _ _)
    have hAt : A ≤ U t := affineOverlap_le_right _ _
    have hO : O ≤ p ⁻¹ᵁ A := le_inf (le_inf hr hs) ht
    rw [transitionOn_refinement p M e hc U r s A hAr hAs hO,
      transitionOn_refinement p M e hc U s t A hAs hAt hO,
      transitionOn_refinement p M e hc U r t A hAr hAt hO]
    apply Iso.ext
    simp

end Motivic.AffineChartModuleDescent
