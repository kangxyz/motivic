/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Modules.FiniteOpenCoverGluingEffective

/-!
# Actual descent data from local identifications

Canonical restrictions of a module sheaf supply ordinary overlap descent data.
Changing local identifications supplies nonidentity gauge transitions.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteOpenModuleGluing

open Scheme.Modules Motivic.OpenModuleGluing

variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens) (N : X.Modules)

/-- The actual restrictions of a module sheaf to the chosen opens. -/
abbrev restrictedModules (i : ι) := (restrictFunctor (U i).ι).obj N

/-- The original restriction comparisons give the canonical overlap transition. -/
def canonicalTransition (i j : ι) : Transition U (restrictedModules U N) i j :=
  (overlapRestrictionIso (isPullback_opens_inf (U i) (U j))).app N

/-- A restriction through one cover member agrees with the direct ambient restriction. -/
def canonicalCommonIso {W : X.Opens} (i : ι) (hi : W ≤ U i) :
    (restrictFunctor (X.homOfLE hi)).obj (restrictedModules U N i) ≅
      (restrictFunctor W.ι).obj N :=
  (restrictFunctorComp (X.homOfLE hi) (U i).ι).symm.app N ≪≫
    (restrictFunctorCongr (X.homOfLE_ι hi)).app N

set_option backward.isDefEq.respectTransparency false in
/-- The restricted canonical transition is the comparison through the direct ambient restriction. -/
theorem canonicalTransitionOn {W : X.Opens} (i j : ι) (hi : W ≤ U i) (hj : W ≤ U j) :
    transitionOn U (restrictedModules U N) (canonicalTransition U N) i j hi hj =
      canonicalCommonIso U N i hi ≪≫ (canonicalCommonIso U N j hj).symm := by
  apply Iso.ext
  apply Scheme.Modules.hom_ext
  intro S
  rw [transitionOn_hom_app]
  simp only [canonicalTransition, overlapRestrictionIso, canonicalCommonIso,
    Iso.trans_hom, Hom.comp_app, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Iso.app_hom, Iso.app_inv, NatTrans.comp_app,
    restrictFunctorComp_hom_app_app, restrictFunctorComp_inv_app_app,
    restrictFunctorCongr_hom_app_app, restrictFunctorCongr_inv_app_app,
    restrictedModules, restrict_map]
  simp only [← Functor.map_comp]
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- Canonical restrictions satisfy the ordinary normalized triple-overlap cocycle. -/
def canonicalDatum : Datum U (restrictedModules U N) where
  transition := canonicalTransition U N
  identity i := by
    change (overlapRestrictionIso (isPullback_opens_inf (U i) (U i))).app N = _
    rw [overlapRestrictionIso_self]
    rfl
  cocycle W i j k hi hj hk := by
    simp only [canonicalTransitionOn]
    apply Iso.ext
    simp

end Motivic.FiniteOpenModuleGluing
