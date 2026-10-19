/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Canonical adjunction coherence for open restriction

The geometric open-restriction associators are mates of the actual pushforward
associators. These identities retain the canonical maps on sections.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Modules.Restriction.AdjunctionCoherence

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [IsOpenImmersion f] [IsOpenImmersion g]

/-- Restriction of an actual module morphism acts on its genuine image-open sections. -/
theorem restrictFunctor_map_app {M N : Y.Modules} (a : M ⟶ N) (U : X.Opens) :
    ((restrictFunctor f).map a).app U = a.app (f ''ᵁ U) := rfl

/-- The canonical restriction associator is the mate of the actual pushforward associator. -/
theorem conjugate_restrictFunctorComp_hom :
    conjugateEquiv ((restrictAdjunction g).comp (restrictAdjunction f))
      (restrictAdjunction (f ≫ g)) (restrictFunctorComp f g).hom = (pushforwardComp f g).hom := by
  apply NatTrans.ext
  funext M
  simp only [conjugateEquiv_apply_app, Adjunction.comp_counit_app]
  apply Scheme.Modules.hom_ext
  intro U
  simp only [Hom.comp_app,
    pushforward_map_app, restrictFunctor_map_app, restrictAdjunction_unit_app_app,
    restrictAdjunction_counit_app_app,
    restrictFunctorComp_hom_app_app, pushforwardComp_hom_app_app]
  simp only [Functor.comp_obj, pushforward_obj_presheaf_map]
  erw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  exact (congrArg M.presheaf.map (Subsingleton.elim _ _)).trans (M.presheaf.map_id _)

/-- Reflexive geometric restriction transport is the identity transformation. -/
theorem restrictFunctorCongr_refl :
    (restrictFunctorCongr (rfl : f = f)).hom = 𝟙 (restrictFunctor f) := by
  apply NatTrans.ext
  funext M
  apply Scheme.Modules.hom_ext
  intro U
  simp only [restrictFunctorCongr_hom_app_app, NatTrans.id_app, Hom.id_app]
  exact M.presheaf.map_id _

/-- Geometric restriction transport across an equality is the actual pushforward mate. -/
theorem conjugate_restrictFunctorCongr_hom {f' : X ⟶ Y} [IsOpenImmersion f'] (h : f = f') :
    conjugateEquiv (restrictAdjunction f') (restrictAdjunction f)
      (restrictFunctorCongr h).hom = (pushforwardCongr h).inv := by
  subst f'
  rw [restrictFunctorCongr_refl, conjugateEquiv_id]
  apply NatTrans.ext
  funext M
  apply Scheme.Modules.hom_ext
  intro U
  simp only [NatTrans.id_app, Hom.id_app, pushforwardCongr_inv_app_app]
  exact (M.presheaf.map_id _).symm

omit [IsOpenImmersion f] in
/-- Reversing a geometric equality exchanges the canonical pushforward maps. -/
theorem pushforwardCongr_symm_hom {f' : X ⟶ Y} (h : f = f') :
    (pushforwardCongr h.symm).hom = (pushforwardCongr h).inv := by
  apply NatTrans.ext
  funext M
  apply Scheme.Modules.hom_ext
  intro U
  simp only [pushforwardCongr_hom_app_app, pushforwardCongr_inv_app_app]
  rfl

end AlgebraicGeometry.Scheme.Modules.Restriction.AdjunctionCoherence
