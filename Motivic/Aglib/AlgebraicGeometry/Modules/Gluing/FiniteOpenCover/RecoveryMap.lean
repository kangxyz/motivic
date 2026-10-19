/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Gluing.FiniteOpenCover.Recovery

/-!
# The canonical covering recovery isomorphism

The actual restriction units construct the comparison from an original
module sheaf to its finite compatible-sections equalizer. When the opens
cover, that comparison is proved to be an isomorphism.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.Gluing.FiniteOpenCover

open Scheme.Modules _root_.AlgebraicGeometry.Scheme.Modules.Gluing.TwoOpenCover

variable {X : Scheme.{u}} {ι : Type u} [Fintype ι]
  (U : ι → X.Opens) (N : X.Modules)

omit [Fintype ι] in
set_option backward.isDefEq.respectTransparency false in
/-- The actual open restriction units satisfy the canonical overlap compatibility. -/
theorem canonicalUnits_condition (i j : ι) :
    (restrictAdjunction (U i).ι).unit.app N ≫
      leftOverlapMap (a := X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i))
        (f := (U i).ι) (restrictedModules U N i) =
    (restrictAdjunction (U j).ι).unit.app N ≫
      rightOverlapMap (isPullback_opens_inf (U i) (U j))
        (restrictedModules U N i) (restrictedModules U N j) (canonicalTransition U N i j) := by
  apply Scheme.Modules.hom_ext
  intro A
  simp only [Hom.comp_app, restrictAdjunction_unit_app_app, leftOverlapMap,
    pushforward_map_app, rightOverlapMap_app, canonicalTransition,
    overlapRestrictionIso, Iso.trans_inv, Iso.app_inv, Iso.symm_inv, NatTrans.comp_app,
    restrictFunctorComp_hom_app_app, restrictFunctorComp_inv_app_app,
    restrictFunctorCongr_inv_app_app, restrictedModules, restrict_map]
  simp only [← Functor.map_comp]
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- The actual family of restriction units gives a compatible finite product cone. -/
theorem canonicalProduct_condition :
    Pi.lift (fun i => (restrictAdjunction (U i).ι).unit.app N) ≫
        firstMap U (restrictedModules U N) =
      Pi.lift (fun i => (restrictAdjunction (U i).ι).unit.app N) ≫
        secondMap U (restrictedModules U N) (canonicalDatum U N) := by
  apply Pi.hom_ext
  intro ij
  rcases ij with ⟨i, j⟩
  simp only [Category.assoc, firstMap_π, secondMap_π]
  erw [Pi.lift_comp_π_assoc, Pi.lift_comp_π_assoc]
  exact canonicalUnits_condition U N i j

/-- The canonical global comparison is constructed from the actual restriction units. -/
def canonicalRecoveryMap : N ⟶ glued U (restrictedModules U N) (canonicalDatum U N) :=
  equalizer.lift (Pi.lift fun i => (restrictAdjunction (U i).ι).unit.app N)
    (canonicalProduct_condition U N)

set_option backward.isDefEq.respectTransparency false in
/-- Every projection of the global recovery comparison is the original restriction unit. -/
@[reassoc (attr := simp)] theorem canonicalRecoveryMap_projection (i : ι) :
    canonicalRecoveryMap U N ≫ projection U (restrictedModules U N) (canonicalDatum U N) i =
      (restrictAdjunction (U i).ι).unit.app N := by
  simp [canonicalRecoveryMap, projection]

set_option backward.isDefEq.respectTransparency false in
/-- Each local recovery comparison is the literal restriction-adjunction triangle identity. -/
@[reassoc] theorem canonicalRecoveryMap_local (i : ι) :
    (restrictFunctor (U i).ι).map (canonicalRecoveryMap U N) ≫
      (localIso U (restrictedModules U N) (canonicalDatum U N) i).hom = 𝟙 _ := by
  rw [localIso_hom, localProjection, ← Functor.map_comp_assoc,
    canonicalRecoveryMap_projection]
  exact (restrictAdjunction (U i).ι).left_triangle_components N

set_option backward.isDefEq.respectTransparency false in
/-- The constructed global recovery comparison is invertible on an actual covering family. -/
theorem canonicalRecoveryMap_isIso (hU : ⨆ i, U i = ⊤) : IsIso (canonicalRecoveryMap U N) := by
  have (i : ι) : IsIso ((restrictFunctor (U i).ι).map (canonicalRecoveryMap U N)) := by
    have h := canonicalRecoveryMap_local U N i
    have : IsIso ((restrictFunctor (U i).ι).map (canonicalRecoveryMap U N) ≫
        (localIso U (restrictedModules U N) (canonicalDatum U N) i).hom) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (localIso U (restrictedModules U N) (canonicalDatum U N) i).hom
  exact isIso_of_cover U (canonicalRecoveryMap U N) hU

/-- Actual finite open-cover gluing recovers the original module sheaf canonically. -/
def canonicalRecoveryIso (hU : ⨆ i, U i = ⊤) :
    N ≅ glued U (restrictedModules U N) (canonicalDatum U N) := by
  letI := canonicalRecoveryMap_isIso U N hU
  exact asIso (canonicalRecoveryMap U N)

end AlgebraicGeometry.Scheme.Modules.Gluing.FiniteOpenCover
