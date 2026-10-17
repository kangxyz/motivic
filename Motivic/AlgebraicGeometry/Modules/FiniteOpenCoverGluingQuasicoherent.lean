/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Modules.FiniteOpenCoverGluingEffective
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Quasi-coherence of actual finite open gluing

Quasi-coherence of the original local module sheaves descends to the
constructed equalizer on an actual open cover. No global quasi-coherence
hypothesis is used.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Motivic.FiniteOpenModuleGluing

open Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- The inverse open/slice equivalence preserves quasi-coherent module sheaves. -/
theorem isQuasicoherent_overEquiv_inverse {X : Scheme.{u}} (U : X.Opens)
    (M : U.toScheme.Modules) [M.IsQuasicoherent] :
    ((overEquiv U).inverse.obj M).IsQuasicoherent := by
  have := U.instIsDenseSubsiteOverSubtypeMemOverGrothendieckTopologyFunctorOverEquivalence
  have (V : Over U) : (Over.post (X := V) U.overEquivalence.functor).IsContinuous
      (((Opens.grothendieckTopology X).over U).over V)
      ((Opens.grothendieckTopology U.carrier).over (U.overEquivalence.functor.obj V)) :=
    Functor.isContinuous_iff_coverPreserving.mpr
      ((CoverPreserving.of_isContinuous U.overEquivalence.functor _ _).overPost V)
  exact SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint
    U.overEquivalence.functor _ (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf)

set_option backward.isDefEq.respectTransparency false in
/-- Quasi-coherence on the actual open restriction gives quasi-coherence on the slice site. -/
theorem isQuasicoherent_over_of_restrict {X : Scheme.{u}} (U : X.Opens) (M : X.Modules)
    [((restrictFunctor U.ι).obj M).IsQuasicoherent] : (M.over U).IsQuasicoherent := by
  have := isQuasicoherent_overEquiv_inverse U ((restrictFunctor U.ι).obj M)
  exact (SheafOfModules.isQuasicoherent (X.ringCatSheaf.over U)).prop_of_iso
    (((overEquiv U).inverse.mapIso ((overFunctorEquiv U).app M)).symm ≪≫
      ((overEquiv U).unitIso.app (M.over U)).symm) inferInstance

/-- Actual open-cover restriction quasi-coherence implies global quasi-coherence. -/
theorem isQuasicoherent_of_cover {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (M : X.Modules) (hU : ⨆ i, U i = ⊤)
    [∀ i, ((restrictFunctor (U i).ι).obj M).IsQuasicoherent] : M.IsQuasicoherent := by
  have (i : ι) : (M.over (U i)).IsQuasicoherent := isQuasicoherent_over_of_restrict (U i) M
  exact SheafOfModules.IsQuasicoherent.of_coversTop M U ((Opens.coversTop_iff X U).mpr hU)

/-- The constructed finite equalizer is quasi-coherent when its local coefficients are. -/
theorem glued_isQuasicoherent {X : Scheme.{u}} {ι : Type u} [Fintype ι]
    (U : ι → X.Opens) (M : ∀ i, (U i).toScheme.Modules) (d : Datum U M)
    (hU : ⨆ i, U i = ⊤) [∀ i, (M i).IsQuasicoherent] : (glued U M d).IsQuasicoherent := by
  have (i : ι) : ((restrictFunctor (U i).ι).obj (glued U M d)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (U i).toScheme.ringCatSheaf).prop_of_iso
      (localIso U M d i).symm inferInstance
  exact isQuasicoherent_of_cover U (glued U M d) hU

end Motivic.FiniteOpenModuleGluing
