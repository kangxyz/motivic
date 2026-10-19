/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Pushforward.Finite.OpenRestriction

/-!
# Whole affine comparisons from relative quasi-coherence

Only quasi-coherence on the whole inverse image of the chosen target affine
open is required. Restriction through its actual affine isomorphism supplies
the chart counit, preserving the original ambient module, complexes, source
stalks and global finite pushforward. No ambient quasi-coherence is inferred.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent.RelativeAffine
open _root_.AlgebraicGeometry.Scheme.Modules.Pushforward

open Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Hom.FiniteAffineChart
open _root_.AlgebraicGeometry.Scheme.Modules.QuasiCoherent.Affine
open _root_.AlgebraicGeometry.Scheme.Modules.Stalk

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
  {U : Y.Opens} (hU : IsAffineOpen U)

/-- Actual affine restriction factors through the entire original inverse-image open. -/
def sourceChartRestrictionIso :
    restrictFunctor (sourceChart f hU) ≅
      restrictFunctor (f ⁻¹ᵁ U).ι ⋙ restrictFunctor (hU.preimage f).isoSpec.inv :=
  restrictFunctorComp (hU.preimage f).isoSpec.inv (f ⁻¹ᵁ U).ι

/-- Quasi-coherence on the whole inverse image suffices on its actual affine chart. -/
theorem sourceChart_quasicoherent (N : X.Modules)
    [((restrictFunctor (f ⁻¹ᵁ U).ι).obj N).IsQuasicoherent] :
    ((restrictFunctor (sourceChart f hU)).obj N).IsQuasicoherent := by
  have : ((restrictFunctor (hU.preimage f).isoSpec.inv).obj
      ((restrictFunctor (f ⁻¹ᵁ U).ι).obj N)).IsQuasicoherent := inferInstance
  exact (SheafOfModules.isQuasicoherent (Spec Γ(X, f ⁻¹ᵁ U)).ringCatSheaf).prop_of_iso
    ((sourceChartRestrictionIso f hU).app N).symm this

variable {ι : Type*} (c : ComplexShape ι) (K : HomologicalComplex X.Modules c)
  [∀ n, ((restrictFunctor (f ⁻¹ᵁ U).ι).obj (K.X n)).IsQuasicoherent]

/-- The actual counit presents the whole restricted complex using relative QC alone. -/
def wholeChartTildeIso :
    ((tilde.functor Γ(X, f ⁻¹ᵁ U)).mapHomologicalComplex c).obj
        (wholeChartCoordinateComplex c f hU K) ≅ wholeChartSheafComplex c f hU K := by
  have (n : ι) : ((wholeChartSheafComplex c f hU K).X n).IsQuasicoherent :=
    sourceChart_quasicoherent f hU (K.X n)
  exact coordinateComplexIso _ c _

/-- Every original source stalk retains its actual open-chart scalar action. -/
def wholeChartStalkIso (q : Spec Γ(X, f ⁻¹ᵁ U)) :
    ((tilde.functor Γ(X, f ⁻¹ᵁ U) ⋙ functor q).mapHomologicalComplex c).obj
        (wholeChartCoordinateComplex c f hU K) ≅
      ((functor (sourceChart f hU q) ⋙ ModuleCat.restrictScalars
        (inv ((sourceChart f hU).stalkMap q)).hom).mapHomologicalComplex c).obj K :=
  ((functor q).mapHomologicalComplex c).mapIso (wholeChartTildeIso f hU c K) ≪≫
    (openRestrictionComplexIso (sourceChart f hU) q c).app K

/-- The original complex maps satisfy the actual differential square under relative QC. -/
theorem wholeChartStalkIso_hom_comm (q : Spec Γ(X, f ⁻¹ᵁ U)) (n m : ι) :
    (((tilde.functor Γ(X, f ⁻¹ᵁ U) ⋙ functor q).mapHomologicalComplex c).obj
        (wholeChartCoordinateComplex c f hU K)).d n m ≫
      (wholeChartStalkIso f hU c K q).hom.f m =
    (wholeChartStalkIso f hU c K q).hom.f n ≫
      (((functor (sourceChart f hU q) ⋙ ModuleCat.restrictScalars
        (inv ((sourceChart f hU).stalkMap q)).hom).mapHomologicalComplex c).obj K).d n m :=
  ((wholeChartStalkIso f hU c K q).hom.comm n m).symm

/-- Actual open base change presents the original global pushforward from relative QC. -/
def wholeChartCoordinatePushforwardIso :
    ((tilde.functor Γ(X, f ⁻¹ᵁ U) ⋙
        pushforward (coordinateMap f)).mapHomologicalComplex c).obj
        (wholeChartCoordinateComplex c f hU K) ≅
      ((pushforward f ⋙ restrictFunctor hU.fromSpec).mapHomologicalComplex c).obj K :=
  ((pushforward (coordinateMap f)).mapHomologicalComplex c).mapIso
      (wholeChartTildeIso f hU c K) ≪≫
    ((FiniteRestriction.wholeChartPushforwardComplexIso f hU c).app K).symm

/-- The actual global finite pushforward stalk comparison needs only whole-open QC. -/
def wholeChartPushforwardStalkIso (p : Spec Γ(Y, U)) :
    ((tilde.functor Γ(X, f ⁻¹ᵁ U) ⋙ pushforward (coordinateMap f) ⋙
        functor p).mapHomologicalComplex c).obj (wholeChartCoordinateComplex c f hU K) ≅
      ((pushforward f ⋙ functor (hU.fromSpec p) ⋙ ModuleCat.restrictScalars
        (inv (hU.fromSpec.stalkMap p)).hom).mapHomologicalComplex c).obj K :=
  ((functor p).mapHomologicalComplex c).mapIso
      (wholeChartCoordinatePushforwardIso f hU c K) ≪≫
    (openRestrictionComplexIso hU.fromSpec p c).app
      ((pushforward f).mapHomologicalComplex c |>.obj K)

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent.RelativeAffine
