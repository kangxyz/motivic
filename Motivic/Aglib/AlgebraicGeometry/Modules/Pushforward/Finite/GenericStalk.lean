/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Relative
public import Motivic.Aglib.AlgebraicGeometry.Intersection.WholeFiberTorStalk
public import Motivic.Aglib.AlgebraicGeometry.Stalk.Generic.Localization
public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.FlatBaseChangeLocalization
public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.AmbientLength

/-!
# Generic stalks of the original finite pushforward from relative quasi-coherence

The original finite pushforward has a genuine tilde presentation on the chosen
whole target affine open. It is constructed from quasi-coherence only on the
whole inverse image, the actual open base-change comparison and affine
pushforward. The same coordinate module presents both original target stalks
along specialization, through their literal section germs. Localizing at the
actual generic prime therefore gives the original global generic stalk. No
quasi-coherence of the ambient source sheaf is assumed or asserted.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.Pushforward.RelativeFinite
open _root_.AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open _root_.AlgebraicGeometry.Scheme.Modules.QuasiCoherent.Affine

open Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Hom.FiniteAffineChart
open _root_.AlgebraicGeometry.Scheme.Modules.Stalk
open _root_.AlgebraicGeometry.Scheme.Intersection

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
  (V : Y.affineOpens) (N : X.Modules)
  [((restrictFunctor (f ⁻¹ᵁ V).ι).obj N).IsQuasicoherent]

/-- One actual coordinate module is used at every target point in the chosen
open: whole-inverse-image sections, restricted along the original section map. -/
def originalPushforwardChartModule : ModuleCat.{u} Γ(Y, V) :=
  (ModuleCat.restrictScalars (f.app V).hom).obj
    (moduleSpecΓFunctor.obj ((restrictFunctor (sourceChart f V.2)).obj N))

/-- The original finite pushforward on the literal target spectrum chart is the
tilde sheaf of the same actual whole-inverse-image coordinate module. -/
def originalPushforwardSpecTildeIso :
    (tilde.functor Γ(Y, V)).obj (originalPushforwardChartModule f V N) ≅
      (restrictFunctor V.2.fromSpec).obj ((pushforward f).obj N) := by
  have := RelativeAffine.sourceChart_quasicoherent f V.2 N
  exact (Affine.tildePushforwardIso (f.app V)).symm.app _ ≪≫
    (pushforward (coordinateMap f)).mapIso
      (asIso (((restrictFunctor (sourceChart f V.2)).obj N).fromTildeΓ)) ≪≫
    ((FiniteRestriction.wholeChartPushforwardIso f V.2).app N).symm

/-- The same sheaf comparison on the original affine open retains the literal
restriction of the original global finite pushforward. -/
def originalPushforwardChartTildeIso :
    (OpenTilde.chartTilde V).obj (originalPushforwardChartModule f V N) ≅
      (restrictFunctor V.1.ι).obj ((pushforward f).obj N) :=
  (restrictFunctor V.2.isoSpec.hom).mapIso
      (originalPushforwardSpecTildeIso f V N) ≪≫
    (restrictFunctorComp V.2.isoSpec.hom V.2.fromSpec).symm.app _ ≪≫
    (restrictFunctorCongr V.2.isoSpec_hom_fromSpec).app _

/-- Relative quasi-coherence of the original finite pushforward is derived on
this actual target open, without a global claim about either ambient sheaf. -/
theorem originalPushforward_relativeQuasicoherent :
    ((restrictFunctor V.1.ι).obj ((pushforward f).obj N)).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent V.1.toScheme.ringCatSheaf).prop_of_iso
    (originalPushforwardChartTildeIso f V N) (by
      dsimp [OpenTilde.chartTilde]
      infer_instance)

/-- Actual original pushforward stalks on the whole target chart are extension
of one coordinate module along their original section germs. -/
def originalPushforwardChartStalkIso (x : Y) (hx : x ∈ V.1) :
    (functor x).obj ((pushforward f).obj N) ≅
      (ModuleCat.extendScalars (Y.presheaf.germ V.1 x hx).hom).obj
        (originalPushforwardChartModule f V N) :=
  (openRestrictionOriginalIso V.1.ι ⟨x, hx⟩ ((pushforward f).obj N)).symm ≪≫
    (ModuleCat.restrictScalars (V.1.ι.stalkMap ⟨x, hx⟩).hom).mapIso
      ((functor (X := V.1.toScheme) ⟨x, hx⟩).mapIso
        (originalPushforwardChartTildeIso f V N).symm) ≪≫
    affineOpenTildeStalkIso V ⟨x, hx⟩ (originalPushforwardChartModule f V N)

/-- Every generization of an original point in the affine chart belongs to
that identical chart. This includes each original global component generic. -/
theorem specialization_mem_targetChart (x y : Y) (hx : x ∈ V.1) (hyx : y ⤳ x) :
    y ∈ V.1 := hyx.mem_open V.1.isOpen hx

/-- The actual structure-stalk specialization commutes with the two original
section germs on this common chart. -/
theorem originalPushforwardChart_germ_specializes (x y : Y)
    (hx : x ∈ V.1) (hyx : y ⤳ x) :
    (Y.presheaf.stalkSpecializes hyx).hom.comp (Y.presheaf.germ V.1 x hx).hom =
      (Y.presheaf.germ V.1 y (specialization_mem_targetChart V x y hx hyx)).hom :=
  congrArg CommRingCat.Hom.hom (Y.presheaf.germ_stalkSpecializes hx hyx)

/-- Extension along the actual specialization isomorphically compares the
original pushforward stalks, using their single genuine chart presentation. -/
def originalPushforwardStalkSpecializationIso (x y : Y)
    (hx : x ∈ V.1) (hyx : y ⤳ x) :
    (ModuleCat.extendScalars (Y.presheaf.stalkSpecializes hyx).hom).obj
        ((functor x).obj ((pushforward f).obj N)) ≅
      (functor y).obj ((pushforward f).obj N) :=
  (ModuleCat.extendScalars (Y.presheaf.stalkSpecializes hyx).hom).mapIso
      (originalPushforwardChartStalkIso f V N x hx) ≪≫
    (ModuleCat.extendScalarsComp (Y.presheaf.germ V.1 x hx).hom
      (Y.presheaf.stalkSpecializes hyx).hom).symm.app
        (originalPushforwardChartModule f V N) ≪≫
    eqToIso (congrArg (fun g => (ModuleCat.extendScalars g).obj
      (originalPushforwardChartModule f V N))
        (originalPushforwardChart_germ_specializes V x y hx hyx)) ≪≫
    (originalPushforwardChartStalkIso f V N y
      (specialization_mem_targetChart V x y hx hyx)).symm

/-- The specialization comparison respects the common affine presentation:
its actual scalar-extension square commutes before generic localization. -/
theorem originalPushforwardStalkSpecializationIso_chart_square (x y : Y)
    (hx : x ∈ V.1) (hyx : y ⤳ x) :
    (originalPushforwardStalkSpecializationIso f V N x y hx hyx).hom ≫
        (originalPushforwardChartStalkIso f V N y
          (specialization_mem_targetChart V x y hx hyx)).hom =
      (ModuleCat.extendScalars (Y.presheaf.stalkSpecializes hyx).hom).map
          (originalPushforwardChartStalkIso f V N x hx).hom ≫
        (ModuleCat.extendScalarsComp (Y.presheaf.germ V.1 x hx).hom
          (Y.presheaf.stalkSpecializes hyx).hom).inv.app
            (originalPushforwardChartModule f V N) ≫
        (eqToIso (congrArg (fun g => (ModuleCat.extendScalars g).obj
          (originalPushforwardChartModule f V N))
            (originalPushforwardChart_germ_specializes V x y hx hyx))).hom := by
  simp only [originalPushforwardStalkSpecializationIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Literal localization of the original pushforward stalk at its actual
local generic prime recovers the same global finite-pushed sheaf at that generic,
restricted through the canonical original generic-stalk ring isomorphism. -/
def originalPushforwardStalkGenericIso (x : Y) (hx : x ∈ V.1)
    (y : {y : genericPoints Y // y.1 ⤳ x}) :
    ModuleCat.of (Localization.AtPrime (genericStalkLocalizationPrime Y x y).asIdeal)
        (LocalizedModule (genericStalkLocalizationPrime Y x y).asIdeal.primeCompl
          ((functor x).obj ((pushforward f).obj N))) ≅
      (ModuleCat.restrictScalars (genericStalkLocalizationIso Y x y).inv.hom).obj
        ((functor y.1.1).obj ((pushforward f).obj N)) := by
  let M := (functor x).obj ((pushforward f).obj N)
  let g := (Y.presheaf.stalkSpecializes y.2).hom
  let e := (genericStalkLocalizationIso Y x y).commRingCatIsoToRingEquiv
  have hg : e.toRingHom.comp g = algebraMap (Y.presheaf.stalk x)
      (Localization.AtPrime (genericStalkLocalizationPrime Y x y).asIdeal) :=
    congrArg CommRingCat.Hom.hom (stalkSpecializes_genericStalkLocalizationIso Y x y)
  exact _root_.ModuleCat.TorComparison.localizedModuleExtendScalarsIso _ M ≪≫
    eqToIso (congrArg (fun r => (ModuleCat.extendScalars r).obj M) hg.symm) ≪≫
    (ModuleCat.extendScalarsComp g e.toRingHom).app M ≪≫
    (ModuleCat.extendScalars e.toRingHom).mapIso
      (originalPushforwardStalkSpecializationIso f V N x y.1.1 hx y.2) ≪≫
    extendScalarsRingEquivIso e _

/-- Generic localization preserves the original full structure-stalk length;
no reduction to a residue-field dimension is made. -/
theorem originalPushforwardStalkGeneric_length (x : Y) (hx : x ∈ V.1)
    (y : {y : genericPoints Y // y.1 ⤳ x}) :
    Module.length (Localization.AtPrime (genericStalkLocalizationPrime Y x y).asIdeal)
        (LocalizedModule (genericStalkLocalizationPrime Y x y).asIdeal.primeCompl
          ((functor x).obj ((pushforward f).obj N))) =
      Module.length (Y.presheaf.stalk y.1.1)
        ((functor y.1.1).obj ((pushforward f).obj N)) := by
  rw [(originalPushforwardStalkGenericIso f V N x hx y).toLinearEquiv.length_eq]
  exact _root_.ModuleCat.length_restrictScalars_of_surjective _
    (ConcreteCategory.bijective_of_isIso (genericStalkLocalizationIso Y x y).inv).2 _

end AlgebraicGeometry.Scheme.Modules.Pushforward.RelativeFinite
