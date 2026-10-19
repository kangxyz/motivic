/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Restriction.Basic
public import Motivic.Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.TildeBaseChange.Cocycle
public import Motivic.Aglib.AlgebraicGeometry.Modules.Restriction.Open.RestrictionAdjunctionCoherence

/-!
# Coherence of tilde restriction on actual affine opens

The canonical affine-chart squares retain their actual section transports.
The geometric restriction unitors and associators are compared with the
corresponding scalar-extension maps on the original coordinate modules.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent.Affine.OpenTilde
open _root_.AlgebraicGeometry.Scheme.Modules.Restriction

variable {X : Scheme.{u}} {U V L : X.affineOpens}

/-- The original section restriction, retaining its affine-open arguments for scalar instances. -/
def sectionRestriction (h : U ≤ V) : Γ(X, V) ⟶ Γ(X, U) :=
  X.presheaf.map (homOfLE (show U.1 ≤ V.1 from h)).op

/-- The original section map between affine opens induces an actual open immersion. -/
instance isOpenImmersion_specMap_sectionRestriction (h : U ≤ V) :
    IsOpenImmersion (Spec.map (sectionRestriction h)) :=
  isOpenImmersion_specMap_restriction (U := U) (V := V) h

/-- Successive actual affine section restrictions also induce the actual open composite. -/
instance isOpenImmersion_specMap_sectionRestriction_comp (h : U ≤ V) (k : V ≤ L) :
    IsOpenImmersion (Spec.map (sectionRestriction k ≫ sectionRestriction h)) := by
  rw [Spec.map_comp]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual affine-open comparison consists of its geometric square and the
original affine tilde/open comparison. -/
theorem restrictionIso_hom_app (h : U ≤ V) (M : ModuleCat.{u} Γ(X, V)) :
    (restrictionIso h).hom.app M =
      (chartRestrictionSquareIso h).hom.app (tilde M) ≫
        (restrictFunctor U.2.isoSpec.hom).map
          ((TildeBaseChange.restrictionIso
            (sectionRestriction (h))).hom.app M) := by
  dsimp only [restrictionIso]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.id_comp, Category.comp_id]
  exact Category.id_comp _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual affine chart square identifies its original image opens. -/
theorem chartRestrictionSquare_image (h : U ≤ V) (O : U.1.toScheme.Opens) :
    Spec.map (sectionRestriction (h)) ''ᵁ
        U.2.isoSpec.hom ''ᵁ O =
      V.2.isoSpec.hom ''ᵁ X.homOfLE h ''ᵁ O := by
  let := isOpenImmersion_specMap_restriction (U := U) (V := V) h
  change Spec.map (X.presheaf.map (homOfLE (show U.1 ≤ V.1 from h)).op) ''ᵁ
    U.2.isoSpec.hom ''ᵁ O = _
  simp only [← Scheme.Hom.comp_image, isoSpec_restriction_square h]

set_option backward.isDefEq.respectTransparency false in
/-- On every actual open, the chart square is the canonical section equality transport. -/
theorem chartRestrictionSquareIso_hom_app_app (h : U ≤ V)
    (M : (Spec Γ(X, V)).Modules) (O : U.1.toScheme.Opens) :
    ((chartRestrictionSquareIso h).hom.app M).app O =
      M.presheaf.map (eqToHom (chartRestrictionSquare_image h O)).op := by
  simp only [chartRestrictionSquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Hom.comp_app, restrictFunctorComp_inv_app_app,
    restrictFunctorCongr_hom_app_app, restrictFunctorComp_hom_app_app]
  simp only [← CategoryTheory.Functor.map_comp]
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- The actual chart square is natural on the original two restriction routes. -/
@[reassoc] theorem chartRestrictionSquareIso_naturality (h : U ≤ V)
    {M N : (Spec Γ(X, V)).Modules} (φ : M ⟶ N) :
    (restrictFunctor (X.homOfLE h)).map ((restrictFunctor V.2.isoSpec.hom).map φ) ≫
      (chartRestrictionSquareIso h).hom.app N =
    (chartRestrictionSquareIso h).hom.app M ≫
      (restrictFunctor U.2.isoSpec.hom).map
        ((restrictFunctor (Spec.map (sectionRestriction h))).map φ) :=
  (chartRestrictionSquareIso h).hom.naturality φ

/-- The canonical geometric identity comparison on the actual affine open. -/
def openIdentityIso (U : X.Opens) :
    restrictFunctor (X.homOfLE (show U ≤ U from le_rfl)) ≅ 𝟭 U.toScheme.Modules :=
  restrictFunctorCongr (X.homOfLE_rfl U) ≪≫ restrictFunctorId

/-- The canonical geometric associator for actual nested affine opens. -/
def openCompositionIso {U V L : X.Opens} (h : U ≤ V) (k : V ≤ L) :
    restrictFunctor (X.homOfLE (h.trans k)) ≅
      restrictFunctor (X.homOfLE k) ⋙ restrictFunctor (X.homOfLE h) :=
  restrictFunctorCongr (X.homOfLE_homOfLE h k).symm ≪≫
    restrictFunctorComp (X.homOfLE h) (X.homOfLE k)

/-- Original section restrictions have the genuine categorical composition equation. -/
theorem sectionRestriction_comp (h : U ≤ V) (k : V ≤ L) :
    sectionRestriction (k) ≫
      sectionRestriction (h) =
        sectionRestriction (h.trans k) :=
  (X.presheaf.map_comp (homOfLE (show V.1 ≤ L.1 from k)).op
    (homOfLE (show U.1 ≤ V.1 from h)).op).symm

/-- The geometric associator on spectra uses the actual original section-composition equality. -/
def specCompositionIso (h : U ≤ V) (k : V ≤ L) :
    restrictFunctor (Spec.map
      (sectionRestriction (h.trans k))) ≅
      restrictFunctor (Spec.map (sectionRestriction (k))) ⋙
        restrictFunctor (Spec.map (sectionRestriction (h))) :=
  restrictFunctorCongr (by rw [← sectionRestriction_comp h k, Spec.map_comp]) ≪≫
    restrictFunctorComp _ _

set_option backward.isDefEq.respectTransparency false in
/-- The two actual affine-chart square transports obey geometric composition on every sheaf. -/
@[reassoc] theorem chartRestrictionSquareIso_hom_comp (h : U ≤ V) (k : V ≤ L)
    (M : (Spec Γ(X, L)).Modules) :
    (openCompositionIso h k).hom.app ((restrictFunctor L.2.isoSpec.hom).obj M) ≫
      (restrictFunctor (X.homOfLE h)).map ((chartRestrictionSquareIso k).hom.app M) ≫
      (chartRestrictionSquareIso h).hom.app
        ((restrictFunctor (Spec.map
          (sectionRestriction (k)))).obj M) =
    (chartRestrictionSquareIso (h.trans k)).hom.app M ≫
      (restrictFunctor U.2.isoSpec.hom).map ((specCompositionIso h k).hom.app M) := by
  apply Scheme.Modules.hom_ext
  intro O
  simp only [openCompositionIso, specCompositionIso, Iso.trans_hom,
    NatTrans.comp_app, Hom.comp_app, restrictFunctorCongr_hom_app_app,
    restrictFunctorComp_hom_app_app,
    AdjunctionCoherence.restrictFunctor_map_app,
    chartRestrictionSquareIso_hom_app_app, restrict_map]
  simp only [← CategoryTheory.Functor.map_comp]
  congr 1

/-- The actual section map of an unchanged affine open is the categorical identity. -/
theorem sectionRestriction_refl (U : X.affineOpens) :
    sectionRestriction (show U ≤ U from le_rfl) = 𝟙 Γ(X, U) :=
  X.presheaf.map_id _

/-- The genuine geometric identity comparison for the actual section restriction spectrum. -/
def specIdentityIso (U : X.affineOpens) :
    restrictFunctor (Spec.map
      (sectionRestriction (show U ≤ U from le_rfl))) ≅
        𝟭 (Spec Γ(X, U)).Modules :=
  restrictFunctorCongr (by rw [sectionRestriction_refl, Spec.map_id]) ≪≫ restrictFunctorId

set_option backward.isDefEq.respectTransparency false in
/-- The actual chart square commutes with both genuine geometric identity comparisons. -/
theorem chartRestrictionSquareIso_hom_refl (U : X.affineOpens)
    (M : (Spec Γ(X, U)).Modules) :
    (chartRestrictionSquareIso (show U ≤ U from le_rfl)).hom.app M ≫
      (restrictFunctor U.2.isoSpec.hom).map ((specIdentityIso U).hom.app M) =
    (openIdentityIso (X := X) U.1).hom.app ((restrictFunctor U.2.isoSpec.hom).obj M) := by
  apply Scheme.Modules.hom_ext
  intro O
  simp only [openIdentityIso, specIdentityIso, Iso.trans_hom,
    NatTrans.comp_app, Hom.comp_app, restrictFunctorCongr_hom_app_app,
    restrictFunctorId_hom_app_app,
    AdjunctionCoherence.restrictFunctor_map_app,
    chartRestrictionSquareIso_hom_app_app, restrict_map]
  simp only [← CategoryTheory.Functor.map_comp]
  congr 1

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Equality of actual affine ring maps transports the same canonical tilde comparison. -/
theorem tildeRestrictionIso_hom_congr {A B : CommRingCat.{u}}
    (φ ψ : A ⟶ B) [IsOpenImmersion (Spec.map φ)] [IsOpenImmersion (Spec.map ψ)]
    (e : φ = ψ) (M : ModuleCat.{u} A) :
    (restrictFunctorCongr (congrArg Spec.map e)).hom.app (tilde M) ≫
      (TildeBaseChange.restrictionIso ψ).hom.app M =
    (TildeBaseChange.restrictionIso φ).hom.app M ≫
      tilde.map (eqToHom
        (congrArg (fun q : A ⟶ B => (ModuleCat.extendScalars q.hom).obj M) e)) := by
  subst ψ
  rw [AdjunctionCoherence.restrictFunctorCongr_refl]
  simp only [NatTrans.id_app, Category.id_comp, eqToHom_refl, tilde.map_id]
  exact (Category.comp_id _).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual spectrum identity transport factors through the canonical tilde identity map. -/
theorem specIdentityIso_hom (U : X.affineOpens) (M : (Spec Γ(X, U)).Modules) :
    (specIdentityIso U).hom.app M =
      (restrictFunctorCongr (congrArg Spec.map (sectionRestriction_refl U))).hom.app M ≫
        (TildeBaseChange.identityRestrictionIso Γ(X, U)).hom.app M := by
  apply Scheme.Modules.hom_ext
  intro O
  simp only [specIdentityIso, TildeBaseChange.identityRestrictionIso, Iso.trans_hom,
    NatTrans.comp_app, Hom.comp_app, restrictFunctorCongr_hom_app_app,
    restrictFunctorId_hom_app_app]
  simp only [← CategoryTheory.Functor.map_comp]
  congr 1

/-- The actual scalar-extension unitor includes the original section-map equality. -/
def scalarIdentityIso (U : X.affineOpens) (M : ModuleCat.{u} Γ(X, U)) :
    (ModuleCat.extendScalars
      (sectionRestriction (show U ≤ U from le_rfl)).hom).obj M ≅ M :=
  eqToIso (congrArg (fun q : Γ(X, U) ⟶ Γ(X, U) => (ModuleCat.extendScalars q.hom).obj M)
    (sectionRestriction_refl U)) ≪≫ (ModuleCat.extendScalarsId Γ(X, U)).app M

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual section-spectrum tilde comparison obeys its original scalar unitor. -/
theorem specRestrictionIso_hom_refl (U : X.affineOpens) (M : ModuleCat.{u} Γ(X, U)) :
    (TildeBaseChange.restrictionIso
      (sectionRestriction (show U ≤ U from le_rfl))).hom.app M ≫
      tilde.map (scalarIdentityIso U M).hom = (specIdentityIso U).hom.app (tilde M) := by
  erw [scalarIdentityIso, Iso.trans_hom, tilde.map_comp, ← Category.assoc,
    ← tildeRestrictionIso_hom_congr _ _ (sectionRestriction_refl U) M,
    Category.assoc, TildeBaseChange.restrictionIso_hom_id Γ(X, U) M,
    ← specIdentityIso_hom U (tilde M)]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Actual affine-open tilde restriction respects the original geometric and scalar unitors. -/
theorem restrictionIso_hom_refl (U : X.affineOpens) (M : ModuleCat.{u} Γ(X, U)) :
    (restrictionIso (show U ≤ U from le_rfl)).hom.app M ≫
      (chartTilde U).map (scalarIdentityIso U M).hom =
    (openIdentityIso (X := X) U.1).hom.app ((chartTilde U).obj M) := by
  rw [restrictionIso_hom_app, Category.assoc]
  change _ ≫ ((restrictFunctor U.2.isoSpec.hom).map
    ((TildeBaseChange.restrictionIso
      (sectionRestriction (show U ≤ U from le_rfl))).hom.app M) ≫
    (restrictFunctor U.2.isoSpec.hom).map (tilde.map (scalarIdentityIso U M).hom)) = _
  rw [← CategoryTheory.Functor.map_comp, specRestrictionIso_hom_refl]
  exact chartRestrictionSquareIso_hom_refl U (tilde M)

set_option backward.isDefEq.respectTransparency false in
/-- The actual spectral composition transport is the canonical tilde associator
preceded by the original section-composition equality. -/
theorem specCompositionIso_hom (h : U ≤ V) (k : V ≤ L)
    (M : (Spec Γ(X, L)).Modules) :
    (specCompositionIso h k).hom.app M =
      (restrictFunctorCongr (congrArg Spec.map (sectionRestriction_comp h k).symm)).hom.app M ≫
        (TildeBaseChange.compositionRestrictionIso (sectionRestriction k)
          (sectionRestriction h)).hom.app M := by
  apply Scheme.Modules.hom_ext
  intro O
  simp only [specCompositionIso, TildeBaseChange.compositionRestrictionIso, Iso.trans_hom,
    NatTrans.comp_app, Hom.comp_app, restrictFunctorCongr_hom_app_app,
    restrictFunctorComp_hom_app_app]
  simp only [← CategoryTheory.Functor.map_comp]
  congr 1

/-- The genuine scalar associator starts at the actual direct section restriction. -/
def scalarCompositionIso (h : U ≤ V) (k : V ≤ L) (M : ModuleCat.{u} Γ(X, L)) :
    (ModuleCat.extendScalars (sectionRestriction (h.trans k)).hom).obj M ≅
      (ModuleCat.extendScalars (sectionRestriction h).hom).obj
        ((ModuleCat.extendScalars (sectionRestriction k).hom).obj M) :=
  eqToIso (congrArg (fun q : Γ(X, L) ⟶ Γ(X, U) => (ModuleCat.extendScalars q.hom).obj M)
    (sectionRestriction_comp h k).symm) ≪≫
      (ModuleCat.extendScalarsComp (sectionRestriction k).hom (sectionRestriction h).hom).app M

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Canonical tilde restriction on the actual section spectra obeys the genuine
geometric and scalar composition maps. -/
theorem specRestrictionIso_hom_comp (h : U ≤ V) (k : V ≤ L)
    (M : ModuleCat.{u} Γ(X, L)) :
    (specCompositionIso h k).hom.app (tilde M) ≫
      (restrictFunctor (Spec.map (sectionRestriction h))).map
        ((TildeBaseChange.restrictionIso (sectionRestriction k)).hom.app M) ≫
      (TildeBaseChange.restrictionIso (sectionRestriction h)).hom.app
        ((ModuleCat.extendScalars (sectionRestriction k).hom).obj M) =
    (TildeBaseChange.restrictionIso (sectionRestriction (h.trans k))).hom.app M ≫
      tilde.map (scalarCompositionIso h k M).hom := by
  erw [specCompositionIso_hom h k (tilde M), Category.assoc,
    TildeBaseChange.restrictionIso_hom_comp_app
      (sectionRestriction k) (sectionRestriction h) M, ← Category.assoc,
    tildeRestrictionIso_hom_congr _ _ (sectionRestriction_comp h k).symm M,
    Category.assoc, ← tilde.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The original affine-open tilde comparisons satisfy the genuine geometric and
scalar composition equation, without a supplied cocycle. -/
@[reassoc] theorem restrictionIso_hom_comp (h : U ≤ V) (k : V ≤ L)
    (M : ModuleCat.{u} Γ(X, L)) :
    (openCompositionIso h k).hom.app ((chartTilde L).obj M) ≫
      (restrictFunctor (X.homOfLE h)).map ((restrictionIso k).hom.app M) ≫
      (restrictionIso h).hom.app ((ModuleCat.extendScalars (sectionRestriction k).hom).obj M) =
    (restrictionIso (h.trans k)).hom.app M ≫
      (chartTilde U).map (scalarCompositionIso h k M).hom := by
  simp only [restrictionIso_hom_app, CategoryTheory.Functor.map_comp, Category.assoc]
  erw [chartRestrictionSquareIso_naturality_assoc h
    ((TildeBaseChange.restrictionIso (sectionRestriction k)).hom.app M)]
  erw [chartRestrictionSquareIso_hom_comp_assoc h k (tilde M)]
  erw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    specRestrictionIso_hom_comp h k M]
  exact congrArg (fun z => (chartRestrictionSquareIso (h.trans k)).hom.app (tilde M) ≫ z)
    ((restrictFunctor U.2.isoSpec.hom).map_comp
      ((TildeBaseChange.restrictionIso (sectionRestriction (h.trans k))).hom.app M)
      (tilde.map (scalarCompositionIso h k M).hom))

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent.Affine.OpenTilde
