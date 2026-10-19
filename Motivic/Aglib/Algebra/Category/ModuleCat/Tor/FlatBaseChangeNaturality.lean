/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.FlatBaseChange

/-!
# Naturality of the canonical flat Tor comparison

The flat base-change comparison can be computed on any projective resolution.
The comparison is natural in both module arguments and independent of the
choice of projective resolution. All maps are the actual scalar-extension maps.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u

namespace ModuleCat.TorComparison

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Flat scalar extension commutes naturally with homology. -/
@[reassoc]
theorem flatExtendHomologyIso_hom_naturality (f : R →+* S) (hf : f.Flat)
    {K L : ChainComplex (ModuleCat.{u} R) ℕ} (φ : K ⟶ L) (n : ℕ) :
    (ModuleCat.extendScalars f).map (HomologicalComplex.homologyMap φ n) ≫
        (flatExtendHomologyIso f hf L n).hom =
      (flatExtendHomologyIso f hf K n).hom ≫
        HomologicalComplex.homologyMap
          (((ModuleCat.extendScalars f).mapHomologicalComplex _).map φ) n := by
  let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  exact ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ n).map φ) (ModuleCat.extendScalars f)

/-- The tensorator comparison is natural in the complex. -/
@[reassoc]
theorem extendTensorComplexIso_hom_naturality (f : R →+* S)
    (M : ModuleCat.{u} R) {K L : ChainComplex (ModuleCat.{u} R) ℕ} (φ : K ⟶ L) :
    ((ModuleCat.extendScalars f).mapHomologicalComplex _).map
        (((tensorLeft M).mapHomologicalComplex _).map φ) ≫
        (extendTensorComplexIso f M L).hom =
      (extendTensorComplexIso f M K).hom ≫
        ((tensorLeft ((ModuleCat.extendScalars f).obj M)).mapHomologicalComplex _).map
          (((ModuleCat.extendScalars f).mapHomologicalComplex _).map φ) :=
  (NatIso.mapHomologicalComplex
    (Functor.Monoidal.commTensorLeft (ModuleCat.extendScalars f) M).symm _).hom.naturality φ

/-- The homological part of flat tensor base change, before resolution comparison. -/
noncomputable def flatExtendTensorHomologyIso (f : R →+* S) (hf : f.Flat)
    (M : ModuleCat.{u} R) (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    (ModuleCat.extendScalars f).obj
        ((((tensorLeft M).mapHomologicalComplex _).obj K).homology n) ≅
      ((((tensorLeft ((ModuleCat.extendScalars f).obj M)).mapHomologicalComplex _).obj
        (((ModuleCat.extendScalars f).mapHomologicalComplex _).obj K)).homology n) :=
  flatExtendHomologyIso f hf (((tensorLeft M).mapHomologicalComplex _).obj K) n ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat S) _ n).mapIso
      (extendTensorComplexIso f M K)

set_option backward.isDefEq.respectTransparency false in
/-- The homological comparison respects every chain map. -/
@[reassoc]
theorem flatExtendTensorHomologyIso_hom_naturality (f : R →+* S) (hf : f.Flat)
    (M : ModuleCat.{u} R) {K L : ChainComplex (ModuleCat.{u} R) ℕ} (φ : K ⟶ L) (n : ℕ) :
    (ModuleCat.extendScalars f).map
        (HomologicalComplex.homologyMap (((tensorLeft M).mapHomologicalComplex _).map φ) n) ≫
        (flatExtendTensorHomologyIso f hf M L n).hom =
      (flatExtendTensorHomologyIso f hf M K n).hom ≫
        HomologicalComplex.homologyMap
          (((tensorLeft ((ModuleCat.extendScalars f).obj M)).mapHomologicalComplex _).map
            (((ModuleCat.extendScalars f).mapHomologicalComplex _).map φ)) n := by
  simp only [flatExtendTensorHomologyIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [flatExtendHomologyIso_hom_naturality_assoc]
  have h := congrArg ((HomologicalComplex.homologyFunctor (ModuleCat S) _ n).map)
    (extendTensorComplexIso_hom_naturality f M φ)
  simp only [Functor.map_comp] at h
  exact congrArg ((flatExtendHomologyIso f hf
    (((tensorLeft M).mapHomologicalComplex _).obj K) n).hom ≫ ·) h

/-- Compute canonical flat Tor base change with an arbitrary projective resolution. -/
noncomputable def flatBaseChangeTorIsoOfResolution (f : R →+* S) (hf : f.Flat)
    (M : ModuleCat.{u} R) {N : ModuleCat.{u} R} (P : ProjectiveResolution N) (n : ℕ) :
    (ModuleCat.extendScalars f).obj (((Tor (ModuleCat R) n).obj M).obj N) ≅
      ((Tor (ModuleCat S) n).obj ((ModuleCat.extendScalars f).obj M)).obj
        ((ModuleCat.extendScalars f).obj N) :=
  (ModuleCat.extendScalars f).mapIso
      (P.isoLeftDerivedObj ((tensoringLeft (ModuleCat R)).obj M) n) ≪≫
    flatExtendTensorHomologyIso f hf M P.complex n ≪≫
    ((flatExtendProjectiveResolution f hf P).isoLeftDerivedObj
      ((tensoringLeft (ModuleCat S)).obj ((ModuleCat.extendScalars f).obj M)) n).symm

/-- Scalar extension carries a comparison lift to a comparison lift. -/
theorem flatExtendProjectiveResolution_lift_commutes (f : R →+* S) (hf : f.Flat)
    {N N' : ModuleCat.{u} R} (v : N ⟶ N')
    (P : ProjectiveResolution N) (Q : ProjectiveResolution N')
    (φ : P.complex ⟶ Q.complex) (hφ : φ.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ v) :
    (((ModuleCat.extendScalars f).mapHomologicalComplex _).map φ).f 0 ≫
        (flatExtendProjectiveResolution f hf Q).π.f 0 =
      (flatExtendProjectiveResolution f hf P).π.f 0 ≫ (ModuleCat.extendScalars f).map v := by
  change (ModuleCat.extendScalars f).map (φ.f 0) ≫
      (ModuleCat.extendScalars f).map (Q.π.f 0) =
    (ModuleCat.extendScalars f).map (P.π.f 0) ≫ (ModuleCat.extendScalars f).map v
  erw [← Functor.map_comp, hφ, Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Flat Tor comparison respects any map of projective resolutions over a module map. -/
@[reassoc]
theorem flatBaseChangeTorIsoOfResolution_hom_naturality (f : R →+* S) (hf : f.Flat)
    (M : ModuleCat.{u} R) {N N' : ModuleCat.{u} R} (v : N ⟶ N')
    (P : ProjectiveResolution N) (Q : ProjectiveResolution N')
    (φ : P.complex ⟶ Q.complex) (hφ : φ.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ v) (n : ℕ) :
    (ModuleCat.extendScalars f).map (((Tor (ModuleCat R) n).obj M).map v) ≫
        (flatBaseChangeTorIsoOfResolution f hf M Q n).hom =
      (flatBaseChangeTorIsoOfResolution f hf M P n).hom ≫
        ((Tor (ModuleCat S) n).obj ((ModuleCat.extendScalars f).obj M)).map
          ((ModuleCat.extendScalars f).map v) := by
  have h₁ := P.isoLeftDerivedObj_hom_naturality v Q φ hφ (tensorLeft M) n
  have h₂ := flatExtendTensorHomologyIso_hom_naturality f hf M φ n
  have h₃ := (flatExtendProjectiveResolution f hf P).isoLeftDerivedObj_inv_naturality
    ((ModuleCat.extendScalars f).map v) (flatExtendProjectiveResolution f hf Q)
    (((ModuleCat.extendScalars f).mapHomologicalComplex _).map φ)
    (flatExtendProjectiveResolution_lift_commutes f hf v P Q φ hφ)
    (tensorLeft ((ModuleCat.extendScalars f).obj M)) n
  simp only [flatBaseChangeTorIsoOfResolution, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Category.assoc]
  erw [← Functor.map_comp_assoc, h₁, Functor.map_comp, Category.assoc]
  erw [h₃]
  have h₂' := congrArg (· ≫ ((flatExtendProjectiveResolution f hf Q).isoLeftDerivedObj
      (tensorLeft ((ModuleCat.extendScalars f).obj M)) n).inv) h₂
  have h₂'' := congrArg ((ModuleCat.extendScalars f).map
      (P.isoLeftDerivedObj (tensorLeft M) n).hom ≫ ·) h₂'
  dsimp only [Functor.comp_map, HomologicalComplex.homologyFunctor] at *
  exact h₂''.trans (by rfl)

/-- At the standard chosen resolution this is exactly the previously constructed comparison. -/
theorem flatBaseChangeTorIsoOfResolution_projectiveResolution (f : R →+* S) (hf : f.Flat)
    (M N : ModuleCat.{u} R) (n : ℕ) :
    flatBaseChangeTorIsoOfResolution f hf M (projectiveResolution N) n =
      flatBaseChangeTorIso f hf M N n := by
  apply Iso.ext
  dsimp [flatBaseChangeTorIsoOfResolution, flatBaseChangeTorIso,
    flatExtendTensorHomologyIso, Iso.trans, Functor.mapIso]
  change (_ ≫ (_ ≫ _) ≫ _) = (_ ≫ _ ≫ _ ≫ _)
  erw [Category.assoc]

/-- The actual flat Tor comparison is independent of the resolution used to compute it. -/
theorem flatBaseChangeTorIsoOfResolution_eq (f : R →+* S) (hf : f.Flat)
    (M : ModuleCat.{u} R) {N : ModuleCat.{u} R} (P Q : ProjectiveResolution N) (n : ℕ) :
    flatBaseChangeTorIsoOfResolution f hf M P n =
      flatBaseChangeTorIsoOfResolution f hf M Q n := by
  apply Iso.ext
  have h := flatBaseChangeTorIsoOfResolution_hom_naturality f hf M (𝟙 N) P Q
    (ProjectiveResolution.lift (𝟙 N) P Q) (ProjectiveResolution.lift_commutes_zero _ _ _) n
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id] at h
  exact h.symm

/-- An arbitrary resolution computes the existing canonical flat Tor comparison. -/
theorem flatBaseChangeTorIsoOfResolution_eq_flatBaseChangeTorIso
    (f : R →+* S) (hf : f.Flat) (M : ModuleCat.{u} R)
    {N : ModuleCat.{u} R} (P : ProjectiveResolution N) (n : ℕ) :
    flatBaseChangeTorIsoOfResolution f hf M P n = flatBaseChangeTorIso f hf M N n :=
  (flatBaseChangeTorIsoOfResolution_eq f hf M P (projectiveResolution N) n).trans
    (flatBaseChangeTorIsoOfResolution_projectiveResolution f hf M N n)

/-- Canonical flat Tor base change is natural in every morphism of the resolved argument. -/
@[reassoc]
theorem flatBaseChangeTorIso_hom_naturality_right (f : R →+* S) (hf : f.Flat)
    (M : ModuleCat.{u} R) {N N' : ModuleCat.{u} R} (v : N ⟶ N') (n : ℕ) :
    (ModuleCat.extendScalars f).map (((Tor (ModuleCat R) n).obj M).map v) ≫
        (flatBaseChangeTorIso f hf M N' n).hom =
      (flatBaseChangeTorIso f hf M N n).hom ≫
        ((Tor (ModuleCat S) n).obj ((ModuleCat.extendScalars f).obj M)).map
          ((ModuleCat.extendScalars f).map v) := by
  simpa only [flatBaseChangeTorIsoOfResolution_projectiveResolution] using
    flatBaseChangeTorIsoOfResolution_hom_naturality f hf M v
      (projectiveResolution N) (projectiveResolution N')
      (ProjectiveResolution.lift v _ _) (ProjectiveResolution.lift_commutes_zero _ _ _) n

/-- The chain tensorator is natural in arbitrary coefficient-module maps. -/
@[reassoc]
theorem extendTensorComplexIso_hom_naturality_left (f : R →+* S)
    {M M' : ModuleCat.{u} R} (u : M ⟶ M') (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    ((ModuleCat.extendScalars f).mapHomologicalComplex _).map
        ((NatTrans.mapHomologicalComplex ((tensoringLeft (ModuleCat R)).map u) _).app K) ≫
        (extendTensorComplexIso f M' K).hom =
      (extendTensorComplexIso f M K).hom ≫
        (NatTrans.mapHomologicalComplex
          ((tensoringLeft (ModuleCat S)).map ((ModuleCat.extendScalars f).map u)) _).app
            (((ModuleCat.extendScalars f).mapHomologicalComplex _).obj K) := by
  ext i : 1
  exact (Functor.OplaxMonoidal.δ_natural_left (ModuleCat.extendScalars f) u (K.X i)).symm

set_option backward.isDefEq.respectTransparency false in
/-- The homological base-change comparison respects every coefficient-module morphism. -/
@[reassoc]
theorem flatExtendTensorHomologyIso_hom_naturality_left (f : R →+* S) (hf : f.Flat)
    {M M' : ModuleCat.{u} R} (u : M ⟶ M') (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    (ModuleCat.extendScalars f).map
        (HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex ((tensoringLeft (ModuleCat R)).map u) _).app K) n) ≫
        (flatExtendTensorHomologyIso f hf M' K n).hom =
      (flatExtendTensorHomologyIso f hf M K n).hom ≫
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex
            ((tensoringLeft (ModuleCat S)).map ((ModuleCat.extendScalars f).map u)) _).app
              (((ModuleCat.extendScalars f).mapHomologicalComplex _).obj K)) n := by
  simp only [flatExtendTensorHomologyIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  erw [flatExtendHomologyIso_hom_naturality_assoc]
  have h := congrArg ((HomologicalComplex.homologyFunctor (ModuleCat S) _ n).map)
    (extendTensorComplexIso_hom_naturality_left f u K)
  simp only [Functor.map_comp] at h
  exact congrArg ((flatExtendHomologyIso f hf
    (((tensorLeft M).mapHomologicalComplex _).obj K) n).hom ≫ ·) h

set_option backward.isDefEq.respectTransparency false in
/-- Resolution computation of Tor intertwines coefficient-module maps. -/
@[reassoc]
theorem torResolutionIso_hom_naturality_left {M M' N : ModuleCat.{u} R}
    (u : M ⟶ M') (P : ProjectiveResolution N) (n : ℕ) :
    ((Tor (ModuleCat R) n).map u).app N ≫
        (P.isoLeftDerivedObj (tensorLeft M') n).hom =
      (P.isoLeftDerivedObj (tensorLeft M) n).hom ≫
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex ((tensoringLeft (ModuleCat R)).map u) _).app
            P.complex) n := by
  change (NatTrans.leftDerived ((tensoringLeft (ModuleCat R)).map u) n).app N ≫ _ = _
  rw [P.leftDerived_app_eq]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The inverse resolution comparison also intertwines coefficient-module maps. -/
@[reassoc]
theorem torResolutionIso_inv_naturality_left {M M' N : ModuleCat.{u} R}
    (u : M ⟶ M') (P : ProjectiveResolution N) (n : ℕ) :
    (P.isoLeftDerivedObj (tensorLeft M) n).inv ≫ ((Tor (ModuleCat R) n).map u).app N =
      HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex ((tensoringLeft (ModuleCat R)).map u) _).app
            P.complex) n ≫
        (P.isoLeftDerivedObj (tensorLeft M') n).inv := by
  rw [← cancel_mono (P.isoLeftDerivedObj (tensorLeft M') n).hom,
    Category.assoc, torResolutionIso_hom_naturality_left,
    Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- The actual arbitrary-resolution comparison is natural in the coefficient module. -/
@[reassoc]
theorem flatBaseChangeTorIsoOfResolution_hom_naturality_left (f : R →+* S) (hf : f.Flat)
    {M M' : ModuleCat.{u} R} (u : M ⟶ M') {N : ModuleCat.{u} R}
    (P : ProjectiveResolution N) (n : ℕ) :
    (ModuleCat.extendScalars f).map (((Tor (ModuleCat R) n).map u).app N) ≫
        (flatBaseChangeTorIsoOfResolution f hf M' P n).hom =
      (flatBaseChangeTorIsoOfResolution f hf M P n).hom ≫
        ((Tor (ModuleCat S) n).map ((ModuleCat.extendScalars f).map u)).app
          ((ModuleCat.extendScalars f).obj N) := by
  have h₁ := torResolutionIso_hom_naturality_left u P n
  have h₂ := flatExtendTensorHomologyIso_hom_naturality_left f hf u P.complex n
  have h₃ := torResolutionIso_inv_naturality_left ((ModuleCat.extendScalars f).map u)
    (flatExtendProjectiveResolution f hf P) n
  simp only [flatBaseChangeTorIsoOfResolution, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Category.assoc]
  erw [← Functor.map_comp_assoc, h₁, Functor.map_comp, Category.assoc, h₃]
  have h₂' := congrArg (· ≫ ((flatExtendProjectiveResolution f hf P).isoLeftDerivedObj
      (tensorLeft ((ModuleCat.extendScalars f).obj M')) n).inv) h₂
  have h₂'' := congrArg ((ModuleCat.extendScalars f).map
      (P.isoLeftDerivedObj (tensorLeft M) n).hom ≫ ·) h₂'
  dsimp only [Functor.comp_map, HomologicalComplex.homologyFunctor] at *
  exact h₂''.trans (by rfl)

/-- Canonical flat Tor base change is natural in every coefficient-module morphism. -/
@[reassoc]
theorem flatBaseChangeTorIso_hom_naturality_left (f : R →+* S) (hf : f.Flat)
    {M M' : ModuleCat.{u} R} (u : M ⟶ M') (N : ModuleCat.{u} R) (n : ℕ) :
    (ModuleCat.extendScalars f).map (((Tor (ModuleCat R) n).map u).app N) ≫
        (flatBaseChangeTorIso f hf M' N n).hom =
      (flatBaseChangeTorIso f hf M N n).hom ≫
        ((Tor (ModuleCat S) n).map ((ModuleCat.extendScalars f).map u)).app
          ((ModuleCat.extendScalars f).obj N) := by
  simpa only [flatBaseChangeTorIsoOfResolution_projectiveResolution] using
    flatBaseChangeTorIsoOfResolution_hom_naturality_left f hf u (projectiveResolution N) n

end ModuleCat.TorComparison
