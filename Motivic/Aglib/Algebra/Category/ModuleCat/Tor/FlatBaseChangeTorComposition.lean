/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.FlatBaseChangeComposition

/-!
# Composition of canonical Tor base-change comparisons

The scalar associator intertwines the actual tensor-complex and projective
resolution comparisons. These are the chain-level inputs to Tor coherence.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u

namespace ModuleCat.TorComparison

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

set_option backward.isDefEq.respectTransparency false in
/-- The scalar-extension tensor-complex comparison respects its genuine associator. -/
theorem extendTensorComplexIso_comp (f : R →+* S) (g : S →+* T)
    (M : ModuleCat.{u} R) (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    (extendTensorComplexIso (g.comp f) M K).hom ≫
        (NatTrans.mapHomologicalComplex
          ((tensoringLeft (ModuleCat T)).map ((ModuleCat.extendScalarsComp f g).hom.app M))
            _).app (((ModuleCat.extendScalars (g.comp f)).mapHomologicalComplex _).obj K) ≫
        ((tensorLeft
      ((ModuleCat.extendScalars f ⋙ ModuleCat.extendScalars g).obj M)).mapHomologicalComplex
          _).map
          ((NatTrans.mapHomologicalComplex (ModuleCat.extendScalarsComp f g).hom _).app K) =
      (NatTrans.mapHomologicalComplex (ModuleCat.extendScalarsComp f g).hom _).app
          (((tensorLeft M).mapHomologicalComplex _).obj K) ≫
        ((ModuleCat.extendScalars g).mapHomologicalComplex _).map
          (extendTensorComplexIso f M K).hom ≫
        (extendTensorComplexIso g ((ModuleCat.extendScalars f).obj M)
          (((ModuleCat.extendScalars f).mapHomologicalComplex _).obj K)).hom := by
  ext i : 1
  have h := extendScalarsComp_tensorator f g M (K.X i)
  rw [tensorHom_def] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The actual scalar associator gives a comparison between extended resolutions. -/
theorem flatExtendProjectiveResolution_comp_commutes (f : R →+* S) (g : S →+* T)
    (hf : f.Flat) (hg : g.Flat) {N : ModuleCat.{u} R} (P : ProjectiveResolution N) :
    ((NatTrans.mapHomologicalComplex (ModuleCat.extendScalarsComp f g).hom _).app
          P.complex).f 0 ≫
        (flatExtendProjectiveResolution g hg (flatExtendProjectiveResolution f hf P)).π.f 0 =
      (flatExtendProjectiveResolution (g.comp f) (hf.comp hg) P).π.f 0 ≫
        (ModuleCat.extendScalarsComp f g).hom.app N := by
  change (ModuleCat.extendScalarsComp f g).hom.app (P.complex.X 0) ≫
      (ModuleCat.extendScalars g).map ((ModuleCat.extendScalars f).map (P.π.f 0)) =
    (ModuleCat.extendScalars (g.comp f)).map (P.π.f 0) ≫
      (ModuleCat.extendScalarsComp f g).hom.app N
  exact ((ModuleCat.extendScalarsComp f g).hom.naturality (P.π.f 0)).symm

/-- The actual comparison of tensor complexes along the scalar associator. -/
noncomputable def extendTensorCompComparison (f : R →+* S) (g : S →+* T)
    (M : ModuleCat.{u} R) (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    ((tensorLeft ((ModuleCat.extendScalars (g.comp f)).obj M)).mapHomologicalComplex _).obj
        (((ModuleCat.extendScalars (g.comp f)).mapHomologicalComplex _).obj K) ⟶
      ((tensorLeft
      ((ModuleCat.extendScalars f ⋙ ModuleCat.extendScalars g).obj M)).mapHomologicalComplex
        _).obj (((ModuleCat.extendScalars g).mapHomologicalComplex _).obj
            (((ModuleCat.extendScalars f).mapHomologicalComplex _).obj K)) :=
  (NatTrans.mapHomologicalComplex
      ((tensoringLeft (ModuleCat T)).map ((ModuleCat.extendScalarsComp f g).hom.app M))
        _).app (((ModuleCat.extendScalars (g.comp f)).mapHomologicalComplex _).obj K) ≫
    ((tensorLeft
      ((ModuleCat.extendScalars f ⋙ ModuleCat.extendScalars g).obj M)).mapHomologicalComplex
      _).map ((NatTrans.mapHomologicalComplex (ModuleCat.extendScalarsComp f g).hom _).app K)

set_option backward.isDefEq.respectTransparency false in
/-- The actual flat tensor-homology comparison obeys scalar-ring composition. -/
theorem flatExtendTensorHomologyIso_comp (f : R →+* S) (g : S →+* T)
    (hf : f.Flat) (hg : g.Flat) (M : ModuleCat.{u} R)
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    (ModuleCat.extendScalarsComp f g).hom.app
        ((((tensorLeft M).mapHomologicalComplex _).obj K).homology n) ≫
        (ModuleCat.extendScalars g).map (flatExtendTensorHomologyIso f hf M K n).hom ≫
        (flatExtendTensorHomologyIso g hg ((ModuleCat.extendScalars f).obj M)
          (((ModuleCat.extendScalars f).mapHomologicalComplex _).obj K) n).hom =
      (flatExtendTensorHomologyIso (g.comp f) (hf.comp hg) M K n).hom ≫
        HomologicalComplex.homologyMap (extendTensorCompComparison f g M K) n := by
  simp only [flatExtendTensorHomologyIso, Iso.trans_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  erw [flatExtendHomologyIso_hom_naturality_assoc g hg
    (extendTensorComplexIso f M K).hom n]
  have hh := congrArg (· ≫
      (HomologicalComplex.homologyFunctor (ModuleCat T) _ n).map
        (((ModuleCat.extendScalars g).mapHomologicalComplex _).map
          (extendTensorComplexIso f M K).hom) ≫
      (HomologicalComplex.homologyFunctor (ModuleCat T) _ n).map
        (extendTensorComplexIso g ((ModuleCat.extendScalars f).obj M)
          (((ModuleCat.extendScalars f).mapHomologicalComplex _).obj K)).hom)
    (flatExtendHomologyIso_comp f g hf hg
      (((tensorLeft M).mapHomologicalComplex _).obj K) n)
  simp only [Category.assoc] at hh
  erw [hh]
  have hc := congrArg ((HomologicalComplex.homologyFunctor (ModuleCat T) _ n).map)
    (extendTensorComplexIso_comp f g M K)
  simp only [Functor.map_comp] at hc
  dsimp only [extendTensorCompComparison, HomologicalComplex.homologyFunctor] at *
  rw [HomologicalComplex.homologyMap_comp]
  exact congrArg ((flatExtendHomologyIso (g.comp f) (hf.comp hg)
    (((tensorLeft M).mapHomologicalComplex _).obj K) n).hom ≫ ·) hc.symm

set_option backward.isDefEq.respectTransparency false in
/-- The scalar associator intertwines the actual target Tor resolution comparisons. -/
theorem torResolutionIso_comp (f : R →+* S) (g : S →+* T)
    (hf : f.Flat) (hg : g.Flat) (M : ModuleCat.{u} R)
    {N : ModuleCat.{u} R} (P : ProjectiveResolution N) (n : ℕ) :
    ((flatExtendProjectiveResolution (g.comp f) (hf.comp hg) P).isoLeftDerivedObj
        (tensorLeft ((ModuleCat.extendScalars (g.comp f)).obj M)) n).inv ≫
        ((Tor (ModuleCat T) n).map ((ModuleCat.extendScalarsComp f g).hom.app M)).app
          ((ModuleCat.extendScalars (g.comp f)).obj N) ≫
        ((Tor (ModuleCat T) n).obj
          ((ModuleCat.extendScalars f ⋙ ModuleCat.extendScalars g).obj M)).map
          ((ModuleCat.extendScalarsComp f g).hom.app N) =
      HomologicalComplex.homologyMap (extendTensorCompComparison f g M P.complex) n ≫
        ((flatExtendProjectiveResolution g hg
          (flatExtendProjectiveResolution f hf P)).isoLeftDerivedObj
          (tensorLeft ((ModuleCat.extendScalars f ⋙ ModuleCat.extendScalars g).obj M)) n).inv := by
  erw [torResolutionIso_inv_naturality_left_assoc
    ((ModuleCat.extendScalarsComp f g).hom.app M)
    (flatExtendProjectiveResolution (g.comp f) (hf.comp hg) P) n]
  erw [ProjectiveResolution.isoLeftDerivedObj_inv_naturality
    ((ModuleCat.extendScalarsComp f g).hom.app N)
    (flatExtendProjectiveResolution (g.comp f) (hf.comp hg) P)
    (flatExtendProjectiveResolution g hg (flatExtendProjectiveResolution f hf P))
    ((NatTrans.mapHomologicalComplex (ModuleCat.extendScalarsComp f g).hom _).app P.complex)
    (flatExtendProjectiveResolution_comp_commutes f g hf hg P)
    (tensorLeft ((ModuleCat.extendScalars f ⋙ ModuleCat.extendScalars g).obj M)) n]
  dsimp only [extendTensorCompComparison, Functor.comp_map, HomologicalComplex.homologyFunctor]
  rw [HomologicalComplex.homologyMap_comp, Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Canonical flat Tor base change agrees with two successive scalar extensions. -/
theorem flatBaseChangeTorIso_hom_comp (f : R →+* S) (g : S →+* T)
    (hf : f.Flat) (hg : g.Flat) (M N : ModuleCat.{u} R) (n : ℕ) :
    (ModuleCat.extendScalarsComp f g).hom.app (((Tor (ModuleCat R) n).obj M).obj N) ≫
        (ModuleCat.extendScalars g).map (flatBaseChangeTorIso f hf M N n).hom ≫
        (flatBaseChangeTorIso g hg ((ModuleCat.extendScalars f).obj M)
          ((ModuleCat.extendScalars f).obj N) n).hom =
      (flatBaseChangeTorIso (g.comp f) (hf.comp hg) M N n).hom ≫
        ((Tor (ModuleCat T) n).map ((ModuleCat.extendScalarsComp f g).hom.app M)).app
          ((ModuleCat.extendScalars (g.comp f)).obj N) ≫
        ((Tor (ModuleCat T) n).obj
          ((ModuleCat.extendScalars f ⋙ ModuleCat.extendScalars g).obj M)).map
          ((ModuleCat.extendScalarsComp f g).hom.app N) := by
  let P := projectiveResolution N
  rw [← flatBaseChangeTorIsoOfResolution_eq_flatBaseChangeTorIso f hf M P n,
    ← flatBaseChangeTorIsoOfResolution_eq_flatBaseChangeTorIso g hg
      ((ModuleCat.extendScalars f).obj M) (flatExtendProjectiveResolution f hf P) n,
    ← flatBaseChangeTorIsoOfResolution_eq_flatBaseChangeTorIso
      (g.comp f) (hf.comp hg) M P n]
  simp only [flatBaseChangeTorIsoOfResolution, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Functor.map_comp, Category.assoc]
  erw [Iso.map_inv_hom_id_assoc
    ((flatExtendProjectiveResolution f hf P).isoLeftDerivedObj
      (tensorLeft ((ModuleCat.extendScalars f).obj M)) n) (ModuleCat.extendScalars g)]
  erw [← (ModuleCat.extendScalarsComp f g).hom.naturality_assoc
    (P.isoLeftDerivedObj (tensorLeft M) n).hom]
  erw [torResolutionIso_comp f g hf hg M P n]
  have h := congrArg ((ModuleCat.extendScalars (g.comp f)).map
      (P.isoLeftDerivedObj (tensorLeft M) n).hom ≫ · ≫
      ((flatExtendProjectiveResolution g hg
        (flatExtendProjectiveResolution f hf P)).isoLeftDerivedObj
        (tensorLeft ((ModuleCat.extendScalars f ⋙ ModuleCat.extendScalars g).obj M)) n).inv)
    (flatExtendTensorHomologyIso_comp f g hf hg M P.complex n)
  simp only [Category.assoc] at h
  exact h

end ModuleCat.TorComparison
