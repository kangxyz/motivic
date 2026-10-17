/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Normalization.FiniteGenericallyEtaleField

/-! # The literal finite coordinate map and an actual étale principal neighborhood -/
@[expose] public noncomputable section
open CategoryTheory TopologicalSpace
universe u
namespace AlgebraicGeometry

/-- The original principal chart is étale, not a substituted coordinate map. -/
theorem etale_basicOpen_of_etale_away
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (r : B)
    (h : ((algebraMap B (Localization.Away r)).comp f).Etale) :
    Etale (Scheme.Opens.ι (X := Spec (.of B)) (PrimeSpectrum.basicOpen r) ≫
      Spec.map (CommRingCat.ofHom f)) := by
  have he : Etale (Spec.map (CommRingCat.ofHom
      ((algebraMap B (Localization.Away r)).comp f))) := HasRingHomProperty.Spec_iff.mpr h
  have H : Etale ((basicOpenIsoSpecAway (R := .of B) r).hom ≫
      Spec.map (CommRingCat.ofHom ((algebraMap B (Localization.Away r)).comp f))) :=
    inferInstance
  rw [CommRingCat.ofHom_comp, Spec.map_comp, ← Category.assoc,
    basicOpenIsoSpecAway_hom_SpecMap (R := .of B)] at H
  exact H

/-- A selected point in an actual étale principal chart forces dominance of the
unchanged coordinate map; no separability premise is added. -/
theorem isDominant_specMap_of_etale_away
    {A B : Type u} [CommRing A] [CommRing B] [IsDomain A]
    (f : A →+* B) (p : PrimeSpectrum B) (r : B) (hr : r ∉ p.asIdeal)
    (h : ((algebraMap B (Localization.Away r)).comp f).Etale) :
    IsDominant (Spec.map (CommRingCat.ofHom f)) := by
  have := etale_basicOpen_of_etale_away f r h
  exact Scheme.isDominant_of_nonempty_etale_open _ (PrimeSpectrum.basicOpen r) ⟨p, hr⟩

/-- The exact selected étale chart and finiteness of the original coordinate map
supply the finite étale extension required by normalization. -/
theorem finite_etale_functionFieldMap_of_etale_away
    {A B : Type u} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    (f : A →+* B) (hf : f.Finite) (p : PrimeSpectrum B) (r : B)
    (hr : r ∉ p.asIdeal) (h : ((algebraMap B (Localization.Away r)).comp f).Etale)
    [IsDominant (Spec.map (CommRingCat.ofHom f))] :
    IsFinite (Spec.map (CommRingCat.ofHom
      (Scheme.functionFieldMap (Spec.map (CommRingCat.ofHom f))))) ∧
    Etale (Spec.map (CommRingCat.ofHom
      (Scheme.functionFieldMap (Spec.map (CommRingCat.ofHom f))))) := by
  have : IsFinite (Spec.map (CommRingCat.ofHom f)) := (IsFinite.SpecMap_iff _).mpr hf
  have := etale_basicOpen_of_etale_away f r h
  refine ⟨Scheme.finite_functionFieldMap _,
    Scheme.etale_functionFieldMap_of_etale_open _ (PrimeSpectrum.basicOpen r) ?_⟩
  apply ((genericPoint_spec (Spec (.of B))).mem_open_set_iff
    (PrimeSpectrum.basicOpen r).isOpen).mpr
  exact ⟨p, trivial, hr⟩

end AlgebraicGeometry
