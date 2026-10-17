/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Normalization.FiniteEtaleAwayFunctionField
public import Motivic.Aglib.AlgebraicGeometry.Normalization.FunctionFieldOpenComposition
public import Lean

/-! # Original finite coordinates and selected étale chart give the actual field extension -/
public noncomputable section
open AlgebraicGeometry CategoryTheory Scheme
universe u

example {A B : Type u} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    (f : A →+* B) (hf : f.Finite) (p : PrimeSpectrum B) (r : B)
    (hr : r ∉ p.asIdeal) (h : ((algebraMap B (Localization.Away r)).comp f).Etale) :
    ∃ hd : IsDominant (Spec.map (CommRingCat.ofHom f)),
      letI := hd
      IsFinite (Spec.map (CommRingCat.ofHom
        (functionFieldMap (Spec.map (CommRingCat.ofHom f))))) ∧
      Etale (Spec.map (CommRingCat.ofHom
        (functionFieldMap (Spec.map (CommRingCat.ofHom f))))) := by
  have hd := isDominant_specMap_of_etale_away f p r hr h
  exact ⟨hd, finite_etale_functionFieldMap_of_etale_away f hf p r hr h⟩

open Lean in
run_cmd do
  for name in #[``isDominant_specMap_of_etale_away,
      ``finite_etale_functionFieldMap_of_etale_away,
      ``finite_etale_functionFieldSpecMap_comp_open] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original finite map: dominance and finite etale generic extension, standard axioms."
