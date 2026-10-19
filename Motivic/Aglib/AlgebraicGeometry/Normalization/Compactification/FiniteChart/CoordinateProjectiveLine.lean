/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.FiniteChart.ChartNormalCompactification
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.FiniteChart.EtaleAwayFunctionField
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Charts.Normal

/-! # The one relative projective-line normalization of the original finite coordinates -/
@[expose] public noncomputable section
open CategoryTheory
universe u
namespace AlgebraicGeometry

/-- A finite map with the original selected étale chart constructs a normal finite
cover of the literal relative projective line. Smoothness supplies source normality. -/
theorem exists_normal_projectiveLine_cover_of_finite_coordinates
    (k R B : Type u) [Field k] [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsNoetherianRing R] [CommRing B] [IsDomain B] [Algebra k B] [Algebra.Smooth k B]
    (f : Polynomial R →+* B) (hf : f.Finite) (p : PrimeSpectrum B)
    (r : B) (hr : r ∉ p.asIdeal)
    (he : ((algebraMap B (Localization.Away r)).comp f).Etale) :
    ∃ (N : Scheme.{u}) (i : Spec (.of B) ⟶ N)
      (π : N ⟶ ProjectiveSpace R (ULift.{u} (Fin 2))),
      IsIntegral N ∧ IsLocallyNoetherian N ∧
      (∀ n : N, IsIntegrallyClosed (N.presheaf.stalk n)) ∧
      IsOpenImmersion i ∧ IsFinite π ∧
      IsProper (π ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) ∧
      i ≫ π = Spec.map (CommRingCat.ofHom f) ≫ RelativeProjectiveLine.chart R 0 ∧
      Set.range i = π ⁻¹' Set.range (RelativeProjectiveLine.chart R 0) := by
  have : IsFinite (Spec.map (CommRingCat.ofHom f)) := (IsFinite.SpecMap_iff _).mpr hf
  have : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k B))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr inferInstance)
  have := etale_basicOpen_of_etale_away f r he
  obtain ⟨N, i, π, hN, hnoeth, hnormal, hi, hπ, hw, hfull⟩ :=
    Scheme.exists_normal_finite_cover_of_finite_chart k (Spec.map (CommRingCat.ofHom f))
      (RelativeProjectiveLine.chart R 0) (Spec.map (CommRingCat.ofHom (algebraMap k B)))
      (PrimeSpectrum.basicOpen r) ⟨p, hr⟩
  have := hπ
  exact ⟨N, i, π, hN, hnoeth, hnormal, hi, hπ, inferInstance, hw, hfull⟩

end AlgebraicGeometry
