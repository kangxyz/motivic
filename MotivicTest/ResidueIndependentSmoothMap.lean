/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Kaehler.ResidueIndependentSmoothMap
public import Lean

/-! # The original polynomial map is a relative curve on a genuine prime neighborhood -/
public noncomputable section
open Module TensorProduct KaehlerDifferential CategoryTheory AlgebraicGeometry
universe u
namespace MotivicTest.ResidueIndependentSmoothMap

/-- The output is the original map restricted from a principal neighborhood of the same prime. -/
theorem original_map_neighborhood (k R : Type u) [Field k] [CommRing R]
    [IsDomain R] [Algebra k R] [Algebra.Smooth k R] (p : PrimeSpectrum R)
    (d : ℕ) (f : Fin d → R) (hd : Algebra.trdeg k R = (d + 1 : ℕ))
    (hf : LinearIndependent p.asIdeal.ResidueField
      (fun i => (1 ⊗ₜ[R] D k R (f i) : p.asIdeal.ResidueField ⊗[R] Ω[R⁄k]))) :
    ∃ r : R, p ∈ PrimeSpectrum.basicOpen r ∧ SmoothOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := k) f).toRingHom)) := by
  obtain ⟨r, hr, hs⟩ := exists_smooth_one_of_residue_independent k R p.asIdeal d f hd hf
  refine ⟨r, hr, ?_⟩
  simpa only [← Spec.map_comp, CommRingCat.ofHom_comp] using hs

/-- Completing the basis retains each prescribed function as the literal tail. -/
theorem actual_function_completion (k R K : Type u) [Field k] [CommRing R] [Field K]
    [Algebra k R] [Algebra R K] [Algebra.EssFiniteType k R]
    (d : ℕ) (f : Fin d → R)
    (hf : LinearIndependent K (fun i => (1 ⊗ₜ[R] D k R (f i) : K ⊗[R] Ω[R⁄k])))
    (hd : Module.finrank K (K ⊗[R] Ω[R⁄k]) = d + 1) :
    ∃ b : Basis (Fin (d + 1)) K (K ⊗[R] Ω[R⁄k]),
      ∀ i : Fin d, b i.succ = 1 ⊗ₜ[R] D k R (f i) := by
  obtain ⟨t, b, hb⟩ := exists_residue_basis_cons k R K d f hf hd
  exact ⟨b, fun i => hb i.succ⟩

open Lean in
run_cmd do
  for name in #[``original_map_neighborhood, ``actual_function_completion,
      ``exists_residue_basis_cons, ``Algebra.exists_etale_cons_of_residue_independent,
      ``exists_smooth_one_of_residue_independent] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original polynomial map, actual prime neighborhood, relative dimension one: audited."

end MotivicTest.ResidueIndependentSmoothMap
