/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Bertini.QuadraticFullSelectedPointOpen
public import Motivic.Aglib.RingTheory.Bertini.QuadraticParameterBaseChange
public import Motivic.Aglib.RingTheory.Kaehler.PolynomialResidueGradient
public import Motivic.Aglib.RingTheory.Etale.ResidueCoordinateCriterion

/-! # The unchanged full quadratic tuple is étale at the selected point on a true open -/
@[expose] public noncomputable section
open Module MvPolynomial TensorProduct KaehlerDifferential
universe u
namespace QuadraticIncidence

/-- A full-rank determinant condition produces an actual étale principal neighborhood
for the same original quadratic tuple, without a separability premise. -/
theorem exists_selectedEtale_open (k R : Type u) [Field k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.Smooth k R] (P : PrimeSpectrum R)
    {σ : Type u} [Fintype σ] (g : σ → R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (n : ℕ)
    (hd : Algebra.trdeg k R = n) :
    ∃ q : MvPolynomial (Fin n × Exponent σ) k, q ≠ 0 ∧
      ∀ c : Fin n × Exponent σ → k, eval c q ≠ 0 →
        ∃ r ∉ P.asIdeal, ((algebraMap R (Localization.Away r)).comp
          (aeval (R := k) (fun i => aeval g (parameterTuple k σ n c i).val)).toRingHom).Etale := by
  let L := P.asIdeal.ResidueField
  obtain ⟨q, hq, hselected⟩ := exists_fullSelectedPoint_open (L := L) g hg n hd
  refine ⟨q, hq, fun c hc => ?_⟩
  let f : Fin n → R := fun i => aeval g (parameterTuple k σ n c i).val
  have hv := hselected c hc
  change LinearIndependent L (fun i => residueGeneratorGradient k R L g
    (fun j => eval (fun l => algebraMap R L (g l))
      (pderiv j (parameterTuple L σ n (algebraMap k L ∘ c) i).val))) at hv
  have hi : LinearIndependent L (fun i => (1 : L) ⊗ₜ[R] D k R (f i)) := by
    simpa only [← parameterTuple_map, residueGeneratorGradient_map_polynomial] using hv
  have hrank : Module.finrank L (L ⊗[R] Ω[R⁄k]) = n := by
    rw [Algebra.cotangent_finrank_eq_trdeg_toNat k R L, hd]
    simp
  let b := basisOfLinearIndependentOfCardEqFinrank'
    (fun i => (1 : L) ⊗ₜ[R] D k R (f i)) hi (by simpa using hrank.symm)
  exact Algebra.exists_etale_polynomial_map_of_residue_differential_basis
    k R P.asIdeal f b (fun i => Basis.mk_apply _ _ i)

end QuadraticIncidence
