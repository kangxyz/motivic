/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Bertini.LargePrimeFullTupleParameters
public import Motivic.Aglib.RingTheory.Bertini.QuadraticScalarInfinityPolynomials
public import Motivic.Aglib.RingTheory.Bertini.ScalarQuadraticEtaleFromWholeFiber
public import Mathlib.RingTheory.Flat.Stability

/-! # Two large prime extensions with actual quadratic étale and infinity conditions -/

@[expose] public noncomputable section

open Module TensorProduct KaehlerDifferential MvPolynomial
open scoped TensorProduct

namespace QuadraticIncidence

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- All infinity equations are constructed before either extension is chosen.
The same full tuple is genuinely étale at the entire original marked fiber and
avoids infinity for the whole original mapped ideal. Smoothness away from the
marked fiber is not asserted here. -/
theorem exists_two_prime_quadratic_etale_infinity
    (k R : Type u) [Field k] [Finite k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.Smooth k R]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (x : PrimeSpectrum R) [x.asIdeal.IsMaximal]
    (I : Ideal R) (hI : I ≠ ⊥)
    {σ : Type u} [Fintype σ] (g : σ → R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg k R ≤ (d : Cardinal.{u}) + 1)
    (B : Basis (Fin (d + 1)) x.asIdeal.ResidueField
      (x.asIdeal.ResidueField ⊗[R] Ω[R⁄k]))
    (f q : MvPolynomial (Fin d × Exponent σ) k)
    (hf : f ≠ 0) (hq : q ≠ 0) (N : ℕ) :
    ∃ n m : ℕ, N < n ∧ N < m ∧ n.Coprime m ∧
      ∀ (r : ℕ) [NeZero r], r = n ∨ r = m →
        let L := ULift.{u} (FiniteField.Extension k p r)
        Module.finrank k L = r ∧ ∃ hdom : IsDomain (R ⊗[k] L),
          letI : IsDomain (R ⊗[k] L) := hdom
          (∃! y : PrimeSpectrum (R ⊗[k] L),
            PrimeSpectrum.comap (algebraMap R (R ⊗[k] L)) y = x) ∧
          ∃ (a : Exponent σ → L) (c : Fin d × Exponent σ → L),
            eval₂ (algebraMap k L) c f ≠ 0 ∧ eval₂ (algebraMap k L) c q ≠ 0 ∧
            InfinityChart.NoCommonInfinityZero L (R ⊗[k] L)
              (algebraMap R (R ⊗[k] L) ∘ g) d (prependParameters L d a c) ∧
            InfinityChart.NoCommonClosedInfinityZero L (R ⊗[k] L)
              (I.map (algebraMap R (R ⊗[k] L)))
              (algebraMap R (R ⊗[k] L) ∘ g) d c ∧
            (let : Algebra (MvPolynomial (Fin d × Exponent σ) k) L :=
              (eval₂Hom (algebraMap k L) c).toAlgebra
             IsUnit (1 ⊗ₜ[MvPolynomial (Fin d × Exponent σ) k]
               (residueCoefficientEquiv k x.asIdeal.ResidueField _).symm
                 (selectedDeterminant d B
                   (selectedDerivative (k := k) (L := x.asIdeal.ResidueField) g)) :
               L ⊗[MvPolynomial (Fin d × Exponent σ) k]
                 (MvPolynomial (Fin d × Exponent σ) k ⊗[k] x.asIdeal.ResidueField))) ∧
            ∀ (y : PrimeSpectrum (R ⊗[k] L)),
              PrimeSpectrum.comap (algebraMap R (R ⊗[k] L)) y = x →
              ∃ s ∉ y.asIdeal,
                ((algebraMap (R ⊗[k] L) (Localization.Away s)).comp
                  (aeval (R := L) (fun i => aeval (algebraMap R (R ⊗[k] L) ∘ g)
                    (parameterTuple L σ (d + 1)
                      (prependParameters L d a c) i).val)).toRingHom).Etale := by
  obtain ⟨F, Q, hF, hQ, hinf⟩ :=
    InfinityChart.exists_scalar_infinity_polynomials k R I hI g d hd
  obtain ⟨n, m, hn, hm, hnm, h⟩ := exists_two_prime_fullTuple_parameters k R p x d B
    (selectedDerivative (k := k) (L := x.asIdeal.ResidueField) g)
    (selectedDerivative_surjective g hg) F f Q q hF hf hQ hq N
  refine ⟨n, m, hn, hm, hnm, ?_⟩
  intro r _ hr
  obtain ⟨hdeg, hdom, hy, a, c, hF', hf', hQ', hq', hE, hD⟩ := h r hr
  let L := ULift.{u} (FiniteField.Extension k p r)
  let : IsDomain (R ⊗[k] L) := hdom
  obtain ⟨hW, hZ⟩ := hinf L (R ⊗[k] L)
    (Algebra.TensorProduct.includeLeft_injective (R := k) (S := k)
      (A := R) (B := L) (algebraMap k L).injective)
    (prependParameters L d a c) c hF' hQ'
  refine ⟨hdeg, hdom, hy, a, c, hf', hq', hW, hZ, hD, ?_⟩
  intro y hyx
  let : Algebra.Smooth L (R ⊗[k] L) :=
    Algebra.Smooth.of_equiv (Algebra.TensorProduct.commRight k L R)
  exact exists_scalar_quadratic_etale_of_isUnit_original_fiber k R L x y hyx g
    (d + 1) B (prependParameters L d a c) hE

end QuadraticIncidence
