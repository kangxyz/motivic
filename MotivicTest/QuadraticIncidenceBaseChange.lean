module
import Motivic.Aglib.RingTheory.Bertini.QuadraticIncidenceBaseChange
import Lean.Util.CollectAxioms

/-! # Exact base change of the original quadratic incidence equations -/
open Module TensorProduct MvPolynomial KaehlerDifferential QuadraticIncidence

noncomputable section
variable (k R A K : Type) [CommRing k] [CommRing R] [CommRing A] [CommRing K]
  [Algebra k R] [Algebra R A] [Algebra R K] [Algebra A K] [IsScalarTower R A K]
  {σ : Type} [Fintype σ]

example (d : ℕ) :
    K ⊗[A] ((Fin d → A) × (A ⊗[R] Ω[R⁄k])) ≃ₗ[K]
      (Fin d → K) × (K ⊗[R] Ω[R⁄k]) :=
  coefficientBaseChange k R A K d

example (g : σ → R) (c : σ → A) :
    AlgebraTensorModule.cancelBaseChange R A K K Ω[R⁄k]
        (1 ⊗ₜ[A] residueGeneratorGradient k R A g c) =
      residueGeneratorGradient k R K g (algebraMap A K ∘ c) :=
  baseChange_residueGeneratorGradient k R A K g c

example (g : σ → R) (a : σ → A) (d : ℕ) (w : Fin d → A)
    (q : Fin d × Exponent σ) :
    coefficientBaseChange k R A K d (1 ⊗ₜ[A] coefficientVector k R A g a d w q) =
      coefficientVector k R K g (algebraMap A K ∘ a) d (algebraMap A K ∘ w) q :=
  coefficientBaseChange_coefficientVector k R A K g a d w q

example (g : σ → R) (a : σ → A) (d : ℕ) (w : Fin d → A)
    (x : Fin d × Exponent σ → K) :
    (∑ q, x q ⊗ₜ[A] coefficientVector k R A g a d w q) = 0 ↔
      (∑ q, x q • coefficientVector k R K g (algebraMap A K ∘ a) d
        (algebraMap A K ∘ w) q) = 0 :=
  sum_coefficientVector_eq_zero_iff k R A K g a d w x
end

open Lean in
run_cmd do
  for name in #[``map_eval_monomial_one, ``map_eval_pderiv_monomial_one,
      ``baseChange_residueGeneratorGradient, ``coefficientBaseChange,
      ``coefficientBaseChange_tmul_fst, ``coefficientBaseChange_tmul_snd,
      ``coefficientBaseChange_coefficientVector,
      ``coefficientBaseChange_tmul_coefficientVector, ``coefficientBaseChange_sum,
      ``sum_coefficientVector_eq_zero_iff] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Quadratic incidence base change: standard foundations only."
