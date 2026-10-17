module
import Motivic.Aglib.RingTheory.Bertini.QuadraticIncidenceSpecialization
import Lean.Util.CollectAxioms

/-! # The actual specialized incidence homomorphism retains every original variable -/
open Module TensorProduct MvPolynomial QuadraticIncidence

noncomputable section
variable (k R A K E : Type) [CommRing k] [CommRing R] [CommRing A]
  [CommRing K] [CommRing E] [Algebra k R] [Algebra R A]
  [Algebra R K] [Algebra A K] [Algebra R E] [Algebra A E] [Algebra K E]
  [IsScalarTower R A E] [IsScalarTower R K E]
  [IsScalarTower A K E] [Algebra.Smooth k R]
  {σ : Type} [Fintype σ]

example (g : σ → R) (a : σ → A) (d : ℕ) (w : Fin d → A)
    (h : CoordinateRing k R A g a d w →ₐ[A] E) :
    (∑ q, coordinateImages k R A g a d w h q ⊗ₜ[K]
      coefficientVector k R K g (algebraMap A K ∘ a) d (algebraMap A K ∘ w) q) = 0 :=
  coordinateImages_specialized_vector_eq_zero k R A K E g a d w h

example (g : σ → R) (a : σ → A) (d : ℕ) (w : Fin d → A)
    (h : CoordinateRing k R A g a d w →ₐ[A] E) :
    CoordinateRing k R K g (algebraMap A K ∘ a) d (algebraMap A K ∘ w) →ₐ[K] E :=
  specialize k R A K E g a d w h

example (g : σ → R) (a : σ → A) (d : ℕ) (w : Fin d → A)
    (h : CoordinateRing k R A g a d w →ₐ[A] E) (q : Fin d × Exponent σ) :
    specialize k R A K E g a d w h
      (LinearIncidence.coordinates (ProjectiveIncidence.coefficientMatrix (R := K)
        (coefficientVector k R K g (algebraMap A K ∘ a) d (algebraMap A K ∘ w))) q) =
      h (LinearIncidence.coordinates (ProjectiveIncidence.coefficientMatrix (R := A)
        (coefficientVector k R A g a d w)) q) :=
  specialize_coordinates k R A K E g a d w h q
end

open Lean in
run_cmd do
  for name in #[``coordinateImages, ``coordinateImages_vector_eq_zero,
      ``coordinateImages_specialized_vector_eq_zero, ``specialized_ideal_le_ker,
      ``specialize, ``specialize_coordinates] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Quadratic incidence specialization: standard foundations only."
