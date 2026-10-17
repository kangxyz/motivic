module
import Motivic.Aglib.RingTheory.Bertini.QuadraticIncidenceGenericFiber
import Lean.Util.CollectAxioms

/-! # The actual generic-field bound for a quadratic incidence component

The component is a genuine quotient of the original incidence ring. Its fraction
field receives the intermediate-coefficient incidence ring by the canonical
specialization map. Original coordinate generation, rather than an assumed
algebraicity property, transfers the incidence bound to that fraction field.
-/
noncomputable section
open Module TensorProduct KaehlerDifferential
universe u
namespace QuadraticIncidence
variable (k R A K C E : Type u) [Field k] [CommRing R] [IsDomain R]
  [CommRing A] [Field K] [CommRing C] [IsDomain C] [Field E]
  [Algebra k R] [Algebra R A] [Algebra R K] [Algebra A K]
  [Algebra A C] [Algebra C E] [IsFractionRing C E]
  [Algebra R E] [Algebra A E] [Algebra K E]
  [IsScalarTower R A E] [IsScalarTower R K E]
  [IsScalarTower A K E] [IsScalarTower A C E] [Algebra.Smooth k R]
  {σ : Type u} [Fintype σ]

example
    (g : σ → R) (hg : Algebra.adjoin k (Set.range g) = ⊤)
    (a : σ → A) (d : ℕ) (hd : Algebra.trdeg k R = (d + 1 : ℕ))
    (w : Fin d → A) (i₀ : Fin d) (hw : w i₀ = 1)
    (hab : algebraMap A K ∘ a ≠ fun i => algebraMap R K (g i))
    (q : CoordinateRing k R A g a d w →ₐ[A] C) (hq : Function.Surjective q) :
    Algebra.trdeg K E + ((2 * d + 1 : ℕ) : Cardinal.{u}) ≤
      (d * Fintype.card (Exponent σ) : ℕ) :=
  trdeg_fractionField_add_constraints_le k R A K C E g hg a d hd w i₀ hw hab q hq

example
    [Algebra k K] [Algebra k E] [IsScalarTower k K E]
    (g : σ → R) (hg : Algebra.adjoin k (Set.range g) = ⊤)
    (a : σ → A) (d : ℕ) (hd : Algebra.trdeg k R = (d + 1 : ℕ))
    (w : Fin d → A) (i₀ : Fin d) (hw : w i₀ = 1)
    (hab : algebraMap A K ∘ a ≠ fun i => algebraMap R K (g i))
    (q : CoordinateRing k R A g a d w →ₐ[A] C) (hq : Function.Surjective q)
    (hK : Algebra.trdeg k K ≤ (2 * d : ℕ)) :
    Algebra.trdeg k E + 1 ≤ (d * Fintype.card (Exponent σ) : ℕ) :=
  trdeg_fractionField_add_one_le k R A K C E g hg a d hd w i₀ hw hab q hq hK

open Lean in
run_cmd do
  for name in #[``trdeg_fractionField_add_constraints_le, ``trdeg_fractionField_add_one_le] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual incidence component fraction field: standard foundations only."

end QuadraticIncidence
