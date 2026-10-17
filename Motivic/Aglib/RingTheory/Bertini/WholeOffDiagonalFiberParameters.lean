/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Bertini.MovingPointBadPointExclusion
public import Motivic.Aglib.RingTheory.Bertini.QuadraticParameterTuple

/-! # One quadratic tuple controls all off-diagonal points of the selected fiber

The quantifier ranges over arbitrary field-valued moving points simultaneously.
The parameters lie in the original infinite ground field and may also be chosen
in any supplied nonempty principal open of that same parameter family.
-/
@[expose] public noncomputable section
open Module TensorProduct KaehlerDifferential MvPolynomial
universe u
namespace QuadraticIncidence
variable (k R B : Type u) [Field k] [CommRing R] [CommRing B]
  [Algebra k R] [Algebra k B] [Algebra R B] {σ : Type u} [Fintype σ]

/-- A property of the actual ground-coefficient tuple, uniform in every field of
an off-diagonal point of the original selected fiber. -/
def GoodOffDiagonalParameters (g : σ → R) (a : σ → B) (d : ℕ)
    (c : Fin d × Exponent σ → k) : Prop :=
  ∀ (K : Type u) [Field K] [Algebra k K] [Algebra R K] [Algebra B K]
    [IsScalarTower k B K] [IsScalarTower R B K],
    let p := parameterTuple K σ d (algebraMap k K ∘ c)
    (fun j => algebraMap R K (g j)) ≠ algebraMap B K ∘ a →
    (∀ i, eval (fun j => algebraMap R K (g j)) (p i).val =
      eval (algebraMap B K ∘ a) (p i).val) →
    LinearIndependent K (fun i => residueGeneratorGradient k R K g
      (fun j => eval (fun l => algebraMap R K (g l)) (pderiv j (p i).val)))

/-- The whole off-diagonal fiber condition is produced, not assumed. Only the
original affine dimension, smoothness, and a genuine finite coefficient extension
are needed before the final infinite-field specialization. -/
theorem exists_goodOffDiagonalParameters [Infinite k] [IsDomain R]
    [IsScalarTower k R B] [Module.Finite R B] [Algebra.Smooth k R]
    (g : σ → R) (hg : Algebra.adjoin k (Set.range g) = ⊤)
    (a : σ → B) (d : ℕ) (hd : Algebra.trdeg k R = (d + 1 : ℕ))
    (q : MvPolynomial (Fin d × Exponent σ) k) (hq : q ≠ 0) :
    ∃ c : Fin d × Exponent σ → k,
      eval c q ≠ 0 ∧ GoodOffDiagonalParameters k R B g a d c := by
  obtain ⟨f, c, _, hf, hq', hz⟩ :=
    MovingPointChart.exists_parameter_choice_avoiding_charts k R B g hg a d hd q hq
  refine ⟨c, hq', ?_⟩
  intro K _ _ _ _ _ _
  dsimp only
  intro hab hvalue
  apply MovingPointChart.linearIndependent_of_parameter_relation_ne_zero k R B K
    g a d f c hf hz (parameterTuple K σ d (algebraMap k K ∘ c)) _ hab hvalue
  intro x
  exact parameterTuple_repr K σ d (algebraMap k K ∘ c) x

end QuadraticIncidence
