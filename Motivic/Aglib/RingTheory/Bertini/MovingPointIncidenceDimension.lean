/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Bertini.MovingPointCoefficientDimension
public import Motivic.Aglib.RingTheory.Bertini.QuadraticIncidenceGenericFiber
public import Motivic.Aglib.RingTheory.Bertini.MovingPointDistinctness

/-! # Dimension drop for every actual normalized off-diagonal incidence component

The intermediate coefficient field and its dimension bound are constructed from
the original chart. Only the original affine dimension and finite coefficient
extension remain as geometric inputs.
-/
@[expose] public noncomputable section
open Module TensorProduct KaehlerDifferential
universe u
namespace QuadraticIncidence.MovingPointChart
variable (k R B : Type u) [Field k] [CommRing R] [IsDomain R] [CommRing B]
  [Algebra k R] [Algebra k B] [Algebra R B] [IsScalarTower k R B]
  [Module.Finite R B] [Algebra.Smooth k R] {σ : Type u} [Fintype σ]

/-- The full original incidence quotient on an actual normalized chart. -/
abbrev incidenceRing (g : σ → R) (a : σ → B) (d : ℕ) (i₀ : Fin d) (j : σ) :=
  let t := algebraMap R B (g j) - a j
  let A := Ring B d i₀ t
  CoordinateRing k R A g (algebraMap B A ∘ a) d (weight B d i₀ t)

/-- Every actual prime component has strictly fewer parameters than the full
quadratic projection space. No component dimension or rank hypothesis is supplied. -/
theorem trdeg_component_fractionField_add_one_le
    (g : σ → R) (hg : Algebra.adjoin k (Set.range g) = ⊤)
    (a : σ → B) (d : ℕ) (hd : Algebra.trdeg k R = (d + 1 : ℕ))
    (i₀ : Fin d) (j : σ) (P : Ideal (incidenceRing k R B g a d i₀ j)) [P.IsPrime] :
    Algebra.trdeg k (FractionRing (incidenceRing k R B g a d i₀ j ⧸ P)) + 1 ≤
      (d * Fintype.card (Exponent σ) : ℕ) := by
  let t := algebraMap R B (g j) - a j
  let A := Ring B d i₀ t
  let C := incidenceRing k R B g a d i₀ j ⧸ P
  let E := FractionRing C
  let K := IncidenceCoefficientField.field k A E
  let := IncidenceCoefficientField.algebra k A E
  let : Algebra R K := ((algebraMap A K).comp (algebraMap R A)).toAlgebra
  let : Algebra B K := ((algebraMap A K).comp (algebraMap B A)).toAlgebra
  have : IsScalarTower R A K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower B A K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R K E := IsScalarTower.to₁₃₄ R A K E
  have : IsScalarTower R B K := IsScalarTower.to₁₂₄ R B A K
  have hK := trdeg_coefficientField_le_twice k R B d i₀ t E hd
  have hab := selected_ne_moving R B g a d i₀ j K
  exact trdeg_fractionField_add_one_le k R A K C E g hg
    (algebraMap B A ∘ a) d hd (weight B d i₀ t) i₀
    (weight_distinguished B d i₀ t) hab (Ideal.Quotient.mkₐ A P)
    (Ideal.Quotient.mkₐ_surjective A P) hK

end QuadraticIncidence.MovingPointChart
