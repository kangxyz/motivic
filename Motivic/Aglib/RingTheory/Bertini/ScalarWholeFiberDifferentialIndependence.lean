/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Bertini.ScalarWholeFiberParameterIndependence
public import Motivic.Aglib.RingTheory.Bertini.ScalarMovingCoefficientMap
public import Motivic.Aglib.RingTheory.Bertini.WholeFiberSmoothProjection
public import Motivic.Aglib.RingTheory.Kaehler.ScalarResidueGradient

/-! # Actual scalar-source differentials at the same scalar fiber -/

@[expose] public noncomputable section

open Module TensorProduct KaehlerDifferential MvPolynomial
open scoped TensorProduct

namespace QuadraticIncidence

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Every field point of the actual scalar moving coefficient algebra has
independent differentials of the same chosen scalar functions. The original
coefficient-algebra map and both value compatibilities are proved internally. -/
theorem independent_scalar_differentials_at_coefficient_point
    (k R L K : Type u) [Field k] [CommRing R] [Field L] [Field K]
    [Algebra k R] [Algebra.Smooth k R] [Algebra k L] [Algebra L K]
    [Algebra (R ⊗[k] L) K]
    (x : PrimeSpectrum R) (y : PrimeSpectrum (R ⊗[k] L))
    (hy : PrimeSpectrum.comap (algebraMap R (R ⊗[k] L)) y = x)
    [Algebra (ClosedPoint.CoefficientRing L (R ⊗[k] L) y) K]
    [IsScalarTower L (ClosedPoint.CoefficientRing L (R ⊗[k] L) y) K]
    [IsScalarTower (R ⊗[k] L) (ClosedPoint.CoefficientRing L (R ⊗[k] L) y) K]
    {σ : Type u} [Fintype σ] (g : σ → R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (B : Basis (Fin (d + 1)) x.asIdeal.ResidueField
      (x.asIdeal.ResidueField ⊗[R] Ω[R⁄k]))
    (f : MvPolynomial (Fin d × Exponent σ) k) (c : Fin d × Exponent σ → L)
    (hf : eval₂ (algebraMap k L) c f ≠ 0)
    (hz : ∀ (i₀ : Fin d) (j : σ),
      MovingPointChart.chartParameterMap k R (ClosedPoint.CoefficientRing k R x) g
        (fun j => ClosedPoint.selectedValue k R x (g j)) d i₀ j f = 0)
    (hu : let : Algebra (MvPolynomial (Fin d × Exponent σ) k) L :=
        (eval₂Hom (algebraMap k L) c).toAlgebra
      IsUnit (1 ⊗ₜ[MvPolynomial (Fin d × Exponent σ) k]
        (residueCoefficientEquiv k x.asIdeal.ResidueField _).symm
          (selectedDeterminant d B
            (selectedDerivative (k := k) (L := x.asIdeal.ResidueField) g)) :
        L ⊗[MvPolynomial (Fin d × Exponent σ) k]
          (MvPolynomial (Fin d × Exponent σ) k ⊗[k] x.asIdeal.ResidueField)))
    (hv : ∀ i,
      algebraMap (R ⊗[k] L) K
          (aeval (algebraMap R (R ⊗[k] L) ∘ g) (parameterTuple L σ d c i).val) =
        algebraMap (ClosedPoint.CoefficientRing L (R ⊗[k] L) y) K
          (ClosedPoint.selectedValue L (R ⊗[k] L) y
            (aeval (algebraMap R (R ⊗[k] L) ∘ g) (parameterTuple L σ d c i).val))) :
    LinearIndependent K (fun i =>
      (1 : K) ⊗ₜ[R ⊗[k] L] D L (R ⊗[k] L)
        (aeval (algebraMap R (R ⊗[k] L) ∘ g) (parameterTuple L σ d c i).val)) := by
  let S := R ⊗[k] L
  let A := ClosedPoint.CoefficientRing k R x
  let A' := ClosedPoint.CoefficientRing L S y
  let : IsScalarTower L S K := IsScalarTower.to₁₂₄ L S A' K
  let : Algebra k K := ((algebraMap L K).comp (algebraMap k L)).toAlgebra
  let : IsScalarTower k L K := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower k S K := IsScalarTower.to₁₃₄ k L S K
  let : IsScalarTower k A' K := IsScalarTower.to₁₃₄ k L A' K
  let : Algebra R K := ((algebraMap S K).comp (algebraMap R S)).toAlgebra
  let : IsScalarTower R S K := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower k R K := IsScalarTower.to₁₂₄ k R S K
  let : IsScalarTower R A' K := IsScalarTower.to₁₃₄ R S A' K
  let μ := ClosedPoint.scalarCoefficientMap k R L x y hy
  let φ : A →ₐ[k] K := (IsScalarTower.toAlgHom k A' K).comp μ
  let : Algebra A K := φ.toRingHom.toAlgebra
  let : IsScalarTower k A K := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  let : IsScalarTower R A K := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R K r = algebraMap A' K (μ (algebraMap R A r))
    rw [ClosedPoint.scalarCoefficientMap_algebraMap]
    exact IsScalarTower.algebraMap_apply R A' K r
  let s : S →ₐ[L] K := (IsScalarTower.toAlgHom L A' K).comp
    ((Algebra.TensorProduct.includeRight : y.asIdeal.ResidueField →ₐ[L] A').comp
      (IsScalarTower.toAlgHom L S y.asIdeal.ResidueField))
  have hsel (j : σ) : algebraMap A K (ClosedPoint.selectedValue k R x (g j)) =
      s (algebraMap R S (g j)) := by
    change algebraMap A' K (μ (ClosedPoint.selectedValue k R x (g j))) = _
    rw [ClosedPoint.scalarCoefficientMap_selectedValue]
    rfl
  have hval : ∀ i, eval (fun j => algebraMap R K (g j))
      (parameterTuple K σ d (algebraMap L K ∘ c) i).val =
        eval (fun j => algebraMap A K (ClosedPoint.selectedValue k R x (g j)))
          (parameterTuple K σ d (algebraMap L K ∘ c) i).val := by
    intro i
    have hm : (fun j => algebraMap R K (g j)) =
        fun j => algebraMap S K ((algebraMap R S ∘ g) j) := by
      funext j
      exact IsScalarTower.algebraMap_apply R S K (g j)
    rw [hm, ← parameterTuple_map, eval_map_generator_polynomial]
    have hs : (fun j => algebraMap A K (ClosedPoint.selectedValue k R x (g j))) =
        fun j => s ((algebraMap R S ∘ g) j) := funext hsel
    rw [hs, eval_map_original_function]
    exact hv i
  have hi := independent_scalarTuple_at_original_coefficient_point k R L K x
    g hg d B f c hf hz hu hval
  have hi' := independent_scalarResidueGradient k R L K g _ hi
  have hgen : (fun j => algebraMap R K (g j)) =
      fun j => algebraMap S K ((algebraMap R S ∘ g) j) := by
    funext j
    exact IsScalarTower.algebraMap_apply R S K (g j)
  have hvect (i : Fin d) :
      residueGeneratorGradient L S K (algebraMap R S ∘ g)
        (fun j => eval (fun l => algebraMap R K (g l))
          (pderiv j (parameterTuple K σ d (algebraMap L K ∘ c) i).val)) =
        (1 : K) ⊗ₜ[S] D L S
          (aeval (algebraMap R S ∘ g) (parameterTuple L σ d c i).val) := by
    rw [hgen, ← parameterTuple_map]
    exact residueGeneratorGradient_map_polynomial L S K _ _
  convert hi' using 1
  funext i
  exact (hvect i).symm

/-- Independence holds at every prime in the same actual scalar projection fiber,
using the native common-residue-field construction over L. -/
theorem independent_scalar_differentials_of_same_fiber
    (k R L : Type u) [Field k] [CommRing R] [Field L]
    [Algebra k R] [Algebra.Smooth k R] [Algebra k L]
    (x : PrimeSpectrum R) (y : PrimeSpectrum (R ⊗[k] L))
    (hy : PrimeSpectrum.comap (algebraMap R (R ⊗[k] L)) y = x)
    {σ : Type u} [Fintype σ] (g : σ → R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (B : Basis (Fin (d + 1)) x.asIdeal.ResidueField
      (x.asIdeal.ResidueField ⊗[R] Ω[R⁄k]))
    (f : MvPolynomial (Fin d × Exponent σ) k) (c : Fin d × Exponent σ → L)
    (hf : eval₂ (algebraMap k L) c f ≠ 0)
    (hz : ∀ (i₀ : Fin d) (j : σ),
      MovingPointChart.chartParameterMap k R (ClosedPoint.CoefficientRing k R x) g
        (fun j => ClosedPoint.selectedValue k R x (g j)) d i₀ j f = 0)
    (hu : let : Algebra (MvPolynomial (Fin d × Exponent σ) k) L :=
        (eval₂Hom (algebraMap k L) c).toAlgebra
      IsUnit (1 ⊗ₜ[MvPolynomial (Fin d × Exponent σ) k]
        (residueCoefficientEquiv k x.asIdeal.ResidueField _).symm
          (selectedDeterminant d B
            (selectedDerivative (k := k) (L := x.asIdeal.ResidueField) g)) :
        L ⊗[MvPolynomial (Fin d × Exponent σ) k]
          (MvPolynomial (Fin d × Exponent σ) k ⊗[k] x.asIdeal.ResidueField)))
    (Q : PrimeSpectrum (R ⊗[k] L))
    (hQ : Ideal.comap (aeval (R := L) (fun i =>
        aeval (algebraMap R (R ⊗[k] L) ∘ g) (parameterTuple L σ d c i).val)).toRingHom
        y.asIdeal =
      Ideal.comap (aeval (R := L) (fun i =>
        aeval (algebraMap R (R ⊗[k] L) ∘ g) (parameterTuple L σ d c i).val)).toRingHom
        Q.asIdeal) :
    LinearIndependent Q.asIdeal.ResidueField (fun i =>
      (1 : Q.asIdeal.ResidueField) ⊗ₜ[R ⊗[k] L] D L (R ⊗[k] L)
        (aeval (algebraMap R (R ⊗[k] L) ∘ g) (parameterTuple L σ d c i).val)) := by
  apply independent_differentials_of_same_fiber L (R ⊗[k] L) y Q d _ hQ
  intro K _ _ _ _ _ _ hv
  exact independent_scalar_differentials_at_coefficient_point k R L K x y hy
    g hg d B f c hf hz hu hv

end QuadraticIncidence
