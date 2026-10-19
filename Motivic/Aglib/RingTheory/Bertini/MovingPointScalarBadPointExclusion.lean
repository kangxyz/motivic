/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Bertini.MovingPointBadPointExclusion

/-! # Nonvanishing original parameter equations exclude every bad fiber point

The field of the moving point is arbitrary. A putative differential relation
constructs its actual normalized chart point and contradicts the unchanged
parameter equation. No selected-point-only rank argument is used.
-/
@[expose] public noncomputable section
open Module TensorProduct KaehlerDifferential _root_.MvPolynomial
universe u
namespace QuadraticIncidence.MovingPointChart
variable (k R B K : Type u) [Field k] [CommRing R] [CommRing B] [Field K]
  [Algebra k R] [Algebra k B] [Algebra R B]
  [Algebra k K] [Algebra R K] [Algebra B K]
  [IsScalarTower k B K] [IsScalarTower R B K] [Algebra.Smooth k R]
  {σ : Type u} [Fintype σ]

/-- Every off-diagonal point of the selected fiber has independent original
differentials when the common bad-chart equation does not vanish on its parameters. -/
theorem linearIndependent_of_eval₂_parameter_relation_ne_zero
    (g : σ → R) (a : σ → B) (d : ℕ)
    (f : MvPolynomial (Fin d × Exponent σ) k) (c : Fin d × Exponent σ → K)
    (hf : eval₂ (algebraMap k K) c f ≠ 0)
    (hz : ∀ (i₀ : Fin d) (j : σ), chartParameterMap k R B g a d i₀ j f = 0)
    (p : Fin d → restrictTotalDegree σ K 2)
    (hp : ∀ q, (parameterBasis K σ d).repr p q = c q)
    (hab : (fun j => algebraMap R K (g j)) ≠ algebraMap B K ∘ a)
    (hvalue : ∀ i, eval (fun j => algebraMap R K (g j)) (p i).val =
      eval (algebraMap B K ∘ a) (p i).val) :
    LinearIndependent K (fun i => residueGeneratorGradient k R K g
      (fun j => eval (fun l => algebraMap R K (g l)) (pderiv j (p i).val))) := by
  classical
  by_contra hli
  obtain ⟨i₀, w, hw, hderiv⟩ :=
    LinearMap.exists_normalized_relation_of_not_linearIndependent _ hli
  obtain ⟨j, hj⟩ : ∃ j, algebraMap R K (g j) ≠ algebraMap B K (a j) := by
    by_contra! h
    exact hab (funext h)
  let t := algebraMap R B (g j) - a j
  have ht : algebraMap B K t ≠ 0 := by
    change algebraMap B K (algebraMap R B (g j) - a j) ≠ 0
    rw [map_sub, ← IsScalarTower.algebraMap_apply R B K]
    exact sub_ne_zero.mpr hj
  let A := Ring B d i₀ t
  let e := evaluate B d i₀ t K w ht
  let : Algebra A K := e.toRingHom.toAlgebra
  have : IsScalarTower B A K := IsScalarTower.of_algebraMap_eq' e.comp_algebraMap.symm
  have : IsScalarTower R A K := IsScalarTower.to₁₃₄ R B A K
  have : IsScalarTower k A K := IsScalarTower.to₁₃₄ k B A K
  have ha : algebraMap A K ∘ (algebraMap B A ∘ a) = algebraMap B K ∘ a := by
    funext i
    exact (IsScalarTower.algebraMap_apply B A K (a i)).symm
  have hwA (i : Fin d) : algebraMap A K (weight B d i₀ t i) = w i :=
    evaluate_weight B d i₀ t K w ht hw i
  have hv : ∀ i, eval (fun j => algebraMap R K (g j)) (p i).val =
      eval (algebraMap A K ∘ (algebraMap B A ∘ a)) (p i).val := by
    simpa only [ha] using hvalue
  have hd : ∑ i, algebraMap A K (weight B d i₀ t i) • residueGeneratorGradient k R K g
      (fun j => eval (fun l => algebraMap R K (g l)) (pderiv j (p i).val)) = 0 := by
    simpa only [hwA] using hderiv
  have hzero := parameter_relation_vanishes k R A K g (algebraMap B A ∘ a) d
    (weight B d i₀ t) p hv hd f (hz i₀ j)
  have he : (fun q => (parameterBasis K σ d).repr p q) = c := funext hp
  rw [he, aeval_def] at hzero
  exact hf hzero

end QuadraticIncidence.MovingPointChart
