/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Kaehler.ResidueFunctionBasis
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Cotangent gradients from an actual affine embedding

Algebra generators, not independently chosen smooth coordinates, give a
surjective ambient-gradient map onto the actual residue cotangent space.
-/
@[expose] public noncomputable section
open Module TensorProduct KaehlerDifferential
universe u v w z
namespace KaehlerDifferential
variable (k : Type u) (R : Type v) (K : Type w)
  [CommRing k] [CommRing R] [CommRing K] [Algebra k R] [Algebra R K]
  {σ : Type z}

/-- The differentials of the original algebra generators span the actual module. -/
theorem span_generator_differentials (g : σ → R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) :
    Submodule.span R (Set.range (fun i => D k R (g i))) = ⊤ := by
  apply top_unique
  rw [← span_range_derivation k R, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ Algebra.adjoin k (Set.range g) := by rw [hg]; trivial
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact Submodule.subset_span ⟨i, rfl⟩
  | algebraMap r => simp
  | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
  | mul x y _ _ hx hy =>
    simpa only [Derivation.leibniz] using!
      Submodule.add_mem _ (Submodule.smul_mem _ x hy) (Submodule.smul_mem _ y hx)

/-- Base changing the same original generators preserves their spanning property. -/
theorem span_residue_generator_differentials (g : σ → R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) :
    Submodule.span K (Set.range (fun i => (1 ⊗ₜ[R] D k R (g i) :
      K ⊗[R] Ω[R⁄k]))) = ⊤ := by
  have h := congrArg (Submodule.baseChange K) (span_generator_differentials k R g hg)
  simpa only [Submodule.baseChange_span, Submodule.baseChange_top,
    ← Set.range_comp, Function.comp_def, TensorProduct.mk_apply] using h

/-- The actual gradient quotient from the fixed affine embedding. -/
def residueGeneratorGradient [Fintype σ] (g : σ → R) :
    (σ → K) →ₗ[K] K ⊗[R] Ω[R⁄k] :=
  Fintype.linearCombination K (fun i => 1 ⊗ₜ[R] D k R (g i))

theorem residueGeneratorGradient_surjective [Fintype σ] (g : σ → R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) :
    Function.Surjective (residueGeneratorGradient k R K g) := by
  apply LinearMap.range_eq_top.mp
  rw [residueGeneratorGradient, Fintype.range_linearCombination]
  exact span_residue_generator_differentials k R K g hg

end KaehlerDifferential
