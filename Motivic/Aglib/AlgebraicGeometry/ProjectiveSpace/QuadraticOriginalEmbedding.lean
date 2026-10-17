/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.QuadraticOriginalClosure
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
/-! # The original quadratic map is an actual immersion for original algebra generators -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry ProjectiveSpace MvPolynomial
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace QuadraticIncidence.InfinityChart
variable (k R : Type u) [Field k] [CommRing R] [Algebra k R]
  {σ : Type u} (g : σ → R)

/-- The original linear coordinate is included in the same degree-at-most-two family. -/
def linearIndex (i : σ) : Exponent σ := ⟨Finsupp.single i 1, by simp⟩

theorem linearIndex_ne_constant (i : σ) : linearIndex i ≠ constantIndex := by
  intro h
  have h' := congrArg (fun e : Exponent σ => e.val i) h
  simp [linearIndex, constantIndex] at h'

@[simp]
theorem monomialFunction_linear (i : σ) : monomialFunction k R g (linearIndex i) = g i := by
  change aeval g (MvPolynomial.X i) = g i
  simp

/-- No new embedding coordinates are chosen: the original quadratic family already
contains the given affine algebra generators. -/
theorem quadraticConstantChartMap_surjective
    (hg : Algebra.adjoin k (Set.range g) = ⊤) :
    Function.Surjective (quadraticConstantChartMap k R g) := by
  have hs : Function.Surjective
      (aeval (fun e : {e : Exponent σ // e ≠ constantIndex} =>
        monomialFunction k R g e.val) : MvPolynomial _ k →ₐ[k] R) := by
    rw [← AlgHom.range_eq_top, aeval_range]
    apply top_unique
    rw [← hg]
    apply Algebra.adjoin_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨linearIndex i, linearIndex_ne_constant i⟩, monomialFunction_linear k R g i⟩
  exact hs.comp (coordinateRingEquivPolynomial k (Exponent σ) constantIndex).surjective

theorem quadraticOriginalMap_isImmersion
    (hg : Algebra.adjoin k (Set.range g) = ⊤) : IsImmersion (quadraticOriginalMap k R g) := by
  have := IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (quadraticConstantChartMap k R g))
    (quadraticConstantChartMap_surjective k R g hg)
  dsimp only [quadraticOriginalMap]
  infer_instance

/-- The original affine scheme is an actual open subscheme of its schematic closure. -/
theorem quadraticOriginalMap_toImage_isOpenImmersion [IsNoetherianRing R]
    (hg : Algebra.adjoin k (Set.range g) = ⊤) :
    IsOpenImmersion (quadraticOriginalMap k R g).toImage := by
  have := quadraticOriginalMap_isImmersion k R g hg
  infer_instance

end QuadraticIncidence.InfinityChart
