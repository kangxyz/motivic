/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.QuadraticOriginalEmbedding
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.QuadraticGlobalChartCoordinates
/-! # The original affine quadratic embedding and its one proper closure -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry ProjectiveSpace
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace QuadraticIncidence.InfinityChart
variable (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R]
  {σ : Type u} (g : σ → R)

/-- The original structure map of the single projective quadratic closure. -/
def quadraticImageProjection : quadraticProjectiveImage k R g ⟶ Spec (.of k) :=
  (quadraticProjectiveGenericMap k R g).imageι ≫ toSpec k (Exponent σ)

instance [Finite σ] : IsProper (quadraticImageProjection k R g) := by
  dsimp only [quadraticImageProjection]
  infer_instance

/-- The entire original affine scheme, not a smaller parameter neighborhood. -/
def quadraticOriginalToImage : Spec (.of R) ⟶ quadraticProjectiveImage k R g :=
  (quadraticOriginalMap k R g).toImage ≫ (quadraticOriginalImageIso k R g).hom

@[reassoc]
theorem quadraticOriginalToImage_inclusion :
    quadraticOriginalToImage k R g ≫ (quadraticProjectiveGenericMap k R g).imageι =
      quadraticOriginalMap k R g := by
  rw [quadraticOriginalToImage, Category.assoc, quadraticOriginalImageIso_hom_inclusion,
    Scheme.Hom.toImage_imageι]

omit [IsDomain R] in
theorem quadraticConstantChartMap_coefficient (a : k) :
    quadraticConstantChartMap k R g
      (coordinateRingCoefficient k (Exponent σ) constantIndex a) = algebraMap k R a := by
  simp [quadraticConstantChartMap, coordinateRingEquivPolynomial,
    coordinateRingToPolynomial_coefficient]

@[reassoc]
theorem quadraticOriginalToImage_projection :
    quadraticOriginalToImage k R g ≫ quadraticImageProjection k R g =
      Spec.map (CommRingCat.ofHom (algebraMap k R)) := by
  rw [quadraticImageProjection, ← Category.assoc, quadraticOriginalToImage_inclusion,
    quadraticOriginalMap, Category.assoc, coordinateChart_toSpec,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  ext a
  exact quadraticConstantChartMap_coefficient k R g a

/-- The actual ratio chart map respects the unchanged ground field structure. -/
@[reassoc]
theorem quadraticRatioChartToImage_projection (j : Exponent σ)
    (hj : monomialFunction k R g j ≠ 0) :
    quadraticRatioChartToImage k R g j hj ≫ quadraticImageProjection k R g =
      Spec.map (CommRingCat.ofHom (algebraMap k (chart k R g j))) := by
  rw [quadraticImageProjection, ← Category.assoc, quadraticRatioChartToImage_inclusion,
    Category.assoc, coordinateChart_toSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  ext a
  change nativeDehomogenization k R g j
    (coordinateRingCoefficient k (Exponent σ) j a) = algebraMap k (FractionRing R) a
  exact nativeDehomogenization_coefficient k R g j a

variable [IsNoetherianRing R]

theorem quadraticOriginalToImage_isOpenImmersion
    (hg : Algebra.adjoin k (Set.range g) = ⊤) :
    IsOpenImmersion (quadraticOriginalToImage k R g) := by
  have := quadraticOriginalMap_toImage_isOpenImmersion k R g hg
  dsimp only [quadraticOriginalToImage]
  infer_instance

/-- The original affine scheme is exactly the constant-coordinate chart of the closure,
including its whole scheme structure. -/
theorem quadraticOriginalToImage_isPullback
    (hg : Algebra.adjoin k (Set.range g) = ⊤) :
    IsPullback (Spec.map (CommRingCat.ofHom (quadraticConstantChartMap k R g)))
      (quadraticOriginalToImage k R g) (quadraticChartInclusion k constantIndex)
      (quadraticProjectiveGenericMap k R g).imageι := by
  have := IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (quadraticConstantChartMap k R g))
    (quadraticConstantChartMap_surjective k R g hg)
  apply isPullback_of_isClosedImmersion _ _ _ _
  · exact (quadraticOriginalToImage_inclusion k R g).symm
  · rw [Scheme.IdealSheafData.ker_subschemeι, ← quadraticOriginalMap_ker]
    exact Scheme.ker_comap_open_factor (quadraticOriginalMap k R g)
      (quadraticChartInclusion k constantIndex)
      (Spec.map (CommRingCat.ofHom (quadraticConstantChartMap k R g))) rfl

/-- The full constant chart is literally the original affine scheme. -/
def quadraticOriginalConstantChartIso
    (hg : Algebra.adjoin k (Set.range g) = ⊤) :
    pullback (quadraticChartInclusion k constantIndex)
      (quadraticProjectiveGenericMap k R g).imageι ≅ Spec (.of R) :=
  (quadraticOriginalToImage_isPullback k R g hg).isoPullback.symm

@[reassoc]
theorem quadraticOriginalConstantChartIso_hom_toImage
    (hg : Algebra.adjoin k (Set.range g) = ⊤) :
    (quadraticOriginalConstantChartIso k R g hg).hom ≫ quadraticOriginalToImage k R g =
      pullback.snd (quadraticChartInclusion k constantIndex)
        (quadraticProjectiveGenericMap k R g).imageι :=
  (quadraticOriginalToImage_isPullback k R g hg).isoPullback_inv_snd

end QuadraticIncidence.InfinityChart
