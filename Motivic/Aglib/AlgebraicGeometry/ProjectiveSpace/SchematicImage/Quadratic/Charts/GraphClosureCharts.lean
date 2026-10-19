/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.PolynomialGraphChart

/-! # Charts of the actual graph closure of the unchanged quadratic tuple -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry _root_.MvPolynomial ProjectiveSpace
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace QuadraticIncidence.InfinityChart
variable (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R]
  {σ : Type u} [Fintype σ] (g : σ → R) (d : ℕ)

instance ratioChartToImage_isOpenImmersion (j : Exponent σ)
    (hj : monomialFunction k R g j ≠ 0) :
    IsOpenImmersion (quadraticRatioChartToImage k R g j hj) := by
  dsimp [quadraticRatioChartToImage]
  infer_instance

/-- The target coordinates are the literal original quadratic functions. -/
def quadraticTupleMap (c : Fin (d + 1) × Exponent σ → k) :
    Spec (.of R) ⟶ Spec (.of (MvPolynomial (Fin (d + 1)) k)) :=
  Spec.map (CommRingCat.ofHom
    (aeval (fun i => aeval g (parameterTuple k σ (d + 1) c i).val)).toRingHom)

/-- The actual original graph in the original proper closure times affine space. -/
def quadraticOriginalGraph (c : Fin (d + 1) × Exponent σ → k) :
    Spec (.of R) ⟶ pullback (quadraticImageProjection k R g)
      (Spec.map (CommRingCat.ofHom (C : k →+* MvPolynomial (Fin (d + 1)) k))) :=
  pullback.lift (quadraticOriginalToImage k R g) (quadraticTupleMap k R g d c) (by
    rw [quadraticOriginalToImage_projection, quadraticTupleMap,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact (aeval (R := k)
      (fun i => aeval g (parameterTuple k σ (d + 1) c i).val)).comp_algebraMap.symm)

/-- Its original generic restriction is used only to compute the identical kernel. -/
def quadraticGenericGraph (c : Fin (d + 1) × Exponent σ → k) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) ≫
    quadraticOriginalGraph k R g d c

theorem quadraticOriginalGraph_ker (c : Fin (d + 1) × Exponent σ → k) :
    (quadraticOriginalGraph k R g d c).ker = (quadraticGenericGraph k R g d c).ker := by
  rw [quadraticGenericGraph, Scheme.Hom.ker_comp,
    Scheme.ker_SpecMap_eq_bot_of_injective _ (IsFractionRing.injective R (FractionRing R)),
    Scheme.IdealSheafData.map_bot]

/-- The unchanged original ratio chart, base changed in the actual graph ambient. -/
abbrev quadraticGraphAmbientChart (j : Exponent σ) (hj : monomialFunction k R g j ≠ 0) :=
  Scheme.polynomialChart k (chart k R g j) (d + 1) (quadraticImageProjection k R g)
    (quadraticRatioChartToImage k R g j hj) (quadraticRatioChartToImage_projection k R g j hj)

omit [Fintype σ] in
/-- The same generic point of the original closure factors through every nonzero chart. -/
theorem ratioChart_generic (j : Exponent σ) (hj : monomialFunction k R g j ≠ 0) :
    Spec.map (CommRingCat.ofHom (chart k R g j).val.toRingHom) ≫
      quadraticRatioChartToImage k R g j hj =
      Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) ≫
        quadraticOriginalToImage k R g := by
  apply (cancel_mono (quadraticProjectiveGenericMap k R g).imageι).mp
  rw [Category.assoc, quadraticRatioChartToImage_inclusion,
    Category.assoc, quadraticOriginalToImage_inclusion,
    quadraticOriginalMap_generic, ← Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  exact nativeChartGenericMap_projective k R g j hj

/-- The polynomial graph-chart map factors the one original generic graph. -/
theorem chartGraphEvaluation_global (j : Exponent σ)
    (hj : monomialFunction k R g j ≠ 0) (c : Fin (d + 1) × Exponent σ → k) :
    Spec.map (CommRingCat.ofHom (chartGraphEvaluation k R g d j c)) ≫
      quadraticGraphAmbientChart k R g d j hj = quadraticGenericGraph k R g d c := by
  apply pullback.hom_ext
  · simp only [Category.assoc, quadraticGraphAmbientChart, Scheme.polynomialChart_fst,
      quadraticGenericGraph, quadraticOriginalGraph, pullback.lift_fst]
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [chartGraphEvaluation, eval₂Hom_comp_C]
    exact ratioChart_generic k R g j hj
  · simp only [Category.assoc, quadraticGraphAmbientChart, Scheme.polynomialChart_snd,
      quadraticGenericGraph, quadraticOriginalGraph, pullback.lift_snd, quadraticTupleMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [chartGraphEvaluation, ← IsScalarTower.algebraMap_apply k R (FractionRing R)]
    · intro i
      simp [chartGraphEvaluation]

/-- The chart of the single global schematic image is exactly the native local
polynomial graph image. No independent replacement closure is used. -/
def quadraticGraphImageChartIso (j : Exponent σ)
    (hj : monomialFunction k R g j ≠ 0) (c : Fin (d + 1) × Exponent σ → k) :
    pullback (quadraticGraphAmbientChart k R g d j hj)
      (quadraticGenericGraph k R g d c).imageι ≅ chartGraphImage k R g d j c :=
  Scheme.imageOpenChartIso (quadraticGenericGraph k R g d c)
    (quadraticGraphAmbientChart k R g d j hj)
    (Spec.map (CommRingCat.ofHom (chartGraphEvaluation k R g d j c)))
    (chartGraphEvaluation_global k R g d j hj c)

@[reassoc]
theorem quadraticGraphImageChartIso_hom_inclusion (j : Exponent σ)
    (hj : monomialFunction k R g j ≠ 0) (c : Fin (d + 1) × Exponent σ → k) :
    (quadraticGraphImageChartIso k R g d j hj c).hom ≫
      (Spec.map (@CommRingCat.ofHom
        (MvPolynomial (Fin (d + 1)) (chart k R g j)) (FractionRing R)
        inferInstance inferInstance (chartGraphEvaluation k R g d j c))).imageι =
      pullback.fst (quadraticGraphAmbientChart k R g d j hj)
        (quadraticGenericGraph k R g d c).imageι :=
  Scheme.imageOpenChartIso_hom_inclusion _ _ _ _

end QuadraticIncidence.InfinityChart
