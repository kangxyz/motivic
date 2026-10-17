/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.QuadraticGraphClosureCharts
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.QuadraticGraphChartBoundary
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.QuadraticOriginalOpen
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.SchematicImageOpenChartProperty

/-! # The actual quadratic graph closure has no points at infinity -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry MvPolynomial ProjectiveSpace
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace QuadraticIncidence.InfinityChart
variable (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R]
  {σ : Type u} (g : σ → R)

/-- The actual nonzero-pivot ratio charts cover the original global closure. -/
theorem exists_ratioChart_preimage (x : quadraticProjectiveImage k R g) :
    ∃ (j : Exponent σ) (hj : monomialFunction k R g j ≠ 0)
      (y : Spec (.of (chart k R g j))), quadraticRatioChartToImage k R g j hj y = x := by
  obtain ⟨j, hj, hx⟩ := quadraticProjectiveImage_exists_chart k R g x
  have hr : (quadraticProjectiveGenericMap k R g).imageι x ∈
      Set.range (quadraticChartInclusion k j) := by
    rw [← Scheme.Hom.coe_opensRange]
    have he : (quadraticChartInclusion k j).opensRange = coordinateOpen k (Exponent σ) j :=
      Proj.opensRange_awayι ..
    rw [he]
    exact hx
  obtain ⟨a, ha⟩ := hr
  obtain ⟨z, _, hz⟩ := Scheme.exists_preimage_of_isPullback
    (IsPullback.of_hasPullback (quadraticChartInclusion k j)
      (quadraticProjectiveGenericMap k R g).imageι) a x ha
  refine ⟨j, hj, (quadraticProjectiveImageChartIso k R g j hj).hom z, ?_⟩
  change ((quadraticProjectiveImageChartIso k R g j hj).hom ≫
    (quadraticProjectiveImageChartIso k R g j hj).inv ≫ pullback.snd _ _) z = x
  rw [Iso.hom_inv_id_assoc]
  exact hz

variable [Fintype σ] [IsNoetherianRing R] (d : ℕ)

/-- Scheme-theoretic graph equations and the full ideal identity exclude every
point of the actual global graph boundary. -/
theorem quadraticGenericGraph_no_infinity
    (hg : Algebra.adjoin k (Set.range g) = ⊤)
    (c : Fin (d + 1) × Exponent σ → k) (hc : NoCommonInfinityZero k R g d c)
    (x : (quadraticGenericGraph k R g d c).image) :
    ((quadraticGenericGraph k R g d c).imageι ≫ pullback.fst _ _) x ∈
      Set.range (quadraticOriginalToImage k R g) := by
  let π := pullback.fst (quadraticImageProjection k R g)
    (Spec.map (CommRingCat.ofHom (C : k →+* MvPolynomial (Fin (d + 1)) k)))
  let a := (quadraticGenericGraph k R g d c).imageι x
  obtain ⟨j, hj, y, hy⟩ := exists_ratioChart_preimage k R g (π a)
  obtain ⟨b, hb, hby⟩ := Scheme.exists_preimage_of_isPullback
    (Scheme.polynomialChart_isPullback k (chart k R g j) (d + 1)
      (quadraticImageProjection k R g) (quadraticRatioChartToImage k R g j hj)
      (quadraticRatioChartToImage_projection k R g j hj)) a y hy.symm
  apply Scheme.point_property_of_pullback_chart
    (quadraticGenericGraph k R g d c).imageι (quadraticGraphAmbientChart k R g d j hj)
    (Spec.map (@CommRingCat.ofHom
      (MvPolynomial (Fin (d + 1)) (chart k R g j)) (FractionRing R)
      inferInstance inferInstance (chartGraphEvaluation k R g d j c))).imageι
    (quadraticGraphImageChartIso k R g d j hj c)
    (quadraticGraphImageChartIso_hom_inclusion k R g d j hj c)
    {z | π z ∈ Set.range (quadraticOriginalToImage k R g)} _ x ⟨b, hb⟩
  intro u
  have hu := chartGraphImage_no_infinity k R g d j hj c hc u
  have hlocal : (Spec.map (CommRingCat.ofHom (C : chart k R g j →+*
      MvPolynomial (Fin (d + 1)) (chart k R g j))))
      ((Spec.map (@CommRingCat.ofHom
        (MvPolynomial (Fin (d + 1)) (chart k R g j)) (FractionRing R)
        inferInstance inferInstance (chartGraphEvaluation k R g d j c))).imageι u) ∈
      quadraticRatioChartToImage k R g j hj ⁻¹' Set.range (quadraticOriginalToImage k R g) := by
    rw [quadraticRatioChartToImage_preimage_original k R g hg j hj]
    exact hu
  change (quadraticGraphAmbientChart k R g d j hj ≫ π)
    ((Spec.map (@CommRingCat.ofHom
      (MvPolynomial (Fin (d + 1)) (chart k R g j)) (FractionRing R)
      inferInstance inferInstance (chartGraphEvaluation k R g d j c))).imageι u) ∈
      Set.range (quadraticOriginalToImage k R g)
  rw [Scheme.polynomialChart_fst]
  exact hlocal

/-- The statement is for the original graph's native scheme-theoretic image,
using exact kernel equality rather than a replacement by reduced support. -/
theorem quadraticOriginalGraph_no_infinity
    (hg : Algebra.adjoin k (Set.range g) = ⊤)
    (c : Fin (d + 1) × Exponent σ → k) (hc : NoCommonInfinityZero k R g d c)
    (x : (quadraticOriginalGraph k R g d c).image) :
    ((quadraticOriginalGraph k R g d c).imageι ≫ pullback.fst _ _) x ∈
      Set.range (quadraticOriginalToImage k R g) := by
  have hr : Set.range (quadraticOriginalGraph k R g d c).imageι =
      Set.range (quadraticGenericGraph k R g d c).imageι := by
    change Set.range (quadraticOriginalGraph k R g d c).ker.subschemeι =
      Set.range (quadraticGenericGraph k R g d c).ker.subschemeι
    rw [quadraticOriginalGraph_ker]
  obtain ⟨y, hy⟩ := hr ▸ (show (quadraticOriginalGraph k R g d c).imageι x ∈
    Set.range (quadraticOriginalGraph k R g d c).imageι from ⟨x, rfl⟩)
  have H := quadraticGenericGraph_no_infinity k R g d hg c hc y
  simpa only [Scheme.Hom.comp_apply, hy] using H

end QuadraticIncidence.InfinityChart
