/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.Quadratic.Infinity.InfinitySchemeEmpty
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.Quadratic.Compactification.OriginalEmbedding
public import Motivic.Aglib.RingTheory.Bertini.QuadraticParameterTuple

/-! # Literal quadratic graph equations on the native schematic image -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry _root_.MvPolynomial
universe u
namespace AlgebraicGeometry.Scheme

/-- The original coordinate pullback to the whole affine schematic image. -/
def affineImageCoordinateMap {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) :
    A →+* Γ((Spec.map (CommRingCat.ofHom φ)).image, ⊤) :=
  ((ΓSpecIso (.of A)).inv ≫ (Spec.map (CommRingCat.ofHom φ)).imageι.appTop).hom

/-- An equation vanishing under the original affine map vanishes on its entire
scheme-theoretic image, without passing to residue fields or a reduction. -/
theorem affineImage_equation_zero {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (z : A) (hz : φ z = 0) :
    (Spec.map (CommRingCat.ofHom φ)).imageι.appTop ((ΓSpecIso (.of A)).inv z) = 0 := by
  apply affineImageSectionMap_injective φ
  rw [map_zero]
  have he := affineImageSectionMap_comp φ
  have hz' := congrArg (fun t : CommRingCat.of A ⟶ CommRingCat.of B => t z) he
  exact hz'.trans hz

end AlgebraicGeometry.Scheme
namespace QuadraticIncidence.InfinityChart
variable (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R]
  {σ : Type u} [Fintype σ] (g : σ → R) (d : ℕ)

omit [IsDomain R] in
/-- The same unchanged quadratic function, expanded in its original monomial basis. -/
theorem originalFunction_eq_sum (c : Fin (d + 1) × Exponent σ → k) (i : Fin (d + 1)) :
    aeval g (parameterTuple k σ (d + 1) c i).val =
      ∑ e, algebraMap k R (c (i, e)) * monomialFunction k R g e := by
  classical
  simp only [parameterTuple, Finset.sum_apply, Pi.smul_apply,
    parameterBasis_apply, Pi.single_apply, Fintype.sum_prod_type]
  simp [monomialBasis_coe, monomialFunction, Algebra.smul_def]


/-- The graph on the original ratio chart: no equation or quotient is supplied externally. -/
def chartGraphEvaluation (j : Exponent σ) (c : Fin (d + 1) × Exponent σ → k) :
    MvPolynomial (Fin (d + 1)) (chart k R g j) →+* FractionRing R :=
  eval₂Hom (chart k R g j).val.toRingHom
    (fun i => algebraMap R (FractionRing R)
      (aeval g (parameterTuple k σ (d + 1) c i).val))

/-- The original graph equation is row_i minus target-coordinate_i times infinity. -/
def chartGraphEquation (j : Exponent σ) (c : Fin (d + 1) × Exponent σ → k)
    (i : Fin (d + 1)) : MvPolynomial (Fin (d + 1)) (chart k R g j) :=
  C (chartRow k R g d j c i) - X i * C (infinityCoordinate k R g j)

theorem chartRow_val (j : Exponent σ) (c : Fin (d + 1) × Exponent σ → k)
    (i : Fin (d + 1)) :
    ((chartRow k R g d j c i : chart k R g j) : FractionRing R) =
      algebraMap R (FractionRing R)
        (aeval g (parameterTuple k σ (d + 1) c i).val) *
          (infinityCoordinate k R g j : FractionRing R) := by
  rw [originalFunction_eq_sum]
  change (chart k R g j).val (∑ e, _) = _
  simp only [map_sum, map_mul, AlgHom.commutes,
    ← IsScalarTower.algebraMap_apply k R (FractionRing R)]
  change (∑ e, algebraMap k (FractionRing R) (c (i, e)) * ratio k R g j e) = _
  simp only [ratio, div_eq_mul_inv, Finset.sum_mul, mul_assoc]
  rfl

/-- The equation lies in the literal graph-evaluation kernel. -/
theorem chartGraphEquation_mem_ker (j : Exponent σ)
    (c : Fin (d + 1) × Exponent σ → k) (i : Fin (d + 1)) :
    chartGraphEquation k R g d j c i ∈ RingHom.ker (chartGraphEvaluation k R g d j c) := by
  change chartGraphEvaluation k R g d j c (chartGraphEquation k R g d j c i) = 0
  simp only [chartGraphEquation, map_sub, map_mul, chartGraphEvaluation, eval₂Hom_C, eval₂Hom_X']
  change (chartRow k R g d j c i : FractionRing R) -
    algebraMap R (FractionRing R)
      (aeval g (parameterTuple k σ (d + 1) c i).val) *
        (infinityCoordinate k R g j : FractionRing R) = 0
  rw [chartRow_val, sub_self]


/-- The actual native affine schematic image satisfies every original graph equation. -/
theorem chartGraphImage_equation_zero (j : Exponent σ)
    (c : Fin (d + 1) × Exponent σ → k) (i : Fin (d + 1)) :
    (Spec.map (CommRingCat.ofHom (chartGraphEvaluation k R g d j c))).imageι.appTop
      ((Scheme.ΓSpecIso (.of _)).inv (chartGraphEquation k R g d j c i)) = 0 :=
  Scheme.affineImage_equation_zero _ _ (chartGraphEquation_mem_ker k R g d j c i)

end QuadraticIncidence.InfinityChart

namespace QuadraticIncidence.InfinityChart
variable (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R]
  {σ : Type u} [Fintype σ] (g : σ → R) (d : ℕ)

/-- The literal pullback of ambient polynomial coordinates to the native image. -/
abbrev chartGraphImage (j : Exponent σ) (c : Fin (d + 1) × Exponent σ → k) :
    Scheme.{u} :=
  (Spec.map (@CommRingCat.ofHom
    (MvPolynomial (Fin (d + 1)) (chart k R g j)) (FractionRing R)
    inferInstance inferInstance (chartGraphEvaluation k R g d j c))).image

abbrev chartGraphImageRingMap (j : Exponent σ) (c : Fin (d + 1) × Exponent σ → k) :=
  @Scheme.affineImageCoordinateMap
    (MvPolynomial (Fin (d + 1)) (chart k R g j)) (FractionRing R)
    inferInstance inferInstance (chartGraphEvaluation k R g d j c)


/-- The actual infinity coordinate is a unit on the full graph image chart. -/
theorem chartGraphImage_infinity_isUnit (j : Exponent σ)
    (hj : monomialFunction k R g j ≠ 0) (c : Fin (d + 1) × Exponent σ → k)
    (hc : NoCommonInfinityZero k R g d c) :
    IsUnit (chartGraphImageRingMap k R g d j c (C (infinityCoordinate k R g j))) := by
  let ψ := chartGraphImageRingMap k R g d j c
  let α := ψ.comp (C : chart k R g j →+* MvPolynomial (Fin (d + 1)) (chart k R g j))
  let I := Ideal.span ({α (infinityCoordinate k R g j)} : Set _)
  have hrows : Ideal.span (Set.range (chartRow k R g d j c)) ≤ Ideal.comap α I := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have he : ψ (C (chartRow k R g d j c i)) =
        ψ (X i) * ψ (C (infinityCoordinate k R g j)) := by
      apply sub_eq_zero.mp
      rw [← map_mul, ← map_sub]
      exact chartGraphImage_equation_zero k R g d j c i
    change ψ (C (chartRow k R g d j c i)) ∈ I
    rw [he]
    exact I.mul_mem_left _ (Ideal.subset_span (Set.mem_singleton _))
  have hh : Ideal.span {infinityCoordinate k R g j} ≤ Ideal.comap α I := by
    apply Ideal.span_le.mpr
    rintro _ rfl
    exact Ideal.subset_span (Set.mem_singleton _)
  have htop : (⊤ : Ideal (chart k R g j)) ≤ Ideal.comap α I := by
    rw [← chartRow_infinity_span_eq_top k R g d j hj c hc]
    exact sup_le hrows hh
  have hone : (1 : _) ∈ I := by
    have H := htop (show (1 : chart k R g j) ∈ ⊤ from trivial)
    change α 1 ∈ I at H
    simpa only [map_one] using H
  exact (Ideal.span_singleton_eq_top).mp ((Ideal.eq_top_iff_one I).mpr hone)

end QuadraticIncidence.InfinityChart
