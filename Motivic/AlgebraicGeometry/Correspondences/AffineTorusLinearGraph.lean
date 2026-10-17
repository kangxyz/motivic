/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.AffineTorusPolynomialBaseChange
public import Motivic.AlgebraicGeometry.Correspondences.DiagonalZeroCycle
public import Mathlib.RingTheory.Polynomial.Quotient

/-! # Literal linear-polynomial divisors are the original unit graphs -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent

universe u

namespace Motivic.AffineTorusPolynomialPresentation

variable {k R : Type u} [Field k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]

/-- The literal morphism of a unit-valued point over the affine source. -/
def unitMorphism (u : Rˣ) : affineSite k R ⟶ SmoothSite.torus (.of k) :=
  SmoothSite.homMk (Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ (algebraMap k R) u))) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext r
    exact LaurentPolynomial.eval₂_C _ _ _)

/-- The constant term of the literal linear equation is invertible. -/
theorem linear_constant_isUnit (u : Rˣ) : IsUnit ((X - C (u : R)).coeff 0) := by
  simp [u.isUnit.neg]

omit [Field k] [Algebra k R] [Algebra.Smooth k R] in
/-- The original linear quotient's structural map is an isomorphism, not just finite flat. -/
instance polynomialProjection_linear_isIso (u : Rˣ) :
    IsIso (polynomialProjection (X - C (u : R))) := by
  have he : CommRingCat.ofHom (AdjoinRoot.of (X - C (u : R))) =
      (quotientSpanXSubCAlgEquiv (u : R)).toRingEquiv.toCommRingCatIso.inv := by
    ext r
    exact (quotientSpanXSubCAlgEquiv_symm_apply (u : R) r).symm
  unfold polynomialProjection
  rw [he]
  infer_instance

/-- The linear quotient's original target coordinate is exactly the specified unit. -/
@[reassoc] theorem polynomialInclusion_linear_target (u : Rˣ) :
    polynomialInclusion (k := k) (X - C (u : R)) (linear_constant_isUnit u) ≫
        pullback.snd _ _ =
      polynomialProjection (X - C (u : R)) ≫ (unitMorphism (k := k) u).left := by
  simp only [polynomialInclusion, Category.assoc, ambientIso_hom_snd]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply CommRingCat.PolynomialLaurent.laurent_hom_ext
  · intro r
    change LaurentPolynomial.eval₂ (AdjoinRoot.of (X - C (u : R)))
      (polynomialUnit (X - C (u : R)) (linear_constant_isUnit u))
      ((CommRingCat.PolynomialLaurent.laurentMap (CommRingCat.ofHom (algebraMap k R)))
        (LaurentPolynomial.C r)) =
      AdjoinRoot.of (X - C (u : R)) (LaurentPolynomial.eval₂ (algebraMap k R) u
        (LaurentPolynomial.C r))
    rw [CommRingCat.PolynomialLaurent.laurentMap_C]
    simp
  · change LaurentPolynomial.eval₂ (AdjoinRoot.of (X - C (u : R)))
      (polynomialUnit (X - C (u : R)) (linear_constant_isUnit u))
      ((CommRingCat.PolynomialLaurent.laurentMap (CommRingCat.ofHom (algebraMap k R)))
        (LaurentPolynomial.T 1)) =
      AdjoinRoot.of (X - C (u : R)) (LaurentPolynomial.eval₂ (algebraMap k R) u
        (LaurentPolynomial.T 1))
    rw [CommRingCat.PolynomialLaurent.laurentMap_T]
    simp only [LaurentPolynomial.eval₂_T, zpow_one, polynomialUnit_val]
    have h := AdjoinRoot.eval₂_root (X - C (u : R))
    simpa only [eval₂_sub, eval₂_X, eval₂_C, sub_eq_zero] using h

variable [IsNoetherianRing R]

/-- The whole original linear polynomial cycle equals the actual unit graph correspondence. -/
theorem polynomialCycle_linear_graph (u : Rˣ) :
    polynomialCycle (k := k) (X - C (u : R)) (monic_X_sub_C _) (linear_constant_isUnit u) =
      (Cor.graphFunctor k).map (unitMorphism (k := k) u) := by
  let p : R[X] := X - C (u : R)
  let h : (𝟙 (Spec (.of R))) ≫ baseMap k R = (unitMorphism (k := k) u).left ≫
      laurentProjection (.of k) := (Category.id_comp _).trans
        (MorphismProperty.Over.w (unitMorphism (k := k) u)).symm
  let j := pullback.lift (𝟙 (Spec (.of R))) (unitMorphism (k := k) u).left h
  let : IsFinite j := FiniteFlatCorrespondence.isFinite_productMap
    (𝟙 (Spec (.of R))) j (pullback.lift_fst _ _ _)
  have hi : polynomialInclusion (k := k) p (linear_constant_isUnit u) =
      polynomialProjection p ≫ j := by
    apply pullback.hom_ext
    · simp [j]
    · simpa only [j, Category.assoc, pullback.lift_snd] using
        polynomialInclusion_linear_target (k := k) u
  have hg : FiniteCorrespondence.toIntegralCycle (f := baseMap k R)
      (g := laurentProjection (.of k)) ((Cor.graphFunctor k).map (unitMorphism (k := k) u)) =
      IntegralCycle.finitePushforward j (fundamentalCycle (Spec (.of R))) := by
    have he := Cor.toIntegralCycle_ofFiniteFlatSpan
      (X := affineSite k R) (Y := SmoothSite.torus (.of k))
      (𝟙 (Spec (.of R))) (unitMorphism (k := k) u).left h
    have hs : Cor.ofFiniteFlatSpan (X := affineSite k R) (Y := SmoothSite.torus (.of k))
        (𝟙 (Spec (.of R))) (unitMorphism (k := k) u).left h =
      (Cor.graphFunctor k).map (unitMorphism (k := k) u) :=
      DiagonalZeroCycle.ofFiniteFlatSpan_id (unitMorphism (k := k) u)
    exact (congrArg (FiniteCorrespondence.toIntegralCycle
      (f := baseMap k R) (g := laurentProjection (.of k))) hs.symm).trans he
  apply FiniteCorrespondence.toIntegralCycle_injective
  rw [toIntegralCycle_polynomialCycle, hg]
  change IntegralCycle.finitePushforward (polynomialInclusion (k := k) p
    (linear_constant_isUnit u)) (fundamentalCycle (Spec (.of (AdjoinRoot p)))) = _
  simp only [hi, IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply,
    finitePushforward_fundamentalCycle]

end Motivic.AffineTorusPolynomialPresentation
