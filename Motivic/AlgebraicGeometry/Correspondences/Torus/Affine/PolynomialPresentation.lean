/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.AffineProduct

public import Motivic.AlgebraicGeometry.Correspondences.Generators.Basic
public import Motivic.Aglib.RingTheory.Polynomial.Normal.LaurentPresentation
public import Motivic.Aglib.RingTheory.Smooth.Normal
public import Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.BaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Monic polynomial presentations of original affine torus correspondences

The source is the spectrum of a smooth integral algebra over a field. Each
original integral finite correspondence to the multiplicative line has its
whole coordinate algebra presented by the minimal polynomial of its literal
Laurent coordinate. Normality, finite generation, scalar injectivity and
surjectivity of Laurent evaluation are extracted from the actual geometry.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent

universe u

namespace Motivic.AffineTorusPolynomialPresentation
open _root_.Algebra.Smooth

variable (k R : Type u) [Field k] [CommRing R] [Algebra k R]

/-- An original integral finite correspondence from `Spec R` to the multiplicative line. -/
abbrev Generator := FiniteCorrespondenceGenerator (baseMap k R) (laurentProjection (.of k))

variable {k R} (Z : Generator k R)

/-- The global section ring of the whole original integral support. -/
abbrev coordinateRing : CommRingCat.{u} := Γ(Z.scheme, ⊤)

instance supportAffine : IsAffine Z.scheme := isAffine_of_isAffineHom Z.projection

instance coordinateDomain : IsDomain (coordinateRing Z) := inferInstance

/-- The original scalar action is induced by the finite support projection. -/
def scalarMap : R →+* coordinateRing Z :=
  Z.projection.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom

instance coordinateAlgebra : Algebra R (coordinateRing Z) := (scalarMap Z).toAlgebra

instance coordinateFinite : Module.Finite R (coordinateRing Z) := by
  change (scalarMap Z).Finite
  exact Z.projection.finite_appTop.comp
    (RingHom.Finite.of_surjective _
      (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv.surjective)

/-- The original closed support, viewed in the canonical Laurent chart. -/
def laurentEmbedding : Z.scheme ⟶ Spec (.of (LaurentPolynomial R)) :=
  Z.inclusion ≫ (ambientIso k R).inv

instance laurentEmbedding_closed : IsClosedImmersion (laurentEmbedding Z) := by
  unfold laurentEmbedding
  infer_instance

@[reassoc] theorem laurentEmbedding_projection :
    laurentEmbedding Z ≫ laurentProjection (.of R) = Z.projection := by
  rw [← ambientIso_hom_fst k R]
  simp only [laurentEmbedding, Category.assoc, Iso.inv_hom_id_assoc]
  rfl

/-- Pullback from the actual Laurent coordinate ring to the whole support. -/
def laurentPullback : LaurentPolynomial R →+* coordinateRing Z :=
  (laurentEmbedding Z).appTop.hom.comp
    (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv.hom

/-- The support's actual Laurent coordinate, including its actual inverse. -/
def coordinateUnit : (coordinateRing Z)ˣ :=
  Units.map (laurentPullback Z).toMonoidHom (laurentCoordinateUnit (.of R))

theorem laurentPullback_C (r : R) :
    laurentPullback Z (LaurentPolynomial.C r) = scalarMap Z r := by
  have h := congrArg (fun f : Z.scheme ⟶ Spec (.of R) =>
    f.appTop ((Scheme.ΓSpecIso (.of R)).inv r)) (laurentEmbedding_projection Z)
  rw [Scheme.Hom.comp_appTop] at h
  have hc := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
      (LaurentPolynomial.C : R →+* LaurentPolynomial R))).symm r
  change (laurentProjection (.of R)).appTop ((Scheme.ΓSpecIso (.of R)).inv r) =
    (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv (LaurentPolynomial.C r) at hc
  simpa only [ConcreteCategory.comp_apply, hc, laurentPullback, scalarMap,
    RingHom.comp_apply] using h

/-- The closed immersion gives surjective actual Laurent evaluation. -/
theorem laurent_eval_surjective :
    Function.Surjective (LaurentPolynomial.eval₂ (algebraMap R (coordinateRing Z))
      (coordinateUnit Z)) := by
  have he : laurentPullback Z =
      LaurentPolynomial.eval₂ (algebraMap R (coordinateRing Z)) (coordinateUnit Z) := by
    apply CommRingCat.PolynomialLaurent.laurent_hom_ext
    · intro r
      rw [laurentPullback_C, LaurentPolynomial.eval₂_C]
      rfl
    · rw [LaurentPolynomial.eval₂_T, zpow_one]
      rfl
  rw [← he]
  exact (IsClosedImmersion.isAffine_surjective_of_isAffine (laurentEmbedding Z)).2.comp
    (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).symm.commRingCatIsoToRingEquiv.surjective

variable [IsDomain R]

/-- Source dominance forces injectivity of the original scalar homomorphism. -/
theorem scalarMap_injective : Function.Injective (scalarMap Z) := by
  have : Surjective Z.projection := ⟨Z.projection_surjective⟩
  have : IsSchemeTheoreticallyDominant Z.projection :=
    IsSchemeTheoreticallyDominant.of_isDominant Z.projection
  exact (Z.projection.app_injective ⊤).comp
    (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv.injective

instance coordinateTorsionFree : Module.IsTorsionFree R (coordinateRing Z) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr (scalarMap_injective Z)

variable [Algebra.Smooth k R]

/-- The entire original support algebra has the claimed constant-unit monic presentation. -/
def polynomialEquiv :
    AdjoinRoot (minpoly R (coordinateUnit Z : coordinateRing Z)) ≃ₐ[R] coordinateRing Z := by
  let : IsIntegrallyClosed R := isIntegrallyClosed_of_smooth_field k R
  exact Algebra.NormalLaurentPresentation.finiteQuotientEquiv (coordinateUnit Z)
    (laurent_eval_surjective Z)

@[simp] theorem polynomialEquiv_root :
    polynomialEquiv Z (AdjoinRoot.root (minpoly R (coordinateUnit Z : coordinateRing Z))) =
      (coordinateUnit Z : coordinateRing Z) := by
  let : IsIntegrallyClosed R := isIntegrallyClosed_of_smooth_field k R
  exact Algebra.NormalLaurentPresentation.finiteQuotientEquiv_root (coordinateUnit Z)
    (laurent_eval_surjective Z)

theorem coordinatePolynomial_constant_isUnit :
    IsUnit ((minpoly R (coordinateUnit Z : coordinateRing Z)).coeff 0) := by
  let : IsIntegrallyClosed R := isIntegrallyClosed_of_smooth_field k R
  exact Algebra.NormalLaurentPresentation.minpoly_constant_isUnit (coordinateUnit Z)
    (Algebra.IsIntegral.isIntegral _) (Algebra.IsIntegral.isIntegral _)

/-- In relative dimension one, every original integral finite torus support is finite free. -/
theorem coordinateFree : Module.Free R (coordinateRing Z) := by
  let : IsIntegrallyClosed R := isIntegrallyClosed_of_smooth_field k R
  exact Algebra.NormalLaurentPresentation.finite_quotient_free (coordinateUnit Z)
    (laurent_eval_surjective Z)

end Motivic.AffineTorusPolynomialPresentation
