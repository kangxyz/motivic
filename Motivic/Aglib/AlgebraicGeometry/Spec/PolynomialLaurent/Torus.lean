/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# The smooth Laurent torus and its identity section

The Laurent spectrum is the principal open complement of zero in the affine
line. Its actual coefficient projection is smooth, separated and of finite
type over every commutative ring. Evaluation of the Laurent coordinate at one
gives its literal identity section.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.PolynomialLaurent

instance instSmoothPolynomialProjection (R : CommRingCat.{u}) :
    Smooth (polynomialProjection R) := by
  apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
  change (algebraMap R (Polynomial R)).Smooth
  rw [RingHom.smooth_algebraMap]
  exact ⟨inferInstance, inferInstance⟩

instance instSmoothLaurentProjection (R : CommRingCat.{u}) :
    Smooth (laurentProjection R) := by
  rw [← laurentPlus_projection]
  infer_instance

instance instIsSeparatedLaurentProjection (R : CommRingCat.{u}) :
    IsSeparated (laurentProjection R) := by
  unfold laurentProjection
  infer_instance

instance instQuasiCompactLaurentProjection (R : CommRingCat.{u}) :
    QuasiCompact (laurentProjection R) := by
  unfold laurentProjection
  infer_instance

/-- Finite type is expressed by local finite type and quasi-compactness. -/
theorem laurentProjection_finiteType (R : CommRingCat.{u}) :
    LocallyOfFiniteType (laurentProjection R) ∧ QuasiCompact (laurentProjection R) :=
  ⟨inferInstance, inferInstance⟩

/-- Evaluation of a Laurent polynomial at the identity unit. -/
def laurentEvalOne (R : CommRingCat.{u}) : LaurentPolynomial R →+* R :=
  LaurentPolynomial.eval₂ (RingHom.id R) 1

@[simp] theorem laurentEvalOne_C (R : CommRingCat.{u}) (r : R) :
    laurentEvalOne R (LaurentPolynomial.C r) = r :=
  LaurentPolynomial.eval₂_C _ _ _

@[simp] theorem laurentEvalOne_T (R : CommRingCat.{u}) (n : ℤ) :
    laurentEvalOne R (LaurentPolynomial.T n) = 1 := by
  simp [laurentEvalOne, LaurentPolynomial.eval₂_T]

/-- The actual identity section, induced by evaluation at one. -/
def laurentOneSection (R : CommRingCat.{u}) :
    Spec R ⟶ Spec (.of (LaurentPolynomial R)) :=
  Spec.map (CommRingCat.ofHom (laurentEvalOne R))

instance instIsClosedImmersionLaurentOneSection (R : CommRingCat.{u}) :
    IsClosedImmersion (laurentOneSection R) :=
  IsClosedImmersion.spec_of_surjective _ (fun r => ⟨LaurentPolynomial.C r,
    laurentEvalOne_C R r⟩)

@[reassoc (attr := simp)]
theorem laurentOneSection_projection (R : CommRingCat.{u}) :
    laurentOneSection R ≫ laurentProjection R = 𝟙 (Spec R) := by
  have h : CommRingCat.ofHom (LaurentPolynomial.C : R →+* LaurentPolynomial R) ≫
      CommRingCat.ofHom (laurentEvalOne R) = 𝟙 R := by
    ext r
    exact laurentEvalOne_C R r
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, h, Spec.map_id]

/-- Pulling back the actual Laurent coordinate along the identity section gives one. -/
@[simp] theorem laurentOneSection_appTop_coordinate (R : CommRingCat.{u}) :
    (laurentOneSection R).appTop (laurentGlobalUnit R :
      Γ(Spec (.of (LaurentPolynomial R)), ⊤)) = 1 := by
  change (Spec.map (CommRingCat.ofHom (laurentEvalOne R))).appTop
    ((Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv (LaurentPolynomial.T 1)) = 1
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
    CommRingCat.comp_apply]
  simp

end AlgebraicGeometry.Scheme.PolynomialLaurent
