/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Presentations.ScalarPolynomial
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # The entire scalar base-point fiber and the whole zero morphism

A scalar point on the base is chosen by actual base-change surjectivity. The
whole-zero naturality equation and the ambient closed-point fiber uniqueness
then identify its zero image. These two facts are not conflated.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates

open _root_.AlgebraicGeometry.PolynomialOpenQuotient.Laurent
open _root_.AlgebraicGeometry.Scheme.PolynomialLaurent
open _root_.AlgebraicGeometry.Scheme.SmoothSite
open _root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite

variable (k R L : Type u) [Field k] [CommRing R] [Field L]
  [Algebra k R] [Algebra k L] [Algebra.Smooth k R]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local instance : Algebra.Smooth L (R ⊗[k] L) :=
  Algebra.Smooth.of_equiv (Algebra.TensorProduct.commRight k L R)

local instance : Algebra.Smooth k (Polynomial R) := by
  let : Algebra.Smooth R (Polynomial R) := {}
  exact Algebra.Smooth.comp k R (Polynomial R)

local instance : Algebra.Smooth L ((Polynomial R) ⊗[k] L) :=
  Algebra.Smooth.of_equiv (Algebra.TensorProduct.commRight k L (Polynomial R))

/-- The scalar whole zero morphism retains its literal original projection. -/
@[reassoc]
theorem tensorPolynomialLineIso_zero_original :
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R ⊗[k] L))) ≫
      (tensorPolynomialLineIso k R L).inv.left ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap (Polynomial R) ((Polynomial R) ⊗[k] L))) =
    Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[k] L))) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) := by
  let F := fieldBaseChange (algebraMap k L)
  let c := affineScalarIso k R L
  let i := (forgetScheme (Spec (.of L))).mapIso (tensorPolynomialLineIso k R L)
  let z₀ : affineSite k R ⟶ lineSite (k := k) (R := R) :=
    a1Section (.of k) (affineSite k R) 0 ≫ lineCylinderIso.inv
  let q := (F.map (z₀ ≫ (polynomialAffineIso k R).hom)).left ≫
    (affineScalarIso k (Polynomial R) L).hom.left
  have hz : c.inv.left ≫ q ≫ i.hom =
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R ⊗[k] L))) := by
    have hs : c.inv ≫ F.map (z₀ ≫ (polynomialAffineIso k R).hom) ≫
        (affineScalarIso k (Polynomial R) L).hom ≫
          (tensorPolynomialLineIso k R L).hom =
        a1Section (.of L) (affineSite L (R ⊗[k] L)) 0 ≫
          (lineCylinderIso (k := L) (R := R ⊗[k] L)).inv := by
      rw [tensorPolynomialLineIso_map]
      have h := scalarLineIso_zero k R L
      change F.map z₀ ≫ (scalarLineIso k R L).hom = c.hom ≫ _ at h
      rw [h, Iso.inv_hom_id_assoc]
    have h := congrArg (fun f => f.left) hs
    rw [polynomial_zero_left] at h
    change c.inv.left ≫ ((F.map (z₀ ≫ (polynomialAffineIso k R).hom)).left ≫
      (affineScalarIso k (Polynomial R) L).hom.left) ≫
        (tensorPolynomialLineIso k R L).hom.left = _
    simpa only [MorphismProperty.Comma.comp_left, Category.assoc] using h
  have hq : q ≫ Spec.map (CommRingCat.ofHom
      (algebraMap (Polynomial R) ((Polynomial R) ⊗[k] L))) =
      pullback.fst (baseMap k R) (Spec.map (CommRingCat.ofHom (algebraMap k L))) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) := by
    have hleft : (z₀ ≫ (polynomialAffineIso k R).hom).left =
        Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) := by
      rw [MorphismProperty.Comma.comp_left]
      change z₀.left ≫ 𝟙 _ = _
      rw [Category.comp_id]
      exact polynomial_zero_left k R
    have h := (scalarPolynomialSourceSquare k R L z₀).w.symm
    rw [hleft] at h
    exact h
  change _ ≫ i.inv ≫ _ = _
  rw [← hz]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [hq, ← Category.assoc, affineScalarIso_inv_original]

/-- The original coefficient projection of an actual scalar affine scheme is
surjective, without an integrality or rational-point premise. -/
theorem scalarCoefficient_surjective :
    Function.Surjective (Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[k] L)))) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap k L))
  have : Surjective f := ⟨Function.surjective_to_subsingleton _⟩
  have h : Surjective ((affineScalarIso k R L).inv.left ≫
      pullback.fst (baseMap k R) f) := inferInstance
  rw [affineScalarIso_inv_original] at h
  exact Scheme.Hom.surjective _

/-- A singleton fiber remains a singleton on a closed section compatible with
an actual ambient isomorphism and a surjective base projection. -/
theorem unique_point_over_closed_section
    {B B' T T' S : Scheme.{u}} (i : T ≅ T')
    (z₀ : B ⟶ S) (z : B' ⟶ T') [IsClosedImmersion z]
    (ρ : T ⟶ S) (π : B' ⟶ B) [Surjective π]
    (hz : z ≫ i.inv ≫ ρ = π ≫ z₀) (w : B) (y : T)
    (hu : ∀ t : T, ρ t = z₀ w → t = y) :
    ∃ v : B', π v = w ∧ (∀ v' : B', π v' = w → v' = v) ∧ i.hom y = z v := by
  obtain ⟨v, hv⟩ := π.surjective w
  have hzero (v' : B') (hv' : π v' = w) : i.inv (z v') = y := by
    apply hu
    have h := congrArg (fun f => f v') hz
    simpa only [Scheme.Hom.comp_apply, hv'] using h
  refine ⟨v, hv, ?_, ?_⟩
  · intro v' hv'
    apply z.isClosedEmbedding.injective
    apply i.inv.homeomorph.injective
    exact (hzero v' hv').trans (hzero v hv).symm
  · rw [← hzero v hv]
    exact congrArg (fun f => f (z v)) i.inv_hom_id

/-- Ambient closed-fiber uniqueness gives a unique point of the entire original
base-point fiber, and its literal whole-zero image is the selected ambient point. -/
theorem exists_unique_scalar_zero_point (w : Spec (.of R))
    (y : Spec (.of ((Polynomial R) ⊗[k] L)))
    (hu : ∀ t : Spec (.of ((Polynomial R) ⊗[k] L)),
      Spec.map (CommRingCat.ofHom
        (algebraMap (Polynomial R) ((Polynomial R) ⊗[k] L))) t =
        Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) w → t = y) :
    ∃ wL : Spec (.of (R ⊗[k] L)),
      Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[k] L))) wL = w ∧
      (∀ v : Spec (.of (R ⊗[k] L)),
        Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[k] L))) v = w → v = wL) ∧
      (tensorPolynomialLineIso k R L).hom.left y =
        Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R ⊗[k] L))) wL := by
  let i := (forgetScheme (Spec (.of L))).mapIso (tensorPolynomialLineIso k R L)
  let z := Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R ⊗[k] L)))
  have : IsClosedImmersion z := IsClosedImmersion.spec_of_surjective _
    (fun a => ⟨Polynomial.C a, Polynomial.eval_C⟩)
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[k] L)))) :=
    ⟨scalarCoefficient_surjective k R L⟩
  exact unique_point_over_closed_section i
    (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) z
    (Spec.map (CommRingCat.ofHom
      (algebraMap (Polynomial R) ((Polynomial R) ⊗[k] L))))
    (Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[k] L))))
    (tensorPolynomialLineIso_zero_original k R L) w y hu

end AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
