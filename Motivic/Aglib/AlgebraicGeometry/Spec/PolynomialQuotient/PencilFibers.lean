/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Spec.PolynomialQuotient.PolynomialQuotientCoordinates
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeEndpointSupportDiagram
/-! # Actual relative endpoint fibers of whole polynomial quotient families -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent
open _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram
universe u
namespace AlgebraicGeometry.PolynomialOpenQuotient
variable {k R : Type u} [Field k] [CommRing R] (σ : k →+* R)

/-- The affine polynomial parameter chart preserves the actual constant section. -/
@[reassoc] theorem ambientIso_endpoint (a : k) :
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (σ a))) ≫ (ambientIso σ).hom =
      endpoint (Spec.map (CommRingCat.ofHom σ)) a := by
  apply pullback.hom_ext
  · erw [Category.assoc, ambientIso_fst, endpoint_fst]
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp]
    convert Spec.map_id (.of R) using 1
    congr 1
    ext r
    exact eval_C
  · erw [Category.assoc, ambientIso_snd, endpoint_snd]
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext
    · intro r
      change ((C r).map σ).eval (σ a) = σ ((C r).eval a)
      simp
    · change (X.map σ).eval (σ a) = σ (X.eval a)
      simp

/-- The chart's structure map is the original coefficient inclusion into the parameter ring. -/
@[reassoc] theorem ambientIso_base :
    (ambientIso σ).hom ≫ relativeLineHom (Spec.map (CommRingCat.ofHom σ)) =
      Spec.map (CommRingCat.ofHom (C.comp σ)) := by
  change (ambientIso σ).hom ≫ (pullback.fst _ _ ≫ Spec.map (CommRingCat.ofHom σ)) = _
  rw [← Category.assoc, ambientIso_fst]
  rw [polynomialProjection, ← Spec.map_comp]
  rfl

/-- Finite-free quotient source in the literal relative affine-line cylinder. -/
def familySource (p : R[X][X]) : Spec (.of (AdjoinRoot p)) ⟶
    relativeLine (Spec.map (CommRingCat.ofHom σ)) := source p ≫ (ambientIso σ).hom

/-- The original coefficient square identifies the whole endpoint fiber. -/
theorem familyEndpoint_isPullback (p : R[X][X]) (a : k) :
    IsPullback (source (p.map (evalRingHom (σ a))))
      (coefficientMap (evalRingHom (σ a)) p)
      (endpoint (Spec.map (CommRingCat.ofHom σ)) a) (familySource σ p) := by
  apply (coefficient_isPullback (evalRingHom (σ a)) p).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (ambientIso σ)
  · simp
  · simp
  · simpa using (ambientIso_endpoint σ a)
  · simp [familySource]

end AlgebraicGeometry.PolynomialOpenQuotient
