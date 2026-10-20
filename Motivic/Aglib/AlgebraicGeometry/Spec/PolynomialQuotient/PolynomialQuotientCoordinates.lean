/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Spec.PolynomialQuotient.PolynomialOpenQuotient
public import Motivic.Aglib.AlgebraicGeometry.BaseChange.Affine.AdjoinRootBaseChange
public import Mathlib.RingTheory.Polynomial.Quotient
public import Aglib.Algebra.Polynomial.Laurent.BaseChange
/-! # Literal source, target and whole-fiber coordinates of polynomial quotients -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace AlgebraicGeometry.PolynomialOpenQuotient
variable {k R : Type u} [CommRing k] [CommRing R] (σ : k →+* R)

/-- The polynomial ambient scheme is the original affine-line product. -/
theorem ambient_isPullback :
    IsPullback (polynomialProjection (.of R))
      (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom σ)))
      (Spec.map (CommRingCat.ofHom σ)) (polynomialProjection (.of k)) :=
  isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.PolynomialLaurent.polynomial_isPushout (CommRingCat.ofHom σ))

/-- The canonical isomorphism `Spec R[X] ≅ Spec R ×[Spec k] Spec k[X]` induced by `σ`. -/
def ambientIso : Spec (.of R[X]) ≅
    pullback (Spec.map (CommRingCat.ofHom σ)) (polynomialProjection (.of k)) :=
  (ambient_isPullback σ).isoPullback

@[reassoc (attr := simp)] theorem ambientIso_fst :
    (ambientIso σ).hom ≫ pullback.fst _ _ = polynomialProjection (.of R) :=
  (ambient_isPullback σ).isoPullback_hom_fst

@[reassoc (attr := simp)] theorem ambientIso_snd :
    (ambientIso σ).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom σ)) :=
  (ambient_isPullback σ).isoPullback_hom_snd

/-- Both actual quotient coordinates form a closed immersion jointly. -/
theorem joint_eq (p : R[X]) :
    pullback.lift (source p) (target σ p) (target_base σ p).symm =
      inclusion p ≫ (ambientIso σ).hom := by
  apply pullback.hom_ext
  · simp
  · simp [target]

instance joint_closed (p : R[X]) :
    IsClosedImmersion (pullback.lift (source p) (target σ p) (target_base σ p).symm) := by
  rw [joint_eq]
  infer_instance

/-- The exact linear quotient structural map is an isomorphism. -/
instance source_linear_isIso (a : R) : IsIso (source (X - C a)) := by
  have he : CommRingCat.ofHom (AdjoinRoot.of (X - C a)) =
      (quotientSpanXSubCAlgEquiv a).toRingEquiv.toCommRingCatIso.inv := by
    ext r
    exact (quotientSpanXSubCAlgEquiv_symm_apply a r).symm
  unfold source
  rw [he]
  infer_instance

/-- The quotient's target is the original coordinate graph. -/
theorem target_linear (a : R) :
    target σ (X - C a) = source (X - C a) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom σ a)) := by
  unfold target inclusion source
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro r
    change AdjoinRoot.mk (X - C a) ((C r).map σ) =
      AdjoinRoot.of (X - C a) ((C r).eval₂ σ a)
    simp only [Polynomial.map_C, eval₂_C]
    rfl
  · change AdjoinRoot.mk (X - C a) (X.map σ) =
      AdjoinRoot.of (X - C a) (X.eval₂ σ a)
    rw [Polynomial.map_X, eval₂_X]
    have h := AdjoinRoot.eval₂_root (X - C a)
    simpa only [eval₂_sub, eval₂_X, eval₂_C, sub_eq_zero, AdjoinRoot.root] using h

variable {S : Type u} [CommRing S] (φ : R →+* S) (p : R[X])

/-- Literal whole quotient base change, including nonreduced fibers. -/
def coefficientMap : Spec (.of (AdjoinRoot (p.map φ))) ⟶ Spec (.of (AdjoinRoot p)) :=
  Spec.map (CommRingCat.ofHom (AdjoinRoot.map φ p (p.map φ) dvd_rfl))

theorem coefficient_isPullback :
    IsPullback (source (p.map φ)) (coefficientMap φ p)
      (Spec.map (CommRingCat.ofHom φ)) (source p) :=
  AdjoinRootBaseChange.isPullback φ p

end AlgebraicGeometry.PolynomialOpenQuotient
