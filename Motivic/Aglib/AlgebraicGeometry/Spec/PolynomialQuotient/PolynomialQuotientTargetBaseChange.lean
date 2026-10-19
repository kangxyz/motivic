/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Spec.PolynomialQuotient.PolynomialQuotientCoordinates
/-! # Literal target naturality of the whole polynomial quotient fiber -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
universe u
namespace AlgebraicGeometry.PolynomialOpenQuotient
variable {k R S : Type u} [CommRing k] [CommRing R] [CommRing S]
  (σ : k →+* R) (φ : R →+* S) (p : R[X])

/-- The native coefficient homomorphism preserves every literal polynomial residue. -/
theorem coefficient_mk (r : R[X]) :
    AdjoinRoot.map φ p (p.map φ) dvd_rfl (AdjoinRoot.mk p r) =
      AdjoinRoot.mk (p.map φ) (r.map φ) := by
  have h : (AdjoinRoot.map φ p (p.map φ) dvd_rfl).comp (AdjoinRoot.mk p) =
      (AdjoinRoot.mk (p.map φ)).comp (Polynomial.mapRingHom φ) := by
    apply Polynomial.ringHom_ext
    · intro a
      change AdjoinRoot.map φ p (p.map φ) dvd_rfl (AdjoinRoot.of p a) =
        AdjoinRoot.mk (p.map φ) ((C a).map φ)
      rw [Polynomial.map_C]
      exact AdjoinRoot.map_of φ p (p.map φ) dvd_rfl a
    · change AdjoinRoot.map φ p (p.map φ) dvd_rfl (AdjoinRoot.root p) =
        AdjoinRoot.mk (p.map φ) (X.map φ)
      rw [Polynomial.map_X]
      exact AdjoinRoot.map_root φ p (p.map φ) dvd_rfl
  exact RingHom.congr_fun h r

@[reassoc] theorem coefficient_target :
    coefficientMap φ p ≫ target σ p = target (φ.comp σ) (p.map φ) := by
  unfold coefficientMap target inclusion
  simp only [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  change AdjoinRoot.map φ p (p.map φ) dvd_rfl (AdjoinRoot.mk p (r.map σ)) =
    AdjoinRoot.mk (p.map φ) (r.map (φ.comp σ))
  rw [coefficient_mk, Polynomial.map_map]

/-- Boundary units specialize on the entire quotient, not merely its reduced support. -/
theorem coefficient_boundary_unit (f : k[X])
    (hf : IsUnit (AdjoinRoot.mk p (f.map σ))) :
    IsUnit (AdjoinRoot.mk (p.map φ) (f.map (φ.comp σ))) := by
  have h := hf.map (AdjoinRoot.map φ p (p.map φ) dvd_rfl)
  rwa [coefficient_mk, Polynomial.map_map] at h

@[reassoc] theorem coefficient_openTarget (f : k[X])
    (hf : IsUnit (AdjoinRoot.mk p (f.map σ))) :
    coefficientMap φ p ≫ openTarget σ p f hf =
      openTarget (φ.comp σ) (p.map φ) f (coefficient_boundary_unit σ φ p f hf) := by
  apply (cancel_mono (principalOpen f).ι).mp
  rw [Category.assoc, openTarget_inclusion, openTarget_inclusion, coefficient_target]

end AlgebraicGeometry.PolynomialOpenQuotient
