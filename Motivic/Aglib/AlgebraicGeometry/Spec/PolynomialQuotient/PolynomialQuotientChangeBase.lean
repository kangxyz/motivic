/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Spec.PolynomialQuotient.PolynomialQuotientCoordinates
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
/-! # Polynomial spans retain their actual coefficients after forgetting the relative base -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace AlgebraicGeometry.PolynomialOpenQuotient
variable {R A : Type u} [CommRing R] [CommRing A]
    (σ : R →+* A) {B : Scheme.{u}} (b : Spec (.of R) ⟶ B)

/-- The unchanged polynomial ambient scheme maps into the product over the original base. -/
def ambientChangeBase : Spec (.of A[X]) ⟶
    pullback (Spec.map (CommRingCat.ofHom σ) ≫ b) (polynomialProjection (.of R) ≫ b) :=
  (ambientIso σ).hom ≫
    pullback.mapDesc (Spec.map (CommRingCat.ofHom σ)) (polynomialProjection (.of R)) b

instance ambientChangeBase_closed [IsSeparated b] : IsClosedImmersion (ambientChangeBase σ b) := by
  dsimp [ambientChangeBase]
  infer_instance

@[reassoc (attr := simp)] theorem ambientChangeBase_fst :
    ambientChangeBase σ b ≫ pullback.fst _ _ = polynomialProjection (.of A) := by
  simp [ambientChangeBase]

@[reassoc (attr := simp)] theorem ambientChangeBase_snd :
    ambientChangeBase σ b ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom σ)) := by
  simp [ambientChangeBase]

/-- The coefficient relation is preserved literally, not replaced by a chosen isomorphism. -/
theorem target_changeBase (p : A[X]) :
    source p ≫ (Spec.map (CommRingCat.ofHom σ) ≫ b) =
      target σ p ≫ (polynomialProjection (.of R) ≫ b) := by
  rw [← Category.assoc, ← Category.assoc, target_base]

/-- The entire polynomial quotient remains jointly closed over the smaller base. -/
theorem joint_changeBase_eq (p : A[X]) :
    pullback.lift (source p) (target σ p) (target_changeBase σ b p) =
      inclusion p ≫ ambientChangeBase σ b := by
  apply pullback.hom_ext <;> simp [target]

instance joint_changeBase_closed [IsSeparated b] (p : A[X]) :
    IsClosedImmersion
      (pullback.lift (source p) (target σ p) (target_changeBase σ b p)) := by
  rw [joint_changeBase_eq]
  infer_instance

end AlgebraicGeometry.PolynomialOpenQuotient
