/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Spec.PolynomialQuotient.PencilFibers
public import Motivic.Aglib.AlgebraicGeometry.Spec.PolynomialQuotient.PolynomialQuotientTargetBaseChange
/-! # Whole finite-flat polynomial families in the original relative cylinder -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent
open _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram
universe u
namespace AlgebraicGeometry.PolynomialOpenQuotient
variable {k R : Type u} [Field k] [CommRing R] (σ : k →+* R) (p : R[X][X])

theorem family_finite (hp : p.Monic) : IsFinite (familySource σ p) := by
  let : IsFinite (source p) := source_finite p hp
  dsimp [familySource]
  infer_instance

theorem family_flat (hp : p.Monic) : Flat (familySource σ p) := by
  let : Flat (source p) := source_flat p hp
  dsimp [familySource]
  infer_instance

/-- The actual family coordinate maps retain the same original coefficient map. -/
theorem family_base :
    familySource σ p ≫ relativeLineHom (Spec.map (CommRingCat.ofHom σ)) =
      target (C.comp σ) p ≫ polynomialProjection (.of k) := by
  rw [familySource, Category.assoc, ambientIso_base, target_base]

/-- The joint source-target family map is genuinely a closed immersion. -/
theorem family_joint_closed :
    IsClosedImmersion (pullback.lift (familySource σ p) (target (C.comp σ) p)
      (family_base σ p)) := by
  let b := Spec.map (CommRingCat.ofHom σ)
  let c := Spec.map (CommRingCat.ofHom (C.comp σ))
  have he : (ambientIso σ).inv ≫ c = relativeLineHom b := by
    rw [show c = (ambientIso σ).hom ≫ relativeLineHom b from (ambientIso_base σ).symm]
    simp
  let m := pullback.map (relativeLineHom b) (polynomialProjection (.of k))
    c (polynomialProjection (.of k)) (ambientIso σ).inv (𝟙 _) (𝟙 _)
    (by simpa using he.symm) (by simp)
  have : IsIso m := by dsimp [m]; infer_instance
  have hm : pullback.lift (familySource σ p) (target (C.comp σ) p) (family_base σ p) ≫ m =
      pullback.lift (source p) (target (C.comp σ) p) (target_base (C.comp σ) p).symm := by
    apply pullback.hom_ext
    · dsimp only [m, b, c, pullback.map]
      erw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
        pullback.lift_fst]
      simp [familySource]
    · dsimp only [m, b, c, pullback.map]
      erw [Category.assoc, pullback.lift_snd, Category.comp_id,
        pullback.lift_snd, pullback.lift_snd]
  have : IsClosedImmersion
      (pullback.lift (familySource σ p) (target (C.comp σ) p) (family_base σ p) ≫ m) := by
    rw [hm]
    exact joint_closed (C.comp σ) p
  exact IsClosedImmersion.of_comp _ m

end AlgebraicGeometry.PolynomialOpenQuotient
