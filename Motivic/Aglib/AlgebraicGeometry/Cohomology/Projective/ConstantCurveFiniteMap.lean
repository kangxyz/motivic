/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Cartesian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # The finite projective map of the actual constant curve

Base change of a finite map to projective space produces the relative finite map on
Spec R ×[Spec k] C, with both structural equations and its actual Cartesian square.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.ConstantCurve
variable {k R : Type u} [CommRing k] [CommRing R] (f : k →+* R) (ι : Type u)
  {C : Scheme.{u}} (q : C ⟶ ProjectiveSpace k ι)

/-- The relative projective map, constructed from the native Cartesian square. -/
def toProjectiveSpace :
    pullback (Spec.map (CommRingCat.ofHom f)) (q ≫ ProjectiveSpace.toSpec k ι) ⟶
      ProjectiveSpace R ι :=
  (ProjectiveSpace.isPullback_map f ι).lift
    (pullback.snd _ _ ≫ q) (pullback.fst _ _)
    (by rw [Category.assoc, ← pullback.condition])

@[reassoc (attr := simp)]
theorem toProjectiveSpace_map : toProjectiveSpace f ι q ≫ ProjectiveSpace.map f ι =
    pullback.snd _ _ ≫ q :=
  (ProjectiveSpace.isPullback_map f ι).lift_fst _ _ _

@[reassoc (attr := simp)]
theorem toProjectiveSpace_toSpec :
    toProjectiveSpace f ι q ≫ ProjectiveSpace.toSpec R ι = pullback.fst _ _ :=
  (ProjectiveSpace.isPullback_map f ι).lift_snd _ _ _

/-- The original finite map is pulled back, not replaced by a projective embedding. -/
theorem isPullback_toProjectiveSpace :
    IsPullback (pullback.snd _ _) (toProjectiveSpace f ι q) q
      (ProjectiveSpace.map f ι) :=
  (IsPullback.of_hasPullback (Spec.map (CommRingCat.ofHom f))
    (q ≫ ProjectiveSpace.toSpec k ι)).flip.of_bot'
      (ProjectiveSpace.isPullback_map f ι)

instance [IsFinite q] : IsFinite (toProjectiveSpace f ι q) :=
  MorphismProperty.of_isPullback (isPullback_toProjectiveSpace f ι q) inferInstance

end AlgebraicGeometry.Scheme.ConstantCurve
