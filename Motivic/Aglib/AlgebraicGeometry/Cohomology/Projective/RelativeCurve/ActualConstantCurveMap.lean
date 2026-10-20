/-
Copyright (c) 2026 Motivic Cohomology contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.Boundary.Twists.ConstantCurve

/-! The actual affine source structure map determines the coefficient map canonically. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace
universe u
namespace AlgebraicGeometry.Scheme.ConstantCurve
variable {k R : Type u} [CommRing k] [CommRing R]
  (b : Spec (.of R) ⟶ Spec (.of k)) (ι : Type u)
  {C : Scheme.{u}} (q : C ⟶ ProjectiveSpace k ι)

/-- The ring homomorphism corresponding to the affine structure map `b`. -/
def coefficientMap : k →+* R := (Spec.preimage b).hom

@[simp] theorem map_coefficientMap :
    Spec.map (CommRingCat.ofHom (coefficientMap b)) = b := Spec.map_preimage b

/-- The projective coefficient square over the unchanged original structure map. -/
theorem coefficient_isPullback :
    IsPullback (ProjectiveSpace.map (coefficientMap b) ι) (toSpec R ι) (toSpec k ι) b := by
  simpa only [map_coefficientMap] using ProjectiveSpace.isPullback_map (coefficientMap b) ι

/-- The actual original product, with no replacement of its source structure morphism. -/
def actualToProjectiveSpace : pullback b (q ≫ toSpec k ι) ⟶ ProjectiveSpace R ι :=
  (coefficient_isPullback b ι).lift (pullback.snd _ _ ≫ q) (pullback.fst _ _)
    (by rw [Category.assoc, ← pullback.condition])

@[reassoc (attr := simp)]
theorem actualToProjectiveSpace_map :
    actualToProjectiveSpace b ι q ≫ ProjectiveSpace.map (coefficientMap b) ι =
      pullback.snd _ _ ≫ q := (coefficient_isPullback b ι).lift_fst _ _ _

@[reassoc (attr := simp)]
theorem actualToProjectiveSpace_toSpec :
    actualToProjectiveSpace b ι q ≫ toSpec R ι = pullback.fst _ _ :=
  (coefficient_isPullback b ι).lift_snd _ _ _

theorem actualToProjectiveSpace_isPullback :
    IsPullback (pullback.snd _ _) (actualToProjectiveSpace b ι q) q
      (ProjectiveSpace.map (coefficientMap b) ι) :=
  (IsPullback.of_hasPullback b (q ≫ toSpec k ι)).flip.of_bot' (coefficient_isPullback b ι)

instance [IsFinite q] : IsFinite (actualToProjectiveSpace b ι q) :=
  MorphismProperty.of_isPullback (actualToProjectiveSpace_isPullback b ι q) inferInstance

/-- The common original target twist on the unchanged actual product. -/
def actualOriginalTwistIso (d : ℤ) :
    (Modules.pullback (actualToProjectiveSpace b ι q)).obj (twistingSheaf R ι d) ≅
      (Modules.pullback (pullback.snd b (q ≫ toSpec k ι))).obj
        ((Modules.pullback q).obj (twistingSheaf k ι d)) :=
  (Modules.pullback (actualToProjectiveSpace b ι q)).mapIso
      (twistingBaseChangeIso (coefficientMap b) ι d).symm ≪≫
    (Modules.pullbackComp (actualToProjectiveSpace b ι q)
      (ProjectiveSpace.map (coefficientMap b) ι)).app (twistingSheaf k ι d) ≪≫
    (Modules.pullbackCongr (actualToProjectiveSpace_map b ι q)).app (twistingSheaf k ι d) ≪≫
    (Modules.pullbackComp (pullback.snd _ _) q).symm.app (twistingSheaf k ι d)
end AlgebraicGeometry.Scheme.ConstantCurve
