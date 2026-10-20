module
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.RelativeCurve.ActualConstantCurveMap
/-! # A finite projective-coordinate map on the actual affine-source product -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.ConstantCurve
variable (R : Type u) [CommRing R] (ι : Type u)
  {Y C : Scheme.{u}} [IsAffine Y]
  (b : Y ⟶ Spec (.of R)) (f : C ⟶ ProjectiveSpace R ι)

/-- The coefficient map induced by the affine source structural map and its spectrum presentation.
-/
abbrev affineSourceCoefficientMap : R →+* Γ(Y, ⊤) := coefficientMap (Y.isoSpec.inv ≫ b)

lemma affineSourceProjectiveSquare :
    IsPullback (ProjectiveSpace.map (affineSourceCoefficientMap R b) ι)
      (ProjectiveSpace.toSpec Γ(Y, ⊤) ι ≫ Y.isoSpec.inv)
      (ProjectiveSpace.toSpec R ι) b :=
  (coefficient_isPullback (Y.isoSpec.inv ≫ b) ι).of_iso
    (Iso.refl _) (Iso.refl _) Y.isoSpec.symm (Iso.refl _)
    (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
    (by simp only [Iso.symm_hom, Iso.refl_hom, Category.id_comp])
    (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
    (by simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom])

/-- The finite map is built on the literal product, without replacing its affine source. -/
def affineSourceToProjectiveSpace :
    pullback b (f ≫ ProjectiveSpace.toSpec R ι) ⟶ ProjectiveSpace Γ(Y, ⊤) ι :=
  (affineSourceProjectiveSquare R ι b).lift (pullback.snd _ _ ≫ f) (pullback.fst _ _)
    (by rw [Category.assoc, ← pullback.condition])

@[reassoc (attr := simp)] lemma affineSourceToProjectiveSpace_map :
    affineSourceToProjectiveSpace R ι b f ≫
      ProjectiveSpace.map (affineSourceCoefficientMap R b) ι = pullback.snd _ _ ≫ f :=
  (affineSourceProjectiveSquare R ι b).lift_fst _ _ _

@[reassoc] lemma affineSourceToProjectiveSpace_toSpec :
    affineSourceToProjectiveSpace R ι b f ≫ ProjectiveSpace.toSpec Γ(Y, ⊤) ι =
      pullback.fst _ _ ≫ Y.isoSpec.hom := by
  rw [← cancel_mono Y.isoSpec.inv]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact (affineSourceProjectiveSquare R ι b).lift_snd _ _ _

lemma affineSourceToProjectiveSpace_isPullback :
    IsPullback (pullback.snd b (f ≫ ProjectiveSpace.toSpec R ι))
      (affineSourceToProjectiveSpace R ι b f) f
      (ProjectiveSpace.map (affineSourceCoefficientMap R b) ι) :=
  (IsPullback.of_hasPullback b (f ≫ ProjectiveSpace.toSpec R ι)).flip.of_bot'
    (affineSourceProjectiveSquare R ι b)

instance [IsFinite f] : IsFinite (affineSourceToProjectiveSpace R ι b f) :=
  MorphismProperty.of_isPullback (affineSourceToProjectiveSpace_isPullback R ι b f) inferInstance

/-- The relative Serre twist is literally the original target twist after canonical transport. -/
def affineSourceOriginalTwistIso (d : ℤ) :
    (Modules.pullback (affineSourceToProjectiveSpace R ι b f)).obj
      (ProjectiveSpace.twistingSheaf Γ(Y, ⊤) ι d) ≅
    (Modules.pullback (pullback.snd b (f ≫ ProjectiveSpace.toSpec R ι))).obj
      ((Modules.pullback f).obj (ProjectiveSpace.twistingSheaf R ι d)) :=
  (Modules.pullback (affineSourceToProjectiveSpace R ι b f)).mapIso
      (ProjectiveSpace.twistingBaseChangeIso (affineSourceCoefficientMap R b) ι d).symm ≪≫
    (Modules.pullbackComp (affineSourceToProjectiveSpace R ι b f)
      (ProjectiveSpace.map (affineSourceCoefficientMap R b) ι)).app
        (ProjectiveSpace.twistingSheaf R ι d) ≪≫
    (Modules.pullbackCongr (affineSourceToProjectiveSpace_map R ι b f)).app
      (ProjectiveSpace.twistingSheaf R ι d) ≪≫
    (Modules.pullbackComp (pullback.snd _ _) f).symm.app
      (ProjectiveSpace.twistingSheaf R ι d)
end AlgebraicGeometry.Scheme.ConstantCurve
