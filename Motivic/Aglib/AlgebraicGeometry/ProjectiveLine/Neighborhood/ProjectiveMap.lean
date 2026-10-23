/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Graph.Geometry
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.RelativeCurve.ActualConstantCurveMap
/-! # The actual graph ambient over an affine neighborhood is a projective line -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R]
variable (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme]

/-- The neighborhood structural map expressed on the spectrum of its section ring. -/
abbrev neighborhoodAffineBase : Spec Γ(V.toScheme, ⊤) ⟶ Spec (.of R) :=
  V.toScheme.isoSpec.inv ≫ neighborhoodProjection R V

lemma neighborhoodProjectiveSquare :
    IsPullback
      (ProjectiveSpace.map (Scheme.ConstantCurve.coefficientMap (neighborhoodAffineBase R V))
        (ULift.{u} (Fin 2)))
      (ProjectiveSpace.toSpec Γ(V.toScheme, ⊤) (ULift.{u} (Fin 2)) ≫ V.toScheme.isoSpec.inv)
      (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) (neighborhoodProjection R V) := by
  exact (Scheme.ConstantCurve.coefficient_isPullback (neighborhoodAffineBase R V)
    (ULift.{u} (Fin 2))).of_iso (Iso.refl _) (Iso.refl _) V.toScheme.isoSpec.symm
      (Iso.refl _) (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
      (by simp only [Iso.symm_hom, Iso.refl_hom, Category.id_comp]; rfl)
      (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
      (by simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom, neighborhoodAffineBase])

/-- A genuine projective isomorphism, not an assumed embedding of a proper curve. -/
def neighborhoodProjectiveIso : neighborhoodGraphAmbient R V ≅
    ProjectiveSpace Γ(V.toScheme, ⊤) (ULift.{u} (Fin 2)) :=
  (IsPullback.of_hasPullback (neighborhoodProjection R V)
    (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))).flip.isoIsPullback _ _
      (neighborhoodProjectiveSquare R V)

@[reassoc (attr := simp)]
lemma neighborhoodProjectiveIso_map : (neighborhoodProjectiveIso R V).hom ≫
    ProjectiveSpace.map (Scheme.ConstantCurve.coefficientMap (neighborhoodAffineBase R V))
      (ULift.{u} (Fin 2)) = pullback.snd _ _ :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

@[reassoc]
lemma neighborhoodProjectiveIso_toSpec : (neighborhoodProjectiveIso R V).hom ≫
    ProjectiveSpace.toSpec Γ(V.toScheme, ⊤) (ULift.{u} (Fin 2)) =
      pullback.fst _ _ ≫ V.toScheme.isoSpec.hom := by
  rw [← cancel_mono V.toScheme.isoSpec.inv]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact (IsPullback.of_hasPullback (neighborhoodProjection R V)
    (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))).flip.isoIsPullback_hom_snd _ _
      (neighborhoodProjectiveSquare R V)
/-- The native relative Serre twist is the same original target twist. -/
def neighborhoodOriginalTwistIso (d : ℤ) :
    (Scheme.Modules.pullback (neighborhoodProjectiveIso R V).hom).obj
      (ProjectiveSpace.twistingSheaf Γ(V.toScheme, ⊤) (ULift.{u} (Fin 2)) d) ≅
    (Scheme.Modules.pullback (pullback.snd (neighborhoodProjection R V)
      (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))))).obj
      (ProjectiveSpace.twistingSheaf R (ULift.{u} (Fin 2)) d) :=
  (Scheme.Modules.pullback (neighborhoodProjectiveIso R V).hom).mapIso
      (ProjectiveSpace.twistingBaseChangeIso
        (Scheme.ConstantCurve.coefficientMap (neighborhoodAffineBase R V))
        (ULift.{u} (Fin 2)) d).symm ≪≫
    (Scheme.Modules.pullbackComp (neighborhoodProjectiveIso R V).hom
      (ProjectiveSpace.map (Scheme.ConstantCurve.coefficientMap (neighborhoodAffineBase R V))
        (ULift.{u} (Fin 2)))).app (ProjectiveSpace.twistingSheaf R _ d) ≪≫
    (Scheme.Modules.pullbackCongr (neighborhoodProjectiveIso_map R V)).app
      (ProjectiveSpace.twistingSheaf R _ d)

end AlgebraicGeometry.RelativeProjectiveLine
