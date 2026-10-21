/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.RelativeCurve.ConstantCurveFiniteMap
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.Twisting.BaseChangeIsomorphism

/-! Both source legs use the same original target twist, not unrelated relative Picard classes. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace
universe u
namespace AlgebraicGeometry.Scheme.ConstantCurve
/-- The relative Serre twist is literally the pullback of the original target twist. -/
def originalTwistIso {k R : Type u} [CommRing k] [CommRing R]
    (f : k →+* R) (ι : Type u) {C : Scheme.{u}}
    (q : C ⟶ ProjectiveSpace k ι) (d : ℤ) :
    (Modules.pullback (toProjectiveSpace f ι q)).obj (twistingSheaf R ι d) ≅
      (Modules.pullback (pullback.snd (Spec.map (CommRingCat.ofHom f))
        (q ≫ toSpec k ι))).obj ((Modules.pullback q).obj (twistingSheaf k ι d)) :=
  (Modules.pullback (toProjectiveSpace f ι q)).mapIso (twistingBaseChangeIso f ι d).symm ≪≫
    (Modules.pullbackComp (toProjectiveSpace f ι q) (ProjectiveSpace.map f ι)).app
      (twistingSheaf k ι d) ≪≫
    (Modules.pullbackCongr (toProjectiveSpace_map f ι q)).app (twistingSheaf k ι d) ≪≫
    (Modules.pullbackComp (pullback.snd _ _) q).symm.app (twistingSheaf k ι d)
end AlgebraicGeometry.Scheme.ConstantCurve
