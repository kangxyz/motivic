/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.AffineSourceProjectiveMap

/-! # The unchanged compact curve after the actual affine base restriction -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurve
variable (R : Type u) [CommRing R] (ι : Type u) {N : Scheme.{u}}
  (π : N ⟶ ProjectiveSpace R ι) (T : (Spec (.of R)).Opens) [IsAffine T.toScheme]

/-- The native finite projective map on the actual open restriction, not a newly
chosen compactification or projection. -/
def finiteProjectiveBaseRestriction :
    ((π ≫ ProjectiveSpace.toSpec R ι) ⁻¹ᵁ T).toScheme ⟶
      ProjectiveSpace Γ(T.toScheme, ⊤) ι :=
  (isPullback_morphismRestrict (π ≫ ProjectiveSpace.toSpec R ι) T).isoPullback.hom ≫
    ConstantCurve.affineSourceToProjectiveSpace R ι T.ι π

instance [IsFinite π] : IsFinite (finiteProjectiveBaseRestriction R ι π T) := by
  unfold finiteProjectiveBaseRestriction
  infer_instance

/-- The base map is exactly the original restricted projection followed by its
canonical affine-spectrum identification. -/
@[reassoc]
theorem finiteProjectiveBaseRestriction_toSpec :
    finiteProjectiveBaseRestriction R ι π T ≫
      ProjectiveSpace.toSpec Γ(T.toScheme, ⊤) ι =
        ((π ≫ ProjectiveSpace.toSpec R ι) ∣_ T) ≫ T.toScheme.isoSpec.hom := by
  rw [finiteProjectiveBaseRestriction, Category.assoc,
    ConstantCurve.affineSourceToProjectiveSpace_toSpec, ← Category.assoc,
    IsPullback.isoPullback_hom_fst]

/-- The original compact projective map is retained by the same base change. -/
@[reassoc]
theorem finiteProjectiveBaseRestriction_map :
    finiteProjectiveBaseRestriction R ι π T ≫
      ProjectiveSpace.map (ConstantCurve.affineSourceCoefficientMap R T.ι) ι =
        ((π ≫ ProjectiveSpace.toSpec R ι) ⁻¹ᵁ T).ι ≫ π := by
  rw [finiteProjectiveBaseRestriction, Category.assoc,
    ConstantCurve.affineSourceToProjectiveSpace_map, ← Category.assoc,
    IsPullback.isoPullback_hom_snd]

end AlgebraicGeometry.Scheme.RelativeCurve
