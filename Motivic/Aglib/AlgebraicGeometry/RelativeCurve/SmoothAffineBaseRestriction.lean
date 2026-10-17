/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.NormalRetainedBaseRestriction
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # The original smooth base after its actual affine principal restriction -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurve
variable (k R : Type u) [Field k] [CommRing R] [Algebra k R]
  [Algebra.Smooth k R] (T : (Spec (.of R)).Opens) [IsAffine T.toScheme]

/-- The coefficient map is induced by the original base structure, with no new choice. -/
abbrev restrictedBaseCoefficientMap : k →+* Γ(T.toScheme, ⊤) :=
  ConstantCurve.coefficientMap (T.toScheme.isoSpec.inv ≫ T.ι ≫
    Spec.map (CommRingCat.ofHom (algebraMap k R)))

/-- The coordinate ring of the same base neighborhood is Noetherian and smooth
for the actual coefficient map inherited from the original field. -/
theorem restrictedBaseCoefficientMap_properties :
    IsNoetherianRing Γ(T.toScheme, ⊤) ∧ (restrictedBaseCoefficientMap k R T).Smooth := by
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  have : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k R))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr inferInstance)
  refine ⟨IsLocallyNoetherian.component_noetherian
    ⟨⊤, isAffineOpen_top T.toScheme⟩, ?_⟩
  apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mp
  change Smooth (Spec.map (CommRingCat.ofHom (ConstantCurve.coefficientMap
    (T.toScheme.isoSpec.inv ≫ T.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))))))
  rw [ConstantCurve.map_coefficientMap]
  infer_instance

end AlgebraicGeometry.Scheme.RelativeCurve
