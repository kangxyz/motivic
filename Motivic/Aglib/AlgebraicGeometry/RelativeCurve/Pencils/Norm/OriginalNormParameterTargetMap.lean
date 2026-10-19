/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.OriginalRetainedNormMaps
/-! # The original target map after an actual component parameter change

This is an equality of scheme maps, preserving the original target line and sections.
No norm along the parameter map, and no definitional equality of the two maps, is assumed.

Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.OriginalNormParameterTargetMap`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`Pencils.NativeSectionPairActionConversion`, `Pencils.NativeSectionPairLambdaAction`.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.Hom

variable {S C P Y X K : Scheme.{u}} (π : P ⟶ S) (f : C ⟶ P)
  (jB : Y ⟶ C) (jA : X ⟶ P) (p : Y ⟶ X) (hret : jB ≫ f = p ≫ jA)
  (α : K ⟶ Y) (b : K ⟶ S) (hb : b = α ≫ (jB ≫ f ≫ π))

/-- The actual composite target parameter has the same original base map. -/
theorem originalNormParameter_target_base_eq (hret : jB ≫ f = p ≫ jA)
    (hb : b = α ≫ (jB ≫ f ≫ π)) : b = (α ≫ p) ≫ (jA ≫ π) := by
  rw [hb]
  simpa only [Category.assoc] using congrArg (fun m => α ≫ m ≫ π) hret

/-- The target leg produced by component normalization is the direct action leg. -/
theorem originalNormParameter_target_comp
    (hA : b = (α ≫ p) ≫ (jA ≫ π)) :
    constantSourceMapOfEq α (jB ≫ f ≫ π) π b hb ≫
        retainedParameterProductMap π f jB jA p hret =
      retainedNormParameterMap π b jA (α ≫ p) hA := by
  apply pullback.hom_ext <;>
    simp [retainedNormParameterMap, retainedParameterProductMap,
      retainedParameterProductIso, Category.assoc]

end AlgebraicGeometry.Scheme.Hom
