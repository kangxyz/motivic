/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.PuncturedSquare
/-! # The original retained overlap maps to the unchanged restricted source

This is the inclusion required by the lambda and correction restriction actions.
The retained open is exactly the one used to choose the source sections.

Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.OriginalRetainedSourceRestriction`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`Pencils.NativeOriginalRestrictionActions`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Hom

variable {S X Y A C : Scheme.{u}} (q : X ⟶ S) (p : Y ⟶ X) (a : A ⟶ X)
  (π : C ⟶ S) (j : Y ⟶ C) (hj : j ≫ π = p ≫ q) (V : S.Opens)

/-- Restrict the original overlap projection, not a new affine neighborhood. -/
def originalRetainedSourceRestriction :
    (((pullback.fst p a ≫ j) ≫ π) ⁻¹ᵁ V).toScheme ⟶
      (boundaryBaseCoverOpen q p ⊤ V).toScheme :=
  IsOpenImmersion.lift (boundaryBaseCoverOpen q p ⊤ V).ι
    ((((pullback.fst p a ≫ j) ≫ π) ⁻¹ᵁ V).ι ≫ pullback.fst p a) (by
      rintro _ ⟨x, rfl⟩
      rw [Opens.range_ι]
      refine ⟨trivial, ?_⟩
      have hx := x.property
      change (((pullback.fst p a ≫ j) ≫ π) x.val) ∈ V at hx
      change ((pullback.fst p a ≫ p) ≫ q) (x.val : (pullback p a : Scheme)) ∈ V
      simpa only [Category.assoc, hj] using hx)

@[reassoc (attr := simp)]
theorem originalRetainedSourceRestriction_ι :
    originalRetainedSourceRestriction q p a π j hj V ≫
      (boundaryBaseCoverOpen q p ⊤ V).ι =
        (((pullback.fst p a ≫ j) ≫ π) ⁻¹ᵁ V).ι ≫ pullback.fst p a :=
  IsOpenImmersion.lift_fac _ _ _

/-- The map factors the literal final retained inclusion in the same compactification. -/
@[reassoc]
theorem originalRetainedSourceRestriction_inclusion :
    originalRetainedSourceRestriction q p a π j hj V ≫
      boundaryBaseCoverInclusion q p π j hj ⊤ V =
        boundaryBaseRetainedTarget π V (pullback.fst p a ≫ j) := by
  apply (cancel_mono (pullback.snd V.ι π)).mp
  simp only [Category.assoc, boundaryBaseCoverInclusion_snd,
    originalRetainedSourceRestriction_ι_assoc, boundaryBaseRetainedTarget,
    boundaryBaseWholeMap_snd]

/-- Postcomposing with any original restriction keeps its original overlap projection. -/
@[reassoc]
theorem originalRetainedSourceRestriction_original_map {Q : Scheme.{u}} (r : Y ⟶ Q) :
    originalRetainedSourceRestriction q p a π j hj V ≫
      ((boundaryBaseCoverOpen q p ⊤ V).ι ≫ r) =
        (((pullback.fst p a ≫ j) ≫ π) ⁻¹ᵁ V).ι ≫ (pullback.fst p a ≫ r) := by
  simpa only [Category.assoc] using congrArg (fun g => g ≫ r)
    (originalRetainedSourceRestriction_ι q p a π j hj V)

/-- The same retained overlap maps to the same restricted original puncture. -/
def originalRetainedPunctureRestriction :
    (((pullback.fst p a ≫ j) ≫ π) ⁻¹ᵁ V).toScheme ⟶
      (boundaryBaseCoverOpen q a ⊤ V).toScheme :=
  IsOpenImmersion.lift (boundaryBaseCoverOpen q a ⊤ V).ι
    ((((pullback.fst p a ≫ j) ≫ π) ⁻¹ᵁ V).ι ≫ pullback.snd p a) (by
      rintro _ ⟨x, rfl⟩
      rw [Opens.range_ι]
      refine ⟨trivial, ?_⟩
      have hx := x.property
      change (((pullback.fst p a ≫ j) ≫ π) x.val) ∈ V at hx
      have he : (pullback.fst p a ≫ j) ≫ π = (pullback.snd p a ≫ a) ≫ q := by
        rw [Category.assoc, hj, ← Category.assoc, pullback.condition]
      change ((pullback.snd p a ≫ a) ≫ q) (x.val : (pullback p a : Scheme)) ∈ V
      simpa only [he] using hx)

@[reassoc (attr := simp)]
theorem originalRetainedPunctureRestriction_ι :
    originalRetainedPunctureRestriction q p a π j hj V ≫
      (boundaryBaseCoverOpen q a ⊤ V).ι =
        (((pullback.fst p a ≫ j) ≫ π) ⁻¹ᵁ V).ι ≫ pullback.snd p a :=
  IsOpenImmersion.lift_fac _ _ _

/-- Both projections are restrictions of the original square, not an identification
of the retained overlap with the separate pullback used by the pencil dictionary. -/
@[reassoc]
theorem originalRetainedRestriction_square :
    originalRetainedSourceRestriction q p a π j hj V ≫ boundaryBaseCoverMap q p ⊤ V =
      originalRetainedPunctureRestriction q p a π j hj V ≫
        boundaryBaseCoverMap q a ⊤ V := by
  apply (cancel_mono (boundaryBaseSourceOpen q ⊤ V).ι).mp
  simp only [Category.assoc, boundaryBaseCoverMap, morphismRestrict_ι]
  rw [← Category.assoc, originalRetainedSourceRestriction_ι,
    ← Category.assoc, originalRetainedPunctureRestriction_ι]
  simp only [Category.assoc, pullback.condition]

end AlgebraicGeometry.Scheme.Hom
