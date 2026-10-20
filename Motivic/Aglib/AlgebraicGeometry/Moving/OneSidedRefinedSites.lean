/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Moving.OneSidedBaseRefinement
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Noetherian
/-! # Original smooth-site maps on the actual one-sided base refinement -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Hom
universe u
namespace AlgebraicGeometry.Scheme.Moving
variable {k : Type u} [Field k] {B : Scheme.{u}} [IsAffine B]
  (X : SmoothSite (Spec (.of k))) [IsAffine X.left]
  (q : X.left ⟶ B) (U : X.left.Opens) (W : B.Opens) [IsAffine W.toScheme]
  [IsAffine (boundaryBaseSourceOpen q U W).toScheme]

/-- The smooth-site object of the parameter open restricted to the base open. -/
abbrev refinedSourceSite : SmoothSite (Spec (.of k)) :=
  SmoothSite.mk ((boundaryBaseSourceOpen q U W).ι ≫ X.hom)

/-- The smooth-site object of the original target restricted to the base open. -/
abbrev refinedTargetSite : SmoothSite (Spec (.of k)) :=
  SmoothSite.mk ((q ⁻¹ᵁ W).ι ≫ X.hom)

/-- The inclusion of the refined parameter into its original smooth-site object. -/
def refinedSourceToOriginal : refinedSourceSite X q U W ⟶ X :=
  SmoothSite.homMk (boundaryBaseSourceOpen q U W).ι rfl

/-- The inclusion of the base-restricted target into the original target. -/
def refinedTargetToOriginal : refinedTargetSite X q W ⟶ X :=
  SmoothSite.homMk (q ⁻¹ᵁ W).ι rfl

/-- The refined parameter inclusion into the base-restricted target. -/
def refinedSourceToTarget : refinedSourceSite X q U W ⟶ refinedTargetSite X q W :=
  SmoothSite.homMk (X.left.homOfLE (show boundaryBaseSourceOpen q U W ≤ q ⁻¹ᵁ W
    from inf_le_right)) (by simp)

omit [IsAffine B] [IsAffine W.toScheme] in
@[reassoc (attr := simp)] theorem refinedSourceToTarget_original :
    refinedSourceToTarget X q U W ≫ refinedTargetToOriginal X q W =
      refinedSourceToOriginal X q U W := by
  apply MorphismProperty.Over.Hom.ext
  simp [refinedSourceToTarget, refinedTargetToOriginal, refinedSourceToOriginal]

variable {A : SmoothSite (Spec (.of k))} [IsAffine A.left]
  (a : A ⟶ X) [IsOpenImmersion a.left]

/-- The smooth-site object of the good open restricted to the base open. -/
abbrev refinedGoodSite : SmoothSite (Spec (.of k)) :=
  SmoothSite.mk (((a.left ≫ q) ⁻¹ᵁ W).ι ≫ A.hom)

/-- The inclusion of the base-restricted good open into the original good open. -/
def refinedGoodToOriginal : refinedGoodSite X q W a ⟶ A :=
  SmoothSite.homMk ((a.left ≫ q) ⁻¹ᵁ W).ι rfl

/-- The good-open map restricted to the base-restricted target. -/
def refinedGoodToTarget : refinedGoodSite X q W a ⟶ refinedTargetSite X q W :=
  SmoothSite.homMk (a.left ∣_ (q ⁻¹ᵁ W)) (by
    change (a.left ∣_ (q ⁻¹ᵁ W)) ≫ (q ⁻¹ᵁ W).ι ≫ X.hom =
      ((a.left ≫ q) ⁻¹ᵁ W).ι ≫ A.hom
    rw [morphismRestrict_ι_assoc]
    have hw : a.left ≫ X.hom = A.hom := a.w
    exact congrArg (fun f => ((a.left ≫ q) ⁻¹ᵁ W).ι ≫ f) hw)

instance : IsOpenImmersion (refinedGoodToTarget X q W a).left := by
  dsimp [refinedGoodToTarget, SmoothSite.homMk]
  infer_instance

omit [IsAffine X.left] [IsOpenImmersion a.left] in
@[reassoc (attr := simp)] theorem refinedGoodToTarget_original :
    refinedGoodToTarget X q W a ≫ refinedTargetToOriginal X q W =
      refinedGoodToOriginal X q W a ≫ a := by
  apply MorphismProperty.Over.Hom.ext
  exact morphismRestrict_ι _ _

end AlgebraicGeometry.Scheme.Moving
