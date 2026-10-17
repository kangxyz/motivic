/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtalePointOpenRefinement
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-! # Actual base-open refinement commutes with puncture base change -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Motivic.FiniteEtaleSite
variable {S T : Scheme.{u}} (j : T ⟶ S) (V : FiniteEtaleSite S)
  [IsNoetherian V.left] [IsNoetherian ((baseChange j).obj V).left] (O : V.left.Opens)

/-- The scheme comparison is the native pullback-restriction isomorphism after pullback pasting. -/
def baseOpenPunctureSchemeIso :
    ((baseChange j).obj (testOpenObject V O)).left ≅
      (pullback.fst V.hom j ⁻¹ᵁ O).toScheme :=
  (pullbackRightPullbackFstIso V.hom j O.ι).symm ≪≫
    pullbackSymmetry O.ι (pullback.fst V.hom j) ≪≫
      pullbackRestrictIsoRestrict (pullback.fst V.hom j) O

omit [AlgebraicGeometry.IsNoetherian ((baseChange j).obj V).left] in
/-- The comparison retains the literal map into the original punctured neighborhood. -/
@[reassoc]
theorem baseOpenPunctureSchemeIso_hom_inclusion :
    (baseOpenPunctureSchemeIso j V O).hom ≫ (pullback.fst V.hom j ⁻¹ᵁ O).ι =
      ((baseChange j).map (testOpenInclusion V O)).left := by
  simp only [baseOpenPunctureSchemeIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    pullbackRestrictIsoRestrict_hom_ι, pullbackSymmetry_hom_comp_fst]
  apply pullback.hom_ext
  · simp only [Category.assoc, pullbackRightPullbackFstIso_inv_snd_fst]
    simp only [baseChange, MorphismProperty.Over.pullback_map_left,
      testOpenInclusion, composeObjectProjection, pullback.lift_fst]
    rfl
  · simp only [Category.assoc, pullbackRightPullbackFstIso_inv_snd_snd]
    simp only [baseChange, MorphismProperty.Over.pullback_map_left, pullback.lift_snd]
    rfl

/-- Refine the original base neighborhood first, or restrict its actual puncture afterwards. -/
def baseOpenPunctureIso :
    (baseChange j).obj (testOpenObject V O) ≅
      testOpenObject ((baseChange j).obj V) (pullback.fst V.hom j ⁻¹ᵁ O) := by
  let e := baseOpenPunctureSchemeIso j V O
  refine MorphismProperty.Over.isoMk e ?_
  change e.hom ≫ ((pullback.fst V.hom j ⁻¹ᵁ O).ι ≫ pullback.snd V.hom j) = _
  rw [← Category.assoc, baseOpenPunctureSchemeIso_hom_inclusion]
  exact MorphismProperty.Over.w ((baseChange j).map (testOpenInclusion V O))

/-- The small-site comparison retains the actual inclusion arrow, not merely its objects. -/
@[reassoc]
theorem baseOpenPunctureIso_hom_inclusion :
    (baseOpenPunctureIso j V O).hom ≫
      testOpenInclusion ((baseChange j).obj V) (pullback.fst V.hom j ⁻¹ᵁ O) =
        (baseChange j).map (testOpenInclusion V O) := by
  apply MorphismProperty.Over.Hom.ext
  exact baseOpenPunctureSchemeIso_hom_inclusion j V O

end Motivic.FiniteEtaleSite
