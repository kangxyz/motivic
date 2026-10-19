/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.DiagonalBoundary
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.DualTensor.MixedBoundary
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Sections.Product.Naturality
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.Semilocal
/-! # The original diagonal ideal in the one-sided moving domain -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Moving
variable {C X S : Scheme.{u}} (j : X ⟶ C) [IsOpenImmersion j]
  (δ : S ⟶ C) [IsClosedImmersion δ] (γ : S ⟶ X)
  (hγ : γ ≫ j = δ) (hI : IsLocallyRankOne C (Scheme.Hom.idealModule δ))

include hγ in
omit [IsClosedImmersion δ] in
/-- Restricting the original closed graph through its actual open target is Cartesian. -/
theorem openGraph_isPullback : IsPullback (𝟙 S) γ δ j :=
  IsPullback.of_horiz_isIso_mono ⟨by simpa only [Category.id_comp] using hγ.symm⟩

/-- The actual graph ideal, including its original scheme structure. -/
def openGraphIdealIso : (Modules.pullback j).obj (Scheme.Hom.idealModule δ) ≅
    Scheme.Hom.idealModule γ := by
  have : IsClosedImmersion γ := MorphismProperty.of_isPullback
    (openGraph_isPullback j δ γ hγ) inferInstance
  have : (Scheme.Hom.idealModule δ).IsQuasicoherent := by
    have := finiteLocallyFree_of_isLocallyRankOne (Scheme.Hom.idealModule δ) hI
    infer_instance
  let e := Scheme.Hom.idealPullbackMap δ γ j (𝟙 S) (openGraph_isPullback j δ γ hγ).w
  have : IsIso e := Scheme.Hom.idealPullbackMap_isIso_of_flat_ambient _ _ _ _ _
    (openGraph_isPullback j δ γ hγ)
  exact asIso e

@[reassoc] theorem openGraphIdealIso_inclusion :
    (openGraphIdealIso j δ γ hγ hI).hom ≫ Scheme.Hom.idealInclusion γ =
      Hom.pullbackToUnit (Scheme.Hom.idealInclusion δ) j :=
  Scheme.Hom.idealPullbackMap_inclusion _ _ _ _ _

include j δ hγ hI in
theorem openGraph_locallyRankOne : IsLocallyRankOne X (Scheme.Hom.idealModule γ) :=
  isLocallyRankOne_of_iso _ (openGraphIdealIso j δ γ hγ hI)
    (pullbackLineBundle j ⟨Scheme.Hom.idealModule δ, hI⟩).property

/-- Native actual line comparison to the original compact numerator dual. -/
def openGraphPencilLineIso (T : LineBundle C) :
    tensorSheaf X (Scheme.Hom.idealModule γ)
      ((Modules.pullback j).obj (dualLineBundle C T).val) ≅
    (Modules.pullback j).obj (dualLineBundle C
      (tensorLineBundle C T (dualLineBundle C ⟨Scheme.Hom.idealModule δ, hI⟩))).val :=
  tensorSheafIso X (openGraphIdealIso j δ γ hγ hI).symm (Iso.refl _) ≪≫
    pulledDualTwistedIdealIso j ⟨Scheme.Hom.idealModule δ, hI⟩ T

/-- Endpoint zero is the literal retained graph times the original denominator. -/
theorem openGraphPencilLineIso_start (T : LineBundle C)
    (b : SheafOfModules.unit C.ringCatSheaf ⟶ T.val) :
    (openGraphPencilLineIso j δ γ hγ hI T).hom ≫
      Hom.pullbackToUnit (sectionDualFunctional C
        (tensorLineBundle C T (dualLineBundle C ⟨Scheme.Hom.idealModule δ, hI⟩))
        (twistedIdealSection C ⟨Scheme.Hom.idealModule δ, hI⟩ T
          (Scheme.Hom.idealInclusion δ) b)) j =
      Hom.productSection (Scheme.Hom.idealInclusion γ)
        (Hom.pullbackToUnit (sectionDualFunctional C T b) j) := by
  simp only [openGraphPencilLineIso, Iso.trans_hom, Category.assoc]
  rw [pulledDualTwistedIdealIso_section]
  change tensorSheafMap X (openGraphIdealIso j δ γ hγ hI).inv (𝟙 _) ≫ _ = _
  rw [Hom.productSection_naturality, Category.id_comp]
  rw [← openGraphIdealIso_inclusion j δ γ hγ hI, Iso.inv_hom_id_assoc]

end AlgebraicGeometry.Scheme.Moving
