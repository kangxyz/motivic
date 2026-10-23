/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Nisnevich
public import Motivic.Aglib.CategoryTheory.Sites.Slice.SheafExtension

/-! The small site embeds in the smooth slice, where terminal objects are preserved. -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable {B : Scheme.{u}} (X : SmoothSite B)

/-- The actual structure morphism of each small object in the big smooth slice. -/
def toSmoothSlice : EtaleSeparatedFiniteType X.left ⥤ Over X where
  obj U := Over.mk (SmoothSite.homMk U.hom (by simp))
  map f := Over.homMk ((toSmoothSite X).map f) (by ext; exact MorphismProperty.Over.w f)
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

instance : PreservesLimitsOfShape WalkingCospan (toSmoothSlice X) := by
  have : PreservesLimitsOfShape WalkingCospan (toSmoothSlice X ⋙ Over.forget X) :=
    inferInstanceAs (PreservesLimitsOfShape WalkingCospan (toSmoothSite X))
  exact preservesLimitsOfShape_of_reflects_of_preserves (toSmoothSlice X) (Over.forget X)

/-- The identity étale object maps to a terminal object of the actual smooth slice. -/
def terminalImageIso :
    (toSmoothSlice X).obj
      (MorphismProperty.Over.mk ⊤ (𝟙 X.left) (etaleSeparatedFiniteType.id_mem X.left)) ≅
      Over.mk (𝟙 X) := by
  apply Over.isoMk
    { hom := SmoothSite.homMk (𝟙 _) (by simp)
      inv := SmoothSite.homMk (𝟙 _) (by simp)
      hom_inv_id := by ext; simp
      inv_hom_id := by ext; simp }

instance : PreservesLimit (Functor.empty.{0} (EtaleSeparatedFiniteType X.left)) (toSmoothSlice X) :=
    by
  apply preservesLimit_of_preserves_limit_cone
    (MorphismProperty.Over.mkIdTerminal etaleSeparatedFiniteType X.left)
  exact (isLimitMapConeEmptyConeEquiv (toSmoothSlice X) _).symm
    (IsTerminal.ofIso Over.mkIdTerminal (terminalImageIso X).symm)

instance : PreservesLimitsOfShape (Discrete PEmpty.{1}) (toSmoothSlice X) :=
  preservesLimitsOfShape_pempty_of_preservesTerminal _

instance : PreservesFiniteLimits (toSmoothSlice X) :=
  preservesFiniteLimits_of_preservesTerminal_and_pullbacks _

instance : RepresentablyFlat (toSmoothSlice X) := flat_of_preservesFiniteLimits _

instance : (toSmoothSlice X).IsContinuous (nisnevichTopology X.left)
    ((SmoothSite.nisnevichTopology B).over X) := by
  rw [SmoothSite.nisnevichTopology,
    over_toGrothendieck_eq_toGrothendieck_comap_forget]
  apply Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy (toSmoothSlice X)
    (nisnevichPrecoverage X.left) ((SmoothSite.nisnevichPrecoverage B).comap (Over.forget X))
  rw [SmoothSite.nisnevichPrecoverage, ← Precoverage.comap_comp,
    ← Precoverage.comap_comp]
  exact le_rfl

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
