module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.CommonBoundaryInclusions
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.MixedProductBoundaryPullback
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.TensorSectionPullback
/-! # The actual relative numerator product is a whole-boundary unit -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil
private lemma section_unit_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {M : Z.Modules} (a : SheafOfModules.unit Z.ringCatSheaf ⟶ M)
    [IsIso (pullbackSectionMap g a)] : IsIso (pullbackSectionMap (f ≫ g) a) := by
  rw [← pullbackSectionMap_comp f g a]
  have : IsIso (pullbackSectionMap f (pullbackSectionMap g a)) := by
    change IsIso ((pullbackUnitIso f).inv ≫
      (Scheme.Modules.pullback f).map (pullbackSectionMap g a))
    infer_instance
  infer_instance
variable {S X Y A B Z C D : Scheme.{u}}
  (q : X ⟶ S) (π : C ⟶ S) (j : Y ⟶ C) (p : Y ⟶ X)
  (hq : j ≫ π = p ≫ q) (a : A ⟶ X)
  (α : B ⟶ Y) (β : B ⟶ A) (h : α ≫ p = β ≫ a)
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (d : D ⟶ C)

/-- Actual unit boundary values of both generated sections imply a unit product functional. -/
theorem commonProduct_boundary_isIso
    (L : LineBundle (pullback (j ≫ π) π)) (M : LineBundle (pullback (a ≫ q) π))
    (u : SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf ⟶ L.val)
    (v : SheafOfModules.unit (pullback (a ≫ q) π).ringCatSheaf ⟶ M.val)
    [IsIso (pullbackSectionMap
      (coprod.desc (Hom.infinityProductMap π j d) (Hom.graphBoundaryRestriction π j s)) u)]
    [IsIso (pullbackSectionMap (psiBoundaryInclusion q π j p hq a z s hs d) v)] :
    IsIso (Hom.pullbackToUnit
      (mixedProductFunctional (commonToLambda π j α) (commonToPsi q π j p hq a α β h) L M u v)
      (commonBoundaryInclusion π j α s d)) := by
  have hA : IsIso (pullbackSectionMap
      (commonBoundaryInclusion π j α s d ≫ commonToLambda π j α) u) := by
    rw [← commonBoundaryToLambda_inclusion π j α s d]
    exact section_unit_comp _ _ u
  have hN : IsIso (pullbackSectionMap
      (commonBoundaryInclusion π j α s d ≫ commonToPsi q π j p hq a α β h) v) := by
    rw [← commonBoundaryToPsi_inclusion q π j p hq a α β h z s hs d]
    exact section_unit_comp _ _ v
  exact mixedProductFunctional_boundary_isIso (commonToLambda π j α)
    (commonToPsi q π j p hq a α β h) (commonBoundaryInclusion π j α s d) L M u v
end AlgebraicGeometry.Scheme.RelativeCurvePencil
