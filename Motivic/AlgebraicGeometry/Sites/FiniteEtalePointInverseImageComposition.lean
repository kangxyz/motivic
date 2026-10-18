/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleFieldPointInverseImage
public import Motivic.Cohomology.A1.BoundaryEtaleLocalization
public import Motivic.Aglib.AlgebraicGeometry.NisnevichDistinguishedSquare
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.Algebra.Category.Grp.AB

/-! # Actual point fibers of genuine inverse images

A field-valued marking that factors through a scheme map evaluates its genuine
inverse image at the same entire mark. The scheme map need not be étale; this
applies in particular to closed Cartier immersions.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Motivic.FiniteEtaleSite
variable {Z Y : Scheme.{u}} (i : Z ⟶ Y) (K : Type u) [Field K]
  (c : Spec (.of K) ⟶ Z)
  (G : Sheaf (nisnevichTopology Y) AddCommGrpCat.{u + 1})

/-- Composition of the actual inverse-image functors compares the original
ambient point fiber with the genuine inverse-image fiber at its full lift. -/
def fieldPointInverseImageCompositionIso :
    (relativeFieldPoint (c ≫ i) K (𝟙 _)).sheafFiber.obj G ≅
      (relativeFieldPoint c K (𝟙 _)).sheafFiber.obj ((inverseImage i).obj G) :=
  (relativeFieldPointInverseImageIso (c ≫ i) K (𝟙 _)).app G ≪≫
    (sheafToPresheaf (nisnevichTopology (Spec (.of K))) AddCommGrpCat.{u + 1} ⋙
      (evaluation (FiniteEtaleSite (Spec (.of K)))ᵒᵖ AddCommGrpCat.{u + 1}).obj
        (op (fieldObject K (𝟙 _)))).mapIso ((inverseImageCompIso c i).symm.app G) ≪≫
    ((relativeFieldPointInverseImageIso c K (𝟙 _)).app ((inverseImage i).obj G)).symm

/-- Zero of the genuine closed inverse image kills the ambient fiber at every
actual field-valued marking factoring through that closed map. -/
theorem fieldPoint_isZero_of_inverseImage (hG : IsZero ((inverseImage i).obj G)) :
    IsZero ((relativeFieldPoint (c ≫ i) K (𝟙 _)).sheafFiber.obj G) := by
  let : ((relativeFieldPoint c K (𝟙 _)).sheafFiber
      (A := AddCommGrpCat.{u + 1})).Additive :=
    Functor.additive_of_preserves_binary_products _
  exact ((relativeFieldPoint c K (𝟙 _)).sheafFiber.map_isZero hG).of_iso
    (fieldPointInverseImageCompositionIso i K c G)


/-- Membership of an arbitrary field-valued point in a closed image supplies an
actual lift with that same field, so no mark-replacement hypothesis is needed. -/
theorem fieldPoint_isZero_of_inverseImage_of_mem_range [SurjectiveOnStalks i]
    (b : Spec (.of K) ⟶ Y) (p : Spec (.of K)) (hb : b p ∈ Set.range i)
    (hG : IsZero ((inverseImage i).obj G)) :
    IsZero ((relativeFieldPoint b K (𝟙 _)).sheafFiber.obj G) := by
  have hp : (IsLocalRing.closedPoint K : PrimeSpectrum K) = p := Subsingleton.elim _ _
  obtain ⟨c, hc⟩ := Scheme.exists_field_lift_of_mem_range i b (by simpa only [hp] using hb)
  simpa only [hc] using fieldPoint_isZero_of_inverseImage i K c G hG

end Motivic.FiniteEtaleSite
