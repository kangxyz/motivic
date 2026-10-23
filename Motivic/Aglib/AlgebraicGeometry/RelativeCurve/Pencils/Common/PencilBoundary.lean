/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.SectionBoundary
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Boundary.MixedProductBoundaryPullback
/-! # The actual compact pencil has identical full-boundary values -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil
variable {S X Y A B Z C D : Scheme.{u}}
  (q : X ⟶ S) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (π : C ⟶ S) [IsSeparated π]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  (p : Y ⟶ X) [Flat p] (hq : j ≫ π = p ≫ q)
  (a : A ⟶ X) [Flat a] (α : B ⟶ Y) (β : B ⟶ A) (h : α ≫ p = β ≫ a)
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 _) p z)
  (e : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
    Hom.idealModule (Hom.boundaryGraphTarget q z))
  (ha : Disjoint (Set.range a) (Set.range z)) (d : D ⟶ C)
  (hd : Disjoint (Set.range j) (Set.range d))

/-- Equality follows from the actual two producer equations and original geometry. -/
theorem relativeCommonPencil_boundary
    (T : LineBundle (pullback (j ≫ π) π)) (N : LineBundle (pullback (a ≫ q) π))
    (aS : SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf ⟶
      (tensorLineBundle _ T (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j))).val)
    (bS : SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf ⟶ T.val)
    (nS dS : SheafOfModules.unit (pullback (a ≫ q) π).ringCatSheaf ⟶ N.val)
    (hA : let zA := coprod.desc (Hom.infinityProductMap π j d) (Hom.graphBoundaryRestriction π j s)
      pullbackSectionMap zA aS ≫ pullbackTensorMap zA T.val
        (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j)).val =
      tensorUnitSection (pullbackSectionMap zA bS)
        (Hom.relativeFullBoundaryFrame q π j p hq z s hs H e d hd).inv)
    (hN : pullbackSectionMap (psiBoundaryInclusion q π j p hq a z s hs d) nS =
      (fixedProductBoundaryFrame q π a z e ha d).hom ≫
        pullbackSectionMap (psiBoundaryInclusion q π j p hq a z s hs d) dS) :
    Hom.pullbackToUnit
      (mixedProductFunctional (commonToLambda π j α) (commonToPsi q π j p hq a α β h)
        (tensorLineBundle _ T (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j)))
        N aS nS) (commonBoundaryInclusion π j α s d) =
    Hom.pullbackToUnit
      (mixedProductFunctional (commonToLambda π j α) (commonToPsi q π j p hq a α β h)
        (tensorLineBundle _ T (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j)))
        N (twistedIdealSection _ (Hom.relativeCompactificationGraphLine π j) T
          (Hom.idealInclusion (Hom.compactificationGraph π j)) bS) dS)
      (commonBoundaryInclusion π j α s d) := by
  apply mixedProductFunctional_boundary
  rw [← commonBoundaryToLambda_inclusion π j α s d,
    ← commonBoundaryToPsi_inclusion q π j p hq a α β h z s hs d]
  exact relativeCommonBoundary_tensor q π j p hq a α β h z s hs H e ha d hd
    T N aS bS nS dS hA hN
end AlgebraicGeometry.Scheme.RelativeCurvePencil
