/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.AffineChart
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Associativity.Diagonal.IntermediateLists

/-!
# Whole finite-chart consumers for the actual intermediate-image map

The actual finite image-product map retains its whole source fiber. Its
original remaining-middle scalar action and list are compared with the exact
Spec coordinate map through canonical open-chart stalk isomorphisms.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.MotivicTest.FiniteAffineChart

open _root_.AlgebraicGeometry.Scheme.Hom.FiniteAffineChart

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i) [IsSeparated h]

/-- Every actual image-product point has a finite whole-affine coordinate
presentation and a bijection retaining all original source-fiber points. -/
theorem everyIntermediateImagePoint (y : F.leftIntermediateImageProduct G H) :
    ∃ (U : (F.leftIntermediateImageProduct G H).Opens) (hU : IsAffineOpen U)
      (p : Spec Γ(F.leftIntermediateImageProduct G H, U)),
      hU.fromSpec p = y ∧ ((F.leftIntermediateImageMap G H).app U).hom.Finite ∧
      Function.Bijective (fiberMap (F.leftIntermediateImageMap G H) hU p) := by
  obtain ⟨U, hU, p, hp⟩ := exists_targetChart y
  exact ⟨U, hU, p, hp, coordinateRingMap_finite _ hU, fiberMap_bijective _ hU p⟩

variable {U : (F.leftIntermediateImageProduct G H).Opens} (hU : IsAffineOpen U)
  (q : Spec Γ(F.leftIntermediateSupportProduct G H,
    (F.leftIntermediateImageMap G H) ⁻¹ᵁ U))

/-- The original middle stalk acts through the actual coordinate finite map,
with the canonical target-point transport fully included. -/
theorem actualRemainingScalarSquare :
    F.leftImageMiddleStalkMap G H (sourceChart (F.leftIntermediateImageMap G H) hU q) ≫
        (targetStalkIsoAtSource (F.leftIntermediateImageMap G H) hU q).hom ≫
        (coordinateMap (F.leftIntermediateImageMap G H)).stalkMap q =
      (F.leftSupportMiddlePair G H).stalkMap
          (sourceChart (F.leftIntermediateImageMap G H) hU q) ≫
        (sourceStalkIso (F.leftIntermediateImageMap G H) hU q).hom := by
  rw [← stalk_square_at_source, ← Category.assoc,
    F.leftImageMiddleStalkMap_comp G H]

/-- The original remaining list on the true support is exactly the coordinate
image of the common target list, at every whole-fiber source point. -/
theorem actualRemainingList
    (s : List ((pullback h h).presheaf.stalk (F.leftSupportMiddlePair G H
      (sourceChart (F.leftIntermediateImageMap G H) hU q)))) :
    ((s.map (F.leftImageMiddleStalkMap G H
        (sourceChart (F.leftIntermediateImageMap G H) hU q)).hom).map
        (targetStalkIsoAtSource (F.leftIntermediateImageMap G H) hU q).hom.hom).map
        ((coordinateMap (F.leftIntermediateImageMap G H)).stalkMap q).hom =
      (s.map ((F.leftSupportMiddlePair G H).stalkMap
        (sourceChart (F.leftIntermediateImageMap G H) hU q)).hom).map
        (sourceStalkIso (F.leftIntermediateImageMap G H) hU q).hom.hom := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro a _
  exact ConcreteCategory.congr_hom (actualRemainingScalarSquare F G H hU q) a

/-- The numerical finite-pushforward weights are the literal original scheme
residue degrees, even after choosing the whole affine chart. -/
theorem actualImageProductResidueDegree :
    (coordinateMap (F.leftIntermediateImageMap G H)).residueDegree q =
      (F.leftIntermediateImageMap G H).residueDegree
        (sourceChart (F.leftIntermediateImageMap G H) hU q) :=
  residueDegree_eq _ hU q

end Motivic.MotivicTest.FiniteAffineChart
