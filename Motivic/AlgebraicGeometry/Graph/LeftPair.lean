/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Graph.Pair
public import Motivic.AlgebraicGeometry.Graph.PointTransport
public import Motivic.AlgebraicGeometry.Correspondences.LeftGraphIntersectionDiagram

/-!
# The same diagonal equation list through the transposed graph pair

The actual symmetry of the target self-product fixes its diagonal. Its actual
stalk ring isomorphism therefore transports a common regular diagonal list
and regularity of its graph images simultaneously. The new literal image
list uses the transposed graph pair, as required for incidence on the left.
No symmetry theorem for Tor is assumed.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingTheory.Sequence

universe u

namespace Motivic.Graph

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- The actual self-product symmetry fixes every actual diagonal point. -/
@[simp]
theorem symmetry_diagonal_apply (y : Y) :
    (pullbackSymmetry g g).hom (pullback.diagonal g y) = pullback.diagonal g y :=
  congrArg (fun m : Y ⟶ pullback g g => m y) (diagonal_symmetry g)

/-- The literal diagonal-to-transposed-graph scalar map at an actual graph point. -/
def leftDiagonalStalkMap (x : X) :
    (pullback g g).presheaf.stalk (pullback.diagonal g (f x)) ⟶
      (pullback (f ≫ g) g).presheaf.stalk (correspondenceGraph f g x) :=
  alignedStalkMap (leftGraphMiddlePair f g) (correspondenceGraph f g x)
    (pullback.diagonal g (f x)) (by
      change (f ≫ pullback.diagonal g) x =
        (correspondenceGraph f g ≫ leftGraphMiddlePair f g) x
      rw [correspondenceGraph_leftMiddlePair])

set_option backward.isDefEq.respectTransparency false in
/-- Actual diagonal symmetry transports a common list to the transposed graph pair. -/
theorem exists_common_regular_left_list_of_common (x : X)
    (h : ∃ rs : List ((pullback g g).presheaf.stalk (pullback.diagonal g (f x))),
      IsRegular ((pullback g g).presheaf.stalk (pullback.diagonal g (f x))) rs ∧
      RingHom.ker ((pullback.diagonal g).stalkMap (f x)).hom = Ideal.ofList rs ∧
      IsRegular ((pullback (f ≫ g) g).presheaf.stalk (correspondenceGraph f g x))
        (rs.map (diagonalStalkMap f g x).hom)) :
    ∃ rs : List ((pullback g g).presheaf.stalk (pullback.diagonal g (f x))),
      IsRegular ((pullback g g).presheaf.stalk (pullback.diagonal g (f x))) rs ∧
      RingHom.ker ((pullback.diagonal g).stalkMap (f x)).hom = Ideal.ofList rs ∧
      IsRegular ((pullback (f ≫ g) g).presheaf.stalk (correspondenceGraph f g x))
        (rs.map (leftDiagonalStalkMap f g x).hom) := by
  have hp : pullback.diagonal g (f x) =
      graphMiddlePair f g (correspondenceGraph f g x) :=
    (congrArg (fun m : X ⟶ pullback g g => m x)
      (correspondenceGraph_middlePair f g)).symm
  have hl : pullback.diagonal g (f x) =
      leftGraphMiddlePair f g (correspondenceGraph f g x) :=
    (congrArg (fun m : X ⟶ pullback g g => m x)
      (correspondenceGraph_leftMiddlePair f g)).symm
  have ht := exists_regular_kernel_and_regular_image_of_openCharts
    (pullback.diagonal g) (leftGraphMiddlePair f g)
    (pullback.diagonal g) (graphMiddlePair f g)
    (𝟙 Y) (𝟙 (pullback (f ≫ g) g)) (pullbackSymmetry g g).hom
    (by simp) (by simp [leftGraphMiddlePair])
    (f x) (correspondenceGraph f g x) (pullback.diagonal g (f x)) rfl hp
    (by simp) (by simpa using hl) (by simpa [diagonalStalkMap] using h)
  have hn := common_regular_list_congr_points
    (pullback.diagonal g) (leftGraphMiddlePair f g)
    (f x) (f x) (correspondenceGraph f g x) (correspondenceGraph f g x)
    _ (pullback.diagonal g (f x)) rfl rfl (symmetry_diagonal_apply g (f x))
    (symmetry_diagonal_apply g (f x)) ((symmetry_diagonal_apply g (f x)).trans hl)
    rfl hl ht
  simpa only [alignedStalkMap_rfl, leftDiagonalStalkMap] using hn


end Motivic.Graph
