/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.GraphPolynomialBlock
public import Motivic.AlgebraicGeometry.Correspondences.ProductGraphTransversality
public import Motivic.AlgebraicGeometry.Intersection.CoefficientStalkTransport

/-!
# A common actual graph block on a closed support

A flat ambient projection to a smooth scheme and an arbitrary closed support
have one literal graph-kernel list regular in both actual product stalks.
Flatness is required only for the ambient projection. The closed support's
projection need not be flat. All comparisons retain the actual closed product
map, graph stalk maps, and the same diagonal equation list.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingTheory.Sequence

universe u

namespace Motivic.Graph

variable {C P X S : Scheme.{u}} (h : P ⟶ X) (b : X ⟶ S) (j : C ⟶ P)

/-- The original closed support induces this actual map of graph ambient products. -/
def supportProductMap : pullback ((j ≫ h) ≫ b) b ⟶ pullback (h ≫ b) b :=
  pullback.map _ _ _ _ j (𝟙 X) (𝟙 S) (by simp) (by simp)

instance supportProductMap_closed [IsClosedImmersion j] :
    IsClosedImmersion (supportProductMap h b j) := by
  exact MorphismProperty.pullbackMap (P := @IsClosedImmersion)
    (inferInstanceAs (IsClosedImmersion j)) (inferInstanceAs (IsClosedImmersion (𝟙 X)))
    (by simp) (by simp)

@[reassoc]
theorem supportProductMap_graph :
    correspondenceGraph (j ≫ h) b ≫ supportProductMap h b j = j ≫ correspondenceGraph h b := by
  apply pullback.hom_ext <;> simp [supportProductMap, pullback.map]

@[reassoc]
theorem supportProductMap_middlePair :
    supportProductMap h b j ≫ graphMiddlePair h b = graphMiddlePair (j ≫ h) b := by
  apply pullback.hom_ext <;> simp [supportProductMap, pullback.map]

/-- The literal closed-support stalk action at the two actual graph points. -/
def supportStalkMap (x : C) :
    (pullback (h ≫ b) b).presheaf.stalk (correspondenceGraph h b (j x)) ⟶
      (pullback ((j ≫ h) ≫ b) b).presheaf.stalk (correspondenceGraph (j ≫ h) b x) :=
  StalkTransport.pointedMap (supportProductMap h b j)
    (correspondenceGraph (j ≫ h) b x) (correspondenceGraph h b (j x))
    (congrArg (fun q : C ⟶ pullback (h ≫ b) b => q x)
      (supportProductMap_graph h b j)).symm

/-- The same diagonal scalar has exactly the same image by the two literal paths. -/
theorem diagonalStalkMap_supportStalkMap (x : C) :
    diagonalStalkMap h b (j x) ≫ supportStalkMap h b j x =
      diagonalStalkMap (j ≫ h) b x := by
  have hp : pullback.diagonal b (h (j x)) =
      graphMiddlePair h b (correspondenceGraph h b (j x)) :=
    (congrArg (fun q : P ⟶ pullback b b => q (j x))
      (correspondenceGraph_middlePair h b)).symm
  have hq : pullback.diagonal b (h (j x)) =
      graphMiddlePair (j ≫ h) b (correspondenceGraph (j ≫ h) b x) :=
    (congrArg (fun q : C ⟶ pullback b b => q x)
      (correspondenceGraph_middlePair (j ≫ h) b)).symm
  have hr : correspondenceGraph h b (j x) =
      supportProductMap h b j (correspondenceGraph (j ≫ h) b x) :=
    (congrArg (fun q : C ⟶ pullback (h ≫ b) b => q x)
      (supportProductMap_graph h b j)).symm
  change StalkTransport.pointedMap (graphMiddlePair h b) _ _ hp ≫
      StalkTransport.pointedMap (supportProductMap h b j) _ _ hr =
    StalkTransport.pointedMap (graphMiddlePair (j ≫ h) b) _ _ hq
  rw [StalkTransport.pointedMap_comp]
  exact StalkTransport.pointedMap_congr _ _ (supportProductMap_middlePair h b j) _ _ _ _

/-- The graph pair is flat only when its original ambient projection is flat. -/
instance graphMiddlePair_flat [Flat h] : Flat (graphMiddlePair h b) := by
  exact MorphismProperty.pullbackMap (P := @Flat)
    (inferInstanceAs (Flat h)) (inferInstanceAs (Flat (𝟙 X))) (by simp) (by simp)

/-- The graph kernel is the image of the actual diagonal kernel, without any flatness premise. -/
theorem graph_kernel_eq_diagonalImage [IsSeparated b] (x : P)
    (t : List ((pullback b b).presheaf.stalk (pullback.diagonal b (h x))))
    (hker : RingHom.ker ((pullback.diagonal b).stalkMap (h x)).hom = Ideal.ofList t) :
    RingHom.ker ((correspondenceGraph h b).stalkMap x).hom =
      Ideal.ofList (t.map (diagonalStalkMap h b x).hom) := by
  rw [Diagonal.baseChange_stalk_kernel (ProductGraph.graphPair_isPullback h b) x,
    hker, Ideal.map_ofList]
  rfl

/-- One actual graph-kernel list is regular on the ambient product and its
closed support product. No flatness of `j ≫ h` is used. -/
theorem exists_common_graphKernel [Smooth b] [IsSeparated b] [Flat h] (x : C) :
    ∃ t : List ((pullback (h ≫ b) b).presheaf.stalk (correspondenceGraph h b (j x))),
      IsRegular ((pullback (h ≫ b) b).presheaf.stalk (correspondenceGraph h b (j x))) t ∧
      RingHom.ker ((correspondenceGraph h b).stalkMap (j x)).hom = Ideal.ofList t ∧
      IsRegular ((pullback ((j ≫ h) ≫ b) b).presheaf.stalk (correspondenceGraph (j ≫ h) b x))
        (t.map (supportStalkMap h b j x).hom) ∧
      RingHom.ker ((correspondenceGraph (j ≫ h) b).stalkMap x).hom =
        Ideal.ofList (t.map (supportStalkMap h b j x).hom) := by
  obtain ⟨t, ht, hker, hC⟩ := exists_common_regular_list_of_smooth (j ≫ h) b x
  have hP := Diagonal.mapped_equations_isRegular (ProductGraph.graphPair_isPullback h b) (j x)
    ht.toIsWeaklyRegular hker.ge
  have hmap : (t.map (diagonalStalkMap h b (j x)).hom).map
      (supportStalkMap h b j x).hom = t.map (diagonalStalkMap (j ≫ h) b x).hom := by
    rw [List.map_map]
    change t.map (⇑((diagonalStalkMap h b (j x) ≫ supportStalkMap h b j x).hom)) = _
    rw [diagonalStalkMap_supportStalkMap]
    rfl
  refine ⟨t.map (diagonalStalkMap h b (j x)).hom, hP,
    graph_kernel_eq_diagonalImage h b (j x) t hker, ?_, ?_⟩
  · rw [hmap]
    exact hC
  · rw [hmap]
    exact graph_kernel_eq_diagonalImage (j ≫ h) b x t hker

end Motivic.Graph
