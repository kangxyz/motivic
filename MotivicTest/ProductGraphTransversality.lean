/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.ProductGraphTransversality

/-!
# Consumers of the mixed-product common regular list

The source support and parameter map are arbitrary. In particular these
consumers impose neither smoothness on the support nor flatness on either
map. They retain the actual diagonal kernel, the same list's literal scalar
images, and all four coordinates of the mixed embedding.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingTheory.Sequence Motivic

universe u

namespace MotivicTest.ProductGraphTransversality

variable {S X V T T' : Scheme.{u}}
  (f : X ⟶ S) (g : T' ⟶ S) (p : V ⟶ X) (u : T ⟶ T')

/-- The mixed middle pair is the graph pair under the actual factor swaps. -/
theorem actual_mixed_pair_square :
    ProductGraph.mixedPair f g p u ≫ ProductGraph.partialSwap f g f g =
      (ProductGraph.coefficientGraphIso f g p u).hom ≫
        graphMiddlePair (ProductGraph.supportMap f g p u) (ProductGraph.middleHom f g) :=
  ProductGraph.mixedPair_partialSwap f g p u

/-- The full mixed incidence scheme is obtained, rather than an assumed lift of a point. -/
theorem actual_mixed_pullback :
    IsPullback (ProductGraph.supportMap f g p u) (ProductGraph.mixedEmbedding f g p u)
      (pullback.diagonal (ProductGraph.middleHom f g)) (ProductGraph.mixedPair f g p u) :=
  ProductGraph.mixed_isPullback f g p u

/-- The original support coordinate is retained by the mixed incidence embedding. -/
theorem actual_support_coordinate :
    ProductGraph.mixedEmbedding f g p u ≫ ProductGraph.third f (u ≫ g) (p ≫ f) g =
      pullback.fst (p ≫ f) (u ≫ g) :=
  ProductGraph.mixedEmbedding_third f g p u

/-- The target parameter coordinate is the original arbitrary map, without replacement. -/
theorem actual_parameter_coordinate :
    ProductGraph.mixedEmbedding f g p u ≫ ProductGraph.fourth f (u ≫ g) (p ≫ f) g =
      pullback.snd (p ≫ f) (u ≫ g) ≫ u :=
  ProductGraph.mixedEmbedding_fourth f g p u

/-- A single kernel-generating regular list remains regular through its actual mixed scalars. -/
theorem actual_common_regular_list [Smooth (ProductGraph.middleHom f g)]
    (v : ProductGraph.support f g p u) :
    ∃ rs : List ((pullback (ProductGraph.middleHom f g)
      (ProductGraph.middleHom f g)).presheaf.stalk
        (pullback.diagonal (ProductGraph.middleHom f g) (ProductGraph.supportMap f g p u v))),
      IsRegular ((pullback (ProductGraph.middleHom f g)
        (ProductGraph.middleHom f g)).presheaf.stalk
          (pullback.diagonal (ProductGraph.middleHom f g) (ProductGraph.supportMap f g p u v)))
        rs ∧
      RingHom.ker ((pullback.diagonal (ProductGraph.middleHom f g)).stalkMap
        (ProductGraph.supportMap f g p u v)).hom = Ideal.ofList rs ∧
      IsRegular ((ProductGraph.coefficient f g p u).presheaf.stalk
        (ProductGraph.mixedEmbedding f g p u v))
        (rs.map (ProductGraph.mixedDiagonalStalkMap f g p u v).hom) :=
  ProductGraph.exists_common_regular_list f g p u v

end MotivicTest.ProductGraphTransversality
