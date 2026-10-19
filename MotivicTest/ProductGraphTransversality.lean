/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Graph.ProductTransversality

/-!
# Consumers of the mixed-product common regular list

The source support and parameter map are arbitrary. In particular these
consumers impose neither smoothness on the support nor flatness on either
map. They retain the actual diagonal kernel, the same list's literal scalar
images, and all four coordinates of the mixed embedding.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingTheory.Sequence

universe u

namespace MotivicTest.ProductGraphTransversality
open _root_.AlgebraicGeometry.Scheme.Graph

variable {S X V T T' : Scheme.{u}}
  (f : X ⟶ S) (g : T' ⟶ S) (p : V ⟶ X) (u : T ⟶ T')

/-- The mixed middle pair is the graph pair under the actual factor swaps. -/
theorem actual_mixed_pair_square :
    Product.mixedPair f g p u ≫ Product.partialSwap f g f g =
      (Product.coefficientGraphIso f g p u).hom ≫
        _root_.AlgebraicGeometry.Scheme.Products.graphMiddlePair (Product.supportMap f g p u)
            (Product.middleHom f g) :=
  Product.mixedPair_partialSwap f g p u

/-- The full mixed incidence scheme is obtained, rather than an assumed lift of a point. -/
theorem actual_mixed_pullback :
    IsPullback (Product.supportMap f g p u) (Product.mixedEmbedding f g p u)
      (pullback.diagonal (Product.middleHom f g)) (Product.mixedPair f g p u) :=
  Product.mixed_isPullback f g p u

/-- The original support coordinate is retained by the mixed incidence embedding. -/
theorem actual_support_coordinate :
    Product.mixedEmbedding f g p u ≫ Product.third f (u ≫ g) (p ≫ f) g =
      pullback.fst (p ≫ f) (u ≫ g) :=
  Product.mixedEmbedding_third f g p u

/-- The target parameter coordinate is the original arbitrary map, without replacement. -/
theorem actual_parameter_coordinate :
    Product.mixedEmbedding f g p u ≫ Product.fourth f (u ≫ g) (p ≫ f) g =
      pullback.snd (p ≫ f) (u ≫ g) ≫ u :=
  Product.mixedEmbedding_fourth f g p u

/-- A single kernel-generating regular list remains regular through its actual mixed scalars. -/
theorem actual_common_regular_list [Smooth (Product.middleHom f g)]
    (v : Product.support f g p u) :
    ∃ rs : List ((pullback (Product.middleHom f g)
      (Product.middleHom f g)).presheaf.stalk
        (pullback.diagonal (Product.middleHom f g) (Product.supportMap f g p u v))),
      IsRegular ((pullback (Product.middleHom f g)
        (Product.middleHom f g)).presheaf.stalk
          (pullback.diagonal (Product.middleHom f g) (Product.supportMap f g p u v)))
        rs ∧
      RingHom.ker ((pullback.diagonal (Product.middleHom f g)).stalkMap
        (Product.supportMap f g p u v)).hom = Ideal.ofList rs ∧
      IsRegular ((Product.coefficient f g p u).presheaf.stalk
        (Product.mixedEmbedding f g p u v))
        (rs.map (Product.mixedDiagonalStalkMap f g p u v).hom) :=
  Product.exists_common_regular_list f g p u v

end MotivicTest.ProductGraphTransversality
