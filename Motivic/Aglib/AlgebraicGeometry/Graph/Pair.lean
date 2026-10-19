/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Graph.CommonStalkTransport
public import Motivic.Aglib.AlgebraicGeometry.Graph.PairGeometry

/-!
# The actual graph-to-diagonal pair map on stalks

The graph ambient product maps to the target self-product by applying the
original morphism to its first factor. We record its chart naturality and the
actual stalk map at a graph point, with the source point identified with the
diagonal point. These are literal maps used by the common-list theorem.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Graph
open _root_.AlgebraicGeometry.Scheme.Products

variable {X Y S : Scheme.{u}}

/-- The actual pair map for a graph with a specified compatible structural map. -/
def middlePair (a : X ⟶ S) (b : Y ⟶ S) (f : X ⟶ Y) (h : f ≫ b = a) :
    pullback a b ⟶ pullback b b :=
  pullback.map a b b b f (𝟙 Y) (𝟙 S) (by simpa using h.symm) (by simp)

@[reassoc (attr := simp)]
theorem middlePair_fst (a : X ⟶ S) (b : Y ⟶ S) (f : X ⟶ Y) (h : f ≫ b = a) :
    middlePair a b f h ≫ pullback.fst b b = pullback.fst a b ≫ f :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem middlePair_snd (a : X ⟶ S) (b : Y ⟶ S) (f : X ⟶ Y) (h : f ≫ b = a) :
    middlePair a b f h ≫ pullback.snd b b = pullback.snd a b := by
  simp only [middlePair, pullback.map, pullback.lift_snd, Category.comp_id]

/-- The actual graph maps to the actual target diagonal. -/
@[reassoc]
theorem morphism_middlePair (a : X ⟶ S) (b : Y ⟶ S) (f : X ⟶ Y) (h : f ≫ b = a) :
    morphism a b f h ≫ middlePair a b f h = f ≫ pullback.diagonal b := by
  apply pullback.hom_ext <;> simp

/-- The actual graph-to-diagonal stalk map for a specified compatible structural map. -/
def genericDiagonalStalkMap (a : X ⟶ S) (b : Y ⟶ S) (f : X ⟶ Y) (h : f ≫ b = a) (x : X) :
    (pullback b b).presheaf.stalk (pullback.diagonal b (f x)) ⟶
      (pullback a b).presheaf.stalk (morphism a b f h x) :=
  alignedStalkMap (middlePair a b f h) (morphism a b f h x)
    (pullback.diagonal b (f x)) (by
      exact (congrArg (fun k : X ⟶ pullback b b => k x) (morphism_middlePair a b f h)).symm)

/-- The generic pair map agrees with the actual correspondence graph adapter. -/
theorem middlePair_eq_graphMiddlePair (f : X ⟶ Y) (b : Y ⟶ S) :
    middlePair (f ≫ b) b f rfl = graphMiddlePair f b := rfl

/-- The generic graph agrees with the actual correspondence graph. -/
theorem morphism_eq_correspondenceGraph (f : X ⟶ Y) (b : Y ⟶ S) :
    morphism (f ≫ b) b f rfl = _root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph f b := rfl

/-- The actual graph-to-diagonal map of stalks, including the canonical point identification. -/
def diagonalStalkMap (f : X ⟶ Y) (g : Y ⟶ S) (x : X) :
    (pullback g g).presheaf.stalk (pullback.diagonal g (f x)) ⟶
      (pullback (f ≫ g) g).presheaf.stalk
        (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph f g x) :=
  alignedStalkMap (graphMiddlePair f g) (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph
    f g x)
    (pullback.diagonal g (f x)) (by
      change (f ≫ pullback.diagonal g) x =
        (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph f g ≫ graphMiddlePair f g) x
      rw [_root_.AlgebraicGeometry.Scheme.Products.correspondenceGraph_middlePair])

/-- The generic aligned stalk map is the exact map used by correspondence graph consumers. -/
theorem genericDiagonalStalkMap_eq_diagonalStalkMap (f : X ⟶ Y) (g : Y ⟶ S) (x : X) :
    genericDiagonalStalkMap (f ≫ g) g f rfl x = diagonalStalkMap f g x := rfl

variable {X' Y' S' : Scheme.{u}}
  (a : X ⟶ S) (b : Y ⟶ S) (f : X ⟶ Y) (h : f ≫ b = a)
  (a' : X' ⟶ S') (b' : Y' ⟶ S') (f' : X' ⟶ Y') (h' : f' ≫ b' = a')
  (iX : X' ⟶ X) (iY : Y' ⟶ Y) (iS : S' ⟶ S)
  (ha : a' ≫ iS = iX ≫ a) (hb : b' ≫ iS = iY ≫ b) (hf : f' ≫ iY = iX ≫ f)

include hf in
set_option backward.isDefEq.respectTransparency false in
/-- The actual pair maps commute with the actual open-chart ambient maps. -/
theorem middlePair_productMap :
    middlePair a' b' f' h' ≫ Diagonal.productMap b b' iY iS hb =
      productMap a b a' b' iX iY iS ha hb ≫ middlePair a b f h := by
  apply pullback.hom_ext <;> simp [middlePair, Diagonal.productMap, productMap, pullback.map, hf]

end AlgebraicGeometry.Scheme.Graph
