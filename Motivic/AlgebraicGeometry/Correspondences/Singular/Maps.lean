/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Exterior.Simplex.GraphInterchange
public import Motivic.Transfers.Presheaf.Basic
public import Motivic.Aglib.Algebra.Homology.SingularComplex.Basic
public import Motivic.Aglib.AlgebraicGeometry.Simplex.CategoricalProduct

/-!
# Actual correspondence maps on all-degree singular complexes

For a smooth scheme `X`, the literal products `X × Δⁿ` form a cosimplicial
smooth scheme. Applying the graph functor gives a cosimplicial object of
actual finite correspondences. The mixed graph interchange law makes the
signed exterior cycles of any correspondence into a map of these objects.

The existing all-degree singular construction therefore supplies a genuine
chain map whose degree-`n` component is the transfer along `α × id_Δⁿ`.
The differentials are the original alternating coface pullbacks. No product
in the category of correspondences or exterior composition law is used.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open scoped Simplicial

universe v u

section

namespace Motivic.Cor
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k]

/-- The actual product simplex in correspondences, obtained through graph cycles. -/
def simplexProductCosimplicial (X : Cor k) : CosimplicialObject (Cor k) :=
  _root_.AlgebraicSimplex.productCosimplicialSmoothSite X.toSmoothSite ⋙ graphFunctor k

@[simp]
theorem simplexProductCosimplicial_obj (X : Cor k) (n : ℕ) :
    (simplexProductCosimplicial X).obj ⦋n⦌ = simplexProduct X n := rfl

/-- Every original simplex operator acts through its actual product graph. -/
theorem simplexProductCosimplicial_map (X : Cor k) {n m : SimplexCategory}
    (f : n ⟶ m) :
    (simplexProductCosimplicial X).map f =
      (graphFunctor k).map (SmoothSite.productMap (𝟙 X.toSmoothSite)
        ((_root_.AlgebraicSimplex.cosimplicialSmoothSite k).map f)) := rfl

/-- Cofaces in correspondences are the graphs of the original product cofaces. -/
@[simp]
theorem simplexProductCosimplicial_δ (X : Cor k) {n : ℕ} (i : Fin (n + 2)) :
    (simplexProductCosimplicial X).δ i =
      (graphFunctor k).map (SmoothSite.productMap (𝟙 X.toSmoothSite)
        ((_root_.AlgebraicSimplex.cosimplicialSmoothSite k).δ i)) :=
  simplexProductCosimplicial_map X (SimplexCategory.δ i)

/-- Mixed graph interchange gives a cosimplicial map for every signed correspondence. -/
def simplexExteriorNatTrans {X Y : Cor k} (α : X ⟶ Y) :
    simplexProductCosimplicial X ⟶ simplexProductCosimplicial Y where
  app n := simplexExterior n.len α
  naturality _n _m f :=
    (simplexExterior_graph_interchange
      ((_root_.AlgebraicSimplex.cosimplicialSmoothSite k).map f) α).symm

@[simp]
theorem simplexExteriorNatTrans_app {X Y : Cor k} (α : X ⟶ Y) (n : ℕ) :
    (simplexExteriorNatTrans α).app ⦋n⦌ = simplexExterior n α := rfl

end Motivic.Cor

namespace Motivic.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k]

/-- The existing all-degree singular complex on actual relative simplex products. -/
def singularObj (P : PresheafWithTransfers.{v} k) (X : Cor k) :
    ChainComplex AddCommGrpCat.{v} ℕ :=
  SingularComplex.obj (Cor.simplexProductCosimplicial X) P.obj

@[simp]
theorem singularObj_X (P : PresheafWithTransfers.{v} k) (X : Cor k) (n : ℕ) :
    (singularObj P X).X n = sections P (Cor.simplexProduct X n) := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The singular differential is the alternating sum of actual product-coface transfers. -/
theorem singularObj_d (P : PresheafWithTransfers.{v} k) (X : Cor k) (n : ℕ) :
    (singularObj P X).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        transfer P ((Cor.graphFunctor k).map (SmoothSite.productMap (𝟙 X.toSmoothSite)
          ((_root_.AlgebraicSimplex.cosimplicialSmoothSite k).δ i))) := by
  change (SingularComplex.obj (Cor.simplexProductCosimplicial X) P.obj).d (n + 1) n =
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
      P.obj.map ((Cor.graphFunctor k).map (SmoothSite.productMap (𝟙 X.toSmoothSite)
        ((_root_.AlgebraicSimplex.cosimplicialSmoothSite k).δ i))).op
  rw [SingularComplex.obj_d]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Cor.simplexProductCosimplicial_δ]

/-- An actual signed correspondence acts by a chain map in the reverse direction. -/
def singularTransfer (P : PresheafWithTransfers.{v} k) {X Y : Cor k} (α : X ⟶ Y) :
    singularObj P Y ⟶ singularObj P X :=
  SingularComplex.geometryMap (Cor.simplexExteriorNatTrans α) P.obj

@[simp]
theorem singularTransfer_f (P : PresheafWithTransfers.{v} k) {X Y : Cor k}
    (α : X ⟶ Y) (n : ℕ) :
    (singularTransfer P α).f n = transfer P (Cor.simplexExterior n α) := rfl

/-- Exterior transfers commute with every differential of the actual singular complex. -/
theorem singularTransfer_comm (P : PresheafWithTransfers.{v} k) {X Y : Cor k}
    (α : X ⟶ Y) (i j : ℕ) :
    transfer P (Cor.simplexExterior i α) ≫ (singularObj P X).d i j =
      (singularObj P Y).d i j ≫ transfer P (Cor.simplexExterior j α) :=
  (singularTransfer P α).comm i j

@[simp]
theorem singularTransfer_zero (P : PresheafWithTransfers.{v} k) (X Y : Cor k) :
    singularTransfer P (0 : X ⟶ Y) = 0 := by
  ext n : 1
  change transfer P (Cor.simplexExterior n (0 : X ⟶ Y)) = 0
  simp

@[simp]
theorem singularTransfer_add (P : PresheafWithTransfers.{v} k) {X Y : Cor k}
    (α β : X ⟶ Y) :
    singularTransfer P (α + β) = singularTransfer P α + singularTransfer P β := by
  ext n : 1
  change transfer P (Cor.simplexExterior n (α + β)) =
    transfer P (Cor.simplexExterior n α) + transfer P (Cor.simplexExterior n β)
  simp

@[simp]
theorem singularTransfer_neg (P : PresheafWithTransfers.{v} k) {X Y : Cor k}
    (α : X ⟶ Y) : singularTransfer P (-α) = -singularTransfer P α := by
  ext n : 1
  change transfer P (Cor.simplexExterior n (-α)) = -transfer P (Cor.simplexExterior n α)
  simp

@[simp]
theorem singularTransfer_zsmul (P : PresheafWithTransfers.{v} k) {X Y : Cor k}
    (m : ℤ) (α : X ⟶ Y) : singularTransfer P (m • α) = m • singularTransfer P α := by
  ext n : 1
  change transfer P (Cor.simplexExterior n (m • α)) = m • transfer P (Cor.simplexExterior n α)
  simp

end Motivic.PresheafWithTransfers

end
