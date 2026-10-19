/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Transfers.Presheaf.Contraction
/-! # Literal graph-square transport of zero, preserving the original coefficient presheaf -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
universe v u
namespace Motivic.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme
variable {k : Type u} [Field k]

/-- Actual site isomorphisms reflect zero after a genuine commutative graph square. -/
theorem transfer_zero_of_iso_square (P : PresheafWithTransfers.{v} k)
    {X X' Y Y' : SmoothSite (Spec (.of k))} (i : X ≅ X') (j : Y ≅ Y')
    (f : Y ⟶ X) (g : Y' ⟶ X') (h : f ≫ i.hom = j.hom ≫ g)
    (s : P.sections (Cor.mk X'))
    (hz : P.transfer ((Cor.graphFunctor k).map f)
      (P.transfer ((Cor.graphFunctor k).map i.hom) s) = 0) :
    P.transfer ((Cor.graphFunctor k).map g) s = 0 := by
  have hi := (ConcreteCategory.bijective_of_isIso
    (P.transfer ((Cor.graphFunctor k).map j.hom))).injective
  apply hi
  have he : P.transfer ((Cor.graphFunctor k).map j.hom)
      (P.transfer ((Cor.graphFunctor k).map g) s) = 0 := by
    rw [← ConcreteCategory.comp_apply, ← transfer_comp, ← Functor.map_comp, ← h,
      Functor.map_comp, transfer_comp, ConcreteCategory.comp_apply]
    exact hz
  exact he.trans (map_zero (P.transfer ((Cor.graphFunctor k).map j.hom)).hom).symm

/-- The original torus presheaf's graph action is the literal product graph. -/
theorem torusSections_graph (P : PresheafWithTransfers.{v} k)
    {X Y : SmoothSite (Spec (.of k))} (f : X ⟶ Y) :
    (torusSections P).transfer ((Cor.graphFunctor k).map f) =
      P.transfer ((Cor.graphFunctor k).map
        (SmoothSite.productMap f (𝟙 (SmoothSite.torus (.of k))))) := by
  change P.transfer ((Cor.parameterProduct (SmoothSite.torus (.of k))).map
    ((Cor.graphFunctor k).map f)) = _
  rw [Cor.parameterProduct_graph]

end Motivic.PresheafWithTransfers
