/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.SmoothSiteFiniteScalarComparison
public import Motivic.AlgebraicGeometry.PresheavesWithTransfers.FiniteSeparableExtension

/-! # Original section comparison for finite scalar extension -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite

universe v u

namespace Motivic.PresheafWithTransfers

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  [Module.Finite k L] [Algebra.IsSeparable k L]
  (P : PresheafWithTransfers.{v} k)

/-- The section comparison is the original graph action of the actual scheme iso. -/
def finiteScalarSectionIso (X : SmoothSite (Spec (.of k))) :
    sections (finiteSeparableExtension L P)
        (Cor.mk ((SmoothSite.fieldBaseChange (algebraMap k L)).obj X)) ≅
      sections P (Cor.mk (SmoothSite.finiteScalarExtension (E := L) X)) :=
  ((toPresheaf k).obj P).mapIso (SmoothSite.fieldBaseChangeFiniteScalarIso (L := L) X).symm.op

/-- Original extended graph restrictions are intertwined with original scalar graphs. -/
theorem finiteScalarSectionIso_naturality {X Y : SmoothSite (Spec (.of k))} (f : X ⟶ Y) :
    transfer (finiteSeparableExtension L P)
        ((Cor.graphFunctor L).map ((SmoothSite.fieldBaseChange (algebraMap k L)).map f)) ≫
        (finiteScalarSectionIso (L := L) P X).hom =
      (finiteScalarSectionIso (L := L) P Y).hom ≫
        transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarMap (E := L) f)) := by
  rw [finiteSeparableExtension_transfer, Cor.finiteSeparableForgetBase_graph]
  change transfer P ((Cor.graphFunctor k).map
      ((SmoothSite.finiteSeparableForgetBase k L).map
        ((SmoothSite.fieldBaseChange (algebraMap k L)).map f))) ≫
      transfer P ((Cor.graphFunctor k).map
        (SmoothSite.fieldBaseChangeFiniteScalarIso (L := L) X).inv) =
    transfer P ((Cor.graphFunctor k).map
        (SmoothSite.fieldBaseChangeFiniteScalarIso (L := L) Y).inv) ≫
      transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarMap (E := L) f))
  rw [← transfer_comp, ← transfer_comp, ← Functor.map_comp, ← Functor.map_comp]
  rw [SmoothSite.fieldBaseChangeFiniteScalarIso_inv_naturality]

/-- Restricting an original section agrees with the original scalar projection,
not just an unspecified isomorphism of section groups. -/
theorem finiteScalarSectionIso_projection (X : SmoothSite (Spec (.of k))) :
    transfer P ((Cor.graphFunctor k).map
        (SmoothSite.fieldBaseChangeForgetProjection (L := L) X)) ≫
        (finiteScalarSectionIso (L := L) P X).hom =
      transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarProjection (E := L) X)) := by
  change transfer P ((Cor.graphFunctor k).map
      (SmoothSite.fieldBaseChangeForgetProjection (L := L) X)) ≫
      transfer P ((Cor.graphFunctor k).map
        (SmoothSite.fieldBaseChangeFiniteScalarIso (L := L) X).inv) = _
  rw [← transfer_comp, ← Functor.map_comp,
    SmoothSite.fieldBaseChangeFiniteScalarIso_inv_projection]

end Motivic.PresheafWithTransfers
