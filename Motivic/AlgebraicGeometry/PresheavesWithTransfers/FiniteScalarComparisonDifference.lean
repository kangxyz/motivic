/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.PresheavesWithTransfers.FiniteScalarComparison
public import Motivic.AlgebraicGeometry.PresheavesWithTransfers.FiniteScalarRestrictionDifference

/-!
# Original extended-coefficient signed relations and actual scalar trace

The corrections are sections of the actual finite-separable coefficient on
base changes of one fixed original diagram. The canonical geometric comparison
transports their signed equation to precisely the scalar-trace input. Arbitrary
extension refinements are not asserted to descend.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe v u

namespace Motivic.PresheafWithTransfers

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  [Module.Finite k L] [Algebra.IsSeparable k L]
  (P : PresheafWithTransfers.{v} k)

local notation "B" => SmoothSite.fieldBaseChange (algebraMap k L)
local notation "Q" => finiteSeparableExtension L P

/-- Transport of the original signed relation preserves its sign, all three
original graph arrows, and the literal scalar restriction of its generator. -/
theorem finiteScalarSectionIso_restriction_difference
    {O T A D : SmoothSite (Spec (.of k))}
    (β : O ⟶ T) (α : O ⟶ A) (φ : O ⟶ D)
    (s : sections P (Cor.mk D))
    (a : sections Q (Cor.mk ((B).obj T))) (c : sections Q (Cor.mk ((B).obj A)))
    (h : transfer Q ((Cor.graphFunctor L).map ((B).map β)) a -
      transfer Q ((Cor.graphFunctor L).map ((B).map α)) c =
      transfer Q ((Cor.graphFunctor L).map ((B).map φ))
        (transfer P ((Cor.graphFunctor k).map
          (SmoothSite.fieldBaseChangeForgetProjection (L := L) D)) s)) :
    transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarMap (E := L) β))
        ((finiteScalarSectionIso (L := L) P T).hom a) -
      transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarMap (E := L) α))
        ((finiteScalarSectionIso (L := L) P A).hom c) =
      transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarMap (E := L) φ))
        (transfer P ((Cor.graphFunctor k).map
          (SmoothSite.finiteScalarProjection (E := L) D)) s) := by
  have hn {U V : SmoothSite (Spec (.of k))} (f : U ⟶ V)
      (x : sections Q (Cor.mk ((B).obj V))) :=
    ConcreteCategory.congr_hom (finiteScalarSectionIso_naturality (L := L) P f) x
  have hp := ConcreteCategory.congr_hom (finiteScalarSectionIso_projection (L := L) P D) s
  simp only [ConcreteCategory.comp_apply] at hn hp
  have ht := congrArg (finiteScalarSectionIso (L := L) P O).hom h
  erw [map_sub, hn β a, hn α c, hn φ, hp] at ht
  exact ht

/-- Actual trace of an extended-coefficient signed relation gives its whole
extension degree on the original diagram. Flatness is needed only for corrections. -/
theorem finiteScalarTrace_finiteSeparable_restriction_difference
    {O T A D : SmoothSite (Spec (.of k))}
    (β : O ⟶ T) [Flat β.left] (α : O ⟶ A) [Flat α.left] (φ : O ⟶ D)
    (s : sections P (Cor.mk D))
    (a : sections Q (Cor.mk ((B).obj T))) (c : sections Q (Cor.mk ((B).obj A)))
    (h : transfer Q ((Cor.graphFunctor L).map ((B).map β)) a -
      transfer Q ((Cor.graphFunctor L).map ((B).map α)) c =
      transfer Q ((Cor.graphFunctor L).map ((B).map φ))
        (transfer P ((Cor.graphFunctor k).map
          (SmoothSite.fieldBaseChangeForgetProjection (L := L) D)) s)) :
    transfer P ((Cor.graphFunctor k).map β)
        (transfer P (Cor.finiteFlatTrace (SmoothSite.finiteScalarProjection (E := L) T))
          ((finiteScalarSectionIso (L := L) P T).hom a)) -
      transfer P ((Cor.graphFunctor k).map α)
        (transfer P (Cor.finiteFlatTrace (SmoothSite.finiteScalarProjection (E := L) A))
          ((finiteScalarSectionIso (L := L) P A).hom c)) =
      (Module.finrank k L : ℤ) • transfer P ((Cor.graphFunctor k).map φ) s :=
  finiteScalarTrace_restriction_difference P β α φ s _ _
    (finiteScalarSectionIso_restriction_difference P β α φ s a c h)

end Motivic.PresheafWithTransfers
