/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.FiniteScalarTrace
public import Motivic.AlgebraicGeometry.PresheavesWithTransfers.Basic

/-!
# Finite scalar trace on the original presheaf with transfers

All maps are the original signed correspondence action. Neither homotopy
invariance nor a supplied trace or cohomological comparison is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe v u

namespace Motivic.PresheafWithTransfers

variable {k : Type u} [Field k] (P : PresheafWithTransfers.{v} k)

/-- Original trace commutes with original restrictions in a flat Cartesian
square; an open immersion is an important special case. -/
theorem finiteFlatTrace_cartesian {X Y U V : SmoothSite (Spec (.of k))}
    (p : Y ⟶ X) [IsFinite p.left] [Flat p.left]
    (q : V ⟶ U) [IsFinite q.left] [Flat q.left]
    (j : U ⟶ X) [Flat j.left] (i : V ⟶ Y)
    (sq : IsPullback q.left i.left j.left p.left) :
    transfer P ((Cor.graphFunctor k).map i) ≫ transfer P (Cor.finiteFlatTrace q) =
      transfer P (Cor.finiteFlatTrace p) ≫ transfer P ((Cor.graphFunctor k).map j) := by
  simpa only [transfer_comp] using
    congrArg (transfer P) (Cor.finiteFlatTrace_cartesian p q j i sq)

variable {E : Type u} [Field E] [Algebra k E]
  [Module.Finite k E] [Algebra.IsSeparable k E]

/-- The original scalar restriction followed by the actual trace multiplies
sections by the entire extension degree. -/
theorem finiteScalar_restriction_trace (X : SmoothSite (Spec (.of k))) :
    transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarProjection (E := E) X)) ≫
        transfer P (Cor.finiteFlatTrace (SmoothSite.finiteScalarProjection (E := E) X)) =
      (Module.finrank k E : ℤ) • 𝟙 (sections P (Cor.mk X)) := by
  simpa only [transfer_comp, transfer_zsmul, transfer_id] using
    congrArg (transfer P) (Cor.finiteScalarTrace_comp_graph (E := E) X)

/-- Actual scalar trace and restriction commute on the original coefficient,
with no separately supplied Cartesian or transfer compatibility. -/
theorem finiteScalarTrace_naturality {U X : SmoothSite (Spec (.of k))}
    (j : U ⟶ X) [Flat j.left] :
    transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarMap (E := E) j)) ≫
        transfer P (Cor.finiteFlatTrace (SmoothSite.finiteScalarProjection (E := E) U)) =
      transfer P (Cor.finiteFlatTrace (SmoothSite.finiteScalarProjection (E := E) X)) ≫
        transfer P ((Cor.graphFunctor k).map j) := by
  simpa only [transfer_comp] using
    congrArg (transfer P) (Cor.finiteScalarTrace_naturality (E := E) j)

/-- A section killed by its actual scalar restriction is killed by the full
extension degree in its unchanged original section group. -/
theorem finrank_smul_eq_zero_of_scalar_restriction_eq_zero
    (X : SmoothSite (Spec (.of k))) (s : sections P (Cor.mk X))
    (hs : transfer P ((Cor.graphFunctor k).map
      (SmoothSite.finiteScalarProjection (E := E) X)) s = 0) :
    (Module.finrank k E : ℤ) • s = 0 := by
  have h := congrArg (fun f => f s) (finiteScalar_restriction_trace (E := E) P X)
  change transfer P (Cor.finiteFlatTrace (SmoothSite.finiteScalarProjection (E := E) X))
    (transfer P ((Cor.graphFunctor k).map
      (SmoothSite.finiteScalarProjection (E := E) X)) s) =
      (Module.finrank k E : ℤ) • s at h
  simpa only [hs, map_zero] using h.symm

end Motivic.PresheafWithTransfers
