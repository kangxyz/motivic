/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Data.BoundarySectionData
public import Motivic.Transfers.Presheaf.Actions.Pencils.Graph
public import Motivic.Transfers.Presheaf.Actions.Pencils.Correction

/-!
# The same section data acts through the original restriction

The literal retained inclusion is followed by the actual restriction map. Both
actions come from the checked graph and correction pencils for one unchanged
BoundarySectionData. No action equality or new section choice is supplied.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open Scheme.Modules Scheme.Modules.Invertible
universe u w
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil
local instance {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f] :
    Smooth f := SmoothOfRelativeDimension.smooth 1 f

variable (k : Type u) [Field k] {S X Y A B Z C D V : Scheme.{u}}
  [IsAffine S] [IsAffine Y] [IsAffine A] [IsAffine B] [IsAffine V]
  (t : S ⟶ Spec (.of k)) [Smooth t]
  (q : X ⟶ S) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (π : C ⟶ S) [IsProper π]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  (p : Y ⟶ X) [Flat p] (hq : j ≫ π = p ≫ q)
  (a : A ⟶ X) [IsOpenImmersion a]
  (α : B ⟶ Y) [Smooth α] (β : B ⟶ A) [Flat β] (h : α ≫ p = β ≫ a)
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 _) p z)
  (e : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
    Hom.idealModule (Hom.boundaryGraphTarget q z))
  (ha : Disjoint (Set.range a) (Set.range z)) (d : D ⟶ C)
  (hd : Disjoint (Set.range j) (Set.range d))

/-- The same original lambda and correction act as the original restriction
and zero after the actual retained inclusion followed by that restriction. -/
theorem BoundarySectionData.transfer_postcompose_original_restriction
    (c : BoundarySectionData q π j p hq a z s hs H e ha d hd)
    (v : V ⟶ C) [IsOpenImmersion v] [SmoothOfRelativeDimension 1 (v ≫ π)]
    (hc : ∀ x : C, x ∈ Set.range v ∨ x ∈ Set.range d ∨ x ∈ Set.range (s ≫ j))
    (φ : B ⟶ V) (hφ : φ ≫ v = α ≫ j)
    (u : V ⟶ Y) (hu : u ≫ j = v)
    (Q : SmoothSite (Spec (.of k))) (r : lambdaSourceSite k t π j ⟶ Q)
    (P : PresheafWithTransfers.{w} k) (hP : P.IsA1Invariant) :
    let uSite : relativeTargetSite k t π v ⟶ lambdaSourceSite k t π j :=
      SmoothSite.homMk u (by
        change u ≫ ((j ≫ π) ≫ t) = (v ≫ π) ≫ t
        simpa only [Category.assoc] using congrArg (fun f => f ≫ π ≫ t) hu)
    let D := BoundarySectionData.toData k t q π j p hq a α β h z s hs H e ha d hd
      c v hc φ hφ
    PresheafWithTransfers.transfer P (D.lam ≫ (Cor.graphFunctor k).map (uSite ≫ r)) =
        PresheafWithTransfers.transfer P ((Cor.graphFunctor k).map r) ∧
      PresheafWithTransfers.transfer P (D.psi ≫ (Cor.graphFunctor k).map (uSite ≫ r)) = 0 := by
  let := c.a_unit
  let := c.b_unit
  let := c.n_unit
  let := c.d_unit
  let uSite : relativeTargetSite k t π v ⟶ lambdaSourceSite k t π j :=
    SmoothSite.homMk u (by
      change u ≫ ((j ≫ π) ≫ t) = (v ≫ π) ≫ t
      simpa only [Category.assoc] using congrArg (fun f => f ≫ π ≫ t) hu)
  let D := BoundarySectionData.toData k t q π j p hq a α β h z s hs H e ha d hd
    c v hc φ hφ
  have hL : PresheafWithTransfers.transfer P (D.lam ≫ (Cor.graphFunctor k).map uSite) =
      PresheafWithTransfers.transfer P
        ((Cor.graphFunctor k).map (𝟙 (lambdaSourceSite k t π j))) := by
    exact transfer_dataOfBoundarySections_lam_comp_graph_eq_id
      k t q π j p hq a α β h z s hs H e ha d hd v hc
      c.T c.N c.aS c.bS c.nS c.dS c.hA c.hN φ hφ u hu P hP
  have hN : PresheafWithTransfers.transfer P (D.psi ≫ (Cor.graphFunctor k).map uSite) = 0 := by
    exact transfer_dataOfBoundarySections_psi_comp_graph_eq_zero
      k t q π j p hq a α β h z s hs H e ha d hd v hc
      c.T c.N c.aS c.bS c.nS c.dS c.hA c.hN φ hφ u hu P hP
  change PresheafWithTransfers.transfer P (D.lam ≫ (Cor.graphFunctor k).map (uSite ≫ r)) = _ ∧
    PresheafWithTransfers.transfer P (D.psi ≫ (Cor.graphFunctor k).map (uSite ≫ r)) = _
  constructor
  · rw [CategoryTheory.Functor.map_comp, ← Category.assoc,
      PresheafWithTransfers.transfer_comp, hL, CategoryTheory.Functor.map_id,
      PresheafWithTransfers.transfer_id, Category.comp_id]
  · rw [CategoryTheory.Functor.map_comp, ← Category.assoc,
      PresheafWithTransfers.transfer_comp, hN, comp_zero]

end AlgebraicGeometry.Scheme.RelativeCurvePencil
