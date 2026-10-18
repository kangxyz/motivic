/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.OpenRangeFrame
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.RetainedGraph
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.InfinityBoundaryIdeal
public import Motivic.AlgebraicGeometry.Cycles.IdealFrameMovedCycle

/-!
# Moving the original compactification graph with a prescribed boundary frame

The graph ideal is literal. The infinity frame is its canonical inclusion, and
only the marked frame is supplied by splitting. The first consumer treats an
integral Noetherian ambient product with nonempty whole boundary; disconnected
assembly and the empty-boundary branch remain separate. No principal A1 relation
or simultaneous covering compatibility is asserted.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible Scheme.Hom

universe u

namespace Motivic.GraphIdealMovedCycle

variable {S C T D Z : Scheme.{u}} (q : C ⟶ S) [IsSeparated q]
  (j : T ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ q)]
  (d : D ⟶ C) (z : Z ⟶ C)
  (hd : Disjoint (Set.range j) (Set.range d))
  (eZ : (Scheme.Modules.pullback (infinityProductMap q j z)).obj
      (idealModule (compactificationGraph q j)) ≅
    SheafOfModules.unit (pullback (pullback.snd (j ≫ q) q) z).ringCatSheaf)

omit [SmoothOfRelativeDimension 1 (j ≫ q)] in
/-- The actual coproduct frame uses the canonical infinity inclusion and the
original marked splitting, preserving both exact component restrictions. -/
def wholeBoundaryFrame :
    (Scheme.Modules.pullback (coprod.desc (infinityProductMap q j d)
      (infinityProductMap q j z))).obj (idealModule (compactificationGraph q j)) ≅
    SheafOfModules.unit
      (pullback (pullback.snd (j ≫ q) q) d ⨿
        pullback (pullback.snd (j ≫ q) q) z).ringCatSheaf :=
  Classical.choose (exists_coprod_pullback_unitIso
    (infinityProductMap q j d) (infinityProductMap q j z)
    (idealModule (compactificationGraph q j))
    (infinityBoundaryIdealIso q j d hd).symm eZ)

omit [SmoothOfRelativeDimension 1 (j ≫ q)] in
/-- The chosen whole frame has the two exact native component values. -/
theorem wholeBoundaryFrame_restrictions :
    (Scheme.Modules.restrictFunctor
      (coprod.inl : pullback (pullback.snd (j ≫ q) q) d ⟶ _)).map
        (wholeBoundaryFrame q j d z hd eZ).hom ≫ (restrictUnitIso _).hom =
      (coprodPullbackRestrictLeft (infinityProductMap q j d)
        (infinityProductMap q j z)).hom.app (idealModule (compactificationGraph q j)) ≫
          (infinityBoundaryIdealIso q j d hd).inv ∧
    (Scheme.Modules.restrictFunctor
      (coprod.inr : pullback (pullback.snd (j ≫ q) q) z ⟶ _)).map
        (wholeBoundaryFrame q j d z hd eZ).hom ≫ (restrictUnitIso _).hom =
      (coprodPullbackRestrictRight (infinityProductMap q j d)
        (infinityProductMap q j z)).hom.app (idealModule (compactificationGraph q j)) ≫
          eZ.hom :=
  Classical.choose_spec (exists_coprod_pullback_unitIso
    (infinityProductMap q j d) (infinityProductMap q j z)
    (idealModule (compactificationGraph q j))
    (infinityBoundaryIdealIso q j d hd).symm eZ)

variable (A : (pullback (j ≫ q) q).affineOpens)
  (b : (pullback (pullback.snd (j ≫ q) q) d ⨿
    pullback (pullback.snd (j ≫ q) q) z) ⟶ A.val.toScheme)
  (hb : b ≫ A.val.ι =
    coprod.desc (infinityProductMap q j d) (infinityProductMap q j z))

/-- The boundary coordinate in the actual affine neighborhood is the same
whole graph frame, transported only by the specified factorization. -/
def affineBoundaryFrame :
    (Scheme.Modules.pullback b).obj
      (pullbackLineBundle A.val.ι (relativeCompactificationGraphLine q j)).val ≅
    SheafOfModules.unit
      (pullback (pullback.snd (j ≫ q) q) d ⨿
        pullback (pullback.snd (j ≫ q) q) z).ringCatSheaf :=
  (Scheme.Modules.pullbackComp b A.val.ι).app (idealModule (compactificationGraph q j)) ≪≫
    (Scheme.Modules.pullbackCongr hb).app (idealModule (compactificationGraph q j)) ≪≫
    wholeBoundaryFrame q j d z hd eZ

omit [SmoothOfRelativeDimension 1 (j ≫ q)] in
/-- The literal compactification graph is a closed immersion. -/
instance compactificationGraph_isClosedImmersion :
    IsClosedImmersion (compactificationGraph q j) := by
  dsimp only [compactificationGraph]
  infer_instance

end Motivic.GraphIdealMovedCycle

namespace Motivic.GraphIdealMovedCycle

variable {S C T D Z : Scheme.{u}} (q : C ⟶ S) [IsProper q]
  (j : T ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ q)]
  (d : D ⟶ C) (z : Z ⟶ C)
  (hd : Disjoint (Set.range j) (Set.range d))
  (eZ : (Scheme.Modules.pullback (infinityProductMap q j z)).obj
      (idealModule (compactificationGraph q j)) ≅
    SheafOfModules.unit (pullback (pullback.snd (j ≫ q) q) z).ringCatSheaf)

variable (A : (pullback (j ≫ q) q).affineOpens)
  (b : (pullback (pullback.snd (j ≫ q) q) d ⨿
    pullback (pullback.snd (j ≫ q) q) z) ⟶ A.val.toScheme)
  (hb : b ≫ A.val.ι =
    coprod.desc (infinityProductMap q j d) (infinityProductMap q j z))

/-- The original graph plus the native order of its boundary-frame ratio has
whole support finite over the unchanged parameter. All frame-extension data,
including the exact prescribed restriction, are retained in the witness. -/
theorem exists_original_graph_moved_sum
    [IsAffine T] [IsIntegral (pullback (j ≫ q) q)]
    [IsNoetherian (pullback (j ≫ q) q)]
    [IsClosedImmersion b]
    [Nonempty ((pullback (pullback.snd (j ≫ q) q) d ⨿
      pullback (pullback.snd (j ≫ q) q) z) : Scheme.{u})]
    {V : Scheme.{u}} [V.IsQuasiAffine]
    (v : V ⟶ pullback (j ≫ q) q) [IsOpenImmersion v]
    (hboundary : (Set.range v)ᶜ ⊆ Set.range
      (coprod.desc (infinityProductMap q j d) (infinityProductMap q j z))) :
    ∃ E : PrescribedAffineFrameExtension A b (relativeCompactificationGraphLine q j)
        (affineBoundaryFrame q j d z hd eZ A b hb),
      (∀ x ∈ E.affineOpen.val,
        idealFrameMovedCycle (compactificationGraph q j) E.affineOpen E.overFrame
          1 isUnit_one x = 0) ∧
      (∀ x, idealFrameMovedCycle (compactificationGraph q j) E.affineOpen E.overFrame
          1 isUnit_one x ≠ 0 →
        IsFinite ((IntegralClosedSubscheme.pointClosure x).val.subschemeι ≫
          pullback.fst (j ≫ q) q)) := by
  obtain ⟨E⟩ := nonempty_prescribedAffineFrameExtension A b
    (relativeCompactificationGraphLine q j) (affineBoundaryFrame q j d z hd eZ A b hb)
  have hI := (relativeCompactificationGraphLine q j).property
  refine ⟨E, fun _ hx => idealFrameMovedCycle_eq_zero_on_frame
    (compactificationGraph q j) E.affineOpen E.overFrame 1 isUnit_one hI hx, ?_⟩
  intro x hx
  apply idealFrameMovedCycle_support_isFinite
    (compactificationGraph q j) E.affineOpen E.overFrame 1 isUnit_one hI
    (pullback.fst (j ≫ q) q) v _ x hx
  rw [← hb] at hboundary
  exact hboundary.trans E.boundary_range_subset

end Motivic.GraphIdealMovedCycle
