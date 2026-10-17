/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.CoordinateGraphIdeal

/-! # Restriction of the original compactification graph ideal to its full boundary -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules

universe u
namespace AlgebraicGeometry.Scheme.Hom

variable {S C Y Z : Scheme.{u}} (q : C ⟶ S) (j : Y ⟶ C) (z : Z ⟶ Y)

/-- The unchanged graph of the open in its compactification. -/
def compactificationGraph : Y ⟶ pullback (j ≫ q) q :=
  pullback.lift (𝟙 Y) j (by simp)

/-- Restriction of the second factor to the specified entire boundary. -/
def graphBoundaryRestriction : pullback (j ≫ q) (z ≫ j ≫ q) ⟶ pullback (j ≫ q) q :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ z ≫ j)
    (by simpa only [Category.assoc] using
      (pullback.condition (f := j ≫ q) (g := z ≫ j ≫ q)))

/-- The graph of the original boundary inclusion in the retained open. -/
def restrictedBoundaryGraph : Z ⟶ pullback (j ≫ q) (z ≫ j ≫ q) :=
  pullback.lift z (𝟙 Z) (by simp)

/-- The ambient restriction is genuinely Cartesian. -/
theorem graphBoundaryRestriction_isPullback :
    IsPullback (graphBoundaryRestriction q j z) (pullback.snd (j ≫ q) (z ≫ j ≫ q))
      (pullback.snd (j ≫ q) q) (z ≫ j) where
  w := by simp [graphBoundaryRestriction]
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun t ↦ by
    have hc : (t.fst ≫ pullback.fst (j ≫ q) q) ≫ (j ≫ q) =
        t.snd ≫ (z ≫ j ≫ q) := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, t.condition]
      simp only [Category.assoc]
    refine ⟨pullback.lift (t.fst ≫ pullback.fst (j ≫ q) q) t.snd hc,
      ?_, pullback.lift_snd _ _ _, ?_⟩
    · apply pullback.hom_ext
      · simp [graphBoundaryRestriction]
      · simpa [graphBoundaryRestriction] using t.condition.symm
    · intro v hv hw
      apply pullback.hom_ext (f := j ≫ q) (g := z ≫ j ≫ q)
      · have he := congrArg (fun r ↦ r ≫ pullback.fst (j ≫ q) q) hv
        simpa [graphBoundaryRestriction] using he
      · simpa using hw)⟩

/-- Restriction of the original compactification graph is the literal boundary graph. -/
theorem compactificationGraph_boundary_isPullback [Mono j] :
    IsPullback z (restrictedBoundaryGraph q j z) (compactificationGraph q j)
      (graphBoundaryRestriction q j z) where
  w := by apply pullback.hom_ext <;> simp [restrictedBoundaryGraph,
    compactificationGraph, graphBoundaryRestriction]
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun t ↦ by
    have hf : t.fst = t.snd ≫ pullback.fst (j ≫ q) (z ≫ j ≫ q) := by
      have he := congrArg (fun r ↦ r ≫ pullback.fst (j ≫ q) q) t.condition
      simpa [compactificationGraph, graphBoundaryRestriction] using he
    have hz : (t.snd ≫ pullback.snd (j ≫ q) (z ≫ j ≫ q)) ≫ z = t.fst := by
      apply (cancel_mono j).mp
      have he := congrArg (fun r ↦ r ≫ pullback.snd (j ≫ q) q) t.condition
      simpa [compactificationGraph, graphBoundaryRestriction] using he.symm
    refine ⟨t.snd ≫ pullback.snd (j ≫ q) (z ≫ j ≫ q), hz, ?_, ?_⟩
    · apply pullback.hom_ext
      · simpa [restrictedBoundaryGraph] using hz.trans hf
      · simp [restrictedBoundaryGraph]
    · intro v _ hv
      have he := congrArg (fun r ↦ r ≫ pullback.snd (j ≫ q) (z ≫ j ≫ q)) hv
      simpa [restrictedBoundaryGraph] using he)⟩

/-- The actual graph ideal restricts isomorphically, using flatness only of the open.
No smoothness or regularity of the compactification is assumed. -/
theorem compactificationGraph_boundaryIdealMap_isIso [IsOpenImmersion j]
    [IsClosedImmersion (compactificationGraph q j)] :
    IsIso (idealPullbackMap (compactificationGraph q j) (restrictedBoundaryGraph q j z)
      (graphBoundaryRestriction q j z) z (compactificationGraph_boundary_isPullback q j z).w) := by
  have : Flat (compactificationGraph q j ≫ pullback.snd (j ≫ q) q) := by
    simpa [compactificationGraph] using (inferInstance : Flat j)
  exact flatQuotient_idealPullbackMap_isIso (pullback.snd (j ≫ q) q) (z ≫ j)
    (pullback.snd (j ≫ q) (z ≫ j ≫ q)) (graphBoundaryRestriction q j z)
    (compactificationGraph q j) (restrictedBoundaryGraph q j z) z _
    (graphBoundaryRestriction_isPullback q j z) (compactificationGraph_boundary_isPullback q j z)

end AlgebraicGeometry.Scheme.Hom
