/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.FullBoundaryTrivialization
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.DisjointClosedImmersion

/-! # The closed full boundary in the original relative product -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Hom
variable {S C Y D Z : Scheme.{u}} (q : C ⟶ S) (j : Y ⟶ C)
  (d : D ⟶ C) (s : Z ⟶ Y)

/-- The full relative boundary, without changing either component scheme structure. -/
def fullBoundaryProductMap :=
  coprod.desc (infinityProductMap q j d) (graphBoundaryRestriction q j s)

/-- Disjointness on C implies disjointness in the original relative product. -/
theorem fullBoundaryProduct_disjoint (h : Disjoint (Set.range j) (Set.range d)) :
    Disjoint (Set.range (infinityProductMap q j d))
      (Set.range (graphBoundaryRestriction q j s)) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨a, rfl⟩ ⟨b, hb⟩
  have he := congrArg (fun x => (pullback.snd (j ≫ q) q) x) hb
  have ha := congrArg
    (fun v : pullback (pullback.snd (j ≫ q) q) d ⟶ C => v a)
    (pullback.condition (f := pullback.snd (j ≫ q) q) (g := d))
  have hb' : (pullback.snd (j ≫ q) q) (graphBoundaryRestriction q j s b) =
      j (s (pullback.snd (j ≫ q) (s ≫ j ≫ q) b)) := by
    change (graphBoundaryRestriction q j s ≫ pullback.snd (j ≫ q) q) b = _
    rw [graphBoundaryRestriction, pullback.lift_snd]
    rfl
  exact Set.disjoint_iff_forall_ne.mp h ⟨_, rfl⟩ ⟨_, rfl⟩
    (hb'.symm.trans (he.trans ha))

/-- The scheme-theoretic union is an actual closed immersion into Y × C. -/
theorem fullBoundaryProduct_isClosedImmersion [IsClosedImmersion d]
    [IsClosedImmersion (s ≫ j)] (h : Disjoint (Set.range j) (Set.range d)) :
    IsClosedImmersion (fullBoundaryProductMap q j d s) := by
  have : IsClosedImmersion (graphBoundaryRestriction q j s) :=
    MorphismProperty.of_isPullback (graphBoundaryRestriction_isPullback q j s).flip inferInstance
  exact isClosedImmersion_coprod_desc _ _ (fullBoundaryProduct_disjoint q j d s h)

/-- The infinity product projection is finite by actual pullback of the finite boundary. -/
theorem infinityProduct_finite [IsFinite (d ≫ q)] :
    IsFinite (infinityProductMap q j d ≫ pullback.fst (j ≫ q) q) := by
  have H := (IsPullback.of_hasPullback (pullback.snd (j ≫ q) q) d).paste_horiz
    (IsPullback.of_hasPullback (j ≫ q) q)
  exact MorphismProperty.of_isPullback H.flip inferInstance

/-- Finiteness of both original components gives finiteness of the whole relative boundary. -/
theorem fullBoundaryProduct_finite [IsFinite (d ≫ q)] [IsFinite (s ≫ j ≫ q)] :
    IsFinite (fullBoundaryProductMap q j d s ≫ pullback.fst (j ≫ q) q) := by
  have := infinityProduct_finite q j d
  have hz : graphBoundaryRestriction q j s ≫ pullback.fst (j ≫ q) q =
      pullback.fst (j ≫ q) (s ≫ j ≫ q) := by
    exact pullback.lift_fst _ _ _
  have : IsFinite (graphBoundaryRestriction q j s ≫ pullback.fst (j ≫ q) q) := by
    rw [hz]
    infer_instance
  dsimp only [fullBoundaryProductMap]
  rw [coprod.desc_comp]
  infer_instance

end AlgebraicGeometry.Scheme.Hom
