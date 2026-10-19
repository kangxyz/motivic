module
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.ProjectiveLine.CoordinateSection.Basic
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Charts.BaseChange
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.InfinityBoundaryIdeal
/-! # Canonical graph-ideal unit on the whole relative missing-neighborhood boundary -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable {R A : Type u} [CommRing R] [CommRing A]

@[reassoc]
lemma coordinateSection_map (z : Polynomial R →+* A) :
    coordinateSection A (z Polynomial.X) ≫
        ProjectiveSpace.map (z.comp Polynomial.C) (ULift.{u} (Fin 2)) =
      Spec.map (CommRingCat.ofHom z) ≫ chart R ⟨0⟩ := by
  rw [coordinateSection, Category.assoc, chart_map, ← Category.assoc, ← Spec.map_comp]
  congr 1
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro r
    simp
  · simp

variable (V : (Spec (.of (Polynomial R))).Opens) (z : Polynomial R →+* A)
  [IsOpenImmersion (Spec.map (CommRingCat.ofHom z))]

/-- The original missing-neighborhood scheme, pulled to the actual relative projective line. -/
abbrev missingBoundaryMap := pullback.fst
  (ProjectiveSpace.map (z.comp Polynomial.C) (ULift.{u} (Fin 2)))
  (neighborhoodBoundaryInclusion R V)

omit [IsOpenImmersion (Spec.map (CommRingCat.ofHom z))] in
lemma coordinateSection_missing_isEmpty
    (hz : Set.range (Spec.map (CommRingCat.ofHom z)) ⊆ V) :
    IsEmpty (pullback (C := Scheme) (coordinateSection A (z Polynomial.X))
      (missingBoundaryMap V z)) := by
  apply Scheme.isEmpty_pullback
  apply Set.disjoint_left.mpr
  rintro x ⟨y, rfl⟩ ⟨b, hb⟩
  let m := ProjectiveSpace.map (z.comp Polynomial.C) (ULift.{u} (Fin 2))
  have hy : m (coordinateSection A (z Polynomial.X) y) ∈ projectiveNeighborhood R V := by
    change (coordinateSection A (z Polynomial.X) ≫ m) y ∈ _
    rw [coordinateSection_map]
    exact ⟨_, hz ⟨y, rfl⟩, rfl⟩
  have hb' : m (missingBoundaryMap V z b) ∈
      Set.range (neighborhoodBoundaryInclusion R V) := by
    refine ⟨pullback.snd m (neighborhoodBoundaryInclusion R V) b, ?_⟩
    exact (congrArg (fun f => f b) (pullback.condition (f := m)
      (g := neighborhoodBoundaryInclusion R V))).symm
  rw [range_neighborhoodBoundaryInclusion] at hb'
  exact hb' (congrArg m hb ▸ hy)

/-- The actual original graph inclusion is invertible on the whole missing boundary. -/
theorem coordinateSection_missing_idealInclusion_isIso
    (hz : Set.range (Spec.map (CommRingCat.ofHom z)) ⊆ V) :
    IsIso (Scheme.Modules.Hom.pullbackToUnit
      (Scheme.Hom.idealInclusion (coordinateSection A (z Polynomial.X)))
      (missingBoundaryMap V z)) := by
  let m := ProjectiveSpace.map (z.comp Polynomial.C) (ULift.{u} (Fin 2))
  let d := neighborhoodBoundaryInclusion R V
  let b := missingBoundaryMap V z
  let i := coordinateSection A (z Polynomial.X)
  let i' := pullback.snd i b
  let a := pullback.fst i b
  have : IsEmpty (pullback (C := Scheme) i b) := coordinateSection_missing_isEmpty V z hz
  have : IsIso (Scheme.Hom.idealInclusion i') :=
    Scheme.Hom.idealInclusion_isIso_of_isEmpty i'
  have : Flat (i ≫ m) := by
    dsimp only [i, m]
    rw [coordinateSection_map]
    infer_instance
  have hv : IsIso (Scheme.Hom.idealPullbackMap i i' b a pullback.condition) :=
    Scheme.Hom.flatQuotient_idealPullbackMap_isIso m d (pullback.snd _ _) b i i' a
      pullback.condition (IsPullback.of_hasPullback _ _) (IsPullback.of_hasPullback _ _)
  change IsIso ((Scheme.Modules.pullback b).map (Scheme.Hom.idealInclusion i) ≫
    SheafOfModules.pullbackObjUnitToUnit b.toRingCatSheafHom)
  rw [← Scheme.Hom.idealPullbackMap_inclusion i i' b a pullback.condition]
  infer_instance
/-- The inverse original inclusion gives the prescribed ideal frame, not an arbitrary unit. -/
def coordinateSection_missing_idealIso
    (hz : Set.range (Spec.map (CommRingCat.ofHom z)) ⊆ V) :
    SheafOfModules.unit (pullback
      (ProjectiveSpace.map (z.comp Polynomial.C) (ULift.{u} (Fin 2)))
      (neighborhoodBoundaryInclusion R V)).ringCatSheaf ≅
    (Scheme.Modules.pullback (missingBoundaryMap V z)).obj
      (coordinateIdealLineBundle A (z Polynomial.X)).val := by
  have := coordinateSection_missing_idealInclusion_isIso V z hz
  exact (asIso (Scheme.Modules.Hom.pullbackToUnit
    (Scheme.Hom.idealInclusion (coordinateSection A (z Polynomial.X)))
    (missingBoundaryMap V z))).symm

@[reassoc (attr := simp)]
lemma coordinateSection_missing_idealIso_inclusion
    (hz : Set.range (Spec.map (CommRingCat.ofHom z)) ⊆ V) :
    (coordinateSection_missing_idealIso V z hz).hom ≫
      Scheme.Modules.Hom.pullbackToUnit
        (Scheme.Hom.idealInclusion (coordinateSection A (z Polynomial.X)))
        (missingBoundaryMap V z) = 𝟙 _ := by
  have := coordinateSection_missing_idealInclusion_isIso V z hz
  exact Iso.inv_hom_id (asIso _)
end AlgebraicGeometry.RelativeProjectiveLine
