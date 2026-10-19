/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Generators.Basic
public import Motivic.Aglib.AlgebraicGeometry.Cycles.IntegralImage
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Incidence schemes for finite-correspondence composition

For geometric generators `A` in `X ×[S] Y` and `B` in `Y ×[S] Z`, the
incidence scheme is the genuine fiber product of their support schemes over
`Y`. Its projection to `X` is finite. If `Z → S` is separated, its natural
map to `X ×[S] Z` is also finite, so its scheme-theoretic image has exactly
the set-theoretic image as support.

The source image is computed without assuming any object integral or
connected. In particular it equals the source component of `A` when the
image of `A` in `Y` lies in the source component of `B`.

This constructs support geometry only. The incidence scheme need not be
integral, reduced or flat. No intersection cycle or multiplicity is assigned,
and no claim about correspondence composition or its category laws is made.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme.Hom

variable {S X Y Z : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S}

/-- The target projection of the actual support of a finite correspondence. -/
noncomputable abbrev targetProjection (A : FiniteCorrespondenceGenerator f g) :
    A.scheme ⟶ Y :=
  A.inclusion ≫ pullback.snd f g

@[reassoc]
theorem projection_base (A : FiniteCorrespondenceGenerator f g) :
    A.projection ≫ f = A.targetProjection ≫ g := by
  exact Category.assoc _ _ _ |>.trans
    (congrArg (A.inclusion ≫ ·) (pullback.condition (f := f) (g := g)))

variable (A : FiniteCorrespondenceGenerator f g) (B : FiniteCorrespondenceGenerator g h)

/-- The genuine incidence scheme of the two geometric correspondence supports. -/
noncomputable abbrev incidence : Scheme.{u} :=
  pullback A.targetProjection B.projection

/-- The incidence projection to the first support. -/
noncomputable abbrev incidenceFst : A.incidence B ⟶ A.scheme :=
  pullback.fst A.targetProjection B.projection

/-- The incidence projection to the second support. -/
noncomputable abbrev incidenceSnd : A.incidence B ⟶ B.scheme :=
  pullback.snd A.targetProjection B.projection

@[reassoc]
theorem incidence_condition :
    A.incidenceFst B ≫ A.targetProjection = A.incidenceSnd B ≫ B.projection :=
  pullback.condition

instance : IsFinite (A.incidenceFst B) :=
  inferInstanceAs (IsFinite (pullback.fst A.targetProjection B.projection))

/-- The finite projection of the incidence scheme to the original source. -/
noncomputable abbrev incidenceSource : A.incidence B ⟶ X :=
  A.incidenceFst B ≫ A.projection

/-- The projection of the incidence scheme to the final target. -/
noncomputable abbrev incidenceTarget : A.incidence B ⟶ Z :=
  A.incidenceSnd B ≫ B.targetProjection

instance : IsFinite (A.incidenceSource B) :=
  inferInstanceAs (IsFinite (A.incidenceFst B ≫ A.projection))

@[reassoc]
theorem incidence_base : A.incidenceSource B ≫ f = A.incidenceTarget B ≫ h := by
  simp only [incidenceSource, incidenceTarget, Category.assoc]
  rw [A.projection_base, ← Category.assoc, A.incidence_condition B, Category.assoc,
    B.projection_base]
  simp only [targetProjection, Category.assoc]

/-- The actual projection of the incidence scheme to the source-target product. -/
noncomputable def incidenceMap : A.incidence B ⟶ pullback f h :=
  pullback.lift (A.incidenceSource B) (A.incidenceTarget B) (A.incidence_base B)

@[reassoc (attr := simp)]
theorem incidenceMap_fst : A.incidenceMap B ≫ pullback.fst f h = A.incidenceSource B :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem incidenceMap_snd : A.incidenceMap B ≫ pullback.snd f h = A.incidenceTarget B :=
  pullback.lift_snd _ _ _

/-- Separatedness of the final target makes the product projection finite on incidence. -/
instance [IsSeparated h] : IsFinite (A.incidenceMap B) := by
  have : IsFinite (A.incidenceMap B ≫ pullback.fst f h) := by
    simpa using (inferInstance : IsFinite (A.incidenceSource B))
  exact IsFinite.of_comp (A.incidenceMap B) (pullback.fst f h)

/-- The first projection meets exactly the part of `A` lying over the source support of `B`. -/
theorem range_incidenceFst :
    Set.range (A.incidenceFst B) = A.targetProjection ⁻¹' Set.range B.projection :=
  Scheme.Pullback.range_fst _ _

/-- The exact source image, retaining the source-component condition for disconnected objects. -/
theorem range_incidenceSource :
    Set.range (A.incidenceSource B) =
      A.projection '' (A.targetProjection ⁻¹' Set.range B.projection) := by
  change Set.range (A.projection ∘ A.incidenceFst B) = _
  rw [Set.range_comp, A.range_incidenceFst B]

/-- Every incidence point projects into the original source component of `A`. -/
theorem range_incidenceSource_subset :
    Set.range (A.incidenceSource B) ⊆ Set.range A.projection := by
  rintro x ⟨w, rfl⟩
  exact ⟨A.incidenceFst B w, rfl⟩

/-- Coverage of the intermediate image suffices to recover the whole first support. -/
theorem incidenceFst_surjective
    (hAB : Set.range A.targetProjection ⊆ Set.range B.projection) :
    Function.Surjective (A.incidenceFst B) := by
  apply Set.range_eq_univ.mp
  rw [A.range_incidenceFst B]
  exact Set.eq_univ_of_forall fun a => hAB ⟨a, rfl⟩

/-- Under intermediate coverage the source image is the source component of `A`. -/
theorem range_incidenceSource_of_coverage
    (hAB : Set.range A.targetProjection ⊆ Set.range B.projection) :
    Set.range (A.incidenceSource B) = Set.range A.projection := by
  change Set.range (A.projection ∘ A.incidenceFst B) = _
  exact (A.incidenceFst_surjective B hAB).range_comp A.projection

/-- The source-component condition holds for the whole incidence scheme under coverage. -/
theorem range_incidenceSource_mem_of_coverage
    (hAB : Set.range A.targetProjection ⊆ Set.range B.projection) :
    Set.range (A.incidenceSource B) ∈ irreducibleComponents X := by
  rw [A.range_incidenceSource_of_coverage B hAB]
  exact A.range_projection_mem

/-- An irreducible intermediate object gives the coverage condition automatically. -/
theorem range_incidenceSource_of_irreducible [IrreducibleSpace Y] :
    Set.range (A.incidenceSource B) = Set.range A.projection :=
  A.range_incidenceSource_of_coverage B (by
    rw [Set.range_eq_univ.mpr B.projection_surjective]
    exact Set.subset_univ _)

/-- The ideal defining the actual closed image in the source-target product. -/
noncomputable def incidenceImageIdeal : (pullback f h).IdealSheafData :=
  (A.incidenceMap B).ker

/-- The image ideal has literally the incidence map's image as its support. -/
theorem support_incidenceImageIdeal [IsSeparated h] :
    ((A.incidenceImageIdeal B).support : Set (pullback (C := Scheme) f h)) =
      Set.range (A.incidenceMap B) :=
  support_finiteImage (A.incidenceMap B)

/-- The source projection of the closed image has the same point image as incidence. -/
theorem source_image_support_incidenceImageIdeal [IsSeparated h] :
    pullback.fst f h '' ((A.incidenceImageIdeal B).support : Set (pullback (C := Scheme) f h)) =
      Set.range (A.incidenceSource B) := by
  rw [A.support_incidenceImageIdeal B, ← Set.range_comp]
  change Set.range (A.incidenceMap B ≫ pullback.fst f h) = _
  rw [A.incidenceMap_fst B]

end Motivic.FiniteCorrespondenceGenerator
