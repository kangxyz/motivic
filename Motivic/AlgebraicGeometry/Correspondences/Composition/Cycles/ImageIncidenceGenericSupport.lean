/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Incidence.IntermediateImageFiber
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Incidence.RightImageFiber
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Associativity.TorCycle
public import Motivic.Aglib.AlgebraicGeometry.Cycles.GenericFinitePushforward

/-!
# Global generic support on both actual image-incidence schemes

Both image-incidence schemes have actual finite projections to the original
smooth source. Their composites with the literal maps from triple incidence
are the original triple source map. Its established component dominance,
followed by quasi-finite reflection, proves generic preservation in both
orders. This discharges the off-generic support obligation in collision-aware
finite pushforward and gives global generic-coefficient expressions for the
pushed canonical triple Tor cycle. Arbitrary signed coefficients, disconnected
smooth objects, nilpotents, and multiple source branches remain allowed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Hom

section Schemes

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  (F : FiniteCorrespondenceGenerator f g)
  (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)

/-- The left image-incidence source projection goes through the whole first-pair
image, with its actual scheme structure and original source projection. -/
abbrev leftImageIncidenceSource : F.leftImageIncidence G H ⟶ X :=
  pullback.fst ((F.incidenceMap G).imageι ≫ pullback.snd f h) H.projection ≫
    (F.incidenceMap G).imageι ≫ pullback.fst f h

/-- The right image-incidence source projection goes through the unchanged first
support and its actual finite projection. -/
abbrev rightImageIncidenceSource : F.rightImageIncidence G H ⟶ X :=
  pullback.fst F.targetProjection ((G.incidenceMap H).imageι ≫ pullback.fst g i) ≫
    F.projection

/-- The left source composite is literally the original triple source map. -/
@[reassoc] theorem tripleToLeftImageIncidence_source :
    F.tripleToLeftImageIncidence G H ≫ F.leftImageIncidenceSource G H =
      F.tripleIncidenceSource G H := by
  simp only [leftImageIncidenceSource, tripleToLeftImageIncidence_fst_assoc,
    Scheme.Hom.toImage_imageι_assoc, incidenceMap_fst, tripleIncidenceSource]

/-- The right source composite is literally the same original triple source map. -/
@[reassoc] theorem tripleToRightImageIncidence_source :
    F.tripleToRightImageIncidence G H ≫ F.rightImageIncidenceSource G H =
      F.tripleIncidenceSource G H := by
  simp only [rightImageIncidenceSource, tripleToRightImageIncidence_fst_assoc,
    tripleIncidenceSource, incidenceSource]

end Schemes

section SmoothSite

variable (k : Type u) [Field k]
  {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

/-- Left image incidence is finite over X: first base change the finite third
support, then use the actual finite first-pair image projection. -/
theorem isFinite_leftImageIncidenceSource :
    IsFinite (F.leftImageIncidenceSource G H) := by
  have := F.isFinite_incidenceImageProjection k G
  exact inferInstanceAs (IsFinite
    (pullback.fst ((F.incidenceMap G).imageι ≫ pullback.snd X.hom Z.hom) H.projection ≫
      ((F.incidenceMap G).imageι ≫ pullback.fst X.hom Z.hom)))

/-- Right image incidence is finite over X: base change the finite source
projection of the second-pair whole image, then use F's original projection. -/
theorem isFinite_rightImageIncidenceSource :
    IsFinite (F.rightImageIncidenceSource G H) := by
  have := G.isFinite_incidenceImageProjection k H
  exact inferInstanceAs (IsFinite
    (pullback.fst F.targetProjection
      ((G.incidenceMap H).imageι ≫ pullback.fst Y.hom W.hom) ≫ F.projection))

/-- The whole left image incidence is Noetherian via its actual finite map to X. -/
instance isNoetherian_smoothLeftImageIncidence : IsNoetherian (F.leftImageIncidence G H) := by
  have := F.isFinite_leftImageIncidenceSource k G H
  have : IsNoetherian ((𝟭 Scheme).obj X.left) :=
    inferInstanceAs (IsNoetherian X.left)
  exact isNoetherian_of_finiteType (F.leftImageIncidenceSource G H)

/-- The whole right image incidence is Noetherian via its actual finite map to X. -/
instance isNoetherian_smoothRightImageIncidence : IsNoetherian (F.rightImageIncidence G H) := by
  have := F.isFinite_rightImageIncidenceSource k G H
  have : IsNoetherian ((𝟭 Scheme).obj X.left) :=
    inferInstanceAs (IsNoetherian X.left)
  exact isNoetherian_of_finiteType (F.rightImageIncidenceSource G H)

/-- Every genuine triple generic maps to a left image-incidence generic because
its projection to X is generic and the intervening map to X is finite. -/
theorem tripleToLeftImageIncidence_mem_genericPoints
    (w : F.tripleIncidence G H) (hw : w ∈ genericPoints (F.tripleIncidence G H)) :
    F.tripleToLeftImageIncidence G H w ∈ genericPoints (F.leftImageIncidence G H) := by
  have := F.isFinite_leftImageIncidenceSource k G H
  apply mem_genericPoints_of_image_generic (F.leftImageIncidenceSource G H)
  change (F.tripleToLeftImageIncidence G H ≫ F.leftImageIncidenceSource G H) w ∈ _
  rw [F.tripleToLeftImageIncidence_source G H]
  exact F.tripleIncidenceSource_mem_genericPoints k G H w hw

/-- Every genuine triple generic maps to a right image-incidence generic by the
same actual finite-to-X reflection, without a finite right-pair projection. -/
theorem tripleToRightImageIncidence_mem_genericPoints
    (w : F.tripleIncidence G H) (hw : w ∈ genericPoints (F.tripleIncidence G H)) :
    F.tripleToRightImageIncidence G H w ∈ genericPoints (F.rightImageIncidence G H) := by
  have := F.isFinite_rightImageIncidenceSource k G H
  apply mem_genericPoints_of_image_generic (F.rightImageIncidenceSource G H)
  change (F.tripleToRightImageIncidence G H ≫ F.rightImageIncidenceSource G H) w ∈ _
  rw [F.tripleToRightImageIncidence_source G H]
  exact F.tripleIncidenceSource_mem_genericPoints k G H w hw

/-- All signed source-generic contributions vanish at a nongeneric left target. -/
theorem leftImageIncidence_genericPushforwardCoefficient_eq_zero_of_not_generic
    (c : genericPoints (F.tripleIncidence G H) → ℤ)
    (y : F.leftImageIncidence G H) (hy : y ∉ genericPoints (F.leftImageIncidence G H)) :
    IntegralCycle.genericPushforwardCoefficient (F.tripleToLeftImageIncidence G H) c y = 0 :=
  IntegralCycle.genericPushforwardCoefficient_eq_zero_of_not_generic
    (F.tripleToLeftImageIncidence G H)
    (fun w => F.tripleToLeftImageIncidence_mem_genericPoints k G H w.1 w.2) c y hy

/-- All signed source-generic contributions vanish at a nongeneric right target. -/
theorem rightImageIncidence_genericPushforwardCoefficient_eq_zero_of_not_generic
    (c : genericPoints (F.tripleIncidence G H) → ℤ)
    (y : F.rightImageIncidence G H) (hy : y ∉ genericPoints (F.rightImageIncidence G H)) :
    IntegralCycle.genericPushforwardCoefficient (F.tripleToRightImageIncidence G H) c y = 0 :=
  IntegralCycle.genericPushforwardCoefficient_eq_zero_of_not_generic
    (F.tripleToRightImageIncidence G H)
    (fun w => F.tripleToRightImageIncidence_mem_genericPoints k G H w.1 w.2) c y hy

/-- Actual left pushforward is globally a generic-coefficient cycle. Its
coefficients sum every actual colliding source with its own residue degree. -/
theorem finitePushforward_tripleToLeftImageIncidence_ofGenericCoefficients
    (c : genericPoints (F.tripleIncidence G H) → ℤ) :
    IntegralCycle.finitePushforward (F.tripleToLeftImageIncidence G H)
        (IntegralCycle.ofGenericCoefficients (F.tripleIncidence G H) c) =
      IntegralCycle.ofGenericCoefficients (F.leftImageIncidence G H)
        (fun y => IntegralCycle.genericPushforwardCoefficient
          (F.tripleToLeftImageIncidence G H) c y.1) :=
  IntegralCycle.finitePushforward_ofGenericCoefficients
    (F.tripleToLeftImageIncidence G H)
    (fun w => F.tripleToLeftImageIncidence_mem_genericPoints k G H w.1 w.2) c

/-- Actual right pushforward is globally a generic-coefficient cycle, with no
injectivity or one-branch assumption on the generic point map. -/
theorem finitePushforward_tripleToRightImageIncidence_ofGenericCoefficients
    (c : genericPoints (F.tripleIncidence G H) → ℤ) :
    IntegralCycle.finitePushforward (F.tripleToRightImageIncidence G H)
        (IntegralCycle.ofGenericCoefficients (F.tripleIncidence G H) c) =
      IntegralCycle.ofGenericCoefficients (F.rightImageIncidence G H)
        (fun y => IntegralCycle.genericPushforwardCoefficient
          (F.tripleToRightImageIncidence G H) c y.1) :=
  IntegralCycle.finitePushforward_ofGenericCoefficients
    (F.tripleToRightImageIncidence G H)
    (fun w => F.tripleToRightImageIncidence_mem_genericPoints k G H w.1 w.2) c

/-- The actual pushed canonical triple Tor cycle has zero coefficient off the
left image-incidence generic support. -/
theorem leftImageIncidenceTorCycleCoefficient_eq_zero_of_not_generic
    (y : F.leftImageIncidence G H) (hy : y ∉ genericPoints (F.leftImageIncidence G H)) :
    IntegralCycle.toPoints
        (IntegralCycle.finitePushforward (F.tripleToLeftImageIncidence G H)
          (F.tripleIncidenceTorCycle k G H)) y = 0 := by
  rw [tripleIncidenceTorCycle,
    IntegralCycle.toPoints_finitePushforward_ofGenericCoefficients_apply]
  exact F.leftImageIncidence_genericPushforwardCoefficient_eq_zero_of_not_generic k G H _ y hy

/-- The actual pushed canonical triple Tor cycle has zero coefficient off the
right image-incidence generic support. -/
theorem rightImageIncidenceTorCycleCoefficient_eq_zero_of_not_generic
    (y : F.rightImageIncidence G H) (hy : y ∉ genericPoints (F.rightImageIncidence G H)) :
    IntegralCycle.toPoints
        (IntegralCycle.finitePushforward (F.tripleToRightImageIncidence G H)
          (F.tripleIncidenceTorCycle k G H)) y = 0 := by
  rw [tripleIncidenceTorCycle,
    IntegralCycle.toPoints_finitePushforward_ofGenericCoefficients_apply]
  exact F.rightImageIncidence_genericPushforwardCoefficient_eq_zero_of_not_generic k G H _ y hy

/-- The canonical triple Tor pushforward on left image incidence is globally
realized by its actual generic coefficients, including all collision weights. -/
theorem finitePushforward_tripleTorCycle_leftImageIncidence :
    IntegralCycle.finitePushforward (F.tripleToLeftImageIncidence G H)
        (F.tripleIncidenceTorCycle k G H) =
      IntegralCycle.ofGenericCoefficients (F.leftImageIncidence G H)
        (fun y => IntegralCycle.genericPushforwardCoefficient
          (F.tripleToLeftImageIncidence G H)
          (F.tripleIncidenceTorCoefficient (S := Spec (.of k)) G H) y.1) :=
  F.finitePushforward_tripleToLeftImageIncidence_ofGenericCoefficients k G H _

/-- The canonical triple Tor pushforward on right image incidence is globally
realized by its actual generic coefficients, without dropping nongeneric checks. -/
theorem finitePushforward_tripleTorCycle_rightImageIncidence :
    IntegralCycle.finitePushforward (F.tripleToRightImageIncidence G H)
        (F.tripleIncidenceTorCycle k G H) =
      IntegralCycle.ofGenericCoefficients (F.rightImageIncidence G H)
        (fun y => IntegralCycle.genericPushforwardCoefficient
          (F.tripleToRightImageIncidence G H)
          (F.tripleIncidenceTorCoefficient (S := Spec (.of k)) G H) y.1) :=
  F.finitePushforward_tripleToRightImageIncidence_ofGenericCoefficients k G H _

end SmoothSite

end Motivic.FiniteCorrespondenceGenerator
