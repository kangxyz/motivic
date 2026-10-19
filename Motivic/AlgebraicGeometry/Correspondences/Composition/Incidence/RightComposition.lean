/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Incidence.TorCycle
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.RightFirstStageWeightedRemainingCoefficient

/-!
# The actual right Tor bracket is the canonical triple correspondence

The final source-target map on the whole right image incidence is finite. It
retains the original first support and the actual last-pair image target. Its
composites with the original triple incidence and every labelled remaining
component incidence are the literal original source-target maps. Pushing the
proved weighted remaining-cycle equality through this map therefore retains
every original G,H generic label, signed Tor coefficient, and incidence degree.

Additivity in the second argument identifies that same weighted sum with the
actual right generator bracket. Faithfulness of the integral-cycle representation
gives equality with the canonical triple Tor correspondence over an arbitrary
field. The nested right pairing follows by its proved value on generator cycles.
No flatness of F over Y is assumed. General associativity is not asserted here.

Prepared as a source-only candidate. Compilation and formal acceptance remain
separate checks, including for the imported pending weighted-cycle result.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

universe u

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme

open _root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme RightExteriorImageComponentGeometry

section Schemes

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  (F : FiniteCorrespondenceGenerator f g)
  (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)

/-- The whole right image incidence retains the actual last-pair image target. -/
abbrev rightImageIncidenceTarget : F.rightImageIncidence G H ⟶ W :=
  pullback.snd F.targetProjection ((G.incidenceMap H).imageι ≫ pullback.fst g i) ≫
    (G.incidenceMap H).imageι ≫ pullback.snd g i

/-- Both outer projections of the whole right image incidence lie over the same base. -/
@[reassoc] theorem rightImageIncidence_base :
    F.rightImageIncidenceSource G H ≫ f = F.rightImageIncidenceTarget G H ≫ i := by
  simp only [rightImageIncidenceSource, rightImageIncidenceTarget, Category.assoc]
  calc
    _ = pullback.fst F.targetProjection ((G.incidenceMap H).imageι ≫ pullback.fst g i) ≫
        F.targetProjection ≫ g :=
      congrArg
        (pullback.fst F.targetProjection ((G.incidenceMap H).imageι ≫ pullback.fst g i) ≫ ·)
        F.projection_base
    _ = pullback.snd F.targetProjection ((G.incidenceMap H).imageι ≫ pullback.fst g i) ≫
        (G.incidenceMap H).imageι ≫ pullback.fst g i ≫ g := by
      simpa only [Category.assoc] using
        congrArg (· ≫ g) (pullback.condition
          (f := F.targetProjection) (g := (G.incidenceMap H).imageι ≫ pullback.fst g i))
    _ = _ := by rw [pullback.condition]

/-- The genuine final source-target map of the full right image incidence. -/
def rightImageIncidenceMap : F.rightImageIncidence G H ⟶ pullback f i :=
  pullback.lift (F.rightImageIncidenceSource G H) (F.rightImageIncidenceTarget G H)
    (F.rightImageIncidence_base G H)

/-- The final map retains the original first-support finite source projection. -/
@[reassoc (attr := simp)] theorem rightImageIncidenceMap_fst :
    F.rightImageIncidenceMap G H ≫ pullback.fst f i = F.rightImageIncidenceSource G H :=
  pullback.lift_fst _ _ _

/-- The final map retains the original last-pair image target projection. -/
@[reassoc (attr := simp)] theorem rightImageIncidenceMap_snd :
    F.rightImageIncidenceMap G H ≫ pullback.snd f i = F.rightImageIncidenceTarget G H :=
  pullback.lift_snd _ _ _

/-- The final map from original triple incidence is literally unchanged. -/
@[reassoc (attr := simp)] theorem tripleToRightImageIncidence_map :
    F.tripleToRightImageIncidence G H ≫ F.rightImageIncidenceMap G H =
      F.tripleIncidenceMap G H := by
  apply pullback.hom_ext
  · simp only [Category.assoc, rightImageIncidenceMap_fst, tripleIncidenceMap_fst,
      tripleToRightImageIncidence_source]
  · simp only [Category.assoc, rightImageIncidenceMap_snd, tripleIncidenceMap_snd,
      rightImageIncidenceTarget, tripleToRightImageIncidence_snd_assoc,
      Scheme.Hom.toImage_imageι_assoc, incidenceMap_snd, incidenceTarget,
      tripleIncidenceToRightPair_snd_assoc, tripleIncidenceTarget]

end Schemes

section SmoothSite

variable (k : Type u) [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

/-- Every labelled remaining incidence has its literal original final map. -/
@[reassoc (attr := simp)] theorem remainingToImage_rightImageIncidenceMap
    (C : IntegralClosedSubscheme (G.incidenceMap H).image)
    (P : FiniteCorrespondenceGenerator Y.hom W.hom)
    (hC : (C.val.subschemeι ≫ (G.incidenceMap H).imageι).ker = P.val) :
    remainingToImage F G H C P hC ≫ F.rightImageIncidenceMap G H = F.incidenceMap P := by
  apply pullback.hom_ext
  · simp only [Category.assoc, rightImageIncidenceMap_fst, incidenceMap_fst,
      remainingToImage_source]
  · simp only [Category.assoc, rightImageIncidenceMap_snd, incidenceMap_snd,
      rightImageIncidenceTarget, remainingToImage_snd_assoc,
      ExteriorImageComponentGeometry.supportInImage_ambient_assoc, incidenceTarget,
      targetProjection]

/-- Finiteness follows from the actual source map and the separated final target. -/
instance isFinite_rightImageIncidenceMap : IsFinite (F.rightImageIncidenceMap G H) := by
  let := F.isFinite_rightImageIncidenceSource k G H
  let : IsFinite (F.rightImageIncidenceMap G H ≫ pullback.fst X.hom W.hom) := by
    simpa only [rightImageIncidenceMap_fst] using
      (inferInstance : IsFinite (F.rightImageIncidenceSource G H))
  exact IsFinite.of_comp (F.rightImageIncidenceMap G H) (pullback.fst X.hom W.hom)

/-- The actual right bracket expands in its second argument over all original
G,H incidence generics, retaining each signed Tor weight and original residue degree. -/
theorem incidenceTorPairing_right_eq_weightedRemaining :
    letI := IntegralCycle.genericPointFintype (G.incidence H)
    FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Y) (Z := W)
        F.cycle (G.incidenceTorCorrespondence (X := Y) (Y := Z) (Z := W) k H) =
      ∑ z : genericPoints (G.incidence H),
        (G.incidenceTorCoefficient (S := Spec (.of k)) H z *
          ((G.incidenceMap H).residueDegree z.1 : ℤ)) •
          F.incidenceTorCorrespondence k
            (G.smoothIncidenceComponentGenerator (X := Y) (Y := Z) (Z := W) k H z) := by
  classical
  let := IntegralCycle.genericPointFintype (G.incidence H)
  rw [incidenceTorCorrespondence, incidenceCycleAssembly_eq_sum]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro z _
  simp only [cycle, FiniteCorrespondence.incidenceTorPairing_single, one_mul]

/-- Pushing the right weighted remaining-cycle equality through the actual
final map gives the same canonical triple correspondence, with all labels retained. -/
theorem tripleTorCorrespondence_eq_rightWeightedRemaining :
    letI := IntegralCycle.genericPointFintype (G.incidence H)
    F.tripleTorCorrespondence k G H =
      ∑ z : genericPoints (G.incidence H),
        (G.incidenceTorCoefficient (S := Spec (.of k)) H z *
          ((G.incidenceMap H).residueDegree z.1 : ℤ)) •
          F.incidenceTorCorrespondence k
            (G.smoothIncidenceComponentGenerator (X := Y) (Y := Z) (Z := W) k H z) := by
  classical
  let := IntegralCycle.genericPointFintype (G.incidence H)
  apply FiniteCorrespondence.toIntegralCycle_injective
  rw [toIntegralCycle_tripleTorCorrespondence, map_sum]
  simp only [map_zsmul, toIntegralCycle_incidenceTorCorrespondence]
  have hpush := congrArg (IntegralCycle.finitePushforward (F.rightImageIncidenceMap G H))
    (F.rightImageIncidenceTorCycle_eq_weightedRemainingIncidence G H)
  simp only [map_sum, map_zsmul] at hpush
  have htriple :
      IntegralCycle.finitePushforward (F.rightImageIncidenceMap G H)
          (IntegralCycle.finitePushforward (F.tripleToRightImageIncidence G H)
            (F.tripleIncidenceTorCycle k G H)) =
        IntegralCycle.finitePushforward (F.tripleIncidenceMap G H)
          (F.tripleIncidenceTorCycle k G H) := by
    rw [← AddMonoidHom.comp_apply, ← IntegralCycle.finitePushforward_comp]
    simp only [tripleToRightImageIncidence_map]
  rw [htriple] at hpush
  refine hpush.trans ?_
  apply Finset.sum_congr rfl
  intro z _
  apply congrArg (fun c : IntegralCycle (pullback X.hom W.hom) =>
    (G.incidenceTorCoefficient (S := Spec (.of k)) H z *
      ((G.incidenceMap H).residueDegree z.1 : ℤ)) • c)
  rw [← AddMonoidHom.comp_apply, ← IntegralCycle.finitePushforward_comp]
  simp only [remainingToImage_rightImageIncidenceMap]

/-- The actual right generator bracket equals the canonical triple Tor correspondence. -/
theorem incidenceTorPairing_right_eq_tripleTorCorrespondence :
    FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Y) (Z := W)
      F.cycle (G.incidenceTorCorrespondence (X := Y) (Y := Z) (Z := W) k H) =
        F.tripleTorCorrespondence k G H := by
  classical
  let := IntegralCycle.genericPointFintype (G.incidence H)
  exact (F.incidenceTorPairing_right_eq_weightedRemaining k G H).trans
    (F.tripleTorCorrespondence_eq_rightWeightedRemaining k G H).symm

/-- Literally nesting the actual pairing on three generator cycles gives the
same canonical triple correspondence, with no caller-supplied comparison. -/
theorem incidenceTorPairing_right_cycle_eq_tripleTorCorrespondence :
    FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Y) (Z := W)
      F.cycle (FiniteCorrespondence.incidenceTorPairing k (X := Y) (Y := Z) (Z := W)
        G.cycle H.cycle) = F.tripleTorCorrespondence k G H := by
  rw [FiniteCorrespondence.incidenceTorPairing_cycle]
  exact F.incidenceTorPairing_right_eq_tripleTorCorrespondence k G H

/-- The faithful cycle of the actual right bracket is the genuine finite
pushforward of the same canonical triple-incidence total Tor cycle. -/
theorem toIntegralCycle_incidenceTorPairing_right :
    FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := W.hom)
        (FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Y) (Z := W)
          F.cycle (G.incidenceTorCorrespondence (X := Y) (Y := Z) (Z := W) k H)) =
      IntegralCycle.finitePushforward (F.tripleIncidenceMap G H)
        (F.tripleIncidenceTorCycle k G H) := by
  rw [incidenceTorPairing_right_eq_tripleTorCorrespondence,
    toIntegralCycle_tripleTorCorrespondence]

end SmoothSite

end Motivic.FiniteCorrespondenceGenerator
