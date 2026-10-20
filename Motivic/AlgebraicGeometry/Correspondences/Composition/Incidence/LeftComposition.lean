/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Incidence.TorCycle
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.FirstStageWeightedRemainingCoefficient

/-!
# The actual left Tor bracket is the canonical triple correspondence

The final source-target map on the whole left image incidence is finite. Its
composites with the original triple incidence and every labelled remaining
component incidence are the literal original source-target maps. Pushing the
proved weighted remaining-cycle equality through this map therefore retains
every original generic label, signed Tor coefficient, and incidence degree.

Biadditivity identifies that same weighted sum with the actual left generator
bracket. Faithfulness of the integral-cycle representation gives equality with
the canonical triple Tor correspondence over an arbitrary field. The nested
left pairing follows by its proved value on generator cycles. The right
bracket and general associativity are not asserted here.

Validation scope and recorded evidence are maintained in
`docs/VERIFICATION.md`.
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

open _root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme ExteriorImageComponentGeometry

section Schemes

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  (F : FiniteCorrespondenceGenerator f g)
  (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)

/-- The whole left image incidence retains the original third-support target. -/
abbrev leftImageIncidenceTarget : F.leftImageIncidence G H ⟶ W :=
  pullback.snd ((F.incidenceMap G).imageι ≫ pullback.snd f h) H.projection ≫
    H.targetProjection

/-- Both outer projections of the whole image incidence lie over the same base. -/
@[reassoc] theorem leftImageIncidence_base :
    F.leftImageIncidenceSource G H ≫ f = F.leftImageIncidenceTarget G H ≫ i := by
  simp only [leftImageIncidenceSource, leftImageIncidenceTarget, Category.assoc]
  calc
    _ = pullback.fst ((F.incidenceMap G).imageι ≫ pullback.snd f h) H.projection ≫
        (F.incidenceMap G).imageι ≫ pullback.snd f h ≫ h := by
      rw [pullback.condition]
    _ = pullback.snd ((F.incidenceMap G).imageι ≫ pullback.snd f h) H.projection ≫
        H.projection ≫ h := by
      simpa only [Category.assoc] using
        congrArg (· ≫ h) (pullback.condition
          (f := (F.incidenceMap G).imageι ≫ pullback.snd f h) (g := H.projection))
    _ = _ := congrArg
      (pullback.snd ((F.incidenceMap G).imageι ≫ pullback.snd f h) H.projection ≫ ·)
      H.projection_base

/-- The genuine final source-target map of the full left image incidence. -/
def leftImageIncidenceMap : F.leftImageIncidence G H ⟶ pullback f i :=
  pullback.lift (F.leftImageIncidenceSource G H) (F.leftImageIncidenceTarget G H)
    (F.leftImageIncidence_base G H)

/-- The final map retains the finite original-source projection. -/
@[reassoc (attr := simp)] theorem leftImageIncidenceMap_fst :
    F.leftImageIncidenceMap G H ≫ pullback.fst f i = F.leftImageIncidenceSource G H :=
  pullback.lift_fst _ _ _

/-- The final map retains the original third-support target projection. -/
@[reassoc (attr := simp)] theorem leftImageIncidenceMap_snd :
    F.leftImageIncidenceMap G H ≫ pullback.snd f i = F.leftImageIncidenceTarget G H :=
  pullback.lift_snd _ _ _

/-- The final map from original triple incidence is literally unchanged. -/
@[reassoc (attr := simp)] theorem tripleToLeftImageIncidence_map :
    F.tripleToLeftImageIncidence G H ≫ F.leftImageIncidenceMap G H =
      F.tripleIncidenceMap G H := by
  apply pullback.hom_ext
  · simp only [Category.assoc, leftImageIncidenceMap_fst, tripleIncidenceMap_fst,
      tripleToLeftImageIncidence_source]
  · simp only [Category.assoc, leftImageIncidenceMap_snd, tripleIncidenceMap_snd,
      leftImageIncidenceTarget, tripleToLeftImageIncidence_snd_assoc, tripleIncidenceTarget]

/-- Every labelled remaining incidence has its literal original final map. -/
@[reassoc (attr := simp)] theorem remainingToImage_leftImageIncidenceMap
    (C : IntegralClosedSubscheme (F.incidenceMap G).image)
    (P : FiniteCorrespondenceGenerator f h)
    (hC : (C.val.subschemeι ≫ (F.incidenceMap G).imageι).ker = P.val) :
    remainingToImage F G H C P hC ≫ F.leftImageIncidenceMap G H = P.incidenceMap H := by
  apply pullback.hom_ext
  · simp only [Category.assoc, leftImageIncidenceMap_fst, incidenceMap_fst,
      remainingToImage_source]
  · simp only [Category.assoc, leftImageIncidenceMap_snd, incidenceMap_snd,
      leftImageIncidenceTarget, remainingToImage_snd_assoc, incidenceTarget]

end Schemes

section SmoothSite

variable (k : Type u) [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

/-- Finiteness follows from the actual source map and the separated final target. -/
instance isFinite_leftImageIncidenceMap : IsFinite (F.leftImageIncidenceMap G H) := by
  let := F.isFinite_leftImageIncidenceSource k G H
  let : IsFinite (F.leftImageIncidenceMap G H ≫ pullback.fst X.hom W.hom) := by
    simpa only [leftImageIncidenceMap_fst] using
      (inferInstance : IsFinite (F.leftImageIncidenceSource G H))
  exact IsFinite.of_comp (F.leftImageIncidenceMap G H) (pullback.fst X.hom W.hom)

/-- The actual left bracket expands over all original pair-incidence generics,
with each original signed Tor coefficient and original residue degree intact. -/
theorem incidenceTorPairing_left_eq_weightedRemaining :
    letI := IntegralCycle.genericPointFintype (F.incidence G)
    FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Z) (Z := W)
        (F.incidenceTorCorrespondence k G) H.cycle =
      ∑ z : genericPoints (F.incidence G),
        (F.incidenceTorCoefficient (S := Spec (.of k)) G z *
          ((F.incidenceMap G).residueDegree z.1 : ℤ)) •
          (F.smoothIncidenceComponentGenerator k G z).incidenceTorCorrespondence k H := by
  classical
  let := IntegralCycle.genericPointFintype (F.incidence G)
  rw [incidenceTorCorrespondence, incidenceCycleAssembly_eq_sum]
  change (FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Z) (Z := W)).flip
    H.cycle (∑ z : genericPoints (F.incidence G),
      Finsupp.single (F.smoothIncidenceComponentGenerator k G z)
        (F.incidenceTorCoefficient (S := Spec (.of k)) G z *
          ((F.incidenceMap G).residueDegree z.1 : ℤ))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro z _
  simp only [AddMonoidHom.flip_apply, cycle,
    FiniteCorrespondence.incidenceTorPairing_single, mul_one]

/-- Pushing the weighted remaining-cycle equality through the actual final map
gives the canonical triple correspondence, without merging colliding labels. -/
theorem tripleTorCorrespondence_eq_weightedRemaining :
    letI := IntegralCycle.genericPointFintype (F.incidence G)
    F.tripleTorCorrespondence k G H =
      ∑ z : genericPoints (F.incidence G),
        (F.incidenceTorCoefficient (S := Spec (.of k)) G z *
          ((F.incidenceMap G).residueDegree z.1 : ℤ)) •
          (F.smoothIncidenceComponentGenerator k G z).incidenceTorCorrespondence k H := by
  classical
  let := IntegralCycle.genericPointFintype (F.incidence G)
  apply FiniteCorrespondence.toIntegralCycle_injective
  rw [toIntegralCycle_tripleTorCorrespondence, map_sum]
  simp only [map_zsmul, toIntegralCycle_incidenceTorCorrespondence]
  have hpush := congrArg (IntegralCycle.finitePushforward (F.leftImageIncidenceMap G H))
    (F.leftImageIncidenceTorCycle_eq_weightedRemainingIncidence G H)
  simp only [map_sum, map_zsmul] at hpush
  have htriple :
      IntegralCycle.finitePushforward (F.leftImageIncidenceMap G H)
          (IntegralCycle.finitePushforward (F.tripleToLeftImageIncidence G H)
            (F.tripleIncidenceTorCycle k G H)) =
        IntegralCycle.finitePushforward (F.tripleIncidenceMap G H)
          (F.tripleIncidenceTorCycle k G H) := by
    rw [← AddMonoidHom.comp_apply, ← IntegralCycle.finitePushforward_comp]
    simp only [tripleToLeftImageIncidence_map]
  rw [htriple] at hpush
  refine hpush.trans ?_
  apply Finset.sum_congr rfl
  intro z _
  apply congrArg (fun c : IntegralCycle (pullback X.hom W.hom) =>
    (F.incidenceTorCoefficient (S := Spec (.of k)) G z *
      ((F.incidenceMap G).residueDegree z.1 : ℤ)) • c)
  rw [← AddMonoidHom.comp_apply, ← IntegralCycle.finitePushforward_comp]
  simp only [remainingToImage_leftImageIncidenceMap]

/-- The actual left generator bracket equals the canonical triple Tor correspondence. -/
theorem incidenceTorPairing_left_eq_tripleTorCorrespondence :
    FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Z) (Z := W)
      (F.incidenceTorCorrespondence k G) H.cycle = F.tripleTorCorrespondence k G H := by
  classical
  let := IntegralCycle.genericPointFintype (F.incidence G)
  exact (F.incidenceTorPairing_left_eq_weightedRemaining k G H).trans
    (F.tripleTorCorrespondence_eq_weightedRemaining k G H).symm

/-- Literally nesting the actual pairing on three generator cycles gives the
same canonical triple correspondence, with no caller-supplied comparison. -/
theorem incidenceTorPairing_left_cycle_eq_tripleTorCorrespondence :
    FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Z) (Z := W)
      (FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Y) (Z := Z)
        F.cycle G.cycle) H.cycle = F.tripleTorCorrespondence k G H := by
  rw [FiniteCorrespondence.incidenceTorPairing_cycle]
  exact F.incidenceTorPairing_left_eq_tripleTorCorrespondence k G H

/-- The faithful cycle of the actual left bracket is the genuine finite
pushforward of the canonical triple-incidence total Tor cycle. -/
theorem toIntegralCycle_incidenceTorPairing_left :
    FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := W.hom)
        (FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Z) (Z := W)
          (F.incidenceTorCorrespondence k G) H.cycle) =
      IntegralCycle.finitePushforward (F.tripleIncidenceMap G H)
        (F.tripleIncidenceTorCycle k G H) := by
  rw [incidenceTorPairing_left_eq_tripleTorCorrespondence,
    toIntegralCycle_tripleTorCorrespondence]

end SmoothSite

end Motivic.FiniteCorrespondenceGenerator
