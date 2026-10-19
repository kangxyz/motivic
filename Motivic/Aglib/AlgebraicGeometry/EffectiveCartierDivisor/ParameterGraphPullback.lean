/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.FlatChartIdealCoordinate

/-! # The original target graph under change of parameter

Changing the parameter pulls back the original graph scheme, not merely its
support. The resulting flat ideal comparison transports the same target frame
and its inclusion, without choosing a new graph generator.


Intended upstream module: `Aglib.AlgebraicGeometry.EffectiveCartierDivisor.ParameterGraphPullback`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.ParameterGraphChartFrame`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Hom

variable {S C X Y : Scheme.{u}} (q : C ⟶ S) (j : X ⟶ C) (p : Y ⟶ X)

/-- The actual first-factor change of parameter, keeping the compact curve fixed. -/
def parameterProductMap : pullback ((p ≫ j) ≫ q) q ⟶ pullback (j ≫ q) q :=
  pullback.lift (pullback.fst _ _ ≫ p) (pullback.snd _ _) (by
    simpa only [Category.assoc] using
      (pullback.condition (f := (p ≫ j) ≫ q) (g := q)))

@[reassoc (attr := simp)] theorem parameterProductMap_fst :
    parameterProductMap q j p ≫ pullback.fst (j ≫ q) q =
      pullback.fst ((p ≫ j) ≫ q) q ≫ p := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem parameterProductMap_snd :
    parameterProductMap q j p ≫ pullback.snd (j ≫ q) q =
      pullback.snd ((p ≫ j) ≫ q) q := pullback.lift_snd _ _ _

/-- The parameter product map is the base change of the ORIGINAL parameter map. -/
theorem parameterProductMap_isPullback :
    IsPullback (pullback.fst ((p ≫ j) ≫ q) q) (parameterProductMap q j p)
      p (pullback.fst (j ≫ q) q) where
  w := by simp
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun c => by
    have hc : c.fst ≫ ((p ≫ j) ≫ q) =
        (c.snd ≫ pullback.snd (j ≫ q) q) ≫ q := by
      simpa only [Category.assoc, pullback.condition] using
        congrArg (fun l => l ≫ (j ≫ q)) c.condition
    refine ⟨pullback.lift c.fst (c.snd ≫ pullback.snd (j ≫ q) q) hc,
      pullback.lift_fst _ _ _, ?_, ?_⟩
    · apply pullback.hom_ext
      · simpa [parameterProductMap] using c.condition
      · simp [parameterProductMap]
    · intro v hv hw
      apply pullback.hom_ext (f := (p ≫ j) ≫ q) (g := q)
      · simpa only [PullbackCone.mk_fst, pullback.lift_fst] using hv
      · have he := congrArg (fun l => l ≫ pullback.snd (j ≫ q) q) hw
        simpa [parameterProductMap] using he)⟩

instance [Flat p] : Flat (parameterProductMap q j p) :=
  MorphismProperty.of_isPullback (parameterProductMap_isPullback q j p) inferInstance

/-- The literal original graph square, including nonreduced graph restrictions. -/
theorem parameterGraph_isPullback :
    IsPullback p (compactificationGraph q (p ≫ j))
      (compactificationGraph q j) (parameterProductMap q j p) := by
  have ho : IsPullback p
      (compactificationGraph q (p ≫ j) ≫ pullback.fst _ _)
      (compactificationGraph q j ≫ pullback.fst _ _) p := by
    simp only [compactificationGraph, pullback.lift_fst]
    exact IsPullback.id_vert p
  apply ho.of_bot _ (parameterProductMap_isPullback q j p).flip
  apply pullback.hom_ext <;> simp [compactificationGraph]

/-- The same target graph ideal under the native flat pullback comparison. -/
def parameterGraphIdealIso [Flat p]
    [IsClosedImmersion (compactificationGraph q j)]
    [IsClosedImmersion (compactificationGraph q (p ≫ j))]
    (hI : IsLocallyRankOne _ (idealModule (compactificationGraph q j))) :
    (Modules.pullback (parameterProductMap q j p)).obj
      (idealModule (compactificationGraph q j)) ≅
        idealModule (compactificationGraph q (p ≫ j)) :=
  flatChartIdealIso (compactificationGraph q j) (compactificationGraph q (p ≫ j))
    (parameterProductMap q j p) p (parameterGraph_isPullback q j p) hI

/-- The canonical comparison preserves the ORIGINAL ideal inclusion. -/
theorem parameterGraphIdealIso_inclusion [Flat p]
    [IsClosedImmersion (compactificationGraph q j)]
    [IsClosedImmersion (compactificationGraph q (p ≫ j))]
    (hI : IsLocallyRankOne _ (idealModule (compactificationGraph q j))) :
    (parameterGraphIdealIso q j p hI).hom ≫ idealInclusion (compactificationGraph q (p ≫ j)) =
      pullbackUnitMap (parameterProductMap q j p) (idealInclusion (compactificationGraph q j)) := by
  simp only [parameterGraphIdealIso, flatChartIdealIso, asIso_hom]
  rw [idealPullbackMap_inclusion]
  rfl

end AlgebraicGeometry.Scheme.Hom
