/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Presentation.BaseBadChart
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Presentation.PrescribedCartesian
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Presentation.PuncturedCover
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Affine.BaseRestriction
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Presentation.PrescribedSubquotient

/-! # Actual curve-presentation data retaining the original étale map and full closed scheme -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurve

/-- The output consumed by the original-section lifting theorem. The étale source and
puncture are always the literal pullbacks along `refinement`; the full original Z is
retained by an actual Cartesian square, not by a point-set replacement. -/
structure OriginalEtalePresentation (k : Type u) [Field k]
    {X Y A Z : Scheme.{u}} (b : X ⟶ Spec (.of k)) (p : Y ⟶ X) (a : A ⟶ X) (z : Z ⟶ X) (s : Z ⟶ Y)
    (x : X) where
  /-- The coefficient ring for the relative projective line. -/
  base : CommRingCat.{u}
  base_noetherian : IsNoetherianRing base
  /-- The structural map from the spectrum of the coefficient ring to the ground field. -/
  toField : Spec base ⟶ Spec (.of k)
  base_smooth : Smooth toField
  /-- The affine scheme presenting an open refinement of the original target. -/
  target : Scheme.{u}
  target_affine : IsAffine target
  /-- The open refinement map to the original target. -/
  refinement : target ⟶ X
  refinement_open : IsOpenImmersion refinement
  /-- A point of the refined target lying over the specified original point. -/
  point : target
  point_eq : refinement point = x
  /-- The integral normal compactification carrying the finite projective map. -/
  compact : Scheme.{u}
  compact_integral : IsIntegral compact
  compact_noetherian : IsLocallyNoetherian compact
  compact_normal : ∀ c : compact, IsIntegrallyClosed (compact.presheaf.stalk c)
  /-- The finite map from the compactification to the relative projective line. -/
  projectiveMap : compact ⟶ ProjectiveSpace base (ULift.{u} (Fin 2))
  projective_finite : IsFinite projectiveMap
  /-- The open inclusion of the refined target into its compactification. -/
  inclusion : target ⟶ compact
  inclusion_open : IsOpenImmersion inclusion
  target_smooth : SmoothOfRelativeDimension 1
    (inclusion ≫ projectiveMap ≫ ProjectiveSpace.toSpec base _)
  base_compatibility : refinement ≫ b =
    inclusion ≫ projectiveMap ≫ ProjectiveSpace.toSpec base _ ≫ toField
  /-- The scheme obtained by pulling back the full original closed scheme to the refined target. -/
  closed : Scheme.{u}
  /-- The projection from the retained closed scheme to the original closed scheme. -/
  closedToOriginal : closed ⟶ Z
  /-- The map from the retained closed scheme to the refined target. -/
  closedInclusion : closed ⟶ target
  closed_cartesian : IsPullback closedToOriginal closedInclusion z refinement
  closed_finite : IsFinite
    (closedInclusion ≫ inclusion ≫ projectiveMap ≫ ProjectiveSpace.toSpec base _)
  /-- The closed lift of the retained closed scheme to the pulled original étale source. -/
  closedLift : closed ⟶ pullback p refinement
  closedLift_original : closedLift ≫ pullback.fst p refinement = closedToOriginal ≫ s
  closedLift_eq : closedLift ≫ pullback.snd p refinement = closedInclusion
  closedLift_closed : IsClosedImmersion closedLift
  closedLift_cartesian : IsPullback closedLift (𝟙 closed) (pullback.snd p refinement)
    closedInclusion
  punctured_disjoint : Disjoint (Set.range (pullback.snd a refinement)) (Set.range closedInclusion)
  punctured_cover : ∀ y : target,
    y ∈ Set.range (pullback.snd a refinement) ∨ y ∈ Set.range closedInclusion
  /-- The boundary scheme equipped with a closed immersion into the compactification. -/
  boundary : Scheme.{u}
  /-- The closed immersion of the boundary into the compactification. -/
  boundaryInclusion : boundary ⟶ compact
  boundary_closed : IsClosedImmersion boundaryInclusion
  boundary_finite : IsFinite (boundaryInclusion ≫ projectiveMap ≫ ProjectiveSpace.toSpec base _)
  /-- The open subset over which the pulled original étale map is finite. -/
  goodOpen : target.Opens
  good_finite : IsFinite ((pullback.snd p refinement) ∣_ goodOpen)
  bad_cover : (Set.range (goodOpen.ι ≫ inclusion))ᶜ ⊆ Set.range boundaryInclusion

end AlgebraicGeometry.Scheme.RelativeCurve
