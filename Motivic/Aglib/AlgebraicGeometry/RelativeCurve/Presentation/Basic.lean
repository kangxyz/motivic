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
  base : CommRingCat.{u}
  base_noetherian : IsNoetherianRing base
  toField : Spec base ⟶ Spec (.of k)
  base_smooth : Smooth toField
  target : Scheme.{u}
  target_affine : IsAffine target
  refinement : target ⟶ X
  refinement_open : IsOpenImmersion refinement
  point : target
  point_eq : refinement point = x
  compact : Scheme.{u}
  compact_integral : IsIntegral compact
  compact_noetherian : IsLocallyNoetherian compact
  compact_normal : ∀ c : compact, IsIntegrallyClosed (compact.presheaf.stalk c)
  projectiveMap : compact ⟶ ProjectiveSpace base (ULift.{u} (Fin 2))
  projective_finite : IsFinite projectiveMap
  inclusion : target ⟶ compact
  inclusion_open : IsOpenImmersion inclusion
  target_smooth : SmoothOfRelativeDimension 1
    (inclusion ≫ projectiveMap ≫ ProjectiveSpace.toSpec base _)
  base_compatibility : refinement ≫ b =
    inclusion ≫ projectiveMap ≫ ProjectiveSpace.toSpec base _ ≫ toField
  closed : Scheme.{u}
  closedToOriginal : closed ⟶ Z
  closedInclusion : closed ⟶ target
  closed_cartesian : IsPullback closedToOriginal closedInclusion z refinement
  closed_finite : IsFinite
    (closedInclusion ≫ inclusion ≫ projectiveMap ≫ ProjectiveSpace.toSpec base _)
  closedLift : closed ⟶ pullback p refinement
  closedLift_original : closedLift ≫ pullback.fst p refinement = closedToOriginal ≫ s
  closedLift_eq : closedLift ≫ pullback.snd p refinement = closedInclusion
  closedLift_closed : IsClosedImmersion closedLift
  closedLift_cartesian : IsPullback closedLift (𝟙 closed) (pullback.snd p refinement)
    closedInclusion
  punctured_disjoint : Disjoint (Set.range (pullback.snd a refinement)) (Set.range closedInclusion)
  punctured_cover : ∀ y : target,
    y ∈ Set.range (pullback.snd a refinement) ∨ y ∈ Set.range closedInclusion
  boundary : Scheme.{u}
  boundaryInclusion : boundary ⟶ compact
  boundary_closed : IsClosedImmersion boundaryInclusion
  boundary_finite : IsFinite (boundaryInclusion ≫ projectiveMap ≫ ProjectiveSpace.toSpec base _)
  goodOpen : target.Opens
  good_finite : IsFinite ((pullback.snd p refinement) ∣_ goodOpen)
  bad_cover : (Set.range (goodOpen.ι ≫ inclusion))ᶜ ⊆ Set.range boundaryInclusion

end AlgebraicGeometry.Scheme.RelativeCurve
