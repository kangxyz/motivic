/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.A1.FixedTargetFiniteChartLifting
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.OriginalEtalePresentation

/-! # Consume the constructed original-data presentation without changing its original maps -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open AlgebraicGeometry.Scheme.RelativeCurve AlgebraicGeometry.Scheme.RelativeCurvePencil
open AlgebraicGeometry.Scheme.Hom
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation
variable (k : Type u) [Field k] {X Y A Z : Scheme.{u}}
  [IsAffine X] [IsAffine Y] [IsAffine A]
  (b : X ⟶ Spec (.of k)) (p : Y ⟶ X) [Etale p] [QuasiCompact p] [IsSeparated p]
  (a : A ⟶ X) [IsOpenImmersion a] (z : Z ⟶ X) (s : Z ⟶ Y) (x : X)
  (e : OriginalEtalePresentation k b p a z s x)
local instance originalLiftingBaseNoetherian : IsNoetherianRing e.base := e.base_noetherian
local instance originalLiftingBaseSmooth : Smooth e.toField := e.base_smooth
local instance originalLiftingTargetAffine : IsAffine e.target := e.target_affine
local instance originalLiftingRefinementOpen : IsOpenImmersion e.refinement := e.refinement_open
local instance originalLiftingCompactIntegral : IsIntegral e.compact := e.compact_integral
local instance originalLiftingCompactLocallyNoetherian : IsLocallyNoetherian e.compact :=
  e.compact_noetherian
local instance originalLiftingCompactNormalStalk (c :
    e.compact) : IsIntegrallyClosed (e.compact.presheaf.stalk c) :=
  e.compact_normal c
local instance originalLiftingProjectiveFinite : IsFinite e.projectiveMap := e.projective_finite
local instance originalLiftingInclusionOpen : IsOpenImmersion e.inclusion := e.inclusion_open
local instance originalLiftingRelativeSmooth : SmoothOfRelativeDimension 1
    (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) := e.target_smooth
local instance originalLiftingClosedLiftClosed : IsClosedImmersion e.closedLift :=
  e.closedLift_closed
local instance originalLiftingBoundaryFinite : IsFinite
    (e.closedInclusion ≫ e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) :=
  e.closed_finite
local instance originalLiftingMarkedBoundaryFinite : IsFinite
    (e.boundaryInclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) := e.boundary_finite
local instance originalLiftingGoodFinite : IsFinite ((pullback.snd p e.refinement) ∣_ e.goodOpen) :=
  e.good_finite

/-- The native fixed-target lifting assertion on the actual original pullback spans. -/
def HasLocalLifting (P : PresheafWithTransfers.{u + 1} k) : Prop :=
    ∃ U : e.target.Opens, IsAffineOpen U ∧ e.point ∈ U ∧
    ∃ (V : (Spec e.base).Opens) (hV : IsAffineOpen V),
      let : IsAffine V.toScheme := hV
      (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) e.point ∈ V ∧
      (∀ c : e.closed,
        (e.closedInclusion ≫ e.inclusion ≫ e.projectiveMap ≫
          ProjectiveSpace.toSpec e.base _) c ∈ V →
          e.closedInclusion c ∈ U) ∧
      ∃ hW : IsAffineOpen (boundaryBaseSourceOpen
          (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) U V),
        let : IsAffine (boundaryBaseSourceOpen
          (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _) U V).toScheme := hW
        PresheafWithTransfers.HasRestrictionDifferenceLifting P
          (fixedTargetPencilGraph k e.base (ULift.{u} (Fin 2)) e.target e.compact e.toField
            (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _)
            (pullback.snd p e.refinement) (pullback.snd a e.refinement)
            e.inclusion e.projectiveMap rfl U V)
          (fixedTargetPencilBeta k e.base (ULift.{u} (Fin 2)) e.target e.compact e.toField
            (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _)
            (pullback.snd p e.refinement) (pullback.snd a e.refinement)
            e.inclusion e.projectiveMap rfl U V)
          (fixedTargetPencilAlpha k e.base (ULift.{u} (Fin 2)) e.target e.compact e.toField
            (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _)
            (pullback.snd p e.refinement) (pullback.snd a e.refinement)
            e.inclusion e.projectiveMap rfl U V)

/-- The constructed presentation supplies actual lifting on its original spans. -/
theorem exists_lifting (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) :
    e.HasLocalLifting k b p a z s x P := by
  apply exists_fixedTarget_finiteChart_lifting k e.base (ULift.{u} (Fin 2))
    e.target e.compact e.toField
    (e.inclusion ≫ e.projectiveMap ≫ ProjectiveSpace.toSpec e.base _)
    (pullback.snd p e.refinement) (pullback.snd a e.refinement)
    e.inclusion e.projectiveMap rfl 1 Equiv.ulift e.closedInclusion e.closedLift
    e.closedLift_eq e.closedLift_cartesian e.punctured_disjoint e.punctured_cover
    e.boundaryInclusion e.goodOpen ?_ e.point P hP
  simpa only [Scheme.Hom.coe_image, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, Scheme.Opens.range_ι]
    using e.bad_cover

end AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation
