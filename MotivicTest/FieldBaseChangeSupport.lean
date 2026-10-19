/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.BaseChange.Field.Support

/-!
# Actual-support field-change consumers

All tests allow arbitrary field maps and disconnected smooth objects. No finite
extension or finite-type ground-field map is assumed. The actual support can
split and can acquire nilpotents, so its local lengths must be retained. In
particular an inseparable example can have coefficient `p`, not coefficient one.
-/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

namespace MotivicTest.FieldBaseChangeSupport
open _root_.AlgebraicGeometry.Scheme (IntegralClosedSubscheme SmoothSite)

variable {k L : Type u} [Field k] [Field L] (φ : k →+* L)
  {X Y : SmoothSite.overField k} (A : FiniteCorrespondenceGenerator X.hom Y.hom)

/-- The support is the literal unreduced product with the new field spectrum. -/
theorem actualWholeSupport : A.fieldBaseChangeSupport φ =
    pullback (A.projection ≫ X.hom) (Spec.map (CommRingCat.ofHom φ)) := rfl

/-- The map to the new smooth source is genuinely finite. -/
example : IsFinite (A.fieldBaseChangeProjection φ) := inferInstance

/-- Every actual reduced support component is finite over the new source. -/
example (w : genericPoints (A.fieldBaseChangeSupport φ)) :
    IsFinite ((IntegralClosedSubscheme.pointClosure w.1).val.subschemeι ≫
      A.fieldBaseChangeProjection φ) := inferInstance

/-- The entire support, before reduction, is closed in the new relative product. -/
example : IsClosedImmersion (A.fieldBaseChangeInclusion φ) := inferInstance

/-- The new ambient source projection is the same geometric map used for finiteness. -/
theorem exactSourceProjection :
    A.fieldBaseChangeInclusion φ ≫
      pullback.fst ((SmoothSite.fieldBaseChange φ).obj X).hom
        ((SmoothSite.fieldBaseChange φ).obj Y).hom = A.fieldBaseChangeProjection φ :=
  A.fieldBaseChangeInclusion_fst φ

/-- The cycle coefficient is the actual whole-support generic local length. -/
theorem actualWholeMultiplicity (w : genericPoints (A.fieldBaseChangeSupport φ)) :
    A.fieldBaseChangeSupportCycle φ (IntegralClosedSubscheme.pointClosure w.1) =
      ((Module.length ((A.fieldBaseChangeSupport φ).presheaf.stalk w.1)
        ((A.fieldBaseChangeSupport φ).presheaf.stalk w.1)).toNat : ℤ) :=
  A.fieldBaseChangeSupportCycle_component φ w

/-- Empty sources admit no integral finite-correspondence generators. -/
theorem noGeneratorOfEmptySource [IsEmpty X.left] :
    IsEmpty (FiniteCorrespondenceGenerator X.hom Y.hom) := by
  constructor
  intro B
  exact isEmptyElim (α := X.left) (B.projection (Classical.arbitrary B.scheme))

/-- An empty new source has empty support, so no component is silently selected. -/
theorem emptyNewSource [IsEmpty ((SmoothSite.fieldBaseChange φ).obj X).left] :
    IsEmpty (A.fieldBaseChangeSupport φ) :=
  ⟨fun w => isEmptyElim (A.fieldBaseChangeProjection φ w)⟩

/-- No irreducibility assumption is placed on either smooth object. Each new
support component has an actual irreducible source component as its whole image. -/
theorem eachActualComponentDominates (w : genericPoints (A.fieldBaseChangeSupport φ)) :
    Set.range ((IntegralClosedSubscheme.pointClosure w.1).val.subschemeι ≫
      A.fieldBaseChangeProjection φ) ∈
        irreducibleComponents ((SmoothSite.fieldBaseChange φ).obj X).left :=
  A.fieldBaseChangeComponent_range_mem φ w

/-- The component really lands in the geometric basis of finite correspondences
on the new ground field, not merely in an unrestricted cycle group. -/
def actualNewGenerator (w : genericPoints (A.fieldBaseChangeSupport φ)) :
    FiniteCorrespondenceGenerator ((SmoothSite.fieldBaseChange φ).obj X).hom
      ((SmoothSite.fieldBaseChange φ).obj Y).hom :=
  A.fieldBaseChangeComponentGenerator φ w

/-- Its ideal sheaf is the literal image of the actual reduced component. -/
theorem actualNewGenerator_image (w : genericPoints (A.fieldBaseChangeSupport φ)) :
    (actualNewGenerator φ A w).val =
      ((IntegralClosedSubscheme.pointClosure w.1).finiteImage
        (A.fieldBaseChangeInclusion φ)).val :=
  A.fieldBaseChangeComponentGenerator_val φ w

open Lean in
run_cmd do
  for name in #[``FiniteCorrespondenceGenerator.fieldBaseChangeProjection_isPullback,
      ``FiniteCorrespondenceGenerator.fieldBaseChangeProjection_isFinite,
      ``FiniteCorrespondenceGenerator.fieldBaseChangeSupport_isNoetherian,
      ``FiniteCorrespondenceGenerator.fieldBaseChangeAmbientInclusion_isPullback,
      ``FiniteCorrespondenceGenerator.fieldBaseChangeInclusion_isClosedImmersion,
      ``exactSourceProjection, ``actualWholeMultiplicity, ``noGeneratorOfEmptySource,
      ``emptyNewSource, ``eachActualComponentDominates, ``actualNewGenerator,
      ``actualNewGenerator_image,
      ``FiniteCorrespondenceGenerator.fieldBaseChangeProjection_generic,
      ``FiniteCorrespondenceGenerator.fieldBaseChangeComponent_range_mem,
      ``FiniteCorrespondenceGenerator.fieldBaseChangeComponentGenerator] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual field-base-change support geometry uses only standard foundations."

end MotivicTest.FieldBaseChangeSupport
