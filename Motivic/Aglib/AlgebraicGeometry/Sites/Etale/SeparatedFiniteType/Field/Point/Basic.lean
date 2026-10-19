/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Nisnevich
public import Mathlib.CategoryTheory.Sites.Point.Presheaf

/-! # Actual field-valued evaluation points on the small Nisnevich site

A connected field object is a genuine Nisnevich point represented by that object.
This does not assert that the topology on disconnected finite étale objects is trivial.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u v w
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable {S : Scheme.{u}} (K : Type u) [Field K] (q : Spec (.of K) ⟶ S)
  [Etale q] [IsSeparated q] [QuasiCompact q]

/-- The actual field object, retaining its structural map. -/
def fieldObject : EtaleSeparatedFiniteType S :=
  MorphismProperty.Over.mk ⊤ q ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩

/-- Every covering sieve lifts an actual map from the field object. -/
theorem fieldObject_cover_lifting {V : EtaleSeparatedFiniteType S} (R : Sieve V)
    (hR : R ∈ nisnevichTopology S V) (a : fieldObject K q ⟶ V) :
    ∃ (W : EtaleSeparatedFiniteType S) (g : W ⟶ V), R g ∧
      ∃ b : fieldObject K q ⟶ W, b ≫ g = a := by
  obtain ⟨Q, hQ, hQR⟩ :=
    Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition.mp hR
  obtain ⟨ι, W, g, rfl⟩ := Q.exists_eq_ofArrows
  have hscheme : Presieve.ofArrows (fun i => (W i).left) (fun i => (g i).left) ∈
      Nisnevich.precoverage V.left := by
    have h := hQ
    change (Presieve.ofArrows W g).map (forgetScheme S) ∈ Nisnevich.precoverage V.left at h
    rwa [Presieve.map_ofArrows] at h
  obtain ⟨_, _, ⟨i⟩, b, hb⟩ := Nisnevich.mem_fieldLiftingPrecoverage_iff.mp hscheme.2 K a.left
  let b' : fieldObject K q ⟶ W i := MorphismProperty.Over.homMk b (by
    change b ≫ (W i).hom = q
    rw [← MorphismProperty.Over.w (g i), ← Category.assoc, hb]
    exact MorphismProperty.Over.w a)
  refine ⟨W i, g i, hQR _ _ ⟨i⟩, b', ?_⟩
  apply MorphismProperty.Over.Hom.ext
  exact hb

/-- A connected field object defines the represented point of the actual Nisnevich topology. -/
def fieldPoint : (nisnevichTopology S).Point.{u + 1} where
  fiber := (GrothendieckTopology.pointBot.{u + 1} (fieldObject K q)).fiber
  jointly_surjective {V} R hR a := by
    obtain ⟨W, g, hg, b, hb⟩ := fieldObject_cover_lifting K q R hR
      (shrinkYonedaObjObjEquiv.{u + 1} a)
    refine ⟨W, g, hg, shrinkYonedaObjObjEquiv.{u + 1}.symm b, ?_⟩
    apply shrinkYonedaObjObjEquiv.{u + 1}.injective
    change shrinkYonedaObjObjEquiv.{u + 1}
      ((shrinkYoneda.{u + 1}.map g).app (op (fieldObject K q))
        (shrinkYonedaObjObjEquiv.{u + 1}.symm b)) = shrinkYonedaObjObjEquiv.{u + 1} a
    rw [shrinkYonedaObjObjEquiv_map_app, Equiv.apply_symm_apply]
    exact hb

variable (A : Type v) [Category.{w} A] [HasColimitsOfSize.{u + 1, u + 1} A]

/-- The represented Nisnevich point evaluates the original presheaf at the actual field object. -/
def fieldPointPresheafFiberIso : (fieldPoint K q).presheafFiber (A := A) ≅
    (CategoryTheory.evaluation (EtaleSeparatedFiniteType S)ᵒᵖ A).obj (op (fieldObject K q)) :=
  GrothendieckTopology.pointBotPresheafFiberIso.{u + 1} (fieldObject K q) A

/-- On ordinary Nisnevich sheaves the point fiber is literal evaluation,
naturally in coefficients. -/
def fieldPointSheafFiberIso : (fieldPoint K q).sheafFiber (A := A) ≅
    sheafToPresheaf (nisnevichTopology S) A ⋙
      (CategoryTheory.evaluation (EtaleSeparatedFiniteType S)ᵒᵖ A).obj (op (fieldObject K q)) :=
  Functor.isoWhiskerLeft (sheafToPresheaf (nisnevichTopology S) A)
    (fieldPointPresheafFiberIso K q A)

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
