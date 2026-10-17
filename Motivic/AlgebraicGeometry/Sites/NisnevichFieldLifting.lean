/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.CategoryTheory.Sites.JointlySurjective
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Field-valued lifting for Nisnevich covers

This file constructs the precoverage of families jointly lifting every
field-valued point. Its stability is proved from the jointly surjective
precoverage on types and the limit preservation of a representable functor.
No étaleness condition is imposed here: the Nisnevich precoverage will be the
intersection of this precoverage with the étale precoverage.

Fields and schemes have the same universe. This includes every residue field
of every scheme in this universe, and imposes no finite-type condition on the
field-valued point.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v w

namespace Motivic.Nisnevich

/-- Families of schemes jointly lifting every field-valued point. -/
def fieldLiftingPrecoverage : Precoverage Scheme.{u} where
  coverings X := {R | ∀ (K : Type u) (_ : Field K),
    R ∈ Types.jointlySurjectivePrecoverage.comap (coyoneda.obj (op (Spec (.of K)))) X}

/-- The explicit lifting condition for a covering family. -/
theorem mem_fieldLiftingPrecoverage_iff {X : Scheme.{u}} {R : Presieve X} :
    R ∈ fieldLiftingPrecoverage X ↔
      ∀ (K : Type u) [Field K] (x : Spec (.of K) ⟶ X),
        ∃ (Y : Scheme.{u}) (f : Y ⟶ X), R f ∧
          ∃ y : Spec (.of K) ⟶ Y, y ≫ f = x := by
  simp only [fieldLiftingPrecoverage, Set.mem_ofPred_eq,
    Presieve.mem_comap_jointlySurjectivePrecoverage_iff, Set.mem_range]
  rfl

/-- Every point has a lift at which the residue-field map is an isomorphism. -/
def IsResidueFieldLifting {X : Scheme.{u}} (R : Presieve X) : Prop :=
  ∀ x : X, ∃ (Y : Scheme.{u}) (f : Y ⟶ X), R f ∧
    ∃ y : Y, f y = x ∧ IsIso (f.residueFieldMap y)

set_option backward.isDefEq.respectTransparency false in
/-- The field-valued lifting condition implies the usual residue-field lifting condition. -/
theorem isResidueFieldLifting_of_mem {X : Scheme.{u}} {R : Presieve X}
    (hR : R ∈ fieldLiftingPrecoverage X) : IsResidueFieldLifting R := by
  intro x
  obtain ⟨Y, f, hf, g, hgf⟩ := mem_fieldLiftingPrecoverage_iff.mp hR
    (X.residueField x) (X.fromSpecResidueField x)
  obtain ⟨⟨y, b⟩, rfl⟩ := (Scheme.SpecToEquivOfField (X.residueField x) Y).symm.surjective g
  have hy : f y = x := by
    have := congrArg (fun h : Spec (X.residueField x) ⟶ X ↦
      h (IsLocalRing.closedPoint (X.residueField x))) hgf
    change f (Y.fromSpecResidueField y (Spec.map b
      (IsLocalRing.closedPoint (X.residueField x)))) =
      X.fromSpecResidueField x (IsLocalRing.closedPoint (X.residueField x)) at this
    simpa only [Scheme.fromSpecResidueField_apply] using this
  refine ⟨Y, f, hf, y, hy, ?_⟩
  subst x
  have hcomp : f.residueFieldMap y ≫ b = 𝟙 _ := by
    rw [← Spec.map_inj]
    apply (cancel_mono (X.fromSpecResidueField (f y))).mp
    change Spec.map b ≫ Y.fromSpecResidueField y ≫ f = _ at hgf
    rw [Spec.map_comp, Category.assoc,
      f.SpecMap_residueFieldMap_fromSpecResidueField y, Spec.map_id]
    exact hgf.trans (Category.id_comp _).symm
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine ⟨(f.residueFieldMap y).hom.injective, fun z ↦ ⟨b z, ?_⟩⟩
  apply b.hom.injective
  exact congrArg (fun t : X.residueField (f y) ⟶ X.residueField (f y) ↦ t (b z)) hcomp

set_option backward.isDefEq.respectTransparency.types false in
/-- The usual residue-field lifting condition lifts every field-valued point. -/
theorem mem_of_isResidueFieldLifting {X : Scheme.{u}} {R : Presieve X}
    (hR : IsResidueFieldLifting R) : R ∈ fieldLiftingPrecoverage X := by
  rw [mem_fieldLiftingPrecoverage_iff]
  intro K _ x
  obtain ⟨⟨x, a⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective x
  obtain ⟨Y, f, hf, y, rfl, hi⟩ := hR x
  let := hi
  refine ⟨Y, f, hf, Spec.map (inv (f.residueFieldMap y) ≫ a) ≫
    Y.fromSpecResidueField y, ?_⟩
  rw [Category.assoc, ← f.SpecMap_residueFieldMap_fromSpecResidueField y,
    ← Spec.map_comp_assoc]
  simp [Scheme.SpecToEquivOfField]

/-- Field-valued lifting is exactly residue-field-isomorphism lifting. -/
theorem mem_fieldLiftingPrecoverage_iff_residueField {X : Scheme.{u}} {R : Presieve X} :
    R ∈ fieldLiftingPrecoverage X ↔ IsResidueFieldLifting R :=
  ⟨isResidueFieldLifting_of_mem, mem_of_isResidueFieldLifting⟩

instance : fieldLiftingPrecoverage.{u}.HasIsos where
  mem_coverings_of_isIso f _ K hK := by
    let := hK
    exact Precoverage.mem_coverings_of_isIso f

instance : fieldLiftingPrecoverage.{u}.IsStableUnderComposition where
  comp_mem_coverings {ι} S X f hf σ Y g hg K hK := by
    let := hK
    exact Precoverage.comp_mem_coverings _ (hf K hK) _ (fun i ↦ hg i K hK)

instance : fieldLiftingPrecoverage.{u}.IsStableUnderBaseChange where
  mem_coverings_of_isPullback {ι} S X f hf Y g P p₁ p₂ h K hK := by
    let := hK
    exact Precoverage.mem_coverings_of_isPullback _ (hf K hK) _ _ _ h

/-- The topology generated by field-lifting families, before imposing étaleness. -/
def fieldLiftingTopology : GrothendieckTopology Scheme.{u} :=
  fieldLiftingPrecoverage.toGrothendieck

/-- A covering family of a field spectrum contains a morphism with a section. -/
theorem exists_section_of_mem_fieldLiftingPrecoverage (K : Type u) [Field K]
    {R : Presieve (Spec (.of K))} (hR : R ∈ fieldLiftingPrecoverage _) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of K)), R f ∧
      ∃ s : Spec (.of K) ⟶ Y, s ≫ f = 𝟙 _ :=
  mem_fieldLiftingPrecoverage_iff.mp hR K (𝟙 _)

/-- Every covering sieve of a field spectrum is maximal. -/
theorem fieldLifting_covering_sieve_eq_top (K : Type u) [Field K]
    {S : Sieve (Spec (.of K))} (hS : S ∈ fieldLiftingTopology _) : S = ⊤ := by
  obtain ⟨R, hR, hRS⟩ :=
    fieldLiftingPrecoverage.mem_toGrothendieck_iff_of_isStableUnderComposition.mp hS
  obtain ⟨Y, f, hf, s, hs⟩ := exists_section_of_mem_fieldLiftingPrecoverage K hR
  apply Sieve.id_mem_iff_eq_top.mp
  simpa only [hs] using S.downward_closed (hRS _ _ hf) s

/-- There are no nonmaximal covering sieves at a field spectrum. -/
theorem mem_fieldLiftingTopology_iff (K : Type u) [Field K]
    (S : Sieve (Spec (.of K))) : S ∈ fieldLiftingTopology _ ↔ S = ⊤ := by
  constructor
  · exact fieldLifting_covering_sieve_eq_top K
  · rintro rfl
    exact fieldLiftingTopology.top_mem _

end Motivic.Nisnevich
