/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.IdealSheaf.RadicalSubscheme
public import Motivic.Aglib.AlgebraicGeometry.Scheme.FiniteTypeNoetherian
public import Motivic.Aglib.AlgebraicGeometry.Cycles.ResidueDegree
public import Motivic.Aglib.AlgebraicGeometry.Sites.Nisnevich.Basic
public import Mathlib.AlgebraicGeometry.SpreadingOut

/-!
# Finite residue-field-lifting subfamilies over noetherian schemes

A family of locally finite-type morphisms which lifts every point with an
isomorphism on its actual residue field has a finite subfamily with the same
property over a noetherian base. In particular this applies to Nisnevich
families. No reducedness or dimension hypothesis on the base is needed.

The proof is noetherian induction on closed subsets. On the reduced closed
subscheme, a lift of one generic point spreads to a nonempty relative open.
The complement is a strictly smaller closed subset. Merely taking a finite
subcover of the topological images would not prove residue-field lifting.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u v

namespace AlgebraicGeometry.Nisnevich

private theorem isIso_residueFieldMap_of_surjectiveOnStalks
    {Y X : Scheme.{u}} (f : Y ⟶ X) [SurjectiveOnStalks f] (y : Y) :
    IsIso (f.residueFieldMap y) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨(f.residueFieldMap y).hom.injective, Scheme.Hom.residueFieldMap_surjective f y⟩

private theorem isIso_residueFieldMap_of_comp
    {W Y X : Scheme.{u}} (s : W ⟶ Y) (f : Y ⟶ X) (w : W)
    [IsIso ((s ≫ f).residueFieldMap w)] : IsIso (f.residueFieldMap (s w)) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine ⟨(f.residueFieldMap (s w)).hom.injective, ?_⟩
  have h := ((ConcreteCategory.isIso_iff_bijective _).mp
    (inferInstance : IsIso ((s ≫ f).residueFieldMap w))).surjective
  rw [Scheme.residueFieldMap_comp] at h
  change Function.Surjective ((s.residueFieldMap w) ∘
    (f.residueFieldMap (s w))) at h
  exact h.of_comp_left (s.residueFieldMap w).hom.injective

/-- Locally finite-type residue-field-lifting families over a noetherian base
have finite residue-field-lifting subfamilies. The index universe is arbitrary. -/
theorem exists_finset_residueFieldLifting
    {X : Scheme.{u}} [IsNoetherian X] {ι : Type v} {Y : ι → Scheme.{u}}
    (f : ∀ i, Y i ⟶ X) [∀ i, LocallyOfFiniteType (f i)]
    (hf : ∀ x : X, ∃ (i : ι) (y : Y i),
      f i y = x ∧ IsIso ((f i).residueFieldMap y)) :
    ∃ s : Finset ι, ∀ x : X, ∃ i ∈ s, ∃ y : Y i,
      f i y = x ∧ IsIso ((f i).residueFieldMap y) := by
  classical
  have hfield : Presieve.ofArrows Y f ∈ fieldLiftingPrecoverage X :=
    mem_of_isResidueFieldLifting fun x ↦ by
      obtain ⟨i, y, hy, hi⟩ := hf x
      exact ⟨Y i, f i, ⟨i⟩, y, hy, hi⟩
  suffices ∀ Z : Closeds X, ∃ s : Finset ι, ∀ x ∈ Z,
      ∃ i ∈ s, ∃ y : Y i, f i y = x ∧ IsIso ((f i).residueFieldMap y) by
    obtain ⟨s, hs⟩ := this ⊤
    exact ⟨s, fun x ↦ hs x (by trivial)⟩
  intro Z
  apply (wellFounded_lt (α := Closeds X)).induction Z
  intro Z ih
  by_cases hZ : Z = ⊥
  · subst Z
    exact ⟨∅, fun x hx ↦ False.elim hx⟩
  let I := (Scheme.IdealSheafData.vanishingIdeal Z).radical
  let R := I.subscheme
  let j : R ⟶ X := I.subschemeι
  have hj : Set.range j = (Z : Set X) := by
    exact I.range_subschemeι
  have : IsNoetherian R := Scheme.isNoetherian_of_finiteType j
  have : IsReduced R := Scheme.IdealSheafData.isReduced_radical_subscheme _
  obtain ⟨x, hx⟩ := Closeds.coe_nonempty.mpr hZ
  obtain ⟨r, _⟩ := hj.symm.subset hx
  let η : genericPoints R := genericPoints.ofComponent
    ⟨irreducibleComponent r, irreducibleComponent_mem_irreducibleComponents r⟩
  let : Field (R.presheaf.stalk η) :=
    (isField_stalk_of_closure_mem_irreducibleComponents R η η.property).toField
  obtain ⟨_, _, ⟨i⟩, g, hg⟩ := mem_fieldLiftingPrecoverage_iff.mp hfield
    (R.presheaf.stalk η) (R.fromSpecStalk η ≫ j)
  obtain ⟨U, hηU, t, _, ht⟩ := spread_out_of_isGermInjective' j (f i) g hg
  let C : Closeds X := ⟨j '' (U : Set R)ᶜ,
    j.isClosedEmbedding.isClosedMap _ U.isOpen.isClosed_compl⟩
  have hCZ : C < Z := by
    refine lt_of_le_of_ne ?_ ?_
    · intro z hz
      rcases hz with ⟨r, _, rfl⟩
      exact hj.subset ⟨r, rfl⟩
    · intro he
      have hη : j η ∈ C := by
        rw [he]
        exact hj.subset ⟨η, rfl⟩
      obtain ⟨r, hr, heq⟩ := hη
      exact hr ((j.isClosedEmbedding.injective heq).symm ▸ hηU)
  obtain ⟨s, hs⟩ := ih C hCZ
  refine ⟨insert i s, fun z hz ↦ ?_⟩
  obtain ⟨r, rfl⟩ := hj.symm.subset hz
  by_cases hr : r ∈ U
  · let w : U.toScheme := ⟨r, hr⟩
    have : IsIso ((U.ι ≫ j).residueFieldMap w) :=
      isIso_residueFieldMap_of_surjectiveOnStalks _ w
    have : IsIso ((t ≫ f i).residueFieldMap w) := by
      rw [ht]
      infer_instance
    refine ⟨i, Finset.mem_insert_self _ _, t w, ?_,
      isIso_residueFieldMap_of_comp t (f i) w⟩
    exact congrArg (fun q : U.toScheme ⟶ X ↦ q w) ht
  · obtain ⟨k, hk, y, hy, hi⟩ := hs (j r) ⟨r, hr, rfl⟩
    exact ⟨k, Finset.mem_insert_of_mem hk, y, hy, hi⟩

/-- A genuine Nisnevich family over a noetherian scheme contains finitely many
members which still lift every point with its actual residue field. -/
theorem exists_finset_of_mem_precoverage
    {X : Scheme.{u}} [IsNoetherian X] {ι : Type v} {Y : ι → Scheme.{u}}
    (f : ∀ i, Y i ⟶ X) (hf : Presieve.ofArrows Y f ∈ precoverage X) :
    ∃ s : Finset ι, ∀ x : X, ∃ i ∈ s, ∃ y : Y i,
      f i y = x ∧ IsIso ((f i).residueFieldMap y) := by
  obtain ⟨he, hl⟩ := (ofArrows_mem_precoverage_iff f).mp hf
  let (i : ι) : Etale (f i) := he i
  exact exists_finset_residueFieldLifting f hl

end AlgebraicGeometry.Nisnevich
