/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.SmoothSiteCoproducts
public import Motivic.Aglib.AlgebraicGeometry.NisnevichFiniteSubfamily

/-!
# Finite total Nisnevich covers in the smooth site

A finite family of smooth separated finite-type schemes has an actual finite
scheme disjoint union. Its component inclusions cover it and its descendent
restricts to the original maps. Over a noetherian target, every Nisnevich family
has a finite subfamily whose total map is again Nisnevich, including residue-field
lifting. The empty family is represented by the empty scheme.

This does not assert that an ordinary sieve containing all the components
contains their total map: that assertion would require additional structure.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace Motivic.SmoothSite

variable {S : Scheme.{u}}

/-- The finite disjoint union, constructed from actual scheme coproducts and the empty scheme. -/
def finiteCoproduct : {n : ℕ} → (Fin n → SmoothSite S) → SmoothSite S
  | 0, _ => mk (Scheme.emptyTo S)
  | n + 1, Y => coproduct (Y 0) (finiteCoproduct (fun i : Fin n => Y i.succ))

/-- Inclusion of a component into the finite disjoint union. -/
def finiteCoproductι : {n : ℕ} → (Y : Fin n → SmoothSite S) →
    (i : Fin n) → Y i ⟶ finiteCoproduct Y
  | 0, _, i => Fin.elim0 i
  | n + 1, Y, i => Fin.cases
      (coproductInl (Y 0) (finiteCoproduct (fun j : Fin n => Y j.succ)))
      (fun j => finiteCoproductι (fun k : Fin n => Y k.succ) j ≫
        coproductInr (Y 0) (finiteCoproduct (fun k : Fin n => Y k.succ))) i

/-- Descent of an ordinary finite family of smooth-site morphisms. -/
def finiteCoproductDesc {X : SmoothSite S} : {n : ℕ} → {Y : Fin n → SmoothSite S} →
    (∀ i, Y i ⟶ X) → (finiteCoproduct Y ⟶ X)
  | 0, _, _ => homMk (Scheme.emptyTo X.left) (Scheme.empty_ext _ _)
  | n + 1, _, f => coproductDesc (f 0)
      (finiteCoproductDesc (fun i : Fin n => f i.succ))

@[reassoc (attr := simp)]
theorem finiteCoproductι_desc {n : ℕ} {X : SmoothSite S} {Y : Fin n → SmoothSite S}
    (f : ∀ i, Y i ⟶ X) (i : Fin n) :
    finiteCoproductι Y i ≫ finiteCoproductDesc f = f i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · change coproductInl _ _ ≫ coproductDesc _ _ = _
        exact coproductInl_desc _ _
      · change (finiteCoproductι _ j ≫ coproductInr _ _) ≫ coproductDesc _ _ = _
        rw [Category.assoc, coproductInr_desc]
        exact ih _ j

instance {n : ℕ} (Y : Fin n → SmoothSite S) (i : Fin n) :
    IsOpenImmersion (finiteCoproductι Y i).left := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · change IsOpenImmersion (coproductInl _ _).left
        infer_instance
      · have := ih (fun k : Fin n => Y k.succ) j
        change IsOpenImmersion ((finiteCoproductι _ j).left ≫ (coproductInr _ _).left)
        infer_instance

instance {n : ℕ} (Y : Fin n → SmoothSite S) (i : Fin n) :
    IsClosedImmersion (finiteCoproductι Y i).left := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · change IsClosedImmersion (coproductInl _ _).left
        infer_instance
      · have := ih (fun k : Fin n => Y k.succ) j
        change IsClosedImmersion ((finiteCoproductι _ j).left ≫ (coproductInr _ _).left)
        infer_instance

instance {n : ℕ} (Y : Fin n → SmoothSite S) (i : Fin n) :
    IsFinite (finiteCoproductι Y i).left := inferInstance

/-- Every point of the finite total scheme lies in an original component. -/
theorem finiteCoproduct_covers {n : ℕ} (Y : Fin n → SmoothSite S)
    (z : (finiteCoproduct Y).left) :
    ∃ (i : Fin n) (y : (Y i).left), (finiteCoproductι Y i).left y = z := by
  induction n with
  | zero =>
      have : IsEmpty (finiteCoproduct Y).left := inferInstanceAs (IsEmpty (∅ : Scheme.{u}))
      exact isEmptyElim z
  | succ n ih =>
      have hz : z ∈ Set.range (coproductInl (Y 0) (finiteCoproduct (fun i => Y i.succ))).left ∪
          Set.range (coproductInr (Y 0) (finiteCoproduct (fun i => Y i.succ))).left :=
        (isCompl_range_inl_inr (Y 0).left
          (finiteCoproduct (fun i : Fin n => Y i.succ)).left).sup_eq_top.ge (Set.mem_univ z)
      rcases hz with ⟨y, rfl⟩ | ⟨w, rfl⟩
      · exact ⟨0, y, rfl⟩
      · obtain ⟨i, y, hy⟩ := ih (fun k : Fin n => Y k.succ) w
        refine ⟨i.succ, y, ?_⟩
        change (coproductInr (Y 0) (finiteCoproduct (fun k : Fin n => Y k.succ))).left
          ((finiteCoproductι (fun k : Fin n => Y k.succ) i).left y) = _
        rw [hy]

set_option backward.isDefEq.respectTransparency false in
instance finiteCoproductDesc_etale {n : ℕ} {X : SmoothSite S}
    {Y : Fin n → SmoothSite S} (f : ∀ i, Y i ⟶ X) [∀ i, Etale (f i).left] :
    Etale (finiteCoproductDesc f).left := by
  induction n with
  | zero => change Etale (Scheme.emptyTo X.left); infer_instance
  | succ n ih =>
      have := ih (fun i : Fin n => f i.succ)
      change Etale (coprod.desc (f 0).left (finiteCoproductDesc (fun i : Fin n => f i.succ)).left)
      apply IsZariskiLocalAtSource.of_openCover (coprodOpenCover.{_, 0} _ _)
      rintro (i | i)
      · simpa [coprodOpenCover] using (inferInstance : Etale (f 0).left)
      · simpa [coprodOpenCover] using
          (inferInstance : Etale (finiteCoproductDesc (fun i : Fin n => f i.succ)).left)

set_option backward.isDefEq.respectTransparency false in
/-- A finite family lifting actual residue fields has a total map with the same property. -/
theorem finiteCoproductDesc_residueFieldLifting {n : ℕ} {X : SmoothSite S}
    {Y : Fin n → SmoothSite S} (f : ∀ i, Y i ⟶ X)
    (hf : ∀ x : X.left, ∃ (i : Fin n) (y : (Y i).left),
      (f i).left y = x ∧ IsIso ((f i).left.residueFieldMap y)) :
    ∀ x : X.left, ∃ y : (finiteCoproduct Y).left,
      (finiteCoproductDesc f).left y = x ∧
        IsIso ((finiteCoproductDesc f).left.residueFieldMap y) := by
  intro x
  obtain ⟨i, y, hy, hi⟩ := hf x
  have hcomp : (finiteCoproductι Y i).left ≫ (finiteCoproductDesc f).left = (f i).left :=
    congrArg (fun g => g.left) (finiteCoproductι_desc f i)
  refine ⟨(finiteCoproductι Y i).left y, ?_, ?_⟩
  · exact (congrArg (fun g : (Y i).left ⟶ X.left => g y) hcomp).trans hy
  · have : IsIso (((finiteCoproductι Y i).left ≫
        (finiteCoproductDesc f).left).residueFieldMap y) := by
      rw [hcomp]
      exact hi
    rw [Scheme.residueFieldMap_comp] at this
    exact IsIso.of_isIso_comp_right _ ((finiteCoproductι Y i).left.residueFieldMap y)

/-- Totalizing a finite Nisnevich family produces a genuine singleton Nisnevich cover. -/
theorem finiteCoproductDesc_mem_precoverage {n : ℕ} {X : SmoothSite S}
    {Y : Fin n → SmoothSite S} (f : ∀ i, Y i ⟶ X)
    (hf : Presieve.ofArrows (fun i => (Y i).left) (fun i => (f i).left) ∈
      Nisnevich.precoverage X.left) :
    Presieve.singleton (finiteCoproductDesc f).left ∈ Nisnevich.precoverage X.left := by
  obtain ⟨he, hl⟩ := (Nisnevich.ofArrows_mem_precoverage_iff _).mp hf
  let (i : Fin n) : Etale (f i).left := he i
  rw [Nisnevich.mem_precoverage_iff]
  refine ⟨fun {_} g hg => ?_, fun x => ?_⟩
  · cases hg
    infer_instance
  · obtain ⟨y, hy, hi⟩ := finiteCoproductDesc_residueFieldLifting f hl x
    exact ⟨_, _, Presieve.singleton_self _, y, hy, hi⟩

/-- A finite selection of original family members whose actual finite disjoint union is
Nisnevich. The index map is injective, so no artificial repetitions are introduced. -/
structure FiniteNisnevichCoverNormalization {X : SmoothSite S} {ι : Type v}
    {Y : ι → SmoothSite S} (f : ∀ i, Y i ⟶ X) where
  /-- Number of selected original members; zero is allowed. -/
  size : ℕ
  /-- The selected indices in the original family. -/
  index : Fin size → ι
  /-- The selected indices have no repetitions. -/
  injective_index : Function.Injective index
  /-- The actual total map is étale. -/
  etale : Etale (finiteCoproductDesc (fun i => f (index i))).left
  /-- The actual total map lifts every point with an isomorphism of residue fields. -/
  residueFieldLifting : ∀ x : X.left,
    ∃ y : (finiteCoproduct (fun i => Y (index i))).left,
      (finiteCoproductDesc (fun i => f (index i))).left y = x ∧
        IsIso ((finiteCoproductDesc (fun i => f (index i))).left.residueFieldMap y)

namespace FiniteNisnevichCoverNormalization

variable {X : SmoothSite S} {ι : Type v} {Y : ι → SmoothSite S} {f : ∀ i, Y i ⟶ X}

/-- The actual finite total smooth scheme over the original base. -/
abbrev total (N : FiniteNisnevichCoverNormalization f) : SmoothSite S :=
  finiteCoproduct (fun i => Y (N.index i))

/-- The actual total morphism to the original target. -/
abbrev map (N : FiniteNisnevichCoverNormalization f) : N.total ⟶ X :=
  finiteCoproductDesc (fun i => f (N.index i))

/-- Inclusion of a selected original member into the finite total scheme. -/
abbrev inclusion (N : FiniteNisnevichCoverNormalization f) (i : Fin N.size) :
    Y (N.index i) ⟶ N.total := finiteCoproductι (fun j => Y (N.index j)) i

instance (N : FiniteNisnevichCoverNormalization f) : Etale N.map.left := N.etale

@[reassoc (attr := simp)]
theorem inclusion_map (N : FiniteNisnevichCoverNormalization f) (i : Fin N.size) :
    N.inclusion i ≫ N.map = f (N.index i) :=
  finiteCoproductι_desc (fun j => f (N.index j)) i

/-- The selected original schemes jointly cover the total scheme. -/
theorem covers (N : FiniteNisnevichCoverNormalization f) (z : N.total.left) :
    ∃ (i : Fin N.size) (y : (Y (N.index i)).left), (N.inclusion i).left y = z :=
  finiteCoproduct_covers _ z

/-- The normalized singleton is a genuine Nisnevich covering family. -/
theorem mem_precoverage (N : FiniteNisnevichCoverNormalization f) :
    Presieve.singleton N.map.left ∈ Nisnevich.precoverage X.left := by
  rw [Nisnevich.mem_precoverage_iff]
  refine ⟨fun {_} g hg => ?_, fun x => ?_⟩
  · cases hg
    infer_instance
  · obtain ⟨y, hy, hi⟩ := N.residueFieldLifting x
    exact ⟨_, _, Presieve.singleton_self _, y, hy, hi⟩

end FiniteNisnevichCoverNormalization

/-- Any arbitrary-index Nisnevich family over a noetherian smooth-site object admits
finite totalization by selected original members. No noetherian hypothesis on the base is used. -/
theorem exists_finiteNisnevichCoverNormalization {X : SmoothSite S} [IsNoetherian X.left]
    {ι : Type v} {Y : ι → SmoothSite S} (f : ∀ i, Y i ⟶ X)
    [∀ i, Etale (f i).left]
    (hf : ∀ x : X.left, ∃ (i : ι) (y : (Y i).left),
      (f i).left y = x ∧ IsIso ((f i).left.residueFieldMap y)) :
    Nonempty (FiniteNisnevichCoverNormalization f) := by
  classical
  obtain ⟨s, hs⟩ := Nisnevich.exists_finset_residueFieldLifting (fun i => (f i).left) hf
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  let a : Fin (Fintype.card s) → ι := fun i => (e i).val
  refine ⟨⟨_, a, Subtype.val_injective.comp e.injective, inferInstance, ?_⟩⟩
  apply finiteCoproductDesc_residueFieldLifting
  intro x
  obtain ⟨i, hi, y, hy, hfield⟩ := hs x
  refine ⟨e.symm ⟨i, hi⟩, ?_⟩
  have ha : a (e.symm ⟨i, hi⟩) = i := by simp [a]
  change ∃ y : (Y (a (e.symm ⟨i, hi⟩))).left,
    (f (a (e.symm ⟨i, hi⟩))).left y = x ∧
      IsIso ((f (a (e.symm ⟨i, hi⟩))).left.residueFieldMap y)
  rw [ha]
  exact ⟨y, hy, hfield⟩

/-- Choose a verified finite totalization of a point-and-residue-field Nisnevich family. -/
def normalizeFiniteNisnevichCover {X : SmoothSite S} [IsNoetherian X.left]
    {ι : Type v} {Y : ι → SmoothSite S} (f : ∀ i, Y i ⟶ X)
    [∀ i, Etale (f i).left]
    (hf : ∀ x : X.left, ∃ (i : ι) (y : (Y i).left),
      (f i).left y = x ∧ IsIso ((f i).left.residueFieldMap y)) :
    FiniteNisnevichCoverNormalization f :=
  Classical.choice (exists_finiteNisnevichCoverNormalization f hf)

/-- Choose a finite totalization from membership in the genuine Nisnevich precoverage. -/
def normalizeFiniteNisnevichCoverOfMem {X : SmoothSite S} [IsNoetherian X.left]
    {ι : Type v} {Y : ι → SmoothSite S} (f : ∀ i, Y i ⟶ X)
    (hf : Presieve.ofArrows (fun i => (Y i).left) (fun i => (f i).left) ∈
      Nisnevich.precoverage X.left) : FiniteNisnevichCoverNormalization f := by
  let (i : ι) : Etale (f i).left := (Nisnevich.ofArrows_mem_precoverage_iff _).mp hf |>.1 i
  exact normalizeFiniteNisnevichCover f ((Nisnevich.ofArrows_mem_precoverage_iff _).mp hf).2

end Motivic.SmoothSite
