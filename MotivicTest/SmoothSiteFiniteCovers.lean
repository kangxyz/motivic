/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.SmoothSiteFiniteCovers

/-! # Consumer tests for actual finite total Nisnevich covers -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Motivic Motivic.SmoothSite

universe u v

variable {S : Scheme.{u}}

-- Finite totalization is smooth, separated and finite type over an arbitrary base.
example {n : ℕ} (Y : Fin n → SmoothSite S) :
    Smooth (finiteCoproduct Y).hom ∧ IsSeparated (finiteCoproduct Y).hom ∧
      LocallyOfFiniteType (finiteCoproduct Y).hom ∧ QuasiCompact (finiteCoproduct Y).hom :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

-- The zero-member total scheme really is empty.
example (Y : Fin 0 → SmoothSite S) : (finiteCoproduct Y).left = (∅ : Scheme.{u}) := rfl

example (Y : Fin 0 → SmoothSite S) : IsEmpty (finiteCoproduct Y).left :=
  inferInstanceAs (IsEmpty (∅ : Scheme.{u}))

-- The descent morphism restricts to each of the actual original maps.
example {n : ℕ} {X : SmoothSite S} {Y : Fin n → SmoothSite S}
    (f : ∀ i, Y i ⟶ X) (i : Fin n) :
    (finiteCoproductι Y i).left ≫ (finiteCoproductDesc f).left = (f i).left :=
  congrArg (fun g => g.left) (finiteCoproductι_desc f i)

example {n : ℕ} (Y : Fin n → SmoothSite S) (i : Fin n) :
    IsOpenImmersion (finiteCoproductι Y i).left ∧
      IsClosedImmersion (finiteCoproductι Y i).left ∧ IsFinite (finiteCoproductι Y i).left :=
  ⟨inferInstance, inferInstance, inferInstance⟩

-- A genuine arbitrary-index family produces an actual singleton Nisnevich cover.
example {X : SmoothSite S} [IsNoetherian X.left] {ι : Type v}
    {Y : ι → SmoothSite S} (f : ∀ i, Y i ⟶ X)
    (hf : Presieve.ofArrows (fun i => (Y i).left) (fun i => (f i).left) ∈
      Nisnevich.precoverage X.left) :
    ∃ (U : SmoothSite S) (q : U ⟶ X), Etale q.left ∧
      (∀ x : X.left, ∃ y : U.left, q.left y = x ∧ IsIso (q.left.residueFieldMap y)) ∧
      Presieve.singleton q.left ∈ Nisnevich.precoverage X.left := by
  let N := normalizeFiniteNisnevichCoverOfMem f hf
  exact ⟨N.total, N.map, inferInstance, N.residueFieldLifting, N.mem_precoverage⟩

-- Normalization exposes the factorization and coverage needed by additive consumers.
example {X : SmoothSite S} {ι : Type v} {Y : ι → SmoothSite S} {f : ∀ i, Y i ⟶ X}
    (N : FiniteNisnevichCoverNormalization f) :
    (∀ i, (N.inclusion i).left ≫ N.map.left = (f (N.index i)).left) ∧
      (∀ z : N.total.left, ∃ (i : Fin N.size) (y : (Y (N.index i)).left),
        (N.inclusion i).left y = z) :=
  ⟨fun i => congrArg (fun g => g.left) (N.inclusion_map i), N.covers⟩

-- Empty source indexing forces an empty total scheme; no member is fabricated.
example {X : SmoothSite S} {Y : PEmpty.{v + 1} → SmoothSite S}
    {f : ∀ i, Y i ⟶ X} (N : FiniteNisnevichCoverNormalization f) : IsEmpty N.total.left := by
  refine ⟨fun z => ?_⟩
  obtain ⟨i, _, _⟩ := N.covers z
  exact (N.index i).elim

-- The empty family covers any genuinely empty noetherian target, vacuously and honestly.
example {X : SmoothSite S} [IsNoetherian X.left] [IsEmpty X.left]
    {Y : PEmpty.{v + 1} → SmoothSite S} (f : ∀ i, Y i ⟶ X) :
    Nonempty (FiniteNisnevichCoverNormalization f) := by
  let (i : PEmpty.{v + 1}) : Etale (f i).left := i.elim
  exact exists_finiteNisnevichCoverNormalization f (fun x => isEmptyElim x)

-- A nonempty target cannot have an empty Nisnevich indexing family.
example {X : SmoothSite S} [Nonempty X.left] {Y : PEmpty.{v + 1} → SmoothSite S}
    {f : ∀ i, Y i ⟶ X} : IsEmpty (FiniteNisnevichCoverNormalization f) := by
  refine ⟨fun N => ?_⟩
  obtain ⟨x⟩ := ‹Nonempty X.left›
  obtain ⟨y, _, _⟩ := N.residueFieldLifting x
  obtain ⟨i, _, _⟩ := N.covers y
  exact (N.index i).elim
