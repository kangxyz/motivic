/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.FiniteDescent
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Noetherian
public import Motivic.AlgebraicGeometry.Correspondences.Noetherian

/-! # Consumer tests for ordinary finite-coproduct Nisnevich descent -/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open Opposite
open Motivic
open _root_.AlgebraicGeometry.Scheme.SmoothSite

universe u v w

variable {S : Scheme.{u}}

-- The hypothesis uses the actual component maps, including the empty product.
example (P : (SmoothSite S)ᵒᵖ ⥤ Type v) {n : ℕ} (Y : Fin n → SmoothSite S)
    (s : P.obj (op (finiteCoproduct Y))) (i : Fin n) :
    finiteCoproductRestriction P Y s i = P.map (finiteCoproductι Y i).op s := rfl

-- Empty-product preservation supplies a unique section on the actual empty scheme.
example (P : (SmoothSite S)ᵒᵖ ⥤ Type v)
    (hprod : ∀ (n : ℕ) (Y : Fin n → SmoothSite S),
      Function.Bijective (fun s : P.obj (op (finiteCoproduct Y)) =>
        fun i => P.map (finiteCoproductι Y i).op s)) :
    ∃! _s : P.obj (op (mk (Scheme.emptyTo S))), True := by
  let Y : Fin 0 → SmoothSite S := Fin.elim0
  obtain ⟨s, _⟩ := (hprod 0 Y).surjective (fun i => Fin.elim0 i)
  refine ⟨s, trivial, fun t _ => ?_⟩
  apply (hprod 0 Y).injective
  funext i
  exact Fin.elim0 i

-- No condition on the base is hidden: Noetherianity of all actual targets is explicit.
example [∀ X : SmoothSite S, IsNoetherian X.left]
    (P : (SmoothSite S)ᵒᵖ ⥤ Type v)
    (hprod : ∀ (n : ℕ) (Y : Fin n → SmoothSite S),
      Function.Bijective (fun s : P.obj (op (finiteCoproduct Y)) =>
        fun i => P.map (finiteCoproductι Y i).op s)) :
    Presieve.IsSheaf (nisnevichTopology S) P ↔
      ∀ {X Y : SmoothSite S} (q : Y ⟶ X),
        Presieve.singleton q ∈ nisnevichPrecoverage S X →
          Presieve.IsSheafFor P (.singleton q) :=
  isSheaf_iff_singleton_of_finiteCoproduct P hprod

-- In particular the ordinary theorem applies over every field, with independent section universe.
example (k : Type u) [Field k]
    (P : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ Type v)
    (hprod : ∀ (n : ℕ) (Y : Fin n → SmoothSite (Spec (.of k))),
      Function.Bijective (finiteCoproductRestriction P Y)) :
    Presieve.IsSheaf (nisnevichTopology (Spec (.of k))) P ↔
      ∀ {X Y : SmoothSite (Spec (.of k))} (q : Y ⟶ X),
        Presieve.singleton q ∈ nisnevichPrecoverage (Spec (.of k)) X →
          Presieve.IsSheafFor P (.singleton q) :=
  isSheaf_iff_singleton_of_finiteCoproduct P hprod

-- Arbitrarily indexed families, not just finite families, satisfy ordinary descent.
example [∀ X : SmoothSite S, IsNoetherian X.left]
    (P : (SmoothSite S)ᵒᵖ ⥤ Type v)
    (hprod : ∀ (n : ℕ) (Y : Fin n → SmoothSite S),
      Function.Bijective (finiteCoproductRestriction P Y))
    (hsingle : ∀ {X Y : SmoothSite S} (q : Y ⟶ X),
      Presieve.singleton q ∈ nisnevichPrecoverage S X → Presieve.IsSheafFor P (.singleton q))
    {X : SmoothSite S} {ι : Type w} {Y : ι → SmoothSite S} (f : ∀ i, Y i ⟶ X)
    (hf : Presieve.ofArrows Y f ∈ nisnevichPrecoverage S X) :
    Presieve.IsSheafFor P (Presieve.ofArrows Y f) :=
  isSheafFor_nisnevich_family_of_finiteCoproduct P hprod hsingle f hf

-- The genuine zero-member cover of an empty target is included without choosing a member.
example [∀ X : SmoothSite S, IsNoetherian X.left]
    (P : (SmoothSite S)ᵒᵖ ⥤ Type v)
    (hprod : ∀ (n : ℕ) (Y : Fin n → SmoothSite S),
      Function.Bijective (finiteCoproductRestriction P Y))
    (hsingle : ∀ {X Y : SmoothSite S} (q : Y ⟶ X),
      Presieve.singleton q ∈ nisnevichPrecoverage S X → Presieve.IsSheafFor P (.singleton q))
    {X : SmoothSite S} [IsEmpty X.left] (Y : Fin 0 → SmoothSite S)
    (f : ∀ i, Y i ⟶ X) : Presieve.IsSheafFor P (Presieve.ofArrows Y f) := by
  apply isSheafFor_nisnevich_family_of_finiteCoproduct P hprod hsingle f
  rw [ofArrows_mem_nisnevichPrecoverage_iff]
  exact ⟨fun i => Fin.elim0 i, fun x => isEmptyElim x⟩

-- The inclusion family is itself genuinely Nisnevich, also at size zero.
example (Y : Fin 0 → SmoothSite S) :
    Presieve.ofArrows Y (finiteCoproductι Y) ∈ nisnevichPrecoverage S (finiteCoproduct Y) :=
  finiteCoproductι_mem_nisnevichPrecoverage Y
