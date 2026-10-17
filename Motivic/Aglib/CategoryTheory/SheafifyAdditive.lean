/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Opposite
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Additivity of sheafified presheaves on singleton-generated sites

Suppose every covering sieve contains an arrow whose generated principal sieve
is itself covering. A locally surjective map from an additive presheaf of
abelian groups to a separated presheaf forces the target to be additive.
Consequently ordinary Mathlib sheafification preserves additivity in the
arrows of the source category under this explicit hypothesis.

The sheafification corollary uses coefficient universe `max u v`, where the
source objects have universe `u` and its morphisms have universe `v`. It retains
the required sheafification and forgetful-functor hypotheses. In particular,
for a source category whose objects live in `Type (u + 1)`, this statement does
not claim a sheafification result with coefficients in `AddCommGrpCat.{u}`.
-/

@[expose] public section

open Opposite

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  (J : GrothendieckTopology C)

namespace Presheaf

/-- Additivity descends along a locally surjective map to a separated presheaf
when every covering sieve contains a covering principal sieve. This concerns
addition of arrows of `C`, rather than addition of natural transformations. -/
theorem additive_of_isLocallySurjective_of_isSeparated
    (hJ : ∀ (X : C) (S : Sieve X), S ∈ J X →
      ∃ (Y : C) (q : Y ⟶ X), S q ∧ Sieve.generate (Presieve.singleton q) ∈ J X)
    {F G : Cᵒᵖ ⥤ AddCommGrpCat.{w}} [F.Additive] (η : F ⟶ G)
    [IsLocallySurjective J η] (hG : IsSeparated J G) : G.Additive := by
  constructor
  intro X₀ X₁ α β
  apply ConcreteCategory.hom_ext
  intro s
  obtain ⟨U, q, ⟨t, ht⟩, hq⟩ :=
    hJ X₀.unop (imageSieve η s) (imageSieve_mem J η s)
  let S := (Sieve.generate (Presieve.singleton q)).pullback α.unop ⊓
    (Sieve.generate (Presieve.singleton q)).pullback β.unop
  have hS : S ∈ J X₁.unop :=
    J.intersection_covering (J.pullback_stable α.unop hq)
      (J.pullback_stable β.unop hq)
  obtain ⟨V, h, hh, hhcover⟩ := hJ X₁.unop S hS
  obtain ⟨_, a, _, ⟨⟩, ha⟩ := hh.1
  obtain ⟨_, b, _, ⟨⟩, hb⟩ := hh.2
  have hab : (a + b) ≫ q = h ≫ (α.unop + β.unop) := by
    rw [Preadditive.add_comp, ha, hb, Preadditive.comp_add]
  have hlocal : G.map h.op (G.map (α + β) s) =
      G.map h.op ((G.map α + G.map β) s) := by
    calc
      G.map h.op (G.map (α + β) s) = G.map (a + b).op (G.map q.op s) := by
        rw [← ConcreteCategory.comp_apply, ← G.map_comp,
          ← ConcreteCategory.comp_apply, ← G.map_comp]
        have hab' : (α + β) ≫ h.op = q.op ≫ (a + b).op := by
          simpa only [op_comp, op_add, Quiver.Hom.op_unop] using
            congrArg Quiver.Hom.op hab.symm
        rw [hab']
      _ = G.map (a + b).op (η.app _ t) := by rw [ht]
      _ = η.app _ (F.map (a + b).op t) :=
        (NatTrans.naturality_apply η (a + b).op t).symm
      _ = η.app _ (F.map a.op t) + η.app _ (F.map b.op t) := by
        rw [op_add, F.map_add, AddCommGrpCat.hom_add_apply, map_add]
      _ = G.map a.op (G.map q.op s) + G.map b.op (G.map q.op s) := by
        rw [NatTrans.naturality_apply, NatTrans.naturality_apply, ht]
      _ = G.map h.op ((G.map α + G.map β) s) := by
        rw [AddCommGrpCat.hom_add_apply, map_add,
          ← ConcreteCategory.comp_apply, ← G.map_comp,
          ← ConcreteCategory.comp_apply, ← G.map_comp,
          ← ConcreteCategory.comp_apply, ← G.map_comp,
          ← ConcreteCategory.comp_apply, ← G.map_comp]
        have ha' := congrArg Quiver.Hom.op ha
        have hb' := congrArg Quiver.Hom.op hb
        simp only [op_comp, Quiver.Hom.op_unop] at ha' hb'
        rw [ha', hb']
  apply hG X₁.unop (Sieve.generate (Presieve.singleton h)) hhcover
  rintro W _ ⟨_, k, _, ⟨⟩, rfl⟩
  simpa only [op_comp, G.map_comp, ConcreteCategory.comp_apply] using
    congrArg (G.map k.op) hlocal

end Presheaf

/-- Ordinary Mathlib sheafification of an additive presheaf is additive in
source arrows on a site with a basis of covering principal sieves.

The coefficient universe is explicitly `max u v`, as required by Mathlib's
local-surjectivity theorem for the ordinary sheafification unit. -/
theorem sheafify_additive_of_principal_covering_basis
    (hJ : ∀ (X : C) (S : Sieve X), S ∈ J X →
      ∃ (Y : C) (q : Y ⟶ X), S q ∧ Sieve.generate (Presieve.singleton q) ∈ J X)
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    [J.HasSheafCompose (forget AddCommGrpCat.{max u v})]
    [J.PreservesSheafification (forget AddCommGrpCat.{max u v})]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) [F.Additive] :
    (sheafify J F).Additive :=
  Presheaf.additive_of_isLocallySurjective_of_isSeparated J hJ (toSheafify J F)
    ((presheafToSheaf J AddCommGrpCat).obj F).isSeparated

end CategoryTheory
