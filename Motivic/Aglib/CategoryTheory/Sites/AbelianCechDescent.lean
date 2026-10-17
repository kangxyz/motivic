/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# Gluing local lifts when their differences are a coboundary

For a short exact sequence of abelian sheaves, differences of local lifts of
one quotient section have unique preimages in the kernel sheaf. If these
differences are the images of the pairwise differences of local kernel
sections, subtracting those sections makes the lifts compatible. The sheaf
axiom then produces a genuine global lift of the original quotient section.

Only pairwise pullbacks of the displayed covering family are required.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory.Limits Opposite

universe t v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{t}]

/-- A section in the kernel has a unique section lift along the monomorphism
in an actual short exact sequence of abelian sheaves. -/
theorem existsUnique_section_preimage
    {S : ShortComplex (Sheaf J AddCommGrpCat.{t})} (hS : S.ShortExact)
    (X : C) (s : S.X₂.obj.obj (op X)) (hs : S.g.hom.app (op X) s = 0) :
    ∃! a : S.X₁.obj.obj (op X), S.f.hom.app (op X) a = s := by
  let E := sheafToPresheaf J AddCommGrpCat.{t} ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{t}).obj (op X)
  have : Mono S.f := hS.mono_f
  have hE : (S.map E).Exact :=
    hS.exact.map_of_mono_of_preservesKernel E inferInstance inferInstance
  obtain ⟨a, ha⟩ := (S.map E).ab_exact_iff.mp hE s hs
  refine ⟨a, ha, ?_⟩
  intro b hb
  exact (AddCommGrpCat.mono_iff_injective (E.map S.f)).mp inferInstance (hb.trans ha.symm)

/-- The literal difference of two restrictions of local quotient lifts has a
unique preimage in the kernel sheaf. -/
theorem existsUnique_localLiftDifference
    {S : ShortComplex (Sheaf J AddCommGrpCat.{t})} (hS : S.ShortExact)
    {X Y Z W : C} (f : Y ⟶ X) (g : Z ⟶ X)
    (a : W ⟶ Y) (b : W ⟶ Z) (hab : a ≫ f = b ≫ g)
    (s : S.X₃.obj.obj (op X))
    (y : S.X₂.obj.obj (op Y)) (z : S.X₂.obj.obj (op Z))
    (hy : S.g.hom.app (op Y) y = S.X₃.obj.map f.op s)
    (hz : S.g.hom.app (op Z) z = S.X₃.obj.map g.op s) :
    ∃! d : S.X₁.obj.obj (op W), S.f.hom.app (op W) d =
      S.X₂.obj.map a.op y - S.X₂.obj.map b.op z := by
  apply existsUnique_section_preimage J hS
  rw [map_sub, S.g.hom.naturality_apply a.op y,
    S.g.hom.naturality_apply b.op z, hy, hz]
  simp only [← Functor.map_comp_apply, ← op_comp, hab, sub_self]

omit [HasSheafify J AddCommGrpCat.{t}] in
/-- If the pairwise differences of local lifts are the image of a Cech
coboundary, the original quotient section has a global lift. -/
theorem exists_section_lift_of_coboundary
    (S : ShortComplex (Sheaf J AddCommGrpCat.{t}))
    {X : C} {ι : Type*} {U : ι → C} (p : ∀ i, U i ⟶ X)
    (hp : Sieve.ofArrows U p ∈ J X)
    [(Presieve.ofArrows U p).HasPairwisePullbacks]
    (s : S.X₃.obj.obj (op X)) (l : ∀ i, S.X₂.obj.obj (op (U i)))
    (hl : ∀ i, S.g.hom.app (op (U i)) (l i) = S.X₃.obj.map (p i).op s)
    (a : ∀ i, S.X₁.obj.obj (op (U i)))
    (ha : ∀ i j,
      S.X₂.obj.map (pullback.fst (p i) (p j)).op (l i) -
        S.X₂.obj.map (pullback.snd (p i) (p j)).op (l j) =
      S.f.hom.app (op (pullback (p i) (p j)))
        (S.X₁.obj.map (pullback.fst (p i) (p j)).op (a i) -
          S.X₁.obj.map (pullback.snd (p i) (p j)).op (a j))) :
    ∃ t : S.X₂.obj.obj (op X), S.g.hom.app (op X) t = s := by
  let l' (i : ι) := l i - S.f.hom.app (op (U i)) (a i)
  have h₂ : Presieve.IsSheafFor (S.X₂.obj ⋙ forget AddCommGrpCat.{t})
      (Presieve.ofArrows U p) := ((isSheaf_iff_isSheaf_of_type J _).mp
    ((sheafCompose J (forget AddCommGrpCat.{t})).obj S.X₂).property).isSheafFor
      (Presieve.ofArrows U p) hp
  have h₃ : Presieve.IsSheafFor (S.X₃.obj ⋙ forget AddCommGrpCat.{t})
      (Presieve.ofArrows U p) := ((isSheaf_iff_isSheaf_of_type J _).mp
    ((sheafCompose J (forget AddCommGrpCat.{t})).obj S.X₃).property).isSheafFor
      (Presieve.ofArrows U p) hp
  have hcompat : Presieve.Arrows.PullbackCompatible
      (S.X₂.obj ⋙ forget AddCommGrpCat.{t}) p l' := by
    intro i j
    change S.X₂.obj.map _ (l i - S.f.hom.app _ (a i)) =
      S.X₂.obj.map _ (l j - S.f.hom.app _ (a j))
    rw [map_sub, map_sub,
      ← S.f.hom.naturality_apply (pullback.fst (p i) (p j)).op (a i),
      ← S.f.hom.naturality_apply (pullback.snd (p i) (p j)).op (a j)]
    have h := ha i j
    rw [map_sub] at h
    exact sub_eq_sub_iff_sub_eq_sub.mp h
  obtain ⟨t, ht, _⟩ := (Presieve.isSheafFor_arrows_iff_pullbacks _ _).mp h₂ l' hcompat
  change ∀ i, S.X₂.obj.map (p i).op t = l' i at ht
  refine ⟨t, h₃.isSeparatedFor.ext ?_⟩
  rintro Y f ⟨i⟩
  change S.X₃.obj.map (p i).op (S.g.hom.app (op X) t) = S.X₃.obj.map (p i).op s
  rw [← S.g.hom.naturality_apply (p i).op t, ht i]
  change S.g.hom.app _ (l i - S.f.hom.app _ (a i)) = _
  rw [map_sub, hl i]
  have hz : S.g.hom.app (op (U i)) (S.f.hom.app (op (U i)) (a i)) = 0 := by
    have h := congrArg (fun η => η.hom.app (op (U i))) S.zero
    exact ConcreteCategory.congr_hom h (a i)
  rw [hz, sub_zero]

end CategoryTheory.Sheaf
